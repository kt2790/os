#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

struct spinlock filelock;
struct spinlock filelock2;
struct spinlock sbrklock;

static struct proc *initproc;

int nextpid = 1;
thread_t nexttid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

struct st
{
  int use;
};

struct
{
  struct st st[NPROC*32];
}st_table;

uint get_base(struct proc* p)
{
  int i;

  for(i=0; i<NPROC*32; i++)
  {
    if(st_table.st[i].use != 0)
      continue;
    
    st_table.st[i].use = 1;
    p->stack_index = i;

    return i;
  }
  panic("stack allocation error");
}


void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  p->prlev = 2;
  p->tick = 0;
  p->allot = 0;
  p->is_stride = 0;
  p->stride = 0;
  p->pass = 0;
  p->is_thread = 0;
  p->recent_proc = p;
  p->main_proc = p;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  acquire(&sbrklock);

  uint sz;
  struct proc *curproc = myproc();
  struct proc *mainproc = myproc()->main_proc;
  
  sz = mainproc->sz;
  
  if(n > 0)
  {
    if((sz = allocuvm(mainproc->pgdir, sz, sz + n)) == 0)
    {
      release(&sbrklock);
      return -1;
    }
  } 
  else if(n < 0)
  {
    if((sz = deallocuvm(mainproc->pgdir, sz, sz + n)) == 0)
    {
      release(&sbrklock);
      return -1;
    }
  }
  mainproc->sz = sz;
  release(&sbrklock);
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = my_copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }

  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;
  np->is_thread = 0;
  np->main_proc = np;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc()->main_proc;
  struct proc *p;
  struct proc *t;
  int fd;
 
  if(curproc == initproc)
    panic("init exiting");

  acquire(&filelock2);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->main_proc == curproc && p->is_thread == 1)
    {
      for(fd = 0; fd < NOFILE; fd++)
      {
        if(p->ofile[fd])
        {
            fileclose(p->ofile[fd]);
            p->ofile[fd] = 0;
        }
      }
    }
  }

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }
  release(&filelock2);
  
  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;
  
  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->main_proc == curproc && p->is_thread == 1)
    {
      if(holding(&filelock2) != 0)
        release(&filelock2);

      p->state = ZOMBIE;
      for(t = ptable.proc; t < &ptable.proc[NPROC]; t++)
      {
        if(t->parent == p)
        {
          t->parent = initproc;
        }
      }      
    }
  }
  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  if(holding(&filelock2) != 0)
    release(&filelock2);
  curproc->state = ZOMBIE;  
      
  sched();
  panic("zombie exit");
}

void
exit_(void)
{
  struct proc *curproc = myproc();
  struct proc *mainproc = curproc->main_proc;
  struct proc *p;
  struct proc *t;
  int fd;
 
  if(curproc == initproc)
    return;
  
  acquire(&filelock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->main_proc == mainproc && p != curproc)
    {
      for(fd = 0; fd < NOFILE; fd++)
      {
        if(p->ofile[fd])
        {
            fileclose(p->ofile[fd]);
            p->ofile[fd] = 0;
        }
      }
    }
  }
  release(&filelock);

  acquire(&ptable.lock);
  
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->main_proc == mainproc && p != curproc && p->is_thread == 1)
    {
      kfree(p->kstack);
      p->kstack = 0;
      deallocuvm(p->pgdir, p->stack_base + 2*PGSIZE, p->stack_base);

      st_table.st[p->stack_index].use = 0;

      p->pid = 0;
      p->parent = 0;
      p->main_proc = 0;
      p->killed = 0;
      p->state = UNUSED;
      p->stack_index = 0;
      p->stack_base = 0;

      if(holding(&filelock) != 0)
        release(&filelock);

      for(t = ptable.proc; t < &ptable.proc[NPROC]; t++)
      {
        if(t->parent == p)
        {
          t->parent = initproc;
        }
      }  
    }
    else if(p->main_proc == mainproc && p != curproc && p->is_thread == 0)
    {
      kfree(p->kstack);
      p->kstack = 0;
      
      p->pid = 0;
      p->parent = 0;
      p->name[0] = 0;
      p->killed = 0;
      p->state = UNUSED;

      if(holding(&filelock) != 0)
        release(&filelock);
      
      for(t = ptable.proc; t < &ptable.proc[NPROC]; t++)
      {
        if(t->parent == p)
        {
          t->parent = initproc;
        }
      }      
    }
  }

  if(curproc->is_thread == 1)
  {
    deallocuvm(curproc->pgdir, curproc->stack_base + 2*PGSIZE, curproc->stack_base);
    st_table.st[curproc->stack_index].use = 0;
  }
  
  curproc->is_thread = 0;
  curproc->pid = nextpid++;
  curproc->tid = 0;
  curproc->main_proc = curproc;
  
  release(&ptable.lock);  
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  struct proc *t;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc || p->is_thread != 0)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        
        for(t = ptable.proc; t < &ptable.proc[NPROC]; t++)
        {
            if(t->main_proc == p && t->is_thread == 1)
            {
               kfree(t->kstack);
               t->kstack = 0;
               deallocuvm(t->pgdir, t->stack_base + 2*PGSIZE, t->stack_base);

               st_table.st[t->stack_index].use = 0;

               t->pid = 0;
               t->parent = 0;
               t->main_proc = 0;
               t->killed = 0;
               t->state = UNUSED;
               t->stack_index = 0;
               t->stack_base = 0;
            }
        }
        release(&ptable.lock);
        return pid; 
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.
void
calc_ratio(int* m, int* n)
{
  // m => stride process, n => default process
  struct proc* p;
  double mlfq_sum = 0;
  double share_sum = 0;
  double mlfq_n = 0;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
      if(p->is_thread != 0)
        continue;

      if(p->is_stride == 0 && p->state == RUNNABLE)
      {
        mlfq_n++;

        if(p->prlev == 2)
          mlfq_sum += 10;
        else if(p->prlev == 1)
          mlfq_sum += 17.5;
        else
          mlfq_sum += 20;

      }
      else if(p->is_stride == 1 && p->state == RUNNABLE)
      {
        share_sum += p->share;
      }

      // a = x*share/(100-share) (100-share)a = x*share
      // x*share : (100-share)*mlfq_
  }
  
  *m = (int)((4*mlfq_sum*share_sum)/(100-share_sum) + 0.5);
  *n = 20*mlfq_n; 

}

struct proc*
get_lwp(struct proc* p)
{
  struct proc* t = p->recent_proc;
  int cnt = 0;
  t++;

  while(cnt != NPROC)
  {
    if(t == &ptable.proc[NPROC])
      t = ptable.proc;
    
    if(t->state == RUNNABLE && t->main_proc == p)
    {
      p->recent_proc = t;
      return t;
    }
    
    cnt++;
    t++;
  }

  return 0;
}

void
scheduler(void)
{
  struct proc *p;
  struct proc* t;
  struct proc* stride_p;
  struct cpu *c = mycpu();
  c->proc = 0;
  int cnt = 0;
  int prl = 2;
  int m, n;
  int stride_cnt = 0;
  int default_cnt = 0;
  uint MAX_PASS;

  calc_ratio(&m, &n);
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run. 
    acquire(&ptable.lock);

    // finding stride process.

    stride_p = ptable.proc;
    MAX_PASS = 2000000000;

    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      
      if(p->is_stride == 0 || p->is_thread != 0 || p->state == UNUSED)
        continue;

      if((get_lwp(p)) == 0)
        continue;

      if(p->pass < MAX_PASS)
      {
        stride_p = p;
        MAX_PASS = stride_p->pass;
      }
    }

    if(stride_p->is_stride == 1 && stride_p->state != UNUSED)
    {
      if(stride_p->is_thread != 0)
        goto MLFQ;

      t = get_lwp(stride_p);

      if(t == 0)
        goto SKIP2;

      c->proc = t;
      switchuvm(t);
      t->state = RUNNING;
      swtch(&(c->scheduler), t->context);
      switchkvm();

      stride_cnt++;
SKIP2:      
      calc_ratio(&m, &n);
      

      if(m == 0 && n != 0)
        goto MLFQ;
      else if(stride_cnt % m == 0 && n != 0)
        goto MLFQ;
      else
        goto STRIDE; 
    }
MLFQ:

    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      
      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      if(p->is_stride == 0 && p->state != UNUSED)
      {
        if(p->prlev == prl && p->is_thread == 0)
        {
          t = get_lwp(p);

          if(t == 0)
            goto SKIP;
          
          
          c->proc = t;
          switchuvm(t);
          t->state = RUNNING;

          cnt = 0;
          prl = 2;
          swtch(&(c->scheduler), t->context);
          switchkvm();

          calc_ratio(&m, &n);
          default_cnt++;

          if(n == 0)
            goto STRIDE;
          else if(default_cnt % n == 0)
            goto STRIDE;
        }
      }
      // Process is done running for now.
      // It should have changed its p->state before coming back.
SKIP:
      cnt++;
      
      if( cnt == NPROC + 1 )
      {
        if(prl == 2)
          prl = 1;
        else if(prl == 1)
          prl = 0;
        else if(prl == 0)
          prl = 2;

        cnt = 1; 
      }
    
      c->proc = 0;
    }

    release(&ptable.lock); // For other interrupts
    sti();
    acquire(&ptable.lock); // Reacquire
    goto MLFQ;

STRIDE:
    c->proc = 0;

    release(&ptable.lock);

  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}


// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

int
getppid(void)
{
  return myproc()->parent->pid;
}

int
getlev(void)
{
  return myproc()->prlev;
}

void
res_prlev(void)
{
  struct proc *p;
  
  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == RUNNABLE || p->state == RUNNING){     
      p->prlev = 2;
      p->allot = 0;
      p->tick = 0;
    }
  }

  release(&ptable.lock); 

}

struct proc*
get_next_lwp(struct proc* p)
{
  struct proc* t = p;
  int cnt = 0;
  t++;

  while(cnt != NPROC)
  {
    if(t == &ptable.proc[NPROC])
      t = ptable.proc;
    
    if(t->state == RUNNABLE && t->main_proc == p->main_proc)
    {
      return t;
    }
    
    cnt++;
    t++;
  }

  return 0;
}

void
lwp_sched(struct proc* t)
{
  int intena;
  struct proc *p = myproc();
  struct cpu *c = mycpu();

  //cprintf("%p %p \n", p, t);
  
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  
  intena = mycpu()->intena;
  c->proc = t;
          
  switchtss(t);
  t->state = RUNNING;

  //cprintf("tss switch ok\n");

  swtch(&p->context, t->context);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
int
lwp_yield(void)
{
  struct proc* p = myproc(); 
  struct proc* t;

  p->state = RUNNABLE;
  t = get_next_lwp(p);
  
  if(t == 0)
    return -1;
  
  if(p == t)
  {
    p->state = RUNNING;
    return 0;
  }
  
  lwp_sched(t);

  return 0;
}

void
judge_proc(void)
{
  struct proc *p = myproc();
  struct proc *mp = p->main_proc;
 
  acquire(&ptable.lock);

  mp->tick += 1;
  mp->allot += 1;

  if(mp->is_stride)
  {
    mp->pass += mp->stride;

    if(mp->pass > 1000000000)
    {
      for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
        mp->pass = 0;
    }
    
    if(mp->tick >= 5)
    {
      mp->tick = 0;
      release(&ptable.lock);
      yield();
      acquire(&ptable.lock);
    }

    if((lwp_yield()) != 0)
    {
      release(&ptable.lock);
      yield();
      acquire(&ptable.lock);
    }

    release(&ptable.lock);
    
    return;
  }
  
  if(mp->prlev == 2)
  {
    if(mp->allot >= 20)
    {
      mp->prlev = 1;
      mp->allot = 0;
    }
    
    if(mp->tick >= 5)
    {
      mp->tick = 0;
      release(&ptable.lock);
      yield();
      acquire(&ptable.lock);
    }
  }
  else if(mp->prlev == 1)
  {
    if(mp->allot >= 40)
    {
      mp->prlev = 0;
      mp->allot = 0;
    }

    if(mp->tick >= 10)
    {
      mp->tick = 0;
      release(&ptable.lock);
      yield();
      acquire(&ptable.lock);
    }
  }
  else if(mp->prlev == 0)
  {
    if(mp->tick >= 20)
    {
      mp->tick = 0;
      release(&ptable.lock);
      yield();
      acquire(&ptable.lock);
    }
  }
  

  if((lwp_yield()) != 0)
  {
    release(&ptable.lock);
    yield();
    acquire(&ptable.lock);
  }


  release(&ptable.lock);

}

int
set_cpu_share(int share)
{
  struct proc* p;
  struct proc* cp = myproc()->main_proc;

  if(share <=0 || cp->is_stride == 1)
    return -1;

  uint minpass = 200000000;

  int share_sum = share;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->is_thread != 0)
      continue;

    if(p->is_stride && (p->state == RUNNABLE || p->state == RUNNING))
    {
      share_sum += p->share;
      if(minpass > p->pass)
        minpass = p->pass;
    }
  }

  if(share_sum > 80)
    return -1;

  acquire(&ptable.lock);

  cp->is_stride = 1;
  cp->pass = minpass;
  cp->stride = 10000000 / share;
  cp->share = share;

  release(&ptable.lock);

  return 0;
}

int thread_create(thread_t* thread, void* (*start_routine)(void*), void* arg)
{
  int i;
  struct proc *np;
  struct proc *curproc = myproc()->main_proc;

  if((np = allocproc()) == 0)
  {
    return -1;
  }

  acquire(&ptable.lock);
/*
  if(curproc->is_thread == 1)
  {
    np->main_proc = curproc->main_proc;
  }
  else if(curproc->is_thread == 0)
  {
    np->main_proc = curproc;
  }
*/
  np->tid = nexttid++;
  np->pid = curproc->pid;
  np->main_proc = curproc;
  *thread = np->tid;

  np->pgdir = curproc->pgdir;
  *np->tf = *curproc->tf;
  safestrcpy(np->name, curproc->name, sizeof(curproc->name));
  np->cwd = idup(curproc->cwd);

  np->stack_base = curproc->sz + (uint)(2*PGSIZE*(get_base(np)+64));
  np->parent = curproc->main_proc->parent;

  if((np->sz = allocuvm(np->pgdir, np->stack_base, np->stack_base + 2*PGSIZE)) == 0)
  {
    np->state = UNUSED;
    return -1;
  }

  uint temp = np->sz - 4;
  *((uint*)(temp)) = (uint)arg;
  temp = temp - 4;
  *((uint*)(temp)) = 0xffffffff;
  np->tf->esp = np->sz - 8;

  np->tf->eip = (uint)start_routine;

  for(i=0; i<NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);

  np->is_thread = 1;
  np->state = RUNNABLE;
  
  release(&ptable.lock);

  return 0;
}

void thread_exit(void* retval)
{
  struct proc *curproc = myproc();
  int fd;

  if(curproc == initproc)
    panic("init exiting\n");

  for(fd=0; fd<NOFILE; fd++)
  {
    if(curproc->ofile[fd])
    {
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd]=0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  curproc->retval = retval;

  wakeup1(curproc->main_proc);
  curproc->state = ZOMBIE;

  sched();

  panic("zombie exit\n");
}

int thread_join(thread_t thread, void** retval)
{
  struct proc *p;
  struct proc *curproc = myproc();

  /*
  if(curproc->is_thread == 1)
    return -1;
  */

  acquire(&ptable.lock);

  for(;;)
  {
    for(p=ptable.proc; p<&ptable.proc[NPROC]; p++)
    {
      if(p->tid != thread || p->main_proc != curproc)
        continue;
      
      if(p->state == ZOMBIE)
      {
        *retval = p->retval;

        kfree(p->kstack);
        p->kstack = 0;
        deallocuvm(p->pgdir, p->stack_base + 2*PGSIZE, p->stack_base);

        st_table.st[p->stack_index].use = 0;

        p->pid = 0;
        p->parent = 0;
        p->main_proc = 0;
        p->killed = 0;
        p->state = UNUSED;
        p->stack_index = 0;
        p->stack_base = 0;

        release(&ptable.lock);

        return 0;
      }
    }

    if(curproc->killed)
    {
      release(&ptable.lock);
      return -1;
    }

    sleep(curproc, &ptable.lock);
  }
}
