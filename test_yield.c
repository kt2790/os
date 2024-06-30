#include "types.h"
#include "stat.h"
#include "user.h"

void* fork_test(void *arg)
{
    int pid = fork();
    int p=0;
    int q=0;

    if(pid == 0)
    {
	    while(p<100)
        {
            //yield();
            //if(p == 100)

            printf(1, "PROCESS A : %d\n", p);
            p++;
        }

        exit();
    }
    else if(pid > 0)
    {
        while(q<100)
        {
            //yield();
            //if (q == 100)

            printf(1, "PROCESS B : %d\n", q);
            q++;
        }
        wait();
    }
    else
    {
        printf(1, "fork failed\n");
        exit();
    }
    return 0;
}

int main(int argc, char* argv[])
{
	//thread_t thread;
	//void *retval;

    /*
	thread_create(&thread, fork_test, 0);
	thread_join(thread, &retval);
    */
    fork_test(0);

	exit();
}
