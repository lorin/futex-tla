#include <stdbool.h>

/**
 * A naive (read: incorrecct) implementation of locking with futexes.
 * It's incorrect due to race conditions.
 */
#define FREE 0
#define ACQUIRED 1
#define CONTENDED 2

void futex_wait(int *futex, int val);
void futex_wake(int *futex);

/**
 * Try to acquire the lock. On failure, wait and then try again.
 */
void lock(int *futex) {
    bool acquired = false;
    while (!acquired) {
        if (*futex == FREE) {
            *futex = ACQUIRED;
            acquired = true;
        }
        else {
            *futex = CONTENDED;
            futex_wait(futex, CONTENDED);
        }
    }
}

/**
 * Release lock, wake threads that are waiting on lock
 */
void unlock(int *futex) {
    int prev = *futex;
    *futex = FREE;

    if(prev == CONTENDED) {
        futex_wake(futex);
    }
}