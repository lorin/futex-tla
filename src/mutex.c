#include <pthread.h>
#include <stdio.h>

// Define a mutex
pthread_mutex_t my_mutex = PTHREAD_MUTEX_INITIALIZER;

// Function to lock and unlock the mutex
void lock_and_unlock() {
    // Lock the mutex
    pthread_mutex_lock(&my_mutex);
    printf("Mutex locked\n");
    // Do some work here...
    printf("Mutex unlocked\n");
    // Unlock the mutex
    pthread_mutex_unlock(&my_mutex);
}

int main() {
    // Create a thread that will call lock_and_unlock()
    pthread_t thread;
    pthread_create(&thread, NULL, (void*)lock_and_unlock, NULL);

    // Wait for the thread to finish
    pthread_join(thread, NULL);

    return 0;
}
