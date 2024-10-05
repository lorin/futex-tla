#include <pthread.h>
#include <stdio.h>

int main() {
    pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
    pthread_mutex_lock(&mutex);
    printf("Mutex locked\n");
    pthread_mutex_unlock(&mutex);
    printf("Mutex unlocked\n");
    return 0;
}
