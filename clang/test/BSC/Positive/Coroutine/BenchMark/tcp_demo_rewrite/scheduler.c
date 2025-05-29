// RUN: %clang -fsyntax-only %s
// expected-no-diagnostics

#include "scheduler.h"
#include <unistd.h>

struct __Trait_Future_struct_Void {
    void *data;
    struct __Trait_Future_Vtable_struct_Void *vtable;
};

struct Task {
    struct __Trait_Future_struct_Void future;
    _Atomic(int) state;
};

struct Queue_void_P {
    unsigned int writeIndex;
    unsigned int readIndex;
    _Atomic(unsigned int) count;
    unsigned int capacity;
    void **buf;
    pthread_mutex_t mutex;
};

struct ThreadContext {
    unsigned int id;
    unsigned long pid;
    struct Queue_void_P localQueue;
    void *runningTask;
};

struct Scheduler {
    _Bool isInit;
    struct Queue_void_P *globalQueue;
    unsigned int threadCount;
    struct ThreadContext **threads;
};

struct _Yield {
    int __future_state;
};

struct PollResult_struct_Void {
    _Bool isPending;
    struct Void res;
};

struct __Trait_Future_Vtable_struct_Void {
    struct PollResult_struct_Void (*poll)(void *);
    void (*free)(void *);
};

static struct PollResult_struct_Void struct_PollResult_struct_Void_pending(void);

static struct PollResult_struct_Void struct_PollResult_struct_Void_completed(struct Void result);

static void struct_Queue_void_P_push(struct Queue_void_P *this, void *value);

static void *struct_Queue_void_P_pop(struct Queue_void_P *this);

static void struct_Queue_void_P_init(struct Queue_void_P *this, unsigned int capacity);

static void struct_Queue_void_P_destroy(struct Queue_void_P *this);

struct Scheduler *getScheduler(void);

struct ThreadContext *getCurrentCtx(void);

struct Task *struct_Scheduler_spawn(struct __Trait_Future_struct_Void future);

struct __Trait_Future_struct_Void yield(void);

struct Scheduler S;

_Atomic(int) g_taskCount;

struct ThreadContext *g_mainThread;

__thread struct ThreadContext *g_curCtx;

extern NOISE g_noise;

struct Scheduler *getScheduler() {
    if (!S.isInit) {
        fprintf(stderr, "please initialize before using the getScheduler() function\n");
        exit(EXIT_FAILURE);
    }
    return &S;
}

struct ThreadContext * getCurrentCtx() {
    return g_curCtx;
}

int taskCount() {
    return atomic_load(&g_taskCount);
}

void taskAddOne() {
    atomic_fetch_add(&g_taskCount, 1);
}

struct PollResult_struct_Void struct__Yield_poll(struct _Yield *this) {
    if (this->__future_state == 0) {
        this->__future_state = 1;
        return struct_PollResult_struct_Void_pending();
    } else if (this->__future_state == 1) {
        this->__future_state = -1;
        return struct_PollResult_struct_Void_completed((struct Void){});
    } else {
        abort();
    }
}

void struct__Yield_free(struct _Yield *this) {
    if (this != ((void *)0)) {
        free(this);
        this = ((void *)0);
    }
}

struct __Trait_Future_Vtable_struct_Void __struct__Yield_trait_Future = {.poll = (struct PollResult_struct_Void (*)(void *))struct__Yield_poll, .free = (void (*)(void *))struct__Yield_free};

struct __Trait_Future_struct_Void yield(void) {
    struct _Yield *ptr = malloc(sizeof(struct _Yield));
    if (ptr != ((void *)0)) {
        fprintf(stderr, "Error: memory alloc failed\n");
        exit(1);
    }
    ptr->__future_state = 0;
    return (struct __Trait_Future_struct_Void){.data = ptr, .vtable = &__struct__Yield_trait_Future};
}

static void *stealTask(void) {
    void *task = ((void *)0);
    for (unsigned int i = 1; i < S.threadCount; i++) {
        if (S.isInit && S.threads[i] != ((void *)0)) {
            task = struct_Queue_void_P_pop(&S.threads[i]->localQueue);
            if (task) {
                return task;
            }
        }
    }
    return task;
}

static void *getReadyTask(void) {
    void *task = ((void *)0);
    do {
        if (g_curCtx->id > 0) {
            task = struct_Queue_void_P_pop(&g_curCtx->localQueue);
            if (task) {
                break;
            }
        }
        task = struct_Queue_void_P_pop(S.globalQueue);
        if (task) {
            break;
        }
        task = stealTask();
        if (task) {
            break;
        }
        if (!S.isInit)
            break;
    } while (1);
    return task;
}

static int findQueue() {
    double avg = (double)taskCount() / S.threadCount;
    for (unsigned int i = 1; i < S.threadCount; i++) {
        if (S.threads[i]->localQueue.count < avg) {
            return i;
        }
    }
    return 0;
}

void *schedule(void *arg) {
    struct ThreadContext *ctx = (struct ThreadContext *)arg;
    g_curCtx = ctx;
    atomic_llong start, end;
    while (1)
        {
            start = read_tsc();
            struct Task *task = (struct Task *)getReadyTask();
            ctx->runningTask = task;
            if (!task && !S.isInit) {
                break;
            }
            end = read_tsc();
            g_noise.getTaskCost += end - start;
            g_noise.getTaskCount++;
            start = read_tsc();
            struct PollResult_struct_Void s = task->future.vtable->poll(task->future.data);
            end = read_tsc();
            g_noise.pollCost += end - start;
            ctx->runningTask = ((void *)0);
            if (s.isPending) {
                __c11_atomic_store(&task->state, PARKED, 5);
                int index = findQueue();
                if (index == 0) {
                    struct_Queue_void_P_push(S.globalQueue, task);
                } else {
                    struct_Queue_void_P_push(&S.threads[index]->localQueue, task);
                }
            } else {
                start = read_tsc();
                __c11_atomic_store(&task->state, COMPLETED, 5);
                __c11_atomic_fetch_sub(&g_taskCount, 1, 5);
                task->future.vtable->free(task->future.data);
                if (task != ((void *)0)) {
                    free(task);
                    task = ((void *)0);
                }
                end = read_tsc();
                g_noise.freeCost += end - start;
                g_noise.freeCount++;
            }
            if (!S.isInit) {
                break;
            }
        }
    return ((void *)0);
}

void struct_Scheduler_init(unsigned int threadCount) {
    if (S.isInit) {
        fprintf(stderr, "Error: cannot create scheudler repeatedly.\n");
        exit(1);
    }
    S = (struct Scheduler){.threadCount = threadCount + 1};
    S.globalQueue = (struct Queue_void_P *)malloc(sizeof(struct Queue_void_P));
    struct_Queue_void_P_init(S.globalQueue, 128);
    S.threads = malloc(sizeof(struct ThreadContext *) * (threadCount + 1));
    if (S.threads == ((void *)0)) {
        fprintf(stderr, "Error: memory alloc failed\n");
        exit(1);
    }
    g_mainThread = malloc(sizeof(struct ThreadContext));
    g_taskCount = 0;
    if (g_mainThread == ((void *)0)) {
        fprintf(stderr, "Error: main thread memory alloc failed\n");
        exit(1);
    }
    g_mainThread->id = 0;
    g_mainThread->pid = getpid();
    g_curCtx = g_mainThread;
    S.threads[0] = g_mainThread;
    S.isInit = 1;
    unsigned int i;
    for (i = 1; i <= threadCount; i++) {
        struct ThreadContext *thread = malloc(sizeof(struct ThreadContext));
        if (thread == ((void *)0)) {
            fprintf(stderr, "Error: memory alloc failed\n");
            exit(1);
        }
        thread->id = i;
        struct_Queue_void_P_init(&thread->localQueue, 128);
        S.threads[i] = thread;
        unsigned long pid;
        int res = pthread_create(&pid, ((void *)0), schedule, (void *)thread);
        thread->pid = pid;
        if (res != 0) {
            fprintf(stderr, "Error: create thread failed\n");
            exit(1);
        }
    }
}

void struct_Scheduler_run(void) {
    if (!S.isInit) {
        fprintf(stderr, "Error: please initialize the scheduler before run.\n");
        exit(1);
    }
    schedule(g_mainThread);
}

struct Task *struct_Scheduler_spawn(struct __Trait_Future_struct_Void future) {
    long start, end;
    start = read_tsc();
    if (!S.isInit) {
        fprintf(stderr, "Error: please initialize the scheduler before spawn.\n");
        exit(1);
    }
    struct Task *t = malloc(sizeof(struct Task));
    if (t == ((void *)0)) {
        fprintf(stderr, "Error: malloc alloc failed\n");
        exit(1);
    }
    t->future = future;
    t->state = READY;
    end = read_tsc();
    g_noise.createTaskCost = end - start;
    g_noise.createTaskCount++;
    int index = findQueue();
    if (index == 0) {
        struct_Queue_void_P_push(S.globalQueue, t);
    } else {
        struct_Queue_void_P_push(&S.threads[index]->localQueue, t);
    }
    taskAddOne();
    return t;
}

void struct_Scheduler_destroy(void) {
    unsigned int i;
    S.isInit = 0;
    if (S.globalQueue != ((void *)0)) {
        struct_Queue_void_P_destroy(S.globalQueue);
        free(S.globalQueue);
        S.globalQueue = ((void *)0);
    }
    for (i = 0; i < S.threadCount; i++) {
        if (i != 0)
            struct_Queue_void_P_destroy(&S.threads[i]->localQueue);
        if (S.threads[i] != ((void *)0)) {
            free(S.threads[i]);
            S.threads[i] = ((void *)0);
        }
    }
    if (S.threads != ((void *)0)) {
        free(S.threads);
        S.threads = ((void *)0);
    }
}

static struct PollResult_struct_Void struct_PollResult_struct_Void_pending(void) {
    struct PollResult_struct_Void this;
    this.isPending = 1;
    return this;
}

static struct PollResult_struct_Void struct_PollResult_struct_Void_completed(struct Void result) {
    struct PollResult_struct_Void this;
    this.isPending = 0;
    this.res = result;
    return this;
}

static void struct_Queue_void_P_push(struct Queue_void_P *this, void *value) {
    unsigned long start, end;
    start = read_tsc();
    pthread_mutex_lock(&this->mutex);
    this->buf[this->writeIndex] = value;
    if ((this->writeIndex + 1) % this->capacity == this->readIndex) {
        this->writeIndex = this->capacity;
        this->readIndex = 0;
        this->capacity = 2 * this->capacity;
        this->buf = realloc(this->buf, sizeof(void *) * this->capacity);
        if (this->buf == ((void *)0)) {
            fprintf(stderr, "Error: expand capacity failed\n");
            exit(1);
        }
        printf("capacity: %d\n", this->capacity);
    } else {
        this->writeIndex = (this->writeIndex + 1) % this->capacity;
    }
    ++this->count;
    pthread_mutex_unlock(&this->mutex);
    end = read_tsc();
    g_noise.pushCost = end - start;
    g_noise.pushCount++;
}

static void *struct_Queue_void_P_pop(struct Queue_void_P *this) {
    unsigned long start, end;
    start = read_tsc();
    pthread_mutex_lock(&this->mutex);
    if (this->count == 0) {
        pthread_mutex_unlock(&this->mutex);
        return ((void *)0);
    }
    void *res = this->buf[this->readIndex];
    this->readIndex = (this->readIndex + 1) % this->capacity;
    --this->count;
    pthread_mutex_unlock(&this->mutex);
    end = read_tsc();
    g_noise.popCost = end - start;
    g_noise.popCount++;
    return res;
}

static void struct_Queue_void_P_init(struct Queue_void_P *this, unsigned int capacity) {
    if (capacity == 0) {
        fprintf(stderr, "Error: invalid capacity: %d\n", capacity);
        return;
    }
    this->buf = malloc(sizeof(void *) * capacity);
    if (this->buf == ((void *)0)) {
        fprintf(stderr, "Error: maloc failed, size: %lu\n", (sizeof(void *) * capacity));
        return;
    }
    int res = pthread_mutex_init(&this->mutex, ((void *)0));
    if (res != 0) {
        fprintf(stderr, "Error: phtread mutex init failed\n");
        exit(1);
    }
    this->capacity = capacity;
    this->readIndex = 0;
    this->writeIndex = 0;
    this->count = 0;
}

static void struct_Queue_void_P_destroy(struct Queue_void_P *this) {
    if (this->buf != ((void *)0)) {
        free(this->buf);
        this->buf = ((void *)0);
    }
    pthread_mutex_destroy(&this->mutex);
    this->capacity = 0;
    this->readIndex = 0;
    this->writeIndex = 0;
    this->count = 0;
}

