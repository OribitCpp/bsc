// RUN: %clang %s %S/scheduler.c %S/noise.c -o %test.output -lpthread
// expected-no-diagnostics

#include <stdio.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <string.h>
#include <unistd.h>
#include <pthread.h>
#include <time.h>
#include "scheduler.h"

#define ROW 50
#define COL 50
#define BUFFER_SIZE 1024

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

struct FileWriter {
    FILE *file;
    char *buffer;
    _Bool isWrited;
};

typedef struct FileWriter FileWriter;

struct PollResult_struct_Void {
    _Bool isPending;
    struct Void res;
};

struct __Trait_Future_Vtable_struct_Void {
    struct PollResult_struct_Void (*poll)(void *);
    void (*free)(void *);
};

struct _FuturecreateMatrix {
    int (*matrix)[50];
    int i;
    int j;
    int k;
    int __future_state;
};

struct _FuturemultiMatrix {
    int (*matrix1)[50];
    int (*matrix2)[50];
    int (*result)[50];
    int i;
    int j;
    int sum;
    int k;
    int __future_state;
};

struct _FuturematrixCalculation {
    char str[52];
    int matrix1[50][50];
    int matrix2[50][50];
    int result[50][50];
    char buffer[1024];
    struct _IO_FILE *file;
    int k;
    int i;
    int j;
    struct __Trait_Future_struct_Void Ft_1;
    struct __Trait_Future_struct_Void Ft_2;
    struct __Trait_Future_struct_Void Ft_3;
    struct FileWriter Ft_4;
    int __future_state;
};

static struct PollResult_struct_Void struct_PollResult_struct_Void_pending(void);

static _Bool struct_PollResult_struct_Void_is_completed(struct PollResult_struct_Void *this, struct Void *out);

static struct PollResult_struct_Void struct_PollResult_struct_Void_completed(struct Void result);

struct Scheduler *getScheduler(void);

struct ThreadContext *getCurrentCtx(void);

struct Task *struct_Scheduler_spawn(struct __Trait_Future_struct_Void future);

struct __Trait_Future_struct_Void yield(void);

NOISE g_noise;

FileWriter fileWriter(FILE *file, char *buffer) {
    struct FileWriter fw;
    fw.file = file;
    fw.buffer = buffer;
    fw.isWrited = false;
    return fw;
}

struct PollResult_struct_Void struct_FileWriter_poll(struct FileWriter *this) {
    if (this->isWrited) {
        this->isWrited = 0;
        struct Void res = {};
        return struct_PollResult_struct_Void_completed(res);
    } else {
        unsigned long start, end;
        start = read_tsc();
        if (fprintf(this->file, "%s", this->buffer) < 0) {
            perror("file writer failed");
        }
        end = read_tsc();
        g_noise.businessCost = end - start;
        this->isWrited = 1;
        return struct_PollResult_struct_Void_pending();
    }
}

void struct_FileWriter_free(struct FileWriter *this) {
}

struct __Trait_Future_Vtable_struct_Void __struct_FileWriter_trait_Future = {.poll = (struct PollResult_struct_Void (*)(void *))struct_FileWriter_poll, .free = (void (*)(void *))struct_FileWriter_free};

struct __Trait_Future_struct_Void __createMatrix(int (*matrix)[50]);

struct PollResult_struct_Void struct__FuturecreateMatrix_poll(struct _FuturecreateMatrix *this) {
    switch (this->__future_state) {
      case 0:
        goto __L0;
    }
  __L0:
    ;
    unsigned long start, end;
    start = read_tsc();
    int i;
    int j;
    this->k = 0;
    srand((unsigned int)time(((void *)0)));
    for (this->i = 0; this->i < 50; this->i++) {
        for (this->j = 0; this->j < 50; this->j++) {
            this->matrix[this->i][this->j] = rand() % 2;
        }
    }
    end = read_tsc();
    g_noise.businessCost = end - start;
    {
        this->__future_state = -1;
        struct Void __RES_RETURN = (struct Void){};
        return struct_PollResult_struct_Void_completed(__RES_RETURN);
    }
}

void struct__FuturecreateMatrix_free(struct _FuturecreateMatrix *this) {
    if (this != 0) {
        free((void *)this);
        this = (struct _FuturecreateMatrix *)(void *)0;
    }
}

struct __Trait_Future_Vtable_struct_Void __Trait_Future_VtablecreateMatrix = {(struct PollResult_struct_Void (*)(void *))struct__FuturecreateMatrix_poll, (void (*)(void *))struct__FuturecreateMatrix_free};

struct __Trait_Future_struct_Void __createMatrix(int (*matrix)[50]) {
    struct _FuturecreateMatrix *data = calloc(1, sizeof(struct _FuturecreateMatrix));
    if (data == 0) {
        exit(1);
    }
    data->matrix = matrix;
    data->__future_state = 0;
    struct __Trait_Future_struct_Void fp = {(void *)data, &__Trait_Future_VtablecreateMatrix};
    return fp;
}

struct __Trait_Future_struct_Void __multiMatrix(int (*matrix1)[50], int (*matrix2)[50], int (*result)[50]);

struct PollResult_struct_Void struct__FuturemultiMatrix_poll(struct _FuturemultiMatrix *this) {
    switch (this->__future_state) {
      case 0:
        goto __L0;
    }
  __L0:
    ;
    unsigned long start, end;
    start = read_tsc();
    for (this->i = 0; this->i < 50; this->i++) {
        for (this->j = 0; this->j < 50; this->j++) {
            this->sum = 0;
            for (this->k = 0; this->k < 50; this->k++) {
                this->sum += this->matrix1[this->i][this->k] * this->matrix2[this->k][this->j];
            }
            this->result[this->i][this->j] = this->sum;
        }
    }
    end = read_tsc();
    g_noise.businessCost = end - start;
    {
        this->__future_state = -1;
        struct Void __RES_RETURN = (struct Void){};
        return struct_PollResult_struct_Void_completed(__RES_RETURN);
    }
}

void struct__FuturemultiMatrix_free(struct _FuturemultiMatrix *this) {
    if (this != 0) {
        free((void *)this);
        this = (struct _FuturemultiMatrix *)(void *)0;
    }
}

struct __Trait_Future_Vtable_struct_Void __Trait_Future_VtablemultiMatrix = {(struct PollResult_struct_Void (*)(void *))struct__FuturemultiMatrix_poll, (void (*)(void *))struct__FuturemultiMatrix_free};

struct __Trait_Future_struct_Void __multiMatrix(int (*matrix1)[50], int (*matrix2)[50], int (*result)[50]) {
    struct _FuturemultiMatrix *data = calloc(1, sizeof(struct _FuturemultiMatrix));
    if (data == 0) {
        exit(1);
    }
    data->matrix1 = matrix1;
    data->matrix2 = matrix2;
    data->result = result;
    data->__future_state = 0;
    struct __Trait_Future_struct_Void fp = {(void *)data, &__Trait_Future_VtablemultiMatrix};
    return fp;
}

struct __Trait_Future_struct_Void __matrixCalculation(void);

struct PollResult_struct_Void struct__FuturematrixCalculation_poll(struct _FuturematrixCalculation *this) {
    switch (this->__future_state) {
      case 0:
        goto __L0;
      case 1:
        goto __L1;
      case 2:
        goto __L2;
      case 3:
        goto __L3;
      case 4:
        goto __L4;
    }
  __L0:
    ;
    unsigned long start, end;
    start = read_tsc();
    char str[52];
    int matrix1[50][50];
    int matrix2[50][50];
    int result[50][50];
    char buffer[1024] = {0};
    char *__ASSIGNED_ARRAY_PTR_char = (char *)buffer;
    char *__ARRAY_PTR_char = (char *)this->buffer;
    for (int I = 0; I < 1024; ++I) {
        *__ARRAY_PTR_char++ = *__ASSIGNED_ARRAY_PTR_char++;
    }
    __ARRAY_PTR_char = /*implicit*/(char *)0;
    end = read_tsc();
    g_noise.businessCost = end - start;
    this->Ft_1 = __createMatrix(this->matrix1);
  __L1:
    ;
    struct Void Res_1;
    struct PollResult_struct_Void PR_1 = this->Ft_1.vtable->poll(this->Ft_1.data);
    if (struct_PollResult_struct_Void_is_completed(&PR_1, &Res_1)) {
        if (this->Ft_1.data != 0) {
            this->Ft_1.vtable->free(this->Ft_1.data);
            this->Ft_1.data = (void *)0;
        }
    } else {
        this->__future_state = 1;
        return struct_PollResult_struct_Void_pending();
    }
    Res_1;
    this->Ft_2 = __createMatrix(this->matrix2);
  __L2:
    ;
    struct Void Res_2;
    struct PollResult_struct_Void PR_2 = this->Ft_2.vtable->poll(this->Ft_2.data);
    if (struct_PollResult_struct_Void_is_completed(&PR_2, &Res_2)) {
        if (this->Ft_2.data != 0) {
            this->Ft_2.vtable->free(this->Ft_2.data);
            this->Ft_2.data = (void *)0;
        }
    } else {
        this->__future_state = 2;
        return struct_PollResult_struct_Void_pending();
    }
    Res_2;
    this->Ft_3 = __multiMatrix(this->matrix1, this->matrix2, this->result);
  __L3:
    ;
    struct Void Res_3;
    struct PollResult_struct_Void PR_3 = this->Ft_3.vtable->poll(this->Ft_3.data);
    if (struct_PollResult_struct_Void_is_completed(&PR_3, &Res_3)) {
        if (this->Ft_3.data != 0) {
            this->Ft_3.vtable->free(this->Ft_3.data);
            this->Ft_3.data = (void *)0;
        }
    } else {
        this->__future_state = 3;
        return struct_PollResult_struct_Void_pending();
    }
    Res_3;
    start = read_tsc();
    this->file = fopen("./matrix.txt", "w");
    if (this->file == ((void *)0)) {
        perror("error opening file\n");
        fclose(this->file);
    }
    this->k = 0;
    end = read_tsc();
    g_noise.businessCost = end - start;
    for (this->i = 0; this->i < 50; this->i++) {
        start = read_tsc();
        for (this->j = 0; this->j < 50; this->j++) {
            this->k += sprintf(&this->str[this->k], "%d ", this->result[this->i][this->j]);
        }
        this->str[this->k++] = '\x00';
        end = read_tsc();
        g_noise.businessCost = end - start;
        this->Ft_4 = fileWriter(this->file, this->buffer);
      __L4:
        ;
        struct Void Res_4;
        struct PollResult_struct_Void PR_4 = struct_FileWriter_poll(&this->Ft_4);
        if (struct_PollResult_struct_Void_is_completed(&PR_4, &Res_4)) {
            struct_FileWriter_free(&this->Ft_4);
        } else {
            this->__future_state = 4;
            return struct_PollResult_struct_Void_pending();
        }
        Res_4;
        this->k = 0;
    }
    end = read_tsc();
    g_noise.businessCost = end - start;
    struct_Scheduler_destroy();
    {
        this->__future_state = -1;
        struct Void __RES_RETURN = (struct Void){};
        return struct_PollResult_struct_Void_completed(__RES_RETURN);
    }
}

void struct__FuturematrixCalculation_free(struct _FuturematrixCalculation *this) {
    if (this->Ft_3.data != 0) {
        this->Ft_3.vtable->free(this->Ft_3.data);
        this->Ft_3.data = (void *)0;
    }
    if (this->Ft_2.data != 0) {
        this->Ft_2.vtable->free(this->Ft_2.data);
        this->Ft_2.data = (void *)0;
    }
    if (this->Ft_1.data != 0) {
        this->Ft_1.vtable->free(this->Ft_1.data);
        this->Ft_1.data = (void *)0;
    }
    if (this != 0) {
        free((void *)this);
        this = (struct _FuturematrixCalculation *)(void *)0;
    }
}

struct __Trait_Future_Vtable_struct_Void __Trait_Future_VtablematrixCalculation = {(struct PollResult_struct_Void (*)(void *))struct__FuturematrixCalculation_poll, (void (*)(void *))struct__FuturematrixCalculation_free};

struct __Trait_Future_struct_Void __matrixCalculation(void) {
    struct _FuturematrixCalculation *data = calloc(1, sizeof(struct _FuturematrixCalculation));
    if (data == 0) {
        exit(1);
    }
    data->__future_state = 0;
    struct __Trait_Future_struct_Void fp = {(void *)data, &__Trait_Future_VtablematrixCalculation};
    return fp;
}

int main(void) {
    NOISE_init(&g_noise);
    unsigned long start, end;
    start = read_tsc();
    struct_Scheduler_init(4);
    end = read_tsc();
    g_noise.initCost = end - start;
    struct_Scheduler_spawn(__matrixCalculation());
    struct_Scheduler_run();

    // 业务逻辑
    printf("matrixCalculation cost: %lu\n", g_noise.businessCost);

    // 协程基础设施
    printf("scheduler init cost: %lu\n", g_noise.initCost); // 初始化调度器
    printf("scheduler init future cost: %lu\n", g_noise.initFutureCost); // 初始化 Future 对象
    if (g_noise.createTaskCount > 0)
        printf("scheduler creat async task cost: %lu\n",g_noise.createTaskCost / g_noise.createTaskCount); // 创建异步任务
    if (g_noise.freeCount > 0)
        printf("scheduler free cost: %lu\n", g_noise.freeCost / g_noise.freeCount); // 销毁任务
    if (g_noise.pushCount > 0)
        printf("scheduler push cost: %lu\n", g_noise.pushCost / g_noise.pushCount); // 入队
    if (g_noise.popCount > 0)
        printf("scheduler pop cost: %lu\n", g_noise.popCost / g_noise.popCount); // 出队
    if (g_noise.businessCost > 0)
        printf("scheduler poll cost: %lu\n", g_noise.pollCost - g_noise.businessCost); // 业务逻辑之外的开销（上下文切换等）

    // 调度策略
    if (g_noise.getTaskCount > 0 && g_noise.popCount > 0)
        printf("scheduler get task cost: %lu\n", (g_noise.getTaskCost / g_noise.getTaskCount) - (g_noise.popCost / g_noise.popCount));
    return 0;
}

static struct PollResult_struct_Void struct_PollResult_struct_Void_pending(void) {
    struct PollResult_struct_Void this;
    this.isPending = 1;
    return this;
}

static _Bool struct_PollResult_struct_Void_is_completed(struct PollResult_struct_Void *this, struct Void *out) {
    *out = this->res;
    return !this->isPending;
}

static struct PollResult_struct_Void struct_PollResult_struct_Void_completed(struct Void result) {
    struct PollResult_struct_Void this;
    this.isPending = 0;
    this.res = result;
    return this;
}




