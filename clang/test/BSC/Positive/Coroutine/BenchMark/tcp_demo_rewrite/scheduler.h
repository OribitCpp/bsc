#ifndef BISHENG_C_SCHEDULER_H
#define BISHENG_C_SCHEDULER_H

#include <stdatomic.h>
#include <time.h>
#include "future.h"
#include "queue.h"

struct Void {};

enum State {
    READY,
    PARKED,
    RUNNING,
    COMPLETED
};

int taskCount();

void taskAddOne();

void struct_Scheduler_init(unsigned int threadCount);

void struct_Scheduler_run(void);

void struct_Scheduler_destroy(void);



#endif