// RUN: %clang_cc1 -fsyntax-only -verify %s
// expected-no-diagnostics

#include "noise.h"

uint64_t read_tsc() {
    uint32_t start, end;
    __asm__ __volatile__("rdtsc" : "=a" (start), "=d" (end));
    return ((uint64_t)end << 32) | start;
}

void NOISE_init(NOISE *this) {
    this->initCost = 0;
    this->createTaskCost = 0;
    this->createTaskCount = 0;
    this->pushCost = 0;
    this->pushCount = 0;
    this->popCost = 0;
    this->popCount = 0;
    this->pollCost = 0;
    this->getTaskCost = 0;
    this->getTaskCount = 0;
    this->freeCost = 0;
    this->businessCost = 0;
    this->initFutureCost = 0;
}

