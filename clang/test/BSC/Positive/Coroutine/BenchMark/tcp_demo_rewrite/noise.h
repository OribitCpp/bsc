#include <stdint.h>

typedef struct {
  uint64_t initCost;
  uint64_t createTaskCost;
  uint64_t createTaskCount;
  uint64_t pushCost;
  uint64_t pushCount;
  uint64_t popCost;
  uint64_t popCount;
  uint64_t pollCost;
  uint64_t getTaskCost;
  uint64_t getTaskCount;
  uint64_t freeCost;
  uint64_t freeCount;
  uint64_t businessCost;
  uint64_t initFutureCost;
}NOISE;

uint64_t read_tsc();

void NOISE_init(NOISE *this);

