#ifdef __GNUC__
#define BSC_LIKELY(x) __builtin_expect(!!(x), 1)
#define BSC_UNLIKELY(x) __builtin_expect(!!(x), 0)
#else
#define BSC_LIKELY(x) (x)
#define BSC_UNLIKELY(x) (x)
#endif
