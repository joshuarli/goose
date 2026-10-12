/* Goose runtime: what only unit output needs, after runtime.h. The one
   header every unit includes. */
#pragma once

#if defined(__GNUC__) || defined(__clang__)
#define GS_HIDDEN __attribute__((visibility("hidden")))
#else
#define GS_HIDDEN
#endif

/* One entry of a function's table of diagnostic locations: the file and the
   line a check in the function reports. */
typedef struct { const char *f; int l; } gs_loc_t;
