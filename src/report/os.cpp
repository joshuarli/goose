// Goose compiler — the platform half of the build report: the process's
// peak resident memory. A translation unit of its own, as process.cpp is, so
// that the platform headers stay out of the compiler's.

#include "../includes.h"

#ifdef _WIN32
    #define WIN32_LEAN_AND_MEAN
    #define NOMINMAX
    #include <windows.h>
    #include <psapi.h>
#else
    #include <sys/resource.h>
#endif

namespace goose {

long long ReportPeakRssBytes() {
    #ifdef _WIN32
        PROCESS_MEMORY_COUNTERS counters;
        if (!GetProcessMemoryInfo(GetCurrentProcess(), &counters, sizeof counters)) return -1;
        return (long long)counters.PeakWorkingSetSize;
    #else
        struct rusage usage;
        if (getrusage(RUSAGE_SELF, &usage) != 0) return -1;
        // Linux counts kilobytes, macOS bytes.
        #ifdef __APPLE__
            return (long long)usage.ru_maxrss;
        #else
            return (long long)usage.ru_maxrss * 1024;
        #endif
    #endif
}

}  // namespace goose
