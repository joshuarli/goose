#define _GNU_SOURCE
#include "runtime.h"
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <linux/mman.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/wait.h>
#include <unistd.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error region_nohuge_requires_linux_x86_64
#endif

static const size_t page_bytes = 4096, huge_bytes = 2097152;
static const size_t usable_bytes = 2147483648ULL, guard_bytes = 1048576;
static size_t base_modulo, advice_bytes;
static uint8_t *reservation;
static size_t reservation_bytes;
static int advice_calls, fail_advice, fail_release;

static void check(int ok, const char *operation) {
    if (ok) return;
    fprintf(stderr, "region policy check failed: %s (errno=%d)\n", operation, errno);
    if (reservation) munmap(reservation, reservation_bytes);
    exit(2);
}

static void *positioned_mmap(void *address, size_t size, int prot, int flags,
                             int fd, off_t offset) {
    check(!reservation && !address && size == usable_bytes + guard_bytes,
          "one complete runtime reservation");
    uint8_t *raw = mmap(address, size + huge_bytes, prot, flags, fd, offset);
    if (raw == MAP_FAILED) return MAP_FAILED;
    size_t prefix = (base_modulo + huge_bytes - (uintptr_t)raw % huge_bytes) % huge_bytes;
    if (prefix) check(!munmap(raw, prefix), "trim reservation prefix");
    uint8_t *base = raw + prefix;
    size_t suffix = huge_bytes - prefix;
    check(!munmap(base + size, suffix), "trim reservation suffix");
    reservation = base;
    reservation_bytes = size;
    return base;
}

static int observed_madvise(void *address, size_t size, int advice) {
    check(address == reservation && advice == MADV_NOHUGEPAGE,
          "runtime advises its reservation");
    advice_calls++;
    advice_bytes = size;
    if (fail_advice) { errno = EINVAL; return -1; }
    return madvise(address, size, advice);
}

static int observed_munmap(void *address, size_t size) {
    check(address == reservation && size == reservation_bytes,
          "release complete reservation including guard");
    if (fail_release) {
        check(write(STDOUT_FILENO, "UNMAP_FAILED\n", 13) == 13, "report injected release failure");
        errno = EBUSY;
        return -1;
    }
    int result = munmap(address, size);
    if (!result) {
        unsigned char resident;
        errno = 0;
        check(mincore(address, page_bytes, &resident) == -1 && errno == ENOMEM,
              "reservation is unmapped before error reporting");
        reservation = NULL;
        if (fail_advice)
            check(write(STDOUT_FILENO, "UNMAPPED\n", 9) == 9, "report advice failure cleanup");
    }
    return result;
}

#define mmap positioned_mmap
#define madvise observed_madvise
#define munmap observed_munmap
#include "runtime_impl.h"
#undef mmap
#undef madvise
#undef munmap

struct backing {
    size_t resident, present, swapped;
    unsigned long rss, dirty, anonymous, huge, swap;
    int nohuge;
};

static struct backing observe(uint8_t *window) {
    struct backing result = {0};
    unsigned char pages[512];
    uint64_t entries[512];
    check(!mincore(window, huge_bytes, pages), "observe residency");
    int fd = open("/proc/self/pagemap", O_RDONLY | O_CLOEXEC);
    check(fd >= 0, "open pagemap");
    check(pread(fd, entries, sizeof entries, (off_t)((uintptr_t)window / page_bytes * 8)) ==
          (ssize_t)sizeof entries, "read every pagemap entry");
    check(!close(fd), "close pagemap");
    for (size_t i = 0; i < 512; ++i) {
        result.resident += (pages[i] & 1) != 0;
        result.present += (entries[i] >> 63) & 1;
        result.swapped += (entries[i] >> 62) & 1;
    }
    FILE *maps = fopen("/proc/self/smaps", "r");
    check(maps != NULL, "open smaps");
    char *line = NULL;
    size_t capacity = 0;
    int selected = 0, seen = 0, fields = 0;
    while (getline(&line, &capacity, maps) >= 0) {
        unsigned long lo, hi, value;
        if (sscanf(line, "%lx-%lx", &lo, &hi) == 2) {
            selected = lo <= (uintptr_t)window && hi >= (uintptr_t)window + huge_bytes;
            seen += selected;
        } else if (selected) {
            if (sscanf(line, "Rss: %lu kB", &value) == 1) {result.rss = value; fields |= 1;}
            else if (sscanf(line, "Private_Dirty: %lu kB", &value) == 1) {result.dirty = value; fields |= 2;}
            else if (sscanf(line, "Anonymous: %lu kB", &value) == 1) {result.anonymous = value; fields |= 4;}
            else if (sscanf(line, "AnonHugePages: %lu kB", &value) == 1) {result.huge = value; fields |= 8;}
            else if (sscanf(line, "Swap: %lu kB", &value) == 1) {result.swap = value; fields |= 16;}
            else if (!strncmp(line, "VmFlags:", 8)) {result.nohuge = strstr(line, " nh") != NULL; fields |= 32;}
        }
    }
    check(!ferror(maps) && seen == 1 && fields == 63, "complete target VMA accounting");
    free(line);
    check(!fclose(maps), "close smaps");
    return result;
}

static void verify_guard(uint8_t *base) {
    FILE *maps = fopen("/proc/self/maps", "r");
    check(maps != NULL, "open guard map");
    char *line = NULL;
    size_t capacity = 0;
    int guarded = 0;
    while (getline(&line, &capacity, maps) >= 0) {
        unsigned long lo, hi;
        char access[5];
        if (sscanf(line, "%lx-%lx %4s", &lo, &hi, access) == 3 &&
            lo <= (uintptr_t)base + usable_bytes && hi >= (uintptr_t)base + reservation_bytes)
            guarded = !strncmp(access, "---", 3);
    }
    check(!ferror(maps) && guarded, "guard gap remains inaccessible");
    free(line);
    check(!fclose(maps), "close guard map");
}

static void geometry(const char *name, size_t modulo, size_t cursor, size_t expected) {
    base_modulo = modulo;
    check(prctl(PR_GET_THP_DISABLE, 0, 0, 0, 0) == 0, "initial process THP setting");
    check(!prctl(PR_SET_THP_DISABLE, 1, 0, 0, 0), "disable THP during sparse setup");
    uint8_t *base = gs_os_reserve(usable_bytes, usable_bytes + guard_bytes);
    check(base != NULL && (uintptr_t)base % huge_bytes == modulo, "runtime reserves positioned region");
    uintptr_t end = (uintptr_t)base + cursor;
    uint8_t *window = (uint8_t *)((end + huge_bytes - 1) / huge_bytes * huge_bytes - huge_bytes);
    size_t payload = expected == 512 ? huge_bytes : end - (uintptr_t)window;
    check(window >= base + huge_bytes && window + huge_bytes <= base + usable_bytes,
          "target is beyond the old protected prefix");
    memset(window, 0x5a, payload);
    gs_stack stack = {expected == 512 ? base : base + cursor};
    check(!prctl(PR_SET_THP_DISABLE, 0, 0, 0, 0), "restore process THP setting");
    verify_guard(base);
    struct backing before = observe(window);
    check(before.resident == expected && before.present == expected && !before.swapped &&
          !before.swap && !before.huge, "exact sparse or resident precondition");
    errno = 0;
    int collapsed = madvise(window, huge_bytes, MADV_COLLAPSE);
    int collapse_errno = errno;
    struct backing after = observe(window);
    printf("case=%s before=%zu after=%zu rss_delta_KiB=%ld huge_before_KiB=%lu "
           "huge_after_KiB=%lu advice_bytes=%zu logical_used=%zu collapse=%d errno=%d\n", name,
           before.present, after.present, (long)after.rss - (long)before.rss,
           before.huge, after.huge, advice_bytes, (size_t)(stack.top - base), collapsed, collapse_errno);
    check(advice_calls == 1 && advice_bytes == usable_bytes && before.nohuge && after.nohuge,
          "complete usable region excludes huge pages");
    check(collapsed == -1 && collapse_errno == EINVAL, "no-huge mapping rejects collapse");
    check(after.present == expected && after.resident == expected && !after.swapped &&
          !after.huge && !after.swap && before.rss == after.rss && before.dirty == after.dirty &&
          before.anonymous == after.anonymous, "collapse preserves sparse backing");
    check(stack.top == (expected == 512 ? base : base + cursor), "backing policy preserves stack cursor");
    for (size_t i = 0; i < payload; ++i) check(window[i] == 0x5a, "payload remains intact");
    base[0] = 17;
    base[usable_bytes - 1] = 23;
    check(base[0] == 17 && base[usable_bytes - 1] == 23, "usable boundaries stay writable");
    gs_region region = {base, usable_bytes, usable_bytes + guard_bytes};
    gs_release_region(&region);
    check(!reservation, "normal runtime release owns the complete mapping");
}

static void advice_error(int release_error) {
    int output[2];
    check(!pipe(output), "create child diagnostic pipe");
    pid_t child = fork();
    check(child >= 0, "fork advice failure control");
    if (!child) {
        close(output[0]);
        check(dup2(output[1], STDOUT_FILENO) >= 0 && dup2(output[1], STDERR_FILENO) >= 0,
              "capture runtime failure");
        close(output[1]);
        fail_advice = 1;
        fail_release = release_error;
        gs_os_reserve(usable_bytes, usable_bytes + guard_bytes);
        _exit(3);
    }
    check(!close(output[1]), "close parent pipe writer");
    char text[1024];
    size_t used = 0;
    for (;;) {
        ssize_t count = read(output[0], text + used, sizeof text - used - 1);
        if (count < 0 && errno == EINTR) continue;
        check(count >= 0, "read runtime failure");
        if (!count) break;
        used += (size_t)count;
        check(used < sizeof text - 1, "bounded runtime diagnostic");
    }
    text[used] = 0;
    check(!close(output[0]), "close diagnostic pipe");
    int status;
    pid_t waited;
    do {waited = waitpid(child, &status, 0);} while (waited < 0 && errno == EINTR);
    check(waited == child && WIFEXITED(status) && WEXITSTATUS(status) == 1,
          "advice failure terminates before publishing a reservation");
    check(strstr(text, "goose runtime error: cannot disable huge pages for data stack") != NULL,
          "advice failure names the required policy");
    check(strstr(text, release_error ? "UNMAP_FAILED\n" : "UNMAPPED\n") != NULL,
          "advice failure attempts complete cleanup");
    if (release_error) check(strstr(text, "cannot release") != NULL, "cleanup failure preserves both errors");
    printf("PASS advice-error release_error=%d child_closed=1\n", release_error);
}

int main(int argc, char **argv) {
    check(argc == 2 && sysconf(_SC_PAGESIZE) == (long)page_bytes, "case and 4096-byte pages");
    if (!strcmp(argv[1], "sparse389")) geometry(argv[1], 1536000, 268491405, 389);
    else if (!strcmp(argv[1], "sparse485")) geometry(argv[1], 487424, 62315764, 485);
    else if (!strcmp(argv[1], "resident-zero")) geometry(argv[1], 753664, 62315764, 512);
    else if (!strcmp(argv[1], "advice-error")) advice_error(0);
    else if (!strcmp(argv[1], "cleanup-error")) advice_error(1);
    else if (!strcmp(argv[1], "smaps")) {
        uint8_t *base = gs_os_reserve(usable_bytes, usable_bytes + guard_bytes);
        check(base != NULL, "reserve arena for the existing program checker");
        puts("ready");
        fflush(stdout);
        check(getchar() == '\n', "program checker releases the arena");
        gs_region region = {base, usable_bytes, usable_bytes + guard_bytes};
        gs_release_region(&region);
    }
    else check(0, "known case");
    puts("PASS region no-huge policy");
    return 0;
}
