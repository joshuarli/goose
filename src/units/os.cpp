// Goose compiler — the platform half of `goose build --units`: holding what
// the compile prints, so that a build that runs nothing can print it again. A
// translation unit of its own so that the platform headers stay out of the
// compiler's.

#include "../includes.h"

#ifndef _WIN32
    #include <fcntl.h>
    #include <unistd.h>
#endif

namespace goose {

#ifndef _WIN32
static int saved_out = -1, saved_err = -1;
#endif

// Sends this process's standard output and standard error to the two files,
// whatever writes them, until OutputCaptureStop. False where that cannot be
// done, which is on Windows.
bool OutputCaptureStart(const string &out, const string &err) {
#ifdef _WIN32
    (void)out;
    (void)err;
    return false;
#else
    fflush(stdout);
    fflush(stderr);
    auto fo = open(out.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
    auto fe = open(err.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fo < 0 || fe < 0) {
        if (fo >= 0) close(fo);
        if (fe >= 0) close(fe);
        return false;
    }
    saved_out = dup(1);
    saved_err = dup(2);
    dup2(fo, 1);
    dup2(fe, 2);
    close(fo);
    close(fe);
    return true;
#endif
}

void OutputCaptureStop() {
#ifndef _WIN32
    if (saved_out < 0) return;
    fflush(stdout);
    fflush(stderr);
    dup2(saved_out, 1);
    dup2(saved_err, 2);
    close(saved_out);
    close(saved_err);
    saved_out = saved_err = -1;
#endif
}

}  // namespace goose
