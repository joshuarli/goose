# Repository conventions

## Goose source formatting

- Format each added or modified `.goose` file with `python scripts/format_goose.py <files>` before finishing a change. This is an exception to the general rule against running formatters; do not run other formatters.
- Check the result with `python scripts/format_goose.py --check <files>`.
- Keep deliberately malformed parser fixtures in `test/errors/` as written. Their source layout and diagnostics are part of the test.
- Use descriptive names and blank lines between distinct parts of a test. Formatting does not replace making the code understandable.
- Apply formatting to files being changed rather than rewriting the whole repository. The fork's formatting workflow enforces added and modified files.

## Upstream pull requests

- Use titles such as `fix(parser): describe the behavior` or `fix(typecheck): describe the behavior` for fixes.
- Write descriptions with `## What`, `## Why`, `## How`, and `## Testing`, in that order. Keep each section short and concrete.
- Keep reproducer prose to the observed before/after result, one environment record, and the run command. Put the minimal tested Dockerfile in a single collapsed Reproduce block; avoid repeating revisions, flags, setup instructions, or background already evident in the code.
- Describe the observable failure and resulting behavior before implementation details.
- Report checks actually run. Claim a regression fails before the fix and passes afterward only when that comparison has been verified.
- A fix for pathological input must also preserve performance on common input. Measure representative valid workloads and normal workloads that exercise the changed path against the exact base revision before recommending the change.
- Use identical compiler/build flags and inputs, warm up both versions, and alternate repeated measurements. Report timing, peak memory when allocation changes, sample counts, and variability; do not infer normal-case performance from a pathological regression alone.
- Include real before/after measurements, the commands and workload sizes, and their limits in the PR's Testing section. Surface regressions and explain any tradeoff; do not describe a change as performance-neutral without evidence.
- Before opening a draft PR, run its exact Docker reproducer locally and verify both the expected baseline failure and the fixed behavior. A draft is not an exception to verification. If the reproducer cannot run, report the blocker before opening the PR.
- Record the actual compiler name/version, musl or glibc version, architecture, and kernel from `uname`, together with build/runtime flags. Thread that environment through the test and performance results rather than implying that different environments are interchangeable.
- Use Clang 23 explicitly for local upstream-fix verification, on a current Ubuntu or Debian image that packages it. Installing an unversioned `clang` package does not establish the tested compiler version.
- Include a self-contained Dockerfile and exact build/run commands in the PR description only. Pin its base image by digest and source revisions, assert the expected failure and fixed result, and print the toolchain/libc/kernel used. Docker uses the host kernel, so the maintainer's kernel may differ from the recorded test kernel.
- Use shell for Docker reproducers. Do not add Python or a general benchmark harness when shell commands can demonstrate the failure and fix.
- Keep fork tooling out of upstream fix branches.
- Do not git push.
