static void gs_test_aligned(int64_t *value) {
    if ((uintptr_t)value % _Alignof(int64_t)) abort();
}
