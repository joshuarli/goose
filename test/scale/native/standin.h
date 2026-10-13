/* The C side of standin.goose, written the way a program with a lot of C of
   its own writes it: for the single-file form, in which the runtime's text
   is in the same translation unit. It reads the runtime's internal state,
   guards against the separate-runtime forms, defines `static` functions that
   the program calls as `extern fn`, and spells a compiler-generated type by
   its single-file name. */
#if defined(GS_SEPARATE_RUNTIME) || defined(GS_RUNTIME_OBJECT)
#error "standin.h needs the runtime implementation in its translation unit"
#endif

/* gs_errmsgs is a static table of the runtime's implementation. */
static int64_t standin_runtime_messages(void) {
    return (int64_t)(sizeof gs_errmsgs / sizeof gs_errmsgs[0]);
}

/* A slice of a struct of the program's, by its generated name. */
static int64_t standin_sum(sl_Point_g points) {
    int64_t sum = 0;
    for (int64_t i = 0; i < points.len; i++) sum += points.data[i].x_g * 10 + points.data[i].y_g;
    return sum;
}

/* A struct through a reference, as a pointer. */
static void standin_scale(Point_g *p, int64_t k) {
    p->x_g *= k;
    p->y_g *= k;
}
