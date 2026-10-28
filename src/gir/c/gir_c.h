// Goose compiler — the C emitter for GIR-L.
//
// Consumes a verified low module and nothing else: it does not look at the
// AST or call the legacy code generator. One statement is written per
// instruction, in order, and none relies on the order C evaluates the
// arguments of a call. Signed arithmetic wraps through unsigned arithmetic;
// where an operation is checked (the debug profile's overflow and `as` range
// checks, division) the runtime's own helpers are called, so the program
// behaves as the legacy backend's does when GS_DEBUG is defined and when it
// is not, and a failure names the same file and line.
//
// Each function's text is a piece of its own, with what it refers to
// recorded (callees, files, globals), so that a later partitioning can take
// pieces; this emitter assembles them into one file.
#pragma once

namespace goose {

// The runtime entry points the emitted C calls, and every one of them: a
// reader of the emitter's output meets nothing else of the runtime's.
//   data stacks     gs_rt_init, gs_stack_init, GS(i), gs_memcpy, gs_memmove, gs_rt_stats
//   aborts          gs_abort (GS_E_SLICE, GS_E_ASSERT), gs_abort_msg, gs_idxfail, gs_exit
//   checked ints    gs_add_*, gs_sub_*, gs_mul_*, gs_neg_*, gs_div_*, gs_mod_*, gs_shl_*, gs_shr_*,
//                   GS_RANGE, GS_RANGE_U
inline constexpr const char *GIR_C_RUNTIME_ENTRY_POINTS =
    "gs_rt_init gs_stack_init GS gs_memcpy gs_memmove gs_rt_stats "
    "gs_out_bytes gs_fmt_i64 gs_fmt_u64 gs_fmt_bool gs_abort gs_abort_msg gs_idxfail gs_exit gs_add gs_sub gs_mul gs_neg "
    "gs_div gs_mod gs_shl gs_shr GS_RANGE GS_RANGE_U";

// One function's text with what it refers to.
struct GirCPiece {
    string name;
    string prototype;
    string text;
    vector<int> callees;
    vector<int> files;
};

struct GirCProgram {
    string head;      // Types, after the runtime's declarations.
    string result;    // Everything else, ending in `main`.
    vector<GirCPiece> pieces;
    UnitSource unit;  // The same program as the unit assembler reads it.
};

class GirCEmitter {
public:
    explicit GirCEmitter(const GirModule &low, optional<string> constructionTrace = nullopt)
        : m(low), constructionTrace(std::move(constructionTrace)) {}

    GirCProgram Emit() {
        if (constructionTrace && (!CoreHasConstruction(m.profile) || constructionTrace->empty() ||
                                  constructionTrace->find('\0') != string::npos))
            throw CompileError { "construction trace requires the construction profile and a valid file path" };
        Names();
        GirCProgram out;
        for (size_t f = 0; f < m.funcs.size(); f++) out.pieces.push_back(Piece((int)f));
        // The sections, in the conventions the unit assembler splits them by.
        string tdecls = "typedef struct { uint8_t *base; int64_t len; } gir_hdr;\n";
        if (CoreHasConstruction(m.profile))
            Append(tdecls, "typedef char gir_pointer_bytes_check[(sizeof(void *) == ", m.pointerBytes,
                   ") ? 1 : -1];\n");
        for (auto size : blobs) Append(tdecls, "typedef struct { uint64_t w[", (size + 7) / 8, "]; } gir_blob_", size, ";\n");
        UnitProgramSupport support;
        if (CoreHasConstruction(m.profile)) {
            support.State("GS_TLS int64_t gir_return_flag;\n");
            for (size_t target = 0; target < m.lowtargets.size(); target++)
                for (size_t cell = 0; cell < m.lowtargets[target].cells.size(); cell++)
                    support.State(cat("GS_TLS ", CT(m.lowtargets[target].cells[cell]), " gir_target_", target, "_", cell, ";\n"));
            support.State("GS_TLS gs_stack **gir_stack_cells;\n");
            support.State("GS_TLS size_t gir_stack_capacity;\n");
            support.Function("gs_stack *gir_stack_at(int64_t base, int64_t offset)", R"GIRSUPPORT({ if (base < 0 || offset < 0 || base > INT64_MAX - offset) gs_panic("invalid construction stack base"); int64_t index = base + offset; if ((uint64_t)index >= SIZE_MAX / sizeof(gs_stack *)) gs_panic("invalid construction stack index"); size_t needed = (size_t)index + 1; if (needed > gir_stack_capacity) { size_t capacity = gir_stack_capacity ? gir_stack_capacity : 8; while (capacity < needed) { if (capacity > SIZE_MAX / sizeof(gs_stack *) / 2) gs_panic("construction stack directory overflow"); capacity *= 2; } gs_stack **cells = (gs_stack **)realloc(gir_stack_cells, capacity * sizeof(gs_stack *)); if (!cells) gs_panic("out of memory allocating construction stacks"); memset(cells + gir_stack_capacity, 0, (capacity - gir_stack_capacity) * sizeof(gs_stack *)); gir_stack_cells = cells; gir_stack_capacity = capacity; } if (!gir_stack_cells[index]) { gir_stack_cells[index] = (gs_stack *)malloc(sizeof(gs_stack)); if (!gir_stack_cells[index]) gs_panic("out of memory allocating construction stack cell"); gs_stack_init(gir_stack_cells[index]); } return gir_stack_cells[index]; }
)GIRSUPPORT");
            support.Function("void gir_stack_cells_close(void)", R"GIRSUPPORT({ for (size_t index = 0; index < gir_stack_capacity; index++) free(gir_stack_cells[index]); free(gir_stack_cells); gir_stack_cells = NULL; gir_stack_capacity = 0; }
)GIRSUPPORT");
            if (constructionTrace) {
                support.State("FILE *gir_trace_file;\n");
                support.State("int gir_trace_comma;\n");
                support.State("int64_t gir_trace_storage, gir_trace_destination;\n");
                support.Function("void gir_trace_fail(void)", R"GIRSUPPORT({ perror("construction trace"); _Exit(74); }
)GIRSUPPORT");
                support.Forward("void gir_source_close(void);\n");
                support.Function("void gir_trace_close(void)", R"GIRSUPPORT({ gir_source_close(); if (fclose(gir_trace_file) != 0) gir_trace_fail(); gir_trace_file = NULL; }
)GIRSUPPORT");
                support.Function("void gir_trace_open(void)", cat("{ gir_trace_file = fopen(", CStr(*constructionTrace),
                       ", \"wb\"); if (!gir_trace_file) gir_trace_fail(); if (atexit(gir_trace_close) != 0) gir_trace_fail(); if (fputs(\"[\\\"construction\\\",[]]\\n\", gir_trace_file) < 0 || fflush(gir_trace_file) != 0) gir_trace_fail(); }\n"));
                support.Function("void gir_trace_record(const char *kind, const char *reason, size_t n, const int64_t *v)", R"GIRSUPPORT({ if (!gir_trace_file) return; if (fseek(gir_trace_file, -3, SEEK_END) != 0) gir_trace_fail(); if (gir_trace_comma && fputc(',', gir_trace_file) == EOF) gir_trace_fail(); gir_trace_comma = 1; if (fprintf(gir_trace_file, "[\"%s\"", kind) < 0) gir_trace_fail(); if (strcmp(kind, "copy") == 0) { if (fprintf(gir_trace_file, ",[\"%s\",%lld", reason, (long long)v[0]) < 0) gir_trace_fail(); if (strcmp(reason, "storage") == 0) { if (fputs(",[", gir_trace_file) < 0) gir_trace_fail(); for (size_t k = 1; k + 1 < n; k++) if (fprintf(gir_trace_file, "%s%lld", k > 1 ? "," : "", (long long)v[k]) < 0) gir_trace_fail(); if (fputc(']', gir_trace_file) == EOF) gir_trace_fail(); } if (fprintf(gir_trace_file, "],%lld", (long long)v[n - 1]) < 0) gir_trace_fail(); } else { for (size_t k = 0; k < n; k++) if (fprintf(gir_trace_file, ",%lld", (long long)v[k]) < 0) gir_trace_fail(); if (*reason && fprintf(gir_trace_file, ",\"%s\"", reason) < 0) gir_trace_fail(); } if (fputc(']', gir_trace_file) == EOF || fputs("]]\n", gir_trace_file) < 0 || fflush(gir_trace_file) != 0) gir_trace_fail(); }
)GIRSUPPORT");
                support.Space("\n");
                support.Type(R"GIRSUPPORT(typedef struct gir_source { size_t refs, count; int64_t storage; int64_t path[]; } gir_source;
)GIRSUPPORT");
                support.Type(R"GIRSUPPORT(typedef struct gir_source_slot { uint8_t **value; struct gir_source_slot *next; } gir_source_slot;
)GIRSUPPORT");
                support.Type(R"GIRSUPPORT(typedef struct gir_source_scope { struct gir_source_scope *previous; gir_source_slot *slots; } gir_source_scope;
)GIRSUPPORT");
                support.Type(R"GIRSUPPORT(typedef struct gir_source_call { struct gir_source_call *previous; size_t count; gir_source **arguments, **results; } gir_source_call;
)GIRSUPPORT");
                support.State("GS_TLS gir_source_scope *gir_source_scope_top;\n");
                support.State("GS_TLS gir_source_call *gir_source_call_top;\n");
                support.State("gir_source **gir_global_sources;\n");
                support.State("size_t gir_global_sources_count;\n");
                support.Function("void *gir_source_alloc(size_t size)", R"GIRSUPPORT({ void *value = calloc(1, size); if (!value) gs_panic("out of memory recording construction provenance"); return value; }
)GIRSUPPORT");
                support.Function("void gir_source_retain(gir_source *source)", R"GIRSUPPORT({ if (source) { if (source->refs == SIZE_MAX) gir_trace_fail(); source->refs++; } }
)GIRSUPPORT");
                support.Function("void gir_source_release(gir_source *source)", R"GIRSUPPORT({ if (source && --source->refs == 0) free(source); }
)GIRSUPPORT");
                support.Function("void gir_source_assign(uint8_t **value, gir_source *source)", R"GIRSUPPORT({ if (!gir_source_scope_top) gir_trace_fail(); gir_source_slot *slot = gir_source_scope_top->slots; while (slot && slot->value != value) slot = slot->next; if (!slot) { slot = (gir_source_slot *)gir_source_alloc(sizeof(*slot)); slot->value = value; slot->next = gir_source_scope_top->slots; gir_source_scope_top->slots = slot; } gir_source_retain(source); gir_source_release((gir_source *)*value); *value = (uint8_t *)source; }
)GIRSUPPORT");
                support.Function("gir_source *gir_source_new(int64_t storage, size_t count, const int64_t *path)", R"GIRSUPPORT({ if (storage < 0 || count > (SIZE_MAX - sizeof(gir_source)) / sizeof(int64_t)) gir_trace_fail(); gir_source *source = (gir_source *)gir_source_alloc(sizeof(*source) + count * sizeof(int64_t)); source->storage = storage; source->count = count; for (size_t index = 0; path && index < count; index++) { if (path[index] < 0) gir_trace_fail(); source->path[index] = path[index]; } return source; }
)GIRSUPPORT");
                support.Function("gir_source *gir_source_child(gir_source *parent, int64_t index)", R"GIRSUPPORT({ if (!parent || index < 0 || parent->count == SIZE_MAX) gir_trace_fail(); gir_source *source = gir_source_new(parent->storage, parent->count + 1, NULL); if (parent->count) memcpy(source->path, parent->path, parent->count * sizeof(int64_t)); source->path[parent->count] = index; return source; }
)GIRSUPPORT");
                support.Function("uint8_t *gir_source_enter(void)", R"GIRSUPPORT({ gir_source_scope *scope = (gir_source_scope *)gir_source_alloc(sizeof(*scope)); scope->previous = gir_source_scope_top; gir_source_scope_top = scope; return (uint8_t *)scope; }
)GIRSUPPORT");
                support.Function("void gir_source_leave(uint8_t *token)", R"GIRSUPPORT({ gir_source_scope *scope = (gir_source_scope *)token; if (scope != gir_source_scope_top) gir_trace_fail(); while (scope->slots) { gir_source_slot *slot = scope->slots; scope->slots = slot->next; gir_source_release((gir_source *)*slot->value); *slot->value = NULL; free(slot); } gir_source_scope_top = scope->previous; free(scope); }
)GIRSUPPORT");
                support.Function("uint8_t *gir_source_call_push(size_t count, gir_source *const *arguments)", R"GIRSUPPORT({ gir_source_call *call = (gir_source_call *)gir_source_alloc(sizeof(*call)); call->previous = gir_source_call_top; call->count = count; call->arguments = (gir_source **)gir_source_alloc((count + 1) * sizeof(gir_source *)); call->results = (gir_source **)gir_source_alloc((count + 1) * sizeof(gir_source *)); for (size_t position = 1; position <= count; position++) { call->arguments[position] = arguments[position - 1]; gir_source_retain(arguments[position - 1]); } gir_source_call_top = call; return (uint8_t *)call; }
)GIRSUPPORT");
                support.Function("gir_source *gir_source_param(size_t position)", R"GIRSUPPORT({ gir_source_call *call = gir_source_call_top; if (!call || position == 0 || position > call->count || !call->arguments[position]) gir_trace_fail(); return call->arguments[position]; }
)GIRSUPPORT");
                support.Function("void gir_source_result(size_t position, gir_source *source)", R"GIRSUPPORT({ gir_source_call *call = gir_source_call_top; if (!call || position == 0 || position > call->count || !source) gir_trace_fail(); gir_source_retain(source); gir_source_release(call->results[position]); call->results[position] = source; }
)GIRSUPPORT");
                support.Function("gir_source *gir_source_call_get(uint8_t *token, size_t position)", R"GIRSUPPORT({ gir_source_call *call = (gir_source_call *)token; if (call != gir_source_call_top || position == 0 || position > call->count || !call->results[position]) gir_trace_fail(); return call->results[position]; }
)GIRSUPPORT");
                support.Function("void gir_source_call_pop(uint8_t *token)", R"GIRSUPPORT({ gir_source_call *call = (gir_source_call *)token; if (call != gir_source_call_top) gir_trace_fail(); for (size_t position = 1; position <= call->count; position++) { gir_source_release(call->arguments[position]); gir_source_release(call->results[position]); } gir_source_call_top = call->previous; free(call->arguments); free(call->results); free(call); }
)GIRSUPPORT");
                support.Function("void gir_source_close(void)", R"GIRSUPPORT({ if (gir_source_scope_top || gir_source_call_top) gir_trace_fail(); for (size_t position = 0; position < gir_global_sources_count; position++) gir_source_release(gir_global_sources[position]); free(gir_global_sources); }
)GIRSUPPORT");
                support.Function("void gir_source_global_set(size_t position, gir_source *source)", R"GIRSUPPORT({ gir_source_retain(source); gir_source_release(gir_global_sources[position]); gir_global_sources[position] = source; }
)GIRSUPPORT");
                support.Function("void gir_source_copy(gir_source *source, int64_t destination)", R"GIRSUPPORT({ if (!source || source->count > SIZE_MAX - 2) gir_trace_fail(); int64_t *values = (int64_t *)gir_source_alloc((source->count + 2) * sizeof(int64_t)); values[0] = source->storage; for (size_t index = 0; index < source->count; index++) values[index + 1] = source->path[index]; values[source->count + 1] = destination; gir_trace_record("copy", "storage", source->count + 2, values); free(values); }
)GIRSUPPORT");
                if (!m.lowtargets.empty()) {
                    support.Type(cat("#define GIR_SOURCE_TARGETS ", m.lowtargets.size(), "\n"));
                    support.Space("\n");
                    support.Type(R"GIRSUPPORT(typedef struct gir_source_target { struct gir_source_target *previous; gir_source_call *call; size_t target, count; int64_t *positions; gir_source **results; } gir_source_target;
)GIRSUPPORT");
                    support.State("GS_TLS gir_source_target *gir_source_targets[GIR_SOURCE_TARGETS];\n");
                    support.Function("uint8_t *gir_source_target_enter(size_t target, size_t count, const int64_t *positions)", R"GIRSUPPORT({ if (target >= GIR_SOURCE_TARGETS) gir_trace_fail(); gir_source_target *record = (gir_source_target *)gir_source_alloc(sizeof(*record)); record->previous = gir_source_targets[target]; record->call = gir_source_call_top; record->target = target; record->count = count; record->positions = (int64_t *)gir_source_alloc((count + 1) * sizeof(int64_t)); record->results = (gir_source **)gir_source_alloc((count + 1) * sizeof(gir_source *)); for (size_t position = 0; position < count; position++) record->positions[position] = positions[position]; gir_source_targets[target] = record; return (uint8_t *)record; }
)GIRSUPPORT");
                    support.Function("void gir_source_target_leave(uint8_t *token)", R"GIRSUPPORT({ gir_source_target *record = (gir_source_target *)token; if (!record || record->target >= GIR_SOURCE_TARGETS || gir_source_targets[record->target] != record) gir_trace_fail(); for (size_t position = 0; position < record->count; position++) gir_source_release(record->results[position]); gir_source_targets[record->target] = record->previous; free(record->positions); free(record->results); free(record); }
)GIRSUPPORT");
                    support.Function("void gir_source_target_result(size_t target, size_t position, gir_source *source)", R"GIRSUPPORT({ if (target >= GIR_SOURCE_TARGETS || !source) gir_trace_fail(); gir_source_target *record = gir_source_targets[target]; if (!record || position >= record->count || record->positions[position] < 1 || !record->call || (uint64_t)record->positions[position] > record->call->count) gir_trace_fail(); gir_source_retain(source); gir_source_release(record->results[position]); record->results[position] = source; size_t output = (size_t)record->positions[position]; gir_source_retain(source); gir_source_release(record->call->results[output]); record->call->results[output] = source; }
)GIRSUPPORT");
                    support.Function("gir_source *gir_source_target_get(uint8_t *token, size_t position)", R"GIRSUPPORT({ gir_source_target *record = (gir_source_target *)token; if (!record || record->target >= GIR_SOURCE_TARGETS || gir_source_targets[record->target] != record || position >= record->count || !record->results[position]) gir_trace_fail(); return record->results[position]; }
)GIRSUPPORT");
                }

            }
        }
        bool controls = false;
        for (auto &function : m.funcs) for (auto &block : function.blocks)
            for (auto &instruction : block.insts) if (GirControlOf(instruction.op)) controls = true;
        if (controls) ControlRuntime(support);
        string data = support.single;
        for (size_t i = 0; i < m.files.size(); i++)
            Append(data, "static const char ", filesym[i], "[] = ", CStr(i < m.diagfiles.size() ? m.diagfiles[i] : m.files[i]), ";\n");
        string gblock;
        for (size_t g = 0; g < m.lowglobals.size(); g++) {
            auto &lg = m.lowglobals[g];
            switch (lg.kind) {
                case GirMember::Scalar: Append(gblock, "    ", CT(lg.ty), " ", gsym[g], ";\n"); break;
                case GirMember::Bytes: Append(gblock, "    gir_blob_", lg.size, " ", gsym[g], ";\n"); break;
                case GirMember::Header: Append(gblock, "    gir_hdr ", gsym[g], ";\n    gs_stack gs_gstk_", gsym[g], ";\n"); break;
                case GirMember::Dynamic: Append(gblock, "    uint8_t *", gsym[g], ";\n    gs_stack gs_gstk_", gsym[g], ";\n"); break;
            }
        }
        if (!m.lowglobals.empty())
            Append(data, "typedef struct {\n", gblock, "} gs_globals_t;\nstatic gs_globals_t gs_globals_main;\n",
                   "#define GS_GL (&gs_globals_main)\n");
        data += "static int gs_program_initialized;\n";
        string pdata;
        for (auto &[text, name] : literals)
            Append(pdata, "static const uint8_t ", name, "[", text.size() ? text.size() : 1, "] = ", CStr(text), ";\n");
        string protos;
        for (auto &p : out.pieces) Append(protos, p.prototype, ";\n");
        string code;
        for (auto &p : out.pieces) Append(code, p.text, "\n");
        // Globals are initialized a module's run at a time, in declaration order.
        vector<pair<string, string>> inits;
        string initcode;
        for (size_t g = 0; g < m.lowglobals.size();) {
            auto module = m.lowglobals[g].module;
            auto to = g;
            while (to < m.lowglobals.size() && m.lowglobals[to].module == module) to++;
            auto name = cat("gs_init_", UnitSegmentId(module), "_", runs[module]++);
            inits.push_back({ module, name });
            Append(initcode, "static void ", name, "(void) {\n");
            for (auto k = g; k < to; k++) {
                if (m.lowglobals[k].kind == GirMember::Header || m.lowglobals[k].kind == GirMember::Dynamic)
                    Append(initcode, "    gs_stack_init(&GS_GL->gs_gstk_", gsym[k], ");\n");
                Append(initcode, "    ", FName(m.initfuncs[k]), "(0);\n");
            }
            initcode += "}\n\n";
            g = to;
        }
        auto program = [&](bool units) {
            string t = "static void gs_program_init(int argc, char **argv) {\n"
                       "    if (gs_program_initialized) return;\n";
            if (constructionTrace) {
                t += "    gir_trace_open();\n";
                Append(t, "    gir_global_sources_count = ", m.lowglobals.size(), ";\n");
                Append(t, "    gir_global_sources = (gir_source **)gir_source_alloc(", max<size_t>(1, m.lowglobals.size()), " * sizeof(gir_source *));\n");
            }
            if (CoreHasConstruction(m.profile)) t += "    if (atexit(gir_stack_cells_close) != 0) gs_panic(\"cannot register construction stack cleanup\");\n";
            if (CoreHasConstruction(m.profile))
                t += "    gs_rt_init(argc, argv, 0, GS_STACK_BUDGET / (GS_STACK_RESERVE + GS_STACK_GAP), 0);\n";
            else
                Append(t, "    gs_rt_init(argc, argv, ", m.mainstacks, ", ", m.mainstacks + m.globalstacks, ", 0);\n");
            if (units) {
                set<string> modules;
                for (auto &lg : m.lowglobals) modules.insert(lg.module);
                for (auto &module : modules)
                    Append(t, "    ", SegName(module), " = &", SegName(module), "_main;\n");
            } else if (!m.lowglobals.empty()) {
                t += "    gs_gl = &gs_globals_main;\n";
            }
            for (auto &[module, name] : inits) Append(t, "    ", name, "();\n");
            t += "    gs_program_initialized = 1;\n}\n\n";
            Append(t, "int main(int argc, char **argv) {\n    gs_program_init(argc, argv);\n    ", FName(m.entry),
                   "(0);\n    gs_rt_stats();\n    return 0;\n}\n");
            return t;
        };
        out.head = tdecls;
        Append(out.result, data, "\n", pdata, "\n/* ---- prototypes ---- */\n", protos, "\n/* ---- code ---- */\n",
               code, initcode, program(false));
        // For the unit assembler.
        auto &u = out.unit;
        u.tdecls = tdecls;
        u.data = data.substr(support.single.size());
        u.support = std::move(support);
        u.pdata = pdata;
        u.gblock = gblock;
        u.code = code + initcode + program(true);
        set<string> modules;
        for (size_t g = 0; g < m.lowglobals.size(); g++) {
            UnitGlobalNames n;
            n.module = m.lowglobals[g].module;
            n.texts = { cat("GS_GL->", gsym[g]) };
            if (m.lowglobals[g].kind == GirMember::Header || m.lowglobals[g].kind == GirMember::Dynamic)
                n.texts.push_back(cat("GS_GL->gs_gstk_", gsym[g]));
            u.globals.push_back(std::move(n));
            modules.insert(m.lowglobals[g].module);
        }
        u.segmodules.assign(modules.begin(), modules.end());
        u.unitinits = inits;
        for (size_t f = 0; f < m.funcs.size(); f++)
            u.functions[FName((int)f)] = { m.funcs[f].module.empty() ? string("?") : m.funcs[f].module, nullptr };
        u.segname = [](const string &module) { return SegName(module); };
        u.fail = [](const string &message) { throw CompileError { message }; };
        return out;
    }

private:
    void ControlRuntime(UnitProgramSupport &support) const {
        support.Type(cat("#define GIR_CONTROL_TARGET_COUNT ", m.lowtargets.size(), "\n"));
        support.Type(cat("enum { GIR_CONTROL_OPEN = ", (int64_t)GirConstructionProgress::Open, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_SUSPENDED = ", (int64_t)GirConstructionProgress::Suspended, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_BUILT = ", (int64_t)GirConstructionProgress::Built, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_PUBLISHED = ", (int64_t)GirConstructionProgress::Published, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_EXITING = ", (int64_t)GirConstructionProgress::Exiting, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_ABANDONED = ", (int64_t)GirConstructionProgress::Abandoned, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_CANCELLED = ", (int64_t)GirConstructionProgress::Cancelled, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_ATTACHED = ", (int64_t)GirConstructionProgress::Attached, " };\n"));
        support.Type(cat("enum { GIR_CONTROL_RETIRED = ", (int64_t)GirConstructionProgress::Retired, " };\n"));
        if (constructionTrace) {
            support.Function("int64_t gir_control_identity(void)", R"GIRSUPPORT({ return gir_trace_destination++; }
)GIRSUPPORT");
            support.Function("void gir_control_event(const char *name, int64_t identity)", R"GIRSUPPORT({ gir_trace_record(name, "", 1, &identity); }
)GIRSUPPORT");
            support.Function("void gir_control_stage(int64_t identity)", R"GIRSUPPORT({ gir_trace_record("stage", "capacity-check", 1, &identity); }
)GIRSUPPORT");
            support.Function("void gir_control_header_removal(int64_t identity)", R"GIRSUPPORT({ gir_trace_record("relocate", "header-removal", 1, &identity); }
)GIRSUPPORT");
        } else {
            support.Function("int64_t gir_control_identity(void)", R"GIRSUPPORT({ return 0; }
)GIRSUPPORT");
            support.Function("void gir_control_event(const char *name, int64_t identity)", R"GIRSUPPORT({ (void)name; (void)identity; }
)GIRSUPPORT");
            support.Function("void gir_control_stage(int64_t identity)", R"GIRSUPPORT({ (void)identity; }
)GIRSUPPORT");
            support.Function("void gir_control_header_removal(int64_t identity)", R"GIRSUPPORT({ (void)identity; }
)GIRSUPPORT");
        }
        support.Space("\n");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_graph gir_control_graph;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_receiving gir_control_receiving;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_attempt gir_control_attempt;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_ticket gir_control_ticket;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_scope gir_control_scope;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_call gir_control_call;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_lease gir_control_lease;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_owner gir_control_owner;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_owner_ref gir_control_owner_ref;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_call_output gir_control_call_output;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_binding_kind { GIR_CONTROL_NAMED_VALUE, GIR_CONTROL_MUTABLE_OWNER } gir_control_binding_kind;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_parent_kind { GIR_CONTROL_ROOT, GIR_CONTROL_CHILD, GIR_CONTROL_REPLACEMENT } gir_control_parent_kind;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_cleanup { GIR_CONTROL_NO_CLEANUP, GIR_CONTROL_RELEASE_STORAGE, GIR_CONTROL_PRESERVE_STORAGE, GIR_CONTROL_STORAGE_CLEANED, GIR_CONTROL_UNSELECTED_COMPLETION } gir_control_cleanup;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_ticket_state { GIR_CONTROL_TICKET_ACTIVE, GIR_CONTROL_TICKET_RESTORED } gir_control_ticket_state;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_ticket_role { GIR_CONTROL_WAITING, GIR_CONTROL_FRESH, GIR_CONTROL_NAMED_AWAITING, GIR_CONTROL_NAMED_READY, GIR_CONTROL_NAMED_MATERIALIZED } gir_control_ticket_role;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_ticket_kind { GIR_CONTROL_TICKET_RESERVED, GIR_CONTROL_TICKET_SELECTED, GIR_CONTROL_TICKET_RECEIVED } gir_control_ticket_kind;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef enum gir_control_ticket_authority { GIR_CONTROL_ORDINARY_TICKET, GIR_CONTROL_WAITING_RECEIPT } gir_control_ticket_authority;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_metadata { int64_t count, identity; } gir_control_metadata;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_snapshot {
    uint8_t *start, *receiving_start, *write_end, *rollback_end;
    int64_t count, progress, prefix, receiving_prefix;
    gir_control_attempt *expected;
} gir_control_snapshot;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_staging {
    gs_stack *cursor;
    uint8_t *base, *end;
    int64_t capacity, element_bytes;
} gir_control_staging;
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_attempt {
    gir_control_metadata metadata;
    int64_t progress;
    gir_control_graph *graph;
    gir_control_attempt *next, *parent, *successor, *expected;
    gir_control_attempt *live_next, *live_previous;
    gir_control_attempt *predecessors, *predecessor_next, *predecessor_previous;
    size_t references;
    gir_control_lease *active;
    gir_control_parent_kind parent_kind;
    uint8_t resumable, extension;
    gs_stack *stack;
    uint8_t *start, *receiving_start, *write_end, *rollback_end;
    int64_t prefix, receiving_prefix;
    gir_control_snapshot resumption, extension_snapshot;
    gir_control_staging staging;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_graph {
    size_t references;
    gir_control_attempt *attempts;
    gir_control_ticket *tickets;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_receiving {
    gir_control_graph *graph;
    gir_control_attempt *boundary, *handoff;
    gir_control_scope *scope;
    gir_control_receiving *next;
    gir_control_ticket *unselected;
    gir_control_call_output *input;
    uint8_t exposed, handoff_mode, outward_mode, consumed, extension;
    ptrdiff_t view_offset;
    int64_t view_prefix;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_lease {
    gir_control_metadata metadata;
    int64_t progress;
    uint8_t *start, *end;
    int64_t prefix;
    gir_control_attempt *attempt;
    gir_control_receiving *receiving;
    uint8_t mode;
    gir_control_cleanup cleanup;
    size_t sequence;
    struct gir_control_lease *next;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_owner {
    size_t references;
    gir_control_binding_kind kind;
    gir_control_graph *graph;
    gir_control_attempt *boundary;
    gir_hdr *header;
    gs_stack *stack;
    uint8_t *base, *value_end;
    int64_t value_count;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_owner_ref {
    gir_control_owner *owner;
    gir_control_owner_ref *next;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_scope {
    gir_control_scope *previous;
    gir_control_call *call;
    gir_control_receiving *receivers;
    gir_control_lease *leases;
    gir_control_ticket *tickets;
    size_t next_lease;
    gir_control_owner_ref *owners;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_ticket {
    gir_control_receiving *receiving;
    gir_control_graph *graph;
    gir_control_owner *source;
    ptrdiff_t view_offset;
    int64_t view_prefix;
    uint8_t outward_mode;
    gir_control_attempt *boundary, *snapshot_attempt, *selected, *prepared;
    gir_control_snapshot snapshot;
    uint8_t *boundary_start, *payload_start, *payload_end;
    gir_control_ticket *previous, *scope_next;
    gir_control_scope *scope;
    gir_control_ticket_state state;
    gir_control_ticket_kind kind;
    gir_control_ticket_role role;
    gir_control_ticket_authority authority;
    size_t lease_boundary;
    size_t protected_count;
    uint8_t **protected_metadata;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_call_output {
    gir_control_attempt *attempt;
    gir_control_receiving *receiving;
    uint8_t mode, claimed;
    ptrdiff_t view_offset;
    int64_t view_prefix;
    gir_control_cleanup completion;
};
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(struct gir_control_call {
    gir_control_call *previous;
    size_t count;
    gir_control_call_output *outputs;
    size_t binding_count;
    gir_control_owner **bindings, **owner_results;
};
)GIRSUPPORT");
        support.State("GS_TLS gir_control_attempt *gir_control_live_attempts;\n");
        support.Forward("void gir_control_ticket_destroy(gir_control_ticket *ticket);\n");
        support.State("GS_TLS gir_control_scope *gir_control_scope_top;\n");
        support.State("GS_TLS gir_control_call *gir_control_call_top;\n");
        support.Type(R"GIRSUPPORT(typedef char gir_control_metadata_size[(sizeof(gir_control_metadata) == 16) ? 1 : -1];
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef char gir_control_progress_size[(sizeof(((gir_control_attempt *)0)->progress) == 8) ? 1 : -1];
)GIRSUPPORT");
        support.Function("void gir_control_require(int condition)", R"GIRSUPPORT({ if (!condition) gs_panic("invalid construction receiver protocol"); }
)GIRSUPPORT");
        support.Function("void *gir_control_alloc(size_t size)", R"GIRSUPPORT({
    void *memory = calloc(1, size);
    if (!memory) gs_panic("out of memory managing construction receivers");
    return memory;
}
)GIRSUPPORT");
        support.Function("gir_control_attempt *gir_control_node(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_require(metadata != NULL);
    return ((gir_control_lease *)metadata)->attempt;
}
)GIRSUPPORT");
        support.Function("void gir_control_capture(gir_control_attempt *attempt)", R"GIRSUPPORT({
    if (!attempt->active) return;
    gir_control_lease *lease = attempt->active;
    gir_control_require(lease->metadata.identity == attempt->metadata.identity);
    attempt->metadata.count = lease->metadata.count;
    attempt->progress = lease->progress;
    attempt->start = lease->start;
    attempt->prefix = lease->prefix;
    if (attempt->progress == GIR_CONTROL_OPEN) {
        attempt->write_end = attempt->stack->top;
        lease->end = attempt->write_end;
    }
}
)GIRSUPPORT");
        support.Function("void gir_control_progress(gir_control_attempt *attempt, int64_t progress)", R"GIRSUPPORT({
    attempt->progress = progress;
    if (attempt->active) attempt->active->progress = progress;
}
)GIRSUPPORT");
        support.Function("void gir_control_graph_retain(gir_control_graph *graph)", R"GIRSUPPORT({
    gir_control_require(graph && graph->references != SIZE_MAX);
    graph->references++;
}
)GIRSUPPORT");
        support.Function("void gir_control_node_retain(gir_control_attempt *attempt)", R"GIRSUPPORT({
    gir_control_require(attempt && attempt->references != SIZE_MAX);
    attempt->references++;
}
)GIRSUPPORT");
        support.Function("void gir_control_graph_release(gir_control_graph *graph)", R"GIRSUPPORT({
    gir_control_require(graph && graph->references);
    if (--graph->references) return;
    gir_control_require(!graph->attempts && !graph->tickets);
    free(graph);
}
)GIRSUPPORT");
        support.Forward("void gir_control_node_release(gir_control_attempt *attempt);\n");
        support.Function("void gir_control_parent_retain(gir_control_attempt *owner, gir_control_attempt *parent)", R"GIRSUPPORT({
    if (!parent) return;
    gir_control_node_retain(parent);
    if (owner->graph != parent->graph) gir_control_graph_retain(parent->graph);
}
)GIRSUPPORT");
        support.Function("void gir_control_parent_release(gir_control_attempt *owner, gir_control_attempt *parent)", R"GIRSUPPORT({
    if (!parent) return;
    gir_control_graph *graph = parent->graph;
    uint8_t other = owner->graph != graph;
    gir_control_node_release(parent);
    if (other) gir_control_graph_release(graph);
}
)GIRSUPPORT");
        support.Function("void gir_control_unlink_successor(gir_control_attempt *attempt)", R"GIRSUPPORT({
    gir_control_attempt *successor = attempt->successor;
    if (!successor) return;
    if (attempt->predecessor_previous) attempt->predecessor_previous->predecessor_next = attempt->predecessor_next;
    else successor->predecessors = attempt->predecessor_next;
    if (attempt->predecessor_next) attempt->predecessor_next->predecessor_previous = attempt->predecessor_previous;
    attempt->successor = attempt->predecessor_next = attempt->predecessor_previous = NULL;
    gir_control_node_release(successor);
}
)GIRSUPPORT");
        support.Function("void gir_control_node_release(gir_control_attempt *attempt)", R"GIRSUPPORT({
    gir_control_require(attempt && attempt->references);
    if (--attempt->references) return;
    gir_control_require(!attempt->predecessors);
    gir_control_attempt **position = &attempt->graph->attempts;
    while (*position && *position != attempt) position = &(*position)->next;
    gir_control_require(*position == attempt);
    *position = attempt->next;
    if (attempt->live_previous) attempt->live_previous->live_next = attempt->live_next;
    else gir_control_live_attempts = attempt->live_next;
    if (attempt->live_next) attempt->live_next->live_previous = attempt->live_previous;
    if (attempt->parent && attempt->parent->expected == attempt) attempt->parent->expected = NULL;
    gir_control_parent_release(attempt, attempt->parent);
    gir_control_unlink_successor(attempt);
    free(attempt);
}
)GIRSUPPORT");
        support.Function("gir_control_attempt *gir_control_resolve(gir_control_attempt *attempt)", R"GIRSUPPORT({
    gir_control_require(attempt != NULL);
    while (attempt->successor) attempt = attempt->successor;
    return attempt;
}
)GIRSUPPORT");
        support.Function("void gir_control_link_direct(gir_control_attempt *attempt, gir_control_attempt *successor)", R"GIRSUPPORT({
    gir_control_require(attempt != successor && attempt->graph == successor->graph && !successor->successor);
    gir_control_node_retain(successor);
    gir_control_unlink_successor(attempt);
    attempt->successor = successor;
    attempt->predecessor_next = successor->predecessors;
    if (successor->predecessors) successor->predecessors->predecessor_previous = attempt;
    successor->predecessors = attempt;
}
)GIRSUPPORT");
        support.Function("void gir_control_link_successor(gir_control_attempt *attempt, gir_control_attempt *successor)", R"GIRSUPPORT({
    gir_control_node_retain(attempt);
    while (attempt->predecessors) gir_control_link_direct(attempt->predecessors, successor);
    gir_control_link_direct(attempt, successor);
    gir_control_node_release(attempt);
}
)GIRSUPPORT");
        support.Function("gir_control_snapshot gir_control_snapshot_of(gir_control_attempt *attempt)", R"GIRSUPPORT({
    gir_control_capture(attempt);
    gir_control_snapshot snapshot;
    snapshot.start = attempt->start;
    snapshot.receiving_start = attempt->receiving_start;
    snapshot.write_end = attempt->write_end;
    snapshot.rollback_end = attempt->rollback_end;
    snapshot.count = attempt->metadata.count;
    snapshot.progress = attempt->progress;
    snapshot.prefix = attempt->prefix;
    snapshot.receiving_prefix = attempt->receiving_prefix;
    snapshot.expected = attempt->expected;
    return snapshot;
}
)GIRSUPPORT");
        support.Function("int gir_control_snapshot_matches(gir_control_attempt *attempt, const gir_control_snapshot *snapshot)", R"GIRSUPPORT({
    return attempt->start == snapshot->start && attempt->receiving_start == snapshot->receiving_start &&
        attempt->write_end == snapshot->write_end && attempt->rollback_end == snapshot->rollback_end &&
        attempt->metadata.count == snapshot->count && attempt->prefix == snapshot->prefix &&
        attempt->receiving_prefix == snapshot->receiving_prefix;
}
)GIRSUPPORT");
        support.Function("void gir_control_restore(gir_control_attempt *attempt, const gir_control_snapshot *snapshot)", R"GIRSUPPORT({
    attempt->start = snapshot->start;
    attempt->receiving_start = snapshot->receiving_start;
    attempt->write_end = snapshot->write_end;
    attempt->rollback_end = snapshot->rollback_end;
    attempt->metadata.count = snapshot->count;
    attempt->progress = snapshot->progress;
    attempt->prefix = snapshot->prefix;
    attempt->receiving_prefix = snapshot->receiving_prefix;
    attempt->expected = snapshot->expected;
    if (attempt->active) {
        attempt->active->metadata.count = attempt->metadata.count;
        attempt->active->progress = attempt->progress;
        attempt->active->start = attempt->start;
        attempt->active->prefix = attempt->prefix;
    }
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_enter(void)", R"GIRSUPPORT({
    gir_control_scope *scope = (gir_control_scope *)gir_control_alloc(sizeof(*scope));
    scope->previous = gir_control_scope_top;
    scope->call = gir_control_call_top;
    gir_control_scope_top = scope;
    return (uint8_t *)scope;
}
)GIRSUPPORT");
        support.Function("gir_control_receiving *gir_control_handle(gir_control_attempt *boundary, ptrdiff_t offset, int64_t prefix)", R"GIRSUPPORT({
    gir_control_require(gir_control_scope_top != NULL);
    gir_control_receiving *receiving = (gir_control_receiving *)gir_control_alloc(sizeof(*receiving));
    receiving->graph = boundary->graph;
    receiving->boundary = boundary;
    receiving->view_offset = offset;
    receiving->view_prefix = prefix;
    receiving->scope = gir_control_scope_top;
    receiving->next = gir_control_scope_top->receivers;
    gir_control_scope_top->receivers = receiving;
    gir_control_graph_retain(receiving->graph);
    gir_control_node_retain(boundary);
    return receiving;
}
)GIRSUPPORT");
        support.Function("void gir_control_handle_close(gir_control_receiving *receiving)", R"GIRSUPPORT({
    for (gir_control_scope *scope = gir_control_scope_top; scope; scope = scope->previous)
        for (gir_control_lease *lease = scope->leases; lease; lease = lease->next)
            if (lease->receiving == receiving) lease->receiving = NULL;
    for (gir_control_ticket *ticket = receiving->graph->tickets; ticket; ticket = ticket->previous)
        if (ticket->receiving == receiving) {
            gir_control_require(ticket->kind != GIR_CONTROL_TICKET_RESERVED);
            ticket->receiving = NULL;
        }
    for (gir_control_call *call = gir_control_call_top; call; call = call->previous)
        for (size_t position = 0; position < call->count; position++)
            gir_control_require(call->outputs[position].receiving != receiving);
    gir_control_receiving **position = &receiving->scope->receivers;
    while (*position && *position != receiving) position = &(*position)->next;
    gir_control_require(*position == receiving);
    *position = receiving->next;
    gir_control_graph *graph = receiving->graph;
    if (receiving->unselected) gir_control_ticket_destroy(receiving->unselected);
    if (receiving->handoff) gir_control_node_release(receiving->handoff);
    gir_control_node_release(receiving->boundary);
    free(receiving);
    gir_control_graph_release(graph);
}
)GIRSUPPORT");
        support.Function("gir_control_attempt *gir_control_boundary(gir_control_receiving *receiving)", R"GIRSUPPORT({
    gir_control_attempt *current = gir_control_resolve(receiving->boundary);
    if (current != receiving->boundary) {
        gir_control_node_retain(current);
        gir_control_node_release(receiving->boundary);
        receiving->boundary = current;
    }
    return current;
}
)GIRSUPPORT");
        support.Function("gir_control_lease *gir_control_find_lease(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_require(gir_control_scope_top != NULL);
    for (gir_control_lease *lease = gir_control_scope_top->leases; lease; lease = lease->next)
        if ((uint8_t *)&lease->metadata == metadata) return lease;
    gir_control_require(0);
    return NULL;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_add_lease_view(gir_control_receiving *receiving, gir_control_attempt *attempt,\n                                          uint8_t mode, ptrdiff_t offset, int64_t prefix)", R"GIRSUPPORT({
    gir_control_require(gir_control_scope_top != NULL && receiving->graph == attempt->graph);
    gir_control_capture(attempt);
    gir_control_lease *lease = (gir_control_lease *)gir_control_alloc(sizeof(*lease));
    lease->attempt = attempt;
    lease->receiving = receiving;
    lease->metadata = attempt->metadata;
    lease->progress = attempt->progress;
    lease->start = attempt->receiving_start + offset;
    lease->end = attempt->write_end;
    lease->prefix = prefix;
    lease->mode = mode;
    gir_control_require(gir_control_scope_top->next_lease != SIZE_MAX);
    lease->sequence = gir_control_scope_top->next_lease++;
    lease->next = gir_control_scope_top->leases;
    gir_control_scope_top->leases = lease;
    attempt->active = lease;
    gir_control_node_retain(attempt);
    gir_control_graph_retain(attempt->graph);
    return (uint8_t *)&lease->metadata;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_add_lease(gir_control_receiving *receiving, gir_control_attempt *attempt, uint8_t mode)", R"GIRSUPPORT({
    gir_control_capture(attempt);
    return gir_control_add_lease_view(receiving, attempt, mode,
        attempt->start - attempt->receiving_start, attempt->prefix);
}
)GIRSUPPORT");
        support.Function("gir_control_lease *gir_control_take_lease(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_require(gir_control_scope_top != NULL);
    gir_control_lease **position = &gir_control_scope_top->leases;
    while (*position && (uint8_t *)&(*position)->metadata != metadata) position = &(*position)->next;
    gir_control_require(*position != NULL);
    gir_control_lease *lease = *position;
    *position = lease->next;
    if (lease->attempt->active == lease) {
        gir_control_capture(lease->attempt);
        lease->attempt->active = NULL;
    }
    return lease;
}
)GIRSUPPORT");
        support.Function("void gir_control_release_lease(gir_control_lease *lease)", R"GIRSUPPORT({
    gir_control_attempt *attempt = lease->attempt;
    gir_control_graph *graph = attempt->graph;
    free(lease);
    gir_control_node_release(attempt);
    gir_control_graph_release(graph);
}
)GIRSUPPORT");
        support.Function("void gir_control_drop_lease(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_release_lease(gir_control_take_lease(metadata));
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_rebase_lease(gir_control_lease *previous)", R"GIRSUPPORT({
    gir_control_attempt *attempt = previous->attempt;
    gir_control_lease *lease = (gir_control_lease *)gir_control_alloc(sizeof(*lease));
    lease->metadata = attempt->metadata;
    lease->progress = attempt->progress;
    lease->start = attempt->start;
    lease->end = attempt->write_end;
    lease->prefix = attempt->prefix;
    lease->attempt = attempt;
    lease->receiving = previous->receiving;
    lease->mode = previous->mode;
    lease->cleanup = GIR_CONTROL_NO_CLEANUP;
    gir_control_require(gir_control_scope_top->next_lease != SIZE_MAX);
    lease->sequence = gir_control_scope_top->next_lease++;
    lease->next = gir_control_scope_top->leases;
    gir_control_scope_top->leases = lease;
    attempt->active = lease;
    gir_control_node_retain(attempt);
    gir_control_graph_retain(attempt->graph);
    gir_control_release_lease(previous);
    return (uint8_t *)&lease->metadata;
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_retain(gir_control_owner *owner)", R"GIRSUPPORT({
    if (!owner) return;
    gir_control_require(owner->references != SIZE_MAX);
    owner->references++;
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_release(gir_control_owner *owner)", R"GIRSUPPORT({
    if (!owner) return;
    gir_control_require(owner->references != 0);
    if (--owner->references) return;
    gir_control_graph *graph = owner->graph;
    gir_control_node_release(owner->boundary);
    free(owner);
    gir_control_graph_release(graph);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_owner_hold(gir_control_owner *owner)", R"GIRSUPPORT({
    if (!owner) return NULL;
    gir_control_require(gir_control_scope_top != NULL);
    for (gir_control_owner_ref *reference = gir_control_scope_top->owners; reference; reference = reference->next)
        if (reference->owner == owner) return (uint8_t *)owner;
    gir_control_owner_ref *reference = (gir_control_owner_ref *)gir_control_alloc(sizeof(*reference));
    reference->owner = owner;
    reference->next = gir_control_scope_top->owners;
    gir_control_scope_top->owners = reference;
    gir_control_owner_retain(owner);
    return (uint8_t *)owner;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_owner_none(void)", R"GIRSUPPORT({ return NULL; }
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_named_bind(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_require(lease->progress == GIR_CONTROL_BUILT);
    gir_control_owner *binding = (gir_control_owner *)gir_control_alloc(sizeof(*binding));
    binding->kind = GIR_CONTROL_NAMED_VALUE;
    binding->graph = attempt->graph;
    binding->boundary = attempt;
    binding->base = lease->start;
    binding->value_end = lease->end;
    binding->value_count = lease->metadata.count;
    binding->stack = attempt->stack;
    gir_control_graph_retain(binding->graph);
    gir_control_node_retain(attempt);
    return gir_control_owner_hold(binding);
}
)GIRSUPPORT");
        support.Function("uint8_t gir_control_owner_is_named(uint8_t *token)", R"GIRSUPPORT({
    gir_control_owner *binding = (gir_control_owner *)token;
    return binding && binding->kind == GIR_CONTROL_NAMED_VALUE;
}
)GIRSUPPORT");
        support.Function("gir_control_owner *gir_control_named_value(uint8_t *token, uint8_t *reference)", R"GIRSUPPORT({
    gir_control_owner *binding = (gir_control_owner *)token;
    gir_control_require(binding && binding->kind == GIR_CONTROL_NAMED_VALUE && reference == binding->base);
    gir_control_attempt *attempt = binding->boundary;
    gir_control_capture(attempt);
    gir_control_require(attempt->progress != GIR_CONTROL_ABANDONED && attempt->progress != GIR_CONTROL_CANCELLED &&
        attempt->progress != GIR_CONTROL_RETIRED && attempt->start == binding->base &&
        attempt->metadata.count == binding->value_count && (attempt->prefix == 0 || attempt->prefix == 4) &&
        binding->base + attempt->prefix <= attempt->write_end);
    return binding;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_named_base(uint8_t *token, uint8_t *reference)", R"GIRSUPPORT({
    gir_control_owner *binding = gir_control_named_value(token, reference);
    return binding->base + binding->boundary->prefix;
}
)GIRSUPPORT");
        support.Function("int64_t gir_control_named_count(uint8_t *token, uint8_t *reference)", R"GIRSUPPORT({
    return gir_control_named_value(token, reference)->value_count;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_owner_bind(uint8_t *control, uint8_t *header, uint8_t *stack)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_attempt *boundary = gir_control_boundary(receiving);
    gir_control_capture(boundary);
    gir_control_require(boundary->progress == GIR_CONTROL_BUILT && boundary->stack == (gs_stack *)stack &&
        ((gir_hdr *)header)->base == boundary->receiving_start + receiving->view_offset + receiving->view_prefix &&
        ((gir_hdr *)header)->len == boundary->metadata.count);
    for (gir_control_owner_ref *reference = gir_control_scope_top->owners; reference; reference = reference->next) {
        gir_control_owner *owner = reference->owner;
        if (owner->kind == GIR_CONTROL_MUTABLE_OWNER && owner->header == (gir_hdr *)header &&
            owner->stack == (gs_stack *)stack && owner->graph == receiving->graph) {
            if (owner->boundary != boundary) {
                gir_control_node_retain(boundary);
                gir_control_node_release(owner->boundary);
                owner->boundary = boundary;
            }
            owner->base = ((gir_hdr *)header)->base;
            return (uint8_t *)owner;
        }
    }
    gir_control_owner *owner = (gir_control_owner *)gir_control_alloc(sizeof(*owner));
    owner->kind = GIR_CONTROL_MUTABLE_OWNER;
    owner->graph = receiving->graph;
    owner->boundary = boundary;
    owner->header = (gir_hdr *)header;
    owner->stack = (gs_stack *)stack;
    owner->base = ((gir_hdr *)header)->base;
    gir_control_graph_retain(owner->graph);
    gir_control_node_retain(boundary);
    return gir_control_owner_hold(owner);
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_check(uint8_t *binding)", R"GIRSUPPORT({
    gir_control_owner *owner = (gir_control_owner *)binding;
    if (!owner) return;
    gir_control_require(owner->kind == GIR_CONTROL_MUTABLE_OWNER);
    gir_control_attempt *attempt = owner->boundary;
    gir_control_capture(attempt);
    gir_control_require(attempt->progress == GIR_CONTROL_BUILT && attempt->stack == owner->stack &&
        owner->header->len == attempt->metadata.count && owner->header->base == owner->base && owner->header->base >= attempt->receiving_start &&
        owner->header->base <= attempt->write_end);
}
)GIRSUPPORT");
        support.Forward("void gir_control_set_parent(gir_control_attempt *, gir_control_attempt *, gir_control_parent_kind);\n");
        support.Function("void gir_control_owner_extend(uint8_t *binding, uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_owner *owner = (gir_control_owner *)binding;
    if (!owner) return;
    gir_control_owner_check(binding);
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *parent = owner->boundary, *child = lease->attempt;
    gir_control_capture(child);
    gir_control_require(child->progress == GIR_CONTROL_OPEN && child->metadata.count == 0 && !child->parent &&
        child->stack == parent->stack && child->rollback_end == parent->write_end && lease->receiving &&
        !lease->receiving->exposed && !parent->expected);
    child->extension_snapshot = gir_control_snapshot_of(parent);
    child->extension = 1;
    lease->receiving->extension = 1;
    gir_control_set_parent(child, parent, GIR_CONTROL_CHILD);
    parent->active = NULL;
    parent->expected = child;
    gir_control_progress(parent, GIR_CONTROL_SUSPENDED);
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_update(uint8_t *binding, int64_t count, uint8_t *end)", R"GIRSUPPORT({
    gir_control_owner *owner = (gir_control_owner *)binding;
    if (!owner) return;
    gir_control_require(owner->kind == GIR_CONTROL_MUTABLE_OWNER);
    gir_control_attempt *attempt = owner->boundary;
    gir_control_capture(attempt);
    if (attempt->progress == GIR_CONTROL_SUSPENDED) {
        gir_control_attempt *child = attempt->expected ? gir_control_resolve(attempt->expected) : NULL;
        gir_control_require(child && child->extension && child->parent == attempt && child->parent_kind == GIR_CONTROL_CHILD);
        gir_control_capture(child);
        gir_control_require(child->progress == GIR_CONTROL_BUILT && end == child->write_end &&
            gir_control_snapshot_matches(attempt, &child->extension_snapshot));
        gir_control_restore(attempt, &child->extension_snapshot);
    }
    gir_control_require(attempt->progress == GIR_CONTROL_BUILT && attempt->stack == owner->stack &&
        owner->header->len == count && owner->header->base == owner->base && count >= 0 && end >= owner->header->base && end <= owner->stack->top);
    attempt->metadata.count = count;
    attempt->write_end = end;
    attempt->active = NULL;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_owner_param(size_t position)", R"GIRSUPPORT({
    gir_control_call *call = gir_control_call_top;
    gir_control_require(call && position > 0 && position <= call->binding_count);
    return gir_control_owner_hold(call->bindings[position - 1]);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_owner_get(uint8_t *token, size_t position)", R"GIRSUPPORT({
    gir_control_call *call = (gir_control_call *)token;
    gir_control_require(call == gir_control_call_top && position > 0 && position <= call->binding_count);
    return gir_control_owner_hold(call->owner_results[position - 1]);
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_result(uint8_t *binding, size_t position)", R"GIRSUPPORT({
    gir_control_call *call = gir_control_scope_top->call;
    gir_control_require(call && position > 0 && position <= call->binding_count);
    gir_control_owner *owner = (gir_control_owner *)binding;
    gir_control_owner_retain(owner);
    gir_control_owner_release(call->owner_results[position - 1]);
    call->owner_results[position - 1] = owner;
}
)GIRSUPPORT");
        support.Type(R"GIRSUPPORT(typedef struct gir_control_owner_target {
    struct gir_control_owner_target *previous;
    gir_control_call *call;
    size_t target, count;
    int64_t *positions;
    gir_control_owner **results;
} gir_control_owner_target;
)GIRSUPPORT");
        support.State("GS_TLS gir_control_owner_target *gir_control_owner_targets[GIR_CONTROL_TARGET_COUNT ? GIR_CONTROL_TARGET_COUNT : 1];\n");
        support.Function("uint8_t *gir_control_owner_target_enter(size_t target, size_t count, const int64_t *positions)", R"GIRSUPPORT({
    gir_control_require(target < GIR_CONTROL_TARGET_COUNT && count <= SIZE_MAX / sizeof(int64_t));
    gir_control_owner_target *record = (gir_control_owner_target *)gir_control_alloc(sizeof(*record));
    record->previous = gir_control_owner_targets[target];
    record->call = gir_control_scope_top->call;
    record->target = target;
    record->count = count;
    record->positions = (int64_t *)gir_control_alloc((count ? count : 1) * sizeof(*record->positions));
    record->results = (gir_control_owner **)gir_control_alloc((count ? count : 1) * sizeof(*record->results));
    for (size_t result = 0; result < count; result++) record->positions[result] = positions[result];
    gir_control_owner_targets[target] = record;
    return (uint8_t *)record;
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_target_result(uint8_t *binding, size_t target, size_t result)", R"GIRSUPPORT({
    gir_control_require(target < GIR_CONTROL_TARGET_COUNT);
    gir_control_owner_target *record = gir_control_owner_targets[target];
    gir_control_require(record && result < record->count && record->positions[result] > 0 && record->call &&
        (uint64_t)record->positions[result] <= record->call->binding_count);
    gir_control_owner *owner = (gir_control_owner *)binding;
    gir_control_owner_retain(owner);
    gir_control_owner_release(record->results[result]);
    record->results[result] = owner;
    size_t position = (size_t)record->positions[result] - 1;
    gir_control_owner_retain(owner);
    gir_control_owner_release(record->call->owner_results[position]);
    record->call->owner_results[position] = owner;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_owner_target_get(uint8_t *token, size_t result)", R"GIRSUPPORT({
    gir_control_owner_target *record = (gir_control_owner_target *)token;
    gir_control_require(record->target < GIR_CONTROL_TARGET_COUNT && gir_control_owner_targets[record->target] == record &&
        result < record->count && record->positions[result] > 0);
    return gir_control_owner_hold(record->results[result]);
}
)GIRSUPPORT");
        support.Function("void gir_control_owner_target_leave(uint8_t *token)", R"GIRSUPPORT({
    gir_control_owner_target *record = (gir_control_owner_target *)token;
    gir_control_require(record->target < GIR_CONTROL_TARGET_COUNT && gir_control_owner_targets[record->target] == record);
    for (size_t result = 0; result < record->count; result++) gir_control_owner_release(record->results[result]);
    gir_control_owner_targets[record->target] = record->previous;
    free(record->positions);
    free(record->results);
    free(record);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_call_push(size_t count, uint8_t *const *metadata, size_t binding_count, uint8_t *const *bindings)", R"GIRSUPPORT({
    gir_control_call *call = (gir_control_call *)gir_control_alloc(sizeof(*call));
    gir_control_require(count <= SIZE_MAX / sizeof(*call->outputs));
    call->outputs = (gir_control_call_output *)gir_control_alloc((count ? count : 1) * sizeof(*call->outputs));
    call->count = count;
    gir_control_require(binding_count <= SIZE_MAX / sizeof(*call->bindings));
    call->binding_count = binding_count;
    call->bindings = (gir_control_owner **)gir_control_alloc((binding_count ? binding_count : 1) * sizeof(*call->bindings));
    call->owner_results = (gir_control_owner **)gir_control_alloc((binding_count ? binding_count : 1) * sizeof(*call->owner_results));
    for (size_t index = 0; index < binding_count; index++) {
        call->bindings[index] = (gir_control_owner *)bindings[index];
        gir_control_owner_retain(call->bindings[index]);
    }
    call->previous = gir_control_call_top;
    for (size_t position = 0; position < count; position++) {
        if (!metadata[position]) continue;
        gir_control_lease *lease = gir_control_take_lease(metadata[position]);
        call->outputs[position].attempt = lease->attempt;
        call->outputs[position].receiving = lease->receiving;
        call->outputs[position].mode = lease->mode;
        call->outputs[position].view_offset = lease->start - lease->attempt->receiving_start;
        call->outputs[position].view_prefix = lease->prefix;
        free(lease);
    }
    gir_control_call_top = call;
    return (uint8_t *)call;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_call_param(size_t position)", R"GIRSUPPORT({
    gir_control_call *call = gir_control_call_top;
    gir_control_require(call && position < call->count && call->outputs[position].attempt && !call->outputs[position].claimed);
    call->outputs[position].claimed = 1;
    gir_control_receiving *receiving = gir_control_handle(gir_control_resolve(call->outputs[position].attempt),
        call->outputs[position].view_offset, call->outputs[position].view_prefix);
    receiving->input = &call->outputs[position];
    return (uint8_t *)receiving;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_call_get(uint8_t *token, size_t position)", R"GIRSUPPORT({
    gir_control_call *call = (gir_control_call *)token;
    gir_control_require(call == gir_control_call_top && position < call->count && call->outputs[position].claimed);
    gir_control_call_output *output = &call->outputs[position];
    uint8_t *metadata = gir_control_add_lease(output->receiving, gir_control_resolve(output->attempt), output->mode);
    gir_control_lease *lease = gir_control_find_lease(metadata);
    if (output->completion == GIR_CONTROL_UNSELECTED_COMPLETION) {
        lease->attempt->active = NULL;
        lease->progress = GIR_CONTROL_CANCELLED;
        lease->cleanup = GIR_CONTROL_UNSELECTED_COMPLETION;
    } else if (lease->progress == GIR_CONTROL_ABANDONED || lease->progress == GIR_CONTROL_CANCELLED)
        lease->cleanup = GIR_CONTROL_STORAGE_CLEANED;
    return metadata;
}
)GIRSUPPORT");
        support.Function("void gir_control_call_pop(uint8_t *token)", R"GIRSUPPORT({
    gir_control_call *call = (gir_control_call *)token;
    gir_control_require(call == gir_control_call_top);
    for (size_t position = 0; position < call->count; position++) {
        gir_control_attempt *attempt = call->outputs[position].attempt;
        if (!attempt) continue;
        gir_control_require(call->outputs[position].claimed);
        gir_control_graph *graph = attempt->graph;
        gir_control_node_release(attempt);
        gir_control_graph_release(graph);
    }
    gir_control_call_top = call->previous;
    for (size_t index = 0; index < call->binding_count; index++) {
        gir_control_owner_release(call->bindings[index]);
        gir_control_owner_release(call->owner_results[index]);
    }
    free(call->bindings);
    free(call->owner_results);
    free(call->outputs);
    free(call);
}
)GIRSUPPORT");
        support.Function("void gir_control_leave(uint8_t *token)", R"GIRSUPPORT({
    gir_control_scope *scope = (gir_control_scope *)token;
    gir_control_require(scope == gir_control_scope_top && !scope->tickets && scope->call == gir_control_call_top);
    while (scope->leases) gir_control_drop_lease((uint8_t *)&scope->leases->metadata);
    while (scope->receivers) gir_control_handle_close(scope->receivers);
    while (scope->owners) {
        gir_control_owner_ref *reference = scope->owners;
        scope->owners = reference->next;
        gir_control_owner_release(reference->owner);
        free(reference);
    }
    gir_control_scope_top = scope->previous;
    free(scope);
}
)GIRSUPPORT");
        support.Function("gir_control_attempt *gir_control_new_attempt(gir_control_graph *graph, gs_stack *stack, uint8_t *start,\n                                                   int64_t identity, int64_t prefix)", R"GIRSUPPORT({
    gir_control_require(prefix == 0 || prefix == 4);
    gir_control_attempt *attempt = (gir_control_attempt *)gir_control_alloc(sizeof(*attempt));
    attempt->graph = graph;
    attempt->stack = stack;
    attempt->start = attempt->receiving_start = start;
    attempt->write_end = start + prefix;
    attempt->rollback_end = start;
    attempt->prefix = attempt->receiving_prefix = prefix;
    attempt->metadata.identity = identity;
    attempt->progress = GIR_CONTROL_OPEN;
    attempt->next = graph->attempts;
    graph->attempts = attempt;
    attempt->live_next = gir_control_live_attempts;
    if (attempt->live_next) attempt->live_next->live_previous = attempt;
    gir_control_live_attempts = attempt;
    return attempt;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_receiving_new(uint8_t *stack, uint8_t *start, int64_t identity, int64_t prefix)", R"GIRSUPPORT({
    gir_control_graph *graph = (gir_control_graph *)gir_control_alloc(sizeof(*graph));
    gir_control_attempt *attempt = gir_control_new_attempt(graph, (gs_stack *)stack, start, identity, prefix);
    return (uint8_t *)gir_control_handle(attempt, 0, prefix);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_receiving_current(uint8_t *control)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    if (receiving->handoff) {
        gir_control_attempt *attempt = receiving->handoff;
        uint8_t *metadata = gir_control_add_lease(receiving, attempt, receiving->handoff_mode);
        return metadata;
    }
    return gir_control_add_lease(receiving, gir_control_boundary(receiving), receiving->outward_mode);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_receiving_open(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_receiving *receiving = lease->receiving;
    if (!receiving || receiving->exposed || receiving->scope != gir_control_scope_top ||
        gir_control_boundary(receiving) != attempt) {
        receiving = gir_control_handle(attempt, lease->start - attempt->receiving_start, lease->prefix);
        receiving->outward_mode = lease->mode;
    }
    receiving->exposed = 1;
    gir_control_drop_lease(metadata);
    return (uint8_t *)receiving;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_stack(uint8_t *metadata)", R"GIRSUPPORT({ return (uint8_t *)gir_control_node(metadata)->stack; }
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_start(uint8_t *metadata)", R"GIRSUPPORT({ return gir_control_find_lease(metadata)->start; }
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_progress(uint8_t *metadata)", R"GIRSUPPORT({ return (uint8_t *)&gir_control_find_lease(metadata)->progress; }
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_receiving(uint8_t *metadata)", R"GIRSUPPORT({
    return (uint8_t *)gir_control_find_lease(metadata)->receiving;
}
)GIRSUPPORT");
        support.Function("uint8_t gir_control_attempt_mode(uint8_t *metadata)", R"GIRSUPPORT({ return gir_control_find_lease(metadata)->mode; }
)GIRSUPPORT");
        support.Function("int64_t gir_control_attempt_prefix(uint8_t *metadata)", R"GIRSUPPORT({
    int64_t prefix = gir_control_find_lease(metadata)->prefix;
    gir_control_require(prefix == 0 || prefix == 4);
    return prefix;
}
)GIRSUPPORT");
        support.Function("void gir_control_pack_lease(gir_control_lease *lease)", R"GIRSUPPORT({
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_require(attempt->active == lease && lease->progress == GIR_CONTROL_OPEN &&
        lease->metadata.count == 0 && lease->prefix == 0 && attempt->stack->top == lease->start);
    memset(attempt->stack->top, 0, 4);
    attempt->stack->top += 4;
    lease->prefix = 4;
    lease->end = attempt->stack->top;
    gir_control_capture(attempt);
}
)GIRSUPPORT");
        support.Function("void gir_control_remove_header_lease(gir_control_lease *lease)", R"GIRSUPPORT({
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_require(attempt->active == lease && lease->progress == GIR_CONTROL_BUILT &&
        lease->prefix == 4 && lease->start + 4 <= lease->end && attempt->stack->top == lease->end);
    size_t bytes = (size_t)(lease->end - (lease->start + 4));
    memmove(lease->start, lease->start + 4, bytes);
    lease->end -= 4;
    lease->prefix = 0;
    attempt->stack->top = lease->end;
    attempt->write_end = lease->end;
    gir_control_capture(attempt);
    gir_control_header_removal(attempt->metadata.identity);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_pack(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_pack_lease(gir_control_find_lease(metadata));
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_remove_header(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_remove_header_lease(gir_control_find_lease(metadata));
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_prepare_named(uint8_t *metadata, int64_t prefix)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_require((prefix == 0 || prefix == 4) && attempt->active == lease &&
        lease->receiving && lease->receiving->scope == gir_control_scope_top &&
        lease->progress == GIR_CONTROL_OPEN && lease->metadata.count == 0 &&
        attempt->stack->top == lease->start + lease->prefix);
    if (prefix == 4 && lease->prefix == 0) gir_control_pack_lease(lease);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_normalize(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_require(attempt->active == lease && lease->progress == GIR_CONTROL_BUILT &&
        (lease->prefix == 0 || lease->prefix == 4) &&
        (attempt->receiving_prefix == 0 || attempt->receiving_prefix == 4));
    if (lease->prefix == attempt->receiving_prefix) return;
    gir_control_require(attempt->receiving_prefix == 0);
    gir_control_remove_header_lease(lease);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_stage(uint8_t *metadata, uint8_t *scratch_stack,\n                                          uint8_t *inline_end, int64_t capacity, int64_t element_bytes)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_receiving *receiving = lease->receiving;
    gir_control_capture(attempt);
    gir_control_require(attempt->active == lease && lease->cleanup == GIR_CONTROL_NO_CLEANUP &&
        lease->progress == GIR_CONTROL_OPEN && lease->metadata.count == 0 && lease->prefix == 0 &&
        !attempt->staging.cursor && receiving && receiving->scope == gir_control_scope_top &&
        !receiving->exposed && !receiving->input && !receiving->consumed && !receiving->handoff &&
        !receiving->unselected && !attempt->graph->tickets && !attempt->parent && !attempt->expected &&
        !attempt->successor && !attempt->resumable && !attempt->extension &&
        attempt->receiving_prefix == 0 && attempt->receiving_start == lease->start &&
        attempt->stack->top == lease->start && lease->end == lease->start &&
        capacity >= 0 && element_bytes > 0 && capacity <= INT64_MAX / element_bytes);
    uintptr_t base = (uintptr_t)lease->start, end = (uintptr_t)inline_end;
    gir_control_require(end >= base && end - base == (uint64_t)capacity * (uint64_t)element_bytes);
    gs_stack *scratch = (gs_stack *)scratch_stack;
    gir_control_require(scratch && scratch != attempt->stack &&
        ((uintptr_t)scratch->top < base || (uintptr_t)scratch->top >= end) && scratch->top != lease->start);
    for (gir_control_lease *owned = gir_control_scope_top->leases; owned; owned = owned->next)
        gir_control_require(owned->attempt->stack != scratch);
    for (gir_control_receiving *owned = gir_control_scope_top->receivers; owned; owned = owned->next)
        for (gir_control_attempt *node = owned->graph->attempts; node; node = node->next)
            gir_control_require(node->stack != scratch);
    for (gir_control_owner_ref *owned = gir_control_scope_top->owners; owned; owned = owned->next)
        gir_control_require(owned->owner->stack != scratch);
    lease = gir_control_take_lease(metadata);
    attempt->staging = (gir_control_staging) { attempt->stack, lease->start, inline_end, capacity, element_bytes };
    attempt->stack = scratch;
    attempt->start = attempt->receiving_start = attempt->write_end = attempt->rollback_end = scratch->top;
    return gir_control_rebase_lease(lease);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_fit(uint8_t *metadata, uint8_t *inline_cursor)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_capture(attempt);
    gir_control_staging stage = attempt->staging;
    gir_control_require(attempt->active == lease && lease->cleanup == GIR_CONTROL_NO_CLEANUP &&
        lease->progress == GIR_CONTROL_BUILT && lease->prefix == 0 && stage.cursor &&
        (uint8_t *)stage.cursor == inline_cursor && !attempt->graph->tickets &&
        lease->metadata.count >= 0 && lease->metadata.count <= stage.capacity && stage.element_bytes > 0 &&
        stage.capacity <= INT64_MAX / stage.element_bytes && stage.cursor->top == stage.base &&
        attempt->stack != stage.cursor && attempt->stack->top == lease->end &&
        attempt->receiving_start == lease->start);
    uint64_t bytes = (uint64_t)lease->metadata.count * (uint64_t)stage.element_bytes;
    uintptr_t start = (uintptr_t)lease->start, end = (uintptr_t)lease->end;
    uintptr_t base = (uintptr_t)stage.base, bound = (uintptr_t)stage.end;
    gir_control_require(end >= start && end - start == bytes && bound >= base &&
        bound - base == (uint64_t)stage.capacity * (uint64_t)stage.element_bytes && bytes <= bound - base &&
        (end <= base || start >= bound));
    lease = gir_control_take_lease(metadata);
    if (bytes) memmove(stage.base, lease->start, (size_t)bytes);
    attempt->stack->top = lease->start;
    attempt->stack = stage.cursor;
    attempt->start = attempt->receiving_start = attempt->rollback_end = stage.base;
    attempt->write_end = stage.base + bytes;
    attempt->stack->top = attempt->write_end;
    memset(&attempt->staging, 0, sizeof(attempt->staging));
    return gir_control_rebase_lease(lease);
}
)GIRSUPPORT");
        support.Function("void gir_control_receiving_transfer(uint8_t *control, uint8_t *metadata, uint8_t mode)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_attempt *attempt = gir_control_node(metadata);
    gir_control_capture(attempt);
    gir_control_require(receiving->graph == attempt->graph && attempt->progress == GIR_CONTROL_BUILT && !attempt->staging.cursor);
    if (receiving->handoff) {
        gir_control_require(receiving->handoff == attempt && receiving->handoff_mode == mode);
        return;
    }
    gir_control_node_retain(attempt);
    receiving->handoff = attempt;
    receiving->handoff_mode = mode;
}
)GIRSUPPORT");
        support.Function("int gir_control_active(gir_control_attempt *attempt)", R"GIRSUPPORT({
    gir_control_capture(attempt);
    return attempt->progress == GIR_CONTROL_OPEN || attempt->progress == GIR_CONTROL_SUSPENDED ||
           attempt->progress == GIR_CONTROL_BUILT || attempt->progress == GIR_CONTROL_EXITING;
}
)GIRSUPPORT");
        support.Function("int gir_control_descendant(gir_control_attempt *ancestor, gir_control_attempt *attempt)", R"GIRSUPPORT({
    for (; attempt; attempt = attempt->parent) if (attempt == ancestor) return 1;
    return 0;
}
)GIRSUPPORT");
        support.Function("void gir_control_set_parent(gir_control_attempt *attempt, gir_control_attempt *parent, gir_control_parent_kind kind)", R"GIRSUPPORT({
    gir_control_parent_retain(attempt, parent);
    gir_control_attempt *old = attempt->parent;
    if (old && old->expected == attempt) old->expected = NULL;
    attempt->parent = parent;
    attempt->parent_kind = kind;
    gir_control_parent_release(attempt, old);
}
)GIRSUPPORT");
        support.Function("int gir_control_carried(gir_control_attempt *attempt, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    for (size_t index = 0; index < count; index++) if (gir_control_node(carried[index]) == attempt) return 1;
    return 0;
}
)GIRSUPPORT");
        support.Function("int gir_control_carried_descendant(gir_control_attempt *attempt, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    for (size_t index = 0; index < count; index++)
        if (gir_control_descendant(attempt, gir_control_node(carried[index]))) return 1;
    return 0;
}
)GIRSUPPORT");
        support.Function("void gir_control_abandon_tree(gir_control_attempt *attempt, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    for (gir_control_attempt *node = gir_control_live_attempts; node; node = node->live_next) {
        if (!gir_control_descendant(attempt, node) || !gir_control_active(node)) continue;
        uint8_t protected = 0;
        for (size_t index = 0; index < count; index++)
            if (gir_control_descendant(gir_control_node(carried[index]), node)) protected = 1;
        if (protected) continue;
        gir_control_progress(node, GIR_CONTROL_ABANDONED);
        gir_control_event("abandon", node->metadata.identity);
    }
}
)GIRSUPPORT");
        support.Function("void gir_control_restore_top(gir_control_attempt *attempt, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    uint8_t *end = attempt->rollback_end;
    for (size_t index = 0; index < count; index++) {
        gir_control_lease *payload = gir_control_find_lease(carried[index]);
        if (payload->attempt->stack == attempt->stack && payload->end > end) end = payload->end;
    }
    gir_control_require(end <= attempt->stack->top);
    attempt->stack->top = end;
}
)GIRSUPPORT");
        support.Function("gir_control_attempt *gir_control_renew_node(gir_control_receiving *receiving, gir_control_attempt *attempt,\n                                                  ptrdiff_t offset, int64_t prefix)", R"GIRSUPPORT({
    attempt = gir_control_resolve(attempt);
    gir_control_capture(attempt);
    if (attempt->progress != GIR_CONTROL_ABANDONED && attempt->progress != GIR_CONTROL_CANCELLED) return attempt;
    gir_control_require(attempt->resumable && offset >= 0 && offset <= 4 && (prefix == 0 || prefix == 4));
    gir_control_snapshot snapshot = attempt->resumption;
    offset = snapshot.start - snapshot.receiving_start;
    prefix = snapshot.prefix;
    gir_control_require(attempt->stack->top == snapshot.receiving_start);
    gir_control_attempt *renewed = gir_control_new_attempt(attempt->graph, attempt->stack,
        snapshot.receiving_start + offset, gir_control_identity(), prefix);
    renewed->receiving_start = snapshot.receiving_start;
    renewed->receiving_prefix = snapshot.receiving_prefix;
    renewed->rollback_end = snapshot.rollback_end;
    renewed->staging = attempt->staging;
    renewed->extension = attempt->extension;
    renewed->extension_snapshot = attempt->extension_snapshot;
    gir_control_set_parent(renewed, attempt->parent, attempt->parent_kind);
    if (renewed->parent) {
        gir_control_require(renewed->parent->expected == attempt ||
                            gir_control_resolve(renewed->parent->expected) == attempt);
        renewed->parent->expected = renewed;
    }
    gir_control_node_retain(renewed);
    gir_control_link_successor(attempt, renewed);
    if (offset + prefix) {
        memset(attempt->stack->top, 0, (size_t)(offset + prefix));
        attempt->stack->top += offset + prefix;
    }
    gir_control_event("begin", renewed->metadata.identity);
    if (renewed->staging.cursor) gir_control_stage(renewed->metadata.identity);
    if (receiving->boundary == attempt) {
        gir_control_node_retain(renewed);
        gir_control_node_release(receiving->boundary);
        receiving->boundary = renewed;
    }
    gir_control_node_release(renewed);
    return renewed;
}
)GIRSUPPORT");
        support.Function("void gir_control_receiving_selectable(gir_control_receiving *receiving)", R"GIRSUPPORT({
    gir_control_require(!receiving->unselected);
    for (gir_control_ticket *ticket = receiving->graph->tickets; ticket; ticket = ticket->previous)
        gir_control_require(ticket->receiving != receiving || ticket->scope != gir_control_scope_top ||
            ticket->role != GIR_CONTROL_WAITING);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_receiving_renew(uint8_t *control)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_receiving_selectable(receiving);
    gir_control_attempt *attempt = gir_control_renew_node(receiving, gir_control_boundary(receiving),
        receiving->view_offset, receiving->view_prefix);
    gir_control_require(attempt->progress == GIR_CONTROL_OPEN);
    return gir_control_add_lease(receiving, attempt, receiving->outward_mode);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_receiving_refresh(uint8_t *control, uint8_t *metadata, uint8_t *view_start, int64_t prefix)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_receiving_selectable(receiving);
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *before = lease->attempt;
    gir_control_require(receiving->graph == before->graph);
    ptrdiff_t offset = view_start - before->receiving_start;
    uint8_t mode = lease->mode;
    gir_control_attempt *attempt = gir_control_renew_node(receiving, before, offset, prefix);
    if (attempt == before) {
        gir_control_require(lease->start == view_start && lease->prefix == prefix);
        lease->metadata = attempt->metadata;
        lease->progress = attempt->progress;
        lease->end = attempt->write_end;
        attempt->active = lease;
        return metadata;
    }
    uint8_t *after = gir_control_add_lease_view(receiving, attempt, mode, offset, prefix);
    gir_control_drop_lease(metadata);
    return after;
}
)GIRSUPPORT");
        support.Function("gir_control_ticket *gir_control_ticket_allocate(gir_control_receiving *receiving)", R"GIRSUPPORT({
    gir_control_require(gir_control_scope_top != NULL);
    gir_control_ticket *ticket = (gir_control_ticket *)gir_control_alloc(sizeof(*ticket));
    ticket->receiving = receiving;
    ticket->graph = receiving->graph;
    ticket->view_offset = receiving->view_offset;
    ticket->view_prefix = receiving->view_prefix;
    ticket->outward_mode = receiving->outward_mode;
    ticket->scope = gir_control_scope_top;
    ticket->lease_boundary = gir_control_scope_top->next_lease;
    ticket->scope_next = gir_control_scope_top->tickets;
    gir_control_scope_top->tickets = ticket;
    ticket->previous = receiving->graph->tickets;
    receiving->graph->tickets = ticket;
    gir_control_graph_retain(receiving->graph);
    return ticket;
}
)GIRSUPPORT");
        support.Function("void gir_control_ticket_snapshot(gir_control_ticket *ticket, gir_control_attempt *boundary,\n                                        gir_control_attempt *snapshot_attempt, gir_control_attempt *selected)", R"GIRSUPPORT({
    ticket->boundary = boundary;
    ticket->snapshot_attempt = snapshot_attempt;
    ticket->selected = selected;
    ticket->boundary_start = boundary->receiving_start + ticket->view_offset;
    ticket->snapshot = gir_control_snapshot_of(snapshot_attempt);
    gir_control_node_retain(boundary);
    gir_control_node_retain(snapshot_attempt);
    gir_control_node_retain(selected);
    gir_control_parent_retain(snapshot_attempt, ticket->snapshot.expected);
}
)GIRSUPPORT");
        support.Function("gir_control_ticket *gir_control_ticket_new(gir_control_receiving *receiving, gir_control_attempt *boundary,\n                                                 gir_control_attempt *snapshot_attempt, gir_control_attempt *selected)", R"GIRSUPPORT({
    gir_control_ticket *ticket = gir_control_ticket_allocate(receiving);
    gir_control_ticket_snapshot(ticket, boundary, snapshot_attempt, selected);
    ticket->role = GIR_CONTROL_FRESH;
    return ticket;
}
)GIRSUPPORT");
        support.Function("void gir_control_drop_ticket_leases(gir_control_ticket *ticket, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    gir_control_scope *scope = ticket->scope;
    gir_control_lease **position = &scope->leases;
    while (*position) {
        gir_control_lease *lease = *position;
        uint8_t protected = 0;
        for (size_t index = 0; index < count; index++)
            if (carried[index] == (uint8_t *)&lease->metadata) protected = 1;
        if (lease->sequence >= ticket->lease_boundary && !protected && lease->cleanup == GIR_CONTROL_NO_CLEANUP &&
            (gir_control_descendant(ticket->selected, lease->attempt) ||
             gir_control_resolve(ticket->selected) == gir_control_resolve(lease->attempt))) {
            *position = lease->next;
            gir_control_attempt *attempt = lease->attempt;
            gir_control_graph *graph = attempt->graph;
            if (attempt->active == lease) { gir_control_capture(attempt); attempt->active = NULL; }
            free(lease);
            gir_control_node_release(attempt);
            gir_control_graph_release(graph);
        } else position = &lease->next;
    }
}
)GIRSUPPORT");
        support.Function("void gir_control_cancel_ticket(gir_control_ticket *ticket, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    gir_control_require(ticket->kind != GIR_CONTROL_TICKET_RECEIVED && ticket->role != GIR_CONTROL_WAITING);
    if (ticket->state == GIR_CONTROL_TICKET_RESTORED) return;
    if (ticket->role != GIR_CONTROL_FRESH) {
        ticket->state = GIR_CONTROL_TICKET_RESTORED;
        return;
    }
    gir_control_attempt *selected = gir_control_resolve(ticket->selected);
    if (gir_control_carried_descendant(selected, count, carried)) return;
    gir_control_abandon_tree(selected, count, carried);
    if (ticket->selected != ticket->snapshot_attempt) {
        gir_control_attempt *snapshot = ticket->snapshot_attempt;
        gir_control_require(snapshot->progress == GIR_CONTROL_EXITING &&
                            snapshot->expected && gir_control_resolve(snapshot->expected) == selected);
        gir_control_restore(snapshot, &ticket->snapshot);
    } else {
        selected->resumable = 1;
        selected->resumption = ticket->snapshot;
        selected->resumption.expected = NULL;
    }
    gir_control_restore_top(selected, count, carried);
    gir_control_drop_ticket_leases(ticket, count, carried);
    ticket->state = GIR_CONTROL_TICKET_RESTORED;
}
)GIRSUPPORT");
        support.Function("void gir_control_restore_named(gir_control_receiving *receiving, gir_control_attempt *named)", R"GIRSUPPORT({
    for (gir_control_ticket *ticket = receiving->graph->tickets; ticket; ticket = ticket->previous) {
        if (ticket->state != GIR_CONTROL_TICKET_ACTIVE || ticket->role != GIR_CONTROL_FRESH ||
            ticket->kind == GIR_CONTROL_TICKET_RECEIVED || ticket->selected == named) continue;
        if (gir_control_descendant(named, ticket->snapshot_attempt)) gir_control_cancel_ticket(ticket, 0, NULL);
    }
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_exit_wait(uint8_t *control)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_require(receiving->scope == gir_control_scope_top && !receiving->consumed && !receiving->unselected);
    for (gir_control_ticket *ticket = receiving->graph->tickets; ticket; ticket = ticket->previous)
        gir_control_require(ticket->receiving != receiving || ticket->role != GIR_CONTROL_WAITING);
    gir_control_ticket *ticket = gir_control_ticket_allocate(receiving);
    ticket->authority = GIR_CONTROL_WAITING_RECEIPT;
    return (uint8_t *)ticket;
}
)GIRSUPPORT");
        support.Function("void gir_control_exit_select(uint8_t *token, uint8_t alias, uint8_t *binding)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && ticket->role == GIR_CONTROL_WAITING &&
        ticket->kind == GIR_CONTROL_TICKET_RESERVED && ticket->scope == gir_control_scope_top && ticket->receiving);
    gir_control_receiving *receiving = ticket->receiving;
    gir_control_require(!receiving->unselected && !receiving->consumed);
    gir_control_owner *source = (gir_control_owner *)binding;
    gir_control_attempt *current = gir_control_boundary(receiving);
    uint8_t named = alias && source && source->boundary == current;
    gir_control_attempt *boundary = gir_control_renew_node(receiving, current,
        receiving->view_offset, receiving->view_prefix);
    gir_control_attempt *frontier = boundary;
    if (!named) {
        while (1) {
            gir_control_capture(frontier);
            if (frontier->progress != GIR_CONTROL_EXITING) break;
            gir_control_require(frontier->expected != NULL);
            gir_control_attempt *next = gir_control_resolve(frontier->expected);
            gir_control_require(next->parent_kind == GIR_CONTROL_REPLACEMENT && next->parent == frontier);
            frontier = next;
        }
    }
    gir_control_snapshot snapshot = gir_control_snapshot_of(frontier);
    gir_control_attempt *selected = frontier;
    uint8_t fresh = !named && !(frontier->progress == GIR_CONTROL_OPEN && frontier->metadata.count == 0);
    if (fresh) {
        gir_control_require(gir_control_active(frontier));
        uint8_t *start = frontier->stack->top;
        selected = gir_control_new_attempt(frontier->graph, frontier->stack, start,
            gir_control_identity(), frontier->prefix);
        selected->receiving_start = start - receiving->view_offset;
        selected->receiving_prefix = frontier->receiving_prefix;
        selected->staging = frontier->staging;
        gir_control_set_parent(selected, frontier, GIR_CONTROL_REPLACEMENT);
    }
    gir_control_ticket_snapshot(ticket, boundary, frontier, selected);
    ticket->snapshot = snapshot;
    ticket->role = named ? GIR_CONTROL_NAMED_AWAITING : GIR_CONTROL_FRESH;
    ticket->source = named ? source : NULL;
    gir_control_owner_retain(ticket->source);
    if (fresh) {
        frontier->expected = selected;
        gir_control_progress(frontier, GIR_CONTROL_EXITING);
        if (selected->prefix) {
            memset(selected->stack->top, 0, (size_t)selected->prefix);
            selected->stack->top += selected->prefix;
        }
        gir_control_event("begin", selected->metadata.identity);
    }
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_exit_reserve(uint8_t *control, uint8_t alias, uint8_t *binding)", R"GIRSUPPORT({
    gir_control_require(!((gir_control_receiving *)control)->unselected);
    gir_control_ticket *ticket = gir_control_ticket_allocate((gir_control_receiving *)control);
    gir_control_exit_select((uint8_t *)ticket, alias, binding);
    return (uint8_t *)ticket;
}
)GIRSUPPORT");
        support.Function("uint8_t gir_control_exit_is_named(uint8_t *token)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && ticket->kind == GIR_CONTROL_TICKET_RESERVED &&
        ticket->role != GIR_CONTROL_WAITING);
    return ticket->role != GIR_CONTROL_FRESH;
}
)GIRSUPPORT");
        support.Function("void gir_control_exit_mark_named(uint8_t *token)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && ticket->role == GIR_CONTROL_NAMED_AWAITING &&
        ticket->kind == GIR_CONTROL_TICKET_RESERVED);
    gir_control_attempt *selected = ticket->selected;
    gir_control_capture(selected);
    gir_control_owner *source = ticket->source;
    gir_control_require(source && source->boundary == selected && source->stack == selected->stack);
    int64_t count = source->kind == GIR_CONTROL_MUTABLE_OWNER ? source->header->len : source->value_count;
    uint8_t *start = source->kind == GIR_CONTROL_MUTABLE_OWNER ? source->header->base : source->base;
    gir_control_require(count == selected->metadata.count &&
        start == selected->start + (source->kind == GIR_CONTROL_MUTABLE_OWNER ? selected->prefix : 0));
    gir_control_require(selected->progress == GIR_CONTROL_BUILT || selected->progress == GIR_CONTROL_SUSPENDED ||
        selected->progress == GIR_CONTROL_EXITING);
    gir_control_snapshot snapshot = gir_control_snapshot_of(selected);
    gir_control_require(snapshot.start <= snapshot.write_end && snapshot.write_end <= selected->stack->top);
    snapshot.progress = GIR_CONTROL_BUILT;
    snapshot.expected = NULL;
    gir_control_parent_release(ticket->snapshot_attempt, ticket->snapshot.expected);
    ticket->snapshot = snapshot;
    ticket->role = GIR_CONTROL_NAMED_READY;
}
)GIRSUPPORT");
        support.Function("void gir_control_materialize_named(gir_control_ticket *ticket)", R"GIRSUPPORT({
    gir_control_require(ticket->role == GIR_CONTROL_NAMED_READY && ticket->receiving);
    gir_control_attempt *selected = ticket->selected;
    gir_control_restore_named(ticket->receiving, selected);
    gir_control_capture(selected);
    gir_control_snapshot *snapshot = &ticket->snapshot;
    gir_control_require(selected->start == snapshot->start && selected->receiving_start == snapshot->receiving_start &&
        selected->write_end == snapshot->write_end && selected->rollback_end == snapshot->rollback_end &&
        selected->metadata.count == snapshot->count && selected->prefix == snapshot->prefix &&
        selected->receiving_prefix == snapshot->receiving_prefix);
    if (selected->progress == GIR_CONTROL_SUSPENDED) {
        gir_control_attempt *child = selected->expected ? gir_control_resolve(selected->expected) : NULL;
        gir_control_require(child && child->parent_kind == GIR_CONTROL_CHILD && child->parent == selected &&
            child->stack == selected->stack && child->rollback_end >= selected->write_end);
        gir_control_abandon_tree(child, 0, NULL);
        gir_control_restore_top(child, 0, NULL);
    } else gir_control_require(selected->progress == GIR_CONTROL_BUILT);
    gir_control_restore(selected, snapshot);
    ticket->role = GIR_CONTROL_NAMED_MATERIALIZED;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_exit_selected(uint8_t *token)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && ticket->kind == GIR_CONTROL_TICKET_RESERVED &&
        ticket->role != GIR_CONTROL_WAITING && ticket->receiving);
    if (ticket->role != GIR_CONTROL_FRESH) gir_control_materialize_named(ticket);
    ticket->kind = GIR_CONTROL_TICKET_SELECTED;
    gir_control_attempt *selected = gir_control_resolve(ticket->selected);
    uint8_t mode = ticket->outward_mode || selected != gir_control_resolve(ticket->boundary);
    return gir_control_add_lease(ticket->receiving, selected, mode);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_exit_adopt(uint8_t *control, uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_attempt *selected = gir_control_node(metadata);
    gir_control_capture(selected);
    gir_control_require(receiving->handoff == selected && selected->progress == GIR_CONTROL_BUILT);
    gir_control_attempt *boundary = gir_control_boundary(receiving);
    gir_control_ticket *ticket = gir_control_ticket_new(receiving, boundary, boundary, selected);
    ticket->kind = GIR_CONTROL_TICKET_RECEIVED;
    receiving->handoff = NULL;
    gir_control_node_release(selected);
    return (uint8_t *)ticket;
}
)GIRSUPPORT");
        support.Function("void gir_control_ticket_detach(gir_control_ticket *ticket)", R"GIRSUPPORT({
    gir_control_graph *graph = ticket->graph;
    gir_control_ticket **scope_position = &ticket->scope->tickets;
    while (*scope_position && *scope_position != ticket) scope_position = &(*scope_position)->scope_next;
    gir_control_require(*scope_position == ticket);
    *scope_position = ticket->scope_next;
    gir_control_ticket **graph_position = &graph->tickets;
    while (*graph_position && *graph_position != ticket) graph_position = &(*graph_position)->previous;
    gir_control_require(*graph_position == ticket);
    *graph_position = ticket->previous;
}
)GIRSUPPORT");
        support.Function("void gir_control_ticket_clear_selection(gir_control_ticket *ticket)", R"GIRSUPPORT({
    if (ticket->snapshot_attempt) {
        gir_control_parent_release(ticket->snapshot_attempt, ticket->snapshot.expected);
        gir_control_node_release(ticket->snapshot_attempt);
    }
    if (ticket->boundary) gir_control_node_release(ticket->boundary);
    if (ticket->selected) gir_control_node_release(ticket->selected);
    if (ticket->prepared) gir_control_node_release(ticket->prepared);
    gir_control_owner_release(ticket->source);
    free(ticket->protected_metadata);
    ticket->boundary = ticket->snapshot_attempt = ticket->selected = ticket->prepared = NULL;
    ticket->source = NULL;
    ticket->protected_metadata = NULL;
    ticket->protected_count = 0;
    memset(&ticket->snapshot, 0, sizeof(ticket->snapshot));
    ticket->boundary_start = ticket->payload_start = ticket->payload_end = NULL;
}
)GIRSUPPORT");
        support.Function("void gir_control_ticket_destroy(gir_control_ticket *ticket)", R"GIRSUPPORT({
    gir_control_graph *graph = ticket->graph;
    gir_control_ticket_clear_selection(ticket);
    free(ticket);
    gir_control_graph_release(graph);
}
)GIRSUPPORT");
        support.Function("void gir_control_exit_rearm(uint8_t *token)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_receiving *receiving = ticket->receiving;
    gir_control_require(ticket->authority == GIR_CONTROL_WAITING_RECEIPT && ticket->role != GIR_CONTROL_WAITING &&
        ticket->kind != GIR_CONTROL_TICKET_RECEIVED && ticket->scope == gir_control_scope_top &&
        receiving && receiving->scope == gir_control_scope_top && !receiving->consumed &&
        !receiving->unselected && !receiving->handoff && !ticket->prepared);
    gir_control_attempt *selected = gir_control_resolve(ticket->selected);
    for (gir_control_lease *lease = gir_control_scope_top->leases; lease; lease = lease->next) {
        if (lease->cleanup != GIR_CONTROL_NO_CLEANUP ||
            (!gir_control_descendant(ticket->selected, lease->attempt) &&
             gir_control_resolve(lease->attempt) != selected)) continue;
        gir_control_require(lease->progress != GIR_CONTROL_OPEN && lease->progress != GIR_CONTROL_SUSPENDED &&
            lease->progress != GIR_CONTROL_BUILT && lease->progress != GIR_CONTROL_EXITING);
    }
    for (gir_control_call *call = gir_control_call_top; call && call != gir_control_scope_top->call; call = call->previous)
        for (size_t position = 0; position < call->count; position++)
            gir_control_require(call->outputs[position].receiving != receiving &&
                !gir_control_descendant(ticket->selected, call->outputs[position].attempt) &&
                gir_control_resolve(call->outputs[position].attempt) != selected);
    gir_control_cancel_ticket(ticket, 0, NULL);
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_RESTORED);
    gir_control_ticket_clear_selection(ticket);
    ticket->role = GIR_CONTROL_WAITING;
    ticket->kind = GIR_CONTROL_TICKET_RESERVED;
    ticket->state = GIR_CONTROL_TICKET_ACTIVE;
    ticket->lease_boundary = gir_control_scope_top->next_lease;
}
)GIRSUPPORT");
        support.Function("void gir_control_exit_release(uint8_t *token)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_ticket_detach(ticket);
    gir_control_ticket_destroy(ticket);
}
)GIRSUPPORT");
        support.Function("void gir_control_exit_discard(uint8_t *token, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    if (ticket->role == GIR_CONTROL_WAITING) {
        gir_control_receiving *receiving = ticket->receiving;
        gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && ticket->kind == GIR_CONTROL_TICKET_RESERVED &&
            ticket->scope == gir_control_scope_top && receiving && receiving->scope == gir_control_scope_top &&
            !receiving->unselected && !receiving->consumed);
        gir_control_ticket_detach(ticket);
        gir_control_require(count <= SIZE_MAX / sizeof(*ticket->protected_metadata));
        ticket->protected_count = count;
        ticket->protected_metadata = (uint8_t **)gir_control_alloc((count ? count : 1) * sizeof(*ticket->protected_metadata));
        for (size_t index = 0; index < count; index++) {
            gir_control_find_lease(carried[index]);
            ticket->protected_metadata[index] = carried[index];
        }
        ticket->state = GIR_CONTROL_TICKET_RESTORED;
        receiving->unselected = ticket;
        return;
    }
    gir_control_cancel_ticket(ticket, count, carried);
    gir_control_exit_release(token);
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_exit_prepare(uint8_t *token, uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *payload = lease->attempt;
    gir_control_capture(payload);
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && ticket->kind != GIR_CONTROL_TICKET_RESERVED && !ticket->prepared && payload->progress == GIR_CONTROL_BUILT);
    gir_control_attempt *selected = gir_control_resolve(ticket->selected);
    gir_control_attempt *boundary = gir_control_resolve(ticket->boundary);
    gir_control_require(selected == payload || gir_control_descendant(selected, payload));
    ticket->payload_start = lease->start;
    ticket->payload_end = lease->end;
    gir_control_attempt *anchor = payload;
    while (anchor != boundary) {
        gir_control_require(anchor->parent_kind == GIR_CONTROL_REPLACEMENT && anchor->parent != NULL);
        gir_control_attempt *parent = anchor->parent;
        gir_control_capture(parent);
        gir_control_require(parent->stack == payload->stack &&
            ((parent->progress == GIR_CONTROL_EXITING && parent->expected &&
              gir_control_resolve(parent->expected) == anchor) ||
             parent->progress == GIR_CONTROL_ABANDONED || parent->progress == GIR_CONTROL_CANCELLED));
        anchor = parent;
    }
    gir_control_require(anchor->receiving_start + ticket->view_offset == ticket->boundary_start);
    gir_control_node_retain(anchor);
    ticket->prepared = anchor;
    if (payload != anchor) {
        uint8_t *carried[] = { metadata };
        gir_control_abandon_tree(anchor, 1, carried);
    }
    return ticket->boundary_start;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_exit_commit(uint8_t *token, uint8_t *metadata, uint8_t *start)", R"GIRSUPPORT({
    gir_control_ticket *ticket = (gir_control_ticket *)token;
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *payload = lease->attempt;
    gir_control_attempt *anchor = ticket->prepared;
    gir_control_require(ticket->state == GIR_CONTROL_TICKET_ACTIVE && anchor && start == ticket->boundary_start &&
        ticket->payload_end >= ticket->payload_start &&
        payload->stack->top == start + (ticket->payload_end - ticket->payload_start));
    ptrdiff_t offset = lease->start - payload->receiving_start;
    if (payload != anchor) {
        gir_control_attempt *parent = payload->parent;
        gir_control_require(parent != NULL);
        gir_control_node_retain(parent);
        gir_control_attempt *owner = anchor->parent;
        gir_control_parent_kind kind = anchor->parent_kind;
        if (kind == GIR_CONTROL_CHILD) {
            gir_control_require(owner && owner->expected && gir_control_resolve(owner->expected) == anchor);
        }
        gir_control_set_parent(payload, owner, kind);
        if (kind == GIR_CONTROL_CHILD) owner->expected = payload;
        payload->rollback_end = anchor->rollback_end;
        payload->extension = anchor->extension;
        payload->extension_snapshot = anchor->extension_snapshot;
        while (1) {
            gir_control_attempt *next = parent == anchor ? NULL : parent->parent;
            if (next) {
                gir_control_require(parent->parent_kind == GIR_CONTROL_REPLACEMENT);
                gir_control_node_retain(next);
            }
            gir_control_link_successor(parent, payload);
            gir_control_node_release(parent);
            if (!next) break;
            parent = next;
        }
    }
    payload->receiving_start = start - offset;
    payload->start = start;
    payload->write_end = start + (ticket->payload_end - ticket->payload_start);
    gir_control_progress(payload, GIR_CONTROL_BUILT);
    lease->start = start;
    lease->end = payload->write_end;
    lease->mode = ticket->outward_mode;
    payload->active = lease;
    return metadata;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_receiving_cancel(uint8_t *control, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    gir_control_attempt *attempt = gir_control_boundary(receiving);
    if (receiving->unselected) {
        gir_control_ticket *ticket = receiving->unselected;
        gir_control_require(receiving->scope == gir_control_scope_top && ticket->receiving == receiving &&
            ticket->scope == gir_control_scope_top && ticket->role == GIR_CONTROL_WAITING &&
            ticket->state == GIR_CONTROL_TICKET_RESTORED && !receiving->consumed);
        gir_control_require(ticket->protected_count == count);
        for (size_t index = 0; index < count; index++)
            gir_control_require(ticket->protected_metadata[index] == carried[index]);
        gir_control_ticket *superseding = NULL;
        for (gir_control_ticket *active = receiving->graph->tickets; active; active = active->previous) {
            if (active->receiving != receiving || active->scope != gir_control_scope_top) continue;
            gir_control_require(!superseding &&
                (active->kind == GIR_CONTROL_TICKET_SELECTED || active->kind == GIR_CONTROL_TICKET_RECEIVED) &&
                active->state == GIR_CONTROL_TICKET_ACTIVE && active->role != GIR_CONTROL_WAITING);
            superseding = active;
        }
        if (superseding) {
            uint8_t matching = 0;
            gir_control_attempt *selected = gir_control_resolve(superseding->selected);
            for (size_t index = 0; index < count; index++) {
                gir_control_lease *lease = gir_control_find_lease(carried[index]);
                gir_control_attempt *node = lease->attempt;
                if (lease->progress != GIR_CONTROL_BUILT) continue;
                while (node != selected && node->parent && node->parent_kind == GIR_CONTROL_REPLACEMENT)
                    node = node->parent;
                if (node == selected) matching = 1;
            }
            gir_control_require(matching);
        }
        for (gir_control_lease *lease = gir_control_scope_top->leases; lease; lease = lease->next) {
            if (lease->receiving != receiving) continue;
            uint8_t protected = 0;
            for (size_t index = 0; index < count; index++)
                if (carried[index] == (uint8_t *)&lease->metadata && lease->progress == GIR_CONTROL_BUILT) protected = 1;
            gir_control_require(superseding && protected);
        }
        for (gir_control_call *call = gir_control_call_top; call && call != gir_control_scope_top->call; call = call->previous)
            for (size_t position = 0; position < call->count; position++)
                gir_control_require(call->outputs[position].receiving != receiving);
        receiving->unselected = NULL;
        gir_control_ticket_destroy(ticket);
        if (!superseding) {
            uint8_t *metadata = gir_control_add_lease(receiving, attempt, receiving->outward_mode);
            gir_control_lease *certificate = gir_control_find_lease(metadata);
            attempt->active = NULL;
            certificate->progress = GIR_CONTROL_CANCELLED;
            certificate->cleanup = GIR_CONTROL_UNSELECTED_COMPLETION;
            if (receiving->input) receiving->input->completion = GIR_CONTROL_UNSELECTED_COMPLETION;
            receiving->consumed = 1;
            return metadata;
        }
    }
    gir_control_receiving_selectable(receiving);
    gir_control_abandon_tree(attempt, count, carried);
    gir_control_restore_top(attempt, count, carried);
    if (receiving->extension && attempt->extension && attempt->parent &&
        !gir_control_carried_descendant(attempt, count, carried) &&
        (attempt->progress == GIR_CONTROL_ABANDONED || attempt->progress == GIR_CONTROL_CANCELLED)) {
        gir_control_attempt *parent = attempt->parent;
        if (parent->progress == GIR_CONTROL_SUSPENDED && parent->expected &&
            gir_control_resolve(parent->expected) == attempt) {
            gir_control_require(gir_control_snapshot_matches(parent, &attempt->extension_snapshot));
            gir_control_restore(parent, &attempt->extension_snapshot);
        }
    }
    gir_control_lease *lease = gir_control_scope_top->leases;
    while (lease) {
        gir_control_lease *next = lease->next;
        uint8_t protected = 0;
        for (size_t index = 0; index < count; index++)
            if (carried[index] == (uint8_t *)&lease->metadata) protected = 1;
        if (lease->receiving == receiving && lease->cleanup == GIR_CONTROL_NO_CLEANUP && !protected)
            gir_control_drop_lease((uint8_t *)&lease->metadata);
        lease = next;
    }
    if (receiving->scope == gir_control_scope_top) receiving->consumed = 1;
    uint8_t *metadata = gir_control_add_lease(receiving, attempt, receiving->outward_mode);
    gir_control_find_lease(metadata)->cleanup = GIR_CONTROL_STORAGE_CLEANED;
    return metadata;
}
)GIRSUPPORT");
        support.Function("uint8_t *gir_control_attempt_abandon(uint8_t *metadata, size_t count, uint8_t *const *carried)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    int64_t before = lease->progress;
    gir_control_capture(attempt);
    if (!(before != GIR_CONTROL_BUILT && attempt->progress == GIR_CONTROL_BUILT))
        gir_control_abandon_tree(attempt, count, carried);
    lease->cleanup = GIR_CONTROL_RELEASE_STORAGE;
    for (size_t index = 0; index < count; index++)
        if (gir_control_node(carried[index])->stack == attempt->stack) lease->cleanup = GIR_CONTROL_PRESERVE_STORAGE;
    return metadata;
}
)GIRSUPPORT");
        support.Function("void gir_control_receiving_drop(uint8_t *control)", R"GIRSUPPORT({
    gir_control_receiving *receiving = (gir_control_receiving *)control;
    uint8_t owning = receiving->scope == gir_control_scope_top;
    if (owning) gir_control_require(!receiving->handoff && !receiving->unselected);
    for (gir_control_ticket *ticket = receiving->graph->tickets; ticket; ticket = ticket->previous)
        if (owning || ticket->scope == gir_control_scope_top) gir_control_require(ticket->receiving != receiving);
    for (gir_control_lease *lease = gir_control_scope_top->leases; lease; lease = lease->next) {
        if (lease->receiving != receiving) continue;
        gir_control_require(lease->progress == GIR_CONTROL_BUILT || lease->progress == GIR_CONTROL_ABANDONED ||
                            lease->progress == GIR_CONTROL_CANCELLED || lease->progress == GIR_CONTROL_ATTACHED);
        lease->receiving = NULL;
    }
    for (gir_control_call *call = gir_control_call_top; call; call = call->previous) {
        if (!owning && call == gir_control_scope_top->call) break;
        for (size_t position = 0; position < call->count; position++)
            gir_control_require(call->outputs[position].receiving != receiving);
    }
    if (owning) gir_control_handle_close(receiving);
}
)GIRSUPPORT");
        support.Function("void gir_control_close_graph_handles(gir_control_graph *graph)", R"GIRSUPPORT({
    gir_control_graph_retain(graph);
    for (gir_control_scope *scope = gir_control_scope_top; scope; scope = scope->previous) {
        gir_control_receiving *receiving = scope->receivers;
        while (receiving) {
            gir_control_receiving *next = receiving->next;
            if (receiving->graph == graph) {
                gir_control_require(scope == gir_control_scope_top);
                for (gir_control_lease *lease = scope->leases; lease; lease = lease->next)
                    if (lease->receiving == receiving) lease->receiving = NULL;
                gir_control_handle_close(receiving);
            }
            receiving = next;
        }
    }
    gir_control_graph_release(graph);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_cancel(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_lease *lease = gir_control_find_lease(metadata);
    gir_control_attempt *attempt = lease->attempt;
    gir_control_receiving *receiving = lease->receiving;
    if (lease->cleanup == GIR_CONTROL_UNSELECTED_COMPLETION) {
        gir_control_require(lease->progress == GIR_CONTROL_CANCELLED && attempt->active != lease);
        uint8_t close = receiving && receiving->scope == gir_control_scope_top && receiving->consumed;
        gir_control_drop_lease(metadata);
        if (close) gir_control_handle_close(receiving);
        return;
    }
    gir_control_capture(attempt);
    gir_control_require(attempt->progress == GIR_CONTROL_ABANDONED || attempt->progress == GIR_CONTROL_CANCELLED ||
                        attempt->progress == GIR_CONTROL_BUILT);
    if (attempt->progress != GIR_CONTROL_BUILT) {
        gir_control_require(lease->cleanup != GIR_CONTROL_NO_CLEANUP);
        if (lease->cleanup == GIR_CONTROL_RELEASE_STORAGE) gir_control_restore_top(attempt, 0, NULL);
        gir_control_progress(attempt, GIR_CONTROL_CANCELLED);
    }
    uint8_t close = receiving && receiving->scope == gir_control_scope_top && (!receiving->exposed || receiving->consumed);
    gir_control_drop_lease(metadata);
    if (close) gir_control_handle_close(receiving);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_child(uint8_t *parent_metadata, uint8_t *child_metadata)", R"GIRSUPPORT({
    gir_control_attempt *parent = gir_control_node(parent_metadata);
    gir_control_attempt *child = gir_control_node(child_metadata);
    gir_control_capture(parent);
    gir_control_capture(child);
    gir_control_require(parent->progress == GIR_CONTROL_OPEN && !parent->expected &&
                        child->progress == GIR_CONTROL_OPEN && child->metadata.count == 0 &&
                        parent->stack == child->stack && !child->parent);
    gir_control_set_parent(child, parent, GIR_CONTROL_CHILD);
    parent->expected = child;
    gir_control_progress(parent, GIR_CONTROL_SUSPENDED);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_finish(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_attempt *attempt = gir_control_node(metadata);
    gir_control_capture(attempt);
    gir_control_require(attempt->progress == GIR_CONTROL_OPEN);
    attempt->write_end = attempt->stack->top;
    gir_control_find_lease(metadata)->end = attempt->write_end;
    gir_control_progress(attempt, GIR_CONTROL_BUILT);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_attach(uint8_t *parent_metadata, uint8_t *child_metadata)", R"GIRSUPPORT({
    gir_control_attempt *parent = gir_control_node(parent_metadata);
    gir_control_attempt *child = gir_control_node(child_metadata);
    gir_control_capture(parent);
    gir_control_capture(child);
    gir_control_require(parent->progress == GIR_CONTROL_SUSPENDED && child->progress == GIR_CONTROL_BUILT &&
                        !child->staging.cursor &&
                        parent->expected && gir_control_resolve(parent->expected) == child &&
                        child->parent_kind == GIR_CONTROL_CHILD && child->parent == parent);
    parent->expected = NULL;
    gir_control_progress(parent, GIR_CONTROL_OPEN);
    gir_control_progress(child, GIR_CONTROL_ATTACHED);
    gir_control_set_parent(child, NULL, GIR_CONTROL_ROOT);
    gir_control_graph *graph = child->graph;
    gir_control_close_graph_handles(graph);
    gir_control_drop_lease(child_metadata);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_publish(uint8_t *metadata)", R"GIRSUPPORT({
    gir_control_attempt *attempt = gir_control_node(metadata);
    gir_control_capture(attempt);
    gir_control_require(attempt->progress == GIR_CONTROL_BUILT && !attempt->graph->tickets && !attempt->staging.cursor);
    gir_control_progress(attempt, GIR_CONTROL_PUBLISHED);
    gir_control_graph *graph = attempt->graph;
    gir_control_close_graph_handles(graph);
    gir_control_drop_lease(metadata);
}
)GIRSUPPORT");
        support.Function("void gir_control_attempt_return(uint8_t *metadata)", R"GIRSUPPORT({ gir_control_drop_lease(metadata); }
)GIRSUPPORT");
    }


    const GirModule &m;
    optional<string> constructionTrace;

    // ---------------------------------------------------------------------
    // Names and types.

    static string Sanitize(const string &s) {
        string out;
        for (auto c : s) out += isalnum((unsigned char)c) ? c : '_';
        return out;
    }

    static string StableKeySymbol(const string &key) {
        static constexpr char digits[] = "0123456789abcdef";
        string out;
        for (unsigned char byte : key) {
            if ((byte >= 'a' && byte <= 'z') || (byte >= 'A' && byte <= 'Z') ||
                (byte >= '0' && byte <= '9')) out += byte;
            else {
                out += '_';
                out += digits[byte >> 4];
                out += digits[byte & 15];
            }
        }
        return out;
    }

    // The names of what is emitted come from stable keys where the module
    // carries them, so that nothing is named by order of arrival.
    vector<string> fsym, gsym, filesym;
    map<string, string> literals;          // Text -> the constant that holds it.
    set<int64_t> blobs;                    // Sizes of the byte blocks globals take.
    map<string, int> runs;

    void Names() {
        set<string> used;
        auto name = [&](string n) {
            if (!used.insert(n).second) throw CompileError { cat("symbol collision: ", n) };
            return n;
        };
        for (size_t f = 0; f < m.funcs.size(); f++) {
            auto &fn = m.funcs[f];
            fsym.push_back(name(fn.key.empty() ? cat("gir_f", f, "_", Sanitize(fn.name))
                                               : cat(Sanitize(fn.name), "_g_", StableKeySymbol(fn.key))));
        }
        for (size_t g = 0; g < m.lowglobals.size(); g++) {
            auto &lg = m.lowglobals[g];
            gsym.push_back(lg.module.empty() ? cat(Sanitize(lg.name), "_g", g)
                                             : cat(Sanitize(lg.name), "_g_",
                                                   Sha256::Of(cat(lg.module, "::", lg.name)).Short()));
            if (lg.kind == GirMember::Bytes) blobs.insert(lg.size);
        }
        for (size_t i = 0; i < m.files.size(); i++)
            filesym.push_back(i < m.filemodules.size() && !m.filemodules[i].empty()
                                  ? cat("gs_file_", Sha256::Of(m.filemodules[i]).Short())
                                  : cat("gs_file_", i));
        for (auto &f : m.funcs)
            for (auto &b : f.blocks)
                for (auto &i : b.insts) {
                    string byteText(i.bytes.begin(), i.bytes.end());
                    auto text = i.op == GirOp::StaticBytes ? &byteText
                                : i.op == GirOp::RtCall && (GirRt)i.idx == GirRt::OutText ? &i.text
                                : i.op == GirOp::Abort && i.abort == GirAbortKind::UserAbort ? &i.text : nullptr;
                    if (text && (i.op == GirOp::StaticBytes || !text->empty()) && !literals.count(*text))
                        literals[*text] = cat("gs_str_", Sha256::Of(*text).Short());
                }
    }

    static string SegName(const string &module) { return "gs_seg_" + UnitSegmentId(module); }

    string FName(int f) const { return fsym[f]; }

    static const char *Sfx(CoreIntTy t) { return CoreIntName(t); }

    static const char *IntCT(CoreIntTy t) {
        static const char *names[] = { "int8_t", "int16_t", "int32_t", "int64_t",
                                       "uint8_t", "uint16_t", "uint32_t", "uint64_t" };
        return names[(int)t];
    }

    string CT(GirTypeId t) const {
        auto &c = m.Type(t);
        switch (c.kind) {
            case CoreType::Int: return IntCT(c.ity);
            case CoreType::Bool: return "uint8_t";
            default: return "uint8_t *";
        }
    }

    static string CStr(const string &s) {
        string out = "\"";
        for (auto ch : s) {
            auto c = (unsigned char)ch;
            if (c == '"' || c == '\\') { out += '\\'; out += ch; }
            else if (c >= 32 && c < 127 && c != '?') out += ch;
            else {
                char buf[8];
                snprintf(buf, sizeof buf, "\\%03o", c);
                out += buf;
            }
        }
        return out + "\"";
    }

    // A C literal of the integer type `t` from its decimal text.
    string Lit(CoreIntTy t, const string &text) const {
        if (CoreIsUnsigned(t)) return cat("(", IntCT(t), ")", text, "ULL");
        if (text == "-9223372036854775808") return "(-9223372036854775807LL - 1)";
        return cat("(", IntCT(t), ")(", text, "LL)");
    }

    static string IntStr(int64_t v) {
        if (v == INT64_MIN) return "(-9223372036854775807LL - 1)";
        if (v == INT32_MIN) return "(-2147483647 - 1)";
        if (v > INT32_MAX || v < INT32_MIN) return cat(v, "LL");
        return cat(v);
    }

    // The range of values a type holds, as i64 bounds: a u64's is its
    // 0..i64.max part, which is all an `as` into it can keep.
    static pair<int64_t, int64_t> Range(CoreIntTy t) {
        switch (t) {
            case CoreIntTy::I8: return { -128, 127 };
            case CoreIntTy::I16: return { -32768, 32767 };
            case CoreIntTy::I32: return { INT32_MIN, INT32_MAX };
            case CoreIntTy::U8: return { 0, 255 };
            case CoreIntTy::U16: return { 0, 65535 };
            case CoreIntTy::U32: return { 0, (int64_t)UINT32_MAX };
            case CoreIntTy::U64: return { 0, INT64_MAX };
            default: return { INT64_MIN, INT64_MAX };
        }
    }

    string Where(int org) const {
        if (org < 0 || org >= (int)m.origins.size()) return cat(filesym.empty() ? string("gs_file_0") : filesym[0], ", 0");
        return cat(filesym[m.origins[org].file], ", ", m.origins[org].line);
    }

    // ---------------------------------------------------------------------
    // One function.

    struct Ctx {
        const GirFunc *f;
        vector<GirTypeId> vt;
        vector<int> callees, files;
        GirSourceClassification sourceKinds;
    };

    string V(int v) const { return cat("v", v); }

    GirCPiece Piece(int fi) {
        auto &f = m.funcs[fi];
        Ctx cx { &f, {}, {}, {}, GirSourceKinds(f) };
        int n = 0;
        for (auto &b : f.blocks) {
            n += (int)b.params.size();
            for (auto &i : b.insts) n += GirDefinesValue(i);
        }
        cx.vt.assign(n, -1);
        for (auto &b : f.blocks) for (auto &p : b.params) cx.vt[p.first] = p.second;
        // Until nothing changes, so that a value defined after its use in
        // table order still gets its type.
        for (auto changed = true; changed;) {
            changed = false;
            for (auto &b : f.blocks)
                for (auto &i : b.insts)
                    if (GirDefinesValue(i) && cx.vt[i.res] < 0) {
                        cx.vt[i.res] = ResultType(f, cx, i);
                        changed |= cx.vt[i.res] >= 0;
                    }
        }
        GirCPiece p;
        p.name = FName(fi);
        string ret = f.results.empty() ? "void" : CT(f.results[0]);
        string proto = cat("static ", ret, " ", p.name, "(");
        auto &entry = f.blocks[0];
        for (size_t k = 0; k < entry.params.size(); k++) {
            if (k) proto += ", ";
            Append(proto, CT(entry.params[k].second), " ", V(entry.params[k].first));
        }
        proto += ")";
        p.prototype = proto;
        string t = proto + " {\n";
        for (size_t k = 0; k < f.members.size(); k++) {
            auto &mem = f.members[k];
            switch (mem.kind) {
                case GirMember::Scalar:
                    if (constructionTrace || cx.sourceKinds.members[k] <= GirSourceKind::Ordinary)
                        Append(t, "    ", CT(mem.ty), " m", k, m.Type(mem.ty).kind == CoreType::Ptr ? " = NULL;\n" : ";\n");
                    break;
                case GirMember::Bytes: Append(t, "    uint64_t m", k, "[", (mem.size + 7) / 8, "];\n"); break;
                case GirMember::Header: Append(t, "    gir_hdr m", k, ";\n"); break;
                case GirMember::Dynamic: Append(t, "    uint8_t *m", k, ";\n"); break;
            }
        }
        for (size_t b = 0; b < f.blocks.size(); b++) {
            for (size_t k = b == 0 ? entry.params.size() : 0; k < f.blocks[b].params.size(); k++)
                if (constructionTrace || cx.sourceKinds.values[f.blocks[b].params[k].first] <= GirSourceKind::Ordinary) Append(t, "    ", CT(f.blocks[b].params[k].second), " ", V(f.blocks[b].params[k].first), m.Type(f.blocks[b].params[k].second).kind == CoreType::Ptr ? " = NULL;\n" : ";\n");
            for (auto &i : f.blocks[b].insts)
                if (GirDefinesValue(i) && (constructionTrace || cx.sourceKinds.values[i.res] <= GirSourceKind::Ordinary)) Append(t, "    ", CT(cx.vt[i.res]), " ", V(i.res), m.Type(cx.vt[i.res]).kind == CoreType::Ptr ? " = NULL;\n" : ";\n");
        }
        for (size_t b = 0; b < f.blocks.size(); b++) {
            Append(t, "  b", b, ":;\n");
            for (auto &i : f.blocks[b].insts) Inst(t, cx, i);
        }
        t += "}\n";
        p.text = std::move(t);
        p.callees = cx.callees;
        p.files = cx.files;
        return p;
    }

    // The type an instruction's value has: the verifier has checked it, so it
    // is read off the instruction.
    GirTypeId ResultType(const GirFunc &f, const Ctx &cx, const GirInst &i) {
        auto &mm = const_cast<GirModule &>(m);
        vector<pair<vector<GirTypeId>, vector<GirTypeId>>> sigs;
        for (auto &g : m.funcs) sigs.push_back({ g.params, g.results });
        GirTyEnv env { mm, f.slots, sigs, cx.vt, &f.members };
        auto r = GirTyper(env).Of(i);
        return r.ok() ? r.ty : -1;
    }

    void Mention(Ctx &cx, int org) {
        if (org >= 0 && org < (int)m.origins.size()) cx.files.push_back(m.origins[org].file);
    }

    string Assigns(const Ctx &cx, int block, const vector<int> &args) {
        auto &parameters = cx.f->blocks[block].params;
        vector<size_t> selected;
        for (size_t position = 0; position < parameters.size(); position++)
            if (constructionTrace || cx.sourceKinds.values[parameters[position].first] <= GirSourceKind::Ordinary) selected.push_back(position);
        string out;
        for (auto position : selected) {
            auto [value, type] = parameters[position];
            Append(out, "{ ", CT(type), " t", position, " = ", V(args[position]), "; ");
            if (constructionTrace && cx.sourceKinds.values[value] == GirSourceKind::Descriptor) Append(out, "gir_source_retain((gir_source *)t", position, "); ");
        }
        for (auto position : selected) {
            auto value = parameters[position].first;
            if (constructionTrace && cx.sourceKinds.values[value] == GirSourceKind::Descriptor)
                Append(out, "gir_source_assign(&", V(value), ", (gir_source *)t", position, "); ");
            else Append(out, V(value), " = t", position, "; ");
        }
        for (auto position : selected) {
            if (constructionTrace && cx.sourceKinds.values[parameters[position].first] == GirSourceKind::Descriptor)
                Append(out, "gir_source_release((gir_source *)t", position, "); ");
        }
        for (auto position : selected) { (void)position; out += "} "; }
        return out;
    }

    static const char *CmpOp(CoreCmpOp o) {
        static const char *ops[] = { "==", "!=", "<", "<=", ">", ">=" };
        return ops[(int)o];
    }

    void Inst(string &t, Ctx &cx, const GirInst &i) {
        auto &f = *cx.f;
        auto L = [&](auto &&...parts) { Append(t, "    ", parts..., "\n"); };
        auto ty = [&](int v) { return m.Type(cx.vt[v]); };
        if (auto contract = GirControlOf(i.op)) {
            vector<string> arguments;
            auto argument = [&](int value) { arguments.push_back(V(value)); };
            auto array = [&] {
                string values;
                for (auto value : i.vals) Append(values, values.empty() ? "" : ", ", V(value));
                arguments.push_back(std::to_string(i.vals.size()));
                arguments.push_back(i.vals.empty() ? "NULL" : cat("(uint8_t *const[]){ ", values, " }"));
            };
            switch (contract->form) {
                case GirControlForm::None: break;
                case GirControlForm::Operand: argument(i.a); break;
                case GirControlForm::Pair: argument(i.a); argument(i.b); break;
                case GirControlForm::Values: array(); break;
                case GirControlForm::OperandValues: argument(i.a); array(); break;
                case GirControlForm::PairValues:
                    argument(i.a); argument(i.b);
                    for (auto value : i.vals) argument(value);
                    break;
                case GirControlForm::Parameter: arguments.push_back(std::to_string(i.idx)); break;
                case GirControlForm::OperandParameter:
                    argument(i.a); arguments.push_back(std::to_string(i.idx));
                    break;
                case GirControlForm::Source:
                    argument(i.a);
                    if (auto binding = GirNamedExitBinding(i.exitSource)) {
                        arguments.push_back("1");
                        argument(*binding);
                    } else {
                        arguments.push_back("0");
                        arguments.push_back("NULL");
                    }
                    break;
                case GirControlForm::TargetPositions: {
                    arguments.push_back(std::to_string(i.idx));
                    arguments.push_back(std::to_string(i.ownerPositions.size()));
                    string positions;
                    for (auto position : i.ownerPositions) Append(positions, positions.empty() ? "" : ", ", position ? std::to_string(*position) : "-1");
                    arguments.push_back(i.ownerPositions.empty() ? "NULL" : cat("(int64_t[]){ ", positions, " }"));
                    break;
                }
                case GirControlForm::TargetResult:
                    argument(i.a);
                    arguments.push_back(std::to_string(i.idx));
                    arguments.push_back(std::to_string(i.idx2));
                    break;
                case GirControlForm::Call: {
                    auto &results = *m.funcs[i.idx].lowResults;
                    size_t channel = 0;
                    string values;
                    for (auto &result : results) {
                        if (!values.empty()) values += ", ";
                        values += holds_alternative<GirLowNonfixedResult>(result.layout) ? V(i.vals[channel++]) : "NULL";
                    }
                    arguments.push_back(std::to_string(results.size()));
                    arguments.push_back(results.empty() ? "NULL" : cat("(uint8_t *const[]){ ", values, " }"));
                    string bindings;
                    for (auto binding : i.ownerBindings) Append(bindings, bindings.empty() ? "" : ", ", binding ? V(*binding) : "NULL");
                    arguments.push_back(std::to_string(i.ownerBindings.size()));
                    arguments.push_back(i.ownerBindings.empty() ? "NULL" : cat("(uint8_t *const[]){ ", bindings, " }"));
                    break;
                }
            }
            string args;
            for (auto &value : arguments) Append(args, args.empty() ? "" : ", ", value);
            string call = cat("gir_", string(contract->wire + 2), "(", args, ");");
            if (contract->result) L(V(i.res), " = ", call);
            else L(call);
            return;
        }
        switch (i.op) {
            case GirOp::Int: L(V(i.res), " = ", Lit(m.Type(i.ty).ity, i.text), ";"); return;
            case GirOp::Bool: L(V(i.res), " = ", i.flag ? 1 : 0, ";"); return;
            case GirOp::Bin: return EmitBin(t, cx, i);
            case GirOp::Un: {
                auto it = m.Type(i.ty).ity;
                if (i.un == CoreUnOp::Neg && i.flag) {
                    Mention(cx, i.org);
                    L(V(i.res), " = gs_neg_", Sfx(it), "(", V(i.a), ", ", Where(i.org), ");");
                } else if (i.un == CoreUnOp::Neg) {
                    L(V(i.res), " = (", IntCT(it), ")(0u - (uint64_t)", V(i.a), ");");
                } else {
                    L(V(i.res), " = (", IntCT(it), ")~", V(i.a), ";");
                }
                return;
            }
            case GirOp::Cmp: L(V(i.res), " = ", V(i.a), " ", CmpOp(i.cmp), " ", V(i.b), ";"); return;
            case GirOp::Not: L(V(i.res), " = !", V(i.a), ";"); return;
            case GirOp::Conv: return EmitConv(t, cx, i);
            case GirOp::Call: {
                cx.callees.push_back(i.idx);
                Mention(cx, i.org);
                string args;
                for (size_t k = 0; k < i.vals.size(); k++) Append(args, k ? ", " : "", V(i.vals[k]));
                auto &callee = m.funcs[i.idx];
                if (callee.results.empty()) L(FName(i.idx), "(", args, ");");
                else L(V(i.res), " = ", FName(i.idx), "(", args, ");");
                return;
            }
            case GirOp::PtrOffset:
                L(V(i.res), " = ", V(i.a), " + ", V(i.b), " * (int64_t)", i.idx, ";");
                return;
            case GirOp::PtrEq: L(V(i.res), " = ", V(i.a), " == ", V(i.b), ";"); return;
            case GirOp::PLoad:
                if (CoreHasConstruction(m.profile)) L("memcpy(&", V(i.res), ", ", V(i.a), ", sizeof(", V(i.res), "));");
                else L(V(i.res), " = *(", CT(i.ty), " *)", V(i.a), ";"); return;
            case GirOp::PStore:
                if (CoreHasConstruction(m.profile)) L("memcpy(", V(i.a), ", &", V(i.b), ", sizeof(", V(i.b), "));");
                else L("*(", CT(i.ty), " *)", V(i.a), " = ", V(i.b), ";"); return;
            case GirOp::FrameAddr: {
                auto &mem = f.members[i.idx];
                if (mem.kind == GirMember::Bytes) L(V(i.res), " = (uint8_t *)m", i.idx, ";");
                else L(V(i.res), " = (uint8_t *)&m", i.idx, ";");
                return;
            }
            case GirOp::LocalGet:
                if (!constructionTrace && cx.sourceKinds.values[i.res] > GirSourceKind::Ordinary) return;
                if (constructionTrace && cx.sourceKinds.values[i.res] == GirSourceKind::Descriptor) L("gir_source_assign(&", V(i.res), ", (gir_source *)m", i.idx, ");");
                else L(V(i.res), " = m", i.idx, ";"); return;
            case GirOp::LocalSet:
                if (!constructionTrace && cx.sourceKinds.members[i.idx] > GirSourceKind::Ordinary) return;
                if (constructionTrace && cx.sourceKinds.members[i.idx] == GirSourceKind::Descriptor) L("gir_source_assign(&m", i.idx, ", (gir_source *)", V(i.a), ");");
                else L("m", i.idx, " = ", V(i.a), ";"); return;
            case GirOp::StackAt:
                L(V(i.res), " = (uint8_t *)", CoreHasConstruction(m.profile) ? "gir_stack_at(" : "GS(",
                  V(i.a), CoreHasConstruction(m.profile) ? ", " : " + ", i.idx, ");"); return;
            case GirOp::StackMark: L(V(i.res), " = ((gs_stack *)", V(i.a), ")->top;"); return;
            case GirOp::StackRelease: L("((gs_stack *)", V(i.a), ")->top = ", V(i.b), ";"); return;
            case GirOp::StackBump:
                if (i.b >= 0) L("((gs_stack *)", V(i.a), ")->top += ", V(i.b), ";");
                else L("((gs_stack *)", V(i.a), ")->top += ", i.idx, ";");
                return;
            case GirOp::GlobalAddr: L(V(i.res), " = (uint8_t *)&GS_GL->", gsym[i.idx], ";"); return;
            case GirOp::GlobalStack: L(V(i.res), " = (uint8_t *)&GS_GL->gs_gstk_", gsym[i.idx], ";"); return;
            case GirOp::HdrBase:
                if (CoreHasConstruction(m.profile)) L("memcpy(&", V(i.res), ", ", V(i.a), ", sizeof(", V(i.res), "));");
                else L(V(i.res), " = ((gir_hdr *)", V(i.a), ")->base;"); return;
            case GirOp::HdrLen:
                if (CoreHasConstruction(m.profile)) L("memcpy(&", V(i.res), ", ", V(i.a), " + 8, sizeof(", V(i.res), "));");
                else L(V(i.res), " = ((gir_hdr *)", V(i.a), ")->len;"); return;
            case GirOp::HdrInit:
                if (CoreHasConstruction(m.profile)) {
                    L("memcpy(", V(i.a), ", &", V(i.b), ", sizeof(", V(i.b), "));");
                    L("memset(", V(i.a), " + 8, 0, 8);");
                } else {
                    L("((gir_hdr *)", V(i.a), ")->base = ", V(i.b), ";");
                    L("((gir_hdr *)", V(i.a), ")->len = 0;");
                }
                return;
            case GirOp::HdrSetLen:
                if (CoreHasConstruction(m.profile)) L("memcpy(", V(i.a), " + 8, &", V(i.b), ", sizeof(", V(i.b), "));");
                else L("((gir_hdr *)", V(i.a), ")->len = ", V(i.b), ";"); return;
            case GirOp::BytesCopy:
                L("gs_memcpy(", V(i.a), ", ", V(i.b), ", (size_t)", V(i.vals[0]), ");");
                return;
            case GirOp::BytesMove:
                L("gs_memmove(", V(i.a), ", ", V(i.b), ", (size_t)", V(i.vals[0]), ");");
                return;
            case GirOp::BytesFill:
                L("for (int64_t k = 0; k < ", V(i.vals[0]), "; k++) gs_memcpy(", V(i.a), " + k * (int64_t)", i.idx,
                  ", ", V(i.b), ", (size_t)", i.idx, ");");
                return;
            case GirOp::RtCall: return EmitRt(t, cx, i);
            case GirOp::StaticBytes:
                L(V(i.res), " = (uint8_t *)", literals.at(string(i.bytes.begin(), i.bytes.end())), ";"); return;
            case GirOp::ReturnFlagGet: L(V(i.res), " = gir_return_flag;"); return;
            case GirOp::ReturnFlagSet: L("gir_return_flag = ", V(i.a), ";"); return;
            case GirOp::TargetLoad: L(V(i.res), " = gir_target_", i.idx, "_", i.idx2, ";"); return;
            case GirOp::TargetStore: L("gir_target_", i.idx, "_", i.idx2, " = ", V(i.a), ";"); return;
            case GirOp::Format:
                L(V(i.res), " = gs_fmt_", i.format == GirFormatKind::Int ? "i64" :
                  i.format == GirFormatKind::Uint ? "u64" : "bool", "(", V(i.b), ", ", V(i.a), ");");
                return;
            case GirOp::OutBytes:
                Mention(cx, i.org);
                L("gs_out_bytes(", V(i.a), ", (size_t)", V(i.b), ");"); return;
            case GirOp::SourceNew:
                if (constructionTrace) {
                    string path = "(const int64_t[]){";
                    for (auto value : i.vals) { if (path.back() != '{') path += ','; path += V(value); }
                    path += i.vals.empty() ? "0}" : "}";
                    L("gir_source_assign(&", V(i.res), ", gir_source_new(", V(i.a), ", ", i.vals.size(), ", ", path, "));");
                } else {}
                return;
            case GirOp::SourceChild:
                if (constructionTrace) L("gir_source_assign(&", V(i.res), ", gir_source_child((gir_source *)", V(i.a), ", ", V(i.b), "));");
                else {}
                return;
            case GirOp::SourceGlobal:
                if (constructionTrace) L("gir_source_assign(&", V(i.res), ", gir_global_sources[", i.idx, "]);");
                else {} return;
            case GirOp::SourceGlobalSet:
                if (constructionTrace) L("gir_source_global_set(", i.idx, ", (gir_source *)", V(i.a), ");"); return;
            case GirOp::SourceParam:
                if (constructionTrace) L("gir_source_assign(&", V(i.res), ", gir_source_param(", i.idx, "));");
                else {}
                return;
            case GirOp::SourceEnter:
                if (constructionTrace) L(V(i.res), " = gir_source_enter();"); return;
            case GirOp::SourceCallPush:
                if (constructionTrace) {
                    string arguments = "(gir_source *[]){";
                    for (auto source : i.vals) { if (arguments.back() != '{') arguments += ','; arguments += source >= 0 ? cat("(gir_source *)", V(source)) : string("NULL"); }
                    arguments += i.vals.empty() ? "NULL}" : "}";
                    L(V(i.res), " = gir_source_call_push(", i.vals.size(), ", ", arguments, ");");
                } else {}
                return;
            case GirOp::SourceCallGet:
                if (constructionTrace) L("gir_source_assign(&", V(i.res), ", gir_source_call_get(", V(i.a), ", ", i.idx, "));");
                else {}
                return;
            case GirOp::SourceLeave:
                if (constructionTrace) L("gir_source_leave(", V(i.a), ");"); return;
            case GirOp::SourceCallPop:
                if (constructionTrace) L("gir_source_call_pop(", V(i.a), ");"); return;
            case GirOp::SourceResult:
                if (constructionTrace) L("gir_source_result(", i.idx, ", (gir_source *)", V(i.a), ");"); return;
            case GirOp::SourceCopy:
                if (constructionTrace) L("gir_source_copy((gir_source *)", V(i.a), ", ", V(i.b), ");"); return;
            case GirOp::SourceTargetEnter:
                if (constructionTrace) {
                    string positions = "(const int64_t[]){";
                    for (auto position : i.vals) { if (positions.back() != '{') positions += ','; positions += to_string(position); }
                    positions += i.vals.empty() ? "-1}" : "}";
                    L(V(i.res), " = gir_source_target_enter(", i.idx, ", ", i.vals.size(), ", ", positions, ");");
                }
                return;
            case GirOp::SourceTargetLeave:
                if (constructionTrace) L("gir_source_target_leave(", V(i.a), ");"); return;
            case GirOp::SourceTargetResult:
                if (constructionTrace) L("gir_source_target_result(", i.idx, ", ", i.idx2, ", (gir_source *)", V(i.a), ");"); return;
            case GirOp::SourceTargetGet:
                if (constructionTrace) L("gir_source_assign(&", V(i.res), ", gir_source_target_get(", V(i.a), ", ", i.idx, "));"); return;
            case GirOp::TraceId:
                if (constructionTrace) L(V(i.res), " = gir_trace_", GirTraceName(i.trace), "++;");
                else L(V(i.res), " = 0;");
                return;
            case GirOp::Event:
                if (constructionTrace) {
                    string operands;
                    for (auto value : i.vals) Append(operands, operands.empty() ? "" : ", ", V(value));
                    L("gir_trace_record(\"", GirEventName(i.event), "\", \"", GirEventReasonName(i.reason),
                      "\", ", i.vals.size(), ", (const int64_t[]){ ", operands, " });");
                }
                return;
            case GirOp::Br:
                L(Assigns(cx, i.idx, i.vals), "goto b", i.idx, ";");
                return;
            case GirOp::CondBr:
                L("if (", V(i.a), ") { ", Assigns(cx, i.idx, i.vals), "goto b", i.idx, "; } else { ",
                  Assigns(cx, i.idx2, i.vals2), "goto b", i.idx2, "; }");
                return;
            case GirOp::Ret:
                if (i.vals.empty()) L("return;");
                else L("return ", V(i.vals[0]), ";");
                return;
            case GirOp::Abort: {
                Mention(cx, i.org);
                switch (i.abort) {
                    case GirAbortKind::IndexOob:
                        L("gs_idxfail(", V(i.vals[0]), ", ", V(i.vals[1]), ", ", Where(i.org), ");");
                        break;
                    case GirAbortKind::PopEmpty: L("gs_abort(GS_E_POP, ", Where(i.org), ");"); break;
                    case GirAbortKind::PopNRange: L("gs_abort(GS_E_POPN, ", Where(i.org), ");"); break;
                    case GirAbortKind::ResizeNegative:
                        L("gs_abort(GS_E_RESIZENEG, ", Where(i.org), ");");
                        break;
                    case GirAbortKind::ResizeFill:
                        L("gs_abort(GS_E_RESIZEFILL, ", Where(i.org), ");");
                        break;
                    case GirAbortKind::Capacity: L("gs_abort(GS_E_CAPACITY, ", Where(i.org), ");"); break;
                    case GirAbortKind::SliceOob: L("gs_abort(GS_E_SLICE, ", Where(i.org), ");"); break;
                    case GirAbortKind::Assert: L("gs_abort(GS_E_ASSERT, ", Where(i.org), ");"); break;
                    case GirAbortKind::UserAbort:
                        L("gs_abort_msg(", i.text.empty() ? string("(const uint8_t *)\"\"") : literals.at(i.text), ", ",
                          i.text.size(), ", ", Where(i.org), ");");
                        break;
                    default: L("gs_abort(GS_E_ASSERT, ", Where(i.org), ");"); break;
                }
                return;
            }
            case GirOp::Exit: L("gs_exit(", V(i.a), ");"); return;
            case GirOp::Unreachable: L("for (;;) { }"); return;
            default: throw CompileError { "internal compiler error: unsupported GIR-L emission operation" };
        }
        (void)ty;
    }

    void EmitBin(string &t, Ctx &cx, const GirInst &i) {
        auto it = m.Type(i.ty).ity;
        auto T = IntCT(it);
        auto a = V(i.a), b = V(i.b), r = V(i.res);
        auto L = [&](auto &&...parts) { Append(t, "    ", parts..., "\n"); };
        auto u = CoreIsUnsigned(it);
        switch (i.bin) {
            case CoreBinOp::Add: case CoreBinOp::Sub: case CoreBinOp::Mul: {
                static const char *names[] = { "add", "sub", "mul" };
                static const char *ops[] = { "+", "-", "*" };
                auto k = (int)i.bin;
                if (i.flag) {
                    Mention(cx, i.org);
                    if (u) L(r, " = gs_", names[k], "_", Sfx(it), "(", a, ", ", b, ");");
                    else L(r, " = gs_", names[k], "_", Sfx(it), "(", a, ", ", b, ", ", Where(i.org), ");");
                } else {
                    L(r, " = (", T, ")((uint64_t)", a, " ", ops[k], " (uint64_t)", b, ");");
                }
                return;
            }
            case CoreBinOp::Div: case CoreBinOp::Mod:
                Mention(cx, i.org);
                L(r, " = gs_", i.bin == CoreBinOp::Div ? "div" : "mod", "_", Sfx(it), "(", a, ", ", b, ", ",
                  Where(i.org), ");");
                return;
            case CoreBinOp::BitAnd: L(r, " = (", T, ")(", a, " & ", b, ");"); return;
            case CoreBinOp::BitOr: L(r, " = (", T, ")(", a, " | ", b, ");"); return;
            case CoreBinOp::BitXor: L(r, " = (", T, ")(", a, " ^ ", b, ");"); return;
            case CoreBinOp::Shl: L(r, " = gs_shl_", Sfx(it), "(", a, ", (int64_t)", b, ");"); return;
            case CoreBinOp::Shr: L(r, " = gs_shr_", Sfx(it), "(", a, ", (int64_t)", b, ");"); return;
        }
    }

    // `as` range-checks in the debug profile through the runtime's checks, with
    // the same bounds the legacy backend states; the other conversions are casts.
    void EmitConv(string &t, Ctx &cx, const GirInst &i) {
        auto st = m.Type(i.ty).ity, dt = m.Type(i.ty2).ity;
        auto T = IntCT(dt);
        auto r = V(i.res), x = V(i.a);
        auto L = [&](auto &&...parts) { Append(t, "    ", parts..., "\n"); };
        if (i.conv != CoreConvKind::As || st == dt) { L(r, " = (", T, ")(", x, ");"); return; }
        Mention(cx, i.org);
        auto named = cat("\"", CoreIntName(dt), "\", ", Where(i.org));
        if (st == CoreIntTy::U64) {
            auto hi = (uint64_t)Range(dt).second;
            L(r, " = (", T, ")GS_RANGE_U(", x, ", ", hi, "ULL, ", named, ");");
            return;
        }
        auto [slo, shi] = Range(st);
        auto [lo, hi] = Range(dt);
        if (slo >= lo && shi <= hi) { L(r, " = (", T, ")(", x, ");"); return; }
        L(r, " = (", T, ")GS_RANGE((int64_t)(", x, "), ", IntStr(lo), ", ", IntStr(hi), ", ", named, ");");
    }

    void EmitRt(string &t, Ctx &cx, const GirInst &i) {
        (void)cx;
        auto L = [&](auto &&...parts) { Append(t, "    ", parts..., "\n"); };
        switch ((GirRt)i.idx) {
            case GirRt::OutInt: L("{ uint8_t buf[GS_FMT_MAX]; int64_t n = gs_fmt_i64(buf, (int64_t)", V(i.a), "); gs_out_bytes(buf, n); }"); break;
            case GirRt::OutUint: L("{ uint8_t buf[GS_FMT_MAX]; int64_t n = gs_fmt_u64(buf, (uint64_t)", V(i.a), "); gs_out_bytes(buf, n); }"); break;
            case GirRt::OutBool: L("{ uint8_t buf[GS_FMT_MAX]; int64_t n = gs_fmt_bool(buf, (int64_t)", V(i.a), "); gs_out_bytes(buf, n); }"); break;
            case GirRt::OutText:
                if (!i.text.empty()) L("gs_out_bytes(", literals.at(i.text), ", ", i.text.size(), ");");
                break;
            case GirRt::OutNl: L("gs_out_bytes((const uint8_t *)\"\\n\", 1);"); break;
            default: break;
        }
    }
};

}  // namespace goose
