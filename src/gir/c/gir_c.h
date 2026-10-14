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
//   output          gs_out_int, gs_out_uint, gs_out_bool, gs_out_bytes, gs_out_nl
//   aborts          gs_abort (GS_E_SLICE, GS_E_ASSERT), gs_abort_msg, gs_idxfail, gs_exit
//   checked ints    gs_add_*, gs_sub_*, gs_mul_*, gs_neg_*, gs_div_*, gs_mod_*, gs_shl_*, gs_shr_*,
//                   GS_RANGE, GS_RANGE_U
inline constexpr const char *GIR_C_RUNTIME_ENTRY_POINTS =
    "gs_rt_init gs_stack_init GS gs_memcpy gs_memmove gs_rt_stats gs_out_int gs_out_uint gs_out_bool "
    "gs_out_bytes gs_out_nl gs_fmt_i64 gs_fmt_u64 gs_fmt_bool gs_abort gs_abort_msg gs_idxfail gs_exit gs_add gs_sub gs_mul gs_neg "
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
        if (!m.lowtargets.empty())
            throw CompileError { "GIR-L target emission requires the complete checked target protocol" };
        Names();
        GirCProgram out;
        for (size_t f = 0; f < m.funcs.size(); f++) out.pieces.push_back(Piece((int)f));
        // The sections, in the conventions the unit assembler splits them by.
        string tdecls = "typedef struct { uint8_t *base; int64_t len; } gir_hdr;\n";
        if (CoreHasConstruction(m.profile))
            Append(tdecls, "typedef char gir_pointer_bytes_check[(sizeof(void *) == ", m.pointerBytes,
                   ") ? 1 : -1];\n");
        for (auto size : blobs) Append(tdecls, "typedef struct { uint64_t w[", (size + 7) / 8, "]; } gir_blob_", size, ";\n");
        string data;
        if (CoreHasConstruction(m.profile)) {
            data += "static GS_TLS int64_t gir_return_flag;\n";
            data += "static GS_TLS gs_stack **gir_stack_cells;\nstatic GS_TLS size_t gir_stack_capacity;\n";
            data += "static gs_stack *gir_stack_at(int64_t base, int64_t offset) { if (base < 0 || offset < 0 || base > INT64_MAX - offset) gs_panic(\"invalid construction stack base\"); int64_t index = base + offset; if ((uint64_t)index >= SIZE_MAX / sizeof(gs_stack *)) gs_panic(\"invalid construction stack index\"); size_t needed = (size_t)index + 1; if (needed > gir_stack_capacity) { size_t capacity = gir_stack_capacity ? gir_stack_capacity : 8; while (capacity < needed) { if (capacity > SIZE_MAX / sizeof(gs_stack *) / 2) gs_panic(\"construction stack directory overflow\"); capacity *= 2; } gs_stack **cells = (gs_stack **)realloc(gir_stack_cells, capacity * sizeof(gs_stack *)); if (!cells) gs_panic(\"out of memory allocating construction stacks\"); memset(cells + gir_stack_capacity, 0, (capacity - gir_stack_capacity) * sizeof(gs_stack *)); gir_stack_cells = cells; gir_stack_capacity = capacity; } if (!gir_stack_cells[index]) { gir_stack_cells[index] = (gs_stack *)malloc(sizeof(gs_stack)); if (!gir_stack_cells[index]) gs_panic(\"out of memory allocating construction stack cell\"); gs_stack_init(gir_stack_cells[index]); } return gir_stack_cells[index]; }\n";
            data += "static void gir_stack_cells_close(void) { for (size_t index = 0; index < gir_stack_capacity; index++) free(gir_stack_cells[index]); free(gir_stack_cells); gir_stack_cells = NULL; gir_stack_capacity = 0; }\n";
            if (constructionTrace) {
                data += "static FILE *gir_trace_file;\nstatic int gir_trace_comma;\nstatic int64_t gir_trace_storage, gir_trace_destination;\n";
                data += "static void gir_trace_fail(void) { perror(\"construction trace\"); _Exit(74); }\n";
                data += "static void gir_source_close(void);\nstatic void gir_trace_close(void) { gir_source_close(); if (fclose(gir_trace_file) != 0) gir_trace_fail(); gir_trace_file = NULL; }\n";
                Append(data, "static void gir_trace_open(void) { gir_trace_file = fopen(", CStr(*constructionTrace),
                       ", \"wb\"); if (!gir_trace_file) gir_trace_fail(); if (atexit(gir_trace_close) != 0) gir_trace_fail(); if (fputs(\"[\\\"construction\\\",[]]\\n\", gir_trace_file) < 0 || fflush(gir_trace_file) != 0) gir_trace_fail(); }\n");
                data += "static void gir_trace_record(const char *kind, const char *reason, size_t n, const int64_t *v) { if (!gir_trace_file) return; if (fseek(gir_trace_file, -3, SEEK_END) != 0) gir_trace_fail(); if (gir_trace_comma && fputc(',', gir_trace_file) == EOF) gir_trace_fail(); gir_trace_comma = 1; if (fprintf(gir_trace_file, \"[\\\"%s\\\"\", kind) < 0) gir_trace_fail(); if (strcmp(kind, \"copy\") == 0) { if (fprintf(gir_trace_file, \",[\\\"%s\\\",%lld\", reason, (long long)v[0]) < 0) gir_trace_fail(); if (strcmp(reason, \"storage\") == 0) { if (fputs(\",[\", gir_trace_file) < 0) gir_trace_fail(); for (size_t k = 1; k + 1 < n; k++) if (fprintf(gir_trace_file, \"%s%lld\", k > 1 ? \",\" : \"\", (long long)v[k]) < 0) gir_trace_fail(); if (fputc(']', gir_trace_file) == EOF) gir_trace_fail(); } if (fprintf(gir_trace_file, \"],%lld\", (long long)v[n - 1]) < 0) gir_trace_fail(); } else { for (size_t k = 0; k < n; k++) if (fprintf(gir_trace_file, \",%lld\", (long long)v[k]) < 0) gir_trace_fail(); if (*reason && fprintf(gir_trace_file, \",\\\"%s\\\"\", reason) < 0) gir_trace_fail(); } if (fputc(']', gir_trace_file) == EOF || fputs(\"]]\\n\", gir_trace_file) < 0 || fflush(gir_trace_file) != 0) gir_trace_fail(); }\n";
                data += R"(
typedef struct gir_source { size_t refs, count; int64_t storage; int64_t path[]; } gir_source;
typedef struct gir_source_slot { uint8_t **value; struct gir_source_slot *next; } gir_source_slot;
typedef struct gir_source_scope { struct gir_source_scope *previous; gir_source_slot *slots; } gir_source_scope;
typedef struct gir_source_call { struct gir_source_call *previous; size_t count; gir_source **arguments, **results; } gir_source_call;
static GS_TLS gir_source_scope *gir_source_scope_top;
static GS_TLS gir_source_call *gir_source_call_top;
static gir_source **gir_global_sources;
static size_t gir_global_sources_count;
static void *gir_source_alloc(size_t size) { void *value = calloc(1, size); if (!value) gs_panic("out of memory recording construction provenance"); return value; }
static void gir_source_retain(gir_source *source) { if (source) { if (source->refs == SIZE_MAX) gir_trace_fail(); source->refs++; } }
static void gir_source_release(gir_source *source) { if (source && --source->refs == 0) free(source); }
static void gir_source_assign(uint8_t **value, gir_source *source) { if (!gir_source_scope_top) gir_trace_fail(); gir_source_slot *slot = gir_source_scope_top->slots; while (slot && slot->value != value) slot = slot->next; if (!slot) { slot = (gir_source_slot *)gir_source_alloc(sizeof(*slot)); slot->value = value; slot->next = gir_source_scope_top->slots; gir_source_scope_top->slots = slot; } gir_source_retain(source); gir_source_release((gir_source *)*value); *value = (uint8_t *)source; }
static gir_source *gir_source_new(int64_t storage, size_t count, const int64_t *path) { if (storage < 0 || count > (SIZE_MAX - sizeof(gir_source)) / sizeof(int64_t)) gir_trace_fail(); gir_source *source = (gir_source *)gir_source_alloc(sizeof(*source) + count * sizeof(int64_t)); source->storage = storage; source->count = count; for (size_t index = 0; path && index < count; index++) { if (path[index] < 0) gir_trace_fail(); source->path[index] = path[index]; } return source; }
static gir_source *gir_source_child(gir_source *parent, int64_t index) { if (!parent || index < 0 || parent->count == SIZE_MAX) gir_trace_fail(); gir_source *source = gir_source_new(parent->storage, parent->count + 1, NULL); if (parent->count) memcpy(source->path, parent->path, parent->count * sizeof(int64_t)); source->path[parent->count] = index; return source; }
static uint8_t *gir_source_enter(void) { gir_source_scope *scope = (gir_source_scope *)gir_source_alloc(sizeof(*scope)); scope->previous = gir_source_scope_top; gir_source_scope_top = scope; return (uint8_t *)scope; }
static void gir_source_leave(uint8_t *token) { gir_source_scope *scope = (gir_source_scope *)token; if (scope != gir_source_scope_top) gir_trace_fail(); while (scope->slots) { gir_source_slot *slot = scope->slots; scope->slots = slot->next; gir_source_release((gir_source *)*slot->value); *slot->value = NULL; free(slot); } gir_source_scope_top = scope->previous; free(scope); }
static uint8_t *gir_source_call_push(size_t count, gir_source *const *arguments) { gir_source_call *call = (gir_source_call *)gir_source_alloc(sizeof(*call)); call->previous = gir_source_call_top; call->count = count; call->arguments = (gir_source **)gir_source_alloc((count + 1) * sizeof(gir_source *)); call->results = (gir_source **)gir_source_alloc((count + 1) * sizeof(gir_source *)); for (size_t position = 1; position <= count; position++) { call->arguments[position] = arguments[position - 1]; gir_source_retain(arguments[position - 1]); } gir_source_call_top = call; return (uint8_t *)call; }
static gir_source *gir_source_param(size_t position) { gir_source_call *call = gir_source_call_top; if (!call || position == 0 || position > call->count || !call->arguments[position]) gir_trace_fail(); return call->arguments[position]; }
static void gir_source_result(size_t position, gir_source *source) { gir_source_call *call = gir_source_call_top; if (!call || position == 0 || position > call->count || !source) gir_trace_fail(); gir_source_retain(source); gir_source_release(call->results[position]); call->results[position] = source; }
static gir_source *gir_source_call_get(uint8_t *token, size_t position) { gir_source_call *call = (gir_source_call *)token; if (call != gir_source_call_top || position == 0 || position > call->count || !call->results[position]) gir_trace_fail(); return call->results[position]; }
static void gir_source_call_pop(uint8_t *token) { gir_source_call *call = (gir_source_call *)token; if (call != gir_source_call_top) gir_trace_fail(); for (size_t position = 1; position <= call->count; position++) { gir_source_release(call->arguments[position]); gir_source_release(call->results[position]); } gir_source_call_top = call->previous; free(call->arguments); free(call->results); free(call); }
static void gir_source_close(void) { if (gir_source_scope_top || gir_source_call_top) gir_trace_fail(); for (size_t position = 0; position < gir_global_sources_count; position++) gir_source_release(gir_global_sources[position]); free(gir_global_sources); }
static void gir_source_global_set(size_t position, gir_source *source) { gir_source_retain(source); gir_source_release(gir_global_sources[position]); gir_global_sources[position] = source; }
static void gir_source_copy(gir_source *source, int64_t destination) { if (!source || source->count > SIZE_MAX - 2) gir_trace_fail(); int64_t *values = (int64_t *)gir_source_alloc((source->count + 2) * sizeof(int64_t)); values[0] = source->storage; for (size_t index = 0; index < source->count; index++) values[index + 1] = source->path[index]; values[source->count + 1] = destination; gir_trace_record("copy", "storage", source->count + 2, values); free(values); }
)";

            }
        }
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
            Append(t, "    gs_rt_init(argc, argv, ", (CoreHasConstruction(m.profile) ? 0 : m.mainstacks), ", ", m.mainstacks + m.globalstacks, ", 0);\n");
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
        u.data = data;
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
    const GirModule &m;
    optional<string> constructionTrace;

    // ---------------------------------------------------------------------
    // Names and types.

    static string Sanitize(const string &s) {
        string out;
        for (auto c : s) out += isalnum((unsigned char)c) ? c : '_';
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
                                               : cat(Sanitize(fn.name), "_g_", fn.key)));
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
            case GirRt::OutInt: L("gs_out_int((int64_t)", V(i.a), ");"); break;
            case GirRt::OutUint: L("gs_out_uint((uint64_t)", V(i.a), ");"); break;
            case GirRt::OutBool: L("gs_out_bool((int64_t)", V(i.a), ");"); break;
            case GirRt::OutText:
                if (!i.text.empty()) L("gs_out_bytes(", literals.at(i.text), ", ", i.text.size(), ");");
                break;
            case GirRt::OutNl: L("gs_out_nl();"); break;
            default: break;
        }
    }
};

}  // namespace goose
