// Goose compiler — code-generation units (--emit-units DIR). The finished C of
// a whole program is divided into translation units that can be compiled
// apart and linked with the runtime object: each unit holds some of the
// program's functions and declares only what they use. Everything here works
// on the text the code generator produced, after sharing and stable naming,
// so what a unit holds is a function of the program's content and not of the
// order things were created in.
//
// What is whole-program, and where it lives:
//   functions            external, hidden; defined once, in the unit of their
//                        class name; small generated helpers are `static` in
//                        each unit that uses them
//   globals              one segment per module, defined in the module's
//                        globals unit with its initialization functions; each
//                        thread reaches a segment through that segment's own
//                        thread-local pointer
//   string/blob literals external constants named by content, defined once in
//                        the literals unit of their digest shard
//   locations            one table per function, in the locations unit of the
//                        function's module; a site passes its entry
//   nonlocal channels    thread-locals, defined in the program unit
//   main, exports, thread entries, runtime start: the program unit
#pragma once

#include <filesystem>

namespace goose {

// The size of C a module's code is spread to by shards: a module has 2^s
// shards, s the smallest value that keeps its largest shard at or under this.
constexpr size_t kUnitTargetBytes = 512 * 1024;
// A generated helper no larger than this is a static function in each unit
// that uses it, which keeps it out of every unit's link interface.
constexpr size_t kStaticHelperBytes = 4096;

inline string UnitName(const string &s) {
    string out;
    for (auto c : s) out += isalnum((unsigned char)c) ? c : '_';
    return out;
}

inline string CodeGen::SegmentId(const string &module) {
    return cat(UnitName(module), "_", Sha256::Of(module).Hex(4));
}

inline string CodeGen::GlobalModule(VarDef *d) {
    if (globalmods.empty())
        for (auto g : ast.globals)
            for (auto dd : g->defs) globalmods[dd] = Keys().ModuleOf(g->line.fileidx);
    return globalmods[d];
}

inline vector<string> CodeGen::SegmentModules() {
    set<string> modules;
    for (auto g : ast.globals)
        for (auto d : g->defs)
            if (gnames[d].find("GS_GL->") != string::npos) modules.insert(GlobalModule(d));
    return vector<string>(modules.begin(), modules.end());
}

// The runtime header of a program written as units: runtime.h and the unit
// additions. The thread-local state runtime.h keeps as C statics of the
// including file (the data stacks) must be one object for the whole
// program, so it is declared extern here and defined in the program unit.
inline string UnitRuntimeHeader(string runtime_h, string_view additions) {
    for (auto [from, to] : { pair<const char *, const char *>
             { "static GS_TLS gs_stack *gs_stks;", "extern GS_TLS gs_stack *gs_stks;" },
             { "static GS_TLS int64_t gs_nstks;", "extern GS_TLS int64_t gs_nstks;" },
             { "static GS_TLS void *gs_gl;", "extern GS_TLS void *gs_gl;" } }) {
        auto at = runtime_h.find(from);
        if (at == string::npos)
            throw CompileError { cat("unit mode: the runtime no longer declares `", from, "`") };
        runtime_h.replace(at, strlen(from), to);
    }
    return cat("#ifndef GOOSE_RUNTIME_H\n#define GOOSE_RUNTIME_H\n", runtime_h, additions);
}

struct UnitInputs {
    string runtime_header;     // runtime.h and the unit additions, as one header.
    string ext_text;           // runtime_ext.h.
    string defines;            // The -D lines.
    string runtime_version;
};

// One piece of text with the names it defines and the types it needs.
struct UnitTypeChunk {
    string text;
    string name;                     // What it defines, or "" for an enum.
    bool forward = false, body = false;
    vector<string> enumerators;
    vector<string> byvalue, bypointer;
};

struct UnitChunk {
    string name, text, head;
    long long locrefbytes = 0;       // The table entries its checks pass.
    enum Kind { Spec, Helper, Init, Program } kind = Spec;
    string module;
    bool isstatic = false;           // A helper small enough to copy.
    FnSpec *rep = nullptr;
    string unit;                     // The unit file that defines it; for a static helper, empty.
    int tablesize = 0;
    set<string> segbodies;           // Modules whose segment's fields it names.
};

struct UnitEntity {
    enum Kind { Type, Enum, Func, StaticFn, Literal, Channel, Queue, StaticConst, Table, SegPtr,
                SegFwd, SegBody, SegMain, ExternFn, ProgStatic } kind = Func;
    string name;
    string decl;                     // Its declaration in a unit that does not define it.
    string def;                      // Its definition, where it has no chunk.
    string home;                     // The unit that defines it.
    int chunk = -1;                  // For functions.
    vector<string> roots;            // The names its declaration needs.
};

struct UnitBuild {
    string file, module;
    enum Kind { Code, Globals, Locations, Literals, Program } kind = Code;
    vector<int> chunks;
    vector<string> defs;             // Definitions of entities, in symbol order.
    set<string> roots;
    long long bytes = 0;
    string text;
    UnitStats::Breakdown parts;
};

// The smallest s for which no shard of the symbols holds more than the target.
// A function larger than the target cannot be divided and shares a shard by
// chance, so where the module has one the limit is twice the largest function
// instead; otherwise the module would be spread over thousands of units to
// separate it from its neighbours.
inline int UnitShardBits(const vector<pair<string, size_t>> &symbols) {
    size_t largest = 0;
    for (auto &[name, bytes] : symbols) largest = max(largest, bytes);
    auto limit = max(kUnitTargetBytes, 2 * largest);
    for (int s = 0; s < 16; s++) {
        map<unsigned, pair<size_t, int>> per;
        for (auto &[name, bytes] : symbols) {
            auto d = Sha256::Of(name);
            unsigned shard = s ? (((unsigned)d.b[0] << 8 | d.b[1]) >> (16 - s)) : 0;
            per[shard].first += bytes;
            per[shard].second++;
        }
        auto ok = true;
        for (auto &[shard, p] : per) ok = ok && (p.first <= limit || p.second == 1);
        if (ok) return s;
    }
    return 15;
}

inline unsigned UnitShard(const string &symbol, int bits) {
    auto d = Sha256::Of(symbol);
    return bits ? (((unsigned)d.b[0] << 8 | d.b[1]) >> (16 - bits)) : 0;
}

inline string UnitHex(unsigned v, int bits) {
    char buf[16];
    snprintf(buf, sizeof buf, "%0*x", (bits + 3) / 4, v);
    return buf;
}

// The first line of a piece of code that is not a preprocessor line.
inline string_view UnitDefinitionLine(string_view piece) {
    for (size_t a = 0; a < piece.size();) {
        auto e = piece.find('\n', a);
        if (e == string_view::npos) e = piece.size();
        auto line = piece.substr(a, e - a);
        if (!line.empty() && line[0] != '#') return line;
        a = e + 1;
    }
    return {};
}

// The functions of the code section: each runs to the line that is a lone
// closing brace, which no nested block's brace is (those are indented). A
// group of simd versions and the function that dispatches among them are
// one piece.
inline vector<string> UnitSplitFunctions(const string &code) {
    vector<string> raws;
    size_t a = 0;
    while (a < code.size()) {
        auto e = code.find("\n}\n", a);
        auto end = e == string::npos ? code.size() : e + 3;
        raws.push_back(code.substr(a, end - a));
        a = end;
    }
    vector<string> out;
    for (size_t i = 0; i < raws.size(); i++) {
        string piece = raws[i];
        auto version = [](const string &r) {
            return UnitDefinitionLine(r).compare(0, 14, "GS_SIMD_TARGET") == 0;
        };
        for (auto v = version(raws[i]); v && i + 1 < raws.size(); v = version(raws[i]))
            piece += raws[++i];
        // Whitespace between functions is not part of either.
        auto first = piece.find_first_not_of(" \n");
        if (first == string::npos) continue;
        out.push_back(piece.substr(first));
    }
    return out;
}


// The identifier before the first parenthesis of a definition's line.
inline string UnitFunctionName(string_view line) {
    auto paren = line.find('(');
    if (paren == string_view::npos) return {};
    auto e = paren;
    auto b = e;
    while (b > 0 && (isalnum((unsigned char)line[b - 1]) || line[b - 1] == '_')) b--;
    return string(line.substr(b, e - b));
}

// Where the line that defines `name` begins: the last such line of a group
// of simd versions, which ends with the function that dispatches among them.
inline size_t UnitDefinitionAt(const string &text, const string &name) {
    size_t at = 0, found = string::npos;
    while (at < text.size()) {
        auto e = text.find('\n', at);
        if (e == string::npos) e = text.size();
        auto line = string_view(text).substr(at, e - at);
        if (!line.empty() && line[0] != '#' && UnitFunctionName(line) == name &&
            line.compare(0, 6, "static") == 0)
            found = at;
        else if (!line.empty() && line[0] != '#' && UnitFunctionName(line) == name && found == string::npos)
            found = at;
        at = e + 1;
    }
    return found;
}

// A definition's text up to its opening brace.
inline string UnitHead(const string &text, const string &name) {
    auto found = UnitDefinitionAt(text, name);
    if (found == string::npos) return {};
    auto brace = text.find(" {\n", found);
    return text.substr(found, brace - found);
}

inline string UnitReplace(string s, string_view from, string_view to) {
    for (auto at = s.find(from); at != string::npos; at = s.find(from, at + to.size()))
        s.replace(at, from.size(), to);
    return s;
}

// The tokens of a text that name something, in order, skipping fields.
template<typename F> void UnitTokens(string_view text, F &&f) {
    ScanC(text, [&](bool ident, string_view tok, bool member) {
        if (ident && !member) f(tok);
    });
}

inline void WriteUnits(CodeGen &cg, const string &dir, const UnitInputs &in) {
    auto &keys = cg.Keys();
    // The specialization behind each emitted function name, where sharing did
    // not say (a function it left out of its classes).
    for (auto &[sp, si] : cg.sinfo) cg.classrep.emplace(si.cname, sp);
    for (auto &[sp, name] : cg.ernames) if (!name.empty()) cg.classrep.emplace(name, sp);
    // ---- Segments of the globals. ----
    auto modules = cg.SegmentModules();
    unordered_map<string, string> memberseg;           // Member name -> module.
    unordered_map<string, string> staticmod;           // Static constant -> module.
    for (auto g : cg.ast.globals)
        for (auto d : g->defs) {
            auto module = cg.GlobalModule(d);
            vector<string> texts = { cg.gnames[d] };
            if (cg.gstks.count(d)) texts.push_back(cg.gstks[d]);
            if (cg.gpools.count(d)) { texts.push_back(cg.gpools[d].first); texts.push_back(cg.gpools[d].second); }
            for (auto &t : texts)
                for (auto at = t.find("GS_GL->"); at != string::npos; at = t.find("GS_GL->", at + 7)) {
                    auto b = at + 7, e = b;
                    while (e < t.size() && (isalnum((unsigned char)t[e]) || t[e] == '_')) e++;
                    memberseg[t.substr(b, e - b)] = module;
                }
            UnitTokens(cg.gnames[d], [&](string_view tok) { staticmod.emplace(string(tok), module); });
        }
    map<string, vector<string>> segmembers;            // Module -> member declaration lines.
    for (size_t a = 0; a < cg.gblock.size();) {
        auto e = cg.gblock.find('\n', a);
        auto line = cg.gblock.substr(a, e - a);
        a = e + 1;
        if (line.empty()) continue;
        auto semi = line.rfind(';');
        auto b = semi;
        while (b > 0 && (isalnum((unsigned char)line[b - 1]) || line[b - 1] == '_')) b--;
        auto member = line.substr(b, semi - b);
        auto it = memberseg.find(member);
        if (it == memberseg.end()) cg.Fail(Line {}, cat("unit mode: global member ", member, " has no module"));
        segmembers[it->second].push_back(line);
    }

    // ---- Entities. ----
    vector<UnitEntity> ents;
    unordered_map<string, int> entof;
    auto add = [&](UnitEntity e) {
        if (entof.count(e.name)) cg.Fail(Line {}, cat("unit mode: two entities named ", e.name));
        entof[e.name] = (int)ents.size();
        ents.push_back(std::move(e));
        return (int)ents.size() - 1;
    };

    // Types.
    vector<UnitTypeChunk> tchunks;
    {
        auto &t = cg.tdecls;
        size_t i = 0;
        while (i < t.size()) {
            while (i < t.size() && isspace((unsigned char)t[i])) i++;
            if (i >= t.size()) break;
            auto start = i;
            int depth = 0;
            while (i < t.size() && !(t[i] == ';' && depth == 0)) {
                depth += t[i] == '{';
                depth -= t[i] == '}';
                i++;
            }
            i++;
            UnitTypeChunk c;
            c.text = t.substr(start, i - start);
            auto &x = c.text;
            auto lastident = [&]() {
                auto e = x.size() - 1;
                while (e > 0 && !(isalnum((unsigned char)x[e - 1]) || x[e - 1] == '_')) e--;
                auto b = e;
                while (b > 0 && (isalnum((unsigned char)x[b - 1]) || x[b - 1] == '_')) b--;
                return x.substr(b, e - b);
            };
            if (x.compare(0, 8, "typedef ") == 0 && x.find('{') == string::npos) {
                c.name = lastident();
                c.forward = true;
            } else if (x.compare(0, 8, "typedef ") == 0) {
                c.name = lastident();
                c.body = true;
            } else if (x.compare(0, 7, "struct ") == 0) {
                auto e = x.find(' ', 7);
                c.name = x.substr(7, e - 7);
                c.body = true;
            } else if (x.compare(0, 4, "enum") == 0) {
                auto b = x.find('{') + 1, e = x.rfind('}');
                for (auto p = b; p < e;) {
                    auto eq = x.find('=', p), comma = x.find(',', p);
                    if (eq == string::npos || eq > e) break;
                    auto id = x.substr(p, eq - p);
                    id.erase(0, id.find_first_not_of(" \n"));
                    id.erase(id.find_last_not_of(" \n") + 1);
                    c.enumerators.push_back(id);
                    if (comma == string::npos) break;
                    p = comma + 1;
                }
            } else {
                cg.Fail(Line {}, cat("unit mode: unrecognized type declaration: ", x.substr(0, 40)));
            }
            tchunks.push_back(std::move(c));
        }
    }
    unordered_map<string, vector<int>> typeof_;        // Type name -> its chunks.
    unordered_map<string, int> enumof;
    for (size_t i = 0; i < tchunks.size(); i++) {
        if (!tchunks[i].name.empty()) typeof_[tchunks[i].name].push_back((int)i);
        for (auto &e : tchunks[i].enumerators) enumof[e] = (int)i;
    }
    for (auto &c : tchunks) {
        if (!c.body) continue;
        // A reference is by value unless a `*` follows it.
        size_t pos = 0;
        auto &x = c.text;
        while (pos < x.size()) {
            if (!(isalpha((unsigned char)x[pos]) || x[pos] == '_')) { pos++; continue; }
            auto e = pos;
            while (e < x.size() && (isalnum((unsigned char)x[e]) || x[e] == '_')) e++;
            auto id = x.substr(pos, e - pos);
            auto m = pos > 0 && (x[pos - 1] == '.' || (pos > 1 && x[pos - 1] == '>' && x[pos - 2] == '-'));
            if (!m && typeof_.count(id) && id != c.name) {
                auto k = e;
                while (k < x.size() && x[k] == ' ') k++;
                // A pointer to a type with no forward declaration needs the
                // type declared first all the same.
                auto fwd = false;
                for (auto ti : typeof_[id]) fwd = fwd || tchunks[ti].forward;
                (k < x.size() && x[k] == '*' && fwd ? c.bypointer : c.byvalue).push_back(id);
            }
            pos = e;
        }
    }

    // Segment layouts, one per module.
    for (auto &module : modules) {
        auto seg = cg.SegName(module);
        // The type's name is declared without its fields, so a unit that only
        // names the segment does not see them.
        UnitEntity fwd;
        fwd.kind = UnitEntity::SegFwd;
        fwd.name = seg + "_t";
        fwd.decl = cat("typedef struct ", seg, "_s ", seg, "_t;");
        add(fwd);
        UnitEntity body;
        body.kind = UnitEntity::SegBody;
        body.name = seg + "_s";
        body.decl = cat("struct ", seg, "_s {\n");
        for (auto &line : segmembers[module]) body.decl += line + "\n";
        body.decl += "};\n";
        add(body);
        UnitEntity ptr;
        ptr.kind = UnitEntity::SegPtr;
        ptr.name = seg;
        ptr.decl = cat("extern GS_TLS ", seg, "_t *", seg, ";");
        ptr.def = cat("GS_TLS ", seg, "_t *", seg, ";\n");
        add(ptr);
        UnitEntity mainseg;
        mainseg.kind = UnitEntity::SegMain;
        mainseg.name = seg + "_main";
        mainseg.decl = cat("extern ", seg, "_t ", seg, "_main;");
        mainseg.def = cat(seg, "_t ", seg, "_main;\n");
        add(mainseg);
    }

    // Data: nonlocal channels, queues, constant globals, the files of the
    // diagnostic locations.
    map<string, string> filestrings;                   // File name symbol -> its literal.
    map<string, string> staticconstdefs;               // Name -> definition.
    {
        for (size_t a = 0; a < cg.data.size();) {
            auto e = cg.data.find('\n', a);
            auto line = cg.data.substr(a, e - a);
            a = e + 1;
            if (line.compare(0, 14, "static GS_TLS ") == 0) {
                auto name = line.substr(line.rfind(' ') + 1);
                name.pop_back();
                name.erase(0, name.find_first_not_of('*'));
                UnitEntity ch;
                ch.kind = UnitEntity::Channel;
                ch.name = name;
                ch.decl = "extern " + line.substr(7);
                ch.def = line.substr(7) + "\n";
                add(ch);
            } else if (line.compare(0, 16, "static gs_queue ") == 0) {
                auto name = line.substr(16, line.find(' ', 16) - 16);
                UnitEntity q;
                q.kind = UnitEntity::Queue;
                q.name = name;
                q.decl = cat("extern gs_queue ", name, ";");
                q.def = line.substr(7) + "\n";
                add(q);
            } else if (line.compare(0, 18, "static const char ") == 0 && line.find("gs_file_") == 18) {
                auto name = line.substr(18, line.find('[') - 18);
                filestrings[name] = line;
            } else if (line.compare(0, 13, "static const ") == 0) {
                auto eq = line.find(" = ");
                auto name = line.substr(line.rfind(' ', eq - 1) + 1, eq - line.rfind(' ', eq - 1) - 1);
                UnitEntity sc;
                sc.kind = UnitEntity::StaticConst;
                sc.name = name;
                sc.decl = "extern " + line.substr(7, eq - 7) + ";";
                sc.def = line.substr(7) + "\n";
                auto it = staticmod.find(name);
                if (it == staticmod.end()) cg.Fail(Line {}, cat("unit mode: constant ", name, " has no module"));
                sc.home = it->second;
                add(sc);
            } else if (line == "static int gs_program_initialized;") {
                UnitEntity ps;
                ps.kind = UnitEntity::ProgStatic;
                ps.name = "gs_program_initialized";
                ps.def = line + "\n";
                add(ps);
            } else if (line.empty() || line == "typedef struct {" || line.compare(0, 4, "    ") == 0 ||
                       line.compare(0, 14, "} gs_globals_t") == 0 ||
                       line.compare(0, 24, "static gs_globals_t gs_g") == 0 ||
                       line.compare(0, 15, "#define GS_GL (") == 0 ||
                       line.compare(0, 15, "#define GS_GL ((") == 0) {
                continue;
            } else {
                cg.Fail(Line {}, cat("unit mode: unrecognized data declaration: ", line.substr(0, 60)));
            }
        }
    }

    // Literals.
    struct Lit { string name, decl, def; };
    vector<Lit> lits;
    for (size_t a = 0; a < cg.pdata.size();) {
        auto start = a;
        for (;;) {
            auto e = cg.pdata.find('\n', a);
            auto lineend = e == string::npos ? cg.pdata.size() : e;
            auto last = lineend > a ? cg.pdata[lineend - 1] : ' ';
            a = e == string::npos ? cg.pdata.size() : e + 1;
            if (last == ';' || a >= cg.pdata.size()) break;
        }
        auto stmt = cg.pdata.substr(start, a - start);
        if (stmt.find_first_not_of(" \n") == string::npos) continue;
        auto eq = stmt.find(" = ");
        auto b = stmt.rfind(' ', eq - 1);
        Lit l;
        auto head = stmt.substr(0, eq);
        auto bracket = head.find('[', head.rfind(' '));
        l.name = bracket != string::npos && head.rfind(' ') < bracket
                     ? head.substr(head.rfind(' ') + 1, bracket - head.rfind(' ') - 1)
                     : stmt.substr(b + 1, eq - b - 1);
        l.decl = "extern " + head.substr(7) + ";";
        l.def = stmt.substr(7);
        lits.push_back(std::move(l));
    }
    for (auto &l : lits) {
        UnitEntity e;
        e.kind = UnitEntity::Literal;
        e.name = l.name;
        e.decl = l.decl;
        e.def = l.def;
        add(e);
    }

    // Extern functions of the program's C side, added once the program's own
    // functions are known: an export's name may also be declared extern.
    vector<UnitEntity> externfns;
    for (size_t a = 0; a < cg.externtext.size();) {
        auto e = cg.externtext.find('\n', a);
        auto line = cg.externtext.substr(a, e - a);
        a = e + 1;
        if (line.empty()) continue;
        UnitEntity ex;
        ex.kind = UnitEntity::ExternFn;
        ex.name = UnitFunctionName(line);
        ex.decl = line;
        externfns.push_back(ex);
    }

    // Functions.
    vector<UnitChunk> chunks;
    {
        unordered_set<string> exports;
        for (auto sf : cg.ast.functions)
            if (sf->isexport) exports.insert(sf->cname);
        unordered_map<string, string> initmod;
        for (auto &[module, fn] : cg.unitinits) initmod[fn] = module;
        for (auto &text : UnitSplitFunctions(cg.code)) {
            UnitChunk c;
            c.text = text;
            c.name = UnitFunctionName(UnitDefinitionLine(text).substr(0, UnitDefinitionLine(text).size()));
            // A group's name is its dispatcher's.
            if (text.compare(0, 4, "#if ") == 0 || UnitDefinitionLine(text).compare(0, 14, "GS_SIMD_TARGET") == 0) {
                size_t at = text.rfind("\nstatic ");
                auto e = text.find('\n', at + 1);
                c.name = UnitFunctionName(string_view(text).substr(at + 1, e - at - 1));
            }
            auto &n = c.name;
            if (initmod.count(n)) { c.kind = UnitChunk::Init; c.module = initmod[n]; }
            else if (n == "gs_program_init" || n == "goose_init" || n == "main" ||
                     n.compare(0, 9, "gs_tmain_") == 0 || exports.count(n))
                { c.kind = UnitChunk::Program; c.module = "~program"; }
            else if (n.compare(0, 8, "gs_size_") == 0 || n.compare(0, 10, "gs_verify_") == 0 ||
                     n.compare(0, 6, "gs_eq_") == 0 || n.compare(0, 10, "gs_render_") == 0) {
                c.kind = UnitChunk::Helper;
                c.module = "~helpers";
            } else {
                auto it = cg.classrep.find(n);
                if (it == cg.classrep.end()) cg.Fail(Line {}, cat("unit mode: unplaced function ", n));
                c.kind = UnitChunk::Spec;
                c.rep = it->second;
                c.module = keys.ModuleOf(c.rep->sf->line.fileidx);
            }
            c.isstatic = c.kind == UnitChunk::Helper && c.text.size() <= kStaticHelperBytes;
            chunks.push_back(std::move(c));
        }
    }

    // Locations and segment accesses: each function's text is rewritten so
    // that a check passes its table entry, and a global is reached through
    // its module's segment pointer.
    struct Table { vector<pair<string, int>> entries; };
    vector<Table> tables(chunks.size());
    for (size_t ci = 0; ci < chunks.size(); ci++) {
        auto &c = chunks[ci];
        auto &table = tables[ci];
        map<pair<string, int>, int> index;
        string out;
        enum { None, GL1, GL2, File, Cond1, Cond2 } st = None;
        string file, condvar;
        auto tableref = [&](const string &f, int line) {
            auto key = make_pair(f, line);
            auto it = index.find(key);
            if (it == index.end()) {
                it = index.emplace(key, (int)table.entries.size()).first;
                table.entries.push_back(key);
            }
            auto ref = cat("gs_loc_", c.name, "[", it->second, "].f, gs_loc_", c.name, "[", it->second, "].l");
            c.locrefbytes += (long long)ref.size();
            return ref;
        };
        ScanC(c.text, [&](bool ident, string_view tok, bool member) {
            if (st == GL1) {
                if (!ident && tok == "->") { st = GL2; return; }
                out += "GS_GL";
                st = None;
            } else if (st == GL2) {
                if (!ident) cg.Fail(Line {}, cat("unit mode: a global is not named in ", c.name));
                auto it = memberseg.find(string(tok));
                if (it == memberseg.end()) cg.Fail(Line {}, cat("unit mode: global member ", tok, " has no module"));
                c.segbodies.insert(it->second);
                out += cg.SegName(it->second) + "->" + string(tok);
                st = None;
                return;
            } else if (st == Cond1) {
                if (!ident) cg.Fail(Line {}, cat("unit mode: a conditional location is not a variable in ", c.name));
                condvar = string(tok);
                st = Cond2;
                return;
            } else if (st == Cond2) {
                // `) ? N : M`: a check whose line depends on a condition.
                size_t p = 0;
                auto expect = [&](string_view s) {
                    if (tok.compare(p, s.size(), s) != 0)
                        cg.Fail(Line {}, cat("unit mode: unsupported conditional location in ", c.name));
                    p += s.size();
                };
                auto number = [&]() {
                    auto b = p;
                    while (p < tok.size() && isdigit((unsigned char)tok[p])) p++;
                    if (b == p) cg.Fail(Line {}, cat("unit mode: unsupported conditional location in ", c.name));
                    return atoi(string(tok.substr(b, p - b)).c_str());
                };
                if (ident) cg.Fail(Line {}, cat("unit mode: unsupported conditional location in ", c.name));
                expect(") ? ");
                auto m = number();
                expect(" : ");
                auto n = number();
                auto one = tableref(file, m), two = tableref(file, n);
                // The two entries share a file; the condition picks the line.
                auto row = [&](const string &ref) { return ref.substr(ref.find(", ") + 2); };
                out += one.substr(0, one.find(", ")) + cat(", (", condvar, ") ? ", row(one), " : ", row(two));
                out.append(tok.data() + p, tok.size() - p);
                st = None;
                return;
            } else if (st == File) {
                if (!ident && tok == ", (") { st = Cond1; return; }
                if (ident || tok.compare(0, 2, ", ") != 0)
                    cg.Fail(Line {}, cat("unit mode: a location is not a file and a line in ", c.name));
                size_t d = 2, e = 2;
                while (e < tok.size() && isdigit((unsigned char)tok[e])) e++;
                if (e == d) cg.Fail(Line {}, cat("unit mode: a location has no line in ", c.name));
                out += tableref(file, atoi(string(tok.substr(d, e - d)).c_str()));
                out.append(tok.data() + e, tok.size() - e);
                st = None;
                return;
            }
            if (ident && !member && tok == "GS_GL") { st = GL1; return; }
            if (ident && !member && tok.compare(0, 8, "gs_file_") == 0) {
                st = File;
                file = string(tok);
                return;
            }
            out.append(tok.data(), tok.size());
        });
        if (st != None) cg.Fail(Line {}, cat("unit mode: unfinished rewrite in ", c.name));
        c.text = std::move(out);
        c.head = UnitHead(c.text, c.name);
        if (c.head.empty()) cg.Fail(Line {}, cat("unit mode: no definition line for ", c.name));
        c.tablesize = (int)table.entries.size();
    }

    // Function entities and their declarations.
    for (size_t ci = 0; ci < chunks.size(); ci++) {
        auto &c = chunks[ci];
        UnitEntity e;
        e.name = c.name;
        e.chunk = (int)ci;
        e.kind = c.isstatic ? UnitEntity::StaticFn : UnitEntity::Func;
        if (c.isstatic) e.decl = c.head + ";";
        else {
            // External with hidden visibility; an always-inline request cannot
            // cross units.
            auto head = c.head;
            if (c.kind != UnitChunk::Program || c.name.compare(0, 9, "gs_tmain_") == 0) {
                head = UnitReplace(head, "GS_INLINE ", "");
                if (head.compare(0, 7, "static ") == 0) head.replace(0, 7, "GS_HIDDEN ");
            }
            e.decl = head + ";";
        }
        add(e);
        if (c.tablesize) {
            UnitEntity t;
            t.kind = UnitEntity::Table;
            t.name = "gs_loc_" + c.name;
            t.decl = cat("extern const gs_loc_t ", t.name, "[", c.tablesize, "];");
            add(t);
        }
    }

    for (auto &ex : externfns)
        if (!entof.count(ex.name)) add(ex);

    // ---- Units. ----
    map<string, UnitBuild> units;
    auto unit = [&](const string &file, UnitBuild::Kind kind, const string &module) -> UnitBuild & {
        auto &u = units[file];
        u.file = file;
        u.kind = kind;
        u.module = module;
        return u;
    };
    auto stem = [&](const string &module) { return cat(UnitName(module), "_", Sha256::Of(module).Hex(4)); };

    // Code units: a module's functions, sharded.
    map<string, vector<int>> bymodule;
    for (size_t ci = 0; ci < chunks.size(); ci++) {
        auto &c = chunks[ci];
        if (c.kind == UnitChunk::Spec || c.kind == UnitChunk::Helper) {
            if (c.isstatic) continue;
            bymodule[c.module].push_back((int)ci);
        }
    }
    for (auto &[module, list] : bymodule) {
        vector<pair<string, size_t>> symbols;
        for (auto ci : list) symbols.push_back({ chunks[ci].name, chunks[ci].text.size() });
        auto bits = UnitShardBits(symbols);
        for (auto ci : list) {
            auto shard = UnitShard(chunks[ci].name, bits);
            auto file = cat(stem(module), bits ? "_" + UnitHex(shard, bits) : string(), ".c");
            auto &u = unit(file, UnitBuild::Code, module);
            u.chunks.push_back(ci);
            chunks[ci].unit = file;
        }
    }
    // Globals units, with the module's initialization functions.
    for (auto &module : modules) {
        auto file = stem(module) + ".globals.c";
        auto &u = unit(file, UnitBuild::Globals, module);
        auto seg = cg.SegName(module);
        u.roots.insert(seg + "_t");
        u.roots.insert(seg + "_s");
        u.defs.push_back(ents[entof[seg]].def);
        u.defs.push_back(ents[entof[seg + "_main"]].def);
        ents[entof[seg]].home = file;
        ents[entof[seg + "_main"]].home = file;
        ents[entof[seg + "_t"]].home = file;
    }
    for (auto &e : ents)
        if (e.kind == UnitEntity::StaticConst) {
            auto file = stem(e.home) + ".globals.c";
            auto &u = unit(file, UnitBuild::Globals, e.home);
            u.defs.push_back(e.def);
            e.home = file;
        }
    for (size_t ci = 0; ci < chunks.size(); ci++)
        if (chunks[ci].kind == UnitChunk::Init) {
            auto file = stem(chunks[ci].module) + ".globals.c";
            unit(file, UnitBuild::Globals, chunks[ci].module).chunks.push_back((int)ci);
            chunks[ci].unit = file;
        }
    // The program unit.
    {
        auto &u = unit("program.c", UnitBuild::Program, "~program");
        // The thread-local state runtime.h would otherwise keep per unit.
        u.defs.push_back("GS_TLS gs_stack *gs_stks;\nGS_TLS int64_t gs_nstks;\nGS_TLS void *gs_gl;\n");
        for (size_t ci = 0; ci < chunks.size(); ci++)
            if (chunks[ci].kind == UnitChunk::Program) { u.chunks.push_back((int)ci); chunks[ci].unit = "program.c"; }
        for (auto &e : ents)
            if (e.kind == UnitEntity::Channel || e.kind == UnitEntity::Queue ||
                e.kind == UnitEntity::ProgStatic) {
                u.defs.push_back(e.def);
                e.home = "program.c";
            }
    }
    // Literals units: by digest shard.
    {
        vector<pair<string, size_t>> symbols;
        for (auto &l : lits) symbols.push_back({ l.name, l.def.size() });
        auto bits = UnitShardBits(symbols);
        for (auto &l : lits) {
            auto file = cat("literals", bits ? "_" + UnitHex(UnitShard(l.name, bits), bits) : string(), ".c");
            auto &u = unit(file, UnitBuild::Literals, "~literals");
            u.defs.push_back(l.def);
            ents[entof[l.name]].home = file;
        }
    }
    // Locations units: each module's tables.
    map<string, vector<int>> locmodules;
    for (size_t ci = 0; ci < chunks.size(); ci++)
        if (chunks[ci].tablesize) locmodules[chunks[ci].module].push_back((int)ci);
    for (auto &[module, list] : locmodules) {
        auto file = stem(module) + ".loc.c";
        auto &u = unit(file, UnitBuild::Locations, module);
        set<string> filesused;
        for (auto ci : list)
            for (auto &[f, line] : tables[ci].entries) filesused.insert(f);
        for (auto &f : filesused) {
            auto it = filestrings.find(f);
            if (it == filestrings.end()) cg.Fail(Line {}, cat("unit mode: unknown file ", f));
            u.defs.push_back(it->second + "\n");
        }
        for (auto ci : list) {
            string t = cat("const gs_loc_t gs_loc_", chunks[ci].name, "[", chunks[ci].tablesize, "] = {\n");
            for (auto &[f, line] : tables[ci].entries) t += cat("    { ", f, ", ", line, " },\n");
            t += "};\n";
            u.defs.push_back(t);
        }
    }
    // Where each function entity is defined.
    for (auto &e : ents)
        if ((e.kind == UnitEntity::Func || e.kind == UnitEntity::StaticFn) && !chunks[e.chunk].isstatic)
            e.home = chunks[e.chunk].unit;
    for (size_t ci = 0; ci < chunks.size(); ci++)
        if (chunks[ci].tablesize) ents[entof["gs_loc_" + chunks[ci].name]].home = stem(chunks[ci].module) + ".loc.c";

    // The core types and the runtime's extern support, written against them,
    // are the same in every unit, so they live once in the runtime header.
    set<string> providednames = { "gs_rhdr", "gs_rref", "gs_pref", "sl_u8" };
    string runtime_header = in.runtime_header + "\n#pragma pack(push, 1)\n";
    for (auto &c : tchunks)
        if (providednames.count(c.name)) runtime_header += c.text + "\n";
    runtime_header += "#pragma pack(pop)\n" + in.ext_text + "\n#endif\n";

    // ---- The text of each unit. ----
    for (auto &[file, u] : units) {
        // What the unit's definitions use, through the static helpers they
        // copy.
        set<string> typeset, statics;
        set<int> used;
        vector<string> work;
        auto scan = [&](string_view text) {
            UnitTokens(text, [&](string_view tok) {
                auto it = entof.find(string(tok));
                if (it != entof.end() && used.insert(it->second).second) work.push_back(string(tok));
                if (typeof_.count(string(tok)) || enumof.count(string(tok))) typeset.insert(string(tok));
            });
        };
        for (auto ci : u.chunks) {
            scan(chunks[ci].text);
            for (auto &m : chunks[ci].segbodies) scan(cg.SegName(m) + "_s");
        }
        for (auto &d : u.defs) scan(d);
        for (auto &r : u.roots) scan(r);
        while (!work.empty()) {
            auto name = work.back();
            work.pop_back();
            auto &e = ents[entof[name]];
            if (e.kind == UnitEntity::StaticFn) { statics.insert(name); scan(chunks[e.chunk].text); }
            if (e.kind == UnitEntity::SegPtr || e.kind == UnitEntity::SegMain) {
                auto fwd = e.name.substr(0, e.kind == UnitEntity::SegMain ? e.name.size() - 5 : e.name.size()) + "_t";
                scan(fwd);
            }
            if (e.kind == UnitEntity::SegBody) scan(e.decl);
            if (e.kind == UnitEntity::Literal || e.kind == UnitEntity::Channel ||
                e.kind == UnitEntity::StaticConst)
                scan(e.decl);
        }
        // Type declarations: those the code names, and what their bodies need.
        set<int> need, needfwd;
        function<void(const string &)> want = [&](const string &name) {
            // What the runtime header declares for every unit.
            if (providednames.count(name)) return;
            auto en = enumof.find(name);
            if (en != enumof.end()) { need.insert(en->second); return; }
            for (auto ci : typeof_[name]) {
                auto &c = tchunks[ci];
                if (c.forward) { needfwd.insert(ci); continue; }
                if (!need.insert(ci).second) continue;
                for (auto &v : c.byvalue) want(v);
                // Code that reaches through a pointer in this body may use
                // the pointee, whose name it does not spell.
                for (auto &p : c.bypointer) want(p);
            }
            for (auto ci : typeof_[name]) if (tchunks[ci].forward) needfwd.insert(ci);
        };
        for (auto &t : typeset) want(t);
        // Order: forward declarations by name; then bodies, dependencies
        // first and otherwise by name.
        string types = "#pragma pack(push, 1)\n";
        vector<int> fwds(needfwd.begin(), needfwd.end());
        sort(fwds.begin(), fwds.end(), [&](int a, int b) { return tchunks[a].name < tchunks[b].name; });
        for (auto ci : fwds) types += tchunks[ci].text + "\n";
        types += "\n";
        vector<int> pending(need.begin(), need.end());
        sort(pending.begin(), pending.end(), [&](int a, int b) {
            auto &x = tchunks[a], &y = tchunks[b];
            return make_tuple(x.name.empty() ? x.enumerators[0] : x.name, a) <
                   make_tuple(y.name.empty() ? y.enumerators[0] : y.name, b);
        });
        set<int> done;
        while (!pending.empty()) {
            auto pick = pending.end();
            for (auto it = pending.begin(); it != pending.end(); ++it) {
                auto ready = true;
                for (auto &v : tchunks[*it].byvalue)
                    for (auto vi : typeof_[v])
                        if (!tchunks[vi].forward && vi != *it && need.count(vi) && !done.count(vi)) ready = false;
                if (ready) { pick = it; break; }
            }
            if (pick == pending.end()) cg.Fail(Line {}, "unit mode: a type depends on itself by value");
            types += tchunks[*pick].text + "\n\n";
            done.insert(*pick);
            pending.erase(pick);
        }
        types += "#pragma pack(pop)\n";

        // Declarations of what the unit uses and does not define.
        map<string, string> externs;
        set<string> layouts;
        auto usesextern = false;
        for (auto id : used) {
            auto &e = ents[id];
            switch (e.kind) {
                case UnitEntity::Func: externs[e.name] = e.decl; break;
                case UnitEntity::StaticFn: externs[e.name] = e.decl; break;
                case UnitEntity::Literal: case UnitEntity::Channel: case UnitEntity::Queue:
                case UnitEntity::StaticConst: case UnitEntity::Table:
                    if (e.home != file) externs[e.name] = e.decl;
                    break;
                case UnitEntity::SegPtr: case UnitEntity::SegMain:
                    if (e.home != file) externs[e.name] = e.decl;
                    break;
                case UnitEntity::ExternFn: externs[e.name] = e.decl; usesextern = true; break;
                default: break;
            }
        }
        string layoutstext;
        for (auto id : used)
            if (ents[id].kind == UnitEntity::SegFwd) layouts.insert(ents[id].name);
        for (auto &l : layouts) layoutstext += ents[entof[l]].decl + "\n";
        for (auto id : used)
            if (ents[id].kind == UnitEntity::SegBody) layouts.insert(ents[id].name);
        for (auto id : used)
            if (ents[id].kind == UnitEntity::SegBody) layoutstext += ents[id].decl;
        UnitStats::Breakdown parts;
        string text = in.defines + "#include \"goose_runtime.h\"\n\n";
        parts.header = (long long)text.size();
        if (u.kind == UnitBuild::Locations || u.kind == UnitBuild::Literals) {
            text += "\n";
        } else {
            text += types + "\n" + layoutstext;
            parts.types = (long long)types.size();
            parts.layouts = (long long)layoutstext.size();
            if (usesextern) { text += "\n" + cg.includetext; parts.includes += (long long)cg.includetext.size(); }
        }
        text += "\n";
        for (auto &[name, decl] : externs) {
            text += decl + "\n";
            parts.externs += (long long)decl.size() + 1;
            if (name.compare(0, 7, "gs_loc_") == 0) parts.location_externs += (long long)decl.size() + 1;
        }
        text += "\n";
        // Definitions: entities first, then functions in symbol order.
        for (auto &d : u.defs) { text += d; parts.definitions += (long long)d.size(); }
        vector<int> fns = u.chunks;
        for (auto &s : statics) fns.push_back(ents[entof[s]].chunk);
        sort(fns.begin(), fns.end(), [&](int a, int b) { return chunks[a].name < chunks[b].name; });
        for (auto ci : fns) {
            auto &c = chunks[ci];
            string body = c.text;
            if (!c.isstatic && c.kind != UnitChunk::Program) {
                // The external definition: hidden, and not an inline request.
                body = UnitReplace(body, "GS_INLINE ", "");
                auto at = UnitDefinitionAt(body, c.name);
                if (body.compare(at, 7, "static ") == 0) body.replace(at, 7, "GS_HIDDEN ");
            } else if (c.kind == UnitChunk::Program && body.compare(0, 7, "static ") == 0 &&
                       (c.name.compare(0, 9, "gs_tmain_") == 0)) {
                body.replace(0, 7, "GS_HIDDEN ");
            }
            text += body + "\n\n";
            parts.functions += (long long)body.size() + 2;
            parts.location_references += c.locrefbytes;
        }
        u.parts = parts;
        u.text = std::move(text);
        u.bytes = (long long)u.text.size();
    }

    // ---- Write. ----
    std::error_code ec;
    filesystem::create_directories(dir, ec);
    auto write = [&](const string &name, const string &text) {
        auto path = dir + "/" + name;
        auto f = fopen(path.c_str(), "wb");
        if (!f) throw CompileError { cat("cannot write unit file: ", path) };
        fwrite(text.data(), 1, text.size(), f);
        fclose(f);
    };
    write("goose_runtime.h", runtime_header);
    unit_stats.runtime_header_bytes = (long long)runtime_header.size();
    unit_stats.files.clear();
    string list;
    for (auto &[file, u] : units) {
        write(file, u.text);
        list += file + "\n";
    }
    write("units.txt", list);

    // ---- What the report says. ----
    auto &st = unit_stats;
    st.ran = true;
    for (auto &[file, u] : units) {
        UnitStats::Unit s;
        s.file = file;
        s.module = u.module;
        s.kind = u.kind == UnitBuild::Code ? "code" : u.kind == UnitBuild::Globals ? "globals"
                 : u.kind == UnitBuild::Locations ? "locations" : u.kind == UnitBuild::Literals ? "literals"
                 : "program";
        s.bytes = u.bytes;
        s.functions = (long long)u.chunks.size();
        s.parts = u.parts;
        st.units.push_back(s);
        st.files.push_back({ file, u.text });
    }
    for (auto &c : chunks)
        if (c.rep && !c.unit.empty()) st.function_units[c.rep->sf].insert(c.unit);
}

}  // namespace goose
