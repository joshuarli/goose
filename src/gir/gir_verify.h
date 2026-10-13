// Goose compiler — the GIR-H verifier.
//
// Checks that stand between a lowered module and everything that consumes it,
// run in the order of their codes over the whole module, so a module is
// reported under the first code at which any function fails:
//
//   GIR-V001  entry, global initializers, tables, value ids, summary targets
//   GIR-V010  operand and result types, arity
//   GIR-V020  one terminator per block, edge arguments, reachability, dominance
//   GIR-V030  slot addresses inside their scope, stores through mutable
//             references, loadable and storable types
//   GIR-V040  scope enter and leave balance on every path and nest as the
//             scope tree; `ret` with no scope entered
//   GIR-V050  summaries closed over the body
//   GIR-V100  origins on every operation that can abort or stands for a
//             statement
//
// Acceptance does not show that references stay valid: that is carried from
// Core by the lowering, and nothing here knows about it.
#pragma once

#include <optional>

namespace goose {

struct GirViolation {
    string code;      // "GIR-V020", say.
    string message;   // Names the function.
};

class GirVerifier {
public:
    explicit GirVerifier(GirModule &module) : m(module), m_low(module.low) {}

    // The first violation, or none.
    optional<GirViolation> Verify() {
        try {
            Run();
        } catch (GirViolation &v) {
            return v;
        }
        return nullopt;
    }

private:
    GirModule &m;
    bool m_low;

    struct Fn {
        string label;
        const GirFunc *f;
        vector<GirTypeId> vt;   // Type of each value by id, -1 where unknown.
        int nvalues = 0;
    };
    vector<Fn> fns;
    vector<pair<vector<GirTypeId>, vector<GirTypeId>>> sigs;

    [[noreturn]] static void Fail(const char *code, string msg) { throw GirViolation { code, std::move(msg) }; }

    static int NumValues(const GirFunc &f) {
        int n = 0;
        for (auto &b : f.blocks) {
            n += (int)b.params.size();
            for (auto &i : b.insts) n += GirDefinesValue(i);
        }
        return n;
    }

    // ---------------------------------------------------------------------
    // Uses and origins of an instruction.

    static void Uses(const GirInst &i, vector<int> &out) {
        auto add = [&](int v) { out.push_back(v); };
        switch (i.op) {
            case GirOp::Int: case GirOp::Bool: case GirOp::Unit: case GirOp::Slot: case GirOp::Global:
            case GirOp::Enter: case GirOp::Leave: case GirOp::Unreachable:
                break;
            case GirOp::Abort:
                for (auto v : i.vals) add(v);
                break;
            case GirOp::Bin: case GirOp::Cmp: case GirOp::BoolCmp: case GirOp::Elem:
            case GirOp::Index: case GirOp::Push: case GirOp::Store: case GirOp::Append:
                add(i.a); add(i.b);
                break;
            case GirOp::Un: case GirOp::Not: case GirOp::Conv: case GirOp::Next: case GirOp::Freeze:
            case GirOp::Load: case GirOp::Snap: case GirOp::SliceView: case GirOp::ViewLen:
            case GirOp::ArrayLen: case GirOp::Fill: case GirOp::Init: case GirOp::Exit:
                add(i.a);
                break;
            case GirOp::ViewSlice:
                add(i.a);
                if (i.lo.kind != GirBound::None) add(i.lo.val);
                if (i.hi.kind != GirBound::None) add(i.hi.val);
                break;
            case GirOp::Call: case GirOp::Arr: case GirOp::Ret: case GirOp::Br:
                for (auto v : i.vals) add(v);
                break;
            case GirOp::Print:
                for (auto &p : i.parts) if (!p.text) add(p.val);
                break;
            case GirOp::FrameAddr: case GirOp::LocalGet: case GirOp::GlobalAddr: case GirOp::GlobalStack:
                break;
            case GirOp::PtrOffset: case GirOp::PStore: case GirOp::StackRelease: case GirOp::HdrInit:
            case GirOp::HdrSetLen:
                add(i.a); add(i.b);
                break;
            case GirOp::PLoad: case GirOp::StackAt: case GirOp::StackMark: case GirOp::HdrBase:
            case GirOp::HdrLen: case GirOp::LocalSet:
                add(i.a);
                break;
            case GirOp::StackBump:
                add(i.a);
                if (i.b >= 0) add(i.b);
                break;
            case GirOp::BytesCopy: case GirOp::BytesMove: case GirOp::BytesFill:
                add(i.a); add(i.b);
                for (auto v : i.vals) add(v);
                break;
            case GirOp::RtCall:
                if (i.a >= 0) add(i.a);
                break;
            case GirOp::CondBr:
                add(i.a);
                for (auto v : i.vals) add(v);
                for (auto v : i.vals2) add(v);
                break;
        }
    }

    static bool MayAbortBin(CoreBinOp o) {
        return o == CoreBinOp::Add || o == CoreBinOp::Sub || o == CoreBinOp::Mul ||
               o == CoreBinOp::Div || o == CoreBinOp::Mod;
    }

    // Instructions that can abort or that stand for a source statement must
    // say where they came from.
    bool NeedsOrigin(const GirInst &i) const {
        switch (i.op) {
            case GirOp::Bin: return MayAbortBin(i.bin) && (!m_low || i.flag);
            case GirOp::Un: return i.un == CoreUnOp::Neg && (!m_low || i.flag);
            case GirOp::Conv: return i.conv == CoreConvKind::As;
            case GirOp::ViewSlice: case GirOp::Index: case GirOp::Call:
            case GirOp::Init: case GirOp::Store: case GirOp::Append: case GirOp::Print:
            case GirOp::Abort: case GirOp::Exit:
                return true;
            default: return false;
        }
    }

    static vector<int> Successors(const GirInst &i) {
        if (i.op == GirOp::Br) return { i.idx };
        if (i.op == GirOp::CondBr) return { i.idx, i.idx2 };
        return {};
    }

    static vector<int> BlockSuccessors(const GirBlock &b) {
        vector<int> out;
        for (auto &i : b.insts)
            if (GirIsTerminator(i.op)) for (auto s : Successors(i)) out.push_back(s);
        return out;
    }

    static int TermCount(const GirBlock &b) {
        int n = 0;
        for (auto &i : b.insts) n += GirIsTerminator(i.op);
        return n;
    }

    static const GirInst *LastTerm(const GirBlock &b) {
        if (!b.insts.empty() && GirIsTerminator(b.insts.back().op)) return &b.insts.back();
        return nullptr;
    }

    // ---------------------------------------------------------------------

    void Run() {
        CheckStages();
        CheckEntryAndGlobals();
        for (auto &f : m.funcs) sigs.push_back({ f.params, f.results });
        for (auto &f : m.funcs) fns.push_back({ cat("function ", f.name), &f, {}, 0 });
        for (auto &g : m.globals)
            fns.push_back({ cat("initializer of global ", g.name), &g.init, {}, 0 });
        for (auto &fn : fns) CheckSymbols(fn);
        for (auto &fn : fns) ValueTypes(fn);
        for (auto &fn : fns) CheckTypes(fn);
        for (auto &fn : fns) CheckCfg(fn);
        CheckUnreachable();
        if (m.low) {
            for (auto &fn : fns) CheckPlacement(fn);
            for (auto &fn : fns) CheckOrigins(fn);
            return;
        }
        vector<ScopeWalk> walks;
        for (auto &fn : fns) walks.push_back(WalkScopes(fn));
        for (size_t k = 0; k < fns.size(); k++) {
            if (!walks[k].storage.empty()) Fail("GIR-V030", walks[k].storage);
            CheckStorage(fns[k]);
        }
        for (auto &w : walks)
            if (!w.scopes.empty()) Fail("GIR-V040", w.scopes);
        CheckEffects();
        for (auto &fn : fns) CheckOrigins(fn);
    }

    // --- GIR-V090 ---------------------------------------------------------

    // Only the stage's operations. Read first, because a module that mixes
    // the stages has no types to check.
    void CheckStages() {
        auto scan = [&](const GirFunc &f, const string &label) {
            for (auto &b : f.blocks)
                for (auto &i : b.insts) {
                    if (m.low && GirHighOnly(i.op))
                        Fail("GIR-V090", cat(label, ": an operation of the high stage in a low module"));
                    if (!m.low && GirLowOnly(i.op))
                        Fail("GIR-V090", cat(label, ": an operation of the low stage in a high module"));
                }
        };
        for (auto &f : m.funcs) scan(f, cat("function ", f.name));
        for (auto &g : m.globals) scan(g.init, cat("initializer of global ", g.name));
    }

    static bool ScopeWithin(const vector<int> &parents, int inner, int outer) {
        for (auto s = inner; s >= 0 && s < (int)parents.size(); s = parents[s])
            if (s == outer) return true;
        return false;
    }

    // A resizable's elements top its data stack for its whole life: the only
    // things that move a stack's top are a header's initialization from the
    // stack's own top, a bump that the same block follows with the length
    // update of that stack's header, and the restoring of a mark taken from the
    // same stack. A bump on a stack passed in cannot be tied to a header more
    // exactly than "a header that was passed in".
    struct StackId {
        int kind = 0;   // 0 none, 1 a stack the function owns, 2 a global's, 3 passed in
        int index = 0;
        bool operator==(const StackId &o) const { return kind == o.kind && (kind == 3 || index == o.index); }
    };

    void CheckStackDiscipline(const Fn &fn) {
        auto &f = *fn.f;
        auto bad = [&](const string &msg) { Fail("GIR-V090", cat(fn.label, ": ", msg)); };
        auto n = fn.vt.size();
        vector<StackId> stack(n), header(n), markof(n);
        auto &entry = f.blocks[0];
        for (size_t k = 1; k < entry.params.size(); k++) {
            stack[entry.params[k].first] = { 3, 0 };
            header[entry.params[k].first] = { 3, 0 };
        }
        auto at = [&](const vector<StackId> &v, int x) { return x >= 0 && x < (int)n ? v[x] : StackId {}; };
        for (int pass = 0; pass < 2; pass++)
            for (auto &b : f.blocks)
                for (auto &i : b.insts) {
                    if (i.res < 0 || i.res >= (int)n) continue;
                    switch (i.op) {
                        case GirOp::StackAt: stack[i.res] = { 1, i.idx }; break;
                        case GirOp::GlobalStack: stack[i.res] = { 2, i.idx }; break;
                        // A stack or header held in a variable or returned: it
                        // is one passed in, as far as the block can tell.
                        case GirOp::LocalGet: case GirOp::PLoad:
                            if (m.Type(fn.vt[i.res]).kind == CoreType::Ptr) {
                                stack[i.res] = { 3, 0 };
                                header[i.res] = { 3, 0 };
                            }
                            break;
                        case GirOp::StackMark: markof[i.res] = at(stack, i.a); break;
                        case GirOp::FrameAddr:
                            if (i.idx >= 0 && i.idx < (int)f.members.size() &&
                                f.members[i.idx].kind == GirMember::Header)
                                header[i.res] = { 1, f.members[i.idx].stack };
                            break;
                        case GirOp::GlobalAddr:
                            if (i.idx >= 0 && i.idx < (int)m.lowglobals.size() &&
                                m.lowglobals[i.idx].kind == GirMember::Header)
                                header[i.res] = { 2, i.idx };
                            break;
                        default: break;
                    }
                }
        for (auto &b : f.blocks) {
            vector<StackId> pending;
            for (auto &i : b.insts) {
                switch (i.op) {
                    case GirOp::HdrInit: {
                        auto h = at(header, i.a), mk = at(markof, i.b);
                        if (h.kind == 0 || h.kind == 3 || mk.kind == 0 || !(h == mk))
                            bad("a header initialized from something other than the top of its own stack");
                        break;
                    }
                    case GirOp::StackRelease: {
                        auto s = at(stack, i.a), mk = at(markof, i.b);
                        if (s.kind == 0 || mk.kind == 0 || !(s == mk))
                            bad("a watermark restored from a mark of another stack");
                        break;
                    }
                    case GirOp::StackBump: {
                        auto s = at(stack, i.a);
                        if (s.kind == 0) bad("a bump of a stack that is not known");
                        pending.push_back(s);
                        break;
                    }
                    case GirOp::HdrSetLen: {
                        auto h = at(header, i.a);
                        for (size_t k = 0; k < pending.size(); k++)
                            if (pending[k] == h) { pending.erase(pending.begin() + k); break; }
                        break;
                    }
                    default: break;
                }
            }
            if (!pending.empty()) bad("a stack bumped without the length of its header following in the block");
        }
    }

    // Layouts, placements and hidden parameters are all resolved, and the
    // data stacks are used as placement promised.
    void CheckPlacement(const Fn &fn) {
        auto &f = *fn.f;
        auto bad = [&](const string &msg) { Fail("GIR-V090", cat(fn.label, ": ", msg)); };
        auto scalar = [&](GirTypeId t) {
            auto k = m.Type(t).kind;
            return k == CoreType::Int || k == CoreType::Bool || k == CoreType::Ptr;
        };
        for (auto t : f.params) if (!scalar(t)) bad("a parameter whose layout is not resolved");
        for (auto t : f.results) if (!scalar(t)) bad("a result whose layout is not resolved");
        if (f.params.empty() || m.Type(f.params[0]).kind != CoreType::Int || m.Type(f.params[0]).ity != CoreIntTy::I64)
            bad("the hidden stack base parameter is missing");
        for (auto &b : f.blocks)
            for (auto &p : b.params) if (!scalar(p.second)) bad("a block parameter whose layout is not resolved");
        for (auto t : fn.vt) if (t >= 0 && !scalar(t)) bad("a value whose layout is not resolved");
        for (auto &mem : f.members) {
            if (mem.kind == GirMember::Scalar && (mem.ty < 0 || !scalar(mem.ty)))
                bad("a frame member whose layout is not resolved");
            if (mem.kind == GirMember::Bytes && mem.size <= 0) bad("a block of bytes without a size");
            if (mem.kind == GirMember::Header && (mem.stack < 0 || mem.stack >= f.stacks))
                bad("a header whose data stack is outside the function's stacks");
        }
        // At most one live resizable per stack: two that share a stack have
        // scopes that neither contains the other.
        for (size_t a = 0; a < f.members.size(); a++)
            for (size_t c = a + 1; c < f.members.size(); c++) {
                auto &x = f.members[a], &y = f.members[c];
                if (x.kind != GirMember::Header || y.kind != GirMember::Header || x.stack != y.stack) continue;
                if (ScopeWithin(f.scopes, x.scope, y.scope) || ScopeWithin(f.scopes, y.scope, x.scope))
                    bad(cat("two resizables live on data stack ", x.stack));
            }
        CheckStackDiscipline(fn);
        // Which stack each address value is: one the function owns, or not.
        // A watermark is restored only on a stack the function owns.
        vector<char> owned(fn.vt.size(), 0);
        for (auto &b : f.blocks)
            for (auto &i : b.insts) {
                if (i.op == GirOp::StackAt && i.res >= 0 && i.res < (int)owned.size())
                    owned[i.res] = i.idx >= 0 && i.idx < f.stacks;
                if (i.op == GirOp::StackRelease && !(i.a >= 0 && i.a < (int)owned.size() && owned[i.a]))
                    bad("a watermark restored on a stack the caller owns");
                if (i.op == GirOp::StackBump && i.idx >= 0 && i.b < 0 && i.idx == 0)
                    bad("a stack bumped by nothing");
            }
    }

    // --- GIR-V001 ---------------------------------------------------------

    void CheckEntryAndGlobals() {
        if (m.entry < 0 || m.entry >= (int)m.funcs.size())
            Fail("GIR-V001", cat("the entry ", m.entry, " is outside the function table"));
        auto &e = m.funcs[m.entry];
        // A low function's one parameter is the base of its data stacks.
        if (e.params.size() != (m.low ? 1u : 0u) || !e.results.empty())
            Fail("GIR-V001", cat("the entry ", e.name, " must take no parameters and return nothing"));
        for (auto g : m.initfuncs)
            if (g < 0 || g >= (int)m.funcs.size())
                Fail("GIR-V001", cat("an initializer function ", g, " is outside the function table"));
        for (auto &g : m.globals) {
            if (!g.init.params.empty() || g.init.results.size() != 1 || g.init.results[0] != g.ty)
                Fail("GIR-V001", cat("the initializer of global ", g.name,
                                      " must take no parameters and return its type"));
            if (g.org < 0 || g.org >= (int)m.origins.size())
                Fail("GIR-V001", cat("global ", g.name, ": origin outside the origin table"));
        }
    }

    [[noreturn]] void SymbolFail(const Fn &fn, const string &msg) { Fail("GIR-V001", cat(fn.label, ": ", msg)); }

    void CheckSymbols(Fn &fn) {
        auto &f = *fn.f;
        if (f.blocks.empty()) SymbolFail(fn, "no blocks");
        for (size_t i = 0; i < f.scopes.size(); i++)
            if (f.scopes[i] >= 0 && f.scopes[i] >= (int)i)
                SymbolFail(fn, cat("scope ", i, ": parent ", f.scopes[i], " is not an earlier scope"));
        for (auto &sl : f.slots)
            if (sl.scope < 0 || sl.scope >= (int)f.scopes.size())
                SymbolFail(fn, cat("slot of variable ", sl.var, ": scope ", sl.scope,
                                   " is outside the scope table"));
        if (f.org >= (int)m.origins.size()) SymbolFail(fn, cat("function origin ", f.org, " is outside the origin table"));
        if (!f.summary.unknown) {
            for (auto *list : { &f.summary.reads, &f.summary.writes, &f.summary.grows, &f.summary.rebinds })
                for (auto &t : *list) {
                    if (!t.global && t.index >= (int)f.params.size())
                        SymbolFail(fn, cat("summary names parameter ", t.index, ", which does not exist"));
                    if (t.global && t.index >= (int)m.globals.size())
                        SymbolFail(fn, cat("summary names global ", t.index, ", outside the global table"));
                }
        }
        auto checkRoots = [&](const vector<CoreRootRef> &roots, bool result) {
            for (auto &r : roots) {
                if (r.kind == CoreRootRef::Local) {
                    if (result) SymbolFail(fn, "a result root names a local slot");
                    if (r.index < 0 || r.index >= (int)f.slots.size())
                        SymbolFail(fn, cat("root info names slot ", r.index, ", outside the slot table"));
                } else if (r.kind == CoreRootRef::Global) {
                    if (r.index < 0 || r.index >= (int)m.globals.size())
                        SymbolFail(fn, cat("root info names global ", r.index, ", outside the global table"));
                } else if (r.index < 0 || r.index >= (int)f.params.size()) {
                    SymbolFail(fn, cat("root info names parameter ", r.index, ", which does not exist"));
                }
            }
        };
        auto checkRows = [&](const vector<pair<int, vector<CoreRootRef>>> &rows, bool contents) {
            vector<char> seen(f.params.size(), 0);
            for (auto &row : rows) {
                auto i = row.first;
                if (i < 0 || i >= (int)f.params.size())
                    SymbolFail(fn, cat("root info names parameter ", i, ", which does not exist"));
                if (seen[i]) SymbolFail(fn, cat("root info repeats parameter ", i));
                seen[i] = 1;
                auto &t = m.Type(f.params[i]);
                if (contents) {
                    if (t.kind != CoreType::Ref || m.Type(t.elem).kind != CoreType::Slice)
                        SymbolFail(fn, cat("content root info annotates parameter ", i,
                                           ", which is not a reference to a slice"));
                } else if (t.kind != CoreType::Ref && t.kind != CoreType::Slice) {
                    SymbolFail(fn, cat("root info annotates non-reference parameter ", i));
                }
                checkRoots(row.second, false);
            }
        };
        checkRows(f.roots.params, false);
        checkRows(f.roots.contents, true);
        for (auto &row : f.roots.params)
            for (auto &r : row.second) {
                if (r.kind == CoreRootRef::Local)
                    SymbolFail(fn, cat("root info for parameter ", row.first, " names a local slot"));
                if (r.kind == CoreRootRef::Param && r.index != row.first)
                    SymbolFail(fn, cat("root info for parameter ", row.first, " names parameter ", r.index));
            }
        for (auto &row : f.roots.contents)
            for (auto &r : row.second)
                if (r.kind == CoreRootRef::Local)
                    SymbolFail(fn, cat("content root info for parameter ", row.first, " names a local slot"));
        if (!f.roots.results.empty() && f.roots.results.size() != f.results.size())
            SymbolFail(fn, "root info has another number of result rows than the function signature");
        for (auto &roots : f.roots.results) checkRoots(roots, true);
        // Value ids are dense and each is defined once.
        auto n = NumValues(f);
        fn.nvalues = n;
        vector<char> seen(n, 0);
        auto define = [&](int d) {
            if (d < 0 || d >= n) SymbolFail(fn, cat("value %", d, " is outside the value table of ", n));
            if (seen[d]) SymbolFail(fn, cat("value %", d, " is defined twice"));
            seen[d] = 1;
        };
        for (auto &b : f.blocks) {
            for (auto &p : b.params) define(p.first);
            for (auto &i : b.insts) if (GirDefinesValue(i)) define(i.res);
            for (auto &i : b.insts) CheckInstSymbols(fn, i, n);
        }
    }

    void CheckInstSymbols(const Fn &fn, const GirInst &i, int n) {
        auto &f = *fn.f;
        vector<int> uses;
        Uses(i, uses);
        for (auto v : uses)
            if (v < 0 || v >= n) SymbolFail(fn, cat("value %", v, " is outside the value table of ", n));
        if (i.org >= (int)m.origins.size()) SymbolFail(fn, cat("origin ", i.org, " is outside the origin table"));
        switch (i.op) {
            case GirOp::Slot: case GirOp::Init:
                if (i.idx < 0 || i.idx >= (int)f.slots.size())
                    SymbolFail(fn, cat("slot ", i.idx, " is outside the slot table"));
                break;
            case GirOp::Global:
                if (i.idx < 0 || i.idx >= (int)m.globals.size())
                    SymbolFail(fn, cat("global ", i.idx, " is outside the global table"));
                break;
            case GirOp::Call:
                if (i.idx < 0 || i.idx >= (int)m.funcs.size())
                    SymbolFail(fn, cat("function ", i.idx, " is outside the function table"));
                break;
            case GirOp::Enter: case GirOp::Leave:
                if (i.idx < 0 || i.idx >= (int)f.scopes.size())
                    SymbolFail(fn, cat("scope ", i.idx, " is outside the scope table"));
                break;
            case GirOp::Br: case GirOp::CondBr:
                for (auto b : Successors(i))
                    if (b < 0 || b >= (int)f.blocks.size())
                        SymbolFail(fn, cat("block ", b, " is outside the block table"));
                break;
            default: break;
        }
    }

    // --- Types ------------------------------------------------------------

    // The type of every value, found by typing instructions until nothing
    // changes, so that a value used before its definition in table order still
    // gets a type.
    void ValueTypes(Fn &fn) {
        auto &f = *fn.f;
        fn.vt.assign(fn.nvalues, -1);
        for (auto &b : f.blocks)
            for (auto &p : b.params)
                if (p.first < fn.nvalues) fn.vt[p.first] = p.second;
        for (auto changed = true; changed;) {
            changed = false;
            for (auto &b : f.blocks)
                for (auto &i : b.insts) {
                    if (!GirDefinesValue(i) || i.res >= fn.nvalues || fn.vt[i.res] >= 0) continue;
                    GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members };
                    auto r = GirTyper(env).Of(i);
                    if (r.ok()) {
                        fn.vt[i.res] = r.ty;
                        changed = true;
                    }
                }
        }
    }

    [[noreturn]] void TypeFail(const Fn &fn, const string &msg) { Fail("GIR-V010", cat(fn.label, ": ", msg)); }

    void CheckEffectTypes(const Fn &fn, const GirInst &i) {
        auto &f = *fn.f;
        GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members };
        GirTyper ty(env);
        auto need = [&](GirTyResult r) {
            if (!r.ok()) TypeFail(fn, r.error);
            return r.ty;
        };
        switch (i.op) {
            case GirOp::Init: {
                auto v = need(ty.Data(i.a));
                if (v != f.slots[i.idx].ty)
                    TypeFail(fn, cat("slot ", i.idx, " is initialized with a value of another type"));
                break;
            }
            case GirOp::Store: {
                auto r = need(ty.Ref(i.a));
                auto v = need(ty.Data(i.b));
                if (v != m.Type(r).elem) TypeFail(fn, "a store of a value of another type than the referent");
                break;
            }
            case GirOp::Append: {
                auto r = need(ty.Ref(i.a));
                auto &pointee = m.Type(m.Type(r).elem);
                if (pointee.kind != CoreType::Grow)
                    TypeFail(fn, "append to a reference that does not point at a grow-only array");
                auto v = need(ty.View(i.b));
                if (m.Type(v).elem != pointee.elem)
                    TypeFail(fn, "appended elements of another type than the array's");
                break;
            }
            case GirOp::PStore: {
                need(ty.PtrOf(i.a));
                auto v = need(ty.Data(i.b));
                if (v != i.ty) TypeFail(fn, "a store of a value of another type than the one stated");
                break;
            }
            case GirOp::LocalSet: {
                if (i.idx < 0 || i.idx >= (int)f.members.size() || f.members[i.idx].kind != GirMember::Scalar)
                    TypeFail(fn, cat("frame member ", i.idx, " is not a scalar of the frame"));
                if (need(ty.Data(i.a)) != f.members[i.idx].ty)
                    TypeFail(fn, "a member set to a value of another type");
                break;
            }
            case GirOp::StackRelease: case GirOp::HdrInit:
                need(ty.PtrOf(i.a));
                need(ty.PtrOf(i.b));
                break;
            case GirOp::StackBump:
                need(ty.PtrOf(i.a));
                if (i.b >= 0) need(ty.IntTy(i.b));
                break;
            case GirOp::HdrSetLen:
                need(ty.PtrOf(i.a));
                need(ty.IntTy(i.b));
                break;
            case GirOp::BytesCopy: case GirOp::BytesMove: case GirOp::BytesFill:
                need(ty.PtrOf(i.a));
                need(ty.PtrOf(i.b));
                if (i.vals.size() != 1) TypeFail(fn, "a byte operation without its count");
                need(ty.IntTy(i.vals[0]));
                break;
            case GirOp::RtCall:
                if (i.idx < 0 || i.idx >= (int)GirRt::Count) TypeFail(fn, "a call of an unknown runtime entry point");
                if (i.a >= 0) {
                    auto t = need(ty.Data(i.a));
                    auto k = m.Type(t).kind;
                    if (k != CoreType::Int && k != CoreType::Bool) TypeFail(fn, "a runtime call argument that is not a scalar");
                }
                break;
            case GirOp::Print:
                for (auto &p : i.parts) {
                    if (p.text) continue;
                    auto t = need(ty.Data(p.val));
                    auto k = m.Type(t).kind;
                    if (k != CoreType::Int && k != CoreType::Bool)
                        TypeFail(fn, "a printed value is neither an integer nor a boolean");
                }
                break;
            default: break;
        }
    }

    void CheckTermTypes(const Fn &fn, const GirInst &i) {
        auto &f = *fn.f;
        GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members };
        GirTyper ty(env);
        auto need = [&](GirTyResult r) {
            if (!r.ok()) TypeFail(fn, r.error);
            return r.ty;
        };
        switch (i.op) {
            case GirOp::CondBr:
                if (m.Type(need(ty.Data(i.a))).kind != CoreType::Bool)
                    TypeFail(fn, "a branch condition that is not a boolean");
                break;
            case GirOp::Ret:
                if (i.vals.size() != f.results.size())
                    TypeFail(fn, cat("return of ", i.vals.size(), " values, the function has ",
                                     f.results.size(), " results"));
                for (size_t k = 0; k < i.vals.size(); k++)
                    if (need(ty.Data(i.vals[k])) != f.results[k])
                        TypeFail(fn, "a returned value of another type than the result");
                break;
            case GirOp::Exit: need(ty.IntTy(i.a)); break;
            default: break;
        }
    }

    void CheckTypes(const Fn &fn) {
        auto &f = *fn.f;
        {
            auto &b0 = f.blocks[0];
            bool same = b0.params.size() == f.params.size();
            for (size_t k = 0; same && k < f.params.size(); k++) same = b0.params[k].second == f.params[k];
            if (!same) TypeFail(fn, "the parameters of block 0 are not the function's parameters");
        }
        for (auto &sl : f.slots)
            if (!GirStorable(m, sl.ty))
                TypeFail(fn, cat("the slot of variable ", sl.var, " has a type no variable may have"));
        for (auto &b : f.blocks)
            for (auto &i : b.insts) {
                if (GirDefinesValue(i)) {
                    GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members };
                    auto r = GirTyper(env).Of(i);
                    if (!r.ok()) TypeFail(fn, r.error);
                    if (fn.vt[i.res] != r.ty) TypeFail(fn, cat("value %", i.res, " has two types"));
                } else if (i.op == GirOp::Call) {
                    // A call with no result in the low stage.
                    GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members };
                    auto r = GirTyper(env).Of(i);
                    if (!r.ok()) TypeFail(fn, r.error);
                } else if (GirIsTerminator(i.op)) {
                    CheckTermTypes(fn, i);
                } else {
                    CheckEffectTypes(fn, i);
                }
            }
    }

    // --- GIR-V020 ---------------------------------------------------------

    [[noreturn]] void CfgFail(const Fn &fn, const string &msg) { Fail("GIR-V020", cat(fn.label, ": ", msg)); }

    void CheckEdge(const Fn &fn, int from, int to, const vector<int> &args) {
        auto &tb = fn.f->blocks[to];
        if (tb.params.size() != args.size())
            CfgFail(fn, cat("the branch from block ", from, " to block ", to, " passes ", args.size(),
                            " arguments for ", tb.params.size(), " parameters"));
        for (size_t k = 0; k < args.size(); k++)
            if (fn.vt[args[k]] != tb.params[k].second)
                CfgFail(fn, cat("argument %", args[k], " of the branch from block ", from, " to block ", to,
                                " has another type than parameter %", tb.params[k].first));
    }

    // A function can return normally when some CFG path reaches `ret` while
    // every call on that path is to a function that may return. Start with all
    // functions as possibly returning and remove only functions whose bodies
    // prove otherwise. Treat `unreachable` as an unknown completion, so it can
    // never certify itself or another function as nonreturning.
    bool MayReturn(const GirFunc &f, const vector<char> &mayReturn) const {
        vector<char> seen(f.blocks.size(), 0);
        vector<int> work { 0 };
        while (!work.empty()) {
            auto b = work.back();
            work.pop_back();
            if (b < 0 || b >= (int)f.blocks.size()) return true;
            if (seen[b]) continue;
            seen[b] = 1;
            bool ended = false;
            for (auto &i : f.blocks[b].insts) {
                if (i.op == GirOp::Call && i.idx >= 0 && i.idx < (int)mayReturn.size() && !mayReturn[i.idx]) {
                    ended = true;
                    break;
                }
                switch (i.op) {
                    case GirOp::Ret: return true;
                    case GirOp::Unreachable: return true;
                    case GirOp::Br:
                        work.push_back(i.idx);
                        ended = true;
                        break;
                    case GirOp::CondBr:
                        work.push_back(i.idx);
                        work.push_back(i.idx2);
                        ended = true;
                        break;
                    case GirOp::Abort: case GirOp::Exit:
                        ended = true;
                        break;
                    default: break;
                }
                if (ended) break;
            }
            // A malformed or incomplete block cannot prove nonreturning.
            if (!ended) return true;
        }
        return false;
    }

    vector<char> FunctionsMayReturn() const {
        vector<char> current(m.funcs.size(), 1);
        for (size_t round = 0; round <= m.funcs.size(); round++) {
            vector<char> next(m.funcs.size(), 0);
            for (size_t k = 0; k < m.funcs.size(); k++) next[k] = MayReturn(m.funcs[k], current);
            if (next == current) return current;
            current = std::move(next);
        }
        return current;
    }

    void CheckUnreachable() {
        auto mayReturn = FunctionsMayReturn();
        for (auto &fn : fns)
            for (auto &b : fn.f->blocks)
                for (size_t k = 0; k < b.insts.size(); k++) {
                    if (b.insts[k].op != GirOp::Unreachable) continue;
                    auto valid = k > 0 && b.insts[k - 1].op == GirOp::Call;
                    if (valid) {
                        auto callee = b.insts[k - 1].idx;
                        valid = callee >= 0 && callee < (int)mayReturn.size() && !mayReturn[callee];
                    }
                    if (!valid)
                        CfgFail(fn, "unreachable does not immediately follow a call to a function that cannot return");
                }
    }

    void CheckCfg(const Fn &fn) {
        auto &f = *fn.f;
        auto n = (int)f.blocks.size();
        for (int b = 0; b < n; b++) {
            auto terms = TermCount(f.blocks[b]);
            if (terms != 1) CfgFail(fn, cat("block ", b, " has ", terms, " terminators, expected one"));
            if (!LastTerm(f.blocks[b])) CfgFail(fn, cat("block ", b, " does not end in its terminator"));
        }
        for (int b = 0; b < n; b++) {
            auto t = LastTerm(f.blocks[b]);
            if (t->op == GirOp::Br) CheckEdge(fn, b, t->idx, t->vals);
            if (t->op == GirOp::CondBr) {
                CheckEdge(fn, b, t->idx, t->vals);
                CheckEdge(fn, b, t->idx2, t->vals2);
            }
        }
        vector<vector<int>> preds(n);
        for (int b = 0; b < n; b++)
            for (auto s : BlockSuccessors(f.blocks[b])) preds[s].push_back(b);
        if (!preds[0].empty()) CfgFail(fn, "the entry block has predecessors");
        vector<char> seen(n, 0);
        vector<int> work { 0 };
        seen[0] = 1;
        while (!work.empty()) {
            auto b = work.back();
            work.pop_back();
            for (auto s : BlockSuccessors(f.blocks[b]))
                if (!seen[s]) {
                    seen[s] = 1;
                    work.push_back(s);
                }
        }
        for (int b = 0; b < n; b++)
            if (!seen[b]) CfgFail(fn, cat("block ", b, " is not reachable from the entry"));
        // Dominator sets as bit masks, by rounds until nothing changes.
        auto words = (size_t)(n + 63) / 64;
        vector<vector<uint64_t>> dom(n, vector<uint64_t>(words, ~uint64_t(0)));
        dom[0].assign(words, 0);
        dom[0][0] = 1;
        for (auto changed = true; changed;) {
            changed = false;
            for (int b = 1; b < n; b++) {
                vector<uint64_t> nd(words, ~uint64_t(0));
                for (auto p : preds[b])
                    for (size_t w = 0; w < words; w++) nd[w] &= dom[p][w];
                nd[b / 64] |= uint64_t(1) << (b % 64);
                if (nd != dom[b]) {
                    dom[b] = std::move(nd);
                    changed = true;
                }
            }
        }
        // Definitions dominate uses.
        vector<pair<int, int>> defat(fn.nvalues, { -1, 0 });
        for (int b = 0; b < n; b++) {
            for (auto &p : f.blocks[b].params) defat[p.first] = { b, -1 };
            for (size_t k = 0; k < f.blocks[b].insts.size(); k++)
                if (GirDefinesValue(f.blocks[b].insts[k])) defat[f.blocks[b].insts[k].res] = { b, (int)k };
        }
        for (int u = 0; u < n; u++)
            for (size_t k = 0; k < f.blocks[u].insts.size(); k++) {
                vector<int> uses;
                Uses(f.blocks[u].insts[k], uses);
                for (auto v : uses) {
                    auto [db, dk] = defat[v];
                    if (db < 0) CfgFail(fn, cat("value %", v, " has no definition"));
                    auto ok = db == u ? dk < (int)k : (dom[u][db / 64] >> (db % 64) & 1) != 0;
                    if (!ok)
                        CfgFail(fn, cat("value %", v, " is used in block ", u, " where its definition in block ",
                                        db, " does not dominate the use"));
                }
            }
    }

    // --- GIR-V030 and GIR-V040 -------------------------------------------

    struct ScopeWalk {
        string storage, scopes, join;
    };

    ScopeWalk WalkScopes(const Fn &fn) {
        auto &f = *fn.f;
        auto n = f.blocks.size();
        ScopeWalk w;
        auto note = [](string &slot, string msg) { if (slot.empty()) slot = std::move(msg); };
        vector<char> have(n, 0);
        vector<vector<int>> entry(n);
        entry[0] = {};
        have[0] = 1;
        vector<int> work { 0 };
        // A stack here is outermost first.
        while (!work.empty()) {
            auto b = work.back();
            work.pop_back();
            auto stack = entry[b];
            for (auto &i : f.blocks[b].insts) {
                auto slotin = [&](int s) {
                    if (s < 0 || s >= (int)f.slots.size()) return;
                    if (find(stack.begin(), stack.end(), f.slots[s].scope) == stack.end())
                        note(w.storage, cat(fn.label, ": block ", b, ": the address of slot ", s,
                                            " is taken outside scope ", f.slots[s].scope));
                };
                switch (i.op) {
                    case GirOp::Slot: case GirOp::Init: slotin(i.idx); break;
                    case GirOp::Enter: {
                        auto parent = f.scopes[i.idx];
                        auto ok = parent >= 0 ? !stack.empty() && stack.back() == parent : stack.empty();
                        if (!ok)
                            note(w.scopes, cat(fn.label, ": block ", b, ": scope ", i.idx,
                                               " is entered where its parent is not the innermost scope entered"));
                        stack.push_back(i.idx);
                        break;
                    }
                    case GirOp::Leave:
                        if (stack.empty())
                            note(w.scopes, cat(fn.label, ": block ", b, ": scope ", i.idx,
                                               " is left but none is entered"));
                        else if (stack.back() == i.idx) stack.pop_back();
                        else
                            note(w.scopes, cat(fn.label, ": block ", b, ": scope ", i.idx,
                                               " is left but scope ", stack.back(), " is the innermost entered"));
                        break;
                    case GirOp::Ret:
                        if (!stack.empty())
                            note(w.scopes, cat(fn.label, ": block ", b, ": return with scope ", stack.back(),
                                               " still entered"));
                        break;
                    default: break;
                }
            }
            for (auto s : BlockSuccessors(f.blocks[b])) {
                if (!have[s]) {
                    have[s] = 1;
                    entry[s] = stack;
                    work.push_back(s);
                } else if (entry[s] != stack) {
                    note(w.join, cat(fn.label, ": block ", s, " is reached with different scopes entered"));
                }
            }
        }
        // A join is reported before the other scope problems, which it usually causes.
        if (!w.join.empty()) w.scopes = w.join;
        return w;
    }

    void CheckStorage(const Fn &fn) {
        auto &f = *fn.f;
        auto refof = [&](int v, CoreMut &mut, GirTypeId &pointee) {
            if (v < 0 || v >= (int)fn.vt.size() || fn.vt[v] < 0) return false;
            auto &t = m.Type(fn.vt[v]);
            if (t.kind != CoreType::Ref) return false;
            mut = t.mut;
            pointee = t.elem;
            return true;
        };
        for (auto &b : f.blocks)
            for (auto &i : b.insts) {
                CoreMut mut;
                GirTypeId pt;
                if (i.op == GirOp::Load) {
                    if (refof(i.a, mut, pt) && !GirReadable(m, pt))
                        Fail("GIR-V030", cat(fn.label, ": a load of a value that cannot be copied"));
                } else if (i.op == GirOp::Store) {
                    if (refof(i.a, mut, pt)) {
                        if (mut != CoreMut::Mut)
                            Fail("GIR-V030", cat(fn.label, ": a store through a read-only reference"));
                        if (!GirReadable(m, pt))
                            Fail("GIR-V030", cat(fn.label, ": a store of a value that cannot be copied"));
                    }
                } else if (i.op == GirOp::Push || i.op == GirOp::Append) {
                    if (refof(i.a, mut, pt) && mut != CoreMut::Mut)
                        Fail("GIR-V030", cat(fn.label, ": growth through a read-only reference"));
                }
            }
    }

    // --- GIR-V050 ---------------------------------------------------------
    //
    // Root annotations summarize specialized parameter and result roots from
    // Core contexts. Provenance and result roots are inferred from the body;
    // computed roots and call-site arguments must fit the annotations before
    // those annotations can be used to attribute effects.

    using Roots = vector<CoreRootRef>;

    struct Prov {
        vector<Roots> slots, vals;
    };

    static bool AddTo(vector<Roots> &a, int i, const Roots &rs) {
        if (i < 0 || i >= (int)a.size()) return false;
        auto changed = false;
        for (auto &r : rs)
            if (find(a[i].begin(), a[i].end(), r) == a[i].end()) {
                a[i].push_back(r);
                changed = true;
            }
        return changed;
    }

    static Roots RootsAt(const vector<Roots> &a, int i) {
        return i >= 0 && i < (int)a.size() ? a[i] : Roots {};
    }

    static void AddRoot(Roots &to, const CoreRootRef &r) {
        if (find(to.begin(), to.end(), r) == to.end()) to.push_back(r);
    }

    static void AddRoots(Roots &to, const Roots &from) {
        for (auto &r : from) AddRoot(to, r);
    }

    const Roots *ParamRoots(const GirFunc &f, int param) const {
        for (auto &row : f.roots.params) if (row.first == param) return &row.second;
        return nullptr;
    }

    const Roots *ContentRoots(const GirFunc &f, int param) const {
        for (auto &row : f.roots.contents) if (row.first == param) return &row.second;
        return nullptr;
    }

    Roots ExpandParameterRoots(const GirFunc &f, const Roots &roots) const {
        Roots out;
        for (auto &root : roots) {
            if (root.kind != CoreRootRef::Param) {
                AddRoot(out, root);
                continue;
            }
            auto annotated = ParamRoots(f, root.index);
            if (!annotated || annotated->empty()) AddRoot(out, root);
            else AddRoots(out, *annotated);
        }
        return out;
    }

    bool IsRefSlice(GirTypeId ty) const {
        auto &t = m.Type(ty);
        return t.kind == CoreType::Ref && m.Type(t.elem).kind == CoreType::Slice;
    }

    Roots MapArgumentRoots(const Fn &caller, const Prov &p, int value, int calleeParam) const {
        Roots out;
        for (auto &r : RootsAt(p.vals, value)) {
            if (r.kind == CoreRootRef::Global) {
                AddRoot(out, r);
            } else if (r.kind == CoreRootRef::Local) {
                AddRoot(out, { CoreRootRef::Param, calleeParam });
            } else {
                auto annotated = ParamRoots(*caller.f, r.index);
                if (!annotated || annotated->empty()) {
                    AddRoot(out, { CoreRootRef::Param, calleeParam });
                } else {
                    for (auto &root : *annotated) {
                        if (root.kind == CoreRootRef::Global) AddRoot(out, root);
                        else AddRoot(out, { CoreRootRef::Param, calleeParam });
                    }
                }
            }
        }
        return out;
    }

    Roots ArgumentContents(const Fn &caller, const Prov &p, int value) const {
        Roots out;
        for (auto &r : RootsAt(p.vals, value)) {
            if (r.kind == CoreRootRef::Local) {
                AddRoots(out, RootsAt(p.slots, r.index));
            } else if (r.kind == CoreRootRef::Global) {
                AddRoot(out, r);
            } else if (r.index >= 0 && r.index < (int)caller.f->params.size() &&
                       IsRefSlice(caller.f->params[r.index])) {
                if (auto contents = ContentRoots(*caller.f, r.index)) AddRoots(out, *contents);
            }
        }
        return out;
    }

    Roots MapDeclaredContents(const Prov &p, const vector<int> &args, const Roots &declared) const {
        Roots out;
        for (auto &r : declared) {
            if (r.kind == CoreRootRef::Global) {
                AddRoot(out, r);
            } else if (r.kind == CoreRootRef::Param && r.index >= 0 && r.index < (int)args.size()) {
                AddRoots(out, RootsAt(p.vals, args[r.index]));
            }
        }
        return out;
    }

    void CheckRootAnnotations(const vector<Roots> &res) {
        for (size_t k = 0; k < m.funcs.size(); k++) {
            auto &f = m.funcs[k];
            auto name = cat("function ", f.name);
            for (size_t r = 0; r < f.results.size(); r++) {
                auto declared = r < f.roots.results.size() ? &f.roots.results[r] : nullptr;
                if (r == 0) for (auto &root : RootsAt(res, (int)k))
                    if (!declared || find(declared->begin(), declared->end(), root) == declared->end())
                        Fail("GIR-V050", cat(name, " result ", r, " root info omits a root returned by the body"));
            }
        }

        for (size_t callerIndex = 0; callerIndex < m.funcs.size(); callerIndex++) {
            auto &caller = fns[callerIndex];
            auto &f = *caller.f;
            auto p = Provenance(res, caller);
            for (auto &block : f.blocks)
                for (auto &i : block.insts) {
                    if (i.op != GirOp::Call) continue;
                    auto &callee = m.funcs[i.idx];
                    auto label = cat("function ", callee.name);
                    for (size_t j = 0; j < callee.params.size(); j++) {
                        if (GirRefLike(m, callee.params[j])) {
                            auto expected = MapArgumentRoots(caller, p, i.vals[j], (int)j);
                            auto declared = ParamRoots(callee, (int)j);
                            for (auto &root : expected)
                                if (!declared || find(declared->begin(), declared->end(), root) == declared->end())
                                    Fail("GIR-V050", cat(label, " parameter ", j,
                                        " root info omits a root passed at a call site"));
                        }
                        if (IsRefSlice(callee.params[j])) {
                            auto actual = ArgumentContents(caller, p, i.vals[j]);
                            auto declared = ContentRoots(callee, (int)j);
                            auto mapped = declared ? MapDeclaredContents(p, i.vals, *declared) : Roots {};
                            for (auto &root : actual)
                                if (find(mapped.begin(), mapped.end(), root) == mapped.end())
                                    Fail("GIR-V050", cat(label, " content root info for parameter ", j,
                                        " omits a root passed at a call site"));
                        }
                    }
                }
        }
    }

    bool ValRefLike(const Fn &fn, int v) {
        if (v < 0 || v >= (int)fn.vt.size() || fn.vt[v] < 0) return false;
        auto k = m.Type(fn.vt[v]).kind;
        return k == CoreType::Ref || k == CoreType::Slice || k == CoreType::View;
    }

    Roots RootsOfDef(const vector<Roots> &res, const Fn &fn, const Prov &p, const GirInst &i) {
        switch (i.op) {
            case GirOp::Slot: return { CoreRootRef { CoreRootRef::Local, i.idx } };
            case GirOp::Global: return { CoreRootRef { CoreRootRef::Global, i.idx } };
            case GirOp::Elem: case GirOp::ViewSlice: case GirOp::Index:
                return RootsAt(p.vals, i.a);
            case GirOp::Freeze: case GirOp::Snap: case GirOp::SliceView: case GirOp::Push:
                return RootsAt(p.vals, i.a);
            case GirOp::Load: {
                Roots out;
                if (!ValRefLike(fn, i.res)) return out;
                auto resultIsSlice = m.Type(fn.vt[i.res]).kind == CoreType::Slice;
                for (auto &r : RootsAt(p.vals, i.a)) {
                    if (r.kind == CoreRootRef::Local) {
                        for (auto &x : RootsAt(p.slots, r.index))
                            if (find(out.begin(), out.end(), x) == out.end()) out.push_back(x);
                    } else if (resultIsSlice && r.kind == CoreRootRef::Param &&
                               r.index < (int)fn.f->params.size()) {
                        auto param = fn.f->params[r.index];
                        auto &pt = m.Type(param);
                        if (pt.kind == CoreType::Ref && m.Type(pt.elem).kind == CoreType::Slice)
                            for (auto &row : fn.f->roots.contents)
                                if (row.first == r.index)
                                    for (auto &x : row.second)
                                        if (find(out.begin(), out.end(), x) == out.end()) out.push_back(x);
                    }
                }
                return out;
            }
            case GirOp::Call: {
                Roots out;
                for (auto &r : RootsAt(res, i.idx)) {
                    if (r.kind == CoreRootRef::Param) {
                        if (r.index < (int)i.vals.size())
                            for (auto &x : RootsAt(p.vals, i.vals[r.index]))
                                if (find(out.begin(), out.end(), x) == out.end()) out.push_back(x);
                    } else if (r.kind == CoreRootRef::Global) {
                        if (find(out.begin(), out.end(), r) == out.end()) out.push_back(r);
                    }
                }
                return out;
            }
            default: return {};
        }
    }

    bool ProvRound(const vector<Roots> &res, const Fn &fn, Prov &p) {
        auto &f = *fn.f;
        auto changed = false;
        auto edge = [&](int b, const vector<int> &args) {
            auto &tb = f.blocks[b];
            for (size_t k = 0; k < tb.params.size() && k < args.size(); k++)
                changed |= AddTo(p.vals, tb.params[k].first, RootsAt(p.vals, args[k]));
        };
        for (auto &blk : f.blocks)
            for (auto &i : blk.insts) {
                if (GirDefinesValue(i)) changed |= AddTo(p.vals, i.res, RootsOfDef(res, fn, p, i));
                else if (i.op == GirOp::Init) changed |= AddTo(p.slots, i.idx, RootsAt(p.vals, i.a));
                else if (i.op == GirOp::Store) {
                    for (auto &root : RootsAt(p.vals, i.a))
                        if (root.kind == CoreRootRef::Local)
                            changed |= AddTo(p.slots, root.index, RootsAt(p.vals, i.b));
                } else if (i.op == GirOp::Br) edge(i.idx, i.vals);
                else if (i.op == GirOp::CondBr) {
                    edge(i.idx, i.vals);
                    edge(i.idx2, i.vals2);
                }
            }
        return changed;
    }

    // Each reference-like parameter of the entry block is rooted at itself.
    Prov ProvStart(const Fn &fn) {
        auto &f = *fn.f;
        Prov p;
        p.slots.assign(f.slots.size(), {});
        p.vals.assign(fn.nvalues, {});
        auto &b0 = f.blocks[0];
        for (size_t k = 0; k < b0.params.size(); k++)
            if (ValRefLike(fn, b0.params[k].first) && b0.params[k].first < fn.nvalues)
                p.vals[b0.params[k].first] = { CoreRootRef { CoreRootRef::Param, (int)k } };
        return p;
    }

    Prov Provenance(const vector<Roots> &res, const Fn &fn) {
        auto p = ProvStart(fn);
        while (ProvRound(res, fn, p)) {}
        return p;
    }

    Roots ReturnedRoots(const Fn &fn, const Prov &p) {
        Roots out;
        for (auto &b : fn.f->blocks)
            for (auto &i : b.insts)
                if (i.op == GirOp::Ret && i.vals.size() == 1)
                    for (auto &r : RootsAt(p.vals, i.vals[0]))
                        if (find(out.begin(), out.end(), r) == out.end()) out.push_back(r);
        return out;
    }

    vector<Roots> ResultRoots() {
        vector<Roots> res(m.funcs.size());
        for (auto changed = true; changed;) {
            changed = false;
            auto next = res;
            for (size_t k = 0; k < m.funcs.size(); k++)
                changed |= AddTo(next, (int)k, ReturnedRoots(fns[k], Provenance(res, fns[k])));
            res = std::move(next);
        }
        return res;
    }

    struct Eff {
        set<CoreTarget> reads, writes, grows, rebinds;
        bool aborts = false, outputs = false, unknown = false;
    };

    static void AddTargets(set<CoreTarget> &to, const Roots &rs) {
        for (auto &r : rs) {
            if (r.kind == CoreRootRef::Global) to.insert({ true, r.index });
            else if (r.kind == CoreRootRef::Param) to.insert({ false, r.index });
        }
    }

    Eff Effects(const Fn &fn, const Prov &p) {
        auto &f = *fn.f;
        Eff e;
        for (auto &blk : f.blocks)
            for (auto &i : blk.insts) {
                switch (i.op) {
                    case GirOp::Load: case GirOp::Snap: case GirOp::ArrayLen:
                        AddTargets(e.reads, RootsAt(p.vals, i.a));
                        break;
                    case GirOp::Push: AddTargets(e.grows, RootsAt(p.vals, i.a)); break;
                    case GirOp::Bin: if (MayAbortBin(i.bin)) e.aborts = true; break;
                    case GirOp::Un: if (i.un == CoreUnOp::Neg) e.aborts = true; break;
                    case GirOp::Conv: if (i.conv == CoreConvKind::As) e.aborts = true; break;
                    case GirOp::ViewSlice: case GirOp::Index: e.aborts = true; break;
                    case GirOp::Call: {
                        auto &callee = m.funcs[i.idx];
                        if (callee.summary.unknown) { e.unknown = true; break; }
                        auto map = [&](const vector<CoreTarget> &from, set<CoreTarget> &to) {
                            for (auto &t : from) {
                                if (t.global) to.insert(t);
                                else if (t.index < (int)i.vals.size()) {
                    AddTargets(to, ExpandParameterRoots(f, RootsAt(p.vals, i.vals[t.index])));
                                    if (t.index < (int)callee.params.size()) {
                                        auto &pt = m.Type(callee.params[t.index]);
                                        if (pt.kind == CoreType::Ref || pt.kind == CoreType::Slice)
                                            for (auto &row : callee.roots.params)
                                                if (row.first == t.index)
                                                    for (auto &r : row.second)
                                                        if (r.kind == CoreRootRef::Global)
                                                            to.insert({ true, r.index });
                                    }
                                }
                            }
                        };
                        map(callee.summary.reads, e.reads);
                        map(callee.summary.writes, e.writes);
                        map(callee.summary.grows, e.grows);
                        e.aborts |= callee.summary.aborts;
                        e.outputs |= callee.summary.outputs;
                        break;
                    }
                    case GirOp::Store: {
                        auto rs = RootsAt(p.vals, i.a);
                        AddTargets(e.writes, rs);
                        // A store through a reference-to-slice parameter replaces
                        // the caller's slice binding.
                        for (auto &r : rs)
                            if (r.kind == CoreRootRef::Param && r.index < (int)f.params.size()) {
                                auto &pt = m.Type(f.params[r.index]);
                                if (pt.kind == CoreType::Ref && m.Type(pt.elem).kind == CoreType::Slice)
                                    e.rebinds.insert({ false, r.index });
                            } else if (r.kind == CoreRootRef::Local && r.index < (int)f.slots.size()) {
                                auto &sl = f.slots[r.index];
                                if (GirRefLike(m, sl.ty) && sl.var < (int)f.params.size())
                                    e.rebinds.insert({ false, sl.var });
                            }
                        break;
                    }
                    case GirOp::Append: AddTargets(e.grows, RootsAt(p.vals, i.a)); break;
                    case GirOp::Print: e.outputs = true; break;
                    case GirOp::Abort: case GirOp::Exit: e.aborts = true; break;
                    default: break;
                }
            }
        return e;
    }

    void CheckEffects() {
        auto res = ResultRoots();
        CheckRootAnnotations(res);
        for (size_t k = 0; k < m.funcs.size(); k++) {
            auto &f = m.funcs[k];
            if (f.summary.unknown) continue;
            auto e = Effects(fns[k], Provenance(res, fns[k]));
            auto name = cat("function ", f.name);
            if (e.unknown)
                Fail("GIR-V050", cat(name, " calls a function whose summary is unknown, so its own summary cannot be known"));
            auto within = [&](const char *what, const set<CoreTarget> &found, const vector<CoreTarget> &declared) {
                for (auto &t : found)
                    if (find(declared.begin(), declared.end(), t) == declared.end())
                        Fail("GIR-V050", cat(name, " ", what, " ", t.global ? "global " : "parameter ", t.index,
                                              ", which its summary omits"));
            };
            within("reads", e.reads, f.summary.reads);
            within("writes", e.writes, f.summary.writes);
            within("grows", e.grows, f.summary.grows);
            within("rebinds", e.rebinds, f.summary.rebinds);
            if (e.aborts && !f.summary.aborts) Fail("GIR-V050", cat(name, " may abort, which its summary omits"));
            if (e.outputs && !f.summary.outputs) Fail("GIR-V050", cat(name, " prints, which its summary omits"));
        }
    }

    // --- GIR-V100 ---------------------------------------------------------

    void CheckOrigins(const Fn &fn) {
        for (auto &b : fn.f->blocks)
            for (auto &i : b.insts)
                if (NeedsOrigin(i) && i.org < 0)
                    Fail("GIR-V100", cat(fn.label, ": an operation that can abort or stands for a statement has no origin"));
    }
};

}  // namespace goose
