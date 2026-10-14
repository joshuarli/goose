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
//   GIR-V060  whole-owner replacement starts from proven empty storage
//   GIR-V080  every proven index follows from its fact certificate
//   GIR-V090  operations belong to the module stage
//   GIR-V100  origins on every operation that can abort or stands for a
//             statement
//
// Acceptance does not show that references stay valid: that is carried from
// Core by the lowering, and nothing here knows about it.
#pragma once

#include <charconv>
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
        bool initializer = false;
        vector<GirTypeId> vt;   // Type of each value by id, -1 where unknown.
        int nvalues = 0;
    };
    vector<Fn> fns;
    vector<pair<vector<GirTypeId>, vector<GirTypeId>>> sigs;
    vector<vector<int>> lowPassedPairs;
    vector<bool> lowReturnedOwnerPairs;

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
            case GirOp::Index: case GirOp::IndexProven: case GirOp::Push: case GirOp::Store: case GirOp::Append:
            case GirOp::PopN: case GirOp::Replace:
                add(i.a); add(i.b);
                break;
            case GirOp::Resize:
                add(i.a); add(i.b);
                for (auto v : i.vals) add(v);
                break;
            case GirOp::Un: case GirOp::Not: case GirOp::Conv: case GirOp::Next: case GirOp::Freeze:
            case GirOp::Load: case GirOp::Snap: case GirOp::SliceView: case GirOp::ViewLen: case GirOp::Field:
            case GirOp::ArrayLen: case GirOp::Fill: case GirOp::Init: case GirOp::Exit:
                add(i.a);
                break;
            case GirOp::DestBytes: case GirOp::DestFinish: case GirOp::DestPublish:
                add(i.a);
                break;
            case GirOp::DestWrite:
                add(i.a); add(i.b);
                break;
            case GirOp::DestOpen:
                if (i.knownCount) add(*i.knownCount);
                break;
            case GirOp::Pop: case GirOp::Clear:
                add(i.a);
                break;
            case GirOp::ViewSlice:
                add(i.a);
                if (i.lo.kind != GirBound::None) add(i.lo.val);
                if (i.hi.kind != GirBound::None) add(i.hi.val);
                break;
            case GirOp::Call: case GirOp::Arr: case GirOp::Struct: case GirOp::Ret: case GirOp::Br:
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
            case GirOp::Push: return CoreHasShrink(m.profile);
            case GirOp::Pop: case GirOp::PopN: case GirOp::Resize: case GirOp::Clear: case GirOp::Replace:
                return true;
            case GirOp::DestOpen:
                return true;
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
        CheckStructTable();
        CheckProfileTypes();
        CheckEntryAndGlobals();
        for (auto &f : m.funcs) sigs.push_back({ f.params, f.results });
        for (auto &f : m.funcs) fns.push_back({ cat("function ", f.name), &f, false, {}, 0 });
        for (auto &g : m.globals)
            fns.push_back({ cat("initializer of global ", g.name), &g.init, true, {}, 0 });
        for (auto &fn : fns) CheckSymbols(fn);
        for (auto &fn : fns) ValueTypes(fn);
        for (auto &fn : fns) CheckTypes(fn);
        for (auto &fn : fns) CheckCfg(fn);
        CheckUnreachable();
        if (m.low) {
            lowPassedPairs.assign(m.funcs.size(), {});
            lowReturnedOwnerPairs.assign(m.funcs.size(), false);
            bool changed = true;
            int rounds = 0;
            while (changed && rounds++ < (int)m.funcs.size() * 4 + 8) {
                auto passed = ComputePassedOwnerPairs(lowReturnedOwnerPairs);
                auto returned = ComputeReturnedOwnerPairs(passed, lowReturnedOwnerPairs);
                changed = passed != lowPassedPairs || returned != lowReturnedOwnerPairs;
                lowPassedPairs = std::move(passed);
                lowReturnedOwnerPairs = std::move(returned);
            }
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
        if (CoreHasConstruction(m.profile))
            for (auto &fn : fns) CheckConstruction(fn);
        if (CoreHasShrink(m.profile)) {
            auto resultRoots = ResultRoots();
            for (auto &fn : fns) CheckShrinkReplace(fn, resultRoots);
        }
        for (auto &fn : fns)
            if (auto error = CheckGirEvidence(m, *fn.f, fn.vt))
                Fail("GIR-V080", cat(fn.label, ": ", *error));
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

    void CheckStructTable() {
        if (m.profile != CoreProfile::Pilot && !CoreHasShrink(m.profile))
            Fail("GIR-V010", "unknown Core profile");
        auto hasStructType = false;
        for (auto &t : m.types) hasStructType |= t.kind == CoreType::Struct;
        auto hasStructInst = false;
        auto scan = [&](const GirFunc &f) {
            for (auto &b : f.blocks)
                for (auto &i : b.insts)
                    hasStructInst |= i.op == GirOp::Struct || i.op == GirOp::Field;
        };
        for (auto &f : m.funcs) scan(f);
        for (auto &g : m.globals) scan(g.init);

        if (m.low) {
            if (hasStructType || hasStructInst || !m.structs.empty() || !m.targets.empty())
                Fail("GIR-V090", "a low module retains a struct type, descriptor, or operation");
            return;
        }
        if (!CoreHasConstruction(m.profile) && !m.targets.empty())
            Fail("GIR-V010", "only core-construction has a target table");
        if (CoreHasConstruction(m.profile)) {
            set<vector<int>> targetsets;
            for (auto &target : m.targets) {
                if (target.members.empty() ||
                    !is_sorted(target.members.begin(), target.members.end()) ||
                    adjacent_find(target.members.begin(), target.members.end()) != target.members.end() ||
                    !targetsets.insert(target.members).second)
                    Fail("GIR-V001", "a construction target is empty, repeated, or not sorted");
                for (auto member : target.members)
                    if (member < 0 || member >= (int)m.funcs.size())
                        Fail("GIR-V001", cat("construction target member ", member,
                                             " is outside the function table"));
                auto &results = m.funcs[target.members[0]].results;
                for (auto member : target.members)
                    if (m.funcs[member].results != results)
                        Fail("GIR-V010", "construction target members have different result types");
            }
        }
        if (m.profile == CoreProfile::Pilot) {
            if (hasStructType || hasStructInst || !m.structs.empty())
                Fail("GIR-V010", "core-pilot has no struct table or struct operations");
            return;
        }

        vector<int> typeForStruct(m.structs.size(), -1);
        for (size_t t = 0; t < m.types.size(); t++) {
            auto &ty = m.types[t];
            if (ty.kind != CoreType::Struct) continue;
            if (ty.structid < 0 || ty.structid >= (int)m.structs.size())
                Fail("GIR-V010", cat("struct type ", t, " names a descriptor outside the table"));
            if (typeForStruct[ty.structid] >= 0)
                Fail("GIR-V010", cat("struct descriptor ", ty.structid, " has more than one type entry"));
            typeForStruct[ty.structid] = (int)t;
        }
        for (size_t s = 0; s < m.structs.size(); s++) {
            auto &st = m.structs[s];
            if (typeForStruct[s] < 0)
                Fail("GIR-V010", cat("struct descriptor ", s, " has no nominal type entry"));
            if (st.size <= 0) Fail("GIR-V010", cat("struct descriptor ", s, " has nonpositive size"));
            int64_t end = 0;
            for (size_t f = 0; f < st.fields.size(); f++) {
                auto &field = st.fields[f];
                if (field.type < 0 || field.type >= (int)m.types.size())
                    Fail("GIR-V010", cat("struct ", s, " field ", f, " has a type outside the type table"));
                if ((uint8_t)field.binding > (uint8_t)CoreVarKind::Var ||
                    (uint8_t)field.contents > (uint8_t)CoreMut::Const)
                    Fail("GIR-V010", cat("struct ", s, " field ", f, " has an unknown permission"));
                if (field.type >= typeForStruct[s])
                    Fail("GIR-V010", cat("struct ", s, " field ", f, " does not precede its containing type"));
                if (!GirFlat(m, field.type))
                    Fail("GIR-V010", cat("struct ", s, " field ", f, " is not flat and fixed"));
                auto bytes = FlatSize(field.type);
                if (bytes <= 0 || field.offset < end || field.offset < 0 ||
                    field.offset > st.size || bytes > st.size - field.offset)
                    Fail("GIR-V010", cat("struct ", s, " field ", f, " has an invalid byte extent"));
                end = field.offset + bytes;
            }
        }
    }

    void CheckProfileTypes() {
        auto shrinkAbort = [](GirAbortKind kind) {
            return kind >= GirAbortKind::PopEmpty;
        };
        for (size_t id = 0; id < m.types.size(); id++) {
            auto &type = m.types[id];
            if (type.kind == CoreType::Dest || type.kind == CoreType::Built ||
                type.kind == CoreType::Cancelled) {
                if (m.low) Fail("GIR-V090", "a low module retains a construction carrier type");
                if (!CoreHasConstruction(m.profile))
                    Fail("GIR-V010", "a construction carrier type appears outside core-construction");
                if (type.elem < 0 || type.elem >= (int)id)
                    Fail("GIR-V010", cat("construction carrier type ", id, " does not name an earlier type"));
                if ((uint8_t)type.request > (uint8_t)CoreRequest::ElementRun)
                    Fail("GIR-V010", cat("construction carrier type ", id, " has an unknown request"));
                auto &owner = m.Type(type.elem);
                if (owner.kind != CoreType::Grow || owner.elem < 0 ||
                    (m.Type(owner.elem).kind != CoreType::Int && m.Type(owner.elem).kind != CoreType::Bool) ||
                    type.request != CoreRequest::Value)
                    Fail("GIR-V010", cat("construction carrier type ", id,
                                         " is outside the scalar grow-array construction slice"));
                continue;
            }
            if (type.kind != CoreType::GrowShrink && type.kind != CoreType::Limited) continue;
            if (m.low) Fail("GIR-V090", "a low module retains a shrink-profile owner type");
            if (!CoreHasShrink(m.profile))
                Fail("GIR-V010", "core-pilot has no growshrink or limited type");
            if (type.elem < 0 || type.elem >= (int)id)
                Fail("GIR-V010", cat("owner type ", id, " does not name an earlier element type"));
            if (type.kind == CoreType::Limited && (type.count <= 0 || type.count > INT32_MAX))
                Fail("GIR-V010", cat("limited type ", id, " has a capacity outside 1..2147483647"));
            if (!GirFlat(m, type.elem))
                Fail("GIR-V010", cat("owner type ", id, " has a non-flat element type"));
        }
        auto scan = [&](const GirFunc &fn) {
            for (auto &block : fn.blocks)
                for (auto &i : block.insts) {
                    if (i.op == GirOp::Abort) {
                        if ((uint8_t)i.abort > (uint8_t)GirAbortKind::Capacity)
                            Fail("GIR-V010", cat("function ", fn.name, " uses an unknown abort kind"));
                        if (shrinkAbort(i.abort) &&
                            (!CoreHasShrink(m.profile) || !m.low))
                            Fail("GIR-V010", cat("function ", fn.name,
                                                   " uses a shrink abort kind outside core-shrink GIR-L"));
                    }
                    if (m.profile == CoreProfile::Pilot &&
                        (i.op == GirOp::Pop || i.op == GirOp::PopN || i.op == GirOp::Resize ||
                         i.op == GirOp::Clear || i.op == GirOp::Replace))
                        Fail("GIR-V010", cat("function ", fn.name, " uses a shrink operation under core-pilot"));
                }
        };
        for (auto &fn : m.funcs) scan(fn);
        for (auto &global : m.globals) scan(global.init);
        if (CoreHasConstruction(m.profile) && m.low && m.pointerBytes != 4 && m.pointerBytes != 8)
            Fail("GIR-V010", "construction GIR-L pointer size is not 4 or 8 bytes");
    }

    int64_t FlatSize(GirTypeId t) const {
        if (t < 0 || t >= (int)m.types.size()) return 0;
        auto &ty = m.Type(t);
        switch (ty.kind) {
            case CoreType::Int: return CoreIntBits(ty.ity) / 8;
            case CoreType::Bool: return 1;
            case CoreType::Arr: {
                if (ty.count <= 0 || ty.elem < 0 || ty.elem >= (int)m.types.size()) return 0;
                auto element = FlatSize(ty.elem);
                if (element <= 0 || ty.count > INT64_MAX / element) return 0;
                return ty.count * element;
            }
            case CoreType::Struct:
                return ty.structid >= 0 && ty.structid < (int)m.structs.size() ? m.structs[ty.structid].size : 0;
            default: return 0;
        }
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
    // same stack. Passed pairs get identities from the call edges that provide
    // adjacent header and stack words for one owner argument. A returned pair
    // is proven from every normal return's hidden result stores.
    struct StackId {
        int kind = 0;   // 0 unknown, 1 local stack, 2 global, 3 passed pair, 4 safe phi, 5 returned pair, 6 unsafe phi
        int index = 0;
        bool operator==(const StackId &o) const { return kind == o.kind && index == o.index; }
    };

    struct StackFacts {
        vector<StackId> stack, header, markof;
    };

    struct LowAddress {
        int kind = 0; // 1 frame, 2 parameter
        int index = -1;
        int64_t offset = 0;
        bool operator==(const LowAddress &other) const {
            return kind == other.kind && index == other.index && offset == other.offset;
        }
    };

    optional<int64_t> IntegerConstant(const Fn &fn, int value) const {
        for (auto &block : fn.f->blocks)
            for (auto &inst : block.insts) if (inst.op == GirOp::Int && inst.res == value) {
                int64_t parsed = 0;
                auto begin = inst.text.data();
                auto end = begin + inst.text.size();
                auto result = from_chars(begin, end, parsed);
                if (result.ec == errc {} && result.ptr == end) return parsed;
                return nullopt;
            }
        return nullopt;
    }

    optional<LowAddress> PointerLocationOf(const Fn &fn, int value, int depth = 0) const {
        if (depth > fn.nvalues) return nullopt;
        auto &f = *fn.f;
        for (size_t p = 0; p < f.blocks[0].params.size(); p++)
            if (f.blocks[0].params[p].first == value) return LowAddress { 2, (int)p, 0 };
        for (auto &block : f.blocks)
            for (auto &inst : block.insts) {
                if (inst.res != value) continue;
                if (inst.op == GirOp::FrameAddr) return LowAddress { 1, inst.idx, 0 };
                if (inst.op != GirOp::PtrOffset || inst.idx != 8) return nullopt;
                auto base = PointerLocationOf(fn, inst.a, depth + 1);
                auto index = IntegerConstant(fn, inst.b);
                if (!base || !index || (*index != 0 && *index != 1) ||
                    (base->offset != 0 && base->offset != 8)) return nullopt;
                auto offset = base->offset + *index * 8;
                if (offset != 0 && offset != 8) return nullopt;
                base->offset = offset;
                return base;
            }
        return nullopt;
    }

    static bool ReturnableStackId(StackId id) {
        return id.kind == 2 || id.kind == 3 || id.kind == 4 || id.kind == 5;
    }

    // Frame loads inherit owner identity only when one call fills their pair
    // slot and no intervening write or call can change that slot.
    map<int, pair<int, StackId>> ReturnedCallLoads(const Fn &fn,
                                                    const vector<bool> &returnedPairs) const {
        struct OutputCall {
            LowAddress destination;
            int callee = -1;
            int block = -1;
            int position = -1;
            int token = -1;
        };
        vector<OutputCall> calls;
        int nextToken = 0;
        for (size_t b = 0; b < fn.f->blocks.size(); b++)
            for (size_t k = 0; k < fn.f->blocks[b].insts.size(); k++) {
                auto &inst = fn.f->blocks[b].insts[k];
                if (inst.op != GirOp::Call || inst.idx < 0 || inst.idx >= (int)m.funcs.size() ||
                    inst.vals.size() < 2) continue;
                auto &callee = m.funcs[inst.idx];
                if (!callee.results.empty() || callee.params.size() < 2 ||
                    m.Type(callee.params[1]).kind != CoreType::Ptr) continue;
                auto destination = PointerLocationOf(fn, inst.vals[1]);
                if (!destination || destination->kind != 1 || destination->offset != 0 ||
                    destination->index < 0 || destination->index >= (int)fn.f->members.size()) continue;
                auto &member = fn.f->members[destination->index];
                if (member.kind != GirMember::Bytes || member.size < 16) continue;
                calls.push_back({ *destination, inst.idx, (int)b, (int)k, nextToken++ });
            }

        map<int, pair<int, StackId>> loads;
        auto hasInterveningWrite = [&](int block, int begin, int end) {
            auto &insts = fn.f->blocks[block].insts;
            for (int k = begin + 1; k < end; k++)
                switch (insts[k].op) {
                    case GirOp::Call: case GirOp::PStore: case GirOp::BytesCopy: case GirOp::BytesMove:
                    case GirOp::BytesFill: case GirOp::RtCall:
                        return true;
                    default: break;
                }
            return false;
        };
        for (size_t b = 0; b < fn.f->blocks.size(); b++)
            for (size_t k = 0; k < fn.f->blocks[b].insts.size(); k++) {
                auto &inst = fn.f->blocks[b].insts[k];
                if (inst.op != GirOp::PLoad || m.Type(inst.ty).kind != CoreType::Ptr) continue;
                auto address = PointerLocationOf(fn, inst.a);
                if (!address || address->kind != 1 || (address->offset != 0 && address->offset != 8)) continue;
                vector<const OutputCall *> matches;
                for (auto &call : calls)
                    if (call.destination.kind == address->kind && call.destination.index == address->index)
                        matches.push_back(&call);
                if (matches.size() != 1) continue;
                auto &call = *matches[0];
                if (call.block != (int)b || call.position >= (int)k ||
                    call.callee >= (int)returnedPairs.size() || !returnedPairs[call.callee] ||
                    hasInterveningWrite((int)b, call.position, (int)k)) continue;
                loads[inst.res] = { (int)address->offset, { 5, call.token } };
            }
        return loads;
    }

    static StackId MergeStackFacts(const vector<StackId> &values) {
        StackId merged;
        bool hasKnown = false;
        for (auto value : values) {
            if (value.kind == -1) continue;
            if (value.kind == 0) return {};
            if (!hasKnown) {
                merged = value;
                hasKnown = true;
            } else if (!(merged == value)) return {};
        }
        return hasKnown ? merged : StackId { -1, 0 };
    }

    StackFacts AnalyzeStackFacts(const Fn &fn, const vector<int> &passedPairs,
                                 const vector<bool> &returnedPairs) const {
        auto &f = *fn.f;
        auto n = fn.vt.size();
        StackFacts facts { vector<StackId>(n), vector<StackId>(n), vector<StackId>(n) };
        auto returnedLoads = ReturnedCallLoads(fn, returnedPairs);
        for (size_t b = 1; b < f.blocks.size(); b++)
            for (auto &p : f.blocks[b].params) {
                facts.stack[p.first] = { -1, 0 };
                facts.header[p.first] = { -1, 0 };
            }
        auto at = [&](const vector<StackId> &v, int x) {
            return x >= 0 && x < (int)n ? v[x] : StackId {};
        };
        auto &entry = f.blocks[0];
        for (auto pos : passedPairs) {
            if (pos < 0 || pos + 1 >= (int)entry.params.size()) continue;
            auto token = StackId { 3, pos };
            facts.header[entry.params[pos].first] = token;
            facts.stack[entry.params[pos + 1].first] = token;
        }

        struct Edge { int block; vector<int> args; };
        vector<vector<Edge>> incoming(f.blocks.size());
        for (size_t b = 0; b < f.blocks.size(); b++) {
            auto *term = LastTerm(f.blocks[b]);
            if (!term) continue;
            auto add = [&](int target, const vector<int> &args) {
                if (target >= 0 && target < (int)incoming.size())
                    incoming[target].push_back({ (int)b, args });
            };
            if (term->op == GirOp::Br) add(term->idx, term->vals);
            else if (term->op == GirOp::CondBr) {
                add(term->idx, term->vals);
                add(term->idx2, term->vals2);
            }
        }
        map<tuple<int, int, bool>, int> phiTokens;
        int nextToken = 0;
        auto pairToken = [&](int headerValue, int stackValue, bool returnable) {
            auto key = make_tuple(headerValue, stackValue, returnable);
            auto [it, inserted] = phiTokens.emplace(key, nextToken);
            if (inserted) nextToken++;
            return StackId { returnable ? 4 : 6, it->second };
        };

        bool changed = true;
        int rounds = 0;
        while (changed && rounds++ < (int)n * 4 + (int)f.blocks.size() * 4 + 32) {
            changed = false;
            auto set = [&](vector<StackId> &v, int id, StackId value) {
                if (id < 0 || id >= (int)v.size() || v[id] == value) return;
                v[id] = value;
                changed = true;
            };

            for (auto &b : f.blocks)
                for (auto &i : b.insts) {
                    if (i.res < 0 || i.res >= (int)n) continue;
                    switch (i.op) {
                        case GirOp::StackAt: set(facts.stack, i.res, { 1, i.idx }); break;
                        case GirOp::GlobalStack: set(facts.stack, i.res, { 2, i.idx }); break;
                        case GirOp::StackMark:
                            set(facts.markof, i.res, at(facts.stack, i.a));
                            break;
                        case GirOp::PLoad: {
                            auto load = returnedLoads.find(i.res);
                            if (load == returnedLoads.end()) break;
                            if (load->second.first == 0) set(facts.header, i.res, load->second.second);
                            else set(facts.stack, i.res, load->second.second);
                            break;
                        }
                        case GirOp::HdrBase:
                            set(facts.markof, i.res, at(facts.header, i.a));
                            break;
                        case GirOp::PtrOffset:
                            set(facts.markof, i.res, at(facts.markof, i.a));
                            break;
                        case GirOp::FrameAddr:
                            if (i.idx >= 0 && i.idx < (int)f.members.size() &&
                                f.members[i.idx].kind == GirMember::Header)
                                set(facts.header, i.res, { 1, f.members[i.idx].stack });
                            break;
                        case GirOp::GlobalAddr:
                            if (i.idx >= 0 && i.idx < (int)m.lowglobals.size() &&
                                m.lowglobals[i.idx].kind == GirMember::Header)
                                set(facts.header, i.res, { 2, i.idx });
                            break;
                        case GirOp::LocalGet: {
                            vector<StackId> stacks, headers;
                            for (auto &sourceBlock : f.blocks)
                                for (auto &source : sourceBlock.insts)
                                    if (source.op == GirOp::LocalSet && source.idx == i.idx) {
                                        stacks.push_back(at(facts.stack, source.a));
                                        headers.push_back(at(facts.header, source.a));
                                    }
                            set(facts.stack, i.res, MergeStackFacts(stacks));
                            set(facts.header, i.res, MergeStackFacts(headers));
                            break;
                        }
                        default: break;
                    }
                }

            for (size_t b = 1; b < f.blocks.size(); b++) {
                auto &params = f.blocks[b].params;
                auto &edges = incoming[b];
                for (size_t p = 0; p < params.size(); p++) {
                    vector<StackId> stacks, headers;
                    for (auto &edge : edges) {
                        if (p >= edge.args.size()) continue;
                        stacks.push_back(at(facts.stack, edge.args[p]));
                        headers.push_back(at(facts.header, edge.args[p]));
                    }
                    set(facts.stack, params[p].first, MergeStackFacts(stacks));
                    set(facts.header, params[p].first, MergeStackFacts(headers));
                }
                for (size_t hp = 0; hp < params.size(); hp++)
                    for (size_t sp = 0; sp < params.size(); sp++) {
                        bool paired = !edges.empty();
                        bool hasKnownPair = false;
                        StackId firstPair;
                        bool samePair = true;
                        bool allReturnable = true;
                        for (auto &edge : edges) {
                            if (hp >= edge.args.size() || sp >= edge.args.size()) {
                                paired = false;
                                break;
                            }
                            auto h = at(facts.header, edge.args[hp]);
                            auto s = at(facts.stack, edge.args[sp]);
                            if (h.kind == -1 || s.kind == -1) continue;
                            if (h.kind == 0 || !(h == s)) { paired = false; break; }
                            if (!hasKnownPair) firstPair = h;
                            else if (!(firstPair == h)) samePair = false;
                            allReturnable &= ReturnableStackId(h);
                            hasKnownPair = true;
                        }
                        if (!paired || !hasKnownPair) continue;
                        auto token = samePair ? firstPair : pairToken(params[hp].first, params[sp].first,
                            allReturnable);
                        set(facts.header, params[hp].first, token);
                        set(facts.stack, params[sp].first, token);
                    }
            }
        }
        return facts;
    }

    bool LowValueDependsOn(const GirFunc &fn, int value, int parameter) const {
        vector<vector<pair<int, vector<int>>>> incoming(fn.blocks.size());
        for (size_t b = 0; b < fn.blocks.size(); b++) {
            auto *term = LastTerm(fn.blocks[b]);
            if (!term) continue;
            auto add = [&](int target, const vector<int> &args) {
                if (target >= 0 && target < (int)incoming.size())
                    incoming[target].push_back({ (int)b, args });
            };
            if (term->op == GirOp::Br) add(term->idx, term->vals);
            else if (term->op == GirOp::CondBr) {
                add(term->idx, term->vals);
                add(term->idx2, term->vals2);
            }
        }
        set<int> seen;
        function<bool(int)> visit = [&](int current) {
            if (current == parameter) return true;
            if (current < 0 || !seen.insert(current).second) return false;
            for (size_t b = 1; b < fn.blocks.size(); b++)
                for (size_t p = 0; p < fn.blocks[b].params.size(); p++)
                    if (fn.blocks[b].params[p].first == current)
                        for (auto &edge : incoming[b])
                            if (p < edge.second.size() && visit(edge.second[p])) return true;
            for (auto &b : fn.blocks)
                for (auto &i : b.insts) {
                    if (i.res != current) continue;
                    if (i.op == GirOp::PtrOffset && visit(i.a)) return true;
                    if (i.op == GirOp::LocalGet)
                        for (auto &sourceBlock : fn.blocks)
                            for (auto &source : sourceBlock.insts)
                                if (source.op == GirOp::LocalSet && source.idx == i.idx && visit(source.a))
                                    return true;
                }
            return false;
        };
        return visit(value);
    }

    bool LowEntryParamIsOwnerPair(const GirFunc &fn, size_t position) const {
        if (position + 1 >= fn.params.size() ||
            m.Type(fn.params[position]).kind != CoreType::Ptr ||
            m.Type(fn.params[position + 1]).kind != CoreType::Ptr) return false;
        auto header = fn.blocks[0].params[position].first;
        auto stack = fn.blocks[0].params[position + 1].first;
        bool headerUsed = false, stackUsed = false;
        for (auto &b : fn.blocks)
            for (auto &i : b.insts) {
                switch (i.op) {
                    case GirOp::HdrInit: case GirOp::HdrSetLen: case GirOp::HdrBase: case GirOp::HdrLen:
                        headerUsed |= LowValueDependsOn(fn, i.a, header);
                        break;
                    case GirOp::StackMark: case GirOp::StackRelease: case GirOp::StackBump:
                        stackUsed |= LowValueDependsOn(fn, i.a, stack);
                        break;
                    default: break;
                }
            }
        return headerUsed && stackUsed;
    }

    vector<vector<int>> ComputePassedOwnerPairs(const vector<bool> &returnedPairs) const {
        vector<vector<int>> pairs(m.funcs.size());
        bool changed = true;
        int rounds = 0;
        while (changed && rounds++ < (int)m.funcs.size() * 4 + 8) {
            changed = false;
            vector<StackFacts> facts;
            facts.reserve(fns.size());
            for (size_t f = 0; f < fns.size(); f++) {
                const vector<int> empty;
                auto args = f < pairs.size() ? pairs[f] : empty;
                facts.push_back(AnalyzeStackFacts(fns[f], args, returnedPairs));
            }
            auto at = [&](const vector<StackId> &values, int id) {
                return id >= 0 && id < (int)values.size() ? values[id] : StackId {};
            };
            vector<vector<bool>> called(m.funcs.size()), valid(m.funcs.size());
            for (size_t f = 0; f < m.funcs.size(); f++) {
                called[f].assign(m.funcs[f].params.size(), false);
                valid[f].assign(m.funcs[f].params.size(), true);
            }
            for (size_t caller = 0; caller < fns.size(); caller++) {
                auto &function = *fns[caller].f;
                for (auto &b : function.blocks)
                    for (auto &i : b.insts) {
                        if (i.op != GirOp::Call || i.idx < 0 || i.idx >= (int)m.funcs.size()) continue;
                        auto target = i.idx;
                        auto &callee = m.funcs[target];
                        for (size_t p = 1; p + 1 < callee.params.size(); p++) {
                            if (m.Type(callee.params[p]).kind != CoreType::Ptr ||
                                m.Type(callee.params[p + 1]).kind != CoreType::Ptr) continue;
                            called[target][p] = true;
                            if (p + 1 >= i.vals.size()) { valid[target][p] = false; continue; }
                            auto header = at(facts[caller].header, i.vals[p]);
                            auto stack = at(facts[caller].stack, i.vals[p + 1]);
                            if (header.kind <= 0 || !(header == stack)) valid[target][p] = false;
                        }
                    }
            }
            for (size_t f = 0; f < m.funcs.size(); f++)
                for (size_t p = 1; p < called[f].size(); p++)
                    if (((called[f][p] && valid[f][p]) ||
                         (!called[f][p] && LowEntryParamIsOwnerPair(m.funcs[f], p))) &&
                        find(pairs[f].begin(), pairs[f].end(), (int)p) == pairs[f].end()) {
                        pairs[f].push_back((int)p);
                        changed = true;
                    }
        }
        return pairs;
    }

    // The low ABI puts a multiword result behind parameter 1; every normal
    // return must store a matching, externally rooted header/stack pair there.
    vector<bool> ComputeReturnedOwnerPairs(const vector<vector<int>> &passedPairs,
                                           const vector<bool> &returnedPairs) const {
        vector<bool> returned(m.funcs.size(), false);
        for (size_t f = 0; f < m.funcs.size() && f < fns.size(); f++) {
            auto &function = m.funcs[f];
            auto &fn = fns[f];
            if (!function.results.empty() || function.params.size() < 2 ||
                fn.f->blocks.empty() || fn.f->blocks[0].params.size() < 2 ||
                m.Type(function.params[1]).kind != CoreType::Ptr) continue;

            const vector<int> empty;
            auto args = f < passedPairs.size() ? passedPairs[f] : empty;
            auto facts = AnalyzeStackFacts(fn, args, returnedPairs);
            bool sawReturn = false;
            bool everyReturnStoresPair = true;
            for (auto &block : fn.f->blocks) {
                auto *term = LastTerm(block);
                if (!term || term->op != GirOp::Ret) continue;
                sawReturn = true;
                StackId outputHeader, outputStack;
                for (auto &inst : block.insts) {
                    if (inst.op != GirOp::PStore || m.Type(inst.ty).kind != CoreType::Ptr) continue;
                    auto destination = PointerLocationOf(fn, inst.a);
                    if (!destination || destination->kind != 2 || destination->index != 1 ||
                        (destination->offset != 0 && destination->offset != 8)) continue;
                    auto &stored = destination->offset == 0 ? outputHeader : outputStack;
                    stored = destination->offset == 0 ? facts.header[inst.b] : facts.stack[inst.b];
                }
                if (outputHeader.kind <= 0 || !(outputHeader == outputStack) ||
                    !ReturnableStackId(outputHeader)) everyReturnStoresPair = false;
            }
            returned[f] = sawReturn && everyReturnStoresPair;
        }
        return returned;
    }

    void CheckStackDiscipline(const Fn &fn) {
        auto &f = *fn.f;
        auto bad = [&](const string &msg) { Fail("GIR-V090", cat(fn.label, ": ", msg)); };
        auto passed = [&]() -> const vector<int> & {
            for (size_t i = 0; i < m.funcs.size(); i++)
                if (&m.funcs[i] == fn.f) return lowPassedPairs[i];
            static const vector<int> empty;
            return empty;
        }();
        auto facts = AnalyzeStackFacts(fn, passed, lowReturnedOwnerPairs);
        auto &stack = facts.stack;
        auto &header = facts.header;
        auto &markof = facts.markof;
        auto n = fn.vt.size();
        auto at = [&](const vector<StackId> &v, int x) { return x >= 0 && x < (int)n ? v[x] : StackId {}; };
        for (auto &b : f.blocks) {
            vector<StackId> pending;
            for (auto &i : b.insts) {
                switch (i.op) {
                    case GirOp::HdrInit: {
                        auto h = at(header, i.a), mk = at(markof, i.b);
                        if (h.kind <= 0 || h.kind == 3 || h.kind == 4 || mk.kind <= 0 || !(h == mk))
                            bad("a header initialized from something other than the top of its own stack");
                        break;
                    }
                    case GirOp::StackRelease: {
                        auto s = at(stack, i.a), mk = at(markof, i.b);
                        if (s.kind <= 0 || mk.kind <= 0 || !(s == mk))
                            bad("a watermark restored from a mark of another stack");
                        break;
                    }
                    case GirOp::StackBump: {
                        auto s = at(stack, i.a);
                        if (s.kind <= 0) bad("a bump of a stack that is not known");
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
        // A caller may pass an owner header and its stack to a callee. The
        // corresponding base is a valid restore point for that same stack.
        for (auto &b : f.blocks)
            for (auto &i : b.insts) {
                if (i.op == GirOp::StackAt && (i.idx < 0 || i.idx >= f.stacks))
                    bad("a stack address is outside the function's owned stacks");
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
            if (m.profile == CoreProfile::Pilot && !f.summary.shrinks.empty())
                SymbolFail(fn, "a core-pilot summary contains shrink targets");
            for (auto *list : { &f.summary.reads, &f.summary.writes, &f.summary.grows,
                                &f.summary.shrinks, &f.summary.rebinds })
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
            case GirOp::DestOpen:
                if (i.idx < 0 || i.idx >= (int)f.slots.size())
                    SymbolFail(fn, cat("destination slot ", i.idx, " is outside the slot table"));
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
                if (!GirOwnerKind(pointee.kind))
                    TypeFail(fn, "append to a reference that does not point at an owner array");
                if (pointee.kind != CoreType::Grow && !CoreHasShrink(m.profile))
                    TypeFail(fn, "shrink-profile append under core-pilot");
                auto v = need(ty.View(i.b));
                if (m.Type(v).elem != pointee.elem)
                    TypeFail(fn, "appended elements of another type than the array's");
                break;
            }
            case GirOp::PopN: {
                auto r = need(ty.Ref(i.a));
                auto kind = m.Type(m.Type(r).elem).kind;
                if (!CoreHasShrink(m.profile) || !GirOwnerKind(kind))
                    TypeFail(fn, "pop_n to a reference that does not point at a shrink-profile owner array");
                need(ty.IntTy(i.b));
                break;
            }
            case GirOp::Resize: {
                auto r = need(ty.Ref(i.a));
                auto &owner = m.Type(m.Type(r).elem);
                if (!CoreHasShrink(m.profile) || !GirOwnerKind(owner.kind))
                    TypeFail(fn, "resize to a reference that does not point at a shrink-profile owner array");
                need(ty.IntTy(i.b));
                if (i.vals.size() > 1) TypeFail(fn, "resize has more than one fill value");
                if (!i.vals.empty() && need(ty.Data(i.vals[0])) != owner.elem)
                    TypeFail(fn, "resize fill value has another type than the owner's elements");
                break;
            }
            case GirOp::Clear: {
                auto r = need(ty.Ref(i.a));
                auto kind = m.Type(m.Type(r).elem).kind;
                if (!CoreHasShrink(m.profile) || !GirOwnerKind(kind))
                    TypeFail(fn, "clear to a reference that does not point at a shrink-profile owner array");
                break;
            }
            case GirOp::Replace: {
                auto r = need(ty.Ref(i.a));
                auto &owner = m.Type(m.Type(r).elem);
                if (!CoreHasShrink(m.profile) || !GirResizableKind(owner.kind))
                    TypeFail(fn, "replace to a reference that does not point at a shrink-profile resizable array");
                if (need(ty.Data(i.b)) != m.Type(r).elem)
                    TypeFail(fn, "replacement run has another type than the owner's");
                break;
            }
            case GirOp::DestBytes: {
                if (m.low || !CoreHasConstruction(m.profile))
                    TypeFail(fn, "byte construction outside core-construction GIR-H");
                auto destination = need(ty.Val(i.a));
                auto &carrier = m.Type(destination);
                if (carrier.kind != CoreType::Dest || carrier.request != CoreRequest::Value)
                    TypeFail(fn, "byte initialization does not use a value-form destination");
                auto &owner = m.Type(carrier.elem);
                if (owner.kind != CoreType::Grow || m.Type(owner.elem).kind != CoreType::Int ||
                    m.Type(owner.elem).ity != CoreIntTy::U8)
                    TypeFail(fn, "byte initialization requires a grow-only u8 array");
                break;
            }
            case GirOp::DestWrite: {
                if (m.low || !CoreHasConstruction(m.profile))
                    TypeFail(fn, "element construction outside core-construction GIR-H");
                auto destination = need(ty.Val(i.a));
                auto &carrier = m.Type(destination);
                if (carrier.kind != CoreType::Dest || carrier.request != CoreRequest::Value)
                    TypeFail(fn, "element write does not use a value-form destination");
                auto &owner = m.Type(carrier.elem);
                auto elementKind = m.Type(owner.elem).kind;
                if (owner.kind != CoreType::Grow ||
                    (elementKind != CoreType::Int && elementKind != CoreType::Bool))
                    TypeFail(fn, "element write requires a grow-only array of scalar elements");
                if (need(ty.Data(i.b)) != owner.elem)
                    TypeFail(fn, "constructed element has another type than the destination element");
                break;
            }
            case GirOp::DestPublish: {
                if (m.low || !CoreHasConstruction(m.profile))
                    TypeFail(fn, "construction publication outside core-construction GIR-H");
                auto completed = need(ty.Val(i.a));
                auto &carrier = m.Type(completed);
                if (carrier.kind != CoreType::Built || carrier.request != CoreRequest::Value)
                    TypeFail(fn, "publication does not consume a value-form completion");
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
        for (auto param : f.params)
            if (GirOwnerKind(m.Type(param).kind))
                TypeFail(fn, "a nonfixed owner is a by-value parameter");
        for (auto result : f.results)
            if (IsRefSlice(result))
                TypeFail(fn, "a reference-to-slice type is only valid for a parameter");
            else if (GirOwnerKind(m.Type(result).kind) && !fn.initializer)
                TypeFail(fn, "a nonfixed owner is a by-value result");
        for (size_t index = 0; index < f.slots.size(); index++) {
            auto &sl = f.slots[index];
            if (sl.var != (int)index)
                TypeFail(fn, cat("slot ", index, " names variable ", sl.var,
                                 ", expected variable ", index));

            auto param = (int)index;
            bool parameterRefSliceSlot = param >= 0 && param < (int)f.params.size() &&
                                         f.params[param] == sl.ty &&
                                         f.blocks[0].params[param].second == sl.ty && IsRefSlice(sl.ty);
            if (!GirStorable(m, sl.ty) && !parameterRefSliceSlot)
                TypeFail(fn, cat("the slot of variable ", sl.var, " has a type no variable may have"));
        }
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
                    case GirOp::Slot: case GirOp::Init: case GirOp::DestOpen: slotin(i.idx); break;
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
        vector<const GirInst *> defs(fn.nvalues, nullptr);
        vector<vector<int>> incoming(fn.nvalues);
        for (auto &b : f.blocks)
            for (auto &i : b.insts)
                if (GirDefinesValue(i) && i.res >= 0 && i.res < fn.nvalues) defs[i.res] = &i;
        auto addEdge = [&](int target, const vector<int> &args) {
            if (target < 0 || target >= (int)f.blocks.size()) return;
            auto &params = f.blocks[target].params;
            for (size_t k = 0; k < params.size() && k < args.size(); k++)
                if (params[k].first >= 0 && params[k].first < fn.nvalues)
                    incoming[params[k].first].push_back(args[k]);
        };
        for (auto &b : f.blocks) for (auto &i : b.insts) {
            if (i.op == GirOp::Br) addEdge(i.idx, i.vals);
            else if (i.op == GirOp::CondBr) {
                addEdge(i.idx, i.vals);
                addEdge(i.idx2, i.vals2);
            }
        }
        auto refof = [&](int v, CoreMut &mut, GirTypeId &pointee) {
            if (v < 0 || v >= (int)fn.vt.size() || fn.vt[v] < 0) return false;
            auto &t = m.Type(fn.vt[v]);
            if (t.kind != CoreType::Ref) return false;
            mut = t.mut;
            pointee = t.elem;
            return true;
        };
        function<bool(int, vector<char> &)> contentsMutable = [&](int v, vector<char> &open) {
            if (v < 0 || v >= fn.nvalues || fn.vt[v] < 0) return false;
            // A backedge can carry the same capability as its loop input. The
            // other incoming edges still have to prove that capability.
            if (open[v]) return true;
            open[v] = 1;
            auto close = [&](bool result) { open[v] = 0; return result; };
            auto *def = defs[v];
            if (def && (def->op == GirOp::Slot || def->op == GirOp::Global)) {
                auto pointee = m.Type(fn.vt[v]).elem;
                auto kind = m.Type(pointee).kind;
                if (kind == CoreType::Struct || kind == CoreType::Arr || GirOwnerKind(kind))
                    return close(true);
                CoreMut mut;
                GirTypeId ignored;
                return close(refof(v, mut, ignored) && mut == CoreMut::Mut);
            }
            if (def && def->op == GirOp::Freeze) return close(false);
            if (def && def->op == GirOp::Field) {
                auto base = fn.vt[def->a];
                if (base < 0 || m.Type(base).kind != CoreType::Ref) return close(false);
                auto owner = m.Type(base).elem;
                if (m.Type(owner).kind != CoreType::Struct) return close(false);
                auto sid = m.Type(owner).structid;
                if (sid < 0 || sid >= (int)m.structs.size()) return close(false);
                auto &fields = m.structs[sid].fields;
                if (def->idx < 0 || def->idx >= (int)fields.size()) return close(false);
                return close(contentsMutable(def->a, open) && fields[def->idx].contents == CoreMut::Mut);
            }
            if (def && def->op == GirOp::Snap) {
                if (def->snap == GirSnapshotMode::Owner) return close(contentsMutable(def->a, open));
                CoreMut mut;
                GirTypeId pointee;
                return close(refof(def->a, mut, pointee) && mut == CoreMut::Mut &&
                             contentsMutable(def->a, open));
            }
            if (def && (def->op == GirOp::SliceView || def->op == GirOp::ViewSlice ||
                        def->op == GirOp::Elem || def->op == GirOp::Index ||
                        def->op == GirOp::IndexProven))
                return close(contentsMutable(def->a, open));
            // The callee's return check has already established that a mutable
            // slice result carries mutable contents.
            if (def && def->op == GirOp::Call) {
                auto &result = m.Type(fn.vt[v]);
                if (result.kind == CoreType::Slice && result.mut == CoreMut::Mut) return close(true);
            }
            if (def && def->op == GirOp::Load) {
                auto &loaded = m.Type(fn.vt[v]);
                if (loaded.kind == CoreType::Slice && loaded.mut == CoreMut::Mut) {
                    auto *address = defs[def->a];
                    if (address && (address->op == GirOp::Slot || address->op == GirOp::Global))
                        return close(true);
                    return close(contentsMutable(def->a, open));
                }
            }
            if (!def) {
                auto &block0 = f.blocks[0];
                auto entryParam = find_if(block0.params.begin(), block0.params.end(),
                                          [&](auto &p) { return p.first == v; });
                if (entryParam != block0.params.end()) {
                    auto &t = m.Type(fn.vt[v]);
                    if (t.kind == CoreType::Slice || t.kind == CoreType::View)
                        return close(t.mut == CoreMut::Mut);
                    CoreMut mut;
                    GirTypeId pointee;
                    return close(refof(v, mut, pointee) && mut == CoreMut::Mut);
                }
                if (!incoming[v].empty()) {
                    for (auto source : incoming[v])
                        if (!contentsMutable(source, open)) return close(false);
                    return close(true);
                }
                return close(false);
            }
            CoreMut mut;
            GirTypeId pointee;
            return close(refof(v, mut, pointee) && mut == CoreMut::Mut);
        };
        function<bool(int, vector<char> &)> writable = [&](int v, vector<char> &open) {
            if (v < 0 || v >= fn.nvalues || fn.vt[v] < 0) return false;
            if (open[v]) return true;
            open[v] = 1;
            auto close = [&](bool result) { open[v] = 0; return result; };
            auto *def = defs[v];
            if (def && def->op == GirOp::Field) {
                auto base = fn.vt[def->a];
                if (base < 0 || m.Type(base).kind != CoreType::Ref) return close(false);
                auto owner = m.Type(base).elem;
                if (m.Type(owner).kind != CoreType::Struct) return close(false);
                auto sid = m.Type(owner).structid;
                if (sid < 0 || sid >= (int)m.structs.size()) return close(false);
                auto &fields = m.structs[sid].fields;
                if (def->idx < 0 || def->idx >= (int)fields.size()) return close(false);
                return close(contentsMutable(def->a, open) && fields[def->idx].binding == CoreVarKind::Var);
            }
            if (def && (def->op == GirOp::Elem || def->op == GirOp::Index ||
                        def->op == GirOp::IndexProven))
                return close(contentsMutable(def->a, open));
            if (def && def->op == GirOp::Freeze) return close(false);
            if (!def) {
                auto &entry = f.blocks[0].params;
                if (find_if(entry.begin(), entry.end(), [&](auto &p) { return p.first == v; }) != entry.end()) {
                    CoreMut mut;
                    GirTypeId pointee;
                    return close(refof(v, mut, pointee) && mut == CoreMut::Mut);
                }
                if (!incoming[v].empty()) {
                    for (auto source : incoming[v])
                        if (!writable(source, open)) return close(false);
                    return close(true);
                }
                return close(false);
            }
            CoreMut mut;
            GirTypeId pointee;
            return close(refof(v, mut, pointee) && mut == CoreMut::Mut);
        };
        auto mutableReferenceIsAuthorized = [&](int value, GirTypeId ty) {
            auto &t = m.Type(ty);
            if (t.kind == CoreType::Ref && t.mut == CoreMut::Mut) {
                vector<char> open(fn.nvalues, 0);
                auto kind = m.Type(t.elem).kind;
                if (GirWholeOwnerBorrowUsesContents(kind))
                    return contentsMutable(value, open);
                if (!writable(value, open)) return false;
                if (kind == CoreType::Arr || kind == CoreType::Struct || kind == CoreType::Slice ||
                    kind == CoreType::Limited) {
                    fill(open.begin(), open.end(), 0);
                    return contentsMutable(value, open);
                }
            } else if (t.kind == CoreType::Slice && t.mut == CoreMut::Mut) {
                vector<char> open(fn.nvalues, 0);
                return contentsMutable(value, open);
            }
            return true;
        };
        function<bool(int, vector<char> &)> replacementBindingWritable = [&](int value, vector<char> &open) {
            if (value < 0 || value >= (int)fn.vt.size() || fn.vt[value] < 0) return false;
            // A loop backedge preserves the capability established by its
            // incoming path; every noncyclic predecessor is still checked.
            if (open[value]) return true;
            open[value] = 1;
            auto close = [&](bool result) { open[value] = 0; return result; };
            auto &reference = m.Type(fn.vt[value]);
            auto *def = defs[value];
            if (def && def->op == GirOp::Slot)
                return close(f.slots[def->idx].kind == CoreVarKind::Var);
            if (def && def->op == GirOp::Global)
                return close(m.globals[def->idx].kind == CoreVarKind::Var);
            if (!def) {
                auto &entry = f.blocks[0].params;
                if (find_if(entry.begin(), entry.end(), [&](auto &p) { return p.first == value; }) != entry.end())
                    return close(reference.kind == CoreType::Ref && reference.mut == CoreMut::Mut);
                if (incoming[value].empty()) return close(false);
                for (auto source : incoming[value])
                    if (!replacementBindingWritable(source, open)) return close(false);
                return close(true);
            }
            // A loaded or returned mutable reference carries its callee's checked
            // permission. A CFG parameter is different: every incoming place
            // must independently permit replacing its whole binding.
            return close(true);
        };
        auto replaceBindingIsWritable = [&](int value) {
            vector<char> open(fn.nvalues, 0);
            return replacementBindingWritable(value, open);
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
                        vector<char> open(fn.nvalues, 0);
                        if (!writable(i.a, open))
                            Fail("GIR-V030", cat(fn.label, ": a store through a value without mutable binding and contents"));
                        if (!GirReadable(m, pt))
                            Fail("GIR-V030", cat(fn.label, ": a store of a value that cannot be copied"));
                        if (!mutableReferenceIsAuthorized(i.b, pt))
                            Fail("GIR-V030", cat(fn.label, ": a store materializes a mutable reference without its required capabilities"));
                    }
                } else if (i.op == GirOp::Init) {
                    auto ty = f.slots[i.idx].ty;
                    if (!mutableReferenceIsAuthorized(i.a, ty))
                        Fail("GIR-V030", cat(fn.label, ": a slot initializer materializes a mutable reference without its required capabilities"));
                } else if (i.op == GirOp::Push || i.op == GirOp::Append || i.op == GirOp::Pop ||
                           i.op == GirOp::PopN || i.op == GirOp::Resize || i.op == GirOp::Clear ||
                           i.op == GirOp::Replace) {
                    if (i.op == GirOp::Replace && refof(i.a, mut, pt) && mut != CoreMut::Mut)
                        Fail("GIR-V030", cat(fn.label, ": owner mutation through a read-only reference"));
                    vector<char> open(fn.nvalues, 0);
                    if (!contentsMutable(i.a, open))
                        Fail("GIR-V030", cat(fn.label, ": owner mutation without mutable contents"));
                    if (i.op == GirOp::Replace && !replaceBindingIsWritable(i.a))
                        Fail("GIR-V030", cat(fn.label, ": whole replacement requires a writable owner binding"));
                }
            }
        for (auto &b : f.blocks) for (auto &i : b.insts) if (i.op == GirOp::Call) {
            auto &callee = m.funcs[i.idx];
            for (size_t j = 0; j < callee.params.size() && j < i.vals.size(); j++) {
                auto &pt = m.Type(callee.params[j]);
                if (pt.kind == CoreType::Ref && pt.mut == CoreMut::Mut) {
                    if (!mutableReferenceIsAuthorized(i.vals[j], callee.params[j]))
                        Fail("GIR-V030", cat(fn.label, ": a mutating call receives a value without its required binding and contents capabilities"));
                } else if (pt.kind == CoreType::Slice && pt.mut == CoreMut::Mut) {
                    vector<char> open(fn.nvalues, 0);
                    if (!contentsMutable(i.vals[j], open))
                        Fail("GIR-V030", cat(fn.label, ": a mutating call receives a slice without mutable contents"));
                }
            }
        }
        for (auto &b : f.blocks) for (auto &i : b.insts) if (i.op == GirOp::Ret) {
            for (size_t j = 0; j < i.vals.size() && j < f.results.size(); j++)
                if (!mutableReferenceIsAuthorized(i.vals[j], f.results[j]))
                    Fail("GIR-V030", cat(fn.label, ": a return exposes a mutable reference without its required capabilities"));
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

    bool ValRefLike(const Fn &fn, int v) const {
        if (v < 0 || v >= (int)fn.vt.size() || fn.vt[v] < 0) return false;
        auto k = m.Type(fn.vt[v]).kind;
        return k == CoreType::Ref || k == CoreType::Slice || k == CoreType::View;
    }

    Roots RootsOfDef(const vector<Roots> &res, const Fn &fn, const Prov &p, const GirInst &i) {
        switch (i.op) {
            case GirOp::Slot: return { CoreRootRef { CoreRootRef::Local, i.idx } };
            case GirOp::Global: return { CoreRootRef { CoreRootRef::Global, i.idx } };
            case GirOp::Field: return RootsAt(p.vals, i.a);
            case GirOp::Elem: case GirOp::ViewSlice: case GirOp::Index: case GirOp::IndexProven:
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
        set<CoreTarget> reads, writes, grows, shrinks, rebinds;
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
                    case GirOp::Push: {
                        auto roots = RootsAt(p.vals, i.a);
                        AddTargets(e.grows, roots);
                        if (CoreHasShrink(m.profile)) AddTargets(e.writes, roots);
                        auto &ref = m.Type(fn.vt[i.a]);
                        if (m.Type(ref.elem).kind == CoreType::Limited) e.aborts = true;
                        break;
                    }
                    case GirOp::Pop: case GirOp::PopN: {
                        auto roots = RootsAt(p.vals, i.a);
                        AddTargets(e.reads, roots);
                        AddTargets(e.shrinks, roots);
                        e.aborts = true;
                        break;
                    }
                    case GirOp::Resize: {
                        auto roots = RootsAt(p.vals, i.a);
                        AddTargets(e.reads, roots);
                        AddTargets(e.shrinks, roots);
                        e.aborts = true;
                        if (!i.vals.empty()) {
                            AddTargets(e.writes, roots);
                            AddTargets(e.grows, roots);
                        }
                        break;
                    }
                    case GirOp::Clear: {
                        auto roots = RootsAt(p.vals, i.a);
                        AddTargets(e.reads, roots);
                        AddTargets(e.shrinks, roots);
                        break;
                    }
                    case GirOp::Replace: {
                        auto roots = RootsAt(p.vals, i.a);
                        AddTargets(e.reads, roots);
                        AddTargets(e.shrinks, roots);
                        AddTargets(e.writes, roots);
                        AddTargets(e.grows, roots);
                        break;
                    }
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
                        map(callee.summary.shrinks, e.shrinks);
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
                    case GirOp::Append: {
                        auto roots = RootsAt(p.vals, i.a);
                        AddTargets(e.grows, roots);
                        if (CoreHasShrink(m.profile)) AddTargets(e.writes, roots);
                        AddTargets(e.reads, RootsAt(p.vals, i.b));
                        auto &ref = m.Type(fn.vt[i.a]);
                        if (m.Type(ref.elem).kind == CoreType::Limited) e.aborts = true;
                        break;
                    }
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
            if (CoreHasConstruction(m.profile) &&
                (!f.summary.constructs.empty() || !f.summary.needs.empty() || !f.summary.escapes.empty()))
                Fail("GIR-V050", cat("function ", f.name,
                                     " has construction summary entries outside the implemented byte slice"));
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
            within("shrinks", e.shrinks, f.summary.shrinks);
            within("rebinds", e.rebinds, f.summary.rebinds);
            if (e.aborts && !f.summary.aborts) Fail("GIR-V050", cat(name, " may abort, which its summary omits"));
            if (e.outputs && !f.summary.outputs) Fail("GIR-V050", cat(name, " prints, which its summary omits"));
        }
    }

    // --- GIR-V060 ---------------------------------------------------------
    // Replacement requires a fresh literal run and an empty-owner fact that
    // survives from clear through replace. Receiver accesses and ref-like
    // source operands kill it; calls use their actual roots and summaries, with
    // unknown calls handled conservatively.

    void CheckConstruction(const Fn &fn) {
        auto &f = *fn.f;
        vector<const GirInst *> definitions(fn.nvalues, nullptr);
        vector<int> uses(fn.nvalues, 0);
        vector<int> expectedDestinationUses(fn.nvalues, -1);
        set<pair<int, int>> matched;
        for (size_t block = 0; block < f.blocks.size(); block++) {
            auto &body = f.blocks[block];
            for (auto &param : body.params)
                if (param.second >= 0 && param.second < (int)m.types.size()) {
                    auto kind = m.Type(param.second).kind;
                    if (kind == CoreType::Dest || kind == CoreType::Built || kind == CoreType::Cancelled)
                        Fail("GIR-V060", cat(fn.label, ": a construction carrier is a block parameter"));
                }
            for (size_t index = 0; index < body.insts.size(); index++) {
                auto &inst = body.insts[index];
                if (GirDefinesValue(inst) && inst.res >= 0 && inst.res < fn.nvalues)
                    definitions[inst.res] = &inst;
                vector<int> operands;
                Uses(inst, operands);
                for (auto operand : operands)
                    if (operand >= 0 && operand < fn.nvalues) uses[operand]++;
                if (m.profile == CoreProfile::Construction &&
                    (inst.op == GirOp::Arr || inst.op == GirOp::Fill) &&
                    inst.ty >= 0 && inst.ty < (int)m.types.size() &&
                    GirOwnerKind(m.Type(inst.ty).kind))
                    Fail("GIR-V060", cat(fn.label, ": a nonfixed array is materialized as a detached aggregate"));
                if (inst.op != GirOp::DestOpen) continue;
                if (inst.idx < 0 || inst.idx >= (int)f.slots.size() ||
                    inst.ty != f.slots[inst.idx].ty || !inst.knownCount)
                    Fail("GIR-V060", cat(fn.label, ": a destination does not name its exact receiver slot"));
                auto countValue = *inst.knownCount;
                auto countDef = countValue >= 0 && countValue < fn.nvalues ? definitions[countValue] : nullptr;
                if (!countDef || countDef->op != GirOp::Int)
                    Fail("GIR-V060", cat(fn.label, ": a destination count is not a constant"));
                int64_t count = -1;
                auto [countEnd, countError] = from_chars(countDef->text.data(),
                                                         countDef->text.data() + countDef->text.size(), count);
                if (countError != errc() || countEnd != countDef->text.data() + countDef->text.size() || count < 0)
                    Fail("GIR-V060", cat(fn.label, ": a destination count is invalid"));

                int writes = 0;
                int byteWrites = 0;
                size_t cursor = index + 1;
                for (; cursor < body.insts.size(); cursor++) {
                    auto &candidate = body.insts[cursor];
                    if (candidate.op == GirOp::DestWrite) {
                        if (byteWrites || candidate.a != inst.res)
                            Fail("GIR-V060", cat(fn.label, ": a destination mixes or misroutes element writes"));
                        writes++;
                        matched.insert({ (int)block, (int)cursor });
                        continue;
                    }
                    if (candidate.op == GirOp::DestBytes) {
                        if (byteWrites || writes || candidate.a != inst.res)
                            Fail("GIR-V060", cat(fn.label, ": a byte destination is mixed or misrouted"));
                        byteWrites++;
                        matched.insert({ (int)block, (int)cursor });
                        continue;
                    }
                    if (candidate.op == GirOp::DestFinish) {
                        if (candidate.a != inst.res) break;
                        matched.insert({ (int)block, (int)cursor });
                        break;
                    }
                    if (candidate.op != GirOp::Int && candidate.op != GirOp::Bool)
                        Fail("GIR-V060", cat(fn.label, ": a destination has an unsupported operation before completion"));
                }
                if (cursor + 1 >= body.insts.size() || body.insts[cursor].op != GirOp::DestFinish ||
                    body.insts[cursor].a != inst.res)
                    Fail("GIR-V060", cat(fn.label, ": a destination does not finish in its block"));
                auto &finish = body.insts[cursor];
                auto publishIndex = cursor + 1;
                auto &publish = body.insts[publishIndex];
                if (publish.op != GirOp::DestPublish || publish.a != finish.res)
                    Fail("GIR-V060", cat(fn.label, ": a destination is not published exactly after completion"));
                auto owner = m.Type(inst.ty);
                if (byteWrites) {
                    auto &write = body.insts[index + 1];
                    if ((uint64_t)count != write.bytes.size() || owner.kind != CoreType::Grow ||
                        m.Type(owner.elem).kind != CoreType::Int || m.Type(owner.elem).ity != CoreIntTy::U8)
                        Fail("GIR-V060", cat(fn.label, ": a byte destination count or element type is invalid"));
                } else if (count != writes) {
                    Fail("GIR-V060", cat(fn.label, ": an element destination count disagrees with its writes"));
                }
                expectedDestinationUses[inst.res] = writes + byteWrites + 1;
                matched.insert({ (int)block, (int)index });
                matched.insert({ (int)block, (int)publishIndex });
            }
        }
        for (size_t block = 0; block < f.blocks.size(); block++)
            for (size_t index = 0; index < f.blocks[block].insts.size(); index++) {
                auto &inst = f.blocks[block].insts[index];
                if ((inst.op == GirOp::DestOpen || inst.op == GirOp::DestWrite || inst.op == GirOp::DestBytes ||
                     inst.op == GirOp::DestFinish || inst.op == GirOp::DestPublish) &&
                    !matched.count({ (int)block, (int)index }))
                    Fail("GIR-V060", cat(fn.label, ": a construction operation is not part of a linear destination"));
            }
        for (int value = 0; value < fn.nvalues; value++) {
            auto type = fn.vt[value];
            if (type < 0 || type >= (int)m.types.size()) continue;
            auto kind = m.Type(type).kind;
            if (kind == CoreType::Dest) {
                if (!definitions[value] || definitions[value]->op != GirOp::DestOpen ||
                    expectedDestinationUses[value] < 1 || uses[value] != expectedDestinationUses[value])
                    Fail("GIR-V060", cat(fn.label, ": destination value %", value, " is not consumed linearly"));
            } else if (kind == CoreType::Built) {
                if (!definitions[value] || definitions[value]->op != GirOp::DestFinish || uses[value] != 1)
                    Fail("GIR-V060", cat(fn.label, ": completion value %", value, " is not published exactly once"));
            } else if (kind == CoreType::Cancelled) {
                Fail("GIR-V060", cat(fn.label, ": cancellation carrier %", value, " has no construction protocol"));
            }
        }
    }

    static vector<int> IncomingValues(const GirFunc &f, int target, size_t param) {
        vector<int> out;
        for (auto &block : f.blocks) {
            auto *term = LastTerm(block);
            if (!term) continue;
            if (term->op == GirOp::Br && term->idx == target && param < term->vals.size())
                out.push_back(term->vals[param]);
            else if (term->op == GirOp::CondBr) {
                if (term->idx == target && param < term->vals.size()) out.push_back(term->vals[param]);
                if (term->idx2 == target && param < term->vals2.size()) out.push_back(term->vals2[param]);
            }
        }
        return out;
    }

    vector<char> FreshOwnerRuns(const Fn &fn) const {
        const auto &f = *fn.f;
        vector<char> fresh(fn.nvalues, 0);
        for (auto &block : f.blocks)
            for (auto &inst : block.insts)
                if (inst.op == GirOp::Arr && inst.res >= 0 && inst.res < fn.nvalues &&
                    inst.ty >= 0 && inst.ty < (int)m.types.size() &&
                    (m.Type(inst.ty).kind == CoreType::Grow ||
                     m.Type(inst.ty).kind == CoreType::GrowShrink) &&
                    fn.vt[inst.res] == inst.ty)
                    fresh[inst.res] = 1;

        bool changed = true;
        for (size_t rounds = 0; changed && rounds <= (size_t)fn.nvalues; rounds++) {
            changed = false;
            for (size_t target = 0; target < f.blocks.size(); target++)
                for (size_t param = 0; param < f.blocks[target].params.size(); param++) {
                    auto value = f.blocks[target].params[param].first;
                    if (value < 0 || value >= fn.nvalues || fresh[value]) continue;
                    auto incoming = IncomingValues(f, (int)target, param);
                    if (!incoming.empty() && all_of(incoming.begin(), incoming.end(), [&](int source) {
                            return source >= 0 && source < fn.nvalues && fresh[source];
                        })) {
                        fresh[value] = 1;
                        changed = true;
                    }
                }
        }
        return fresh;
    }

    static bool RootsOverlap(const Roots &a, const Roots &b) {
        if (a.empty() || b.empty()) return true;
        for (auto &x : a)
            for (auto &y : b) {
                if (x.kind == CoreRootRef::Param || y.kind == CoreRootRef::Param) {
                    if (x.kind == CoreRootRef::Local || y.kind == CoreRootRef::Local) continue;
                    return true;
                }
                if (x.kind == y.kind && x.index == y.index) return true;
            }
        return false;
    }

    optional<Roots> CallDependencies(const Fn &fn, const Prov &p, const GirInst &call) const {
        if (call.idx < 0 || call.idx >= (int)m.funcs.size()) return nullopt;
        const auto &callee = m.funcs[call.idx];
        if (callee.summary.unknown) return nullopt;
        Roots out;
        for (auto arg : call.vals) {
            if (!ValRefLike(fn, arg)) continue;
            auto actual = RootsAt(p.vals, arg);
            if (actual.empty()) return nullopt;
            AddRoots(out, actual);
        }
        auto add = [&](const vector<CoreTarget> &targets) {
            for (auto &target : targets) {
                if (target.global) {
                    AddRoot(out, { CoreRootRef::Global, target.index });
                    continue;
                }
                if (target.index < 0 || target.index >= (int)call.vals.size()) return false;
                auto actual = RootsAt(p.vals, call.vals[target.index]);
                if (actual.empty()) return false;
                AddRoots(out, actual);
                if (target.index < (int)callee.params.size())
                    if (auto annotated = ParamRoots(callee, target.index))
                        for (auto &root : *annotated)
                            if (root.kind == CoreRootRef::Global) AddRoot(out, root);
            }
            return true;
        };
        for (auto *targets : { &callee.summary.reads, &callee.summary.writes, &callee.summary.grows,
                               &callee.summary.shrinks, &callee.summary.rebinds })
            if (!add(*targets)) return nullopt;
        return out;
    }

    vector<int> KillEmptyFacts(const vector<int> &facts, const Roots &roots, const Prov &p) const {
        if (roots.empty()) return {};
        vector<int> kept;
        for (auto fact : facts)
            if (!RootsOverlap(roots, RootsAt(p.vals, fact))) kept.push_back(fact);
        return kept;
    }

    // Source values can read or expose a cleared receiver even when the
    // instruction's destination belongs to another root. Keep mutation targets
    // out of this list; their receiver effects are handled separately.
    vector<int> EmptyFactSourceOperands(const GirInst &inst) const {
        vector<int> out;
        if (inst.op == GirOp::Call || inst.op == GirOp::Clear || GirIsTerminator(inst.op) ||
            GirLowOnly(inst.op))
            return out;
        Uses(inst, out);
        switch (inst.op) {
            case GirOp::Push: case GirOp::Pop: case GirOp::Store: case GirOp::Append: case GirOp::PopN:
            case GirOp::Resize: case GirOp::Replace:
                if (!out.empty()) out.erase(out.begin());
                break;
            default:
                break;
        }
        return out;
    }

    vector<int> TransferEmptyInst(const Fn &fn, const Prov &p, vector<int> facts,
                                  const GirInst &inst) const {
        auto contains = [&](int value) { return find(facts.begin(), facts.end(), value) != facts.end(); };
        if (inst.op == GirOp::Clear) {
            if (!contains(inst.a)) facts.push_back(inst.a);
            return facts;
        }
        if (inst.op == GirOp::Call) {
            auto dependencies = CallDependencies(fn, p, inst);
            if (!dependencies) return {};
            if (!dependencies->empty()) facts = KillEmptyFacts(facts, *dependencies, p);
        } else {
            Roots operands;
            bool checksOperands = false;
            switch (inst.op) {
                case GirOp::Load: case GirOp::Snap: case GirOp::ArrayLen: case GirOp::SliceView:
                case GirOp::ViewLen: case GirOp::ViewSlice: case GirOp::Index:
                case GirOp::IndexProven: case GirOp::Push:
                case GirOp::Pop: case GirOp::PopN: case GirOp::Resize: case GirOp::Store:
                case GirOp::Append: case GirOp::Replace:
                    operands = RootsAt(p.vals, inst.a);
                    checksOperands = true;
                    break;
                default:
                    break;
            }
            if (checksOperands) facts = KillEmptyFacts(facts, operands, p);
        }
        for (auto value : EmptyFactSourceOperands(inst))
            if (ValRefLike(fn, value)) facts = KillEmptyFacts(facts, RootsAt(p.vals, value), p);
        if (GirDefinesValue(inst) && ValRefLike(fn, inst.res))
            facts = KillEmptyFacts(facts, RootsAt(p.vals, inst.res), p);
        return facts;
    }

    vector<int> TransferEmptyBlock(const Fn &fn, const Prov &p, vector<int> facts,
                                   const GirBlock &block) const {
        for (auto &inst : block.insts) facts = TransferEmptyInst(fn, p, std::move(facts), inst);
        return facts;
    }

    vector<int> TransferEmptyEdge(const GirFunc &f, const vector<int> &facts,
                                  int target, const vector<int> &args) const {
        auto translated = facts;
        auto contains = [&](int value) {
            return find(translated.begin(), translated.end(), value) != translated.end();
        };
        if (target < 0 || target >= (int)f.blocks.size()) return translated;
        auto &params = f.blocks[target].params;
        for (size_t i = 0; i < params.size() && i < args.size(); i++)
            if (contains(args[i]) && find(translated.begin(), translated.end(), params[i].first) == translated.end())
                translated.push_back(params[i].first);
        return translated;
    }

    vector<optional<vector<int>>> EmptyFactsAtBlocks(const Fn &fn, const Prov &p) const {
        const auto &f = *fn.f;
        vector<optional<vector<int>>> states(f.blocks.size());
        if (!states.empty()) states[0] = vector<int> {};
        bool changed = true;
        for (size_t rounds = 0; changed && rounds <= (f.blocks.size() + 1) * (fn.nvalues + 1); rounds++) {
            changed = false;
            auto old = states;
            for (size_t b = 0; b < f.blocks.size(); b++) {
                if (!old[b]) continue;
                auto outgoing = TransferEmptyBlock(fn, p, *old[b], f.blocks[b]);
                auto *term = LastTerm(f.blocks[b]);
                if (!term) continue;
                auto propagate = [&](int target, const vector<int> &args) {
                    if (target < 0 || target >= (int)states.size()) return;
                    auto edgeFacts = TransferEmptyEdge(f, outgoing, target, args);
                    if (!states[target]) {
                        states[target] = std::move(edgeFacts);
                        changed = true;
                    } else {
                        vector<int> intersection;
                        for (auto fact : *states[target])
                            if (find(edgeFacts.begin(), edgeFacts.end(), fact) != edgeFacts.end())
                                intersection.push_back(fact);
                        if (intersection != *states[target]) {
                            states[target] = std::move(intersection);
                            changed = true;
                        }
                    }
                };
                if (term->op == GirOp::Br) propagate(term->idx, term->vals);
                else if (term->op == GirOp::CondBr) {
                    propagate(term->idx, term->vals);
                    propagate(term->idx2, term->vals2);
                }
            }
        }
        return states;
    }

    void CheckShrinkReplace(const Fn &fn, const vector<Roots> &resultRoots) {
        const auto &f = *fn.f;
        auto provenance = Provenance(resultRoots, fn);
        auto fresh = FreshOwnerRuns(fn);
        auto states = EmptyFactsAtBlocks(fn, provenance);
        for (size_t b = 0; b < f.blocks.size(); b++) {
            if (!states[b]) Fail("GIR-V060", cat(fn.label, ": no clear-state proof for block ", b));
            auto facts = *states[b];
            for (auto &inst : f.blocks[b].insts) {
                if (inst.op == GirOp::Replace) {
                    auto &ref = m.Type(fn.vt[inst.a]);
                    auto ownerTy = ref.kind == CoreType::Ref ? ref.elem : -1;
                    if (ownerTy < 0 || (m.Type(ownerTy).kind != CoreType::Grow &&
                                        m.Type(ownerTy).kind != CoreType::GrowShrink))
                        Fail("GIR-V060", cat(fn.label, ": whole replacement owner is not grow or growshrink"));
                    if (inst.b < 0 || inst.b >= fn.nvalues || !fresh[inst.b])
                        Fail("GIR-V060", cat(fn.label, ": whole replacement run is not a fresh literal run"));
                    if (find(facts.begin(), facts.end(), inst.a) == facts.end())
                        Fail("GIR-V060", cat(fn.label, ": whole replacement owner was not cleared on every path"));
                }
                facts = TransferEmptyInst(fn, provenance, std::move(facts), inst);
            }
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
