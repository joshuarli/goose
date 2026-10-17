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
    vector<vector<int>> lowPassedPairs, lowStackParams;
    vector<vector<pair<int, int>>> lowMarkParams;
    vector<bool> lowReturnedOwnerPairs;
    vector<set<int>> constructionNeeds, constructionEscapes;
    set<pair<int, int>> checkedTargetUnreachable;
    struct LowReturnFlagEffect {
        set<int64_t> values;
        bool preservesInput = false;
        bool operator==(const LowReturnFlagEffect &) const = default;
    };
    vector<LowReturnFlagEffect> lowReturnFlagEffects;

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
            case GirOp::Bytes: case GirOp::StaticBytes: case GirOp::ReturnFlagGet:
            case GirOp::TargetLoad: case GirOp::TraceId: case GirOp::SourceParam: case GirOp::SourceEnter: case GirOp::SourceGlobal: case GirOp::SourceTargetEnter: case GirOp::DestNamed:
            case GirOp::ResultExitDest: case GirOp::TargetDest:
                break;
            case GirOp::Abort:
                for (auto v : i.vals) add(v);
                break;
            case GirOp::Bin: case GirOp::Cmp: case GirOp::BoolCmp: case GirOp::Elem:
            case GirOp::Index: case GirOp::IndexProven: case GirOp::Push: case GirOp::Store: case GirOp::Append:
            case GirOp::PopN: case GirOp::Replace:
            case GirOp::Format: case GirOp::OutBytes: case GirOp::AppendValue:
            case GirOp::PtrEq: case GirOp::SourceChild: case GirOp::SourceCopy: case GirOp::DestAttach: case GirOp::DestText: case GirOp::DestCopy: case GirOp::DestRepeat: case GirOp::DestSnapshot:
                add(i.a); add(i.b);
                break;
            case GirOp::SourceNew:
                add(i.a); for (auto path : i.vals) add(path); break;
            case GirOp::SourceCallPush:
                for (auto source : i.vals) if (source >= 0) add(source); break;
            case GirOp::Resize:
                add(i.a); add(i.b);
                for (auto v : i.vals) add(v);
                break;
            case GirOp::Un: case GirOp::Not: case GirOp::Conv: case GirOp::Next: case GirOp::Freeze:
            case GirOp::Load: case GirOp::Snap: case GirOp::SliceView: case GirOp::ViewLen: case GirOp::Field:
            case GirOp::ArrayLen: case GirOp::Fill: case GirOp::Init: case GirOp::Exit: case GirOp::Render:
                add(i.a);
                break;
            case GirOp::DestBytes: case GirOp::DestFinish: case GirOp::DestPublish:
            case GirOp::Result: case GirOp::DestChild: case GirOp::DestArg:
            case GirOp::DestAbandon: case GirOp::DestValue: case GirOp::DestRelocate: case GirOp::DestAdapt: case GirOp::DestAdaptFinish:
            case GirOp::DestStage: case GirOp::DestFit: case GirOp::DestBind:
            case GirOp::DestCancel: case GirOp::ReturnFlagSet: case GirOp::TargetStore:
            case GirOp::DestAbandonNamed: case GirOp::SourceCallGet: case GirOp::SourceLeave: case GirOp::SourceCallPop: case GirOp::SourceResult: case GirOp::SourceGlobalSet: case GirOp::SourceTargetLeave: case GirOp::SourceTargetResult: case GirOp::SourceTargetGet: case GirOp::DestPublishRef:
                add(i.a);
                break;
            case GirOp::DestWrite:
                add(i.a); add(i.b);
                break;
            case GirOp::DestOpen:
                if (i.knownCount) add(*i.knownCount);
                if (auto whole = get_if<GirDestWholeReceiver>(&i.destReceiver)) add(whole->reference);
                if (auto push = get_if<GirDestPushReceiver>(&i.destReceiver)) add(push->reference);
                if (auto append = get_if<GirDestAppendReceiver>(&i.destReceiver)) add(append->reference);
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
            case GirOp::Event:
                for (auto v : i.vals) add(v);
                break;
            case GirOp::CallConstruct: case GirOp::Invoke: case GirOp::Escape:
                for (auto v : i.vals) add(v);
                for (auto v : i.vals2) add(v);
                for (auto v : i.forwarded) add(v);
                for (auto &edge : i.escapes) for (auto v : edge.forwarded) add(v);
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
            case GirOp::DestOpen: case GirOp::DestWrite: case GirOp::DestFinish: case GirOp::DestPublish: case GirOp::DestBytes:
            case GirOp::OutBytes: case GirOp::DestChild: case GirOp::Render: case GirOp::DestPublishRef: case GirOp::DestAdapt: case GirOp::DestAdaptFinish:
            case GirOp::DestNamed: case GirOp::ResultExitDest: case GirOp::DestAbandonNamed:
            case GirOp::DestArg: case GirOp::DestAbandon: case GirOp::DestValue:
            case GirOp::DestRelocate: case GirOp::DestStage: case GirOp::DestFit:
            case GirOp::CallConstruct: case GirOp::TargetDest: case GirOp::DestAttach:
            case GirOp::DestText: case GirOp::DestCopy: case GirOp::DestRepeat: case GirOp::DestSnapshot: case GirOp::DestBind:
            case GirOp::DestCancel: case GirOp::Invoke: case GirOp::Escape:
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
        if (i.op == GirOp::Invoke) {
            vector<int> out { i.a };
            for (auto &edge : i.escapes) out.push_back(edge.block);
            return out;
        }
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
        for (auto &function : m.funcs)
            if (function.lowResults && (!m.low || !CoreHasConstruction(m.profile)))
                Fail("GIR-V090", "result channel descriptors appear outside construction GIR-L");
        CheckEntryAndGlobals();
        for (auto &f : m.funcs) sigs.push_back({ f.params, f.results });
        for (auto &f : m.funcs) fns.push_back({ cat("function ", f.name), &f, false, {}, 0 });
        for (auto &g : m.globals)
            fns.push_back({ cat("initializer of global ", g.name), &g.init, true, {}, 0 });
        for (auto &fn : fns) CheckSymbols(fn);
        for (auto &fn : fns) ValueTypes(fn);
        for (auto &fn : fns) CheckTypes(fn);
        for (auto &fn : fns) CheckCfg(fn);
        if (m.low && CoreHasConstruction(m.profile)) { CheckLowResultTables(); CheckLowTargetProtocols(); }
        CheckUnreachable();
        if (m.low) {
            lowPassedPairs.assign(m.funcs.size(), {});
            lowStackParams.assign(m.funcs.size(), {});
            lowMarkParams.assign(m.funcs.size(), {});
            lowReturnedOwnerPairs.assign(m.funcs.size(), false);
            if (CoreHasConstruction(m.profile))
                for (size_t function = 0; function < m.funcs.size(); function++)
                    for (auto &result : *m.funcs[function].lowResults)
                        if (auto nonfixed = get_if<GirLowNonfixedResult>(&result.layout)) {
                            lowStackParams[function].push_back(nonfixed->stack);
                            lowMarkParams[function].push_back({ nonfixed->start, nonfixed->stack });
                        }
            bool changed = true;
            int rounds = 0;
            while (changed && rounds++ < (int)m.funcs.size() * 4 + 8) {
                auto channelChanged = CoreHasConstruction(m.profile) && ComputePassedStackChannels();
                auto passed = ComputePassedOwnerPairs(lowReturnedOwnerPairs);
                auto returned = ComputeReturnedOwnerPairs(passed, lowReturnedOwnerPairs);
                changed = channelChanged || passed != lowPassedPairs || returned != lowReturnedOwnerPairs;
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
        if (CoreHasConstruction(m.profile)) CheckConstructionTargets();
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
            if (hasStructType || hasStructInst || !m.structs.empty() || !m.targets.empty() ||
                (!CoreHasConstruction(m.profile) && !m.lowtargets.empty()))
                Fail("GIR-V090", "a low module retains a high-stage artifact or an unsupported target table");
            CheckLowTargetTables();
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
                auto &protocols = m.funcs[target.members[0]].resultProtocols;
                for (auto member : target.members)
                    {
                        auto &candidate = m.funcs[member];
                        bool same = candidate.results == results && candidate.resultProtocols.size() == protocols.size();
                        if (same) for (size_t result = 0; result < protocols.size(); result++)
                            same &= candidate.resultProtocols[result].request == protocols[result].request;
                        if (!same) Fail("GIR-V010", "construction target members have different result types or requests");
                    }
            }
        }
        if (m.profile == CoreProfile::Pilot) {
            if (hasStructType || hasStructInst || !m.structs.empty())
                Fail("GIR-V010", "core-pilot has no struct table or struct operations");
            return;
        }

        vector<int> typeForStruct(m.structs.size(), -1);
        if (CoreHasConstruction(m.profile))
            for (auto &descriptor : m.structs)
                if (descriptor.displayName.empty() || !CoreIsUtf8(descriptor.displayName))
                    Fail("GIR-V010", "construction struct display name is empty or not UTF-8");
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

    void CheckLowTargetTables() {
        auto bad = [&](const string &message) { Fail("GIR-V090", message); };
        set<vector<int>> sets;
        for (size_t target = 0; target < m.lowtargets.size(); target++) {
            auto &table = m.lowtargets[target];
            if (table.members.empty() || !is_sorted(table.members.begin(), table.members.end()) ||
                adjacent_find(table.members.begin(), table.members.end()) != table.members.end() || !sets.insert(table.members).second)
                bad("low target member set is empty, repeated, or unsorted");
            for (size_t channel = 0; channel < table.channels.size(); channel++)
                if (table.channels[channel].position != (int)channel) bad("low target result positions are not dense and ordered");
            for (auto member : table.members) if (member < 0 || member >= (int)m.funcs.size()) bad("low target member lies outside the function table");
            if (table.cells.empty() || table.cells[0] < 0 || table.cells[0] >= (int)m.types.size() || m.Type(table.cells[0]).kind != CoreType::Bool)
                bad("low target active cell is not boolean");
            vector<bool> covered(table.cells.size(), false);
            covered[0] = true;
            for (auto &channel : table.channels) {
                if (channel.incoming.empty() || channel.escaped.empty() || channel.incoming.size() != channel.escaped.size())
                    bad("low target channel omits incoming or escaped ABI words");
                for (auto *cells : { &channel.incoming, &channel.escaped })
                    for (auto cell : *cells) {
                        if (cell <= 0 || cell >= (int)table.cells.size() || covered[cell]) bad("low target channels do not partition their cells");
                        covered[cell] = true;
                        auto type = table.cells[cell];
                        if (type < 0 || type >= (int)m.types.size()) bad("low target cell type lies outside the type table");
                        auto kind = m.Type(type).kind;
                        if (kind != CoreType::Int && kind != CoreType::Bool && kind != CoreType::Ptr) bad("low target cell retains an unresolved layout");
                        if (cells == &channel.incoming && kind != CoreType::Ptr) bad("low target incoming output channel is not an address");
                    }
                if (channel.incoming.size() == 3 &&
                    (m.Type(table.cells[channel.escaped[0]]).kind != CoreType::Ptr ||
                     m.Type(table.cells[channel.escaped[1]]).kind != CoreType::Ptr ||
                     m.Type(table.cells[channel.escaped[2]]).kind != CoreType::Int ||
                     m.Type(table.cells[channel.escaped[2]]).ity != CoreIntTy::I64))
                    bad("low target construction payload is not start, end, and count");
            }
            if (find(covered.begin(), covered.end(), false) != covered.end()) bad("low target table has an unconsumed cell");
            for (auto member : table.members) {
                auto &function = m.funcs[member];
                if (function.blocks.empty()) bad("low target member has no entry block");
                const GirInst *enter = nullptr;
                for (auto &block : function.blocks) for (auto &inst : block.insts)
                    if (inst.op == GirOp::SourceTargetEnter && inst.idx == (int)target) {
                        if (enter || &block != &function.blocks[0]) bad("low target member does not have one entry activation");
                        enter = &inst;
                    }
                if (!enter || enter->vals.size() != table.channels.size()) bad("low target member does not consume every declared channel");
                auto &entry = function.blocks[0].insts;
                auto enterPosition = find_if(entry.begin(), entry.end(), [&](const GirInst &inst) { return &inst == enter; });
                if (enterPosition == entry.end()) bad("low target activation is not in its entry block");
                int activeStores = 0;
                for (auto inst = entry.begin(); inst != enterPosition; ++inst) if (inst->op == GirOp::TargetStore && inst->idx == (int)target && inst->idx2 == 0) {
                    bool active = false;
                    for (auto &definition : entry)
                        if (definition.res == inst->a && definition.op == GirOp::Bool && definition.flag) active = true;
                    if (!active) bad("low target activation does not set its active cell");
                    activeStores++;
                }
                if (activeStores != 1) bad("low target activation does not set its active cell exactly once");
                vector<int> parameters;
                for (auto &channel : table.channels) for (auto cell : channel.incoming) {
                    int parameter = -1;
                    for (auto &inst : function.blocks[0].insts)
                        if (&inst == enter) break;
                        else if (inst.op == GirOp::TargetStore && inst.idx == (int)target && inst.idx2 == cell)
                            for (size_t position = 1; position < function.blocks[0].params.size(); position++)
                                if (function.blocks[0].params[position].first == inst.a) parameter = (int)position;
                    if (parameter < 1 || m.Type(function.params[parameter]).kind != CoreType::Ptr) bad("low target incoming cell is not installed from an output parameter");
                    parameters.push_back(parameter);
                }
                for (size_t position = 1; position < parameters.size(); position++)
                    if (parameters[position] != parameters[position - 1] + 1) bad("low target primitive output positions are not consecutive");
                size_t offset = 0;
                for (size_t channel = 0; channel < table.channels.size(); channel++) {
                    if (enter->vals[channel] >= 0 && enter->vals[channel] != parameters[offset]) bad("low target reference shadow names another output channel");
                    offset += table.channels[channel].incoming.size();
                }
            }
        }
    }

    template<class Integer>
    vector<LowReturnFlagEffect> ComputeLowReturnFlagEffects(Integer integer) const {
        struct Flow {
            set<int64_t> values;
            bool preservesInput = false;
            bool reachable = false;
            bool operator==(const Flow &) const = default;
        };
        vector<LowReturnFlagEffect> effects(m.funcs.size());
        bool changed = true;
        while (changed) {
            auto nextEffects = effects;
            for (size_t function = 0; function < m.funcs.size(); function++) {
                auto &f = m.funcs[function];
                vector<optional<Flow>> incoming(f.blocks.size());
                if (f.blocks.empty()) continue;
                incoming[0] = Flow { {}, true, true };
                vector<int> work { 0 };
                auto merge = [&](int block, Flow state) {
                    if (!state.reachable) return;
                    if (!incoming[block]) {
                        incoming[block] = std::move(state);
                        work.push_back(block);
                        return;
                    }
                    auto merged = *incoming[block];
                    merged.reachable = true;
                    merged.preservesInput |= state.preservesInput;
                    merged.values.insert(state.values.begin(), state.values.end());
                    if (!(merged == *incoming[block])) {
                        incoming[block] = std::move(merged);
                        work.push_back(block);
                    }
                };
                while (!work.empty()) {
                    auto block = work.back();
                    work.pop_back();
                    auto state = *incoming[block];
                    for (auto &inst : f.blocks[block].insts) {
                        if (inst.op == GirOp::ReturnFlagSet) {
                            state.values = { integer(f, inst.a) };
                            state.preservesInput = false;
                        } else if (inst.op == GirOp::Call) {
                            auto &callee = effects[inst.idx];
                            if (callee.values.empty() && !callee.preservesInput) {
                                state.reachable = false;
                            } else {
                                auto values = callee.values;
                                if (callee.preservesInput)
                                    values.insert(state.values.begin(), state.values.end());
                                state.values = std::move(values);
                                state.preservesInput &= callee.preservesInput;
                                state.reachable = !state.values.empty() || state.preservesInput;
                            }
                        } else if (inst.op == GirOp::Ret) {
                            nextEffects[function].values.insert(state.values.begin(), state.values.end());
                            nextEffects[function].preservesInput |= state.preservesInput;
                            break;
                        } else if (inst.op == GirOp::Abort || inst.op == GirOp::Exit || inst.op == GirOp::Unreachable) {
                            state.reachable = false;
                        }
                        if (!state.reachable) break;
                    }
                    if (!state.reachable) continue;
                    auto *term = LastTerm(f.blocks[block]);
                    if (!term) continue;
                    if (term->op == GirOp::Br) merge(term->idx, state);
                    if (term->op == GirOp::CondBr) {
                        merge(term->idx, state);
                        merge(term->idx2, state);
                    }
                }
            }
            changed = nextEffects != effects;
            effects = std::move(nextEffects);
        }
        return effects;
    }

    struct LowResultWord {
        int parameter;
        GirTypeId type;
        int64_t bytes;
        bool operator==(const LowResultWord &) const = default;
    };

    vector<LowResultWord> LowResultWords(const GirLowResult &result) const {
        auto primitive = [&](CoreType::Kind kind) {
            for (size_t type = 0; type < m.types.size(); type++)
                if (m.types[type].kind == kind && (kind != CoreType::Int || m.types[type].ity == CoreIntTy::I64)) return (int)type;
            return -1;
        };
        auto pointer = primitive(CoreType::Ptr), integer = primitive(CoreType::Int);
        if (auto scalar = get_if<GirLowScalarResult>(&result.layout))
            return { { scalar->output, scalar->type, scalar->type >= 0 && scalar->type < (int)m.types.size() ? FlatSize(scalar->type) : 0 } };
        if (auto snapshot = get_if<GirLowSnapshotResult>(&result.layout)) return { { snapshot->output, pointer, snapshot->bytes } };
        if (auto reference = get_if<GirLowReferenceResult>(&result.layout)) return { { reference->output, pointer, m.pointerBytes } };
        if (auto reference = get_if<GirLowResizableReferenceResult>(&result.layout))
            return { { reference->header, pointer, m.pointerBytes }, { reference->stack, pointer, m.pointerBytes } };
        if (auto slice = get_if<GirLowSliceResult>(&result.layout))
            return { { slice->data, pointer, m.pointerBytes }, { slice->count, integer, 8 } };
        auto &nonfixed = get<GirLowNonfixedResult>(result.layout);
        return { { nonfixed.stack, pointer, 0 }, { nonfixed.start, pointer, 0 }, { nonfixed.count, integer, 8 } };
    }

    void CheckLowResultTables() {
        auto bad = [&](const string &message) { Fail("GIR-V090", message); };
        map<int, pair<size_t, int64_t>> sourceLayouts;
        for (auto &function : m.funcs) {
            if (!function.lowResults) bad("construction function omits its result channel descriptors");
            set<int> parameters;
            int previousParameter = -1;
            for (auto &result : *function.lowResults) {
                if (result.sourceType < 0) bad("low result source identity is negative");
                int64_t detail = 0;
                if (auto scalar = get_if<GirLowScalarResult>(&result.layout)) detail = scalar->type;
                if (auto snapshot = get_if<GirLowSnapshotResult>(&result.layout)) detail = snapshot->bytes;
                auto shape = make_pair(result.layout.index(), detail);
                auto previous = sourceLayouts.emplace(result.sourceType, shape);
                if (!previous.second && previous.first->second != shape) bad("one low result source identity has contradictory physical layouts");
                if (auto nonfixed = get_if<GirLowNonfixedResult>(&result.layout))
                    if (nonfixed->request != CoreRequest::Value && nonfixed->request != CoreRequest::ElementRun)
                        bad("nonfixed low result has no construction request");
                for (auto &word : LowResultWords(result)) {
                    if (word.parameter <= 0 || word.parameter >= (int)function.params.size() ||
                        m.Type(function.params[word.parameter]).kind != CoreType::Ptr || !parameters.insert(word.parameter).second)
                        bad("low result descriptors do not name distinct primitive output parameters");
                    if (previousParameter >= 0 && word.parameter != previousParameter + 1)
                        bad("low result outputs do not follow result and word order");
                    previousParameter = word.parameter;
                    if (word.type < 0 || word.type >= (int)m.types.size() || word.bytes < 0)
                        bad("low result descriptor has an invalid primitive layout");
                }
                if (auto scalar = get_if<GirLowScalarResult>(&result.layout))
                    if (m.Type(scalar->type).kind != CoreType::Int && m.Type(scalar->type).kind != CoreType::Bool)
                        bad("scalar low result does not name an integer or boolean");
                if (auto snapshot = get_if<GirLowSnapshotResult>(&result.layout))
                    if (snapshot->bytes <= 0) bad("snapshot low result has no byte extent");
            }
            if (!parameters.empty()) {
                auto first = *parameters.begin();
                if ((int)parameters.size() != (int)function.params.size() - first)
                    bad("low result outputs are not a dense signature suffix");
            }
        }
        for (auto &target : m.lowtargets) for (auto member : target.members) {
            auto &function = m.funcs[member];
            if (function.lowResults->size() != target.channels.size()) bad("low target channel count disagrees with its member result ABI");
            for (size_t result = 0; result < target.channels.size(); result++) {
                auto &canonical = (*m.funcs[target.members[0]].lowResults)[result];
                auto &actual = (*function.lowResults)[result];
                if (canonical.layout.index() != actual.layout.index() || canonical.sourceType != actual.sourceType) bad("low target member result descriptor kinds disagree");
                if (auto scalar = get_if<GirLowScalarResult>(&canonical.layout))
                    if (scalar->type != get<GirLowScalarResult>(actual.layout).type) bad("low target scalar result types disagree");
                if (auto snapshot = get_if<GirLowSnapshotResult>(&canonical.layout))
                    if (snapshot->bytes != get<GirLowSnapshotResult>(actual.layout).bytes) bad("low target snapshot extents disagree");
                if (auto nonfixed = get_if<GirLowNonfixedResult>(&canonical.layout))
                    if (nonfixed->request != get<GirLowNonfixedResult>(actual.layout).request) bad("low target construction requests disagree");
                auto &channel = target.channels[result];
                auto words = LowResultWords((*function.lowResults)[result]);
                if (words.size() != channel.incoming.size()) bad("low target incoming words disagree with its member result ABI");
                bool nonfixed = holds_alternative<GirLowNonfixedResult>((*function.lowResults)[result].layout);
                if (nonfixed != (channel.incoming.size() == 3)) bad("low target result kind disagrees with its member result ABI");
                for (size_t word = 0; word < words.size(); word++) {
                    auto expected = nonfixed && word < 2 ? m.Type(target.cells[channel.escaped[word]]).kind == CoreType::Ptr :
                        target.cells[channel.escaped[word]] == words[word].type;
                    if (!expected) bad("low target escaped word disagrees with its member result ABI");
                    bool installed = false;
                    auto parameter = function.blocks[0].params[words[word].parameter].first;
                    for (auto &inst : function.blocks[0].insts)
                        installed |= inst.op == GirOp::TargetStore && inst.idx == (int)(&target - m.lowtargets.data()) &&
                            inst.idx2 == channel.incoming[word] && inst.a == parameter;
                    if (!installed) bad("low target incoming cell does not install its declared result parameter");
                }
            }
        }
    }

    void CheckLowTargetProtocols() {
        auto bad = [&](const string &message) { Fail("GIR-V090", message); };
        vector<set<int>> needs(m.funcs.size()), escapes(m.funcs.size());
        vector<set<int64_t>> returnFlags(m.funcs.size());
        auto member = [&](size_t function, int target) {
            auto &members = m.lowtargets[target].members;
            return find(members.begin(), members.end(), (int)function) != members.end();
        };
        auto integer = [&](const GirFunc &function, int value) -> int64_t {
            for (auto &block : function.blocks) for (auto &inst : block.insts) if (inst.res == value && inst.op == GirOp::Int) {
                int64_t result = -1;
                auto parsed = from_chars(inst.text.data(), inst.text.data() + inst.text.size(), result);
                if (parsed.ec == errc() && parsed.ptr == inst.text.data() + inst.text.size()) return result;
            }
            return -1;
        };
        for (size_t function = 0; function < m.funcs.size(); function++)
            for (auto &block : m.funcs[function].blocks) for (auto &inst : block.insts) {
                if (inst.op == GirOp::TargetLoad || inst.op == GirOp::TargetStore || inst.op == GirOp::SourceTargetResult) {
                    if (inst.idx < 0 || inst.idx >= (int)m.lowtargets.size()) bad("low target use is outside the table");
                    if (!member(function, inst.idx)) needs[function].insert(inst.idx);
                }
                if (inst.op == GirOp::ReturnFlagSet) {
                    auto flag = integer(m.funcs[function], inst.a);
                    if (flag < 0 || flag > (int64_t)m.lowtargets.size()) bad("return flag does not name a checked target");
                }
            }
        lowReturnFlagEffects = ComputeLowReturnFlagEffects(integer);
        for (size_t function = 0; function < m.funcs.size(); function++) {
            returnFlags[function] = lowReturnFlagEffects[function].values;
            for (auto flag : returnFlags[function]) if (flag) escapes[function].insert((int)flag - 1);
            if (lowReturnFlagEffects[function].preservesInput)
                for (size_t target = 0; target < m.lowtargets.size(); target++) escapes[function].insert((int)target);
        }
        for (bool changed = true; changed;) {
            changed = false;
            for (size_t function = 0; function < m.funcs.size(); function++)
                for (auto &block : m.funcs[function].blocks) for (auto &inst : block.insts) if (inst.op == GirOp::Call)
                    for (auto target : needs[inst.idx]) if (!member(function, target)) changed |= needs[function].insert(target).second;
        }
        if (!needs[m.entry].empty()) bad("low entry requires an unavailable target activation");
        for (auto initializer : m.initfuncs) if (!needs[initializer].empty()) bad("low global initializer requires an unavailable target activation");
        for (size_t functionIndex = 0; functionIndex < m.funcs.size(); functionIndex++) {
            auto &function = m.funcs[functionIndex];
            vector<vector<int>> predecessors(function.blocks.size());
            for (size_t block = 0; block < function.blocks.size(); block++) {
                auto *term = LastTerm(function.blocks[block]);
                if (!term) continue;
                for (auto successor : Successors(*term))
                    if (successor >= 0 && successor < (int)predecessors.size()) predecessors[successor].push_back((int)block);
            }
            auto comparedTag = [&](int value, int flag) -> optional<int64_t> {
                for (auto &block : function.blocks) for (auto &inst : block.insts)
                    if (inst.res == value && inst.op == GirOp::Cmp && inst.cmp == CoreCmpOp::Eq) {
                        if (inst.a == flag) return integer(function, inst.b);
                        if (inst.b == flag) return integer(function, inst.a);
                    }
                return nullopt;
            };
            auto singleBranchSentinel = [&](int start, int source) {
                set<int> seen;
                auto block = start;
                auto predecessor = source;
                while (block >= 0 && block < (int)function.blocks.size() && seen.insert(block).second &&
                    predecessors[block].size() == 1 && predecessors[block][0] == predecessor) {
                    auto &candidate = function.blocks[block];
                    auto *term = LastTerm(candidate);
                    if (term && term->op == GirOp::Unreachable && candidate.insts.size() == 1) return block;
                    if (!term || term->op != GirOp::Br) return -1;
                    predecessor = block;
                    block = term->idx;
                }
                return -1;
            };
            for (size_t block = 0; block < function.blocks.size(); block++) {
                auto &instructions = function.blocks[block].insts;
                for (size_t position = 0; position < instructions.size(); position++) {
                    auto &call = instructions[position];
                    if (call.op != GirOp::Call || escapes[call.idx].empty()) continue;
                    if (position + 1 >= instructions.size() || instructions[position + 1].op != GirOp::ReturnFlagGet)
                        bad("escaping low call does not read its return discriminant");
                    auto flag = instructions[position + 1].res;
                    auto *first = LastTerm(function.blocks[block]);
                    if (!first || first->op != GirOp::CondBr) bad("escaping low call has no zero discriminant branch");
                    auto zero = comparedTag(first->a, flag);
                    if (!zero || *zero != 0 || first->idx == first->idx2)
                        bad("escaping low call does not dispatch normal return exactly once");
                    auto normal = first->idx;
                    auto next = first->idx2;
                    auto sentinelPredecessor = (int)block;
                    set<int64_t> pending;
                    for (auto target : escapes[call.idx]) pending.insert((int64_t)target + 1);
                    set<int> handledBlocks;
                    while (!pending.empty()) {
                        if (next < 0 || next >= (int)function.blocks.size()) bad("escaping low call dispatch leaves the block table");
                        auto *term = LastTerm(function.blocks[next]);
                        if (!term || term->op != GirOp::CondBr) bad("escaping low call omits a handled target case");
                        auto tag = comparedTag(term->a, flag);
                        if (!tag || !pending.erase(*tag) || term->idx == term->idx2 || !handledBlocks.insert(term->idx).second)
                            bad("escaping low call has a duplicate or invalid handled target case");
                        auto target = (int)*tag - 1;
                        bool active = member(functionIndex, target) || needs[functionIndex].count(target);
                        if (!active) bad("escaping low call handles a target without an active receiving protocol");
                        auto &handler = function.blocks[term->idx];
                        bool readsTarget = false;
                        for (auto &inst : handler.insts)
                            readsTarget |= (inst.op == GirOp::TargetLoad || inst.op == GirOp::TargetStore ||
                                            inst.op == GirOp::SourceTargetGet || inst.op == GirOp::SourceTargetResult) && inst.idx == target;
                        if (!readsTarget) bad("escaping low call has a target case without a receiving handler");
                        for (auto &channel : m.lowtargets[target].channels) {
                            vector<int> required = channel.escaped;
                            if (channel.incoming.size() == 3) required = { channel.escaped[0], channel.escaped[2] };
                            for (auto cell : required) {
                                const GirInst *load = nullptr;
                                for (auto &inst : handler.insts)
                                    if (inst.op == GirOp::TargetLoad && inst.idx == target && inst.idx2 == cell) load = &inst;
                                if (!load) bad("target case omits an escaped result cell");
                            }
                            if (member(functionIndex, target)) {
                                bool reference = false;
                                for (auto targetMember : m.lowtargets[target].members)
                                    for (auto &entryBlock : m.funcs[targetMember].blocks)
                                        for (auto &inst : entryBlock.insts)
                                            if (inst.op == GirOp::SourceTargetEnter && inst.idx == target &&
                                                channel.position < (int)inst.vals.size() && inst.vals[channel.position] >= 0)
                                                reference = true;
                                if (reference) {
                                    bool source = false;
                                    for (auto &inst : handler.insts)
                                        source |= inst.op == GirOp::SourceTargetGet && inst.idx == channel.position;
                                    if (!source) bad("target case omits its reference result source");
                                }
                            }
                        }
                        sentinelPredecessor = next;
                        next = term->idx2;
                    }
                    if (next < 0 || next >= (int)function.blocks.size()) bad("escaping low call has no invalid-discriminant sentinel");
                    auto &sentinel = function.blocks[next];
                    auto *last = LastTerm(sentinel);
                    if (!last || last->op != GirOp::Unreachable || sentinel.insts.size() != 1 ||
                        predecessors[next].size() != 1 || predecessors[next][0] != sentinelPredecessor)
                        bad("escaping low call has no closed invalid-discriminant sentinel");
                    checkedTargetUnreachable.emplace((int)functionIndex, next);
                    if (!returnFlags[call.idx].count(0) && !lowReturnFlagEffects[call.idx].preservesInput) {
                        auto normalSentinel = singleBranchSentinel(normal, (int)block);
                        if (normalSentinel >= 0) checkedTargetUnreachable.emplace((int)functionIndex, normalSentinel);
                    }
                }
            }
            map<pair<int, int>, int> saved;
            for (size_t target = 0; target < m.lowtargets.size(); target++) if (member(functionIndex, (int)target)) {
                set<int> installed;
                for (auto &inst : function.blocks[0].insts) {
                    if (inst.op == GirOp::TargetLoad && inst.idx == (int)target && !installed.count(inst.idx2))
                        if (!saved.emplace(make_pair((int)target, inst.idx2), inst.res).second) bad("low target activation saves a cell twice");
                    if (inst.op == GirOp::TargetStore && inst.idx == (int)target) installed.insert(inst.idx2);
                    if (inst.op == GirOp::SourceTargetEnter && inst.idx == (int)target) break;
                }
                for (size_t cell = 0; cell < m.lowtargets[target].cells.size(); cell++)
                    if (!saved.count({ (int)target, (int)cell })) bad("low target activation does not save every recursive cell");
            }
            struct State {
                set<pair<int, int>> restored, payload;
                int flag = -1;
                bool operator==(const State &) const = default;
            };
            vector<optional<State>> incoming(function.blocks.size());
            incoming[0] = State {};
            vector<int> work { 0 };
            auto merge = [&](int block, State state) {
                if (!incoming[block]) { incoming[block] = std::move(state); work.push_back(block); return; }
                auto next = *incoming[block];
                if (next.flag != state.flag) next.flag = -1;
                for (auto *items : { &next.restored, &next.payload }) {
                    auto &other = items == &next.restored ? state.restored : state.payload;
                    for (auto iterator = items->begin(); iterator != items->end();) {
                        if (!other.count(*iterator)) iterator = items->erase(iterator); else ++iterator;
                    }
                }
                if (!(next == *incoming[block])) { incoming[block] = std::move(next); work.push_back(block); }
            };
            while (!work.empty()) {
                auto block = work.back(); work.pop_back();
                auto state = *incoming[block];
                for (size_t position = 0; position < function.blocks[block].insts.size(); position++) {
                    auto &inst = function.blocks[block].insts[position];
                    if (inst.op == GirOp::Call && !escapes[inst.idx].empty()) {
                        auto &instructions = function.blocks[block].insts;
                        if (position + 1 >= instructions.size() || instructions[position + 1].op != GirOp::ReturnFlagGet)
                            bad("escaping low call reads outputs before its return discriminant");
                    }
                    if (inst.op == GirOp::TargetStore) {
                        auto key = make_pair(inst.idx, inst.idx2);
                        auto previous = saved.find(key);
                        if (previous != saved.end() && previous->second == inst.a) state.restored.insert(key);
                        else {
                            bool incomingCell = inst.idx2 == 0;
                            for (auto &channel : m.lowtargets[inst.idx].channels)
                                incomingCell |= find(channel.incoming.begin(), channel.incoming.end(), inst.idx2) != channel.incoming.end();
                            if (incomingCell && block != 0) bad("low target incoming activation cell is overwritten outside its entry or restoration");
                            state.restored.erase(key);
                            if (!incomingCell) state.payload.insert(key);
                        }
                    }
                    if (inst.op == GirOp::Call) {
                        auto &effect = lowReturnFlagEffects[inst.idx];
                        if (effect.preservesInput && effect.values.empty()) continue;
                        if (!effect.preservesInput && effect.values.size() == 1) state.flag = (int)*effect.values.begin();
                        else state.flag = -1;
                    }
                    if (inst.op == GirOp::ReturnFlagSet) state.flag = (int)integer(function, inst.a);
                    if (inst.op == GirOp::Ret && !m.lowtargets.empty()) {
                        if (state.flag < 0) bad("low return omits its normal or target discriminant");
                        for (auto &[key, value] : saved) { (void)value; if (!state.restored.count(key)) bad("low return fails to restore a recursive target cell"); }
                        if (state.flag) {
                            auto target = state.flag - 1;
                            for (auto &channel : m.lowtargets[target].channels) for (auto cell : channel.escaped)
                                if (!state.payload.count({ target, cell })) bad("low target return omits an escaped payload cell");
                        }
                    }
                }
                auto *term = LastTerm(function.blocks[block]);
                if (term && term->op == GirOp::Br) merge(term->idx, state);
                if (term && term->op == GirOp::CondBr) { merge(term->idx, state); merge(term->idx2, state); }
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
                if (!GirNonfixed(m, type.elem) || !GirConstructible(m, type.elem) ||
                    (type.request != CoreRequest::Value && type.request != CoreRequest::ElementRun))
                    Fail("GIR-V010", cat("construction carrier type ", id, " has no constructible type/request"));
                continue;
            }
            if (m.low && type.kind != CoreType::Int && type.kind != CoreType::Bool &&
                type.kind != CoreType::Unit && type.kind != CoreType::Ptr)
                Fail("GIR-V090", "a low module retains a nonprimitive type");
            if (type.kind == CoreType::VarArr || type.kind == CoreType::Tuple) {
                if (!CoreHasConstruction(m.profile)) Fail("GIR-V010", "construction type under an earlier profile");
                if (type.kind == CoreType::VarArr) {
                    if (type.elem < 0 || type.elem >= (int)id || !GirConstructible(m, (int)id))
                        Fail("GIR-V010", "variable array has an invalid recursive element");
                } else {
                    if (type.parts.size() < 2) Fail("GIR-V010", "result pack has fewer than two components");
                    for (auto part : type.parts)
                        if (part < 0 || part >= (int)id || m.Type(part).kind == CoreType::Dest ||
                            m.Type(part).kind == CoreType::Cancelled || m.Type(part).kind == CoreType::Tuple)
                            Fail("GIR-V010", "result pack has an invalid component");
                }
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
                    auto constructionOp = (i.op >= GirOp::Bytes && i.op <= GirOp::DestAdaptFinish) ||
                                          (i.op >= GirOp::StaticBytes && i.op <= GirOp::SourceTargetGet) ||
                                          i.op == GirOp::AppendValue ||
                                          (i.op >= GirOp::DestWrite && i.op <= GirOp::DestCancel) ||
                                          (i.op >= GirOp::ReturnFlagSet && i.op <= GirOp::SourceTargetResult) ||
                                          i.op == GirOp::Invoke || i.op == GirOp::Escape;
                    if (constructionOp && !CoreHasConstruction(m.profile))
                        Fail("GIR-V010", cat("function ", fn.name,
                                             " uses a construction operation under an earlier profile"));
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

        if (CoreHasConstruction(m.profile))
            for (size_t function = 0; function < m.funcs.size(); function++) if (&m.funcs[function] == &f) {
                for (auto position : lowStackParams[function])
                    facts.stack[entry.params[position].first] = { 3, position };
                for (auto [mark, stack] : lowMarkParams[function])
                    facts.markof[entry.params[mark].first] = { 3, stack };
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
                        case GirOp::TargetLoad: {
                            if (i.idx < 0 || i.idx >= (int)m.lowtargets.size()) break;
                            for (size_t channel = 0; channel < m.lowtargets[i.idx].channels.size(); channel++) {
                                auto &cells = m.lowtargets[i.idx].channels[channel];
                                if (cells.incoming.size() != 3) continue;
                                StackId token { 7, i.idx * 65536 + (int)channel };
                                for (auto &entryInst : f.blocks[0].insts)
                                    if (entryInst.op == GirOp::TargetStore && entryInst.idx == i.idx && entryInst.idx2 == cells.incoming[0])
                                        for (auto &parameter : f.blocks[0].params) if (parameter.first == entryInst.a && at(facts.stack, entryInst.a).kind > 0)
                                            token = at(facts.stack, entryInst.a);
                                if (i.idx2 == cells.incoming[0]) set(facts.stack, i.res, token);
                                if (i.idx2 == cells.incoming[1] || i.idx2 == cells.escaped[0] || i.idx2 == cells.escaped[1]) set(facts.markof, i.res, token);
                            }
                            break;
                        }
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

            if (CoreHasConstruction(m.profile))
                for (auto &block : f.blocks) for (auto &inst : block.insts) {
                    if (inst.op != GirOp::HdrInit) continue;
                    auto location = PointerLocationOf(fn, inst.a);
                    if (!location || location->kind != 1 || location->offset != 0 ||
                        f.members[location->index].kind != GirMember::Bytes || f.members[location->index].size != 16) continue;
                    auto owner = at(facts.markof, inst.b);
                    bool unique = owner.kind > 0;
                    for (auto &otherBlock : f.blocks) for (auto &other : otherBlock.insts)
                        if (other.op == GirOp::HdrInit && &other != &inst) {
                            auto address = PointerLocationOf(fn, other.a);
                            if (address && *address == *location) unique = false;
                        }
                    if (unique) set(facts.header, inst.a, owner);
                }

            for (size_t b = 1; b < f.blocks.size(); b++) {
                auto &params = f.blocks[b].params;
                auto &edges = incoming[b];
                for (size_t p = 0; p < params.size(); p++) {
                    vector<StackId> stacks, headers, marks;
                    for (auto &edge : edges) {
                        if (p >= edge.args.size()) continue;
                        stacks.push_back(at(facts.stack, edge.args[p]));
                        headers.push_back(at(facts.header, edge.args[p]));
                        marks.push_back(at(facts.markof, edge.args[p]));
                    }
                    set(facts.stack, params[p].first, MergeStackFacts(stacks));
                    set(facts.header, params[p].first, MergeStackFacts(headers));
                    set(facts.markof, params[p].first, MergeStackFacts(marks));
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

    bool ComputePassedStackChannels() {
        vector<StackFacts> facts;
        for (size_t function = 0; function < fns.size(); function++)
            facts.push_back(AnalyzeStackFacts(fns[function], lowPassedPairs[function], lowReturnedOwnerPairs));
        bool changed = false;
        for (size_t target = 0; target < m.funcs.size(); target++) {
            auto &callee = m.funcs[target];
            for (size_t position = 1; position < callee.params.size(); position++) {
                if (m.Type(callee.params[position]).kind != CoreType::Ptr) continue;
                bool called = false, valid = true;
                for (size_t caller = 0; caller < fns.size(); caller++)
                    for (auto &block : fns[caller].f->blocks) for (auto &inst : block.insts) {
                        if (inst.op != GirOp::Call || inst.idx != (int)target) continue;
                        called = true;
                        if (facts[caller].stack[inst.vals[position]].kind <= 0) valid = false;
                    }
                if (called && valid && find(lowStackParams[target].begin(), lowStackParams[target].end(), (int)position) == lowStackParams[target].end()) {
                    lowStackParams[target].push_back((int)position);
                    changed = true;
                }
            }
            for (size_t position = 1; position < callee.params.size(); position++)
                for (auto stack : lowStackParams[target]) {
                    bool called = false, valid = true;
                    for (size_t caller = 0; caller < fns.size(); caller++)
                        for (auto &block : fns[caller].f->blocks) for (auto &inst : block.insts) {
                            if (inst.op != GirOp::Call || inst.idx != (int)target) continue;
                            called = true;
                            auto mark = facts[caller].markof[inst.vals[position]];
                            auto owner = facts[caller].stack[inst.vals[stack]];
                            if (mark.kind <= 0 || !(mark == owner)) valid = false;
                        }
                    auto pair = make_pair((int)position, stack);
                    if (called && valid && find(lowMarkParams[target].begin(), lowMarkParams[target].end(), pair) == lowMarkParams[target].end()) {
                        lowMarkParams[target].push_back(pair);
                        changed = true;
                    }
                }
        }
        return changed;
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
                        auto location = PointerLocationOf(fn, i.a);
                        bool localAliasHeader = CoreHasConstruction(m.profile) && location && location->kind == 1 &&
                            location->offset == 0 && f.members[location->index].kind == GirMember::Bytes &&
                            f.members[location->index].size == 16;
                        if (h.kind <= 0 || ((h.kind == 3 || h.kind == 4) && !localAliasHeader) ||
                            mk.kind <= 0 || !(h == mk))
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
                        auto dynamic = false;
                        if (s.kind == 1)
                            for (auto &member : f.members)
                                dynamic |= member.kind == GirMember::Dynamic && member.stack == s.index;
                        if (s.kind == 2 && s.index >= 0 && s.index < (int)m.lowglobals.size())
                            dynamic = m.lowglobals[s.index].kind == GirMember::Dynamic;
                        if (!dynamic && (!CoreHasConstruction(m.profile) || find(pending.begin(), pending.end(), s) == pending.end())) pending.push_back(s);
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
            if (!CoreHasConstruction(m.profile) && !pending.empty()) bad("a stack bumped without the length of its header following in the block");
        }
        if (CoreHasConstruction(m.profile)) {
            vector<set<pair<int, int>>> incoming(f.blocks.size());
            vector<bool> reached(f.blocks.size(), false);
            vector<int> work { 0 };
            reached[0] = true;
            while (!work.empty()) {
                auto block = work.back(); work.pop_back();
                auto pending = incoming[block];
                for (auto &instruction : f.blocks[block].insts) {
                    if (instruction.op == GirOp::StackBump) {
                        auto owner = at(stack, instruction.a);
                        bool localHeader = false;
                        if (owner.kind == 1) for (auto &member : f.members)
                            localHeader |= member.kind == GirMember::Header && member.stack == owner.index;
                        if (owner.kind == 2 && owner.index >= 0 && owner.index < (int)m.lowglobals.size())
                            localHeader = m.lowglobals[owner.index].kind == GirMember::Header;
                        if (localHeader) pending.insert({ owner.kind, owner.index });
                    }
                    if (instruction.op == GirOp::HdrSetLen) {
                        auto owner = at(header, instruction.a);
                        pending.erase({ owner.kind, owner.index });
                    }
                    if (instruction.op == GirOp::StackRelease) {
                        auto owner = at(stack, instruction.a);
                        pending.erase({ owner.kind, owner.index });
                    }
                    if (instruction.op == GirOp::Ret && !pending.empty())
                        bad("normal return leaves an unpublished header growth");
                }
                for (auto successor : BlockSuccessors(f.blocks[block])) {
                    auto before = incoming[successor];
                    incoming[successor].insert(pending.begin(), pending.end());
                    if (!reached[successor] || before != incoming[successor]) {
                        reached[successor] = true;
                        work.push_back(successor);
                    }
                }
            }
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
        if (CoreHasConstruction(m.profile)) { CheckConstructionByteIntervals(fn); CheckLowSources(fn); CheckLowResultFlow(fn); }
        for (auto t : f.params) if (!scalar(t)) bad("a parameter whose layout is not resolved");
        for (auto t : f.results) if (!scalar(t)) bad("a result whose layout is not resolved");
        if (CoreHasConstruction(m.profile) && !f.results.empty())
            bad("construction result ABI retains a C return value");
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
            if (mem.kind == GirMember::Dynamic &&
                (!CoreHasConstruction(m.profile) || mem.stack < 0 || mem.stack >= f.stacks))
                bad("a dynamic member without a construction-owned data stack");
        }
        for (size_t a = 0; a < f.members.size(); a++)
            for (size_t c = a + 1; c < f.members.size(); c++) {
                auto &x = f.members[a], &y = f.members[c];
                auto ownsStack = [](const GirMember &member) {
                    return member.kind == GirMember::Header || member.kind == GirMember::Dynamic;
                };
                if (!ownsStack(x) || !ownsStack(y) || x.stack != y.stack) continue;
                if (ScopeWithin(f.scopes, x.scope, y.scope) || ScopeWithin(f.scopes, y.scope, x.scope))
                    bad(cat("two resizables live on data stack ", x.stack));
            }
        CheckStackDiscipline(fn);
        // A caller may pass an owner header and its stack to a callee. The
        // corresponding base is a valid restore point for that same stack.
        for (auto &b : f.blocks)
            for (auto &i : b.insts) {
                if (i.op == GirOp::ReturnFlagSet) {
                    const GirInst *value = nullptr;
                    for (auto &source : f.blocks) for (auto &candidate : source.insts)
                        if (GirDefinesValue(candidate) && candidate.res == i.a) value = &candidate;
                    int64_t flag = -1;
                    if (!value || value->op != GirOp::Int ||
                        from_chars(value->text.data(), value->text.data() + value->text.size(), flag).ec != errc() ||
                        flag < 0 || flag > (int64_t)m.lowtargets.size())
                        bad("return discriminant is not a known target or normal return");
                }
                if (i.op == GirOp::StackAt && (i.idx < 0 || i.idx >= f.stacks))
                    bad("a stack address is outside the function's owned stacks");
                if (i.op == GirOp::StackBump && i.idx >= 0 && i.b < 0 && i.idx == 0)
                    bad("a stack bumped by nothing");
            }
    }

    void CheckLowResultFlow(const Fn &fn) {
        auto &function = *fn.f;
        auto functionIndex = (int)(&function - m.funcs.data());
        auto bad = [&](const string &message) { Fail("GIR-V090", cat(fn.label, ": ", message)); };
        struct Address {
            enum class Kind { Unknown, Value, Frame, Global, LocalStack, GlobalStack, StackBytes, SavedTarget, EscapedTarget } kind = Kind::Unknown;
            int root = 0;
            int64_t offset = 0;
            int target = -1, cell = -1;
            Address() = default;
            Address(int identity, int64_t bytes) : kind(identity >= 0 ? Kind::Value : Kind::Frame),
                root(identity >= 0 ? identity : (int)(-(int64_t)identity - 1)), offset(bytes) {}
            static Address Target(int target, int cell, bool escaped) {
                Address result;
                result.kind = escaped ? Kind::EscapedTarget : Kind::SavedTarget;
                result.target = target;
                result.cell = cell;
                return result;
            }
            bool SameBase(const Address &other) const {
                return kind == other.kind && root == other.root && target == other.target && cell == other.cell;
            }
            bool operator==(const Address &) const = default;
            auto operator<=>(const Address &) const = default;
        };
        struct Value {
            Address address;
            int target = -1, cell = -1, sourceResult = -1;
            bool operator==(const Value &) const = default;
        };
        struct Blocked {
            Address address;
            int64_t bytes;
            int call;
            bool operator==(const Blocked &) const = default;
            auto operator<=>(const Blocked &) const = default;
        };
        struct State {
            map<int, Value> values, members;
            map<Address, pair<Value, int64_t>> memory, bytePayloads;
            map<Address, Value> stackEnds;
            set<tuple<int, int, int>> extents;
            set<Blocked> blocked;
            set<pair<Address, int64_t>> initialized;
            set<pair<int, int>> receiving, sourceReceiving;
            map<pair<int, int>, Value> payload;
            map<pair<int, int>, int> moves;
            int flag = 0, pending = -1, inFlight = -1;
            bool operator==(const State &) const = default;
        };
        vector<const GirInst *> definitions(fn.nvalues, nullptr);
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (GirDefinesValue(inst)) definitions[inst.res] = &inst;
        auto constant = [&](int value) -> optional<int64_t> {
            if (value < 0 || value >= fn.nvalues) return nullopt;
            auto inst = definitions[value];
            if (!inst || inst->op != GirOp::Int) return nullopt;
            int64_t number;
            auto parsed = from_chars(inst->text.data(), inst->text.data() + inst->text.size(), number);
            if (parsed.ec != errc() || parsed.ptr != inst->text.data() + inst->text.size()) return nullopt;
            return number;
        };
        auto member = [&](int target) {
            auto &members = m.lowtargets[target].members;
            return find(members.begin(), members.end(), functionIndex) != members.end();
        };
        auto value = [&](const State &state, int id) {
            auto found = state.values.find(id);
            auto result = found == state.values.end() ? Value {} : found->second;
            auto content = state.bytePayloads.find(result.address);
            if (content != state.bytePayloads.end()) {
                result.target = content->second.first.target;
                result.cell = content->second.first.cell;
            } else if (result.target >= 0 && result.cell >= 0) {
                auto &target = m.lowtargets[result.target];
                for (size_t position = 0; position < target.channels.size(); position++)
                    if (target.channels[position].escaped[0] == result.cell &&
                        holds_alternative<GirLowSnapshotResult>((*m.funcs[target.members[0]].lowResults)[position].layout))
                        result.target = result.cell = -1;
            }
            return result;
        };
        auto overlaps = [&](Address a, int64_t bytes, const Blocked &blocked) {
            if (a.kind != Address::Kind::Unknown && blocked.address.kind != Address::Kind::Unknown && !a.SameBase(blocked.address)) return false;
            if (a.kind == Address::Kind::Unknown || blocked.address.kind == Address::Kind::Unknown || a.offset == INT64_MAX ||
                blocked.address.offset == INT64_MAX || bytes == INT64_MAX || blocked.bytes == INT64_MAX) return true;
            if (a.offset <= blocked.address.offset)
                return (uint64_t)blocked.address.offset - (uint64_t)a.offset < (uint64_t)bytes;
            return (uint64_t)a.offset - (uint64_t)blocked.address.offset < (uint64_t)blocked.bytes;
        };
        auto read = [&](const State &state, Address address, int64_t bytes) {
            if (bytes == 0) return;
            for (auto &blocked : state.blocked) if (blocked.call != -2 && overlaps(address, bytes, blocked))
                bad("normal output is read before its call completed or its target payload landed");
        };
        auto initialize = [&](State &state, Address address, int64_t bytes) {
            for (auto iterator = state.blocked.begin(); iterator != state.blocked.end();) {
                auto &blocked = *iterator;
                bool covered = address.kind != Address::Kind::Unknown && address.SameBase(blocked.address) &&
                    address.offset != INT64_MAX && blocked.address.offset != INT64_MAX && address.offset <= blocked.address.offset &&
                    (bytes == INT64_MAX || (blocked.bytes != INT64_MAX && bytes >= blocked.bytes &&
                        (uint64_t)blocked.address.offset - (uint64_t)address.offset <= (uint64_t)(bytes - blocked.bytes)));
                if (covered) iterator = state.blocked.erase(iterator); else ++iterator;
            }
        };
        auto output = [&](const State &state, int target, size_t result, size_t word) {
            auto words = LowResultWords((*function.lowResults)[result]);
            auto parameter = function.blocks[0].params[words[word].parameter].first;
            (void)target;
            return value(state, parameter).address;
        };
        State entry;
        for (auto &parameter : function.blocks[0].params)
            if (m.Type(parameter.second).kind == CoreType::Ptr) entry.values[parameter.first].address = { parameter.first, 0 };
        for (auto &result : *function.lowResults) for (auto &word : LowResultWords(result)) if (word.bytes)
            entry.blocked.insert({ value(entry, function.blocks[0].params[word.parameter].first).address, word.bytes,
                holds_alternative<GirLowNonfixedResult>(result.layout) ? -2 : -1 });
        for (auto &result : *function.lowResults) if (auto nonfixed = get_if<GirLowNonfixedResult>(&result.layout)) {
            auto address = value(entry, function.blocks[0].params[nonfixed->count].first).address;
            entry.initialized.insert({ address, 8 });
            address.offset += 8;
            entry.initialized.insert({ address, 8 });
        }
        vector<map<int, State>> incoming(function.blocks.size());
        incoming[0].emplace(-1, entry);
        vector<pair<int, int>> work { { 0, -1 } };
        auto merge = [&](int block, State state) {
            auto partition = state.inFlight;
            auto found = incoming[block].find(partition);
            if (found == incoming[block].end()) {
                incoming[block].emplace(partition, std::move(state));
                work.push_back({ block, partition });
                return;
            }
            auto next = found->second;
            for (auto *facts : { &next.values, &next.members }) {
                auto &other = facts == &next.values ? state.values : state.members;
                for (auto iterator = facts->begin(); iterator != facts->end();) {
                    auto found = other.find(iterator->first);
                    if (found == other.end() || found->second != iterator->second) iterator = facts->erase(iterator); else ++iterator;
                }
            }
            for (auto iterator = next.memory.begin(); iterator != next.memory.end();) {
                auto found = state.memory.find(iterator->first);
                if (found == state.memory.end() || found->second != iterator->second) iterator = next.memory.erase(iterator); else ++iterator;
            }
            for (auto iterator = next.bytePayloads.begin(); iterator != next.bytePayloads.end();) {
                auto found = state.bytePayloads.find(iterator->first);
                if (found == state.bytePayloads.end() || found->second != iterator->second) iterator = next.bytePayloads.erase(iterator); else ++iterator;
            }
            for (auto iterator = next.stackEnds.begin(); iterator != next.stackEnds.end();) {
                auto found = state.stackEnds.find(iterator->first);
                if (found == state.stackEnds.end() || found->second != iterator->second) iterator = next.stackEnds.erase(iterator); else ++iterator;
            }
            for (auto iterator = next.moves.begin(); iterator != next.moves.end();) {
                auto found = state.moves.find(iterator->first);
                if (found == state.moves.end() || found->second != iterator->second) iterator = next.moves.erase(iterator); else ++iterator;
            }
            for (auto iterator = next.payload.begin(); iterator != next.payload.end();) {
                auto found = state.payload.find(iterator->first);
                if (found == state.payload.end() || found->second != iterator->second) iterator = next.payload.erase(iterator); else ++iterator;
            }
            set<tuple<int, int, int>> extents;
            set_intersection(next.extents.begin(), next.extents.end(), state.extents.begin(), state.extents.end(), inserter(extents, extents.end()));
            next.extents = std::move(extents);
            set<pair<Address, int64_t>> initialized;
            set_intersection(next.initialized.begin(), next.initialized.end(), state.initialized.begin(), state.initialized.end(), inserter(initialized, initialized.end()));
            next.initialized = std::move(initialized);
            next.blocked.insert(state.blocked.begin(), state.blocked.end());
            next.receiving.insert(state.receiving.begin(), state.receiving.end());
            next.sourceReceiving.insert(state.sourceReceiving.begin(), state.sourceReceiving.end());
            if (next.flag != state.flag) next.flag = -1;
            if (next.pending != state.pending) bad("control flow merges different calls awaiting their return discriminants");
            if (!(next == found->second)) { found->second = std::move(next); work.push_back({ block, partition }); }
        };
        auto receive = [&](State &state, Address destination, const Value &stored, bool bytes, int64_t extent, int byteValue) {
            if (stored.target < 0 || !member(stored.target)) return;
            auto &target = m.lowtargets[stored.target];
            for (size_t result = 0; result < target.channels.size(); result++) {
                auto &channel = target.channels[result];
                bool nonfixed = holds_alternative<GirLowNonfixedResult>((*function.lowResults)[result].layout);
                for (size_t word = 0; word < channel.escaped.size(); word++) if (channel.escaped[word] == stored.cell) {
                    if (nonfixed && word == 1) continue;
                    size_t outputWord = nonfixed && word == 0 ? 1 : word;
                    if (bytes != (nonfixed ? word == 0 : holds_alternative<GirLowSnapshotResult>((*function.lowResults)[result].layout))) continue;
                    if (destination != output(state, stored.target, result, outputWord)) continue;
                    if (bytes) {
                        if (nonfixed && !state.extents.count({ stored.target, stored.cell, byteValue })) continue;
                        if (auto snapshot = get_if<GirLowSnapshotResult>(&(*function.lowResults)[result].layout))
                            if (extent != snapshot->bytes) continue;
                    } else {
                        auto words = LowResultWords((*function.lowResults)[result]);
                        if (extent != words[outputWord].bytes) continue;
                    }
                    state.receiving.erase({ stored.target, stored.cell });
                    if (nonfixed && bytes) state.moves[{ stored.target, (int)result }] = byteValue;
                }
            }
        };
        auto invalidateBytes = [&](State &state, Address address, int64_t bytes) {
            for (auto iterator = state.memory.begin(); iterator != state.memory.end();)
                if (overlaps(address, bytes, { iterator->first, iterator->second.second, 0 })) iterator = state.memory.erase(iterator); else ++iterator;
            for (auto iterator = state.bytePayloads.begin(); iterator != state.bytePayloads.end();)
                if (overlaps(address, bytes, { iterator->first, iterator->second.second, 0 })) iterator = state.bytePayloads.erase(iterator); else ++iterator;
            if (address.kind == Address::Kind::Frame) state.members.erase(address.root);
        };
        auto invalidateLanding = [&](State &state, Address address, int64_t bytes) {
            if (state.inFlight < 0 || !member(state.inFlight)) return;
            auto target = state.inFlight;
            for (size_t result = 0; result < m.lowtargets[target].channels.size(); result++) {
                auto &channel = m.lowtargets[target].channels[result];
                auto words = LowResultWords((*function.lowResults)[result]);
                bool nonfixed = holds_alternative<GirLowNonfixedResult>((*function.lowResults)[result].layout);
                for (size_t word = 0; word < channel.escaped.size(); word++) {
                    if (nonfixed && word == 1) continue;
                    auto position = nonfixed && word == 0 ? 1 : word;
                    auto extent = nonfixed && word == 0 ? INT64_MAX : words[position].bytes;
                    if (overlaps(address, bytes, { output(state, target, result, position), extent, 0 }))
                        state.receiving.insert({ target, channel.escaped[word] });
                }
            }
        };
        auto protect = [&](const State &state, Address address, int64_t bytes, const Value *landing = nullptr, int byteValue = -1) {
            if (bytes == 0 || state.inFlight < 0) return;
            auto target = state.inFlight;
            auto &receiver = m.funcs[m.lowtargets[target].members[0]];
            for (size_t result = 0; result < m.lowtargets[target].channels.size(); result++) {
                auto &channel = m.lowtargets[target].channels[result];
                auto &layout = (*receiver.lowResults)[result].layout;
                bool nonfixed = holds_alternative<GirLowNonfixedResult>(layout);
                auto snapshot = get_if<GirLowSnapshotResult>(&layout);
                if (!nonfixed && !snapshot) continue;
                auto cell = channel.escaped[0];
                bool local = member(target);
                if (local && !state.receiving.count({ target, cell })) continue;
                auto destination = local ? output(state, target, result, nonfixed ? 1 : 0) : Address {};
                auto incoming = state.payload.find({ target, channel.incoming[0] });
                auto snapshotDestination = incoming == state.payload.end() ? Address::Target(target, channel.incoming[0], false) : incoming->second.address;
                bool exactLanding = landing && landing->target == target && landing->cell == cell &&
                    (local ? address == destination : snapshot && address == snapshotDestination) &&
                    (nonfixed ? state.extents.count({ target, cell, byteValue }) != 0 : bytes == snapshot->bytes);
                if (exactLanding) continue;
                bool escapedAlias = address.kind == Address::Kind::Unknown ||
                    (address.kind == Address::Kind::EscapedTarget && address.target == target &&
                        (address.cell == cell || (nonfixed && address.cell == channel.escaped[1]))) ||
                    (address.kind == Address::Kind::SavedTarget && address.target == target &&
                        address.cell == channel.incoming[nonfixed ? 1 : 0]);
                bool receivingAlias = local && overlaps(address, bytes, { destination, nonfixed ? INT64_MAX : snapshot->bytes, 0 });
                if (escapedAlias || receivingAlias)
                    bad("pending escaped payload bytes are overwritten before landing");
            }
        };
        map<Address, int> stackRoots;
        int callOrdinal = 0;
        map<const GirInst *, int> callIds;
        map<int, int> flagCalls;
        for (auto &block : function.blocks) for (size_t position = 0; position < block.insts.size(); position++) {
            auto &inst = block.insts[position];
            if (inst.op != GirOp::Call) continue;
            callIds[&inst] = callOrdinal++;
            if (position + 1 < block.insts.size() && block.insts[position + 1].op == GirOp::ReturnFlagGet)
                flagCalls[block.insts[position + 1].res] = callIds[&inst];
        }
        while (!work.empty()) {
            auto [block, partition] = work.back(); work.pop_back();
            auto state = incoming[block].at(partition);
            for (auto &inst : function.blocks[block].insts) {
                if (state.pending >= 0) {
                    switch (inst.op) {
                        case GirOp::ReturnFlagGet: case GirOp::Int: case GirOp::Bool: case GirOp::Unit:
                        case GirOp::Bin: case GirOp::Un: case GirOp::Cmp: case GirOp::BoolCmp:
                        case GirOp::Not: case GirOp::Conv: case GirOp::Next: case GirOp::PtrEq:
                        case GirOp::PtrOffset: case GirOp::FrameAddr: case GirOp::GlobalAddr:
                        case GirOp::Br: case GirOp::CondBr: case GirOp::Unreachable: break;
                        default: bad("a call awaiting its return discriminant resumes effects before dispatch");
                    }
                }
                if (GirDefinesValue(inst) && m.Type(fn.vt[inst.res]).kind == CoreType::Ptr)
                    state.values[inst.res] = Value { { inst.res, 0 } };
                if (inst.op == GirOp::StackAt || inst.op == GirOp::GlobalStack) {
                    auto &address = state.values[inst.res].address;
                    address.kind = inst.op == GirOp::StackAt ? Address::Kind::LocalStack : Address::Kind::GlobalStack;
                    address.root = inst.idx;
                    address.target = inst.op == GirOp::StackAt ? inst.a : -1;
                }
                if (inst.op == GirOp::StackMark) {
                    auto stack = value(state, inst.a).address;
                    auto &address = state.values[inst.res].address;
                    if (stack.kind == Address::Kind::Unknown) address = Address {};
                    else {
                        auto root = stackRoots.emplace(stack, (int)stackRoots.size()).first->second;
                        address.kind = Address::Kind::StackBytes;
                        address.root = root;
                        address.offset = INT64_MAX;
                    }
                    auto end = state.stackEnds.find(stack);
                    if (stack.kind != Address::Kind::Unknown && end != state.stackEnds.end()) state.values[inst.res] = end->second;
                }
                if (inst.op == GirOp::StackBump || inst.op == GirOp::StackRelease) {
                    auto stack = value(state, inst.a).address;
                    if (state.inFlight >= 0) {
                        auto target = state.inFlight;
                        for (size_t result = 0; result < m.lowtargets[target].channels.size(); result++) {
                            auto &channel = m.lowtargets[target].channels[result];
                            if (channel.incoming.size() != 3) continue;
                            auto incoming = state.payload.find({ target, channel.incoming[0] });
                            auto active = incoming == state.payload.end() ? Address::Target(target, channel.incoming[0], false) : incoming->second.address;
                            if (stack.kind != Address::Kind::Unknown && stack != active) continue;
                            if (inst.op == GirOp::StackBump) bad("stack growth changes an in-flight escaped payload interval");
                            auto landed = state.moves.find({ target, (int)result });
                            bool preserves = false;
                            if (member(target) && landed != state.moves.end()) {
                                auto release = definitions[inst.b];
                                preserves = release && release->op == GirOp::PtrOffset && release->idx == 1 && release->b == landed->second &&
                                    value(state, release->a).address == output(state, target, result, 1);
                            } else {
                                auto mark = value(state, inst.b);
                                preserves = mark.target == target && mark.cell == channel.escaped[1];
                            }
                            if (!preserves) bad("stack release crosses an in-flight escaped payload interval");
                        }
                    }
                    if (inst.op == GirOp::StackBump) state.stackEnds.erase(stack);
                    else if (stack.kind != Address::Kind::Unknown) state.stackEnds[stack] = value(state, inst.b);
                }
                if (inst.op == GirOp::HdrBase) state.values[inst.res].address = Address {};
                if (inst.op == GirOp::GlobalAddr) {
                    auto &address = state.values[inst.res].address;
                    address.kind = Address::Kind::Global;
                    address.root = inst.idx;
                }
                if (inst.op == GirOp::FrameAddr) state.values[inst.res].address = { -inst.idx - 1, 0 };
                if (inst.op == GirOp::LocalSet) {
                    state.members[inst.idx] = value(state, inst.a);
                    auto bytes = function.members[inst.idx].kind != GirMember::Scalar || m.Type(function.members[inst.idx].ty).kind == CoreType::Ptr ? m.pointerBytes : FlatSize(function.members[inst.idx].ty);
                    Address address { -inst.idx - 1, 0 };
                    protect(state, address, bytes);
                    invalidateLanding(state, address, bytes);
                    initialize(state, address, bytes);
                    for (auto iterator = state.memory.begin(); iterator != state.memory.end();)
                        if (overlaps(address, bytes, { iterator->first, iterator->second.second, 0 })) iterator = state.memory.erase(iterator); else ++iterator;
                    invalidateBytes(state, address, bytes);
                    state.members[inst.idx] = value(state, inst.a);
                    state.memory[address] = { value(state, inst.a), bytes };
                    state.initialized.insert({ address, bytes });
                    receive(state, address, value(state, inst.a), false, bytes, -1);
                }
                if (inst.op == GirOp::LocalGet) {
                    auto bytes = function.members[inst.idx].kind != GirMember::Scalar || m.Type(function.members[inst.idx].ty).kind == CoreType::Ptr ? m.pointerBytes : FlatSize(function.members[inst.idx].ty);
                    read(state, { -inst.idx - 1, 0 }, bytes);
                    auto found = state.members.find(inst.idx);
                    state.values[inst.res] = found == state.members.end() ? Value {} : found->second;
                }
                if (inst.op == GirOp::PtrOffset) {
                    auto address = value(state, inst.a).address;
                    auto index = constant(inst.b);
                    if (!index || address.offset == INT64_MAX || inst.idx <= 0 ||
                        *index > INT64_MAX / inst.idx || *index < INT64_MIN / inst.idx ||
                        (*index >= 0 && address.offset > INT64_MAX - *index * inst.idx) ||
                        (*index < 0 && address.offset < INT64_MIN - *index * inst.idx)) address.offset = INT64_MAX;
                    else address.offset += *index * inst.idx;
                    state.values[inst.res].address = address;
                }
                if (inst.op == GirOp::TargetLoad) {
                    auto found = state.payload.find({ inst.idx, inst.idx2 });
                    if (found != state.payload.end()) state.values[inst.res] = found->second;
                    else state.values[inst.res] = Value { Address::Target(inst.idx, inst.idx2, false) };
                }
                if (inst.op == GirOp::TargetStore) {
                    auto stored = value(state, inst.a);
                    if (state.inFlight == inst.idx && !member(inst.idx))
                        for (auto &channel : m.lowtargets[inst.idx].channels)
                            if (find(channel.escaped.begin(), channel.escaped.end(), inst.idx2) != channel.escaped.end() &&
                                (stored.target != inst.idx || stored.cell != inst.idx2))
                                bad("forwarding frame changes an in-flight escaped payload cell");
                    if (state.inFlight == inst.idx && member(inst.idx) && !state.receiving.empty())
                        if (stored.target != inst.idx || stored.cell != inst.idx2)
                            bad("target activation is restored or changed before its payload lands");
                    state.payload[{ inst.idx, inst.idx2 }] = stored;
                }
                if (inst.op == GirOp::PLoad) {
                    auto address = value(state, inst.a).address;
                    auto bytes = m.Type(inst.ty).kind == CoreType::Ptr ? m.pointerBytes : FlatSize(inst.ty);
                    read(state, address, bytes);
                    auto found = state.memory.find(address);
                    state.values[inst.res] = address.kind == Address::Kind::Unknown || address.offset == INT64_MAX ||
                        found == state.memory.end() || found->second.second != bytes ? Value {} : found->second.first;
                }
                if (inst.op == GirOp::PStore) {
                    auto address = value(state, inst.a).address;
                    auto bytes = m.Type(inst.ty).kind == CoreType::Ptr ? m.pointerBytes : FlatSize(inst.ty);
                    protect(state, address, bytes);
                    invalidateLanding(state, address, bytes);
                    initialize(state, address, bytes);
                    for (auto iterator = state.memory.begin(); iterator != state.memory.end();)
                        if (overlaps(address, bytes, { iterator->first, iterator->second.second, 0 })) iterator = state.memory.erase(iterator); else ++iterator;
                    if (address.kind == Address::Kind::Frame) {
                        state.members.erase(address.root);
                        auto &field = function.members[address.root];
                        auto width = field.kind != GirMember::Scalar || m.Type(field.ty).kind == CoreType::Ptr ? m.pointerBytes : FlatSize(field.ty);
                        if (address.offset == 0 && bytes == width) state.members[address.root] = value(state, inst.b);
                    }
                    invalidateBytes(state, address, bytes);
                    if (address.kind == Address::Kind::Frame && address.offset == 0) {
                        auto &field = function.members[address.root];
                        auto width = field.kind != GirMember::Scalar || m.Type(field.ty).kind == CoreType::Ptr ? m.pointerBytes : FlatSize(field.ty);
                        if (bytes == width) state.members[address.root] = value(state, inst.b);
                    }
                    if (address.kind != Address::Kind::Unknown && address.offset != INT64_MAX)
                        state.memory[address] = { value(state, inst.b), bytes };
                    if (address.kind != Address::Kind::Unknown && address.offset != INT64_MAX)
                        state.initialized.insert({ address, bytes });
                    receive(state, address, value(state, inst.b), false, bytes, -1);
                }
                if (inst.op == GirOp::HdrBase || inst.op == GirOp::HdrLen) read(state, value(state, inst.a).address, 16);
                if (inst.op == GirOp::OutBytes) read(state, value(state, inst.a).address, constant(inst.b).value_or(INT64_MAX));
                if (inst.op == GirOp::BytesCopy || inst.op == GirOp::BytesMove || inst.op == GirOp::BytesFill) {
                    auto bytes = inst.vals.empty() ? optional<int64_t>(inst.idx) : constant(inst.vals[0]);
                    auto count = bytes && *bytes >= 0 ? *bytes : INT64_MAX;
                    auto source = value(state, inst.b);
                    if (inst.op == GirOp::BytesFill) {
                        if (bytes && *bytes >= 0 && inst.idx >= 0 && *bytes <= INT64_MAX / max(inst.idx, 1)) count = *bytes * inst.idx;
                        else count = INT64_MAX;
                        read(state, source.address, count == 0 ? 0 : inst.idx);
                    } else read(state, source.address, count);
                    auto destination = value(state, inst.a).address;
                    protect(state, destination, count, inst.op == GirOp::BytesFill ? nullptr : &source,
                        inst.vals.empty() ? -1 : inst.vals[0]);
                    if (destination.kind == Address::Kind::Frame) state.members.erase(destination.root);
                    invalidateLanding(state, destination, count);
                    for (auto iterator = state.memory.begin(); iterator != state.memory.end();)
                        if (overlaps(destination, count, { iterator->first, iterator->second.second, 0 })) iterator = state.memory.erase(iterator); else ++iterator;
                    invalidateBytes(state, destination, count);
                    if (inst.op != GirOp::BytesFill && source.target >= 0 && destination.kind != Address::Kind::Unknown && destination.offset != INT64_MAX) {
                        auto &target = m.lowtargets[source.target];
                        for (size_t result = 0; result < target.channels.size(); result++)
                            if (target.channels[result].escaped[0] == source.cell)
                                if (auto snapshot = get_if<GirLowSnapshotResult>(&(*m.funcs[target.members[0]].lowResults)[result].layout))
                                    if (bytes && *bytes == snapshot->bytes) state.bytePayloads[destination] = { source, *bytes };
                    }
                    bool exactPayload = !inst.vals.empty() && source.target >= 0 &&
                        state.extents.count({ source.target, source.cell, inst.vals[0] });
                    if (bytes && *bytes >= 0 && count != INT64_MAX) {
                        initialize(state, destination, count);
                        if (destination.kind != Address::Kind::Unknown && destination.offset != INT64_MAX)
                            state.initialized.insert({ destination, count });
                    }
                    else if (exactPayload) initialize(state, destination, INT64_MAX);
                    if (inst.op != GirOp::BytesFill)
                        receive(state, destination, source, true, bytes.value_or(-1), inst.vals.empty() ? -1 : inst.vals[0]);
                }
                if (inst.op == GirOp::HdrInit || inst.op == GirOp::HdrSetLen || inst.op == GirOp::Format) {
                    auto address = value(state, inst.op == GirOp::Format ? inst.b : inst.a).address;
                    auto bytes = inst.op == GirOp::Format ? 32 : inst.op == GirOp::HdrInit ? 16 : 8;
                    if (inst.op == GirOp::HdrSetLen) {
                        if (address.offset == INT64_MAX || address.offset > INT64_MAX - 8) address.offset = INT64_MAX;
                        else address.offset += 8;
                    }
                    protect(state, address, bytes);
                    invalidateLanding(state, address, bytes);
                    invalidateBytes(state, address, bytes);
                }
                if (inst.op == GirOp::Call) {
                    if (state.inFlight >= 0 || state.flag > 0) bad("a frame resumes calls while an escaped result is in flight");
                    for (auto *facts : { &state.values, &state.members })
                        for (auto &[id, fact] : *facts) {
                            (void)id;
                            fact.target = fact.cell = fact.sourceResult = -1;
                            if (fact.address.kind == Address::Kind::EscapedTarget) fact.address = Address {};
                        }
                    state.stackEnds.clear();
                    state.memory.clear();
                    state.bytePayloads.clear();
                    for (size_t target = 0; target < m.lowtargets.size(); target++)
                        for (auto &channel : m.lowtargets[target].channels) for (auto cell : channel.escaped)
                            state.payload.erase({ (int)target, cell });
                    state.extents.clear();
                    auto &callee = m.funcs[inst.idx];
                    set<int> outputParameters;
                    for (auto &result : *callee.lowResults) for (auto &word : LowResultWords(result)) outputParameters.insert(word.parameter);
                    for (size_t parameter = 1; parameter < callee.params.size(); parameter++)
                        if (m.Type(callee.params[parameter]).kind == CoreType::Ptr && !outputParameters.count((int)parameter))
                        {
                            auto address = value(state, inst.vals[parameter]).address;
                            read(state, address, INT64_MAX);
                            protect(state, address, INT64_MAX);
                        }
                    for (auto &result : *callee.lowResults) if (auto nonfixed = get_if<GirLowNonfixedResult>(&result.layout)) {
                        auto address = value(state, inst.vals[nonfixed->count]).address;
                        if (address.kind == Address::Kind::Unknown || address.offset == INT64_MAX || !state.initialized.count({ address, 8 })) bad("nonfixed call count metadata is not initialized");
                        if (address.offset > INT64_MAX - 8) bad("nonfixed call identity metadata address overflows");
                        address.offset += 8;
                        if (address.kind == Address::Kind::Unknown || address.offset == INT64_MAX || !state.initialized.count({ address, 8 })) bad("nonfixed call destination identity metadata is not initialized");
                    }
                    vector<Blocked> outputs;
                    for (auto &result : *callee.lowResults) for (auto &word : LowResultWords(result)) if (word.bytes) {
                        Blocked output { value(state, inst.vals[word.parameter]).address,
                            holds_alternative<GirLowNonfixedResult>(result.layout) ? 16 : word.bytes, 0 };
                        for (auto &previous : outputs) if (overlaps(output.address, output.bytes, previous))
                            bad("call result output cells overlap or have unknown aliasing");
                        outputs.push_back(output);
                    }
                    if (state.inFlight >= 0 && member(state.inFlight))
                        for (auto &output : outputs) invalidateLanding(state, output.address, output.bytes);
                    auto &effect = lowReturnFlagEffects[inst.idx];
                    bool escaping = (effect.preservesInput && state.flag != 0) || any_of(effect.values.begin(), effect.values.end(), [](auto flag) { return flag != 0; });
                    for (auto &result : *callee.lowResults) {
                        auto words = LowResultWords(result);
                        for (size_t word = 0; word < words.size(); word++) if (words[word].bytes ||
                            (holds_alternative<GirLowNonfixedResult>(result.layout) && word == 1)) {
                            auto address = value(state, inst.vals[words[word].parameter]).address;
                            auto bytes = words[word].bytes ? words[word].bytes : INT64_MAX;
                            initialize(state, address, bytes);
                            if (address.kind == Address::Kind::Frame) state.members.erase(address.root);
                            if (escaping) {
                                state.blocked.insert({ address, bytes, callIds.at(&inst) });
                                for (auto iterator = state.initialized.begin(); iterator != state.initialized.end();)
                                    if (overlaps(iterator->first, iterator->second, { address, bytes, 0 })) iterator = state.initialized.erase(iterator); else ++iterator;
                            } else if (address.kind != Address::Kind::Unknown && address.offset != INT64_MAX)
                                state.initialized.insert({ address, bytes });
                        }
                    }
                    state.pending = escaping ? callIds.at(&inst) : -1;
                    auto returnedFlags = effect.values;
                    bool unknownInput = effect.preservesInput && state.flag < 0;
                    if (effect.preservesInput && state.flag >= 0) returnedFlags.insert(state.flag);
                    state.flag = !unknownInput && returnedFlags.size() == 1 ? (int)*returnedFlags.begin() : -1;
                }
                if (inst.op == GirOp::SourceTargetGet) {
                    auto enter = definitions[inst.a];
                    if (enter && enter->op == GirOp::SourceTargetEnter) {
                        state.values[inst.res].target = enter->idx;
                        state.values[inst.res].sourceResult = inst.idx;
                    }
                }
                if (inst.op == GirOp::SourceTargetResult && state.inFlight == inst.idx)
                    bad("forwarding or receiving frame replaces in-flight reference provenance");
                if (inst.op == GirOp::SourceResult && state.inFlight >= 0 && member(state.inFlight)) {
                    auto target = state.inFlight;
                    for (size_t result = 0; result < function.lowResults->size(); result++) {
                        auto &layout = (*function.lowResults)[result].layout;
                        bool reference = holds_alternative<GirLowReferenceResult>(layout) || holds_alternative<GirLowResizableReferenceResult>(layout);
                        if (!reference) continue;
                        if (LowResultWords((*function.lowResults)[result])[0].parameter != inst.idx) continue;
                        auto source = value(state, inst.a);
                        if (source.target != target || source.sourceResult != (int)result)
                            bad("target catch returns reference provenance from another result channel");
                        state.sourceReceiving.erase({ target, (int)result });
                    }
                }
                if (inst.op == GirOp::ReturnFlagSet) state.flag = (int)constant(inst.a).value_or(-1);
                if (inst.op == GirOp::Ret) {
                    if (state.inFlight >= 0 && member(state.inFlight) && state.flag != 0)
                        bad("target member propagates an escape instead of completing its catch");
                    if (state.inFlight >= 0 && !member(state.inFlight) && state.flag != state.inFlight + 1)
                        bad("forwarding frame changes its in-flight target discriminant");
                    if (state.flag > 0 && state.inFlight >= 0)
                        for (auto &channel : m.lowtargets[state.inFlight].channels) for (auto cell : channel.escaped)
                            if (!state.payload.count({ state.inFlight, cell })) bad("forwarding frame loses an in-flight payload cell");
                    if (state.flag <= 0) {
                        if (!state.sourceReceiving.empty()) bad("target catch omits its escaped reference provenance");
                        if (!state.receiving.empty()) bad("target catch returns without transferring its escaped payload");
                        for (auto &result : *function.lowResults) for (auto &word : LowResultWords(result)) if (word.bytes) {
                            auto address = value(state, function.blocks[0].params[word.parameter].first).address;
                            for (auto &blocked : state.blocked) if (overlaps(address, word.bytes, blocked))
                                bad("normal return omits a declared primitive result output");
                        }
                    }
                }
            }
            auto *term = LastTerm(function.blocks[block]);
            if (!term) continue;
            auto edge = [&](int destination, const vector<int> &arguments, bool positive) {
                auto next = state;
                if (term->op == GirOp::CondBr) {
                    auto condition = definitions[term->a];
                    if (condition && condition->op == GirOp::PtrEq) {
                        auto left = value(state, condition->a).address, right = value(state, condition->b).address;
                        if (!positive && left.kind != Address::Kind::Unknown && left == right && left.offset != INT64_MAX) return;
                    }
                    if (positive && condition && condition->op == GirOp::PtrEq) {
                        auto prove = [&](int computed, int endpoint) {
                            auto offset = computed >= 0 && computed < fn.nvalues ? definitions[computed] : nullptr;
                            if (!offset || offset->op != GirOp::PtrOffset || offset->idx != 1) return;
                            auto source = value(state, offset->a), end = value(state, endpoint);
                            if (source.target < 0 || source.target != end.target) return;
                            for (auto &channel : m.lowtargets[source.target].channels)
                                if (channel.incoming.size() == 3 && source.cell == channel.escaped[0] && end.cell == channel.escaped[1])
                                    next.extents.insert({ source.target, source.cell, offset->b });
                        };
                        prove(condition->a, condition->b);
                        prove(condition->b, condition->a);
                    }
                    if (condition && condition->op == GirOp::Cmp && condition->cmp == CoreCmpOp::Eq) {
                        int flag = condition->a;
                        auto tag = constant(condition->b);
                        if (!tag) { flag = condition->b; tag = constant(condition->a); }
                        auto call = flagCalls.find(flag);
                        if (positive && tag && call != flagCalls.end() && call->second == state.pending) {
                            next.flag = (int)*tag;
                            if (*tag == 0) {
                                next.pending = -1;
                                for (auto iterator = next.blocked.begin(); iterator != next.blocked.end();)
                                    if (iterator->call == call->second) {
                                        if (iterator->address.kind != Address::Kind::Unknown && iterator->address.offset != INT64_MAX)
                                            next.initialized.insert({ iterator->address, iterator->bytes });
                                        iterator = next.blocked.erase(iterator);
                                    } else ++iterator;
                            } else if (*tag > 0 && *tag <= (int64_t)m.lowtargets.size()) {
                                int target = (int)*tag - 1;
                                next.pending = -1;
                                next.inFlight = target;
                                for (auto &channel : m.lowtargets[target].channels) {
                                    for (auto cell : channel.escaped)
                                        next.payload[{ target, cell }] = Value { Address::Target(target, cell, true), target, cell };
                                    auto result = (size_t)(&channel - m.lowtargets[target].channels.data());
                                    auto &layout = (*m.funcs[m.lowtargets[target].members[0]].lowResults)[result].layout;
                                    if (auto snapshot = get_if<GirLowSnapshotResult>(&layout)) {
                                        auto payload = next.payload.at({ target, channel.escaped[0] });
                                        next.bytePayloads[payload.address] = { payload, snapshot->bytes };
                                    }
                                    if (channel.incoming.size() == 3) {
                                        auto stack = next.payload.find({ target, channel.incoming[0] });
                                        auto address = stack == next.payload.end() ? Address::Target(target, channel.incoming[0], false) : stack->second.address;
                                        next.stackEnds[address] = next.payload.at({ target, channel.escaped[1] });
                                    }
                                    if (member(target)) {
                                        auto result = (size_t)(&channel - m.lowtargets[target].channels.data());
                                        auto &layout = (*function.lowResults)[result].layout;
                                        if (holds_alternative<GirLowReferenceResult>(layout) || holds_alternative<GirLowResizableReferenceResult>(layout))
                                            next.sourceReceiving.insert({ target, (int)result });
                                    }
                                    for (size_t word = 0; word < channel.escaped.size(); word++) {
                                        if (channel.incoming.size() == 3 && word == 1) continue;
                                        if (member(target)) next.receiving.insert({ target, channel.escaped[word] });
                                    }
                                }
                            }
                        }
                    }
                }
                for (size_t position = 0; position < arguments.size(); position++)
                    next.values[function.blocks[destination].params[position].first] = value(state, arguments[position]);
                merge(destination, std::move(next));
            };
            if (term->op == GirOp::Br) edge(term->idx, term->vals, true);
            if (term->op == GirOp::CondBr) { edge(term->idx, term->vals, true); edge(term->idx2, term->vals2, false); }
        }
    }

    void CheckLowSources(const Fn &fn) {
        auto &function = *fn.f;
        auto kinds = GirSourceKinds(function);
        auto bad = [&](const string &message) { Fail("GIR-V090", cat(fn.label, ": ", message)); };
        for (auto kind : kinds.values) if (kind == GirSourceKind::Mixed) bad("trace metadata merges with a program value or another token kind");
        for (auto kind : kinds.members) if (kind >= GirSourceKind::Scope) bad("a frame member stores a trace token or mixed program metadata");
        struct Call { int token, scope, callee = -1; bool operator==(const Call &) const = default; };
        struct State {
            vector<int> scopes;
            vector<Call> calls;
            vector<pair<int, int>> targets;
            map<int, int> owners, members;
            set<int> outputs;
            int flag = 0;
            bool operator==(const State &) const = default;
        };
        vector<optional<State>> incoming(function.blocks.size());
        incoming[0] = State {};
        vector<int> work { 0 };
        auto merge = [&](int target, State state) {
            if (!incoming[target]) { incoming[target] = std::move(state); work.push_back(target); return; }
            auto previous = *incoming[target];
            auto next = previous;
            if (next.scopes != state.scopes || next.calls != state.calls || next.targets != state.targets) bad("control-flow merge changes active trace scopes, targets, or calls");
            if (next.flag != state.flag) next.flag = -1;
            for (auto *members : { &next.owners, &next.members }) {
                auto &other = members == &next.owners ? state.owners : state.members;
                for (auto iterator = members->begin(); iterator != members->end();) {
                    auto found = other.find(iterator->first);
                    if (found == other.end() || found->second != iterator->second) iterator = members->erase(iterator);
                    else ++iterator;
                }
            }
            set<int> outputs;
            set_intersection(next.outputs.begin(), next.outputs.end(), state.outputs.begin(), state.outputs.end(), inserter(outputs, outputs.end()));
            next.outputs = std::move(outputs);
            if (!(next == previous)) { incoming[target] = std::move(next); work.push_back(target); }
        };
        auto sourceResults = [&](int callee) {
            set<int> positions;
            for (auto &block : m.funcs[callee].blocks) for (auto &inst : block.insts)
                if (inst.op == GirOp::SourceResult) positions.insert(inst.idx);
            return positions;
        };
        while (!work.empty()) {
            auto block = work.back(); work.pop_back();
            auto state = *incoming[block];
            auto live = [&](int value) {
                auto owner = state.owners.find(value);
                if (owner == state.owners.end() || find(state.scopes.begin(), state.scopes.end(), owner->second) == state.scopes.end())
                    bad("source descriptor used outside its live trace scope");
            };
            auto source = [&](int value) {
                if (value < 0 || kinds.values[value] != GirSourceKind::Descriptor) bad("trace operation consumes a program pointer instead of a source descriptor");
                live(value);
            };
            auto owner = [&](int result) {
                if (state.scopes.empty()) bad("source descriptor created without a trace scope");
                state.owners[result] = state.scopes.back();
            };
            auto call = [&](int token) -> Call & {
                if (token < 0 || kinds.values[token] != GirSourceKind::Call || state.calls.empty() || state.calls.back().token != token)
                    bad("trace call token is dead or not the innermost call");
                return state.calls.back();
            };
            for (auto &inst : function.blocks[block].insts) {
                vector<int> uses;
                Uses(inst, uses);
                bool traceOperation = (inst.op >= GirOp::SourceNew && inst.op <= GirOp::SourceTargetGet) ||
                                      (inst.op >= GirOp::SourceLeave && inst.op <= GirOp::SourceTargetResult);
                for (auto value : uses) if (kinds.values[value] > GirSourceKind::Ordinary && !traceOperation) {
                    if (inst.op == GirOp::LocalSet && kinds.values[value] == GirSourceKind::Descriptor) source(value);
                    else if ((inst.op == GirOp::Br || inst.op == GirOp::CondBr) && kinds.values[value] == GirSourceKind::Descriptor && value != inst.a) source(value);
                    else bad("trace metadata is used as ordinary program memory or an ABI argument");
                }
                switch (inst.op) {
                    case GirOp::SourceEnter: state.scopes.push_back(inst.res); break;
                    case GirOp::SourceLeave:
                        if (inst.a < 0 || kinds.values[inst.a] != GirSourceKind::Scope || state.scopes.empty() || state.scopes.back() != inst.a)
                            bad("trace scope token is dead or not the innermost scope");
                        for (auto &active : state.calls) if (active.scope == inst.a) bad("trace scope leaves before its call epilogue");
                        if (!state.targets.empty()) bad("trace scope leaves before its target activation cleanup");
                        state.scopes.pop_back();
                        break;
                    case GirOp::SourceNew: {
                        const GirInst *identity = nullptr;
                        for (auto &identityBlock : function.blocks) for (auto &candidate : identityBlock.insts)
                            if (GirDefinesValue(candidate) && candidate.res == inst.a) identity = &candidate;
                        if (!identity || identity->op != GirOp::TraceId || identity->trace != GirTraceKind::Storage)
                            bad("source storage identity does not come from an object creation ordinal");
                        if (kinds.values[inst.a] != GirSourceKind::Ordinary) bad("storage identity comes from metadata");
                        for (auto value : inst.vals) if (kinds.values[value] != GirSourceKind::Ordinary) bad("source path contains metadata");
                        owner(inst.res);
                        break;
                    }
                    case GirOp::SourceChild:
                        source(inst.a);
                        if (kinds.values[inst.b] != GirSourceKind::Ordinary) bad("source path index is metadata");
                        owner(inst.res);
                        break;
                    case GirOp::SourceGlobal:
                        if (inst.idx < 0 || inst.idx >= (int)m.lowglobals.size()) bad("source global position is outside the global table");
                        owner(inst.res);
                        break;
                    case GirOp::SourceGlobalSet:
                        if (inst.idx < 0 || inst.idx >= (int)m.lowglobals.size()) bad("source global position is outside the global table");
                        source(inst.a);
                        break;
                    case GirOp::SourceParam:
                        if (inst.idx <= 0 || inst.idx >= (int)function.params.size() || m.Type(function.params[inst.idx]).kind != CoreType::Ptr)
                            bad("source parameter is not a primitive pointer parameter");
                        owner(inst.res);
                        break;
                    case GirOp::SourceCallPush:
                        if (state.scopes.empty()) bad("trace call has no live scope");
                        for (auto value : inst.vals) if (value >= 0) source(value);
                        state.calls.push_back({ inst.res, state.scopes.back(), -1 });
                        break;
                    case GirOp::Call: {
                        auto &effect = lowReturnFlagEffects[inst.idx];
                        if (!(effect.preservesInput && effect.values.empty())) {
                            if (!effect.preservesInput && effect.values.size() == 1) state.flag = (int)*effect.values.begin();
                            else state.flag = -1;
                        }
                        bool hasTraceParam = false;
                        for (auto &calleeBlock : m.funcs[inst.idx].blocks) for (auto &candidate : calleeBlock.insts)
                            hasTraceParam |= candidate.op == GirOp::SourceParam || candidate.op == GirOp::SourceResult;
                        if (state.calls.empty() || state.calls.back().callee >= 0) {
                            if (hasTraceParam) bad("call omits the required provenance shadow");
                            break;
                        }
                        auto &active = state.calls.back();
                        const GirInst *push = nullptr;
                        for (auto &searchBlock : function.blocks) for (auto &candidate : searchBlock.insts)
                            if (candidate.op == GirOp::SourceCallPush && candidate.res == active.token) push = &candidate;
                        if (!push || push->vals.size() + 1 != m.funcs[inst.idx].params.size()) bad("trace shadow does not map every primitive argument position");
                        for (auto &calleeBlock : m.funcs[inst.idx].blocks) for (auto &candidate : calleeBlock.insts)
                            if (candidate.op == GirOp::SourceParam &&
                                (candidate.idx <= 0 || candidate.idx > (int)push->vals.size() || push->vals[candidate.idx - 1] < 0))
                                bad("trace shadow omits a borrowed parameter source");
                        active.callee = inst.idx;
                        break;
                    }
                    case GirOp::SourceCallGet: {
                        auto &active = call(inst.a);
                        if (active.callee < 0 || !sourceResults(active.callee).count(inst.idx)) bad("trace result does not map a produced source channel");
                        owner(inst.res);
                        break;
                    }
                    case GirOp::SourceCallPop:
                        if (call(inst.a).callee < 0) bad("trace call token popped before the call");
                        state.calls.pop_back();
                        break;
                    case GirOp::SourceTargetEnter: {
                        if (state.scopes.empty() || inst.idx < 0 || inst.idx >= (int)m.lowtargets.size()) bad("target provenance activation has no live scope or checked target");
                        auto &table = m.lowtargets[inst.idx];
                        auto functionIndex = (int)(&function - m.funcs.data());
                        if (find(table.members.begin(), table.members.end(), functionIndex) == table.members.end() ||
                            inst.vals.size() != table.channels.size()) bad("target provenance activation does not belong to its member or channels");
                        for (auto position : inst.vals)
                            if (position >= 0 && !sourceResults(functionIndex).count(position)) bad("target provenance maps an unproduced primitive output position");
                        state.targets.push_back({ inst.res, inst.idx });
                        break;
                    }
                    case GirOp::SourceTargetLeave:
                        if (state.targets.empty() || state.targets.back().first != inst.a || kinds.values[inst.a] != GirSourceKind::Target)
                            bad("target provenance token is dead or not the innermost activation");
                        state.targets.pop_back();
                        break;
                    case GirOp::SourceTargetGet: {
                        auto active = find_if(state.targets.begin(), state.targets.end(), [&](auto entry) { return entry.first == inst.a; });
                        if (active == state.targets.end() || kinds.values[inst.a] != GirSourceKind::Target) bad("target provenance lookup uses a dead activation");
                        const GirInst *enter = nullptr;
                        for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                            if (candidate.op == GirOp::SourceTargetEnter && candidate.res == inst.a) enter = &candidate;
                        if (!enter || inst.idx < 0 || inst.idx >= (int)enter->vals.size() || enter->vals[inst.idx] < 0)
                            bad("target provenance lookup does not map a reference result position");
                        owner(inst.res);
                        break;
                    }
                    case GirOp::SourceTargetResult:
                        if (inst.idx < 0 || inst.idx >= (int)m.lowtargets.size() || inst.idx2 < 0 ||
                            inst.idx2 >= (int)m.lowtargets[inst.idx].channels.size()) bad("target provenance result lies outside its checked channels");
                        {
                            bool referenceChannel = false;
                            for (auto member : m.lowtargets[inst.idx].members)
                                for (auto &candidateBlock : m.funcs[member].blocks) for (auto &candidate : candidateBlock.insts)
                                    if (candidate.op == GirOp::SourceTargetEnter && candidate.idx == inst.idx && candidate.vals[inst.idx2] >= 0)
                                        referenceChannel = true;
                            if (!referenceChannel) bad("target provenance result does not name a reference output channel");
                        }
                        source(inst.a);
                        break;
                    case GirOp::ReturnFlagSet:
                        state.flag = -1;
                        for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                            if (candidate.op == GirOp::Int && candidate.res == inst.a) {
                                auto parsed = from_chars(candidate.text.data(), candidate.text.data() + candidate.text.size(), state.flag);
                                if (parsed.ec != errc()) bad("return discriminant is invalid");
                            }
                        break;
                    case GirOp::SourceResult: {
                        source(inst.a);
                        if (inst.idx <= 0 || inst.idx >= (int)function.params.size() || m.Type(function.params[inst.idx]).kind != CoreType::Ptr)
                            bad("trace result does not name a primitive output pointer");
                        auto parameter = function.blocks[0].params[inst.idx].first;
                        bool stored = false;
                        for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                            stored |= candidate.op == GirOp::PStore && m.Type(candidate.ty).kind == CoreType::Ptr &&
                                      LowValueDependsOn(function, candidate.a, parameter);
                        if (!stored) bad("trace result has no matching address output store");
                        state.outputs.insert(inst.idx);
                        break;
                    }
                    case GirOp::SourceCopy:
                        source(inst.a);
                        if (kinds.values[inst.b] != GirSourceKind::Ordinary) bad("copy destination identity is metadata");
                        break;
                    case GirOp::LocalSet:
                        if (kinds.members[inst.idx] == GirSourceKind::Descriptor) { source(inst.a); state.members[inst.idx] = state.scopes.back(); }
                        break;
                    case GirOp::LocalGet:
                        if (kinds.values[inst.res] == GirSourceKind::Descriptor) {
                            auto member = state.members.find(inst.idx);
                            if (member == state.members.end() || find(state.scopes.begin(), state.scopes.end(), member->second) == state.scopes.end())
                                bad("source frame member is uninitialized or outside its scope");
                            owner(inst.res);
                        }
                        break;
                    case GirOp::FrameAddr:
                        if (kinds.members[inst.idx] > GirSourceKind::Ordinary) bad("program memory exposes a trace metadata member");
                        break;
                    case GirOp::Ret:
                        if (!state.scopes.empty() || !state.calls.empty() || !state.targets.empty()) bad("return omits trace scope, target, or call cleanup");
                        if (state.flag <= 0) for (auto position : sourceResults((int)(&function - m.funcs.data())))
                            if (!state.outputs.count(position)) bad("normal return omits a source output channel");
                        break;
                    default: break;
                }
            }
            auto *term = LastTerm(function.blocks[block]);
            if (!term) continue;
            auto edge = [&](int target, const vector<int> &values) {
                auto next = state;
                for (size_t position = 0; position < values.size(); position++) {
                    auto parameter = function.blocks[target].params[position].first;
                    if (kinds.values[parameter] == GirSourceKind::Descriptor) next.owners[parameter] = state.owners.at(values[position]);
                    else if (kinds.values[parameter] > GirSourceKind::Descriptor) bad("control flow transfers a trace token");
                }
                merge(target, std::move(next));
            };
            if (term->op == GirOp::Br) edge(term->idx, term->vals);
            if (term->op == GirOp::CondBr) { edge(term->idx, term->vals); edge(term->idx2, term->vals2); }
        }
    }

    void CheckConstructionByteIntervals(const Fn &fn) {
        auto &f = *fn.f;
        vector<const GirInst *> definitions(fn.nvalues, nullptr);
        vector<vector<int>> incoming(fn.nvalues);
        for (auto &block : f.blocks) {
            for (auto &param : block.params) {
                auto blockId = (int)(&block - f.blocks.data());
                auto position = (size_t)(&param - block.params.data());
                incoming[param.first] = IncomingValues(f, blockId, position);
            }
            for (auto &inst : block.insts) if (GirDefinesValue(inst)) definitions[inst.res] = &inst;
        }
        vector<char> open(fn.nvalues, 0);
        function<optional<int64_t>(int)> upper = [&](int value) -> optional<int64_t> {
            if (value < 0 || value >= fn.nvalues || open[value]) return nullopt;
            open[value] = 1;
            auto done = [&](optional<int64_t> bound) { open[value] = 0; return bound; };
            auto *definition = definitions[value];
            if (!definition) {
                if (incoming[value].empty()) return done(nullopt);
                int64_t bound = 0;
                for (auto source : incoming[value]) {
                    auto candidate = upper(source);
                    if (!candidate) return done(nullopt);
                    bound = max(bound, *candidate);
                }
                return done(bound);
            }
            if (definition->op == GirOp::Int) {
                int64_t number = -1;
                auto &text = definition->text;
                auto parsed = from_chars(text.data(), text.data() + text.size(), number);
                return done(parsed.ec == errc() && parsed.ptr == text.data() + text.size() && number >= 0
                                ? optional<int64_t>(number) : nullopt);
            }
            if (definition->op == GirOp::Format) return done(32);
            if (definition->op == GirOp::Conv && m.Type(definition->ty).kind == CoreType::Int &&
                m.Type(definition->ty2).kind == CoreType::Int &&
                GirPreservesAll(m.Type(definition->ty).ity, m.Type(definition->ty2).ity))
                return done(upper(definition->a));
            if (definition->op == GirOp::Bin &&
                (definition->bin == CoreBinOp::Add || definition->bin == CoreBinOp::Mul)) {
                auto left = upper(definition->a), right = upper(definition->b);
                if (!left || !right) return done(nullopt);
                if (definition->bin == CoreBinOp::Add)
                    return done(*left <= INT64_MAX - *right ? optional<int64_t>(*left + *right) : nullopt);
                return done(*right == 0 || *left <= INT64_MAX / *right
                                ? optional<int64_t>(*left * *right) : nullopt);
            }
            return done(nullopt);
        };
        struct Region { int64_t available; bool writable; };
        vector<char> pointerOpen(fn.nvalues, 0);
        function<optional<Region>(int)> region = [&](int value) -> optional<Region> {
            if (value < 0 || value >= fn.nvalues || pointerOpen[value]) return nullopt;
            pointerOpen[value] = 1;
            auto done = [&](optional<Region> result) { pointerOpen[value] = 0; return result; };
            auto *definition = definitions[value];
            if (!definition) {
                if (incoming[value].empty()) return done(nullopt);
                optional<Region> merged;
                for (auto source : incoming[value]) {
                    auto next = region(source);
                    if (!next) return done(nullopt);
                    if (!merged) merged = next;
                    else { merged->available = min(merged->available, next->available); merged->writable &= next->writable; }
                }
                return done(merged);
            }
            if (definition->op == GirOp::StaticBytes)
                return done(Region { (int64_t)definition->bytes.size(), false });
            if (definition->op == GirOp::FrameAddr) {
                auto &member = f.members[definition->idx];
                if (member.kind == GirMember::Bytes) return done(Region { member.size, true });
                return done(nullopt);
            }
            if (definition->op == GirOp::PtrOffset && definition->idx >= 0) {
                auto base = region(definition->a);
                auto count = upper(definition->b);
                if (!base || !count || (definition->idx > 0 && *count > INT64_MAX / definition->idx))
                    return done(nullopt);
                auto offset = *count * definition->idx;
                return done(offset <= base->available
                                ? optional<Region>(Region { base->available - offset, base->writable }) : nullopt);
            }
            return done(nullopt);
        };
        auto allocatedOutput = [&](int blockId, const GirInst &output) {
            auto *start = definitions[output.a];
            if (!start || start->op != GirOp::StackMark) return false;
            auto guarded = false;
            auto bound = upper(output.b);
            if (bound) guarded = true;
            for (auto &predecessor : f.blocks) {
                auto *term = LastTerm(predecessor);
                if (!term || term->op != GirOp::CondBr || term->idx != blockId || !term->vals.empty()) continue;
                auto *condition = definitions[term->a];
                if (!condition || condition->op != GirOp::Cmp || condition->cmp != CoreCmpOp::Ge ||
                    condition->a != output.b || upper(condition->b) != optional<int64_t>(0)) continue;
                auto *failure = LastTerm(f.blocks[term->idx2]);
                if (failure && failure->op == GirOp::Abort) guarded = true;
            }
            if (!guarded) return false;
            bool marked = false, allocated = false;
            for (auto &instruction : f.blocks[blockId].insts) {
                if (&instruction == &output) return marked && allocated;
                if (&instruction == start) marked = true;
                if (instruction.op == GirOp::StackBump && instruction.a == start->a) {
                    if (!marked || allocated || instruction.b != output.b) return false;
                    allocated = true;
                }
                if (instruction.op == GirOp::StackRelease && instruction.a == start->a) return false;
                if (instruction.op == GirOp::Call) return false;
            }
            return false;
        };
        for (auto &block : f.blocks) for (auto &inst : block.insts) {
            if (inst.op == GirOp::OutBytes) {
                auto source = region(inst.a);
                auto count = upper(inst.b);
                if ((!source || !count || *count > source->available) &&
                    !allocatedOutput((int)(&block - f.blocks.data()), inst))
                    Fail("GIR-V090", cat(fn.label, ": byte output interval is not proven live and nonnegative"));
            }
            if (inst.op == GirOp::Format) {
                auto destination = region(inst.b);
                if (!destination || !destination->writable || destination->available < 32)
                    Fail("GIR-V090", cat(fn.label, ": scalar formatting exceeds its writable byte interval"));
            }
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
                } else if (r.kind == CoreRootRef::Param && (r.index < 0 || r.index >= (int)f.params.size())) {
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
        if (((CoreHasConstruction(m.profile) && !m.low) || !f.roots.results.empty()) && f.roots.results.size() != f.results.size())
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
            case GirOp::Call: case GirOp::CallConstruct: case GirOp::Invoke:
                if (i.idx < 0 || i.idx >= (int)m.funcs.size())
                    SymbolFail(fn, cat("function ", i.idx, " is outside the function table"));
                if (i.op == GirOp::Invoke)
                    for (auto block : Successors(i))
                        if (block < 0 || block >= (int)f.blocks.size())
                            SymbolFail(fn, "invoke successor is outside the block table");
                break;
            case GirOp::DestOpen:
                if (auto slot = get_if<GirDestSlotReceiver>(&i.destReceiver))
                    if (slot->slot < 0 || slot->slot >= (int)f.slots.size())
                        SymbolFail(fn, cat("destination slot ", slot->slot, " is outside the slot table"));
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
                    GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members, &f.blocks, &f };
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
        GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members, &f.blocks, &f };
        GirTyper ty(env);
        auto need = [&](GirTyResult r) {
            if (!r.ok()) TypeFail(fn, r.error);
            return r.ty;
        };
        switch (i.op) {
            case GirOp::Init: {
                auto v = need(ty.Data(i.a));
                auto alias = false;
                if (CoreHasConstruction(m.profile) && GirNonfixed(m, f.slots[i.idx].ty))
                    for (size_t parameter = 0; parameter < f.params.size(); parameter++)
                        alias |= f.params[parameter] == f.slots[i.idx].ty && f.blocks[0].params[parameter].first == i.a &&
                                 v == m.RefType(CoreMut::Mut, f.slots[i.idx].ty);
                if (v != f.slots[i.idx].ty && !alias)
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
                if (carrier.kind != CoreType::Dest)
                    TypeFail(fn, "byte initialization does not use an open destination");
                auto &owner = m.Type(carrier.elem);
                if (!GirArrayKind(owner.kind) || m.Type(owner.elem).kind != CoreType::Int ||
                    m.Type(owner.elem).ity != CoreIntTy::U8)
                    TypeFail(fn, "byte initialization requires a grow-only u8 array");
                break;
            }
            case GirOp::DestWrite: {
                if (m.low || !CoreHasConstruction(m.profile))
                    TypeFail(fn, "element construction outside core-construction GIR-H");
                auto destination = need(ty.Val(i.a));
                auto &carrier = m.Type(destination);
                if (carrier.kind != CoreType::Dest)
                    TypeFail(fn, "element write does not use an open destination");
                auto &owner = m.Type(carrier.elem);
                if (!GirArrayKind(owner.kind) || !GirFlat(m, owner.elem))
                    TypeFail(fn, "element write requires a fixed element");
                if (need(ty.Data(i.b)) != owner.elem)
                    TypeFail(fn, "constructed element has another type than the destination element");
                break;
            }
            case GirOp::DestPublish: {
                if (m.low || !CoreHasConstruction(m.profile))
                    TypeFail(fn, "construction publication outside core-construction GIR-H");
                auto completed = need(ty.Val(i.a));
                auto &carrier = m.Type(completed);
                if (carrier.kind != CoreType::Built)
                    TypeFail(fn, "publication does not consume a completion");
                break;
            }
            case GirOp::DestCancel:
                if (m.low || !CoreHasConstruction(m.profile) ||
                    m.Type(need(ty.Val(i.a))).kind != CoreType::Cancelled)
                    TypeFail(fn, "cancellation does not consume an abandonment certificate");
                break;
            case GirOp::DestAttach: {
                auto &parent = m.Type(need(ty.Val(i.a)));
                auto &child = m.Type(need(ty.Val(i.b)));
                if (parent.kind != CoreType::Dest || child.kind != CoreType::Built ||
                    child.request != CoreRequest::Value || m.Type(parent.elem).elem != child.elem)
                    TypeFail(fn, "nested completion does not match the parent element");
                break;
            }
            case GirOp::DestText: {
                auto &carrier = m.Type(need(ty.Val(i.a)));
                if (carrier.kind != CoreType::Dest || !GirArrayKind(m.Type(carrier.elem).kind) ||
                    m.Type(m.Type(carrier.elem).elem).kind != CoreType::Int ||
                    m.Type(m.Type(carrier.elem).elem).ity != CoreIntTy::U8)
                    TypeFail(fn, "text construction does not name a u8 destination");
                auto &rendered = m.Type(need(ty.Val(i.b)));
                if (rendered.kind != CoreType::Int && rendered.kind != CoreType::Bool &&
                    rendered.kind != CoreType::View && !GirFlat(m, need(ty.Data(i.b))))
                    TypeFail(fn, "text operand is not a supported scalar or sampled value");
                break;
            }
            case GirOp::DestCopy: {
                auto &carrier = m.Type(need(ty.Val(i.a)));
                auto &source = m.Type(need(ty.Val(i.b)));
                if (carrier.kind != CoreType::Dest || (source.kind != CoreType::Ref && source.kind != CoreType::View))
                    TypeFail(fn, "construction copy lacks an open destination and stored source");
                auto sourceType = source.kind == CoreType::Ref ? source.elem : -1;
                if (sourceType != carrier.elem &&
                    (source.kind == CoreType::View ? source.elem != m.Type(carrier.elem).elem :
                     !GirArrayKind(m.Type(sourceType).kind) || m.Type(sourceType).elem != m.Type(carrier.elem).elem))
                    TypeFail(fn, "construction copy changes the element type");
                break;
            }
            case GirOp::DestRepeat: {
                auto &destination = m.Type(need(ty.Val(i.a)));
                auto &source = m.Type(need(ty.Val(i.b)));
                if (destination.kind != CoreType::Dest || source.kind != CoreType::Built ||
                    source.request != CoreRequest::Value || m.Type(destination.elem).kind != CoreType::Arr ||
                    m.Type(destination.elem).elem != source.elem)
                    TypeFail(fn, "repeat source does not match the fixed-count destination element");
                break;
            }
            case GirOp::DestSnapshot: {
                auto &destination = m.Type(need(ty.Val(i.a)));
                auto snapshot = need(ty.Data(i.b));
                if (destination.kind != CoreType::Dest || m.Type(snapshot).kind != CoreType::Arr ||
                    !GirFlat(m, snapshot) || m.Type(destination.elem).elem != m.Type(snapshot).elem)
                    TypeFail(fn, "fixed snapshot does not match destination elements");
                break;
            }
            case GirOp::DestBind: {
                auto &carrier = m.Type(need(ty.Val(i.a)));
                bool matches = false;
                for (size_t result = 0; result < f.resultProtocols.size(); result++)
                    matches |= f.resultProtocols[result].namedSlot == i.idx && f.results[result] == carrier.elem;
                if (carrier.kind != CoreType::Built || carrier.request != CoreRequest::Value || i.idx < 0 ||
                    i.idx >= (int)f.slots.size() || !matches)
                    TypeFail(fn, "named binding does not consume its receiving channel completion");
                break;
            }
            case GirOp::AppendValue: {
                auto reference = need(ty.Ref(i.a));
                auto &owner = m.Type(m.Type(reference).elem);
                auto snapshot = need(ty.Data(i.b));
                if (!GirOwnerKind(owner.kind) || m.Type(snapshot).kind != CoreType::Arr ||
                    !GirFlat(m, snapshot) || m.Type(snapshot).elem != owner.elem)
                    TypeFail(fn, "fixed append snapshot does not match its owner elements");
                break;
            }
            case GirOp::PStore: {
                need(ty.PtrOf(i.a));
                auto v = need(ty.Data(i.b));
                if (v != i.ty) TypeFail(fn, "a store of a value of another type than the one stated");
                break;
            }
            case GirOp::SourceLeave: case GirOp::SourceCallPop: case GirOp::SourceResult: case GirOp::SourceGlobalSet: case GirOp::SourceTargetLeave: case GirOp::SourceTargetResult:
                need(ty.PtrOf(i.a)); break;
            case GirOp::SourceCopy:
                need(ty.PtrOf(i.a));
                if (need(ty.IntTy(i.b)) != m.IntType(CoreIntTy::I64)) TypeFail(fn, "copy destination identity is not i64");
                break;
            case GirOp::ReturnFlagSet:
                if (need(ty.Data(i.a)) != m.IntType(CoreIntTy::I64))
                    TypeFail(fn, "return discriminant is not i64");
                break;
            case GirOp::TargetStore:
                if (i.idx < 0 || i.idx >= (int)m.lowtargets.size() || i.idx2 < 0 ||
                    i.idx2 >= (int)m.lowtargets[i.idx].cells.size())
                    TypeFail(fn, "target cell outside the target table");
                if (need(ty.Data(i.a)) != m.lowtargets[i.idx].cells[i.idx2])
                    TypeFail(fn, "target cell store has another primitive type");
                break;
            case GirOp::OutBytes:
                need(ty.PtrOf(i.a));
                if (need(ty.IntTy(i.b)) != m.IntType(CoreIntTy::I64))
                    TypeFail(fn, "byte output count is not i64");
                break;
            case GirOp::Event: {
                if ((uint8_t)i.event > (uint8_t)GirEventKind::Abandon ||
                    (uint8_t)i.reason > (uint8_t)GirEventReason::CapacityCheck)
                    TypeFail(fn, "unknown construction event or reason");
                auto arity = i.event == GirEventKind::Write ? 2u : 1u;
                if (i.event == GirEventKind::Copy) {
                    if ((i.reason != GirEventReason::Storage && i.reason != GirEventReason::Repeat) ||
                        i.vals.size() < 2 || (i.reason == GirEventReason::Repeat && i.vals.size() != 2))
                        TypeFail(fn, "copy event has invalid source operands");
                } else if (i.vals.size() != arity) {
                    TypeFail(fn, "construction event has invalid operand count");
                }
                if (i.event == GirEventKind::Relocate) {
                    if (i.reason != GirEventReason::HeaderRemoval && i.reason != GirEventReason::ExitValue)
                        TypeFail(fn, "relocation event has an invalid reason");
                } else if (i.event == GirEventKind::Stage) {
                    if (i.reason != GirEventReason::CapacityCheck)
                        TypeFail(fn, "stage event has an invalid reason");
                } else if (i.event != GirEventKind::Copy && i.reason != GirEventReason::None) {
                    TypeFail(fn, "construction event carries an unexpected reason");
                }
                for (auto operand : i.vals)
                    if (need(ty.IntTy(operand)) != m.IntType(CoreIntTy::I64))
                        TypeFail(fn, "construction event operand is not i64");
                break;
            }
            case GirOp::LocalSet: {
                if (i.idx < 0 || i.idx >= (int)f.members.size() ||
                    (f.members[i.idx].kind != GirMember::Scalar && f.members[i.idx].kind != GirMember::Dynamic))
                    TypeFail(fn, cat("frame member ", i.idx, " is not a scalar of the frame"));
                if (need(ty.Data(i.a)) != (f.members[i.idx].kind == GirMember::Dynamic ? m.PtrType() : f.members[i.idx].ty))
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
                    auto t = need(ty.Val(p.val));
                    auto k = m.Type(t).kind;
                    if (k != CoreType::Int && k != CoreType::Bool &&
                        !(CoreHasConstruction(m.profile) && k == CoreType::View &&
                          m.Type(t).mut == CoreMut::Const && m.Type(m.Type(t).elem).kind == CoreType::Int &&
                          m.Type(m.Type(t).elem).ity == CoreIntTy::U8))
                        TypeFail(fn, "a printed value is not a scalar or rendered byte snapshot");
                }
                break;
            default: break;
        }
    }

    void CheckTermTypes(const Fn &fn, const GirInst &i) {
        auto &f = *fn.f;
        GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members, &f.blocks, &f };
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
                    if (need(m.low || !CoreHasConstruction(m.profile) || !GirNonfixed(m, f.results[k])
                                 ? ty.Data(i.vals[k]) : ty.Val(i.vals[k])) !=
                        (!m.low && CoreHasConstruction(m.profile) && GirNonfixed(m, f.results[k])
                             ? m.CarrierType(CoreType::Built, f.results[k], f.resultProtocols[k].request)
                             : f.results[k]))
                        TypeFail(fn, "a returned value of another type than the result");
                break;
            case GirOp::Exit: need(ty.IntTy(i.a)); break;
            case GirOp::Invoke: {
                auto call = i;
                auto &callee = m.funcs[i.idx];
                bool constructing = false;
                for (auto result : callee.results) constructing |= GirNonfixed(m, result);
                call.op = constructing ? GirOp::CallConstruct : GirOp::Call;
                need(ty.Of(call));
                break;
            }
            case GirOp::Escape: {
                if (i.idx < 0 || i.idx >= (int)m.targets.size()) TypeFail(fn, "escape target is outside the table");
                auto &target = m.funcs[m.targets[i.idx].members[0]];
                auto types = ConstructionResultTypes(target);
                if (i.vals.size() != types.size()) TypeFail(fn, "escape result carrier count differs from the target");
                for (size_t result = 0; result < types.size(); result++)
                    if (need(ty.Val(i.vals[result])) != types[result]) TypeFail(fn, "escape result type or request differs");
                size_t cancellation = 0;
                for (size_t result = 0; result < f.results.size(); result++) {
                    if (!GirNonfixed(m, f.results[result])) continue;
                    if (cancellation >= i.vals2.size() ||
                        need(ty.Val(i.vals2[cancellation++])) !=
                            m.CarrierType(CoreType::Cancelled, f.results[result], f.resultProtocols[result].request))
                        TypeFail(fn, "escape cancellation does not match its normal result channel");
                }
                if (cancellation != i.vals2.size()) TypeFail(fn, "escape has extra normal-channel cancellations");
                break;
            }
            default: break;
        }
    }

    void CheckTypes(const Fn &fn) {
        auto &f = *fn.f;
        if (!f.resultProtocols.empty() &&
            (m.low || !CoreHasConstruction(m.profile) || f.resultProtocols.size() != f.results.size()))
            TypeFail(fn, "result protocol descriptors do not match the high construction signature");
        set<int> aliases;
        vector<GirTypeId> entryTypes;
        for (auto type : f.params)
            entryTypes.push_back(!m.low && CoreHasConstruction(m.profile) && GirNonfixed(m, type)
                                     ? m.RefType(CoreMut::Mut, type) : type);
        for (size_t result = 0; result < f.results.size() && !m.low && CoreHasConstruction(m.profile); result++) {
            auto type = f.results[result];
            auto protocol = f.resultProtocols.empty() ? GirResultProtocol {} : f.resultProtocols[result];
            if (GirNonfixed(m, type)) {
                if (f.resultProtocols.empty() || !GirConstructible(m, type) ||
                    (protocol.request != CoreRequest::Value && protocol.request != CoreRequest::ElementRun))
                    TypeFail(fn, "nonfixed result omits a constructible request descriptor");
                entryTypes.push_back(m.CarrierType(CoreType::Dest, type, protocol.request));
            } else if (protocol.request != CoreRequest::Register || protocol.namedSlot) {
                TypeFail(fn, "fixed result has a nonregister request or named alias");
            }
            if (protocol.namedSlot) {
                auto slot = *protocol.namedSlot;
                if (protocol.request != CoreRequest::Value || !GirNonfixed(m, type) || slot < 0 ||
                    slot >= (int)f.slots.size() || !aliases.insert(slot).second)
                    TypeFail(fn, "named result slot aliases an invalid or repeated value channel");
                auto local = f.slots[slot].ty;
                bool sameLayout = local == type || (m.Type(type).kind == CoreType::VarArr &&
                    GirResizableKind(m.Type(local).kind) && m.Type(local).elem == m.Type(type).elem);
                if (!sameLayout)
                    TypeFail(fn, "named result slot aliases an invalid or repeated value channel");
            }
        }
        {
            auto &b0 = f.blocks[0];
            bool same = b0.params.size() == entryTypes.size();
            for (size_t k = 0; same && k < entryTypes.size(); k++) same = b0.params[k].second == entryTypes[k];
            if (!same) TypeFail(fn, "the parameters of block 0 are not the function's parameters");
        }
        for (auto param : f.params)
            if (GirOwnerKind(m.Type(param).kind) && !CoreHasConstruction(m.profile))
                TypeFail(fn, "a nonfixed owner is a by-value parameter");
        if (CoreHasConstruction(m.profile) && !m.low)
            for (size_t parameter = 0; parameter < f.params.size(); parameter++) {
                if (!GirNonfixed(m, f.params[parameter])) continue;
                int bindings = 0;
                for (auto &inst : f.blocks[0].insts)
                    if (inst.op == GirOp::Init && inst.a == f.blocks[0].params[parameter].first &&
                        inst.idx == (int)parameter && f.slots[inst.idx].scope == 0 &&
                        f.slots[inst.idx].ty == f.params[parameter]) bindings++;
                if (bindings != 1) TypeFail(fn, "owned parameter does not bind exactly one local slot in block 0");
            }
        for (auto result : f.results)
            if (IsRefSlice(result))
                TypeFail(fn, "a reference-to-slice type is only valid for a parameter");
            else if (GirOwnerKind(m.Type(result).kind) && !fn.initializer && !CoreHasConstruction(m.profile))
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
                    GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members, &f.blocks, &f };
                    auto r = GirTyper(env).Of(i);
                    if (!r.ok()) TypeFail(fn, r.error);
                    if (fn.vt[i.res] != r.ty) TypeFail(fn, cat("value %", i.res, " has two types"));
                } else if (i.op == GirOp::Call) {
                    // A call with no result in the low stage.
                    GirTyEnv env { m, f.slots, sigs, fn.vt, &f.members, &f.blocks, &f };
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

    vector<GirTypeId> ConstructionResultTypes(const GirFunc &function) {
        vector<GirTypeId> types;
        for (size_t result = 0; result < function.results.size(); result++) {
            auto type = function.results[result];
            types.push_back(GirNonfixed(m, type)
                                ? m.CarrierType(CoreType::Built, type, function.resultProtocols[result].request)
                                : type);
        }
        return types;
    }

    void CheckInvokeEdge(const Fn &fn, int to, const vector<GirTypeId> &leading, const vector<int> &forwarded) {
        auto &params = fn.f->blocks[to].params;
        if (params.size() != leading.size() + forwarded.size())
            CfgFail(fn, "invoke successor has the wrong number of implicit and forwarded carriers");
        for (size_t position = 0; position < leading.size(); position++)
            if (params[position].second != leading[position])
                CfgFail(fn, "invoke successor has another implicit carrier type or request");
        for (size_t position = 0; position < forwarded.size(); position++)
            if (params[leading.size() + position].second != fn.vt[forwarded[position]])
                CfgFail(fn, "invoke successor has another forwarded operand type");
    }

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
                if ((i.op == GirOp::Call || i.op == GirOp::CallConstruct) && i.idx >= 0 && i.idx < (int)mayReturn.size() && !mayReturn[i.idx]) {
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
                    case GirOp::Invoke:
                        if (mayReturn[i.idx]) work.push_back(i.a);
                        for (auto &edge : i.escapes) work.push_back(edge.block);
                        ended = true;
                        break;
                    case GirOp::Escape:
                        for (auto member : m.targets[i.idx].members)
                            if (&m.funcs[member] == &f) return true;
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
                    auto valid = false;
                    if (m.low && CoreHasConstruction(m.profile)) {
                        auto function = find_if(m.funcs.begin(), m.funcs.end(), [&](const GirFunc &candidate) { return &candidate == fn.f; });
                        auto block = find_if(fn.f->blocks.begin(), fn.f->blocks.end(), [&](const GirBlock &candidate) { return &candidate == &b; });
                        if (function != m.funcs.end() && block != fn.f->blocks.end())
                            valid = checkedTargetUnreachable.count({ (int)(function - m.funcs.begin()), (int)(block - fn.f->blocks.begin()) });
                    }
                    if (!valid && k > 0 && b.insts[k - 1].op == GirOp::Call) {
                        auto callee = b.insts[k - 1].idx;
                        valid = callee >= 0 && callee < (int)mayReturn.size() && !mayReturn[callee];
                    }
                    if (!valid && CoreHasConstruction(m.profile) && k == 0) {
                        bool reached = false;
                        valid = true;
                        auto destination = (int)(&b - fn.f->blocks.data());
                        for (auto &predecessor : fn.f->blocks) {
                            auto term = LastTerm(predecessor);
                            if (!term) continue;
                            auto successors = Successors(*term);
                            if (find(successors.begin(), successors.end(), destination) == successors.end()) continue;
                            reached = true;
                            valid &= term->op == GirOp::Invoke && term->a == destination && !mayReturn[term->idx];
                            for (auto &edge : term->escapes) if (edge.block == destination) valid = false;
                        }
                        valid &= reached;
                    }
                    if (!valid)
                        CfgFail(fn, "unreachable has no immediate call or invoke-normal proof that its callee cannot return");
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
            if (t->op == GirOp::Invoke) {
                auto &callee = m.funcs[t->idx];
                CheckInvokeEdge(fn, t->a, ConstructionResultTypes(callee), t->forwarded);
                for (auto &edge : t->escapes) {
                    if (edge.target < 0 || edge.target >= (int)m.targets.size())
                        CfgFail(fn, "invoke escape target is outside the target table");
                    auto types = ConstructionResultTypes(m.funcs[m.targets[edge.target].members[0]]);
                    for (size_t result = 0; result < callee.results.size(); result++)
                        if (GirNonfixed(m, callee.results[result]))
                            types.push_back(m.CarrierType(CoreType::Cancelled, callee.results[result],
                                                        callee.resultProtocols[result].request));
                    CheckInvokeEdge(fn, edge.block, types, edge.forwarded);
                }
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
                    case GirOp::DestOpen:
                        if (auto slot = get_if<GirDestSlotReceiver>(&i.destReceiver)) slotin(slot->slot);
                        break;
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
                    case GirOp::Ret: case GirOp::Escape:
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
        for (auto &b : f.blocks) for (auto &i : b.insts)
            if (i.op == GirOp::Call || i.op == GirOp::CallConstruct || i.op == GirOp::Invoke) {
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

    using ResultRootInfo = vector<vector<Roots>>;

    struct Prov {
        vector<Roots> slots, vals;
        vector<vector<Roots>> packs;
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
            if (!annotated) AddRoot(out, root);
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
            if (r.kind == CoreRootRef::Global || r.kind == CoreRootRef::Static) {
                AddRoot(out, r);
            } else if (r.kind == CoreRootRef::Local) {
                AddRoot(out, { CoreRootRef::Param, calleeParam });
            } else {
                auto annotated = ParamRoots(*caller.f, r.index);
                if (!annotated) {
                    AddRoot(out, { CoreRootRef::Param, calleeParam });
                } else {
                    for (auto &root : *annotated) {
                        if (root.kind == CoreRootRef::Global || root.kind == CoreRootRef::Static) AddRoot(out, root);
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
            } else if (r.kind == CoreRootRef::Global || r.kind == CoreRootRef::Static) {
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
            if (r.kind == CoreRootRef::Global || r.kind == CoreRootRef::Static) {
                AddRoot(out, r);
            } else if (r.kind == CoreRootRef::Param && r.index >= 0 && r.index < (int)args.size()) {
                AddRoots(out, RootsAt(p.vals, args[r.index]));
            }
        }
        return out;
    }

    void CheckRootAnnotations(const ResultRootInfo &res) {
        for (size_t k = 0; k < m.funcs.size(); k++) {
            auto &f = m.funcs[k];
            auto name = cat("function ", f.name);
            for (size_t r = 0; r < f.results.size(); r++) {
                auto declared = r < f.roots.results.size() ? &f.roots.results[r] : nullptr;
                for (auto &root : res[k][r])
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
                    if (i.op != GirOp::Call && i.op != GirOp::CallConstruct && i.op != GirOp::Invoke) continue;
                    auto &callee = m.funcs[i.idx];
                    auto label = cat("function ", callee.name);
                    for (size_t j = 0; j < callee.params.size(); j++) {
                        if (GirRefLike(m, callee.params[j])) {
                            auto expected = MapArgumentRoots(caller, p, i.vals[j], (int)j);
                            auto declared = ParamRoots(callee, (int)j);
                            bool generic = !declared || (declared->size() == 1 &&
                                (*declared)[0] == CoreRootRef { CoreRootRef::Param, (int)j });
                            for (auto &root : expected)
                                if (!generic && (!declared || find(declared->begin(), declared->end(), root) == declared->end()))
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

    Roots RootsOfDef(const ResultRootInfo &res, const Fn &fn, const Prov &p, const GirInst &i) {
        switch (i.op) {
            case GirOp::Bytes: return { CoreRootRef { CoreRootRef::Static, 0 } };
            case GirOp::DestOpen:
                if (auto slot = get_if<GirDestSlotReceiver>(&i.destReceiver)) return { CoreRootRef { CoreRootRef::Local, slot->slot } };
                if (auto global = get_if<GirDestGlobalReceiver>(&i.destReceiver)) return { CoreRootRef { CoreRootRef::Global, global->global } };
                if (auto whole = get_if<GirDestWholeReceiver>(&i.destReceiver)) return RootsAt(p.vals, whole->reference);
                if (auto append = get_if<GirDestAppendReceiver>(&i.destReceiver)) return RootsAt(p.vals, append->reference);
                if (auto push = get_if<GirDestPushReceiver>(&i.destReceiver)) return RootsAt(p.vals, push->reference);
                return {};
            case GirOp::DestFinish: case GirOp::DestAbandon: case GirOp::DestAdapt:
            case GirOp::DestAdaptFinish: case GirOp::DestValue: case GirOp::DestRelocate:
            case GirOp::DestStage: case GirOp::DestFit: case GirOp::DestPublishRef:
                return RootsAt(p.vals, i.a);
            case GirOp::DestNamed: return { CoreRootRef { CoreRootRef::Local, i.idx } };
            case GirOp::CallConstruct: {
                Roots roots;
                if (m.funcs[i.idx].results.size() == 1 && !i.vals2.empty()) return RootsAt(p.vals, i.vals2[0]);
                return roots;
            }
            case GirOp::Result:
                if (ValRefLike(fn, i.res) && i.idx < (int)p.packs[i.a].size()) return p.packs[i.a][i.idx];
                for (auto &block : fn.f->blocks) for (auto &producer : block.insts)
                    if (producer.res == i.a && producer.op == GirOp::CallConstruct &&
                        GirNonfixed(m, m.funcs[producer.idx].results[i.idx])) {
                        size_t position = 0;
                        for (int result = 0; result < i.idx; result++)
                            if (GirNonfixed(m, m.funcs[producer.idx].results[result])) position++;
                        return RootsAt(p.vals, producer.vals2[position]);
                    }
                return {};
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
                if (!ValRefLike(fn, i.res) || res[i.idx].size() != 1) return out;
                for (auto &r : res[i.idx][0]) {
                    if (r.kind == CoreRootRef::Param) {
                        if (r.index < (int)i.vals.size())
                            for (auto &x : RootsAt(p.vals, i.vals[r.index]))
                                if (find(out.begin(), out.end(), x) == out.end()) out.push_back(x);
                    } else if (r.kind == CoreRootRef::Global || r.kind == CoreRootRef::Static) {
                        if (find(out.begin(), out.end(), r) == out.end()) out.push_back(r);
                    }
                }
                return out;
            }
            default: return {};
        }
    }

    bool ProvRound(const ResultRootInfo &res, const Fn &fn, Prov &p) {
        auto &f = *fn.f;
        auto changed = false;
        auto edge = [&](int b, const vector<int> &args) {
            auto &tb = f.blocks[b];
            for (size_t k = 0; k < tb.params.size() && k < args.size(); k++) {
                changed |= AddTo(p.vals, tb.params[k].first, RootsAt(p.vals, args[k]));
                for (size_t result = 0; result < p.packs[args[k]].size(); result++)
                    changed |= AddTo(p.packs[tb.params[k].first], (int)result, p.packs[args[k]][result]);
            }
        };
        for (auto &blk : f.blocks)
            for (auto &i : blk.insts) {
                if (GirDefinesValue(i)) {
                    changed |= AddTo(p.vals, i.res, RootsOfDef(res, fn, p, i));
                    if ((i.op == GirOp::Call || i.op == GirOp::CallConstruct) && m.funcs[i.idx].results.size() > 1)
                        for (size_t result = 0; result < res[i.idx].size(); result++) {
                            Roots mapped;
                            for (auto &root : res[i.idx][result]) {
                                if (root.kind == CoreRootRef::Param && root.index < (int)i.vals.size())
                                    AddRoots(mapped, RootsAt(p.vals, i.vals[root.index]));
                                else if (root.kind == CoreRootRef::Global || root.kind == CoreRootRef::Static) AddRoot(mapped, root);
                            }
                            changed |= AddTo(p.packs[i.res], (int)result, mapped);
                        }
                }
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
        p.packs.resize(fn.nvalues);
        for (int value = 0; value < fn.nvalues; value++)
            if (fn.vt[value] >= 0 && m.Type(fn.vt[value]).kind == CoreType::Tuple)
                p.packs[value].resize(m.Type(fn.vt[value]).parts.size());
        auto &b0 = f.blocks[0];
        for (size_t k = 0; k < b0.params.size(); k++)
            if (ValRefLike(fn, b0.params[k].first) && b0.params[k].first < fn.nvalues) {
                CoreRootRef root { CoreRootRef::Param, (int)k };
                if (CoreHasConstruction(m.profile) && k < f.params.size() && GirNonfixed(m, f.params[k]))
                    for (auto &instruction : b0.insts)
                        if (instruction.op == GirOp::Init && instruction.a == b0.params[k].first)
                            root = { CoreRootRef::Local, instruction.idx };
                p.vals[b0.params[k].first] = { root };
            }
        return p;
    }

    Prov Provenance(const ResultRootInfo &res, const Fn &fn) {
        auto p = ProvStart(fn);
        while (ProvRound(res, fn, p)) {}
        return p;
    }

    vector<Roots> ReturnedRoots(const Fn &fn, const Prov &p) {
        vector<Roots> out(fn.f->results.size());
        for (auto &block : fn.f->blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::Ret)
                for (size_t result = 0; result < inst.vals.size(); result++)
                    if (GirRefLike(m, fn.f->results[result])) AddRoots(out[result], RootsAt(p.vals, inst.vals[result]));
        return out;
    }

    ResultRootInfo ResultRoots() {
        ResultRootInfo res(m.funcs.size());
        for (size_t function = 0; function < m.funcs.size(); function++) res[function].resize(m.funcs[function].results.size());
        for (auto changed = true; changed;) {
            changed = false;
            auto next = res;
            for (size_t function = 0; function < m.funcs.size(); function++) {
                auto roots = ReturnedRoots(fns[function], Provenance(res, fns[function]));
                for (size_t result = 0; result < roots.size(); result++) changed |= AddTo(next[function], (int)result, roots[result]);
            }
            res = std::move(next);
        }
        return res;
    }

    struct Eff {
        set<CoreTarget> reads, writes, grows, shrinks, rebinds;
        set<int> constructs;
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
                    case GirOp::Ret:
                        for (size_t result = 0; result < i.vals.size(); result++)
                            if (CoreHasConstruction(m.profile) && GirNonfixed(m, f.results[result]))
                                e.constructs.insert((int)result);
                        break;
                    case GirOp::DestCopy:
                        AddTargets(e.reads, RootsAt(p.vals, i.b));
                        break;
                    case GirOp::DestPublish: case GirOp::DestPublishRef:
                        AddTargets(e.writes, RootsAt(p.vals, i.a));
                        AddTargets(e.grows, RootsAt(p.vals, i.a));
                        break;
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
                    case GirOp::Call: case GirOp::CallConstruct: case GirOp::Invoke: {
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
            auto e = Effects(fns[k], Provenance(res, fns[k]));
            auto name = cat("function ", f.name);
            if (e.unknown)
                Fail("GIR-V050", cat(name, " calls a function whose summary is unknown, so its own summary cannot be known"));
            auto normalize = [&](const auto &targets, bool binding) {
                set<CoreTarget> normalized;
                if (binding) { normalized.insert(targets.begin(), targets.end()); return normalized; }
                for (auto &target : targets) {
                    if (target.global) normalized.insert(target);
                    else AddTargets(normalized, ExpandParameterRoots(f, { CoreRootRef { CoreRootRef::Param, target.index } }));
                }
                return normalized;
            };
            auto within = [&](const char *what, const set<CoreTarget> &found, const vector<CoreTarget> &declared, bool binding = false) {
                auto actual = normalize(found, binding), covered = normalize(declared, binding);
                for (auto &target : actual)
                    if (!covered.count(target))
                        Fail("GIR-V050", cat(name, " ", what, " ", target.global ? "global " : "parameter ", target.index,
                                              ", which its summary omits"));
            };
            within("reads", e.reads, f.summary.reads);
            within("writes", e.writes, f.summary.writes);
            within("grows", e.grows, f.summary.grows);
            within("shrinks", e.shrinks, f.summary.shrinks);
            within("rebinds", e.rebinds, f.summary.rebinds, true);
            for (auto result : e.constructs)
                if (find(f.summary.constructs.begin(), f.summary.constructs.end(), result) == f.summary.constructs.end())
                    Fail("GIR-V050", cat(name, " completes result ", result, ", which its summary omits"));
            if (e.aborts && !f.summary.aborts) Fail("GIR-V050", cat(name, " may abort, which its summary omits"));
            if (e.outputs && !f.summary.outputs) Fail("GIR-V050", cat(name, " prints, which its summary omits"));
        }
    }

    // --- GIR-V060 ---------------------------------------------------------
    void CheckConstructionTargets() {
        constructionNeeds.assign(fns.size(), {});
        constructionEscapes.assign(fns.size(), {});
        auto handles = [&](size_t function, int target) {
            auto &members = m.targets[target].members;
            return function < m.funcs.size() && find(members.begin(), members.end(), (int)function) != members.end();
        };
        for (size_t function = 0; function < fns.size(); function++) {
            auto &f = *fns[function].f;
            auto validate = [&](const vector<int> &targets, const char *name) {
                if (!is_sorted(targets.begin(), targets.end()) ||
                    adjacent_find(targets.begin(), targets.end()) != targets.end())
                    Fail("GIR-V001", cat(fns[function].label, ": repeated or unsorted ", name));
                for (auto target : targets)
                    if (target < 0 || target >= (int)m.targets.size())
                        Fail("GIR-V001", cat(fns[function].label, ": ", name, " target is outside the table"));
            };
            validate(f.summary.needs, "required");
            validate(f.summary.escapes, "escape");
            if (!is_sorted(f.summary.constructs.begin(), f.summary.constructs.end()) ||
                adjacent_find(f.summary.constructs.begin(), f.summary.constructs.end()) != f.summary.constructs.end())
                Fail("GIR-V001", cat(fns[function].label, ": repeated or unsorted constructed results"));
            for (auto result : f.summary.constructs)
                if (result < 0 || result >= (int)f.results.size() || !GirNonfixed(m, f.results[result]))
                    Fail("GIR-V001", cat(fns[function].label, ": construction summary result is not a nonfixed channel"));
            for (auto &block : f.blocks) for (auto &inst : block.insts) {
                if (inst.op != GirOp::TargetDest && inst.op != GirOp::Escape) continue;
                if (inst.idx < 0 || inst.idx >= (int)m.targets.size())
                    Fail("GIR-V001", cat(fns[function].label, ": target operation is outside the target table"));
                if (!handles(function, inst.idx)) constructionNeeds[function].insert(inst.idx);
                if (inst.op == GirOp::Escape) {
                    if (handles(function, inst.idx))
                        Fail("GIR-V060", cat(fns[function].label, ": a target member propagates instead of catching"));
                    constructionEscapes[function].insert(inst.idx);
                }
            }
        }
        for (bool changed = true; changed;) {
            changed = false;
            for (size_t function = 0; function < fns.size(); function++)
                for (auto &block : fns[function].f->blocks) for (auto &inst : block.insts) {
                    if (inst.op != GirOp::Call && inst.op != GirOp::CallConstruct && inst.op != GirOp::Invoke) continue;
                    auto needs = constructionNeeds[inst.idx];
                    auto escapes = constructionEscapes[inst.idx];
                    auto &callee = m.funcs[inst.idx];
                    needs.insert(callee.summary.needs.begin(), callee.summary.needs.end());
                    if (callee.summary.unknown)
                        for (size_t target = 0; target < m.targets.size(); target++) {
                            needs.insert((int)target);
                            escapes.insert((int)target);
                        }
                    for (auto target : needs)
                        if (!handles(function, target))
                            changed |= constructionNeeds[function].insert(target).second;
                    for (auto target : escapes)
                        if (!handles(function, target))
                            changed |= constructionEscapes[function].insert(target).second;
                }
        }
        for (size_t function = 0; function < fns.size(); function++) {
            auto &f = *fns[function].f;
            if (!f.summary.unknown) {
                for (auto target : constructionNeeds[function])
                    if (find(f.summary.needs.begin(), f.summary.needs.end(), target) == f.summary.needs.end())
                        Fail("GIR-V050", cat(fns[function].label, ": body requires a target omitted by its summary"));
                for (auto target : constructionEscapes[function])
                    if (find(f.summary.escapes.begin(), f.summary.escapes.end(), target) == f.summary.escapes.end())
                        Fail("GIR-V050", cat(fns[function].label, ": body escapes to a target omitted by its summary"));
            }
            if (function == (size_t)m.entry || fns[function].initializer) {
                if (!constructionNeeds[function].empty() || !f.summary.needs.empty())
                    Fail("GIR-V060", cat(fns[function].label, ": external target requirement has no enclosing activation"));
            }
            for (auto &block : f.blocks) for (auto &inst : block.insts) {
                if (inst.op != GirOp::Call && inst.op != GirOp::CallConstruct && inst.op != GirOp::Invoke) continue;
                auto possible = constructionEscapes[inst.idx];
                auto &callee = m.funcs[inst.idx];
                possible.insert(callee.summary.escapes.begin(), callee.summary.escapes.end());
                if (callee.summary.unknown)
                    for (size_t target = 0; target < m.targets.size(); target++) possible.insert((int)target);
                if (inst.op != GirOp::Invoke && !possible.empty())
                    Fail("GIR-V060", cat(fns[function].label, ": normal-only call can propagate a target"));
                if (inst.op == GirOp::Invoke) {
                    vector<int> actual;
                    for (auto &edge : inst.escapes) actual.push_back(edge.target);
                    if (actual != vector<int>(possible.begin(), possible.end()))
                        Fail("GIR-V060", cat(fns[function].label, ": invoke edges do not exactly cover the callee's possible targets"));
                }
            }
        }
    }

    void CheckConstruction(const Fn &fn) {
        auto &f = *fn.f;
        auto bad = [&](const string &message) { Fail("GIR-V060", cat(fn.label, ": ", message)); };
        struct Ownership {
            int root = -1;
            int channel = -1;
            int target = -1;
            int parent = -1;
            int slot = -1;
            int pushReference = -1;
            int argumentFunction = -1;
            int argumentPosition = -1;
            int64_t count = 0;
            int64_t expected = -1;
            bool staged = false;
            bool valueAdapter = false;
            GirTypeId adaptedFrom = -1;
            bool replacement = false;
            bool landed = false;
            bool operator==(const Ownership &) const = default;
        };
        struct State {
            map<int, Ownership> live;
            map<int, Ownership> named;
            map<pair<int, int>, Ownership> packed;
            map<int, Ownership> arguments;
            set<int> rendered;
            bool operator==(const State &) const = default;
        };
        vector<const GirInst *> definitions(fn.nvalues, nullptr);
        for (auto &block : f.blocks) for (auto &inst : block.insts)
            if (GirDefinesValue(inst)) definitions[inst.res] = &inst;
        auto carrier = [&](int value) {
            auto kind = m.Type(fn.vt[value]).kind;
            return kind == CoreType::Dest || kind == CoreType::Built || kind == CoreType::Cancelled;
        };
        auto constant = [&](int value) -> int64_t {
            if (value < 0 || value >= fn.nvalues || !definitions[value] || definitions[value]->op != GirOp::Int)
                return -1;
            auto &text = definitions[value]->text;
            int64_t n = -1;
            auto parsed = from_chars(text.data(), text.data() + text.size(), n);
            return parsed.ec == errc() && parsed.ptr == text.data() + text.size() ? n : -1;
        };
        auto fixedCount = [&](GirTypeId type) -> int64_t {
            auto &array = m.Type(type);
            return array.kind == CoreType::Arr ? array.count : -1;
        };
        for (auto &block : f.blocks) for (auto &inst : block.insts) {
            vector<int> uses;
            Uses(inst, uses);
            for (auto value : uses)
                if (definitions[value] && definitions[value]->op == GirOp::Render &&
                    !((inst.op == GirOp::Print) || (inst.op == GirOp::DestText && inst.b == value)))
                    bad("rendered print snapshot escapes its statement consumer");
        }
        State initial;
        size_t channel = f.params.size();
        for (size_t result = 0; result < f.results.size(); result++) {
            if (!GirNonfixed(m, f.results[result])) continue;
            auto value = f.blocks[0].params[channel++].first;
            Ownership owner;
            owner.root = value;
            owner.channel = (int)result;
            owner.expected = fixedCount(f.results[result]);
            initial.live[value] = owner;
        }
        auto handlesTarget = [&](int target) {
            if (target < 0 || target >= (int)m.targets.size()) return false;
            for (auto member : m.targets[target].members) if (&m.funcs[member] == &f) return true;
            return false;
        };
        auto sameChannel = [&](const Ownership &left, const Ownership &right) {
            return left.channel >= 0 && left.channel == right.channel &&
                   (left.target == right.target || (left.target < 0 && handlesTarget(right.target)) ||
                    (right.target < 0 && handlesTarget(left.target)));
        };
        vector<optional<State>> incoming(f.blocks.size());
        incoming[0] = initial;
        vector<int> work { 0 };
        auto merge = [&](int target, State next) {
            if (!incoming[target]) {
                incoming[target] = std::move(next);
                work.push_back(target);
                return;
            }
            auto combined = *incoming[target];
            if (combined.rendered != next.rendered) bad("control-flow merge changes unconsumed print snapshots");
            if (combined.live.size() != next.live.size() || combined.named.size() != next.named.size() ||
                combined.packed.size() != next.packed.size() || combined.arguments.size() != next.arguments.size())
                bad("control-flow merge changes outstanding destination ownership");
            auto mergeMap = [&](auto &left, const auto &right) {
                for (auto &[key, ownership] : left) {
                    auto found = right.find(key);
                    if (found == right.end()) bad("control-flow merge changes the owned carrier");
                    auto other = found->second;
                    if (ownership.count != other.count) ownership.count = other.count = -1;
                    if (!(ownership == other)) bad("control-flow merge changes the receiver or result channel");
                }
            };
            mergeMap(combined.live, next.live);
            mergeMap(combined.named, next.named);
            mergeMap(combined.packed, next.packed);
            mergeMap(combined.arguments, next.arguments);
            if (!(combined == *incoming[target])) {
                incoming[target] = std::move(combined);
                work.push_back(target);
            }
        };
        while (!work.empty()) {
            auto block = work.back();
            work.pop_back();
            auto state = *incoming[block];
            auto owned = [&](int value) -> Ownership & {
                auto found = state.live.find(value);
                if (found == state.live.end()) bad(cat("carrier %", value, " has already transferred or consumed its ownership"));
                return found->second;
            };
            auto ready = [&](int value) -> Ownership & {
                auto &ownership = owned(value);
                for (auto &[other, child] : state.live)
                    if (child.parent == ownership.root) bad("parent destination used while a child is incomplete");
                for (auto &[key, child] : state.packed)
                    if (child.parent == ownership.root) bad("parent destination used while a child completion is unprojected");
                return ownership;
            };
            auto consume = [&](int value) {
                auto ownership = ready(value);
                state.live.erase(value);
                return ownership;
            };
            auto transfer = [&](int from, int to) { auto ownership = consume(from); state.live[to] = ownership; };
            auto edge = [&](int target, const vector<int> &values) {
                auto next = state;
                set<int> consumed;
                vector<pair<int, Ownership>> translated;
                for (size_t position = 0; position < values.size(); position++) {
                    if (!carrier(values[position])) continue;
                    auto found = next.live.find(values[position]);
                    if (found == next.live.end() || !consumed.insert(values[position]).second)
                        bad("edge duplicates or transfers an unavailable carrier");
                    translated.push_back({ f.blocks[target].params[position].first, found->second });
                }
                for (auto value : consumed) next.live.erase(value);
                for (auto &entry : translated) next.live[entry.first] = entry.second;
                merge(target, std::move(next));
            };
            for (auto &inst : f.blocks[block].insts) {
                if ((inst.op == GirOp::Arr || inst.op == GirOp::Fill || inst.op == GirOp::Load) &&
                    GirDefinesValue(inst) && GirNonfixed(m, fn.vt[inst.res]))
                    bad("nonfixed value is materialized as a detached aggregate");
                switch (inst.op) {
                    case GirOp::DestOpen: {
                        Ownership owner;
                        owner.root = inst.res;
                        owner.expected = fixedCount(inst.ty);
                        if (inst.knownCount) {
                            auto count = constant(*inst.knownCount);
                            if (count < 0 && definitions[*inst.knownCount] &&
                                definitions[*inst.knownCount]->op == GirOp::Int)
                                bad("destination known count is negative or invalid");
                            if (owner.expected >= 0 && count >= 0 && owner.expected != count)
                                bad("destination known count differs from its fixed array length");
                            if (count >= 0) owner.expected = count;
                        }
                        if (auto slot = get_if<GirDestSlotReceiver>(&inst.destReceiver)) {
                            owner.slot = slot->slot;
                            for (auto &[value, live] : state.live)
                                if (live.slot == owner.slot) bad("receiver slot has another unfinished construction");
                        }
                        if (auto push = get_if<GirDestPushReceiver>(&inst.destReceiver)) owner.pushReference = push->reference;
                        if (auto argument = get_if<GirDestArgReceiver>(&inst.destReceiver)) {
                            owner.argumentFunction = argument->function;
                            owner.argumentPosition = argument->parameter;
                        }
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestChild: {
                        auto &parent = ready(inst.a);
                        Ownership child;
                        child.root = inst.res;
                        child.parent = parent.root;
                        child.expected = fixedCount(inst.ty);
                        state.live[inst.res] = child;
                        break;
                    }
                    case GirOp::DestWrite: {
                        auto &owner = ready(inst.a);
                        if (owner.count >= 0) owner.count++;
                        break;
                    }
                    case GirOp::DestBytes: {
                        auto &owner = ready(inst.a);
                        if (owner.count >= 0) owner.count += (int64_t)inst.bytes.size();
                        break;
                    }
                    case GirOp::Render:
                        state.rendered.insert(inst.res);
                        break;
                    case GirOp::Print:
                        for (auto &part : inst.parts)
                            if (!part.text && definitions[part.val] && definitions[part.val]->op == GirOp::Render &&
                                !state.rendered.erase(part.val)) bad("print consumes a rendered snapshot twice");
                        break;
                    case GirOp::DestText:
                        if (definitions[inst.b] && definitions[inst.b]->op == GirOp::Render && !state.rendered.erase(inst.b))
                            bad("text destination consumes a rendered snapshot twice");
                        ready(inst.a).count = -1;
                        break;
                    case GirOp::DestCopy:
                        ready(inst.a).count = -1;
                        break;
                    case GirOp::DestSnapshot: {
                        auto &owner = ready(inst.a);
                        if (owner.count >= 0) owner.count += m.Type(fn.vt[inst.b]).count;
                        break;
                    }
                    case GirOp::DestRepeat: {
                        auto source = consume(inst.b);
                        if (source.parent >= 0 || source.channel >= 0 || source.argumentFunction >= 0 || source.staged)
                            bad("repeat consumes a completion belonging to another receiver");
                        auto &owner = ready(inst.a);
                        if (owner.count != 0) bad("repeat destination already contains elements");
                        owner.count = m.Type(m.Type(fn.vt[inst.a]).elem).count;
                        break;
                    }
                    case GirOp::DestAttach: {
                        auto child = consume(inst.b);
                        auto &parent = ready(inst.a);
                        if (child.parent != parent.root) bad("child completion belongs to another parent destination");
                        if (parent.count >= 0) parent.count++;
                        break;
                    }
                    case GirOp::DestFinish: {
                        auto owner = consume(inst.a);
                        if (owner.expected >= 0 && owner.count >= 0 && owner.count != owner.expected)
                            bad("destination count disagrees with the initialized elements");
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestPublish: {
                        auto owner = consume(inst.a);
                        if (owner.channel >= 0 || owner.parent >= 0 || owner.argumentFunction >= 0 || owner.staged || owner.adaptedFrom >= 0)
                            bad("completion published at another owning receiver");
                        break;
                    }
                    case GirOp::DestPublishRef: {
                        auto owner = consume(inst.a);
                        if (owner.pushReference < 0 || owner.channel >= 0 || owner.parent >= 0 || owner.staged || owner.adaptedFrom >= 0)
                            bad("reference publication does not own a completed push receiver");
                        break;
                    }
                    case GirOp::DestAbandon:
                        transfer(inst.a, inst.res);
                        break;
                    case GirOp::DestCancel:
                        if (consume(inst.a).adaptedFrom >= 0) bad("producer cancellation has not restored its receiving protocol");
                        break;
                    case GirOp::DestBind: {
                        auto owner = consume(inst.a);
                        if (owner.adaptedFrom >= 0 || owner.channel < 0 || f.resultProtocols[owner.channel].namedSlot != inst.idx ||
                            state.named.count(inst.idx)) bad("named local does not own its declared incoming result channel");
                        owner.slot = inst.idx;
                        state.named[inst.idx] = owner;
                        break;
                    }
                    case GirOp::DestNamed: {
                        auto found = state.named.find(inst.idx);
                        if (found == state.named.end()) bad("named result ownership is unavailable");
                        state.live[inst.res] = found->second;
                        state.named.erase(found);
                        break;
                    }
                    case GirOp::ResultExitDest: {
                        if (inst.idx < 0 || inst.idx >= (int)f.results.size() || f.results[inst.idx] != inst.ty ||
                            f.resultProtocols[inst.idx].request != inst.request)
                            bad("replacement does not name this activation's result channel");
                        Ownership replacement;
                        replacement.root = inst.res;
                        replacement.channel = inst.idx;
                        replacement.expected = fixedCount(inst.ty);
                        replacement.replacement = true;
                        state.live[inst.res] = replacement;
                        break;
                    }
                    case GirOp::DestAbandonNamed: {
                        auto replacement = ready(inst.a);
                        auto found = state.named.find(inst.idx);
                        if (!replacement.replacement || found == state.named.end() ||
                            !sameChannel(replacement, found->second))
                            bad("named abandonment belongs to another replacement result channel");
                        state.live[inst.res] = found->second;
                        state.named.erase(found);
                        break;
                    }
                    case GirOp::DestAdapt: {
                        auto owner = consume(inst.a);
                        if (owner.count != 0 || owner.adaptedFrom >= 0 || owner.valueAdapter)
                            bad("destination adaptation begins after writes or inside another adapter");
                        owner.adaptedFrom = fn.vt[inst.a];
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestAdaptFinish: {
                        auto owner = consume(inst.a);
                        auto &restored = m.Type(fn.vt[inst.res]);
                        if (owner.adaptedFrom < 0 || owner.valueAdapter ||
                            m.Type(owner.adaptedFrom).elem != restored.elem ||
                            m.Type(owner.adaptedFrom).request != restored.request)
                            bad("producer completion or cancellation restores another receiving channel");
                        owner.adaptedFrom = -1;
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestValue: {
                        auto owner = consume(inst.a);
                        if (owner.count != 0 || owner.adaptedFrom >= 0) bad("value adapter begins after writes or during another adaptation");
                        owner.valueAdapter = true;
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestRelocate: {
                        auto owner = consume(inst.a);
                        if (inst.reason == GirEventReason::HeaderRemoval) {
                            if (!owner.valueAdapter || owner.adaptedFrom >= 0) bad("header removal has no restored value adapter");
                            owner.valueAdapter = false;
                        } else {
                            if (!owner.replacement || owner.landed) bad("exit landing has no pending replacement interval");
                            for (auto &[value, other] : state.live)
                                if (sameChannel(other, owner)) bad("exit landing precedes cancellation of the superseded channel");
                            for (auto &[slot, other] : state.named)
                                if (sameChannel(other, owner)) bad("exit landing precedes abandonment of the named result");
                            owner.landed = true;
                        }
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestStage: {
                        auto owner = consume(inst.a);
                        if (owner.staged || owner.expected >= 0 || owner.count != 0 || owner.adaptedFrom >= 0)
                            bad("capacity stage is repeated or has a known element count");
                        owner.staged = true;
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestFit: {
                        auto owner = consume(inst.a);
                        if (!owner.staged || owner.adaptedFrom >= 0) bad("capacity fit does not consume a restored private stage");
                        owner.staged = false;
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::DestArg: {
                        auto owner = consume(inst.a);
                        if (owner.adaptedFrom >= 0 || owner.argumentFunction < 0) bad("argument completion has no reserved call parameter region");
                        state.arguments[inst.res] = owner;
                        break;
                    }
                    case GirOp::Call: case GirOp::CallConstruct: {
                        auto &callee = m.funcs[inst.idx];
                        if (callee.summary.unknown || !callee.summary.escapes.empty())
                            bad("normal-only call can propagate an unhandled target");
                        for (size_t argument = 0; argument < inst.vals.size(); argument++) {
                            auto found = state.arguments.find(inst.vals[argument]);
                            if (GirNonfixed(m, callee.params[argument])) {
                                if (found == state.arguments.end() || found->second.argumentFunction != inst.idx ||
                                    found->second.argumentPosition != (int)argument)
                                    bad("nonfixed parameter does not own its associated argument region");
                                state.arguments.erase(found);
                            } else if (found != state.arguments.end()) bad("owned argument transferred to another source parameter");
                        }
                        size_t destination = 0;
                        for (size_t result = 0; result < callee.results.size(); result++) {
                            if (!GirNonfixed(m, callee.results[result])) continue;
                            if (inst.op != GirOp::CallConstruct) bad("ordinary call returns a detached nonfixed value");
                            auto owner = consume(inst.vals2[destination++]);
                            owner.count = -1;
                            if (callee.results.size() == 1) state.live[inst.res] = owner;
                            else state.packed[{ inst.res, (int)result }] = owner;
                        }
                        break;
                    }
                    case GirOp::Result:
                        if (carrier(inst.res)) {
                            auto found = state.packed.find({ inst.a, inst.idx });
                            if (found == state.packed.end()) bad("nonfixed result pack component projected twice or unavailable");
                            state.live[inst.res] = found->second;
                            state.packed.erase(found);
                        }
                        break;
                    case GirOp::Br: edge(inst.idx, inst.vals); break;
                    case GirOp::CondBr: edge(inst.idx, inst.vals); edge(inst.idx2, inst.vals2); break;
                    case GirOp::Ret:
                        for (size_t result = 0; result < inst.vals.size(); result++) {
                            if (!carrier(inst.vals[result])) continue;
                            auto owner = consume(inst.vals[result]);
                            if (owner.channel != (int)result || (owner.target >= 0 && !handlesTarget(owner.target)) ||
                                owner.staged || owner.valueAdapter || owner.adaptedFrom >= 0 || (owner.replacement && !owner.landed))
                                bad("returned completion belongs to another channel or an unfinished adapter");
                        }
                        if (!state.live.empty() || !state.named.empty() || !state.packed.empty() || !state.arguments.empty() || !state.rendered.empty())
                            bad("return leaves unfinished destination, named, argument, or pack ownership");
                        break;
                    case GirOp::Abort: case GirOp::Exit: case GirOp::Unreachable: break;
                    case GirOp::TargetDest: {
                        Ownership owner;
                        owner.root = inst.res;
                        owner.channel = inst.idx2;
                        owner.expected = fixedCount(inst.ty);
                        owner.target = inst.idx;
                        owner.replacement = true;
                        state.live[inst.res] = owner;
                        break;
                    }
                    case GirOp::Invoke: {
                        auto &callee = m.funcs[inst.idx];
                        for (size_t argument = 0; argument < inst.vals.size(); argument++) {
                            auto found = state.arguments.find(inst.vals[argument]);
                            if (GirNonfixed(m, callee.params[argument])) {
                                if (found == state.arguments.end() || found->second.argumentFunction != inst.idx ||
                                    found->second.argumentPosition != (int)argument)
                                    bad("invoke does not transfer its own associated argument region");
                                state.arguments.erase(found);
                            } else if (found != state.arguments.end()) bad("invoke transfers an argument to another parameter");
                        }
                        vector<Ownership> normalOwners;
                        for (auto value : inst.vals2) normalOwners.push_back(consume(value));
                        auto emitEdge = [&](int target, vector<pair<int, Ownership>> leading, const vector<int> &forwarded,
                                            size_t offset) {
                            auto next = state;
                            vector<pair<int, Ownership>> moved;
                            set<int> consumed;
                            for (size_t position = 0; position < forwarded.size(); position++) {
                                auto value = forwarded[position];
                                if (!carrier(value)) continue;
                                auto found = next.live.find(value);
                                if (found == next.live.end() || !consumed.insert(value).second)
                                    bad("invoke edge duplicates or forwards an unavailable carrier");
                                moved.push_back({ f.blocks[target].params[offset + position].first, found->second });
                            }
                            for (auto value : consumed) next.live.erase(value);
                            for (auto &entry : moved) next.live[entry.first] = entry.second;
                            for (auto &entry : leading) {
                                if (next.live.count(entry.first)) bad("invoke edge overwrites outstanding ownership");
                                next.live[entry.first] = entry.second;
                            }
                            merge(target, std::move(next));
                        };
                        vector<pair<int, Ownership>> normal;
                        size_t nonfixed = 0;
                        for (size_t result = 0; result < callee.results.size(); result++) {
                            if (!GirNonfixed(m, callee.results[result])) continue;
                            auto owner = normalOwners[nonfixed++];
                            owner.count = -1;
                            normal.push_back({ f.blocks[inst.a].params[result].first, owner });
                        }
                        emitEdge(inst.a, std::move(normal), inst.forwarded, callee.results.size());
                        for (auto &escape : inst.escapes) {
                            auto &target = m.funcs[m.targets[escape.target].members[0]];
                            vector<pair<int, Ownership>> escaped;
                            for (size_t result = 0; result < target.results.size(); result++) {
                                if (!GirNonfixed(m, target.results[result])) continue;
                                auto value = f.blocks[escape.block].params[result].first;
                                Ownership owner;
                                owner.root = value;
                                owner.channel = (int)result;
                                owner.target = escape.target;
                                owner.count = -1;
                                owner.replacement = true;
                                escaped.push_back({ value, owner });
                            }
                            for (size_t result = 0; result < normalOwners.size(); result++)
                                escaped.push_back({ f.blocks[escape.block].params[target.results.size() + result].first,
                                                    normalOwners[result] });
                            emitEdge(escape.block, std::move(escaped), escape.forwarded,
                                     target.results.size() + normalOwners.size());
                        }
                        break;
                    }
                    case GirOp::Escape:
                        for (size_t result = 0; result < inst.vals.size(); result++) {
                            if (!carrier(inst.vals[result])) continue;
                            auto owner = consume(inst.vals[result]);
                            if (owner.target != inst.idx || owner.channel != (int)result || owner.staged || owner.valueAdapter || owner.adaptedFrom >= 0)
                                bad("escape carrier belongs to another target or incomplete adapter");
                        }
                        {
                            size_t cancellation = 0;
                            for (size_t result = 0; result < f.results.size(); result++) {
                                if (!GirNonfixed(m, f.results[result])) continue;
                                auto owner = consume(inst.vals2[cancellation++]);
                                if (owner.target >= 0 || owner.channel != (int)result)
                                    bad("escape forwards another normal result channel's cancellation");
                            }
                        }
                        if (!state.live.empty() || !state.named.empty() || !state.packed.empty() || !state.arguments.empty() || !state.rendered.empty())
                            bad("escape leaves unfinished local, result, argument, or pack ownership");
                        break;
                    case GirOp::Leave:
                        for (auto &[value, owner] : state.live)
                            if (owner.channel < 0 && owner.slot >= 0 && f.slots[owner.slot].scope == inst.idx)
                                bad("receiver scope leaves before completing its construction ownership");
                        break;
                    default: {
                        vector<int> uses;
                        Uses(inst, uses);
                        for (auto value : uses)
                            if (carrier(value)) bad("construction carrier used as an ordinary value");
                            else if (state.arguments.count(value)) bad("owned call argument used outside its associated transfer");
                        break;
                    }
                }
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
        if (inst.op == GirOp::Call || inst.op == GirOp::CallConstruct || inst.op == GirOp::Invoke ||
            inst.op == GirOp::Clear || GirIsTerminator(inst.op) ||
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
        if (inst.op == GirOp::Call || inst.op == GirOp::CallConstruct || inst.op == GirOp::Invoke) {
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
                } else if (term->op == GirOp::Invoke) {
                    auto &callee = m.funcs[term->idx];
                    vector<int> normal(callee.results.size(), -1);
                    normal.insert(normal.end(), term->forwarded.begin(), term->forwarded.end());
                    propagate(term->a, normal);
                    size_t cancelled = 0;
                    for (auto result : callee.results) cancelled += GirNonfixed(m, result);
                    for (auto &edge : term->escapes) {
                        vector<int> escaped(m.funcs[m.targets[edge.target].members[0]].results.size() + cancelled, -1);
                        escaped.insert(escaped.end(), edge.forwarded.begin(), edge.forwarded.end());
                        propagate(edge.block, escaped);
                    }
                }
            }
        }
        return states;
    }

    void CheckShrinkReplace(const Fn &fn, const ResultRootInfo &resultRoots) {
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
