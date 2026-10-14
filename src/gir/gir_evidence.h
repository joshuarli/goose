// Goose compiler — checked bounds evidence for GIR-H.
#pragma once

#include <charconv>

namespace goose {

using GirFacts = vector<GirFact>;

inline bool GirFactLess(const GirFact &a, const GirFact &b) {
    return tie(a.kind, a.a, a.b) < tie(b.kind, b.a, b.b);
}

inline void CanonicalGirFacts(GirFacts &facts) {
    sort(facts.begin(), facts.end(), GirFactLess);
    facts.erase(unique(facts.begin(), facts.end()), facts.end());
}

class GirEvidenceAnalysis {
public:
    GirEvidenceAnalysis(const GirModule &module, const GirFunc &function) : m(module), f(function) {
        int count = 0;
        for (auto &block : f.blocks) {
            for (auto &param : block.params) count = max(count, param.first + 1);
            for (auto &inst : block.insts)
                if (GirDefinesValue(inst)) count = max(count, inst.res + 1);
        }
        defs.assign(count, nullptr);
        for (auto &block : f.blocks)
            for (auto &inst : block.insts)
                if (GirDefinesValue(inst) && inst.res >= 0 && inst.res < count) defs[inst.res] = &inst;
    }

    optional<string> Check(const vector<GirTypeId> &types) const {
        bool proven = false;
        for (auto &block : f.blocks)
            for (auto &inst : block.insts) proven |= inst.op == GirOp::IndexProven;
        if (!f.certificate) {
            if (proven) return "a proven index has no fact certificate";
            return nullopt;
        }
        auto &sets = f.certificate->blocks;
        if (sets.size() != f.blocks.size()) return "the fact certificate does not have one set per block";
        if (!sets.empty() && !sets[0].empty()) return "the entry block asserts facts";
        for (size_t block = 0; block < sets.size(); block++) {
            auto canonical = sets[block];
            CanonicalGirFacts(canonical);
            if (canonical != sets[block]) return cat("block ", block, " facts are not a canonical set");
            for (auto &fact : sets[block])
                if (!FactWellTyped(fact, types)) return cat("block ", block, " contains an ill-typed fact");
        }
        for (size_t block = 0; block < f.blocks.size(); block++) {
            string error;
            auto outgoing = TransferBlock(sets[block], f.blocks[block], &error);
            if (!error.empty()) return cat("block ", block, ": ", error);
            auto edges = Edges(f.blocks[block], (int)block);
            for (auto &edge : edges) {
                auto facts = TransferEdge(outgoing, edge);
                for (auto &claimed : sets[edge.target])
                    if (!binary_search(facts.begin(), facts.end(), claimed, GirFactLess))
                        return cat("block ", edge.target, " asserts a fact not implied by block ", block);
            }
        }
        return nullopt;
    }

    vector<GirFacts> BlockEntries() const {
        auto edges = AllEdges();
        vector<vector<int>> outgoing(f.blocks.size()), incoming(f.blocks.size());
        for (size_t e = 0; e < edges.size(); e++) {
            outgoing[edges[e].from].push_back((int)e);
            incoming[edges[e].target].push_back((int)e);
        }
        vector<optional<GirFacts>> states(f.blocks.size()), edgeStates(edges.size());
        if (states.empty()) return {};
        states[0] = GirFacts {};
        vector<int> work { 0 };
        vector<char> queued(f.blocks.size(), 0);
        queued[0] = 1;
        while (!work.empty()) {
            auto block = work.back();
            work.pop_back();
            queued[block] = 0;
            auto facts = TransferBlock(*states[block], f.blocks[block]);
            for (auto edgeIndex : outgoing[block]) {
                auto translated = TransferEdge(facts, edges[edgeIndex]);
                if (edgeStates[edgeIndex] == translated) continue;
                edgeStates[edgeIndex] = std::move(translated);
                auto target = edges[edgeIndex].target;
                optional<GirFacts> joined;
                for (auto incomingEdge : incoming[target]) {
                    if (!edgeStates[incomingEdge]) continue;
                    if (!joined) joined = *edgeStates[incomingEdge];
                    else joined = Intersection(*joined, *edgeStates[incomingEdge]);
                }
                if (joined && states[target] != joined) {
                    states[target] = std::move(joined);
                    if (!queued[target]) {
                        work.push_back(target);
                        queued[target] = 1;
                    }
                }
            }
        }
        vector<GirFacts> result(f.blocks.size());
        for (size_t block = 0; block < result.size(); block++)
            if (states[block]) result[block] = std::move(*states[block]);
        return result;
    }

    GirFacts TransferBlock(GirFacts facts, const GirBlock &block, string *error = nullptr) const {
        for (auto &inst : block.insts) facts = TransferInst(std::move(facts), inst, error);
        return facts;
    }

    bool ProvesIndex(const GirFacts &facts, const GirInst &inst) const {
        if (!Has(facts, FactGe0(inst.b))) return false;
        for (auto &view : facts) {
            if (view.kind != GirFact::ViewLenGe || view.a != inst.a) continue;
            if (Has(facts, FactLt(inst.b, view.b))) return true;
        }
        return false;
    }

private:
    const GirModule &m;
    const GirFunc &f;
    vector<const GirInst *> defs;

    struct Edge {
        int from = -1, target = -1;
        vector<int> args;
        bool trueEdge = false;
    };

    static GirFact FactGe0(int value) {
        GirFact fact;
        fact.kind = GirFact::Ge0;
        fact.a = value;
        return fact;
    }

    static GirFact FactLt(int value, int bound) {
        GirFact fact;
        fact.kind = GirFact::Lt;
        fact.a = value;
        fact.b = bound;
        return fact;
    }

    static GirFact FactLenGe(int reference, int bound) {
        GirFact fact;
        fact.kind = GirFact::LenGe;
        fact.a = reference;
        fact.b = bound;
        return fact;
    }

    static GirFact FactViewLenGe(int view, int bound) {
        GirFact fact;
        fact.kind = GirFact::ViewLenGe;
        fact.a = view;
        fact.b = bound;
        return fact;
    }

    static bool Has(const GirFacts &facts, const GirFact &fact) {
        return binary_search(facts.begin(), facts.end(), fact, GirFactLess);
    }

    static void Add(GirFacts &facts, GirFact fact) {
        facts.push_back(std::move(fact));
    }

    static bool Mentions(const GirFact &fact, int value) {
        switch (fact.kind) {
            case GirFact::Ge0: return fact.a == value;
            case GirFact::Lt: case GirFact::ViewLenGe: return fact.a == value || fact.b == value;
            case GirFact::LenGe: return fact.a == value || fact.b == value;
        }
        return false;
    }

    static void KillValue(GirFacts &facts, int value) {
        facts.erase(remove_if(facts.begin(), facts.end(),
                              [&](const GirFact &fact) { return Mentions(fact, value); }), facts.end());
    }

    static void KillLengths(GirFacts &facts) {
        facts.erase(remove_if(facts.begin(), facts.end(),
                              [](const GirFact &fact) { return fact.kind == GirFact::LenGe; }), facts.end());
    }

    optional<int64_t> Constant(int value) const {
        if (value < 0 || value >= (int)defs.size() || !defs[value]) return nullopt;
        auto &inst = *defs[value];
        if (inst.op != GirOp::Int || inst.ty < 0 || inst.ty >= (int)m.types.size()) return nullopt;
        auto &type = m.Type(inst.ty);
        if (type.kind != CoreType::Int || type.ity != CoreIntTy::I64) return nullopt;
        int64_t result = 0;
        auto parsed = from_chars(inst.text.data(), inst.text.data() + inst.text.size(), result);
        if (parsed.ec != errc() || parsed.ptr != inst.text.data() + inst.text.size()) return nullopt;
        return result;
    }

    bool IsI64Value(int value, const vector<GirTypeId> &types) const {
        if (value < 0 || value >= (int)types.size()) return false;
        auto type = types[value];
        return type >= 0 && type < (int)m.types.size() && m.Type(type).kind == CoreType::Int &&
               m.Type(type).ity == CoreIntTy::I64;
    }

    bool FactWellTyped(const GirFact &fact, const vector<GirTypeId> &types) const {
        switch (fact.kind) {
            case GirFact::Ge0:
                return fact.b == 0 && IsI64Value(fact.a, types);
            case GirFact::Lt:
                return IsI64Value(fact.a, types) && IsI64Value(fact.b, types);
            case GirFact::LenGe: {
                if (!IsI64Value(fact.b, types) || fact.a < 0 || fact.a >= (int)types.size()) return false;
                auto type = types[fact.a];
                if (type < 0 || type >= (int)m.types.size() || m.Type(type).kind != CoreType::Ref)
                    return false;
                auto pointee = m.Type(type).elem;
                if (pointee < 0 || pointee >= (int)m.types.size()) return false;
                auto kind = m.Type(pointee).kind;
                return kind == CoreType::Arr || GirOwnerKind(kind);
            }
            case GirFact::ViewLenGe:
                if (!IsI64Value(fact.b, types) || fact.a < 0 || fact.a >= (int)types.size()) return false;
                return types[fact.a] >= 0 && types[fact.a] < (int)m.types.size() &&
                       m.Type(types[fact.a]).kind == CoreType::View;
        }
        return false;
    }

    static bool KillsLengths(const GirInst &inst) {
        switch (inst.op) {
            case GirOp::Call: case GirOp::Init: case GirOp::Store: case GirOp::Push: case GirOp::Append:
            case GirOp::Pop: case GirOp::PopN:
            case GirOp::Resize: case GirOp::Clear: case GirOp::Replace: case GirOp::Enter:
            case GirOp::Leave:
                return true;
            default:
                return false;
        }
    }

    GirFacts TransferInst(GirFacts facts, const GirInst &inst, string *error) const {
        if (inst.op == GirOp::IndexProven && !ProvesIndex(facts, inst)) {
            if (error && error->empty()) *error = "a proven index is not justified by its entry facts";
        }
        if (GirDefinesValue(inst)) KillValue(facts, inst.res);
        if (KillsLengths(inst)) KillLengths(facts);
        if (inst.op == GirOp::Int) {
            auto value = Constant(inst.res);
            if (value && *value >= 0) Add(facts, FactGe0(inst.res));
        } else if (inst.op == GirOp::ArrayLen) {
            Add(facts, FactLenGe(inst.a, inst.res));
            Add(facts, FactGe0(inst.res));
        } else if (inst.op == GirOp::Snap) {
            auto before = facts;
            for (auto &fact : before)
                if (fact.kind == GirFact::LenGe && fact.a == inst.a)
                    Add(facts, FactViewLenGe(inst.res, fact.b));
        }
        CanonicalGirFacts(facts);
        return facts;
    }

    vector<Edge> Edges(const GirBlock &block, int from = -1) const {
        vector<Edge> result;
        if (block.insts.empty()) return result;
        auto &term = block.insts.back();
        if (term.op == GirOp::Br) result.push_back({ from, term.idx, term.vals, false });
        if (term.op == GirOp::CondBr) {
            result.push_back({ from, term.idx, term.vals, true });
            result.push_back({ from, term.idx2, term.vals2, false });
        }
        return result;
    }

    vector<Edge> AllEdges() const {
        vector<Edge> result;
        for (size_t block = 0; block < f.blocks.size(); block++) {
            auto edges = Edges(f.blocks[block], (int)block);
            result.insert(result.end(), make_move_iterator(edges.begin()), make_move_iterator(edges.end()));
        }
        return result;
    }

    GirFacts Translate(GirFacts facts, const Edge &edge) const {
        if (edge.target < 0 || edge.target >= (int)f.blocks.size()) return {};
        auto &params = f.blocks[edge.target].params;
        facts.erase(remove_if(facts.begin(), facts.end(), [&](const GirFact &fact) {
            for (auto &param : params) if (Mentions(fact, param.first)) return true;
            return false;
        }), facts.end());
        CanonicalGirFacts(facts);
        return facts;
    }

    GirFacts TransferEdge(GirFacts facts, const Edge &edge) const {
        if (edge.trueEdge && edge.from >= 0 && edge.from < (int)f.blocks.size() &&
            !f.blocks[edge.from].insts.empty()) {
            auto &term = f.blocks[edge.from].insts.back();
            if (term.op == GirOp::CondBr && term.a >= 0 && term.a < (int)defs.size() && defs[term.a]) {
                auto &condition = *defs[term.a];
                if (condition.op == GirOp::Cmp && condition.ty >= 0 &&
                    condition.ty < (int)m.types.size() && m.Type(condition.ty).kind == CoreType::Int &&
                    m.Type(condition.ty).ity == CoreIntTy::I64) {
                    if (condition.cmp == CoreCmpOp::Lt) Add(facts, FactLt(condition.a, condition.b));
                }
            }
        }
        CanonicalGirFacts(facts);
        return Translate(std::move(facts), edge);
    }

    static GirFacts Intersection(const GirFacts &a, const GirFacts &b) {
        GirFacts result;
        set_intersection(a.begin(), a.end(), b.begin(), b.end(), back_inserter(result), GirFactLess);
        return result;
    }
};

inline optional<string> CheckGirEvidence(const GirModule &module, const GirFunc &function,
                                         const vector<GirTypeId> &types) {
    return GirEvidenceAnalysis(module, function).Check(types);
}

inline void ProposeGirEvidenceForFunction(const GirModule &module, GirFunc &function) {
    GirEvidenceAnalysis analysis(module, function);
    auto entries = analysis.BlockEntries();
    bool any = false;
    for (size_t block = 0; block < function.blocks.size(); block++) {
        auto facts = entries[block];
        for (auto &inst : function.blocks[block].insts) {
            if (inst.op == GirOp::Index && analysis.ProvesIndex(facts, inst)) inst.op = GirOp::IndexProven;
            any |= inst.op == GirOp::IndexProven;
            facts = analysis.TransferBlock(std::move(facts), GirBlock { {}, { inst } });
        }
    }
    if (any) function.certificate = GirFactCertificate { std::move(entries) };
    else function.certificate.reset();
}

inline void ProposeGirEvidence(GirModule &module) {
    if (module.low) return;
    for (auto &function : module.funcs) ProposeGirEvidenceForFunction(module, function);
    for (auto &global : module.globals) ProposeGirEvidenceForFunction(module, global.init);
}

}  // namespace goose
