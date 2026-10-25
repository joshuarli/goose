#pragma once

#include <optional>
#include <variant>

namespace goose {

class GirReplacementContentFlow {
    friend class GirVerifier;

    struct Atom {
        enum Kind { Local, Global, Param, Contents };
        Kind kind;
        int index;
        bool operator==(const Atom &) const = default;
    };

    class FlowRoots {
        struct Pending { bool operator==(const Pending &) const = default; };
        struct Unknown { bool operator==(const Unknown &) const = default; };
        variant<Pending, vector<Atom>, Unknown> value;

    public:
        FlowRoots() : value(Pending {}) {}
        static FlowRoots Known(vector<Atom> roots = {}) {
            FlowRoots result;
            result.value = std::move(roots);
            return result;
        }
        static FlowRoots Opaque() {
            FlowRoots result;
            result.value = Unknown {};
            return result;
        }
        bool IsPending() const { return holds_alternative<Pending>(value); }
        bool IsUnknown() const { return holds_alternative<Unknown>(value); }
        const vector<Atom> *KnownRoots() const { return get_if<vector<Atom>>(&value); }
        bool operator==(const FlowRoots &) const = default;
        FlowRoots Join(const FlowRoots &other) const {
            if (IsUnknown() || other.IsUnknown()) return Opaque();
            if (IsPending()) return other;
            if (other.IsPending()) return *this;
            auto roots = *KnownRoots();
            for (auto &root : *other.KnownRoots())
                if (find(roots.begin(), roots.end(), root) == roots.end()) roots.push_back(root);
            return Known(std::move(roots));
        }
        template<class Map> FlowRoots Bind(Map map) const {
            if (!KnownRoots()) return *this;
            auto result = Known();
            for (auto &root : *KnownRoots()) {
                auto mapped = map(root);
                if (result.IsUnknown() || mapped.IsUnknown()) result = Opaque();
                else if (result.IsPending() || mapped.IsPending()) result = FlowRoots {};
                else result = result.Join(mapped);
            }
            return result;
        }
    };

    struct Unchanged { bool operator==(const Unchanged &) const = default; };
    using Write = variant<Unchanged, FlowRoots>;
    struct State {
        vector<FlowRoots> values, slots, contents;
        vector<Write> writes;
        FlowRoots touched = FlowRoots::Known();
        FlowRoots returned;
        bool operator==(const State &) const = default;
    };
    using Query = optional<vector<CoreRootRef>>;
    using OperandUses = void (*)(const GirInst &, vector<int> &);
    static vector<int> AccessOperands(const GirInst &inst, OperandUses uses) {
        if (GirIsTerminator(inst.op)) return {};
        switch (inst.op) {
            case GirOp::Slot: case GirOp::Global: case GirOp::Field: case GirOp::Freeze:
            case GirOp::OwnerBorrow: case GirOp::Init: return {};
            case GirOp::Store: return { inst.a };
            default: {
                vector<int> values;
                uses(inst, values);
                return values;
            }
        }
    }
    static optional<int> LoadedResult(const GirInst &inst) {
        if (inst.op == GirOp::Load) return inst.res;
        return nullopt;
    }
    const GirModule &module;
    vector<vector<GirTypeId>> canonicalTypes;
    OperandUses operandUses;
    optional<vector<State>> states;

    static FlowRoots At(const vector<FlowRoots> &roots, int index) {
        return index >= 0 && index < (int)roots.size() ? roots[index] : FlowRoots::Opaque();
    }
    static void Add(vector<FlowRoots> &roots, int index, const FlowRoots &added) {
        if (index >= 0 && index < (int)roots.size()) roots[index] = roots[index].Join(added);
    }
    static void AddRoot(vector<CoreRootRef> &roots, CoreRootRef root) {
        if (find(roots.begin(), roots.end(), root) == roots.end()) roots.push_back(root);
    }
    static void AddRoots(vector<CoreRootRef> &roots, const vector<CoreRootRef> &added) {
        for (auto &root : added) AddRoot(roots, root);
    }
    static vector<CoreRootRef> ParameterRoots(const GirFunc &function, int parameter) {
        for (auto &row : function.roots.params) if (row.first == parameter) return row.second;
        return { { CoreRootRef::Param, parameter } };
    }
    static vector<CoreRootRef> Expand(const GirFunc &function, const vector<CoreRootRef> &roots) {
        vector<CoreRootRef> result;
        for (auto &root : roots) {
            if (root.kind == CoreRootRef::Param) AddRoots(result, ParameterRoots(function, root.index));
            else AddRoot(result, root);
        }
        return result;
    }
    bool RefLike(const vector<GirTypeId> &types, int value) const {
        if (value < 0 || value >= (int)types.size() || types[value] < 0) return false;
        auto kind = module.Type(types[value]).kind;
        return kind == CoreType::Ref || kind == CoreType::Slice || kind == CoreType::View;
    }
    bool InteriorRefLike(const vector<GirTypeId> &types, int value) const {
        if (!RefLike(types, value)) return false;
        auto &type = module.Type(types[value]);
        return type.kind != CoreType::Ref || !GirOwnerKind(module.Type(type.elem).kind);
    }
    bool RefSlice(GirTypeId type) const {
        return type >= 0 && module.Type(type).kind == CoreType::Ref &&
            module.Type(module.Type(type).elem).kind == CoreType::Slice;
    }
    State Start(const GirFunc &function, const vector<GirTypeId> &types) const {
        State state;
        state.values.resize(types.size());
        state.slots.resize(function.slots.size());
        state.writes.resize(function.params.size(), Unchanged {});
        state.returned = FlowRoots::Known();
        for (size_t parameter = 0; parameter < function.params.size(); parameter++)
            state.contents.push_back(RefSlice(function.params[parameter]) ?
                FlowRoots::Known({ { Atom::Contents, (int)parameter } }) : FlowRoots::Known());
        if (!function.blocks.empty())
            for (size_t index = 0; index < function.blocks[0].params.size(); index++) {
                auto value = function.blocks[0].params[index].first;
                if (value >= 0 && value < (int)state.values.size())
                    state.values[value] = RefLike(types, value) ?
                        FlowRoots::Known({ { Atom::Param, (int)index } }) : FlowRoots::Known();
            }
        return state;
    }
    FlowRoots Content(const GirFunc &function, const State &state, const FlowRoots &address) const {
        return address.Bind([&](const Atom &root) {
            switch (root.kind) {
                case Atom::Local: return At(state.slots, root.index);
                case Atom::Param:
                    return root.index >= 0 && root.index < (int)function.params.size() && RefSlice(function.params[root.index]) ?
                        At(state.contents, root.index) : FlowRoots::Opaque();
                case Atom::Global: case Atom::Contents: return FlowRoots::Opaque();
            }
            return FlowRoots::Opaque();
        });
    }
    void Store(const GirFunc &function, State &state, const FlowRoots &address, const FlowRoots &value) const {
        if (address.IsPending()) return;
        if (address.IsUnknown()) {
            fill(state.slots.begin(), state.slots.end(), FlowRoots::Opaque());
            fill(state.contents.begin(), state.contents.end(), FlowRoots::Opaque());
            fill(state.writes.begin(), state.writes.end(), Write { FlowRoots::Opaque() });
            return;
        }
        for (auto &root : *address.KnownRoots()) {
            switch (root.kind) {
                case Atom::Local: Add(state.slots, root.index, value); break;
                case Atom::Param:
                    if (root.index >= 0 && root.index < (int)function.params.size() && RefSlice(function.params[root.index])) {
                        Add(state.contents, root.index, value);
                        if (auto previous = get_if<FlowRoots>(&state.writes[root.index])) state.writes[root.index] = previous->Join(value);
                        else state.writes[root.index] = value;
                    }
                    break;
                case Atom::Global: case Atom::Contents: state.touched = FlowRoots::Opaque(); break;
            }
        }
    }
    FlowRoots Substitute(const GirFunc &function, const State &state, const vector<int> &args, const FlowRoots &roots) const {
        return roots.Bind([&](const Atom &root) {
            if (root.kind == Atom::Global) return FlowRoots::Known({ root });
            if (root.kind == Atom::Local || root.index < 0 || root.index >= (int)args.size()) return FlowRoots::Opaque();
            auto actual = At(state.values, args[root.index]);
            return root.kind == Atom::Contents ? Content(function, state, actual) : actual;
        });
    }
    static FlowRoots PublicTouches(const FlowRoots &roots) {
        return roots.Bind([](const Atom &root) {
            return root.kind == Atom::Local ? FlowRoots::Known() : FlowRoots::Known({ root });
        });
    }
    FlowRoots Call(const vector<State> &closed, const GirFunc &function, State &state, int fn, const vector<int> &args) const {
        if (fn < 0 || fn >= (int)module.funcs.size() || fn >= (int)closed.size()) {
            state.touched = FlowRoots::Opaque();
            return FlowRoots::Opaque();
        }
        auto before = state;
        auto &callee = module.funcs[fn];
        auto &effects = closed[fn];
        state.touched = state.touched.Join(Substitute(function, before, args, PublicTouches(effects.touched)));
        for (size_t index = 0; index < callee.params.size(); index++)
            if (RefSlice(callee.params[index])) {
                auto written = index < effects.writes.size() ? get_if<FlowRoots>(&effects.writes[index]) : nullptr;
                if (!written && index < effects.writes.size()) continue;
                auto address = index < args.size() ? At(before.values, args[index]) : FlowRoots::Opaque();
                Store(function, state, address, written ? Substitute(function, before, args, *written) : FlowRoots::Opaque());
            }
        return Substitute(function, before, args, effects.returned);
    }
    FlowRoots Result(const GirFunc &function, const vector<GirTypeId> &types, const State &state, const GirInst &inst) const {
        if (!RefLike(types, inst.res)) return FlowRoots::Known();
        switch (inst.op) {
            case GirOp::Slot: return FlowRoots::Known({ { Atom::Local, inst.idx } });
            case GirOp::Global: return FlowRoots::Known({ { Atom::Global, inst.idx } });
            case GirOp::Field: case GirOp::Elem: case GirOp::ViewSlice: case GirOp::Index:
            case GirOp::IndexProven: case GirOp::Freeze: case GirOp::OwnerBorrow: case GirOp::SliceView:
            case GirOp::Push: case GirOp::Snap: return At(state.values, inst.a);
            case GirOp::Load: return Content(function, state, At(state.values, inst.a));
            case GirOp::Call: return FlowRoots {};
            default: return FlowRoots::Opaque();
        }
    }
    static void Edge(const GirFunc &function, State &state, int target, const vector<int> &args) {
        if (target < 0 || target >= (int)function.blocks.size()) {
            state.touched = FlowRoots::Opaque();
            return;
        }
        auto &parameters = function.blocks[target].params;
        for (size_t index = 0; index < parameters.size() && index < args.size(); index++)
            Add(state.values, parameters[index].first, At(state.values, args[index]));
    }
    void Step(const vector<State> &closed, const GirFunc &function, const vector<GirTypeId> &types, State &state, const GirInst &inst) const {
        if (inst.op != GirOp::Call)
            for (auto value : AccessOperands(inst, operandUses))
                if (RefLike(types, value)) state.touched = state.touched.Join(At(state.values, value));
        if (inst.op == GirOp::CallConstruct || inst.op == GirOp::Invoke) {
            state.touched = FlowRoots::Opaque();
            Store(function, state, FlowRoots::Opaque(), FlowRoots::Opaque());
            if (GirDefinesValue(inst)) Add(state.values, inst.res, FlowRoots::Opaque());
            return;
        }
        if (inst.op == GirOp::Call) {
            auto roots = Call(closed, function, state, inst.idx, inst.vals);
            if (GirDefinesValue(inst)) Add(state.values, inst.res, RefLike(types, inst.res) ? roots : FlowRoots::Known());
        } else if (GirDefinesValue(inst)) Add(state.values, inst.res, Result(function, types, state, inst));
        else if (inst.op == GirOp::Init) Add(state.slots, inst.idx, At(state.values, inst.a));
        else if (inst.op == GirOp::Store && RefLike(types, inst.b)) Store(function, state, At(state.values, inst.a), At(state.values, inst.b));
        else if (inst.op == GirOp::Br) Edge(function, state, inst.idx, inst.vals);
        else if (inst.op == GirOp::CondBr) {
            Edge(function, state, inst.idx, inst.vals);
            Edge(function, state, inst.idx2, inst.vals2);
        } else if (inst.op == GirOp::Ret && inst.vals.size() == 1) state.returned = state.returned.Join(At(state.values, inst.vals[0]));
        if (auto value = LoadedResult(inst); value && InteriorRefLike(types, *value))
            state.touched = state.touched.Join(At(state.values, *value));
    }
    State Round(const vector<State> &closed, const GirFunc &function, const vector<GirTypeId> &types, State state) const {
        for (auto &block : function.blocks) for (auto &inst : block.insts) Step(closed, function, types, state, inst);
        return state;
    }
    size_t Capacity(const GirFunc &function, const vector<GirTypeId> &types) const {
        return (types.size() + function.slots.size() + 3 * function.params.size() + 3) *
            (module.globals.size() + function.slots.size() + 2 * function.params.size() + 3);
    }
    Query Normalize(const GirFunc &function, const FlowRoots &roots) const {
        auto known = roots.KnownRoots();
        if (!known) return nullopt;
        vector<CoreRootRef> result;
        for (auto &root : *known) {
            if (root.kind == Atom::Local) AddRoot(result, { CoreRootRef::Local, root.index });
            else if (root.kind == Atom::Global) AddRoot(result, { CoreRootRef::Global, root.index });
            else if (root.kind == Atom::Param) AddRoots(result, ParameterRoots(function, root.index));
            else {
                auto row = find_if(function.roots.contents.begin(), function.roots.contents.end(), [&](const auto &entry) { return entry.first == root.index; });
                if (row == function.roots.contents.end()) return nullopt;
                AddRoots(result, Expand(function, row->second));
            }
        }
        return result;
    }
    FlowRoots RawOwnerTouches(const FlowRoots &roots) const {
        auto known = roots.KnownRoots();
        if (!known || !all_of(module.globals.begin(), module.globals.end(), [&](const GirGlobal &global) {
                return GirStorable(module, global.ty) && !GirRefLike(module, global.ty);
            })) return roots;
        vector<Atom> result;
        for (auto &root : *known) {
            if (root.kind == Atom::Global && root.index >= 0 && root.index < (int)module.globals.size() &&
                !GirOwnerKind(module.Type(module.globals[root.index].ty).kind)) continue;
            if (find(result.begin(), result.end(), root) == result.end()) result.push_back(root);
        }
        return FlowRoots::Known(std::move(result));
    }
    Query OwnerDependencies(const GirFunc &function, const FlowRoots &roots) const {
        return Normalize(function, RawOwnerTouches(roots));
    }
    static bool Within(const Query &actual, const vector<CoreRootRef> &expected) {
        return actual && all_of(actual->begin(), actual->end(), [&](const CoreRootRef &root) {
            return find(expected.begin(), expected.end(), root) != expected.end();
        });
    }
    struct CallerStorage {};
    class ContentInputBound {
        variant<vector<CoreRootRef>, CallerStorage> value;
    public:
        explicit ContentInputBound(vector<CoreRootRef> roots = {}) : value(std::move(roots)) {}
        explicit ContentInputBound(CallerStorage storage) : value(storage) {}
        ContentInputBound Join(const ContentInputBound &other) const {
            if (holds_alternative<CallerStorage>(value) || holds_alternative<CallerStorage>(other.value))
                return ContentInputBound(CallerStorage {});
            auto roots = get<vector<CoreRootRef>>(value);
            AddRoots(roots, get<vector<CoreRootRef>>(other.value));
            return ContentInputBound(std::move(roots));
        }
        bool Covers(const Query &actual) const {
            return actual && (holds_alternative<CallerStorage>(value) || Within(actual, get<vector<CoreRootRef>>(value)));
        }
    };
    optional<ContentInputBound> AdmittedArgumentBound(const GirFunc &callee, const GirFunc &function,
        const State &state, const vector<int> &args, int index) const {
        if (index < 0 || index >= (int)callee.params.size() || index >= (int)args.size()) return nullopt;
        auto actual = Normalize(function, At(state.values, args[index]));
        if (!actual) return nullopt;
        auto row = find_if(callee.roots.params.begin(), callee.roots.params.end(), [&](const auto &entry) { return entry.first == index; });
        if (row != callee.roots.params.end()) {
            CoreRootRef self { CoreRootRef::Param, index };
            if (GirRefLike(module, callee.params[index]) && find(row->second.begin(), row->second.end(), self) != row->second.end())
                return ContentInputBound(CallerStorage {});
            for (auto &root : row->second) if (root.kind == CoreRootRef::Global) AddRoot(*actual, root);
        }
        return ContentInputBound(std::move(*actual));
    }
    optional<ContentInputBound> InputBound(const GirFunc &callee, const GirFunc &function,
        const State &state, const vector<int> &args, const vector<CoreRootRef> &bound) const {
        ContentInputBound result;
        for (auto &root : bound) {
            if (root.kind == CoreRootRef::Global) result = result.Join(ContentInputBound({ root }));
            else if (root.kind == CoreRootRef::Param) {
                auto next = AdmittedArgumentBound(callee, function, state, args, root.index);
                if (!next) return nullopt;
                result = result.Join(*next);
            } else return nullopt;
        }
        return result;
    }
    bool ArgsTyped(const vector<GirTypeId> &types, int fn, const vector<int> &args) const {
        if (fn < 0 || fn >= (int)module.funcs.size() || args.size() != module.funcs[fn].params.size()) return false;
        for (size_t index = 0; index < args.size(); index++) {
            auto value = args[index];
            if (value < 0 || value >= (int)types.size() || types[value] < 0) return false;
            auto kind = module.Type(types[value]).kind;
            if (kind == CoreType::View || kind == CoreType::Dest || kind == CoreType::Built || kind == CoreType::Cancelled ||
                !GirPassable(module, types[value], module.funcs[fn].params[index])) return false;
        }
        return true;
    }
    bool CheckCall(const GirFunc &function, const State &state, int fn, const vector<int> &args) const {
        if (fn < 0 || fn >= (int)module.funcs.size()) return false;
        auto &callee = module.funcs[fn];
        for (size_t parameter = 0; parameter < callee.params.size(); parameter++) {
            if (!GirRefLike(module, callee.params[parameter])) continue;
            if (parameter >= args.size()) return false;
            auto declared = ParameterRoots(callee, (int)parameter);
            CoreRootRef self { CoreRootRef::Param, (int)parameter };
            if (find(declared.begin(), declared.end(), self) != declared.end()) continue;
            auto actual = Normalize(function, At(state.values, args[parameter]));
            if (!actual) return false;
            for (auto &root : *actual) {
                CoreRootRef expected = root.kind == CoreRootRef::Global || root.kind == CoreRootRef::Static ? root : CoreRootRef { CoreRootRef::Param, (int)parameter };
                if (find(declared.begin(), declared.end(), expected) == declared.end()) return false;
            }
        }
        for (auto &row : callee.roots.contents) {
            if (row.first < 0 || row.first >= (int)args.size()) return false;
            auto expected = InputBound(callee, function, state, args, row.second);
            if (!expected || !expected->Covers(Normalize(function, Content(function, state, At(state.values, args[row.first]))))) return false;
        }
        return true;
    }
    bool Check(const GirFunc &function, const vector<GirTypeId> &types, const State &state) const {
        if (function.results.size() > 1) return false;
        if (function.results.size() == 1 && GirRefLike(module, function.results[0]) &&
            (function.roots.results.empty() || !Within(Normalize(function, state.returned), Expand(function, function.roots.results[0])))) return false;
        for (size_t index = 0; index < state.writes.size(); index++)
            if (auto written = get_if<FlowRoots>(&state.writes[index])) {
                auto actual = Normalize(function, *written);
                if (actual && actual->empty()) continue;
                auto row = find_if(function.roots.contents.begin(), function.roots.contents.end(), [&](const auto &entry) { return entry.first == (int)index; });
                if (row == function.roots.contents.end() || !Within(actual, Expand(function, row->second))) return false;
            }
        for (auto &block : function.blocks) for (auto &inst : block.insts) {
            vector<int> uses;
            operandUses(inst, uses);
            for (auto value : uses)
                if (value < 0 || value >= (int)types.size() || types[value] < 0 || (RefLike(types, value) && At(state.values, value).IsPending())) return false;
            if (inst.op == GirOp::Call && !CheckCall(function, state, inst.idx, inst.vals)) return false;
        }
        return true;
    }
    optional<State> CloseFunction(const vector<State> &closed, const GirFunc &function, const vector<GirTypeId> &types) const {
        auto state = Start(function, types);
        for (size_t round = 0; round <= Capacity(function, types); round++) {
            auto next = Round(closed, function, types, state);
            if (next == state) return Check(function, types, state) ? optional<State>(std::move(state)) : nullopt;
            state = std::move(next);
        }
        return nullopt;
    }
    optional<vector<State>> Close() const {
        vector<State> closed;
        size_t fuel = 1;
        for (size_t index = 0; index < module.funcs.size(); index++) {
            closed.push_back(Start(module.funcs[index], canonicalTypes[index]));
            fuel += Capacity(module.funcs[index], canonicalTypes[index]);
        }
        for (size_t round = 0; round < fuel; round++) {
            auto next = closed;
            for (size_t index = 0; index < module.funcs.size(); index++) next[index] = Round(closed, module.funcs[index], canonicalTypes[index], closed[index]);
            if (next == closed) {
                for (size_t index = 0; index < module.funcs.size(); index++) if (!Check(module.funcs[index], canonicalTypes[index], closed[index])) return nullopt;
                for (size_t index = 0; index < module.globals.size(); index++) {
                    auto &initializer = module.globals[index].init;
                    if (initializer.blocks.empty() || !initializer.params.empty() || initializer.results != vector<GirTypeId> { module.globals[index].ty } ||
                        !CloseFunction(closed, initializer, canonicalTypes[module.funcs.size() + index])) return nullopt;
                }
                return closed;
            }
            closed = std::move(next);
        }
        return nullopt;
    }

    class Function {
        friend class GirReplacementContentFlow;
        const GirReplacementContentFlow *cache;
        const GirFunc *function;
        const vector<GirTypeId> *types;
        optional<State> state;
        Function(const GirReplacementContentFlow &owner, const GirFunc &body, const vector<GirTypeId> &valueTypes, optional<State> closed)
            : cache(&owner), function(&body), types(&valueTypes), state(std::move(closed)) {}
    public:
        Query Value(int value) const {
            return state ? cache->Normalize(*function, At(state->values, value)) : nullopt;
        }
        Query Call(int fn, const vector<int> &args) const {
            if (!state || !cache->states || fn < 0 || fn >= (int)cache->states->size() ||
                !cache->ArgsTyped(*types, fn, args) || !cache->CheckCall(*function, *state, fn, args)) return nullopt;
            vector<CoreRootRef> result;
            for (auto arg : args) if (cache->RefLike(*types, arg)) {
                auto actual = cache->OwnerDependencies(*function, At(state->values, arg));
                if (!actual) return nullopt;
                AddRoots(result, *actual);
            }
            auto rawTouched = cache->Substitute(*function, *state, args, PublicTouches((*cache->states)[fn].touched));
            auto touched = cache->OwnerDependencies(*function, rawTouched);
            if (!touched) return nullopt;
            AddRoots(result, *touched);
            return result;
        }
        Query OwnerDependencies(int value) const {
            return state ? cache->OwnerDependencies(*function, At(state->values, value)) : nullopt;
        }

    };

    GirReplacementContentFlow(const GirModule &source, vector<vector<GirTypeId>> types, OperandUses uses)
        : module(source), canonicalTypes(std::move(types)), operandUses(uses) {
        if (canonicalTypes.size() != module.funcs.size() + module.globals.size()) return;
        for (auto &global : module.globals) if (!GirStorable(module, global.ty) || GirRefLike(module, global.ty)) return;
        if (module.entry < 0 || module.entry >= (int)module.funcs.size() ||
            !module.funcs[module.entry].params.empty() || !module.funcs[module.entry].results.empty()) return;
        states = Close();
    }
    Function ForFunction(const GirFunc &function, const vector<GirTypeId> &types) const {
        optional<size_t> index;
        for (size_t candidate = 0; candidate < module.funcs.size(); candidate++)
            if (&function == &module.funcs[candidate]) { index = candidate; break; }
        if (!index)
            for (size_t global = 0; global < module.globals.size(); global++)
                if (&function == &module.globals[global].init) { index = module.funcs.size() + global; break; }
        if (!index || *index >= canonicalTypes.size() || canonicalTypes[*index] != types)
            return Function(*this, function, types, nullopt);
        return Function(*this, function, canonicalTypes[*index], states ? CloseFunction(*states, function, types) : nullopt);
    }
};

}
