#pragma once

namespace goose {

class GirLowerer {
public:
    // `origin` maps a Core origin to its number in the Core module's document.
    GirLowerer(const CoreModule &core, vector<string> files, vector<CoreOrigin> origins,
               function<int(const CoreOrigin &)> origin)
        : core(core), files(std::move(files)), origins(std::move(origins)), originof(std::move(origin)) {}

    GirModule Lower() {
        noReturn = ComputeNoReturn();
        mod.types = core.types;
        mod.profile = core.profile;
        mod.structs = core.structs;
        mod.files = files;
        mod.origins = origins;
        for (auto &target : core.targets) {
            vector<int> members;
            for (size_t context = 0; context < core.contexts.size(); context++)
                if (find(target.members.begin(), target.members.end(), core.contexts[context].impl) != target.members.end())
                    members.push_back((int)context);
            mod.targets.push_back({ std::move(members) });
        }
        vector<int> representative(core.impls.size(), -1);
        for (size_t context = 0; context < core.contexts.size(); context++) {
            auto impl = core.contexts[context].impl;
            if (impl < 0 || impl >= (int)core.impls.size())
                throw CompileError { "context names a missing implementation" };
            if (representative[impl] < 0) representative[impl] = (int)context;
            auto &im = core.impls[impl];
            pair<vector<GirTypeId>, vector<GirTypeId>> sig;
            for (auto &p : im.params) sig.first.push_back(im.vars[p.var].type);
            for (auto &result : im.results) sig.second.push_back(result.type);
            GirFunc signature;
            signature.params = sig.first;
            signature.results = sig.second;
            signature.summary = im.summary;
            for (auto &result : im.results) signature.resultProtocols.push_back({ result.request, result.namedLocal });
            mod.funcs.push_back(std::move(signature));
            sigs.push_back(std::move(sig));
        }
        for (auto &g : core.globals) globaltypes.push_back({ g.type, g.kind });
        for (auto &g : core.globals) mod.globals.push_back(LowerGlobal(g));
        for (size_t impl = 0; impl < core.impls.size(); impl++) {
            if (representative[impl] < 0) continue;
            auto body = LowerImpl(core.impls[impl], (int)impl, representative[impl]);
            for (size_t context = representative[impl]; context < core.contexts.size(); context++) {
                if (core.contexts[context].impl != (int)impl) continue;
                auto function = body;
                function.roots = Roots((int)context, (int)impl);
                function.key = core.contexts[context].stablekey;
                function.module = core.contexts[context].module;
                mod.funcs[context] = std::move(function);
            }
        }
        mod.entry = core.entry;
        return std::move(mod);
    }

private:
    const CoreModule &core;
    vector<string> files;
    vector<CoreOrigin> origins;
    function<int(const CoreOrigin &)> originof;
    GirModule mod;
    vector<pair<vector<GirTypeId>, vector<GirTypeId>>> sigs;
    vector<pair<GirTypeId, CoreVarKind>> globaltypes;
    vector<char> noReturn;

    static bool Plain(const CoreStmt &s) {
        switch (s.kind) {
            case CoreStmtKind::Let: case CoreStmtKind::Assign: case CoreStmtKind::AssignOp:
            case CoreStmtKind::Rebind: case CoreStmtKind::Expr: case CoreStmtKind::Append:
            case CoreStmtKind::Print: case CoreStmtKind::Assert:
                return true;
            default:
                return false;
        }
    }

    bool BlockStops(const CoreBlock &b, const vector<char> &nr, int impl = -1) const {
        for (auto &s : b.stmts) {
            bool stops = s.kind == CoreStmtKind::Abort || s.kind == CoreStmtKind::Exit;
            if (s.kind == CoreStmtKind::ReturnFrom || s.kind == CoreStmtKind::ReturnFromForward)
                stops = find(core.targets[s.target].members.begin(), core.targets[s.target].members.end(), impl) == core.targets[s.target].members.end();
            if (s.kind == CoreStmtKind::Expr && s.expr && s.expr->kind == CoreExprKind::Call &&
                s.expr->ctx >= 0 && s.expr->ctx < (int)nr.size())
                {
                    stops = nr[s.expr->ctx];
                    if (stops && impl >= 0)
                        for (auto target : core.impls[core.contexts[s.expr->ctx].impl].summary.escapes)
                            if (find(core.targets[target].members.begin(), core.targets[target].members.end(), impl) != core.targets[target].members.end())
                                stops = false;
                }
            if (s.kind == CoreStmtKind::If && s.otherwise)
                stops = BlockStops(*s.then, nr, impl) && BlockStops(*s.otherwise, nr, impl);
            if (stops) return true;
            if (!Plain(s)) return false;
        }
        return false;
    }

    vector<char> ComputeNoReturn() const {
        vector<char> current(core.contexts.size(), 0);
        for (size_t round = 0; round < core.contexts.size(); round++) {
            auto next = current;
            for (size_t c = 0; c < core.contexts.size(); c++) {
                auto impl = core.contexts[c].impl;
                if (impl >= 0 && impl < (int)core.impls.size())
                    next[c] = BlockStops(core.impls[impl].body, current, impl);
            }
            if (next == current) break;
            current = std::move(next);
        }
        return current;
    }

    // The function being lowered.
    struct Loop {
        size_t depth;
        int breakto;
        bool counted;       // `continue` increments `counter` before the header.
        int header;
        GirTypeId ty;
        int counter;
    };
    vector<GirBlock> blocks;
    vector<GirTypeId> vals;
    int cur = -1;
    vector<int> stack;      // Scopes entered, outermost first.
    vector<GirSlot> slots;
    const vector<CoreVar> *vars = nullptr;
    const vector<CoreResultDescriptor> *currentResults = nullptr;
    const CoreBlock *functionBody = nullptr;
    int functionOrigin = -1;
    int currentImpl = -1;
    int currentFunction = -1;
    vector<int> resultDestinations, activeDestinations;
    set<int> boundNamedSlots;

    int Org(const CoreOrigin &o) { return originof(o); }

    GirTypeId I64() { return mod.IntType(CoreIntTy::I64); }

    // ---------------------------------------------------------------------
    // The builder.

    GirTypeId ValTy(int v) {
        if (v >= 0 && v < (int)vals.size() && vals[v] >= 0) return vals[v];
        return mod.UnitType();
    }

    // The integer type of a value, i64 for a value that has none.
    GirTypeId IntTyOf(int v) {
        auto t = ValTy(v);
        return mod.Type(t).kind == CoreType::Int ? t : I64();
    }

    int EmitDef(GirInst i) {
        if (cur < 0) return 0;
        GirTyEnv env { mod, slots, sigs, vals, nullptr, &blocks, currentFunction < 0 ? nullptr : &mod.funcs[currentFunction] };
        auto r = GirTyper(env).Of(i);
        if (!r.ok()) throw CompileError { cat("internal compiler error: GIR lowering type: ", r.error) };
        auto ty = r.ty;
        auto v = (int)vals.size();
        vals.push_back(ty);
        i.res = v;
        blocks[cur].insts.push_back(std::move(i));
        return v;
    }

    void EmitEffect(GirInst i) {
        if (cur >= 0) blocks[cur].insts.push_back(std::move(i));
    }

    void EmitTerm(GirInst i) {
        if (cur < 0) return;
        blocks[cur].insts.push_back(std::move(i));
        cur = -1;
    }

    void PatchTerm(int b, GirInst i) { blocks[b].insts.push_back(std::move(i)); }

    // A block; its parameters take the next value ids.
    pair<int, vector<int>> NewBlock(vector<GirTypeId> tys) {
        auto b = (int)blocks.size();
        GirBlock blk;
        vector<int> ids;
        for (auto t : tys) {
            ids.push_back((int)vals.size());
            blk.params.push_back({ (int)vals.size(), t });
            vals.push_back(t);
        }
        blocks.push_back(std::move(blk));
        return { b, ids };
    }

    void LeaveTo(size_t depth) {
        for (size_t k = stack.size(); k > depth; k--) {
            GirInst i;
            i.op = GirOp::Leave;
            i.idx = stack[k - 1];
            EmitEffect(std::move(i));
        }
    }

    // A mutable address frozen to read-only when a read-only reference is wanted.
    int FreezeTo(CoreMut m, int r) {
        auto &t = mod.Type(ValTy(r));
        if (m == CoreMut::Const && t.kind == CoreType::Ref && t.mut == CoreMut::Mut) {
            GirInst i;
            i.op = GirOp::Freeze;
            i.a = r;
            return EmitDef(std::move(i));
        }
        return r;
    }

    int Def(GirOp op, int a = -1, int b = -1) {
        GirInst i;
        i.op = op;
        i.a = a;
        i.b = b;
        return EmitDef(std::move(i));
    }

    int ConstInt(GirTypeId t, string text) {
        GirInst i;
        i.op = GirOp::Int;
        i.ty = t;
        i.text = std::move(text);
        return EmitDef(std::move(i));
    }

    static GirInst Br(int b, vector<int> args) {
        GirInst i;
        i.op = GirOp::Br;
        i.idx = b;
        i.vals = std::move(args);
        return i;
    }

    static GirInst CondBr(int c, int t, vector<int> targs, int e, vector<int> eargs) {
        GirInst i;
        i.op = GirOp::CondBr;
        i.a = c;
        i.idx = t;
        i.vals = std::move(targs);
        i.idx2 = e;
        i.vals2 = std::move(eargs);
        return i;
    }

    // The join of the two arms of an `if` expression: each arm that still has a
    // current block branches to it with its value.
    int JoinValue(int endT, int vt, int endF, int vf) {
        if (endT < 0 && endF < 0) {
            cur = -1;
            return 0;
        }
        vector<pair<int, int>> live;
        if (endT >= 0) live.push_back({ endT, vt });
        if (endF >= 0) live.push_back({ endF, vf });
        auto ty = ValTy(live[0].second);
        auto [jb, js] = NewBlock({ ty });
        for (auto &[b, v] : live) PatchTerm(b, Br(jb, { v }));
        cur = jb;
        return js[0];
    }

    // The join of the two arms of an `if` statement, created only if an arm
    // reaches it.
    void JoinArms(int endT, int endF) {
        if (endT < 0 && endF < 0) {
            cur = -1;
            return;
        }
        auto [jb, js] = NewBlock({});
        (void)js;
        if (endT >= 0) PatchTerm(endT, Br(jb, {}));
        if (endF >= 0) PatchTerm(endF, Br(jb, {}));
        cur = jb;
    }

    // ---------------------------------------------------------------------
    // Expressions, places, views and statements.

    int LowerExpr(const CoreExpr &e) {
        switch (e.kind) {
            case CoreExprKind::Lit: return ConstInt(e.type, e.value);
            case CoreExprKind::Bool: {
                GirInst i;
                i.op = GirOp::Bool;
                i.flag = e.flag;
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Read: {
                auto r = LowerPlace(*e.place);
                return Def(GirOp::Load, r);
            }
            case CoreExprKind::Ref: {
                auto r = LowerPlace(*e.place);
                return FreezeTo(e.mut, r);
            }
            case CoreExprKind::Slice: {
                auto vw = LowerView(*e.view);
                auto lo = LowerBound(e.lo);
                auto hi = LowerBound(e.hi);
                GirInst i;
                i.op = GirOp::ViewSlice;
                i.mut = e.mut;
                i.a = vw;
                i.lo = lo;
                i.hi = hi;
                i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Len: {
                int vw;
                if (e.view->kind == CoreView::Of) {
                    auto owner = LowerPlace(*e.view->place);
                    auto &reference = mod.Type(ValTy(owner));
                    if (reference.kind == CoreType::Ref) {
                        auto kind = mod.Type(reference.elem).kind;
                        if (kind == CoreType::Arr || GirOwnerKind(kind)) return Def(GirOp::ArrayLen, owner);
                    }
                    vw = SnapshotPlaceView(*e.view, owner);
                } else {
                    vw = LowerView(*e.view);
                }
                return Def(GirOp::ViewLen, vw);
            }
            case CoreExprKind::Un: {
                auto a = LowerExpr(*e.a);
                GirInst i;
                i.op = GirOp::Un;
                i.un = e.un;
                i.ty = IntTyOf(a);
                i.a = a;
                i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Bin: {
                auto x = LowerExpr(*e.a);
                auto y = LowerExpr(*e.b);
                GirInst i;
                i.op = GirOp::Bin;
                i.bin = e.bin;
                i.ty = IntTyOf(x);
                i.a = x;
                i.b = y;
                i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Cmp: {
                auto x = LowerExpr(*e.a);
                auto y = LowerExpr(*e.b);
                GirInst i;
                i.cmp = e.cmp;
                i.a = x;
                i.b = y;
                auto t = ValTy(x);
                if (mod.Type(t).kind == CoreType::Int) {
                    i.op = GirOp::Cmp;
                    i.ty = t;
                } else {
                    i.op = GirOp::BoolCmp;
                }
                return EmitDef(std::move(i));
            }
            case CoreExprKind::And: case CoreExprKind::Or: {
                auto x = LowerExpr(*e.a);
                return ShortCircuit(e.kind == CoreExprKind::And, x, *e.b);
            }
            case CoreExprKind::Not: {
                auto a = LowerExpr(*e.a);
                return Def(GirOp::Not, a);
            }
            case CoreExprKind::Conv: {
                auto a = LowerExpr(*e.a);
                auto src = IntTyOf(a);
                GirInst i;
                i.op = GirOp::Conv;
                i.conv = e.conv;
                i.ty = src;
                i.ty2 = mod.Type(e.type).kind == CoreType::Int ? e.type : src;
                i.a = a;
                i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Call: {
                auto context = e.ctx;
                auto callee = core.contexts[context].impl;
                auto vs = LowerArgs(e.args, context, Org(e.org));
                if (CoreHasConstruction(core.profile) && !core.impls[callee].summary.escapes.empty()) {
                    auto values = InvokeValues(context, std::move(vs), {}, Org(e.org));
                    return cur >= 0 && !values.empty() ? values[0] : 0;
                }
                GirInst i;
                i.op = GirOp::Call;
                i.idx = context;
                i.vals = std::move(vs);
                i.org = Org(e.org);
                auto v = EmitDef(std::move(i));
                if (e.ctx >= 0 && e.ctx < (int)noReturn.size() && noReturn[e.ctx]) {
                    GirInst end;
                    end.op = GirOp::Unreachable;
                    EmitTerm(std::move(end));
                }
                if (cur >= 0 && mod.Type(ValTy(v)).kind == CoreType::Tuple &&
                    mod.Type(e.type).kind != CoreType::Tuple) {
                    GirInst result;
                    result.op = GirOp::Result;
                    result.a = v;
                    result.idx = 0;
                    return EmitDef(std::move(result));
                }
                return v;
            }
            case CoreExprKind::Push: {
                auto r = LowerPlace(*e.place);
                if (CoreHasConstruction(core.profile) && GirNonfixed(mod, e.a->type)) {
                    auto destination = OpenDestination(*e.a, GirDestPushReceiver { r }, CoreRequest::Value, Org(e.org));
                    auto completed = LowerConstruct(*e.a, destination, Org(e.org));
                    if (cur < 0) return 0;
                    GirInst publish;
                    publish.op = GirOp::DestPublishRef;
                    publish.a = completed;
                    publish.org = Org(e.org);
                    return EmitDef(std::move(publish));
                }
                auto v = LowerExpr(*e.a);
                GirInst i;
                i.op = GirOp::Push;
                i.a = r;
                i.b = v;
                if (CoreHasShrink(core.profile)) i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Pop: {
                auto r = LowerPlace(*e.place);
                GirInst i;
                i.op = GirOp::Pop;
                i.a = r;
                i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::If: {
                auto cv = LowerExpr(*e.a);
                if (cur < 0) return 0;
                auto [tb, ts] = NewBlock({});
                auto [eb, es] = NewBlock({});
                (void)ts; (void)es;
                EmitTerm(CondBr(cv, tb, {}, eb, {}));
                cur = tb;
                auto vt = LowerBlock(nullptr, {}, true, *e.then);
                auto endT = cur;
                cur = eb;
                auto vf = LowerBlock(nullptr, {}, true, *e.otherwise);
                auto endF = cur;
                return JoinValue(endT, vt, endF, vf);
            }
            case CoreExprKind::Block: return LowerBlock(nullptr, {}, true, *e.then);
            case CoreExprKind::Bytes:
                throw CompileError { "internal compiler error: byte construction has no receiving destination" };
            case CoreExprKind::Arr: {
                auto vs = LowerExprs(e.elems);
                GirInst i;
                i.op = GirOp::Arr;
                i.ty = e.type;
                i.vals = std::move(vs);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Fill: {
                auto v = LowerExpr(*e.a);
                GirInst i;
                i.op = GirOp::Fill;
                i.ty = e.type;
                i.a = v;
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Struct: {
                GirInst i;
                i.op = GirOp::Struct;
                i.ty = e.type;
                i.vals = LowerExprs(e.elems);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Copy: {
                if (GirNonfixed(mod, e.type)) throw CompileError { "construction copy requires an explicit receiving channel" };
                GirInst load;
                load.op = GirOp::Load;
                load.a = LowerPlace(*e.place);
                return EmitDef(std::move(load));
            }
            case CoreExprKind::String: case CoreExprKind::ResultLocal:
            case CoreExprKind::Values:
                throw CompileError { "construction expression requires explicit receiving channels" };
        }
        throw CompileError { "internal compiler error: unknown Core expression" };
    }

    // The right operand of `and`/`or`, whose left value is `x`.
    int ShortCircuit(bool isand, int x, const CoreExpr &rhs) {
        if (cur < 0) return 0;
        auto [rb, rs] = NewBlock({});
        auto [jb, js] = NewBlock({ mod.BoolType() });
        (void)rs;
        if (isand) EmitTerm(CondBr(x, rb, {}, jb, { x }));
        else EmitTerm(CondBr(x, jb, { x }, rb, {}));
        cur = rb;
        auto y = LowerExpr(rhs);
        EmitTerm(Br(jb, { y }));
        cur = jb;
        return js[0];
    }

    vector<int> LowerExprs(const vector<CoreExprP> &es) {
        vector<int> out;
        for (auto &e : es) out.push_back(LowerExpr(*e));
        return out;
    }

    vector<int> LowerArgs(const vector<CoreArg> &args, int callee = -1, int org = -1) {
        vector<int> out;
        vector<size_t> constructed;
        for (auto &argument : args) {
            if (auto value = get_if<CoreArgValue>(&argument)) out.push_back(LowerExpr(*value->expr));
            else if (auto construct = get_if<CoreArgConstruct>(&argument)) {
                if (callee < 0) throw CompileError { "construction argument has no receiving call" };
                auto destination = OpenDestination(*construct->expr,
                                                  GirDestArgReceiver { callee, (int)out.size() },
                                                  CoreRequest::Value, org);
                auto completed = LowerConstruct(*construct->expr, destination, org);
                if (cur < 0) return {};
                constructed.push_back(out.size());
                out.push_back(completed);
                activeDestinations.push_back(completed);
            } else {
                auto &reference = get<CoreArgReference>(argument);
                auto address = LowerPlace(*reference.place);
                out.push_back(FreezeTo(reference.mut, address));
            }
            if (cur < 0) return {};
        }
        for (auto position : constructed) {
            auto completed = out[position];
            GirInst argument;
            argument.op = GirOp::DestArg;
            argument.a = completed;
            argument.org = org;
            out[position] = EmitDef(std::move(argument));
            auto active = find(activeDestinations.begin(), activeDestinations.end(), completed);
            if (active == activeDestinations.end()) throw CompileError { "completed argument lost its owned receiving region" };
            activeDestinations.erase(active);
        }
        return out;
    }

    int LowerPlace(const CorePlace &p) {
        switch (p.kind) {
            case CorePlace::Local: {
                GirInst i;
                i.op = GirOp::Slot;
                i.idx = p.index;
                return EmitDef(std::move(i));
            }
            case CorePlace::Global: {
                GirInst i;
                i.op = GirOp::Global;
                i.idx = p.index;
                return EmitDef(std::move(i));
            }
            case CorePlace::Deref: return LowerExpr(*p.expr);
            case CorePlace::Elem: {
                auto vw = LowerView(*p.view);
                auto iv = LowerExpr(*p.expr);
                GirInst i;
                i.op = GirOp::Index;
                i.a = vw;
                i.b = iv;
                i.org = Org(p.org);
                return EmitDef(std::move(i));
            }
            case CorePlace::Field: {
                GirInst i;
                i.op = GirOp::Field;
                i.a = LowerPlace(*p.base);
                i.idx = p.index;
                return EmitDef(std::move(i));
            }
        }
        return 0;
    }

    int LowerView(const CoreView &v) {
        if (v.kind == CoreView::Of) {
            auto r = LowerPlace(*v.place);
            return SnapshotPlaceView(v, r);
        }
        auto s = LowerExpr(*v.expr);
        return Def(GirOp::SliceView, s);
    }

    int SnapshotPlaceView(const CoreView &v, int place) {
        GirInst i;
        i.op = GirOp::Snap;
        i.a = place;
        i.snap = v.place->kind == CorePlace::Local || v.place->kind == CorePlace::Global ||
                 v.place->kind == CorePlace::Field
            ? GirSnapshotMode::Owner : GirSnapshotMode::Borrowed;
        return EmitDef(std::move(i));
    }

    GirBound LowerBound(const CoreBound &b) {
        GirBound out;
        if (b.kind == CoreBound::None) return out;
        out.kind = b.kind == CoreBound::Expr ? GirBound::Val : GirBound::End;
        out.val = LowerExpr(*b.expr);
        return out;
    }

    struct Binding {
        int slot, val, org;
    };

    // A Core block: enter its scope, bind `pre`, run the statements, evaluate
    // the value (a unit when one is wanted and the block has none) and leave
    // the scope. Yields the value; 0 when nothing was produced.
    int LowerBlock(const Loop *lc, const vector<Binding> &pre, bool want, const CoreBlock &b) {
        {
            GirInst i;
            i.op = GirOp::Enter;
            i.idx = b.scope;
            EmitEffect(std::move(i));
        }
        stack.push_back(b.scope);
        for (auto &p : pre) {
            GirInst i;
            i.op = GirOp::Init;
            i.idx = p.slot;
            i.a = p.val;
            i.org = p.org;
            EmitEffect(std::move(i));
        }
        for (auto &s : b.stmts) {
            if (cur < 0) break;
            LowerStmt(lc, s);
        }
        int r = 0;
        if (cur >= 0 && &b == functionBody && CoreHasConstruction(core.profile)) {
            vector<const CoreExpr *> operands;
            if (b.value && b.value->kind == CoreExprKind::Values)
                for (auto &value : b.value->values) operands.push_back(value.get());
            else if (b.value) operands.push_back(b.value.get());
            LowerFunctionReturn(operands, functionOrigin);
        } else if (b.value) r = LowerExpr(*b.value);
        else if (want) {
            GirInst i;
            i.op = GirOp::Unit;
            r = EmitDef(std::move(i));
        }
        {
            GirInst i;
            i.op = GirOp::Leave;
            i.idx = b.scope;
            EmitEffect(std::move(i));
        }
        stack.pop_back();
        return r;
    }

    GirInst Store(int r, int v, int org) {
        GirInst i;
        i.op = GirOp::Store;
        i.a = r;
        i.b = v;
        i.org = org;
        return i;
    }

    bool IsConstructionValue(const CoreExpr &expression) const {
        return expression.type >= 0 && GirNonfixed(mod, expression.type);
    }

    int OpenDestination(const CoreExpr &expression, GirDestReceiver receiver, CoreRequest request, int org) {
        GirInst open;
        open.op = GirOp::DestOpen;
        open.destReceiver = std::move(receiver);
        open.ty = expression.type;
        if (auto slot = get_if<GirDestSlotReceiver>(&open.destReceiver)) open.ty = slots.at(slot->slot).ty;
        if (auto global = get_if<GirDestGlobalReceiver>(&open.destReceiver)) open.ty = mod.globals.at(global->global).ty;
        if (auto argument = get_if<GirDestArgReceiver>(&open.destReceiver)) open.ty = mod.funcs.at(argument->function).params.at(argument->parameter);
        if (auto whole = get_if<GirDestWholeReceiver>(&open.destReceiver)) open.ty = mod.Type(ValTy(whole->reference)).elem;
        if (auto append = get_if<GirDestAppendReceiver>(&open.destReceiver)) open.ty = mod.Type(ValTy(append->reference)).elem;
        if (auto push = get_if<GirDestPushReceiver>(&open.destReceiver)) open.ty = mod.Type(mod.Type(ValTy(push->reference)).elem).elem;
        open.request = request;
        if (expression.kind == CoreExprKind::Bytes)
            open.knownCount = ConstInt(I64(), to_string(expression.bytes.size()));
        if (expression.kind == CoreExprKind::Arr)
            open.knownCount = ConstInt(I64(), to_string(expression.elems.size()));
        open.org = org;
        return EmitDef(std::move(open));
    }

    pair<int, bool> AdaptProducerDestination(int destination, const CoreResultDescriptor &producer, int org) {
        auto receiving = mod.Type(ValTy(destination));
        if (receiving.elem == producer.type && receiving.request == producer.request) return { destination, false };
        GirInst adapt;
        adapt.op = GirOp::DestAdapt;
        adapt.a = destination;
        adapt.ty = producer.type;
        adapt.request = producer.request;
        adapt.org = org;
        return { EmitDef(std::move(adapt)), true };
    }

    int RestoreProducerDestination(int closed, bool adapted, int org) {
        if (!adapted || cur < 0) return closed;
        GirInst restore;
        restore.op = GirOp::DestAdaptFinish;
        restore.a = closed;
        restore.org = org;
        return EmitDef(std::move(restore));
    }

    int FinishDestination(int destination, int org) {
        GirInst finish;
        finish.op = GirOp::DestFinish;
        finish.a = destination;
        finish.org = org;
        return EmitDef(std::move(finish));
    }

    void PublishDestination(int completed, int org) {
        GirInst publish;
        publish.op = GirOp::DestPublish;
        publish.a = completed;
        publish.org = org;
        EmitEffect(std::move(publish));
    }

    int LowerConstructBlock(const CoreBlock &block, int destination, int org) {
        if (!block.value) throw CompileError { "construction block has no result" };
        GirInst enter;
        enter.op = GirOp::Enter;
        enter.idx = block.scope;
        EmitEffect(std::move(enter));
        stack.push_back(block.scope);
        for (auto &statement : block.stmts) {
            if (cur < 0) break;
            LowerStmt(nullptr, statement);
        }
        auto completed = cur < 0 ? 0 : LowerConstruct(*block.value, destination, org);
        GirInst leave;
        leave.op = GirOp::Leave;
        leave.idx = block.scope;
        EmitEffect(std::move(leave));
        stack.pop_back();
        return completed;
    }

    int LowerConstruct(const CoreExpr &expression, int destination, int org) {
        auto inserted = find(activeDestinations.begin(), activeDestinations.end(), destination) == activeDestinations.end();
        if (inserted) activeDestinations.push_back(destination);
        auto done = [&](int completed) {
            if (inserted) {
                auto found = find(activeDestinations.begin(), activeDestinations.end(), destination);
                if (found != activeDestinations.end()) activeDestinations.erase(found);
            }
            return completed;
        };
        if (expression.kind == CoreExprKind::Bytes || expression.kind == CoreExprKind::Copy ||
            expression.kind == CoreExprKind::String || expression.kind == CoreExprKind::ResultLocal ||
            expression.kind == CoreExprKind::Call) org = Org(expression.org);
        switch (expression.kind) {
            case CoreExprKind::Bytes: {
                GirInst bytes;
                bytes.op = GirOp::DestBytes;
                bytes.a = destination;
                bytes.bytes = expression.bytes;
                bytes.org = org;
                EmitEffect(std::move(bytes));
                return done(FinishDestination(destination, org));
            }
            case CoreExprKind::Arr:
                for (auto &element : expression.elems) {
                    if (GirNonfixed(mod, element->type)) {
                        GirInst child;
                        child.op = GirOp::DestChild;
                        child.a = destination;
                        child.ty = element->type;
                        child.org = org;
                        auto childDestination = EmitDef(std::move(child));
                        auto completed = LowerConstruct(*element, childDestination, org);
                        if (cur < 0) return done(0);
                        GirInst attach;
                        attach.op = GirOp::DestAttach;
                        attach.a = destination;
                        attach.b = completed;
                        attach.org = org;
                        EmitEffect(std::move(attach));
                    } else {
                        auto value = LowerExpr(*element);
                        if (cur < 0) return done(0);
                        GirInst write;
                        write.op = GirOp::DestWrite;
                        write.a = destination;
                        write.b = value;
                        write.org = org;
                        EmitEffect(std::move(write));
                    }
                }
                return done(FinishDestination(destination, org));
            case CoreExprKind::Copy: case CoreExprKind::ResultLocal: {
                auto source = expression.kind == CoreExprKind::Copy ? LowerPlace(*expression.place) :
                              EmitDef([&] { GirInst slot; slot.op = GirOp::Slot; slot.idx = expression.var; return slot; }());
                GirInst copy;
                copy.op = GirOp::DestCopy;
                copy.a = destination;
                copy.b = source;
                copy.org = org;
                EmitEffect(std::move(copy));
                return done(FinishDestination(destination, org));
            }
            case CoreExprKind::String:
                for (auto &argument : expression.print) {
                    if (argument.kind == CorePrintArg::Text) {
                        GirInst text;
                        text.op = GirOp::DestBytes;
                        text.a = destination;
                        text.bytes.assign(argument.str.begin(), argument.str.end());
                        text.org = org;
                        EmitEffect(std::move(text));
                    } else {
                        auto value = argument.kind == CorePrintArg::View ? LowerView(*argument.view) : LowerExpr(*argument.expr);
                        if (cur < 0) return done(0);
                        GirInst text;
                        text.op = GirOp::DestText;
                        text.a = destination;
                        text.b = value;
                        text.org = org;
                        EmitEffect(std::move(text));
                    }
                }
                return done(FinishDestination(destination, org));
            case CoreExprKind::Block:
                return done(LowerConstructBlock(*expression.then, destination, org));
            case CoreExprKind::If: {
                auto condition = LowerExpr(*expression.a);
                if (cur < 0) return done(0);
                auto [thenBlock, thenParams] = NewBlock({});
                auto [elseBlock, elseParams] = NewBlock({});
                (void)thenParams;
                (void)elseParams;
                EmitTerm(CondBr(condition, thenBlock, {}, elseBlock, {}));
                auto saved = activeDestinations;
                cur = thenBlock;
                auto thenValue = LowerConstructBlock(*expression.then, destination, org);
                auto thenEnd = cur;
                activeDestinations = saved;
                cur = elseBlock;
                auto elseValue = LowerConstructBlock(*expression.otherwise, destination, org);
                auto elseEnd = cur;
                activeDestinations = saved;
                return done(JoinValue(thenEnd, thenValue, elseEnd, elseValue));
            }
            case CoreExprKind::Call: {
                auto context = expression.ctx;
                auto callee = core.contexts[context].impl;
                if (core.impls[callee].results.size() != 1 || core.impls[callee].summary.unknown)
                    throw CompileError { "construction call requires explicit multiple-result or escape channels" };
                if (!GirNonfixed(mod, core.impls[callee].results[0].type)) {
                    auto snapshot = LowerExpr(expression);
                    if (cur < 0) return done(0);
                    GirInst write;
                    write.op = GirOp::DestSnapshot;
                    write.a = destination;
                    write.b = snapshot;
                    write.org = org;
                    EmitEffect(std::move(write));
                    return done(FinishDestination(destination, org));
                }
                if (!core.impls[callee].summary.escapes.empty()) {
                    auto arguments = LowerArgs(expression.args, context, org);
                    auto values = InvokeValues(context, std::move(arguments), { destination }, org);
                    return done(cur >= 0 ? values[0] : 0);
                }
                auto arguments = LowerArgs(expression.args, context, org);
                if (cur < 0) return done(0);
                auto [producerDestination, adapted] = AdaptProducerDestination(destination, core.impls[callee].results[0], org);
                GirInst call;
                call.op = GirOp::CallConstruct;
                call.idx = context;
                call.vals = std::move(arguments);
                call.vals2 = { producerDestination };
                call.org = org;
                return done(RestoreProducerDestination(EmitDef(std::move(call)), adapted, org));
            }
            case CoreExprKind::Fill: {
                auto slot = (int)slots.size();
                slots.push_back({ expression.a->type, CoreVarKind::Let, stack.empty() ? 0 : stack.back(), slot });
                auto source = OpenDestination(*expression.a, GirDestSlotReceiver { slot }, CoreRequest::Value, org);
                auto completed = LowerConstruct(*expression.a, source, org);
                GirInst repeat;
                repeat.op = GirOp::DestRepeat;
                repeat.a = destination;
                repeat.b = completed;
                repeat.org = org;
                EmitEffect(std::move(repeat));
                return done(FinishDestination(destination, org));
            }
            default: throw CompileError { "construction expression is not a single destination producer" };
        }
    }

    bool HandlesTarget(int target) const {
        auto &members = core.targets.at(target).members;
        return find(members.begin(), members.end(), currentImpl) != members.end();
    }

    int AbandonDestination(int destination, int org) {
        GirInst abandon;
        abandon.op = GirOp::DestAbandon;
        abandon.a = destination;
        abandon.org = org;
        return EmitDef(std::move(abandon));
    }

    void CancelDestination(int cancelled, int org) {
        GirInst cancel;
        cancel.op = GirOp::DestCancel;
        cancel.a = cancelled;
        cancel.org = org;
        EmitEffect(std::move(cancel));
    }

    void FinishTargetReturn(int target, vector<int> values, map<int, int> incomingCancelled, int org) {
        vector<int> cancellations;
        set<int> normalChannels;
        for (size_t result = 0; result < currentResults->size(); result++) {
            auto &descriptor = (*currentResults)[result];
            if (!GirNonfixed(mod, descriptor.type)) continue;
            auto original = resultDestinations[result];
            auto named = descriptor.namedLocal;
            int cancelled = -1;
            if (named && boundNamedSlots.count(*named)) {
                if (HandlesTarget(target)) {
                    GirInst abandon;
                    abandon.op = GirOp::DestAbandonNamed;
                    abandon.idx = *named;
                    abandon.a = values[result];
                    abandon.org = org;
                    cancelled = EmitDef(std::move(abandon));
                } else {
                    GirInst completed;
                    completed.op = GirOp::DestNamed;
                    completed.idx = *named;
                    completed.org = org;
                    cancelled = AbandonDestination(EmitDef(std::move(completed)), org);
                }
                boundNamedSlots.erase(*named);
            } else if (auto found = incomingCancelled.find(original); found != incomingCancelled.end()) {
                cancelled = found->second;
                incomingCancelled.erase(found);
            } else if (original >= 0) cancelled = AbandonDestination(original, org);
            if (cancelled < 0) throw CompileError { "target exit has no owned normal-result cancellation" };
            cancellations.push_back(cancelled);
            if (original >= 0) normalChannels.insert(original);
        }
        for (auto &[original, cancelled] : incomingCancelled) CancelDestination(cancelled, org);
        for (auto active = activeDestinations.rbegin(); active != activeDestinations.rend(); ++active)
            if (!normalChannels.count(*active) && !incomingCancelled.count(*active))
                CancelDestination(AbandonDestination(*active, org), org);
        activeDestinations.clear();
        if (HandlesTarget(target)) {
            for (auto cancelled : cancellations) CancelDestination(cancelled, org);
            auto &descriptor = core.impls[core.targets[target].members[0]];
            for (size_t result = 0; result < values.size(); result++) {
                if (!GirNonfixed(mod, descriptor.results[result].type)) continue;
                GirInst land;
                land.op = GirOp::DestRelocate;
                land.a = values[result];
                land.reason = GirEventReason::ExitValue;
                land.org = org;
                values[result] = EmitDef(std::move(land));
            }
            LeaveTo(0);
            GirInst ret;
            ret.op = GirOp::Ret;
            ret.vals = std::move(values);
            ret.org = org;
            EmitTerm(std::move(ret));
        } else {
            LeaveTo(0);
            GirInst escape;
            escape.op = GirOp::Escape;
            escape.idx = target;
            escape.vals = std::move(values);
            escape.vals2 = std::move(cancellations);
            escape.org = org;
            EmitTerm(std::move(escape));
        }
    }

    vector<int> InvokeValues(int context, vector<int> arguments, const vector<int> &receivers, int org) {
        if (cur < 0) return {};
        auto callee = core.contexts[context].impl;
        auto &function = core.impls[callee];
        vector<GirTypeId> normalTypes;
        vector<int> producerDestinations;
        vector<pair<int, bool>> adapted;
        for (size_t result = 0; result < function.results.size(); result++) {
            auto &descriptor = function.results[result];
            normalTypes.push_back(GirNonfixed(mod, descriptor.type)
                ? mod.CarrierType(CoreType::Built, descriptor.type, descriptor.request) : descriptor.type);
            if (!GirNonfixed(mod, descriptor.type)) continue;
            if (result >= receivers.size() || receivers[result] < 0)
                throw CompileError { "invoke nonfixed result has no receiving channel" };
            auto producer = AdaptProducerDestination(receivers[result], descriptor, org);
            producerDestinations.push_back(producer.first);
            adapted.push_back({ receivers[result], producer.second });
        }
        auto [normalBlock, normalValues] = NewBlock(normalTypes);
        GirInst invoke;
        invoke.op = GirOp::Invoke;
        invoke.idx = context;
        invoke.vals = std::move(arguments);
        invoke.vals2 = std::move(producerDestinations);
        invoke.a = normalBlock;
        invoke.org = org;
        vector<vector<int>> escapeValues;
        for (auto target : function.summary.escapes) {
            auto &member = core.impls[core.targets[target].members[0]];
            vector<GirTypeId> types;
            for (auto &result : member.results)
                types.push_back(GirNonfixed(mod, result.type)
                    ? mod.CarrierType(CoreType::Built, result.type, result.request) : result.type);
            for (auto &result : function.results)
                if (GirNonfixed(mod, result.type)) types.push_back(mod.CarrierType(CoreType::Cancelled, result.type, result.request));
            auto [block, values] = NewBlock(types);
            invoke.escapes.push_back({ target, block, {} });
            escapeValues.push_back(std::move(values));
        }
        auto edges = invoke.escapes;
        EmitTerm(std::move(invoke));
        auto savedScopes = stack;
        auto savedActive = activeDestinations;
        auto savedNamed = boundNamedSlots;
        for (size_t edge = 0; edge < edges.size(); edge++) {
            stack = savedScopes;
            activeDestinations = savedActive;
            boundNamedSlots = savedNamed;
            cur = edges[edge].block;
            auto target = edges[edge].target;
            auto resultCount = core.impls[core.targets[target].members[0]].results.size();
            vector<int> payload(escapeValues[edge].begin(), escapeValues[edge].begin() + resultCount);
            map<int, int> cancelled;
            for (size_t result = 0; result < adapted.size(); result++)
                cancelled[adapted[result].first] = RestoreProducerDestination(escapeValues[edge][resultCount + result], adapted[result].second, org);
            FinishTargetReturn(target, std::move(payload), std::move(cancelled), org);
        }
        stack = std::move(savedScopes);
        activeDestinations = std::move(savedActive);
        boundNamedSlots = std::move(savedNamed);
        cur = normalBlock;
        auto canReturn = context >= 0 && context < (int)noReturn.size() && !noReturn[context];
        if (!canReturn) {
            GirInst end;
            end.op = GirOp::Unreachable;
            EmitTerm(std::move(end));
        } else {
            size_t nonfixed = 0;
            for (size_t result = 0; result < function.results.size(); result++)
                if (GirNonfixed(mod, function.results[result].type))
                    normalValues[result] = RestoreProducerDestination(normalValues[result], adapted[nonfixed++].second, org);
        }
        return normalValues;
    }

    void LowerTargetReturn(const CoreStmt &statement, int org) {
        auto &target = core.impls[core.targets.at(statement.target).members[0]];
        vector<int> destinations(target.results.size(), -1);
        for (size_t result = 0; result < target.results.size(); result++) {
            auto &descriptor = target.results[result];
            if (!GirNonfixed(mod, descriptor.type)) continue;
            GirInst destination;
            destination.op = GirOp::TargetDest;
            destination.idx = statement.target;
            destination.idx2 = (int)result;
            destination.ty = descriptor.type;
            destination.request = descriptor.request;
            destination.org = org;
            destinations[result] = EmitDef(std::move(destination));
        }
        vector<int> values;
        if (statement.kind == CoreStmtKind::ReturnFromForward) values = LowerProducer(*statement.expr, destinations, org);
        else {
            vector<const CoreExpr *> operands;
            for (auto &value : statement.values) operands.push_back(value.get());
            if (operands.empty() && statement.expr) operands.push_back(statement.expr.get());
            if (operands.size() != destinations.size()) throw CompileError { "target return operands differ from its descriptors" };
            for (size_t result = 0; result < operands.size(); result++) {
                values.push_back(destinations[result] >= 0 ? LowerConstruct(*operands[result], destinations[result], org) : LowerExpr(*operands[result]));
                if (cur < 0) return;
            }
        }
        if (cur >= 0) FinishTargetReturn(statement.target, std::move(values), {}, org);
    }

    vector<int> LowerProducer(const CoreExpr &expression, const vector<int> &destinations, int org) {
        vector<int> values;
        auto activeValues = destinations;
        for (auto destination : destinations)
            if (destination >= 0 && find(activeDestinations.begin(), activeDestinations.end(), destination) == activeDestinations.end())
                activeDestinations.push_back(destination);
        auto finished = [&](vector<int> results) {
            if (cur >= 0) for (auto destination : activeValues) {
                auto active = find(activeDestinations.begin(), activeDestinations.end(), destination);
                if (active != activeDestinations.end()) activeDestinations.erase(active);
            }
            return results;
        };
        if (expression.kind == CoreExprKind::Values) {
            if (expression.values.size() != destinations.size()) throw CompileError { "producer result count differs from its receiving channels" };
            for (size_t position = 0; position < destinations.size(); position++) {
                auto &operand = *expression.values[position];
                values.push_back(destinations[position] >= 0 ? LowerConstruct(operand, destinations[position], org) : LowerExpr(operand));
                if (cur < 0) return {};
                if (destinations[position] >= 0) {
                    auto active = find(activeDestinations.begin(), activeDestinations.end(), destinations[position]);
                    if (active != activeDestinations.end()) *active = values.back();
                    activeValues[position] = values.back();
                }
            }
            return finished(std::move(values));
        }
        if (expression.kind != CoreExprKind::Call) throw CompileError { "multiple-result producer is not values or a call" };
        auto context = expression.ctx;
        auto callee = core.contexts[context].impl;
        auto &function = core.impls[callee];
        if (function.results.size() != destinations.size()) throw CompileError { "call result count differs from its receiving channels" };
        if (!function.summary.escapes.empty())
            return finished(InvokeValues(context, LowerArgs(expression.args, context, org), destinations, org));
        GirInst call;
        call.op = GirOp::Call;
        call.idx = context;
        vector<bool> adapted(destinations.size(), false);
        auto arguments = LowerArgs(expression.args, context, org);
        if (cur < 0) return {};
        for (size_t position = 0; position < destinations.size(); position++) {
            if (!GirNonfixed(mod, function.results[position].type)) continue;
            if (destinations[position] < 0) throw CompileError { "nonfixed call result has no receiving destination" };
            call.op = GirOp::CallConstruct;
            auto producer = AdaptProducerDestination(destinations[position], function.results[position], org);
            adapted[position] = producer.second;
            call.vals2.push_back(producer.first);
        }
        call.vals = std::move(arguments);
        call.org = org;
        if (!function.summary.escapes.empty() || function.summary.unknown)
            throw CompileError { "escaping call requires invoke receiving edges" };
        auto pack = EmitDef(std::move(call));
        if (destinations.size() == 1) return finished({ RestoreProducerDestination(pack, adapted[0], org) });
        for (size_t position = 0; position < destinations.size(); position++) {
            GirInst result;
            result.op = GirOp::Result;
            result.a = pack;
            result.idx = (int)position;
            values.push_back(RestoreProducerDestination(EmitDef(std::move(result)), adapted[position], org));
        }
        return finished(std::move(values));
    }

    void LowerConstructionValue(const CoreExpr &expression, GirDestReceiver receiver, int org) {
        auto destination = OpenDestination(expression, std::move(receiver), CoreRequest::Value, org);
        auto completed = LowerConstruct(expression, destination, org);
        if (cur >= 0) PublishDestination(completed, org);
    }

    void AbandonActiveDestinations(int org) {
        for (auto destination = activeDestinations.rbegin(); destination != activeDestinations.rend(); ++destination) {
            GirInst abandon;
            abandon.op = GirOp::DestAbandon;
            abandon.a = *destination;
            abandon.org = org;
            auto cancelled = EmitDef(std::move(abandon));
            GirInst cancel;
            cancel.op = GirOp::DestCancel;
            cancel.a = cancelled;
            cancel.org = org;
            EmitEffect(std::move(cancel));
        }
        activeDestinations.clear();
    }

    void LowerFunctionReturn(const vector<const CoreExpr *> &operands, int org) {
        if (!currentResults || operands.size() != currentResults->size())
            throw CompileError { "return operands do not match the current function result descriptors" };
        vector<int> values;
        vector<pair<int, int>> replacements;
        for (size_t result = 0; result < operands.size(); result++) {
            auto &descriptor = (*currentResults)[result];
            auto &expression = *operands[result];
            if (!GirNonfixed(mod, descriptor.type)) { values.push_back(LowerExpr(expression)); continue; }
            if (expression.kind == CoreExprKind::ResultLocal && descriptor.namedLocal == expression.var &&
                boundNamedSlots.count(expression.var)) {
                GirInst named;
                named.op = GirOp::DestNamed;
                named.idx = expression.var;
                named.org = org;
                values.push_back(EmitDef(std::move(named)));
                boundNamedSlots.erase(expression.var);
                continue;
            }
            auto destination = resultDestinations[result];
            auto replacement = destination < 0 || find(activeDestinations.begin(), activeDestinations.end(), destination) != activeDestinations.end();
            if (replacement) {
                GirInst exitDestination;
                exitDestination.op = GirOp::ResultExitDest;
                exitDestination.idx = (int)result;
                exitDestination.ty = descriptor.type;
                exitDestination.request = descriptor.request;
                exitDestination.org = org;
                destination = EmitDef(std::move(exitDestination));
            }
            auto completed = LowerConstruct(expression, destination, org);
            if (cur < 0) return;
            values.push_back(completed);
            if (replacement) replacements.push_back({ (int)result, completed });
        }
        for (auto &[result, completed] : replacements) {
            auto named = (*currentResults)[result].namedLocal;
            if (named && boundNamedSlots.count(*named)) {
                GirInst abandon;
                abandon.op = GirOp::DestAbandonNamed;
                abandon.idx = *named;
                abandon.a = completed;
                abandon.org = org;
                auto cancelled = EmitDef(std::move(abandon));
                GirInst cancel;
                cancel.op = GirOp::DestCancel;
                cancel.a = cancelled;
                cancel.org = org;
                EmitEffect(std::move(cancel));
                boundNamedSlots.erase(*named);
            }
        }
        AbandonActiveDestinations(org);
        for (auto &[result, completed] : replacements) {
            GirInst land;
            land.op = GirOp::DestRelocate;
            land.a = completed;
            land.reason = GirEventReason::ExitValue;
            land.org = org;
            values[result] = EmitDef(std::move(land));
        }
        LeaveTo(0);
        GirInst ret;
        ret.op = GirOp::Ret;
        ret.vals = std::move(values);
        ret.org = org;
        EmitTerm(std::move(ret));
    }

    void LowerStmt(const Loop *lc, const CoreStmt &s) {
        auto org = Org(s.org);
        switch (s.kind) {
            case CoreStmtKind::Let: {
                if (CoreHasConstruction(core.profile) && GirNonfixed(mod, slots.at(s.var).ty)) {
                    if (currentResults)
                        for (size_t result = 0; result < currentResults->size(); result++)
                            if ((*currentResults)[result].namedLocal == s.var) {
                                auto completed = LowerConstruct(*s.expr, resultDestinations[result], org);
                                if (cur < 0) return;
                                GirInst bind;
                                bind.op = GirOp::DestBind;
                                bind.idx = s.var;
                                bind.a = completed;
                                bind.org = org;
                                EmitEffect(std::move(bind));
                                resultDestinations[result] = -1;
                                boundNamedSlots.insert(s.var);
                                return;
                            }
                    LowerConstructionValue(*s.expr, GirDestSlotReceiver { s.var }, org);
                    return;
                }
                auto v = LowerExpr(*s.expr);
                GirInst i;
                i.op = GirOp::Init;
                i.idx = s.var;
                i.a = v;
                i.org = org;
                EmitEffect(std::move(i));
                return;
            }
            case CoreStmtKind::Assign: {
                auto r = LowerPlace(*s.place);
                auto v = LowerExpr(*s.expr);
                EmitEffect(Store(r, v, org));
                return;
            }
            case CoreStmtKind::AssignOp: {
                auto r = LowerPlace(*s.place);
                auto old = Def(GirOp::Load, r);
                auto rhs = LowerExpr(*s.expr);
                GirInst i;
                i.op = GirOp::Bin;
                i.bin = s.bin;
                i.ty = IntTyOf(old);
                i.a = old;
                i.b = rhs;
                i.org = org;
                auto res = EmitDef(std::move(i));
                EmitEffect(Store(r, res, org));
                return;
            }
            case CoreStmtKind::Rebind: {
                auto v = LowerExpr(*s.expr);
                GirInst i;
                i.op = GirOp::Slot;
                i.idx = s.var;
                auto r = EmitDef(std::move(i));
                EmitEffect(Store(r, v, org));
                return;
            }
            case CoreStmtKind::Expr: LowerExpr(*s.expr); return;
            case CoreStmtKind::Append: {
                auto r = LowerPlace(*s.place);
                auto vw = LowerView(*s.view);
                GirInst i;
                i.op = GirOp::Append;
                i.a = r;
                i.b = vw;
                i.org = org;
                EmitEffect(std::move(i));
                return;
            }
            case CoreStmtKind::PopN: {
                auto r = LowerPlace(*s.place);
                auto count = LowerExpr(*s.expr);
                GirInst i;
                i.op = GirOp::PopN;
                i.a = r;
                i.b = count;
                i.org = org;
                EmitEffect(std::move(i));
                return;
            }
            case CoreStmtKind::Resize: {
                auto r = LowerPlace(*s.place);
                auto size = LowerExpr(*s.expr);
                GirInst i;
                i.op = GirOp::Resize;
                i.a = r;
                i.b = size;
                if (s.expr2) i.vals.push_back(LowerExpr(*s.expr2));
                i.org = org;
                EmitEffect(std::move(i));
                return;
            }
            case CoreStmtKind::Clear: {
                auto r = LowerPlace(*s.place);
                GirInst i;
                i.op = GirOp::Clear;
                i.a = r;
                i.org = org;
                EmitEffect(std::move(i));
                return;
            }
            case CoreStmtKind::AssignWhole: {
                auto r = LowerPlace(*s.place);
                if (CoreHasConstruction(core.profile) && GirNonfixed(mod, mod.Type(ValTy(r)).elem)) {
                    GirInst clear;
                    clear.op = GirOp::Clear;
                    clear.a = r;
                    clear.org = org;
                    EmitEffect(std::move(clear));
                    LowerConstructionValue(*s.expr, GirDestWholeReceiver { r }, org);
                    return;
                }
                GirInst clear;
                clear.op = GirOp::Clear;
                clear.a = r;
                clear.org = org;
                EmitEffect(std::move(clear));
                auto replacement = LowerExpr(*s.expr);
                GirInst replace;
                replace.op = GirOp::Replace;
                replace.a = r;
                replace.b = replacement;
                replace.org = org;
                EmitEffect(std::move(replace));
                return;
            }
            case CoreStmtKind::If: {
                auto cv = LowerExpr(*s.expr);
                if (cur < 0) return;
                if (!s.otherwise) {
                    auto [tb, ts] = NewBlock({});
                    auto [jb, js] = NewBlock({});
                    (void)ts; (void)js;
                    EmitTerm(CondBr(cv, tb, {}, jb, {}));
                    cur = tb;
                    LowerBlock(lc, {}, false, *s.then);
                    EmitTerm(Br(jb, {}));
                    cur = jb;
                } else {
                    auto [tb, ts] = NewBlock({});
                    auto [eb, es] = NewBlock({});
                    (void)ts; (void)es;
                    EmitTerm(CondBr(cv, tb, {}, eb, {}));
                    cur = tb;
                    LowerBlock(lc, {}, false, *s.then);
                    auto endT = cur;
                    cur = eb;
                    LowerBlock(lc, {}, false, *s.otherwise);
                    auto endF = cur;
                    JoinArms(endT, endF);
                }
                return;
            }
            case CoreStmtKind::While: {
                auto [hb, hs] = NewBlock({});
                (void)hs;
                EmitTerm(Br(hb, {}));
                cur = hb;
                auto cv = LowerExpr(*s.expr);
                if (cur < 0) return;
                auto depth = stack.size();
                auto [bb, bs] = NewBlock({});
                auto [xb, xs] = NewBlock({});
                (void)bs; (void)xs;
                EmitTerm(CondBr(cv, bb, {}, xb, {}));
                cur = bb;
                Loop l { depth, xb, false, hb, -1, -1 };
                LowerBlock(&l, {}, false, *s.then);
                EmitTerm(Br(hb, {}));
                cur = xb;
                return;
            }
            case CoreStmtKind::ForRange: {
                auto a = LowerExpr(*s.expr);
                auto b = LowerExpr(*s.expr2);
                if (cur < 0) return;
                auto t = IntTyOf(a);
                auto depth = stack.size();
                auto [hb, hs] = NewBlock({ t });
                auto i = hs[0];
                EmitTerm(Br(hb, { a }));
                cur = hb;
                GirInst cmp;
                cmp.op = GirOp::Cmp;
                cmp.cmp = CoreCmpOp::Lt;
                cmp.ty = t;
                cmp.a = i;
                cmp.b = b;
                auto c = EmitDef(std::move(cmp));
                auto [bb, bs] = NewBlock({});
                auto [xb, xs] = NewBlock({});
                (void)bs; (void)xs;
                EmitTerm(CondBr(c, bb, {}, xb, {}));
                cur = bb;
                Loop l { depth, xb, true, hb, t, i };
                LowerBlock(&l, { { s.var, i, org } }, false, *s.then);
                if (cur >= 0) Increment(l);
                cur = xb;
                return;
            }
            case CoreStmtKind::ForEach: return LowerForEach(s, org);
            case CoreStmtKind::Ret: {
                if (CoreHasConstruction(core.profile)) {
                    vector<const CoreExpr *> values;
                    if (s.expr) values.push_back(s.expr.get());
                    LowerFunctionReturn(values, org);
                    return;
                }
                vector<int> vs;
                if (s.expr) vs.push_back(LowerExpr(*s.expr));
                LeaveTo(0);
                GirInst i;
                i.op = GirOp::Ret;
                i.vals = std::move(vs);
                i.org = org;
                EmitTerm(std::move(i));
                return;
            }
            case CoreStmtKind::Break:
                if (lc) {
                    LeaveTo(lc->depth);
                    EmitTerm(Br(lc->breakto, {}));
                }
                return;
            case CoreStmtKind::Continue:
                if (lc) {
                    LeaveTo(lc->depth);
                    if (!lc->counted) EmitTerm(Br(lc->header, {}));
                    else Increment(*lc);
                }
                return;
            case CoreStmtKind::Print: {
                vector<GirPart> parts;
                for (auto &a : s.print) {
                    GirPart p;
                    if (a.kind == CorePrintArg::Text) {
                        p.text = true;
                        p.str = a.str;
                    } else {
                        p.val = a.kind == CorePrintArg::View ? LowerView(*a.view) : LowerExpr(*a.expr);
                        if (CoreHasConstruction(core.profile)) {
                            GirInst render;
                            render.op = GirOp::Render;
                            render.a = p.val;
                            render.org = org;
                            p.val = EmitDef(std::move(render));
                        }
                    }
                    parts.push_back(std::move(p));
                }
                GirInst i;
                i.op = GirOp::Print;
                i.parts = std::move(parts);
                i.org = org;
                EmitEffect(std::move(i));
                return;
            }
            case CoreStmtKind::Assert: {
                auto cv = LowerExpr(*s.expr);
                if (cur < 0) return;
                auto [pb, ps] = NewBlock({});
                auto [fb, fs] = NewBlock({});
                (void)ps; (void)fs;
                EmitTerm(CondBr(cv, pb, {}, fb, {}));
                cur = fb;
                GirInst i;
                i.op = GirOp::Abort;
                i.abort = GirAbortKind::Assert;
                i.org = org;
                EmitTerm(std::move(i));
                cur = pb;
                return;
            }
            case CoreStmtKind::Abort: {
                GirInst i;
                i.op = GirOp::Abort;
                i.abort = GirAbortKind::UserAbort;
                i.text = s.message;   // Not in the wire format; the C emitter prints it.
                i.org = org;
                EmitTerm(std::move(i));
                return;
            }
            case CoreStmtKind::Exit: {
                auto v = LowerExpr(*s.expr);
                GirInst i;
                i.op = GirOp::Exit;
                i.a = v;
                i.org = org;
                EmitTerm(std::move(i));
                return;
            }
            case CoreStmtKind::RetValues: {
                vector<const CoreExpr *> operands;
                for (auto &value : s.values) operands.push_back(value.get());
                LowerFunctionReturn(operands, org);
                return;
            }
            case CoreStmtKind::AppendValue: {
                auto reference = LowerPlace(*s.place);
                auto value = LowerExpr(*s.expr);
                if (cur < 0) return;
                GirInst append;
                append.op = GirOp::AppendValue;
                append.a = reference;
                append.b = value;
                append.org = org;
                EmitEffect(std::move(append));
                return;
            }
            case CoreStmtKind::AppendConstruct: {
                auto reference = LowerPlace(*s.place);
                auto destination = OpenDestination(*s.expr, GirDestAppendReceiver { reference }, CoreRequest::ElementRun, org);
                auto completed = LowerConstruct(*s.expr, destination, org);
                if (cur >= 0) PublishDestination(completed, org);
                return;
            }
            case CoreStmtKind::Receive: {
                vector<int> destinations(s.vars.size(), -1);
                for (size_t position = 0; position < s.vars.size(); position++) {
                    auto slot = s.vars[position];
                    auto type = slots.at(slot).ty;
                    if (!GirNonfixed(mod, type)) continue;
                    CoreExpr receiver;
                    receiver.type = type;
                    destinations[position] = OpenDestination(receiver, GirDestSlotReceiver { slot }, CoreRequest::Value, org);
                }
                auto values = LowerProducer(*s.expr, destinations, org);
                if (cur < 0) return;
                for (size_t position = 0; position < values.size(); position++) {
                    if (destinations[position] >= 0) PublishDestination(values[position], org);
                    else { GirInst init; init.op = GirOp::Init; init.idx = s.vars[position]; init.a = values[position]; init.org = org; EmitEffect(std::move(init)); }
                }
                return;
            }
            case CoreStmtKind::RetForward: {
                vector<int> destinations = resultDestinations;
                for (size_t position = 0; position < destinations.size(); position++) {
                    auto &descriptor = (*currentResults)[position];
                    if (!GirNonfixed(mod, descriptor.type)) continue;
                    if (destinations[position] < 0) throw CompileError { "forward return replaces an already bound named channel" };
                }
                auto values = LowerProducer(*s.expr, destinations, org);
                if (cur < 0) return;
                AbandonActiveDestinations(org);
                LeaveTo(0);
                GirInst ret;
                ret.op = GirOp::Ret;
                ret.vals = std::move(values);
                ret.org = org;
                EmitTerm(std::move(ret));
                return;
            }
            case CoreStmtKind::ReturnFrom: case CoreStmtKind::ReturnFromForward:
                return LowerTargetReturn(s, org);
            case CoreStmtKind::BreakValue:
                throw CompileError { "construction break requires its enclosing value receiver" };
        }
    }

    // The counter's increment and the branch back to the loop header.
    void Increment(const Loop &l) {
        GirInst n;
        n.op = GirOp::Next;
        n.ty = l.ty;
        n.a = l.counter;
        auto v = EmitDef(std::move(n));
        EmitTerm(Br(l.header, { v }));
    }

    void LowerForEach(const CoreStmt &s, int org) {
        // The source is sampled once. An owner that is a grow-only array is
        // kept by address so that its length can be read again.
        int owner = -1, vw;
        if (s.view->kind == CoreView::Of) {
            owner = LowerPlace(*s.view->place);
            GirInst i;
            i.op = GirOp::Snap;
            i.a = owner;
            i.snap = s.view->place->kind == CorePlace::Local || s.view->place->kind == CorePlace::Global ||
                     s.view->place->kind == CorePlace::Field
                ? GirSnapshotMode::Owner : GirSnapshotMode::Borrowed;
            vw = EmitDef(std::move(i));
        } else {
            auto sl = LowerExpr(*s.view->expr);
            vw = Def(GirOp::SliceView, sl);
        }
        auto resizable = owner >= 0 && IsResizableRef(owner);
        int sampled = resizable ? 0 : Def(GirOp::ViewLen, vw);
        auto startat = ConstInt(I64(), "0");
        if (cur < 0) return;
        auto depth = stack.size();
        auto [hb, hs] = NewBlock({ I64() });
        auto i = hs[0];
        EmitTerm(Br(hb, { startat }));
        cur = hb;
        int n = resizable ? Def(GirOp::ArrayLen, owner) : sampled;
        GirInst cmp;
        cmp.op = GirOp::Cmp;
        cmp.cmp = CoreCmpOp::Lt;
        cmp.ty = I64();
        cmp.a = i;
        cmp.b = n;
        auto c = EmitDef(std::move(cmp));
        auto [bb, bs] = NewBlock({});
        auto [xb, xs] = NewBlock({});
        (void)bs; (void)xs;
        EmitTerm(CondBr(c, bb, {}, xb, {}));
        cur = bb;
        auto elem = Def(GirOp::Elem, vw, i);
        int ev;
        if (s.byRef) {
            auto &vt = mod.Type((*vars)[s.var].type);
            ev = vt.kind == CoreType::Ref ? FreezeTo(vt.mut, elem) : elem;
        } else {
            ev = Def(GirOp::Load, elem);
        }
        vector<Binding> pre { { s.var, ev, org } };
        if (s.index >= 0) pre.push_back({ s.index, i, org });
        Loop l { depth, xb, true, hb, I64(), i };
        LowerBlock(&l, pre, false, *s.then);
        if (cur >= 0) Increment(l);
        cur = xb;
    }

    bool IsResizableRef(int r) {
        auto &t = mod.Type(ValTy(r));
        if (t.kind != CoreType::Ref) return false;
        return GirResizableKind(mod.Type(t.elem).kind);
    }

    // ---------------------------------------------------------------------
    // The scope tree: the parent of every Core block, from the blocks'
    // nesting.

    using ScopePairs = vector<pair<int, int>>;

    void ExprScopes(int parent, const CoreExpr &e, ScopePairs &out) {
        if (e.place) PlaceScopes(parent, *e.place, out);
        if (e.view) ViewScopes(parent, *e.view, out);
        if (e.kind == CoreExprKind::Slice) {
            if (e.lo.expr) ExprScopes(parent, *e.lo.expr, out);
            if (e.hi.expr) ExprScopes(parent, *e.hi.expr, out);
        }
        if (e.a) ExprScopes(parent, *e.a, out);
        if (e.b) ExprScopes(parent, *e.b, out);
        for (auto &a : e.args) {
            if (auto value = get_if<CoreArgValue>(&a)) ExprScopes(parent, *value->expr, out);
            else if (auto construct = get_if<CoreArgConstruct>(&a)) ExprScopes(parent, *construct->expr, out);
            else PlaceScopes(parent, *get<CoreArgReference>(a).place, out);
        }
        for (auto &el : e.elems) ExprScopes(parent, *el, out);
        for (auto &el : e.values) ExprScopes(parent, *el, out);
        for (auto &arg : e.print) {
            if (arg.kind == CorePrintArg::Expr) ExprScopes(parent, *arg.expr, out);
            if (arg.kind == CorePrintArg::View) ViewScopes(parent, *arg.view, out);
        }
        if (e.then) BlockScopes(parent, *e.then, out);
        if (e.otherwise) BlockScopes(parent, *e.otherwise, out);
    }

    void PlaceScopes(int parent, const CorePlace &p, ScopePairs &out) {
        if (p.kind == CorePlace::Deref) ExprScopes(parent, *p.expr, out);
        if (p.kind == CorePlace::Elem) {
            ViewScopes(parent, *p.view, out);
            ExprScopes(parent, *p.expr, out);
        }
    }

    void ViewScopes(int parent, const CoreView &v, ScopePairs &out) {
        if (v.kind == CoreView::Of) PlaceScopes(parent, *v.place, out);
        else ExprScopes(parent, *v.expr, out);
    }

    void BlockScopes(int parent, const CoreBlock &b, ScopePairs &out) {
        out.push_back({ b.scope, parent });
        for (auto &s : b.stmts) StmtScopes(b.scope, s, out);
        if (b.value) ExprScopes(b.scope, *b.value, out);
    }

    // The same order as the statement's parts are lowered, which does not
    // matter to a table indexed by scope number but keeps the walk readable.
    void StmtScopes(int parent, const CoreStmt &s, ScopePairs &out) {
        if (s.place) PlaceScopes(parent, *s.place, out);
        if (s.view) ViewScopes(parent, *s.view, out);
        if (s.expr) ExprScopes(parent, *s.expr, out);
        if (s.expr2) ExprScopes(parent, *s.expr2, out);
        for (auto &a : s.print) {
            if (a.kind == CorePrintArg::Expr) ExprScopes(parent, *a.expr, out);
            if (a.kind == CorePrintArg::View) ViewScopes(parent, *a.view, out);
        }
        for (auto &value : s.values) ExprScopes(parent, *value, out);
        if (s.then) BlockScopes(parent, *s.then, out);
        if (s.otherwise) BlockScopes(parent, *s.otherwise, out);
    }

    static vector<int> ScopeTable(const ScopePairs &pairs) {
        int n = 0;
        for (auto &p : pairs) n = max(n, p.first + 1);
        vector<int> t(n, -1);
        for (auto &p : pairs) t[p.first] = p.second;
        return t;
    }

    // ---------------------------------------------------------------------
    // Functions.

    void Begin(const vector<CoreVar> *vs) {
        blocks.clear();
        vals.clear();
        cur = -1;
        stack.clear();
        slots.clear();
        vars = vs;
        currentResults = nullptr;
        functionBody = nullptr;
        functionOrigin = -1;
        currentImpl = -1;
        currentFunction = -1;
        resultDestinations.clear();
        activeDestinations.clear();
        boundNamedSlots.clear();
        if (vs)
            for (size_t i = 0; i < vs->size(); i++)
                slots.push_back({ (*vs)[i].type, (*vs)[i].kind, (*vs)[i].scope, (int)i });
    }

    GirRootInfo Roots(int contextIndex, int implIndex) const {
        GirRootInfo out;
        if (contextIndex < 0 || contextIndex >= (int)core.contexts.size() ||
            implIndex < 0 || implIndex >= (int)core.impls.size() ||
            core.contexts[contextIndex].impl != implIndex) return out;
        auto &impl = core.impls[implIndex];
        auto &context = core.contexts[contextIndex];
        out.results.resize(impl.results.size());
        for (size_t i = 0; i < impl.params.size(); i++) {
            auto var = impl.params[i].var;
            if (CoreHasConstruction(core.profile) && GirNonfixed(mod, impl.vars[var].type)) continue;
            auto roots = find_if(context.varroots.begin(), context.varroots.end(),
                [&](auto &entry) { return entry.first == var; });
            if (roots != context.varroots.end()) out.params.push_back({ (int)i, roots->second });
            for (size_t j = 0; j < context.varroots.size() && j < context.hascontent.size(); j++)
                if (context.varroots[j].first == var && context.hascontent[j])
                    out.contents.push_back({ (int)i, j < context.content.size() ? context.content[j] : vector<CoreRootRef> {} });
        }
        for (size_t i = 0; i < context.resultroots.size() && i < out.results.size(); i++)
            out.results[i] = context.resultroots[i];
        return out;
    }

    GirFunc LowerImpl(const CoreImpl &impl, int implIndex, int contextIndex) {
        Begin(&impl.vars);
        currentResults = &impl.results;
        currentImpl = implIndex;
        currentFunction = contextIndex;
        functionBody = &impl.body;
        functionOrigin = impl.vars.empty() ? -1 : Org(impl.vars[0].org);
        vector<GirTypeId> ptys;
        for (auto &p : impl.params) ptys.push_back(impl.vars[p.var].type);
        vector<GirTypeId> entryTypes;
        for (auto type : ptys)
            entryTypes.push_back(CoreHasConstruction(core.profile) && GirNonfixed(mod, type)
                                     ? mod.RefType(CoreMut::Mut, type) : type);
        if (CoreHasConstruction(core.profile))
            for (auto &result : impl.results)
                if (GirNonfixed(mod, result.type))
                    entryTypes.push_back(mod.CarrierType(CoreType::Dest, result.type, result.request));
        auto [b0, ps] = NewBlock(entryTypes);
        cur = b0;
        resultDestinations.assign(impl.results.size(), -1);
        size_t channel = ptys.size();
        if (CoreHasConstruction(core.profile))
            for (size_t result = 0; result < impl.results.size(); result++)
                if (GirNonfixed(mod, impl.results[result].type)) resultDestinations[result] = ps[channel++];
        vector<Binding> pre;
        for (size_t k = 0; k < impl.params.size(); k++)
            pre.push_back({ impl.params[k].var, ps[k], Org(impl.vars[impl.params[k].var].org) });
        auto v = LowerBlock(nullptr, pre, false, impl.body);
        if (cur >= 0) {
            GirInst i;
            i.op = GirOp::Ret;
            if (impl.body.value) i.vals.push_back(v);
            EmitTerm(std::move(i));
        }
        GirFunc f;
        f.name = impl.name;
        f.params = ptys;
        for (auto &result : impl.results) {
            f.results.push_back(result.type);
            if (CoreHasConstruction(core.profile))
                f.resultProtocols.push_back({ result.request, result.namedLocal });
        }
        f.slots = slots;
        ScopePairs pairs;
        BlockScopes(-1, impl.body, pairs);
        f.scopes = ScopeTable(pairs);
        f.blocks = std::move(blocks);
        f.roots = Roots(contextIndex, implIndex);
        f.summary = impl.summary;
        f.org = impl.vars.empty() ? -1 : Org(impl.vars[0].org);
        f.key = core.contexts[contextIndex].stablekey;
        f.module = core.contexts[contextIndex].module;
        return f;
    }

    GirGlobal LowerGlobal(const CoreGlobal &g) {
        Begin(nullptr);
        auto nonfixed = CoreHasConstruction(core.profile) && GirNonfixed(mod, g.type);
        auto [b0, ps] = NewBlock(nonfixed ? vector<GirTypeId> { mod.CarrierType(CoreType::Dest, g.type, CoreRequest::Value) } : vector<GirTypeId> {});
        cur = b0;
        auto v = nonfixed ? LowerConstruct(*g.init, ps[0], Org(g.org)) : LowerExpr(*g.init);
        GirInst r;
        r.op = GirOp::Ret;
        r.vals = { v };
        r.org = Org(g.org);
        EmitTerm(std::move(r));
        GirGlobal out;
        out.name = g.name;
        out.ty = g.type;
        out.kind = g.kind;
        out.org = Org(g.org);
        out.module = g.module;
        out.init.module = g.module;
        out.init.key = Sha256::Of(cat(g.module, "::", g.name)).Short();
        out.init.name = g.name;
        out.init.results = { g.type };
        if (CoreHasConstruction(core.profile)) out.init.resultProtocols = { { nonfixed ? CoreRequest::Value : CoreRequest::Register, nullopt } };
        out.init.slots = slots;
        ScopePairs pairs;
        ExprScopes(-1, *g.init, pairs);
        out.init.scopes = ScopeTable(pairs);
        out.init.blocks = std::move(blocks);
        out.init.roots.results.resize(1);
        out.init.summary.unknown = true;
        out.init.org = Org(g.org);
        return out;
    }
};

}  // namespace goose
