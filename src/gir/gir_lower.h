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
        size_t exitDepth;
        size_t constructionDepth;
    };
    const Loop *lexicalLoop = nullptr;
    struct ValueBoundary {
        int receiving = -1;
        int catchBlock = -1;
        int catchValue = -1;
        GirTypeId type = -1;
        int depth = 0;
        size_t exitDepth = 0;
        size_t constructionDepth = 0;
        function<void(const CoreExpr &, int)> complete;
    };
    ValueBoundary *valueBoundary = nullptr;
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
    vector<int> activeReceivings;
    vector<int> resultReceivings;
    map<int, int> rawReceivings;
    map<int, int> receivingParents;
    vector<int> exitReservations;
    map<int, int> reservationReceivings, reservationBuilders, rawReservations, receivingReservations;
    set<int> boundNamedSlots;
    set<int> waitingExits;
    set<int> delegatedReceivings;
    struct CompletionBoundary {
        vector<int> tickets;
        vector<int> handles;
    };
    vector<CompletionBoundary *> completionBoundaries;
    struct CompletionBranch {
        vector<int> scopes, active, reservations;
        set<int> named, waiting, delegated;
        map<int, int> rawReceiving, rawReservation, parents, reservationReceiving, builders, receivingReservation;
        vector<vector<int>> handles;
    };

    int Org(const CoreOrigin &o) { return originof(o); }

    int CompletionOrigin(const CoreExpr &expression) {
        switch (expression.kind) {
            case CoreExprKind::Bytes: case CoreExprKind::String: case CoreExprKind::Copy: case CoreExprKind::ResultLocal:
            case CoreExprKind::Call: case CoreExprKind::Un: case CoreExprKind::Bin: case CoreExprKind::Conv:
            case CoreExprKind::Slice: case CoreExprKind::Pop: case CoreExprKind::Arr: case CoreExprKind::Fill:
            case CoreExprKind::If: case CoreExprKind::Block: case CoreExprKind::Push: return Org(expression.org);
            default: return mod.origins.empty() ? -1 : 0;
        }
    }

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

    int BorrowTo(CoreMut m, int r) {
        auto &t = mod.Type(ValTy(r));
        if (m == CoreMut::Const && t.kind == CoreType::Ref && t.mut == CoreMut::Mut) {
            GirInst i;
            i.op = GirOp::Freeze;
            i.a = r;
            return EmitDef(std::move(i));
        }
        if (m == CoreMut::Mut && mod.profile == CoreProfile::Shrink && t.kind == CoreType::Ref &&
            t.mut == CoreMut::Mut && GirResizableKind(mod.Type(t.elem).kind)) {
            GirInst borrow;
            borrow.op = GirOp::OwnerBorrow;
            borrow.a = r;
            return EmitDef(std::move(borrow));
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
                return BorrowTo(e.mut, r);
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
                    DropCompletedReceiving(completed);
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
                auto saved = SaveCompletionBranch();
                cur = tb;
                auto vt = LowerBlock(lexicalLoop, {}, true, *e.then);
                auto endT = cur;
                RestoreCompletionBranch(saved);
                cur = eb;
                auto vf = LowerBlock(lexicalLoop, {}, true, *e.otherwise);
                auto endF = cur;
                return JoinValue(endT, vt, endF, vf);
            }
            case CoreExprKind::Block: return LowerValueBlock(*e.then, e.type);
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
                activeReceivings.push_back(rawReceivings.at(completed));
            } else {
                auto &reference = get<CoreArgReference>(argument);
                auto address = LowerPlace(*reference.place);
                out.push_back(BorrowTo(reference.mut, address));
            }
            if (cur < 0) return {};
        }
        for (auto position : constructed) {
            auto completed = out[position];
            auto active = find(activeReceivings.begin(), activeReceivings.end(), rawReceivings.at(completed));
            if (active == activeReceivings.end()) throw CompileError { "completed argument lost its owned receiving region" };
            activeReceivings.erase(active);
            DropCompletedReceiving(completed);
            GirInst argument;
            argument.op = GirOp::DestArg;
            argument.a = completed;
            argument.org = org;
            out[position] = EmitDef(std::move(argument));
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
        auto savedLoop = lexicalLoop;
        lexicalLoop = lc;
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
            if (b.value) LowerImplicitReturn(*b.value);
            else LowerFunctionReturn({}, functionOrigin);
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
        lexicalLoop = savedLoop;
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
        auto adapted = EmitDef(std::move(adapt));
        rawReceivings[adapted] = rawReceivings.at(destination);
        return { adapted, true };
    }

    int RestoreProducerDestination(int closed, bool adapted, int org) {
        if (!adapted || cur < 0) return closed;
        GirInst restore;
        restore.op = GirOp::DestAdaptFinish;
        restore.a = closed;
        restore.org = org;
        auto restored = EmitDef(std::move(restore));
        if (auto receiving = rawReceivings.find(closed); receiving != rawReceivings.end())
            rawReceivings[restored] = receiving->second;
        return restored;
    }

    void DropCompletedReceiving(int completed, int stop = -1) {
        auto found = rawReceivings.find(completed);
        if (found == rawReceivings.end()) return;
        auto receiver = found->second;
        while (receiver >= 0 && receiver != stop) {
            if (find(resultReceivings.begin(), resultReceivings.end(), receiver) != resultReceivings.end() ||
                find(activeReceivings.begin(), activeReceivings.end(), receiver) != activeReceivings.end() ||
                any_of(exitReservations.begin(), exitReservations.end(), [&](int ticket) {
                    return reservationReceivings.at(ticket) == receiver;
                })) break;
            GirInst drop;
            drop.op = GirOp::ReceivingDrop;
            drop.a = receiver;
            EmitEffect(std::move(drop));
            delegatedReceivings.erase(receiver);
            receiver = receivingParents.at(receiver);
            found->second = receiver;
        }
    }

    int FinishDestination(int destination, int org) {
        destination = RefreshDestination(destination);
        GirInst finish;
        finish.op = GirOp::DestFinish;
        finish.a = destination;
        finish.org = org;
        auto completed = EmitDef(std::move(finish));
        rawReceivings[completed] = rawReceivings.at(destination);
        return completed;
    }

    void PublishDestination(int completed, int org) {
        DropCompletedReceiving(completed);
        GirInst publish;
        publish.op = GirOp::DestPublish;
        publish.a = completed;
        publish.org = org;
        EmitEffect(std::move(publish));
    }

    int LowerValueBlock(const CoreBlock &block, GirTypeId type) {
        ValueBoundary boundary { -1, -1, -1, type, (int)stack.size(), exitReservations.size(), activeReceivings.size() };
        auto previous = valueBoundary;
        valueBoundary = &boundary;
        auto value = LowerBlock(lexicalLoop, {}, true, block);
        valueBoundary = previous;
        if (boundary.catchBlock < 0) return value;
        if (cur >= 0) EmitTerm(Br(boundary.catchBlock, { value }));
        cur = boundary.catchBlock;
        return boundary.catchValue;
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
            LowerStmt(lexicalLoop, statement);
        }
        auto completed = cur < 0 ? 0 : LowerConstruct(*block.value, RefreshDestination(destination), org);
        GirInst leave;
        leave.op = GirOp::Leave;
        leave.idx = block.scope;
        EmitEffect(std::move(leave));
        stack.pop_back();
        return completed;
    }

    int LowerConstruct(const CoreExpr &expression, int destination, int org) {
        auto receiving = OpenReceiving(destination);
        destination = RenewReceiving(receiving);
        auto inserted = find(activeReceivings.begin(), activeReceivings.end(), receiving) == activeReceivings.end();
        if (inserted) activeReceivings.push_back(receiving);
        auto done = [&](int completed) {
            if (cur >= 0 && mod.Type(ValTy(completed)).kind == CoreType::Built) {
                DropCompletedReceiving(completed, receiving);
                rawReceivings[completed] = receiving;
            }
            if (inserted) {
                auto found = find(activeReceivings.begin(), activeReceivings.end(), receiving);
                if (found != activeReceivings.end()) activeReceivings.erase(found);
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
                        destination = RefreshDestination(destination);
                        GirInst child;
                        child.op = GirOp::DestChild;
                        child.a = destination;
                        child.ty = element->type;
                        child.org = org;
                        auto childDestination = EmitDef(std::move(child));
                        auto completed = LowerConstruct(*element, childDestination, org);
                        if (cur < 0) return done(0);
                        destination = RefreshDestination(destination);
                        DropCompletedReceiving(completed);
                        GirInst attach;
                        attach.op = GirOp::DestAttach;
                        attach.a = destination;
                        attach.b = completed;
                        attach.org = org;
                        EmitEffect(std::move(attach));
                    } else {
                        auto value = LowerExpr(*element);
                        if (cur < 0) return done(0);
                        destination = RefreshDestination(destination);
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
                destination = RefreshDestination(destination);
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
                        destination = RefreshDestination(destination);
                        GirInst text;
                        text.op = GirOp::DestText;
                        text.a = destination;
                        text.b = value;
                        text.org = org;
                        EmitEffect(std::move(text));
                    }
                }
                return done(FinishDestination(destination, org));
            case CoreExprKind::Block: {
                auto type = mod.CarrierType(CoreType::Built, mod.Type(ValTy(destination)).elem, mod.Type(ValTy(destination)).request);
                auto blockReceiving = OpenReceiving(destination);
                ValueBoundary boundary { blockReceiving, -1, -1, type, (int)stack.size(), exitReservations.size(), activeReceivings.size() };
                auto previous = valueBoundary;
                valueBoundary = &boundary;
                auto completed = LowerConstructBlock(*expression.then, RenewReceiving(blockReceiving), org);
                valueBoundary = previous;
                if (cur >= 0) {
                    DropCompletedReceiving(completed, blockReceiving);
                    CancelDestination(CancelReceiving(blockReceiving, { completed }, org), org);
                }
                if (boundary.catchBlock < 0) return done(completed);
                if (cur >= 0) EmitTerm(Br(boundary.catchBlock, { completed }));
                cur = boundary.catchBlock;
                rawReceivings[boundary.catchValue] = receiving;
                return done(boundary.catchValue);
            }
            case CoreExprKind::If: {
                auto condition = LowerExpr(*expression.a);
                if (cur < 0) return done(0);
                destination = RefreshDestination(destination);
                auto [thenBlock, thenParams] = NewBlock({});
                auto [elseBlock, elseParams] = NewBlock({});
                (void)thenParams;
                (void)elseParams;
                EmitTerm(CondBr(condition, thenBlock, {}, elseBlock, {}));
                auto saved = SaveCompletionBranch();
                cur = thenBlock;
                auto thenValue = LowerConstructBlock(*expression.then, destination, org);
                if (cur >= 0) DropCompletedReceiving(thenValue, receiving);
                auto thenEnd = cur;
                RestoreCompletionBranch(saved);
                cur = elseBlock;
                auto elseValue = LowerConstructBlock(*expression.otherwise, destination, org);
                if (cur >= 0) DropCompletedReceiving(elseValue, receiving);
                auto elseEnd = cur;
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
                    destination = RefreshDestination(destination);
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
                    if (cur < 0) return done(0);
                    destination = RefreshDestination(destination);
                    auto values = InvokeValues(context, std::move(arguments), { destination }, org);
                    return done(cur >= 0 ? values[0] : 0);
                }
                auto arguments = LowerArgs(expression.args, context, org);
                if (cur < 0) return done(0);
                destination = RefreshDestination(destination);
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
                if (cur < 0) return done(0);
                destination = RefreshDestination(destination);
                DropCompletedReceiving(completed);
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

    int OpenReceiving(int destination) {
        auto parent = rawReceivings.find(destination);
        auto parentReceiving = parent == rawReceivings.end() ? -1 : parent->second;
        GirInst open;
        open.op = GirOp::ReceivingOpen;
        open.a = destination;
        auto receiving = EmitDef(std::move(open));
        rawReceivings[destination] = receiving;
        receivingParents[receiving] = parentReceiving;
        if (auto ticket = rawReservations.find(destination); ticket != rawReservations.end()) {
            receivingReservations[receiving] = ticket->second;
            reservationBuilders.try_emplace(ticket->second, receiving);
        }
        if (auto ticket = rawReservations.find(destination); ticket != rawReservations.end())
            for (auto boundary = completionBoundaries.rbegin(); boundary != completionBoundaries.rend(); ++boundary)
                for (size_t position = 0; position < (*boundary)->tickets.size(); position++)
                    if ((*boundary)->tickets[position] == ticket->second && (*boundary)->handles[position] < 0) {
                        (*boundary)->handles[position] = receiving;
                        return receiving;
                    }
        return receiving;
    }

    int RenewReceiving(int receiving) {
        GirInst renew;
        renew.op = GirOp::DestRenew;
        renew.a = receiving;
        auto destination = EmitDef(std::move(renew));
        rawReceivings[destination] = receiving;
        if (auto ticket = receivingReservations.find(receiving); ticket != receivingReservations.end())
            rawReservations[destination] = ticket->second;
        return destination;
    }

    int RefreshDestination(int destination) {
        auto found = rawReceivings.find(destination);
        if (found == rawReceivings.end()) throw CompileError { "raw writer has no receiving lease" };
        GirInst refresh;
        refresh.op = GirOp::DestRefresh;
        refresh.a = found->second;
        refresh.b = destination;
        auto current = EmitDef(std::move(refresh));
        rawReceivings[current] = found->second;
        if (auto ticket = rawReservations.find(destination); ticket != rawReservations.end())
            rawReservations[current] = ticket->second;
        return current;
    }

    int WaitExit(int receiving) {
        GirInst wait;
        wait.op = GirOp::ExitWait;
        wait.a = receiving;
        auto ticket = EmitDef(std::move(wait));
        exitReservations.push_back(ticket);
        reservationReceivings[ticket] = receiving;
        waitingExits.insert(ticket);
        return ticket;
    }

    void SelectExit(int ticket, GirExitSource source, int org) {
        GirInst select;
        select.op = GirOp::ExitSelect;
        select.a = ticket;
        select.exitSource = source;
        select.org = org;
        EmitEffect(std::move(select));
        waitingExits.erase(ticket);
    }

    int ReserveExit(int receiving, GirExitSource source, int org) {
        GirInst reserve;
        reserve.op = GirOp::ExitReserve;
        reserve.a = receiving;
        reserve.exitSource = source;
        reserve.org = org;
        auto ticket = EmitDef(std::move(reserve));
        exitReservations.push_back(ticket);
        reservationReceivings[ticket] = receiving;
        return ticket;
    }

    int AdoptExit(int receiving, int completed) {
        GirInst adopt;
        adopt.op = GirOp::ExitAdopt;
        adopt.a = receiving;
        adopt.b = completed;
        auto ticket = EmitDef(std::move(adopt));
        exitReservations.push_back(ticket);
        reservationReceivings[ticket] = receiving;
        return ticket;
    }

    int ExtractExit(int ticket, GirExitSource source, int org) {
        GirInst selected;
        selected.op = GirNamedExitBinding(source).has_value() ? GirOp::ReservedNamed : GirOp::ReservedDest;
        selected.a = ticket;
        if (selected.op == GirOp::ReservedNamed) selected.org = org;
        auto raw = EmitDef(std::move(selected));
        rawReservations[raw] = ticket;
        return raw;
    }

    int LandExit(int ticket, int completed, int org) {
        GirInst land;
        land.op = GirOp::ExitLand;
        land.a = ticket;
        land.b = completed;
        land.org = org;
        return EmitDef(std::move(land));
    }

    void MarkNamedExit(int ticket, int org) {
        GirInst mark;
        mark.op = GirOp::ExitMarkNamed;
        mark.a = ticket;
        mark.org = org;
        EmitEffect(std::move(mark));
    }

    void ReleaseExit(int ticket, int org) {
        GirInst release;
        release.op = GirOp::ExitRelease;
        release.a = ticket;
        release.org = org;
        EmitEffect(std::move(release));
    }

    void DiscardExits(size_t first, const vector<int> &carried, int org) {
        for (size_t position = exitReservations.size(); position > first; position--) {
            GirInst discard;
            discard.op = GirOp::ExitDiscard;
            discard.a = exitReservations[position - 1];
            discard.vals = carried;
            discard.org = org;
            EmitEffect(std::move(discard));
        }
    }

    int CancelReceiving(int receiving, const vector<int> &carried, int org) {
        GirInst cancel;
        cancel.op = GirOp::ReceivingCancel;
        cancel.a = receiving;
        cancel.vals = carried;
        cancel.org = org;
        auto certificate = EmitDef(std::move(cancel));
        auto parent = receivingParents.find(receiving);
        for (auto value : carried) {
            auto raw = rawReceivings.find(value);
            if (raw != rawReceivings.end() && ReceivingWithin(raw->second, receiving))
                raw->second = parent == receivingParents.end() ? -1 : parent->second;
        }
        return certificate;
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

    vector<int> CancelNormalReceivings(const vector<int> &carried, int org) {
        vector<int> cancellations;
        for (auto receiving : resultReceivings)
            if (receiving >= 0) cancellations.push_back(CancelReceiving(receiving, carried, org));
        boundNamedSlots.clear();
        return cancellations;
    }

    void FinishTargetReturn(int target, vector<int> values, map<int, int> incomingCancelled, int org,
                            vector<int> tickets = {}, size_t first = 0) {
        if (tickets.empty()) {
            first = exitReservations.size();
            tickets.assign(values.size(), -1);
            if (HandlesTarget(target))
                for (size_t result = 0; result < values.size(); result++)
                    if (GirNonfixed(mod, (*currentResults)[result].type))
                        tickets[result] = AdoptExit(resultReceivings[result], values[result]);
        }
        auto carried = RawCompletions(values);
        for (auto &[original, cancelled] : incomingCancelled) {
            (void)original;
            CancelDestination(cancelled, org);
            auto receiving = rawReceivings.find(original);
            if (receiving != rawReceivings.end() && delegatedReceivings.erase(receiving->second)) {
                GirInst drop;
                drop.op = GirOp::ReceivingDrop;
                drop.a = receiving->second;
                EmitEffect(std::move(drop));
            }
        }
        for (auto receiver : delegatedReceivings) {
            GirInst drop;
            drop.op = GirOp::ReceivingDrop;
            drop.a = receiver;
            EmitEffect(std::move(drop));
        }
        delegatedReceivings.clear();
        CancelActiveReceivings(org, carried);
        DiscardEnclosingExits(first, carried, org);
        auto cancellations = CancelNormalReceivings(carried, org);
        if (HandlesTarget(target)) {
            for (auto cancelled : cancellations) CancelDestination(cancelled, org);
            for (size_t result = 0; result < values.size(); result++)
                if (tickets[result] >= 0) values[result] = LandExit(tickets[result], values[result], org);
        } else {
            for (size_t result = 0; result < tickets.size(); result++)
                if (tickets[result] >= 0)
                    DropCompletedReceiving(values[result], reservationReceivings.at(tickets[result]));
        }
        for (auto ticket = tickets.rbegin(); ticket != tickets.rend(); ++ticket)
            if (*ticket >= 0) ReleaseExit(*ticket, org);
        if (!HandlesTarget(target))
            for (auto ticket : tickets)
                if (ticket >= 0) {
                    GirInst drop;
                    drop.op = GirOp::ReceivingDrop;
                    drop.a = reservationReceivings.at(ticket);
                    EmitEffect(std::move(drop));
                }
        exitReservations.resize(first);
        LeaveTo(0);
        GirInst term;
        term.op = HandlesTarget(target) ? GirOp::Ret : GirOp::Escape;
        term.idx = target;
        term.vals = std::move(values);
        if (term.op == GirOp::Escape) term.vals2 = std::move(cancellations);
        term.org = org;
        EmitTerm(std::move(term));
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
        auto savedActive = activeReceivings;
        auto savedNamed = boundNamedSlots;
        auto savedReservations = exitReservations;
        auto savedWaiting = waitingExits;
        auto savedDelegated = delegatedReceivings;
        for (size_t edge = 0; edge < edges.size(); edge++) {
            stack = savedScopes;
            activeReceivings = savedActive;
            boundNamedSlots = savedNamed;
            exitReservations = savedReservations;
            waitingExits = savedWaiting;
            delegatedReceivings = savedDelegated;
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
        activeReceivings = std::move(savedActive);
        boundNamedSlots = std::move(savedNamed);
        exitReservations = std::move(savedReservations);
        waitingExits = std::move(savedWaiting);
        delegatedReceivings = std::move(savedDelegated);
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

    void LowerExitOperands(const vector<const CoreExpr *> &operands, const vector<int> &tickets,
                           const vector<int> &receivings, const vector<GirExitSource> &sources,
                           size_t position, vector<int> values,
                           const function<void(vector<int>)> &finish, int org) {
        if (cur < 0) return;
        if (position == operands.size()) {
            for (size_t result = 0; result < values.size(); result++)
                if (values[result] < 0) {
                    values[result] = ExtractExit(tickets[result], sources[result], org);
                    boundNamedSlots.erase(*GirNamedExitBinding(sources[result]));
                }
            finish(std::move(values));
            return;
        }
        auto advance = [&](int value) {
            auto next = values;
            next.push_back(value);
            LowerExitOperands(operands, tickets, receivings, sources, position + 1, std::move(next), finish, org);
        };
        if (tickets[position] < 0) {
            auto value = LowerExpr(*operands[position]);
            if (cur >= 0) advance(value);
            return;
        }
        auto fresh = [&] {
            auto selected = ExtractExit(tickets[position], GirExitNewValue {}, org);
            rawReceivings[selected] = receivings[position];
            auto completed = LowerConstruct(*operands[position], selected, org);
            if (cur >= 0) advance(completed);
        };
        if (!GirNamedExitBinding(sources[position])) { fresh(); return; }
        GirInst role;
        role.op = GirOp::ExitIsNamed;
        role.a = tickets[position];
        auto named = EmitDef(std::move(role));
        auto [namedBlock, namedParams] = NewBlock({});
        auto [freshBlock, freshParams] = NewBlock({});
        (void)namedParams; (void)freshParams;
        EmitTerm(CondBr(named, namedBlock, {}, freshBlock, {}));
        auto saved = make_tuple(stack, activeReceivings, exitReservations, boundNamedSlots, rawReceivings,
                                rawReservations, receivingParents, reservationReceivings, reservationBuilders,
                                receivingReservations);
        cur = namedBlock;
        MarkNamedExit(tickets[position], Org(operands[position]->org));
        advance(-1);
        tie(stack, activeReceivings, exitReservations, boundNamedSlots, rawReceivings,
            rawReservations, receivingParents, reservationReceivings, reservationBuilders,
            receivingReservations) = saved;
        cur = freshBlock;
        fresh();
    }

    void LowerTargetReturn(const CoreStmt &statement, int org) {
        auto savedReservations = exitReservations;
        auto savedActive = activeReceivings;
        auto savedNamed = boundNamedSlots;
        auto &target = core.impls[core.targets.at(statement.target).members[0]];
        auto first = exitReservations.size();
        vector<int> tickets(target.results.size(), -1);
        vector<int> receiving(target.results.size(), -1);
        vector<int> destinations(target.results.size(), -1);
        vector<const CoreExpr *> operands;
        for (auto &value : statement.values) operands.push_back(value.get());
        if (operands.empty() && statement.expr && statement.kind != CoreStmtKind::ReturnFromForward)
            operands.push_back(statement.expr.get());
        if (statement.kind != CoreStmtKind::ReturnFromForward && operands.size() != target.results.size())
            throw CompileError { "target return operands differ from its descriptors" };
        vector<GirExitSource> sources(target.results.size(), GirExitNewValue {});
        for (size_t result = 0; result < target.results.size(); result++) {
            auto &descriptor = target.results[result];
            if (!GirNonfixed(mod, descriptor.type)) continue;
            if (HandlesTarget(statement.target)) receiving[result] = resultReceivings[result];
            else {
                GirInst channel;
                channel.op = GirOp::TargetReceiving;
                channel.idx = statement.target;
                channel.idx2 = (int)result;
                channel.org = org;
                receiving[result] = EmitDef(std::move(channel));
                receivingParents[receiving[result]] = -1;
            }
            if (!operands.empty() && operands[result]->kind == CoreExprKind::ResultLocal &&
                boundNamedSlots.count(operands[result]->var)) sources[result] = GirExitNamedAlias { operands[result]->var };
            tickets[result] = ReserveExit(receiving[result], sources[result], org);
        }
        vector<int> values;
        if (statement.kind == CoreStmtKind::ReturnFromForward) {
            for (size_t result = 0; result < tickets.size(); result++)
                if (tickets[result] >= 0) {
                    destinations[result] = ExtractExit(tickets[result], sources[result], org);
                    rawReceivings[destinations[result]] = receiving[result];
                }
            values = LowerProducer(*statement.expr, destinations, org);
        } else {
            LowerExitOperands(operands, tickets, receiving, sources, 0, {}, [&](vector<int> completed) {
                FinishTargetReturn(statement.target, std::move(completed), {}, org, tickets, first);
            }, org);
        }
        if (statement.kind == CoreStmtKind::ReturnFromForward && cur >= 0)
            FinishTargetReturn(statement.target, std::move(values), {}, org, tickets, first);
        exitReservations = std::move(savedReservations);
        activeReceivings = std::move(savedActive);
        boundNamedSlots = std::move(savedNamed);
    }

    vector<int> LowerProducer(const CoreExpr &expression, const vector<int> &destinations, int org) {
        vector<int> receiving(destinations.size(), -1);
        vector<int> writers = destinations;
        auto savedActive = activeReceivings;
        for (size_t position = 0; position < destinations.size(); position++)
            if (destinations[position] >= 0) {
                receiving[position] = OpenReceiving(destinations[position]);
                if (expression.kind == CoreExprKind::Call) delegatedReceivings.insert(receiving[position]);
                else {
                    writers[position] = RenewReceiving(receiving[position]);
                    activeReceivings.push_back(receiving[position]);
                }
            }
        auto values = LowerProducerValues(expression, writers, receiving, org);
        for (size_t position = 0; cur >= 0 && position < values.size(); position++)
            if (receiving[position] >= 0) {
                DropCompletedReceiving(values[position], receiving[position]);
                rawReceivings[values[position]] = receiving[position];
            }
        activeReceivings = std::move(savedActive);
        return values;
    }

    vector<int> LowerProducerValues(const CoreExpr &expression, const vector<int> &destinations, const vector<int> &receiving, int org) {
        vector<int> values;
        if (expression.kind == CoreExprKind::Values) {
            if (expression.values.size() != destinations.size()) throw CompileError { "producer result count differs from its receiving channels" };
            for (size_t position = 0; position < destinations.size(); position++) {
                auto &operand = *expression.values[position];
                values.push_back(destinations[position] >= 0 ? LowerConstruct(operand, destinations[position], org) : LowerExpr(operand));
                if (cur < 0) return {};
            }
            return values;
        }
        if (expression.kind != CoreExprKind::Call) throw CompileError { "multiple-result producer is not values or a call" };
        auto context = expression.ctx;
        auto callee = core.contexts[context].impl;
        auto &function = core.impls[callee];
        if (function.results.size() != destinations.size()) throw CompileError { "call result count differs from its receiving channels" };
        auto arguments = LowerArgs(expression.args, context, org);
        if (cur < 0) return {};
        auto writers = destinations;
        for (size_t position = 0; position < writers.size(); position++)
            if (writers[position] >= 0) writers[position] = RenewReceiving(receiving[position]);
        if (!function.summary.escapes.empty())
            return InvokeValues(context, std::move(arguments), writers, org);
        GirInst call;
        call.op = GirOp::Call;
        call.idx = context;
        vector<bool> adapted(destinations.size(), false);
        for (size_t position = 0; position < destinations.size(); position++) {
            if (!GirNonfixed(mod, function.results[position].type)) continue;
            if (destinations[position] < 0) throw CompileError { "nonfixed call result has no receiving destination" };
            call.op = GirOp::CallConstruct;
            auto producer = AdaptProducerDestination(writers[position], function.results[position], org);
            adapted[position] = producer.second;
            call.vals2.push_back(producer.first);
        }
        call.vals = std::move(arguments);
        call.org = org;
        if (!function.summary.escapes.empty() || function.summary.unknown)
            throw CompileError { "escaping call requires invoke receiving edges" };
        auto pack = EmitDef(std::move(call));
        if (destinations.size() == 1) return { RestoreProducerDestination(pack, adapted[0], org) };
        for (size_t position = 0; position < destinations.size(); position++) {
            GirInst result;
            result.op = GirOp::Result;
            result.a = pack;
            result.idx = (int)position;
            values.push_back(RestoreProducerDestination(EmitDef(std::move(result)), adapted[position], org));
        }
        return values;
    }

    void LowerConstructionValue(const CoreExpr &expression, GirDestReceiver receiver, int org) {
        auto destination = OpenDestination(expression, std::move(receiver), CoreRequest::Value, org);
        auto completed = LowerConstruct(expression, destination, org);
        if (cur >= 0) PublishDestination(completed, org);
    }

    vector<int> RawCompletions(const vector<int> &values) {
        vector<int> carried;
        for (auto value : values)
            if (mod.Type(ValTy(value)).kind == CoreType::Built) carried.push_back(value);
        return carried;
    }

    bool ReceivingWithin(int receiving, int ancestor) const {
        for (auto current = receiving; current >= 0;) {
            if (current == ancestor) return true;
            auto parent = receivingParents.find(current);
            if (parent == receivingParents.end()) return false;
            current = parent->second;
        }
        return false;
    }

    set<int> CancelReceivingRoots(const vector<int> &receivings, const vector<int> &protectedBoundaries,
                                  const vector<int> &carried, int org) {
        set<int> cancelled;
        for (auto selected = receivings.rbegin(); selected != receivings.rend(); ++selected) {
            auto receiving = *selected;
            if (receiving < 0 || cancelled.count(receiving)) continue;
            auto protectedReceiver = any_of(protectedBoundaries.begin(), protectedBoundaries.end(), [&](int boundary) {
                return boundary >= 0 && ReceivingWithin(receiving, boundary);
            });
            auto nested = any_of(receivings.begin(), receivings.end(), [&](int owner) {
                return owner >= 0 && owner != receiving && ReceivingWithin(receiving, owner);
            });
            if (!protectedReceiver && !nested) {
                CancelDestination(CancelReceiving(receiving, carried, org), org);
                cancelled.insert(receiving);
            }
        }
        activeReceivings.erase(remove_if(activeReceivings.begin(), activeReceivings.end(), [&](int receiving) {
            return any_of(cancelled.begin(), cancelled.end(), [&](int ancestor) { return ReceivingWithin(receiving, ancestor); });
        }), activeReceivings.end());
        return cancelled;
    }

    void CancelActiveReceivings(int org, const vector<int> &carried = {}) {
        vector<int> protectedBoundaries;
        for (auto receiver : resultReceivings)
            if (receiver >= 0 && none_of(waitingExits.begin(), waitingExits.end(), [&](int ticket) {
                    return reservationReceivings.at(ticket) == receiver;
                })) protectedBoundaries.push_back(receiver);
        CancelReceivingRoots(activeReceivings, protectedBoundaries, carried, org);
        activeReceivings.clear();
    }

    void DiscardEnclosingExits(size_t end, const vector<int> &carried, int org) {
        for (size_t position = end; position > 0; position--) {
            GirInst discard;
            discard.op = GirOp::ExitDiscard;
            discard.a = exitReservations[position - 1];
            discard.vals = carried;
            discard.org = org;
            EmitEffect(std::move(discard));
        }
    }

    void FinishFunctionReturn(vector<int> values, const vector<int> &tickets, size_t first, int org) {
        auto carried = RawCompletions(values);
        CancelActiveReceivings(org, carried);
        DiscardEnclosingExits(first, carried, org);
        for (auto cancelled : CancelNormalReceivings(carried, org)) CancelDestination(cancelled, org);
        for (size_t result = 0; result < tickets.size(); result++)
            if (tickets[result] >= 0) values[result] = LandExit(tickets[result], values[result], org);
        for (auto ticket = tickets.rbegin(); ticket != tickets.rend(); ++ticket)
            if (*ticket >= 0) ReleaseExit(*ticket, org);
        exitReservations.resize(first);
        LeaveTo(0);
        GirInst ret;
        ret.op = GirOp::Ret;
        ret.vals = std::move(values);
        ret.org = org;
        EmitTerm(std::move(ret));
    }

    using Completion = function<void(vector<int>, vector<GirExitSource>)>;

    CompletionBranch SaveCompletionBranch() {
        CompletionBranch saved { stack, activeReceivings, exitReservations,
            boundNamedSlots, waitingExits, delegatedReceivings, rawReceivings, rawReservations,
            receivingParents, reservationReceivings, reservationBuilders, receivingReservations, {} };
        for (auto boundary : completionBoundaries) {
            saved.handles.push_back(boundary->handles);
        }
        return saved;
    }

    void RestoreCompletionBranch(const CompletionBranch &saved) {
        stack = saved.scopes;
        activeReceivings = saved.active;
        exitReservations = saved.reservations;
        boundNamedSlots = saved.named;
        waitingExits = saved.waiting;
        delegatedReceivings = saved.delegated;
        rawReceivings = saved.rawReceiving;
        rawReservations = saved.rawReservation;
        receivingParents = saved.parents;
        reservationReceivings = saved.reservationReceiving;
        reservationBuilders = saved.builders;
        receivingReservations = saved.receivingReservation;
        for (size_t position = 0; position < saved.handles.size(); position++) {
            completionBoundaries[position]->handles = saved.handles[position];
        }
    }

    void LowerCompletionBlock(const CoreBlock &block, const vector<int> &positions, const vector<int> &tickets,
                              vector<int> values, vector<GirExitSource> sources, const Completion &finish) {
        auto depth = stack.size();
        EmitEffect([&] { GirInst enter; enter.op = GirOp::Enter; enter.idx = block.scope; return enter; }());
        stack.push_back(block.scope);
        for (auto &statement : block.stmts) {
            if (cur < 0) break;
            LowerStmt(lexicalLoop, statement);
        }
        if (cur >= 0 && block.value)
            LowerCompletionExpression(*block.value, positions, tickets, std::move(values), std::move(sources),
                [&](vector<int> completed, vector<GirExitSource> selectedSources) {
                    LeaveTo(depth);
                    auto saved = stack;
                    stack.resize(depth);
                    finish(std::move(completed), std::move(selectedSources));
                    stack = std::move(saved);
                });
        stack.resize(depth);
    }

    void LowerCompletionExpression(const CoreExpr &expression, const vector<int> &positions, const vector<int> &tickets,
                                   vector<int> values, vector<GirExitSource> sources, const Completion &finish) {
        if (cur < 0) return;
        auto org = CompletionOrigin(expression);
        if (expression.kind == CoreExprKind::Values) {
            if (positions.size() != expression.values.size()) throw CompileError { "implicit result tuple has another arity" };
            function<void(size_t, vector<int>, vector<GirExitSource>)> next;
            next = [&](size_t position, vector<int> completed, vector<GirExitSource> selectedSources) {
                if (position == positions.size()) { finish(std::move(completed), std::move(selectedSources)); return; }
                LowerCompletionExpression(*expression.values[position], { positions[position] }, tickets,
                    std::move(completed), std::move(selectedSources), [&](vector<int> after, vector<GirExitSource> afterSources) {
                        next(position + 1, std::move(after), std::move(afterSources));
                    });
            };
            next(0, std::move(values), std::move(sources));
            return;
        }
        if (expression.kind == CoreExprKind::If) {
            auto condition = LowerExpr(*expression.a);
            if (cur < 0) return;
            auto [yes, yesParams] = NewBlock({});
            auto [no, noParams] = NewBlock({});
            (void)yesParams; (void)noParams;
            EmitTerm(CondBr(condition, yes, {}, no, {}));
            auto saved = SaveCompletionBranch();
            cur = yes;
            LowerCompletionBlock(*expression.then, positions, tickets, values, sources, finish);
            RestoreCompletionBranch(saved);
            cur = no;
            LowerCompletionBlock(*expression.otherwise, positions, tickets, std::move(values), std::move(sources), finish);
            return;
        }
        if (expression.kind == CoreExprKind::Block) {
            CompletionBoundary completion { tickets, vector<int>(tickets.size(), -1) };
            completionBoundaries.push_back(&completion);
            auto previous = valueBoundary;
            ValueBoundary boundary;
            boundary.depth = (int)stack.size();
            boundary.exitDepth = exitReservations.size();
            boundary.constructionDepth = activeReceivings.size();
            auto complete = [&](vector<int> completed, vector<GirExitSource> selectedSources) {
                auto carried = RawCompletions([&] { vector<int> raw; for (auto value : completed) if (value >= 0) raw.push_back(value); return raw; }());
                vector<int> active(activeReceivings.begin() + min(boundary.constructionDepth, activeReceivings.size()), activeReceivings.end());
                CancelReceivingRoots(active, completion.handles, carried, org);
                for (auto receiver : completion.handles) if (receiver >= 0)
                    CancelDestination(CancelReceiving(receiver, carried, org), org);
                LeaveTo(boundary.depth);
                auto savedStack = stack;
                stack.resize(boundary.depth);
                valueBoundary = previous;
                completionBoundaries.pop_back();
                finish(std::move(completed), std::move(selectedSources));
                completionBoundaries.push_back(&completion);
                valueBoundary = &boundary;
                stack = std::move(savedStack);
            };
            boundary.complete = [&](const CoreExpr &operand, int breakOrigin) {
                auto saved = SaveCompletionBranch();
                auto breakTickets = tickets;
                auto breakSources = sources;
                auto first = exitReservations.size();
                for (size_t index = 0; index < positions.size(); index++) {
                    auto position = positions[index];
                    if (tickets[position] < 0 || waitingExits.count(tickets[position])) continue;
                    auto receiver = completion.handles[position];
                    if (receiver < 0) throw CompileError { "completed block channel lost its selected receiving view" };
                    GirExitSource source = GirExitNewValue {};
                    const CoreExpr *sourceExpression = &operand;
                    if (operand.kind == CoreExprKind::Values) sourceExpression = operand.values[index].get();
                    if (sourceExpression->kind == CoreExprKind::ResultLocal && boundNamedSlots.count(sourceExpression->var))
                        source = GirExitNamedAlias { sourceExpression->var };
                    breakSources[position] = source;
                    breakTickets[position] = ReserveExit(receiver, source, breakOrigin);
                }
                LowerCompletionExpression(operand, positions, breakTickets, values, breakSources,
                    [&](vector<int> completed, vector<GirExitSource> selectedSources) {
                        for (auto position : positions)
                            if (breakTickets[position] != tickets[position] && completed[position] < 0)
                                completed[position] = ExtractExit(breakTickets[position], selectedSources[position], breakOrigin);
                        auto carried = RawCompletions([&] { vector<int> raw; for (auto value : completed) if (value >= 0) raw.push_back(value); return raw; }());
                        vector<int> active(activeReceivings.begin() + min(boundary.constructionDepth, activeReceivings.size()), activeReceivings.end());
                        CancelReceivingRoots(active, completion.handles, carried, breakOrigin);
                        for (auto position : positions) if (breakTickets[position] != tickets[position]) {
                            auto closed = completion.handles[position];
                            CancelDestination(CancelReceiving(closed, carried, breakOrigin), breakOrigin);
                            activeReceivings.erase(remove_if(activeReceivings.begin(), activeReceivings.end(), [&](int receiver) {
                                return ReceivingWithin(receiver, closed);
                            }), activeReceivings.end());
                            completion.handles[position] = -1;
                            completed[position] = LandExit(breakTickets[position], completed[position], breakOrigin);
                            ReleaseExit(breakTickets[position], breakOrigin);
                        }
                        exitReservations.resize(first);
                        complete(std::move(completed), std::move(selectedSources));
                    });
                RestoreCompletionBranch(saved);
            };
            valueBoundary = &boundary;
            LowerCompletionBlock(*expression.then, positions, tickets, values, sources, complete);
            valueBoundary = previous;
            completionBoundaries.pop_back();
            return;
        }
        if (expression.kind == CoreExprKind::Call) {
            vector<int> destinations(positions.size(), -1);
            for (size_t index = 0; index < positions.size(); index++) {
                auto position = positions[index];
                if (tickets[position] < 0) continue;
                if (waitingExits.count(tickets[position])) SelectExit(tickets[position], GirExitNewValue {}, org);
                destinations[index] = ExtractExit(tickets[position], GirExitNewValue {}, org);
                rawReceivings[destinations[index]] = reservationReceivings.at(tickets[position]);
            }
            auto completed = LowerProducer(expression, destinations, org);
            if (cur >= 0) {
                for (size_t index = 0; index < positions.size(); index++) values[positions[index]] = completed[index];
                finish(std::move(values), std::move(sources));
            }
            return;
        }
        if (positions.size() != 1) throw CompileError { "implicit leaf result count differs from its channels" };
        auto position = positions[0];
        if (tickets[position] < 0) {
            values[position] = LowerExpr(expression);
            if (cur >= 0) finish(std::move(values), std::move(sources));
            return;
        }
        auto source = sources[position];
        if (waitingExits.count(tickets[position])) {
            source = expression.kind == CoreExprKind::ResultLocal && boundNamedSlots.count(expression.var)
                ? GirExitSource { GirExitNamedAlias { expression.var } } : GirExitSource { GirExitNewValue {} };
            SelectExit(tickets[position], source, org);
        }
        sources[position] = source;
        auto fresh = [&] {
            auto destination = ExtractExit(tickets[position], GirExitNewValue {}, org);
            rawReceivings[destination] = reservationReceivings.at(tickets[position]);
            values[position] = LowerConstruct(expression, destination, org);
            if (cur >= 0) finish(values, sources);
        };
        if (!GirNamedExitBinding(source)) { fresh(); return; }
        GirInst role; role.op = GirOp::ExitIsNamed; role.a = tickets[position];
        auto named = EmitDef(std::move(role));
        auto [yes, yesParams] = NewBlock({});
        auto [no, noParams] = NewBlock({});
        (void)yesParams; (void)noParams;
        EmitTerm(CondBr(named, yes, {}, no, {}));
        auto saved = SaveCompletionBranch();
        cur = yes;
        MarkNamedExit(tickets[position], org);
        values[position] = -1;
        finish(values, sources);
        RestoreCompletionBranch(saved);
        cur = no;
        fresh();
    }

    void LowerImplicitReturn(const CoreExpr &expression) {
        auto saved = SaveCompletionBranch();
        auto first = exitReservations.size();
        vector<int> tickets(currentResults->size(), -1), positions;
        for (size_t position = 0; position < currentResults->size(); position++) {
            positions.push_back((int)position);
            if (resultReceivings[position] >= 0) tickets[position] = WaitExit(resultReceivings[position]);
        }
        auto org = CompletionOrigin(expression);
        LowerCompletionExpression(expression, positions, tickets, vector<int>(tickets.size(), -2),
            vector<GirExitSource>(tickets.size(), GirExitNewValue {}),
            [&](vector<int> values, vector<GirExitSource> sources) {
                for (size_t position = 0; position < values.size(); position++) if (values[position] < 0) {
                    values[position] = ExtractExit(tickets[position], sources[position], org);
                    boundNamedSlots.erase(*GirNamedExitBinding(sources[position]));
                }
                FinishFunctionReturn(std::move(values), tickets, first, org);
            });
        RestoreCompletionBranch(saved);
    }

    void LowerFunctionReturn(const vector<const CoreExpr *> &operands, int org) {
        auto savedActive = activeReceivings;
        auto savedReservations = exitReservations;
        auto savedNamed = boundNamedSlots;
        LowerReturnOperands(operands, org);
        activeReceivings = std::move(savedActive);
        exitReservations = std::move(savedReservations);
        boundNamedSlots = std::move(savedNamed);
    }

    void LowerReturnOperands(const vector<const CoreExpr *> &operands, int org) {
        if (!currentResults || operands.size() != currentResults->size())
            throw CompileError { "return operands do not match the current function result descriptors" };
        auto first = exitReservations.size();
        vector<int> tickets(operands.size(), -1);
        vector<GirExitSource> sources(operands.size(), GirExitNewValue {});
        for (size_t result = 0; result < operands.size(); result++) {
            auto &descriptor = (*currentResults)[result];
            if (!GirNonfixed(mod, descriptor.type)) continue;
            auto &expression = *operands[result];
            if (expression.kind == CoreExprKind::ResultLocal && boundNamedSlots.count(expression.var))
                sources[result] = GirExitNamedAlias { expression.var };
            tickets[result] = ReserveExit(resultReceivings[result], sources[result], org);
        }
        LowerExitOperands(operands, tickets, resultReceivings, sources, 0, {}, [&](vector<int> completed) {
            FinishFunctionReturn(std::move(completed), tickets, first, org);
        }, org);
    }

    void CancelInterruptedReturn(const Loop &loop, int org) {
        vector<int> active(activeReceivings.begin() + loop.constructionDepth, activeReceivings.end());
        auto cancelled = CancelReceivingRoots(active, {}, {}, org);
        DiscardExits(loop.exitDepth, {}, org);
        vector<int> unfinished;
        for (size_t position = loop.exitDepth; position < exitReservations.size(); position++)
            if (auto selected = reservationBuilders.find(exitReservations[position]); selected != reservationBuilders.end()) {
                auto receiving = selected->second;
                auto closed = any_of(cancelled.begin(), cancelled.end(), [&](int ancestor) {
                    return ReceivingWithin(receiving, ancestor);
                });
                if (!closed) unfinished.push_back(receiving);
            }
        CancelReceivingRoots(unfinished, {}, {}, org);
    }

    void LowerStmt(const Loop *lc, const CoreStmt &s) {
        auto org = Org(s.org);
        switch (s.kind) {
            case CoreStmtKind::Let: {
                if (CoreHasConstruction(core.profile) && GirNonfixed(mod, slots.at(s.var).ty)) {
                    if (currentResults)
                        for (size_t result = 0; result < currentResults->size(); result++)
                            if ((*currentResults)[result].namedLocal == s.var) {
                                auto completed = LowerConstruct(*s.expr, RenewReceiving(resultReceivings[result]), org);
                                if (cur < 0) return;
                                DropCompletedReceiving(completed);
                                GirInst bind;
                                bind.op = GirOp::DestBind;
                                bind.idx = s.var;
                                bind.a = completed;
                                bind.org = org;
                                EmitEffect(std::move(bind));
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
                    auto saved = SaveCompletionBranch();
                    cur = tb;
                    LowerBlock(lc, {}, false, *s.then);
                    EmitTerm(Br(jb, {}));
                    RestoreCompletionBranch(saved);
                    cur = jb;
                } else {
                    auto [tb, ts] = NewBlock({});
                    auto [eb, es] = NewBlock({});
                    (void)ts; (void)es;
                    EmitTerm(CondBr(cv, tb, {}, eb, {}));
                    auto saved = SaveCompletionBranch();
                    cur = tb;
                    LowerBlock(lc, {}, false, *s.then);
                    auto endT = cur;
                    RestoreCompletionBranch(saved);
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
                Loop l { depth, xb, false, hb, -1, -1, exitReservations.size(), activeReceivings.size() };
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
                Loop l { depth, xb, true, hb, t, i, exitReservations.size(), activeReceivings.size() };
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
                    CancelInterruptedReturn(*lc, org);
                    LeaveTo(lc->depth);
                    EmitTerm(Br(lc->breakto, {}));
                }
                return;
            case CoreStmtKind::Continue:
                if (lc) {
                    CancelInterruptedReturn(*lc, org);
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
                if (s.expr->kind == CoreExprKind::Values) {
                    vector<const CoreExpr *> operands;
                    for (auto &value : s.expr->values) operands.push_back(value.get());
                    LowerFunctionReturn(operands, org);
                    return;
                }
                auto savedActive = activeReceivings;
                auto savedReservations = exitReservations;
                auto savedNamed = boundNamedSlots;
                auto first = exitReservations.size();
                vector<int> tickets(currentResults->size(), -1);
                vector<int> destinations(currentResults->size(), -1);
                for (size_t result = 0; result < currentResults->size(); result++)
                    if (resultReceivings[result] >= 0)
                        tickets[result] = ReserveExit(resultReceivings[result], GirExitNewValue {}, org);
                for (size_t result = 0; result < tickets.size(); result++)
                    if (tickets[result] >= 0) {
                        destinations[result] = ExtractExit(tickets[result], GirExitNewValue {}, org);
                        rawReceivings[destinations[result]] = resultReceivings[result];
                    }
                auto values = LowerProducer(*s.expr, destinations, org);
                if (cur >= 0) FinishFunctionReturn(std::move(values), tickets, first, org);
                activeReceivings = std::move(savedActive);
                exitReservations = std::move(savedReservations);
                boundNamedSlots = std::move(savedNamed);
                return;
            }
            case CoreStmtKind::ReturnFrom: case CoreStmtKind::ReturnFromForward:
                return LowerTargetReturn(s, org);
            case CoreStmtKind::BreakValue: {
                if (!valueBoundary) throw CompileError { "value break has no enclosing value block" };
                auto &boundary = *valueBoundary;
                if (boundary.complete) {
                    boundary.complete(*s.expr, org);
                    return;
                }
                auto savedReservations = exitReservations;
                auto ticket = boundary.receiving < 0 ? -1 : ReserveExit(boundary.receiving, GirExitNewValue {}, org);
                int value;
                if (ticket < 0) value = LowerExpr(*s.expr);
                else {
                    auto destination = ExtractExit(ticket, GirExitNewValue {}, org);
                    rawReceivings[destination] = boundary.receiving;
                    value = LowerConstruct(*s.expr, destination, org);
                }
                if (cur >= 0) {
                    auto carried = RawCompletions({ value });
                    vector<int> active(activeReceivings.begin() + boundary.constructionDepth, activeReceivings.end());
                    CancelReceivingRoots(active, { boundary.receiving }, carried, org);
                    for (size_t position = exitReservations.size(); position > boundary.exitDepth; position--) {
                        auto enclosing = exitReservations[position - 1];
                        if (enclosing == ticket) continue;
                        GirInst discard;
                        discard.op = GirOp::ExitDiscard;
                        discard.a = enclosing;
                        discard.vals = carried;
                        discard.org = org;
                        EmitEffect(std::move(discard));
                    }
                    if (ticket >= 0) {
                        CancelDestination(CancelReceiving(boundary.receiving, carried, org), org);
                        value = LandExit(ticket, value, org);
                        ReleaseExit(ticket, org);
                    }
                    if (boundary.catchBlock < 0) {
                        auto [catchBlock, caught] = NewBlock({ boundary.type });
                        boundary.catchBlock = catchBlock;
                        boundary.catchValue = caught[0];
                    }
                    LeaveTo(boundary.depth);
                    EmitTerm(Br(boundary.catchBlock, { value }));
                }
                exitReservations = std::move(savedReservations);
                return;
            }
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
            ev = vt.kind == CoreType::Ref ? BorrowTo(vt.mut, elem) : elem;
        } else {
            ev = Def(GirOp::Load, elem);
        }
        vector<Binding> pre { { s.var, ev, org } };
        if (s.index >= 0) pre.push_back({ s.index, i, org });
        Loop l { depth, xb, true, hb, I64(), i, exitReservations.size(), activeReceivings.size() };
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
        lexicalLoop = nullptr;
        valueBoundary = nullptr;
        stack.clear();
        slots.clear();
        vars = vs;
        currentResults = nullptr;
        functionBody = nullptr;
        functionOrigin = -1;
        currentImpl = -1;
        currentFunction = -1;
        activeReceivings.clear();
        resultReceivings.clear();
        rawReceivings.clear();
        receivingParents.clear();
        exitReservations.clear();
        reservationReceivings.clear();
        reservationBuilders.clear();
        rawReservations.clear();
        receivingReservations.clear();
        boundNamedSlots.clear();
        waitingExits.clear();
        delegatedReceivings.clear();
        completionBoundaries.clear();
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
        auto ceiling = [&](const vector<CoreRootRef> &source) {
            auto roots = source;
            for (size_t j = 0; j < impl.params.size(); j++) {
                auto var = impl.params[j].var;
                auto parameterRoots = find_if(context.varroots.begin(), context.varroots.end(),
                    [&](auto &entry) { return entry.first == var; });
                if (parameterRoots == context.varroots.end()) continue;
                auto fullyIncluded = all_of(parameterRoots->second.begin(), parameterRoots->second.end(),
                    [&](auto &root) { return find(source.begin(), source.end(), root) != source.end(); });
                CoreRootRef alias { CoreRootRef::Param, (int)j };
                if (fullyIncluded && find(roots.begin(), roots.end(), alias) == roots.end()) roots.push_back(alias);
            }
            return roots;
        };
        for (size_t i = 0; i < out.results.size(); i++)
            out.results[i] = ceiling(i < context.resultroots.size() ? context.resultroots[i] : vector<CoreRootRef> {});
        out.slots.emplace();
        for (auto &row : context.varroots) {
            if (row.first < 0 || row.first >= (int)impl.vars.size()) continue;
            auto type = impl.vars[row.first].type;
            if (!GirRefLike(mod, type)) continue;
            auto &ty = mod.Type(type);
            auto refSlice = ty.kind == CoreType::Ref && mod.Type(ty.elem).kind == CoreType::Slice &&
                row.first < (int)impl.params.size() && impl.params[row.first].var == row.first;
            out.slots->push_back({ row.first, refSlice ? vector<CoreRootRef> { { CoreRootRef::Param, row.first } } : ceiling(row.second) });
        }
        return out;
    }

    GirFunc LowerImpl(const CoreImpl &impl, int implIndex, int contextIndex) {
        Begin(&impl.vars);
        currentResults = &impl.results;
        currentImpl = implIndex;
        currentFunction = contextIndex;
        functionBody = &impl.body;
        functionOrigin = !impl.vars.empty() ? Org(impl.vars[0].org) :
            !impl.body.stmts.empty() ? Org(impl.body.stmts[0].org) : impl.body.value ? CompletionOrigin(*impl.body.value) : -1;
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
        resultReceivings.assign(impl.results.size(), -1);
        size_t channel = ptys.size();
        if (CoreHasConstruction(core.profile))
            for (size_t result = 0; result < impl.results.size(); result++)
                if (GirNonfixed(mod, impl.results[result].type)) {
                    resultReceivings[result] = OpenReceiving(ps[channel++]);
                }
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
        f.org = functionOrigin;
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
