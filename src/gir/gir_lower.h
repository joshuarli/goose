// Goose compiler — lowering a Core module to GIR-H.
//
// Every Core form becomes a fixed sequence of instructions, and every table is
// numbered by the order the lowering creates its entries. The lowering reads
// implementations, never a context's root annotations; a context contributes
// only the implementation a call or the entry names.
//
// Slots, scopes and globals keep the numbers of the Core variables, blocks and
// globals. Blocks and values are numbered as they are created: a block takes
// the next block id and then the next value ids for its parameters, and an
// instruction that defines a value takes the next value id when it is emitted.
// The lowering emits into one current block. A terminator closes it and leaves
// none; while there is none nothing is emitted, no block is created and
// statements are skipped, so there is no unreachable block and no instruction
// after a terminator.
//
// Evaluation order is instruction order. `ifE`/`ifS` branch on the condition
// and create their join after both arms, only if an arm reaches it. A loop's
// source is sampled once; a grow-only array has its length read again in the
// loop header. Every Core block enters its scope, binds the variables its
// construct declares, runs its statements, evaluates its value and leaves its
// scope; `ret` leaves every scope entered, `break` and `continue` those
// entered since the loop began.
#pragma once

namespace goose {

class GirLowerer {
public:
    // `origin` maps a Core origin to its number in the Core module's document.
    GirLowerer(const CoreModule &core, vector<string> files, vector<CoreOrigin> origins,
               function<int(const CoreOrigin &)> origin)
        : core(core), files(std::move(files)), origins(std::move(origins)), originof(std::move(origin)) {}

    GirModule Lower() {
        mod.types = core.types;
        mod.files = files;
        mod.origins = origins;
        for (auto &im : core.impls) {
            pair<vector<GirTypeId>, vector<GirTypeId>> sig;
            for (auto &p : im.params) sig.first.push_back(im.vars[p.var].type);
            sig.second = im.results;
            sigs.push_back(std::move(sig));
        }
        for (auto &g : core.globals) globaltypes.push_back({ g.type, g.kind });
        for (auto &g : core.globals) mod.globals.push_back(LowerGlobal(g));
        for (auto &im : core.impls) mod.funcs.push_back(LowerImpl(im));
        mod.entry = core.contexts[core.entry].impl;
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
        GirTyEnv env { mod, slots, sigs, vals };
        auto r = GirTyper(env).Of(i);
        auto ty = r.ok() ? r.ty : mod.UnitType();
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
                auto vw = LowerView(*e.view);
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
                auto vs = LowerArgs(e.args);
                GirInst i;
                i.op = GirOp::Call;
                i.idx = core.contexts[e.ctx].impl;
                i.vals = std::move(vs);
                i.org = Org(e.org);
                return EmitDef(std::move(i));
            }
            case CoreExprKind::Push: {
                auto r = LowerPlace(*e.place);
                auto v = LowerExpr(*e.a);
                GirInst i;
                i.op = GirOp::Push;
                i.a = r;
                i.b = v;
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
        }
        return 0;
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

    vector<int> LowerArgs(const vector<CoreArg> &args) {
        vector<int> out;
        for (auto &a : args) {
            if (a.kind == CoreArg::Val) out.push_back(LowerExpr(*a.expr));
            else {
                auto r = LowerPlace(*a.place);
                out.push_back(FreezeTo(a.mut, r));
            }
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
        }
        return 0;
    }

    int LowerView(const CoreView &v) {
        if (v.kind == CoreView::Of) {
            auto r = LowerPlace(*v.place);
            return Def(GirOp::Snap, r);
        }
        auto s = LowerExpr(*v.expr);
        return Def(GirOp::SliceView, s);
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
        if (b.value) r = LowerExpr(*b.value);
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

    void LowerStmt(const Loop *lc, const CoreStmt &s) {
        auto org = Org(s.org);
        switch (s.kind) {
            case CoreStmtKind::Let: {
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
                    if (a.text) {
                        p.text = true;
                        p.str = a.str;
                    } else {
                        p.val = LowerExpr(*a.expr);
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
            vw = Def(GirOp::Snap, owner);
        } else {
            auto sl = LowerExpr(*s.view->expr);
            vw = Def(GirOp::SliceView, sl);
        }
        auto regrow = owner >= 0 && IsGrowRef(owner);
        int sampled = regrow ? 0 : Def(GirOp::ViewLen, vw);
        auto startat = ConstInt(I64(), "0");
        if (cur < 0) return;
        auto depth = stack.size();
        auto [hb, hs] = NewBlock({ I64() });
        auto i = hs[0];
        EmitTerm(Br(hb, { startat }));
        cur = hb;
        int n = regrow ? Def(GirOp::ArrayLen, owner) : sampled;
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

    bool IsGrowRef(int r) {
        auto &t = mod.Type(ValTy(r));
        return t.kind == CoreType::Ref && mod.Type(t.elem).kind == CoreType::Grow;
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
            if (a.expr) ExprScopes(parent, *a.expr, out);
            if (a.place) PlaceScopes(parent, *a.place, out);
        }
        for (auto &el : e.elems) ExprScopes(parent, *el, out);
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
        for (auto &a : s.print) if (!a.text) ExprScopes(parent, *a.expr, out);
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
        if (vs)
            for (size_t i = 0; i < vs->size(); i++)
                slots.push_back({ (*vs)[i].type, (*vs)[i].kind, (*vs)[i].scope, (int)i });
    }

    GirFunc LowerImpl(const CoreImpl &impl) {
        Begin(&impl.vars);
        vector<GirTypeId> ptys;
        for (auto &p : impl.params) ptys.push_back(impl.vars[p.var].type);
        auto [b0, ps] = NewBlock(ptys);
        cur = b0;
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
        f.results = impl.results;
        f.slots = slots;
        ScopePairs pairs;
        BlockScopes(-1, impl.body, pairs);
        f.scopes = ScopeTable(pairs);
        f.blocks = std::move(blocks);
        f.summary = impl.summary;
        f.org = impl.vars.empty() ? -1 : Org(impl.vars[0].org);
        return f;
    }

    GirGlobal LowerGlobal(const CoreGlobal &g) {
        Begin(nullptr);
        auto [b0, ps] = NewBlock({});
        (void)ps;
        cur = b0;
        auto v = LowerExpr(*g.init);
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
        out.init.name = g.name;
        out.init.results = { g.type };
        ScopePairs pairs;
        ExprScopes(-1, *g.init, pairs);
        out.init.scopes = ScopeTable(pairs);
        out.init.blocks = std::move(blocks);
        out.init.summary.unknown = true;
        out.init.org = Org(g.org);
        return out;
    }
};

}  // namespace goose
