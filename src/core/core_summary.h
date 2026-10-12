// Goose compiler — Typed Goose Core, effect summaries.
//
// The summary of an implementation is computed from its Core body alone: the
// storage a place or reference denotes is resolved to parameters and globals
// by following, flow-insensitively, what each local reference or slice
// variable was bound to; a call contributes its callee's summary with the
// callee's parameters replaced by what this call passes. Whatever cannot be
// resolved that way makes the summary unknown, which implies every effect.
// Summaries are the least fixed point, so recursion needs no special case.
#pragma once

namespace goose {

class CoreSummarizer {
public:
    explicit CoreSummarizer(CoreModule &module) : m(module) {}

    void Run() {
        pts.resize(m.impls.size());
        for (auto changed = true; changed;) {
            changed = false;
            for (size_t i = 0; i < m.impls.size(); i++) {
                // What a local may point at depends on what the callees do to
                // the variables they are passed, so it is redone each round.
                PointsTo(i);
                auto s = Summarize(i);
                if (!SameSummary(s, m.impls[i].summary)) {
                    m.impls[i].summary = std::move(s);
                    changed = true;
                }
            }
        }
    }

private:
    CoreModule &m;

    // The storage a place, view or reference may denote, as parameters and
    // globals; locals are not targets.
    struct Targets {
        set<CoreTarget> set_;
        bool unknown = false;
        void Add(const Targets &o) {
            set_.insert(o.set_.begin(), o.set_.end());
            unknown |= o.unknown;
        }
    };

    struct Effects {
        Targets reads, writes, grows, rebinds;
        bool aborts = false, outputs = false, unknown = false;
    };

    vector<vector<Targets>> pts;   // Per implementation, per variable.
    size_t ci = 0;                 // The implementation being walked.
    Effects *fx = nullptr;

    CoreImpl &Impl() { return m.impls[ci]; }

    static bool SameSummary(const CoreSummary &a, const CoreSummary &b) {
        return a.unknown == b.unknown && a.reads == b.reads && a.writes == b.writes &&
               a.grows == b.grows && a.rebinds == b.rebinds && a.aborts == b.aborts &&
               a.outputs == b.outputs;
    }

    static Targets Unknown() {
        Targets t;
        t.unknown = true;
        return t;
    }

    // ---------------------------------------------------------------------
    // What each reference or slice variable may point at.

    void PointsTo(size_t i) {
        ci = i;
        auto &impl = Impl();
        auto &p = pts[i];
        p.assign(impl.vars.size(), Targets {});
        for (auto &param : impl.params) {
            if (!m.IsRefOrSlice(impl.vars[param.var].type)) continue;
            p[param.var].set_.insert(CoreTarget { false, param.var });
        }
        // Bindings of locals flow into each other, so repeat until stable.
        for (auto changed = true; changed;) {
            changed = false;
            auto bind = [&](int var, const Targets &t) {
                auto &dst = p[var];
                auto n = dst.set_.size();
                auto u = dst.unknown;
                dst.Add(t);
                if (dst.set_.size() != n || dst.unknown != u) changed = true;
            };
            BindBlock(impl.body, bind);
        }
    }

    template<typename F> void BindBlock(CoreBlock &b, F &bind) {
        for (auto &s : b.stmts) BindStmt(s, bind);
        if (b.value) BindExpr(*b.value, bind);
    }

    template<typename F> void BindStmt(CoreStmt &s, F &bind) {
        switch (s.kind) {
            case CoreStmtKind::Let:
            case CoreStmtKind::Rebind:
                if (m.IsRefOrSlice(Impl().vars[s.var].type)) bind(s.var, Ref(*s.expr));
                break;
            case CoreStmtKind::ForEach:
                if (s.byRef) bind(s.var, ViewT(*s.view));
                break;
            default: break;
        }
        if (s.then) BindBlock(*s.then, bind);
        if (s.otherwise) BindBlock(*s.otherwise, bind);
        // Blocks nested in expressions hold statements too.
        if (s.expr) BindExpr(*s.expr, bind);
        if (s.expr2) BindExpr(*s.expr2, bind);
    }

    template<typename F> void BindExpr(CoreExpr &e, F &bind) {
        if (e.kind == CoreExprKind::Call) {
            // A callee that rebinds a slice variable it was passed leaves it
            // pointing somewhere this implementation cannot name.
            auto &callee = m.impls[m.contexts[e.ctx].impl].summary;
            for (size_t j = 0; j < e.args.size(); j++) {
                auto &a = e.args[j];
                if (a.kind != CoreArg::Ref || a.place->kind != CorePlace::Local) continue;
                auto var = a.place->index;
                if (!m.IsRefOrSlice(Impl().vars[var].type)) continue;
                auto rebound = callee.unknown;
                for (auto &t : callee.rebinds) rebound |= !t.global && t.index == (int)j;
                if (rebound) bind(var, Unknown());
            }
        }
        if (e.then) BindBlock(*e.then, bind);
        if (e.otherwise) BindBlock(*e.otherwise, bind);
        if (e.a) BindExpr(*e.a, bind);
        if (e.b) BindExpr(*e.b, bind);
        for (auto &el : e.elems) BindExpr(*el, bind);
        for (auto &a : e.args) if (a.expr) BindExpr(*a.expr, bind);
    }

    // ---------------------------------------------------------------------
    // Resolving storage.

    Targets PlaceT(const CorePlace &p) {
        switch (p.kind) {
            case CorePlace::Local: return {};
            case CorePlace::Global: {
                Targets t;
                t.set_.insert(CoreTarget { true, p.index });
                return t;
            }
            case CorePlace::Deref: return Ref(*p.expr);
            case CorePlace::Elem: return ViewT(*p.view);
        }
        return Unknown();
    }

    Targets ViewT(const CoreView &v) {
        return v.kind == CoreView::Of ? PlaceT(*v.place) : Ref(*v.expr);
    }

    // Where a reference- or slice-typed expression points.
    Targets Ref(const CoreExpr &e) {
        switch (e.kind) {
            case CoreExprKind::Read:
                if (e.place->kind == CorePlace::Local) return pts[ci][e.place->index];
                return Unknown();
            case CoreExprKind::Ref: return PlaceT(*e.place);
            case CoreExprKind::Push: return PlaceT(*e.place);
            case CoreExprKind::Slice: return ViewT(*e.view);
            case CoreExprKind::Call: {
                Targets t;
                auto &roots = m.contexts[e.ctx].resultroots;
                if (roots.empty()) return t;
                for (auto &r : roots[0]) {
                    if (r.kind == CoreRootRef::Global) t.set_.insert(CoreTarget { true, r.index });
                    else if (r.kind == CoreRootRef::Param) t.Add(ArgT(e.args[r.index]));
                    else return Unknown();
                }
                return t;
            }
            case CoreExprKind::If: {
                Targets t = e.then->value ? Ref(*e.then->value) : Unknown();
                t.Add(e.otherwise->value ? Ref(*e.otherwise->value) : Unknown());
                return t;
            }
            case CoreExprKind::Block:
                return e.then->value ? Ref(*e.then->value) : Unknown();
            default: return Unknown();
        }
    }

    Targets ArgT(const CoreArg &a) {
        if (a.kind == CoreArg::Ref) return PlaceT(*a.place);
        return m.IsRefOrSlice(a.expr->type) ? Ref(*a.expr) : Targets {};
    }

    // ---------------------------------------------------------------------
    // Effects.

    CoreSummary Summarize(size_t i) {
        ci = i;
        Effects e;
        fx = &e;
        Block(Impl().body);
        fx = nullptr;
        CoreSummary s;
        if (e.unknown || e.reads.unknown || e.writes.unknown || e.grows.unknown ||
            e.rebinds.unknown) {
            s.unknown = true;
            return s;
        }
        auto vec = [](const Targets &t) { return vector<CoreTarget>(t.set_.begin(), t.set_.end()); };
        s.reads = vec(e.reads);
        s.writes = vec(e.writes);
        s.grows = vec(e.grows);
        s.rebinds = vec(e.rebinds);
        s.aborts = e.aborts;
        s.outputs = e.outputs;
        return s;
    }

    void Block(const CoreBlock &b) {
        for (auto &s : b.stmts) Stmt(s);
        if (b.value) Ex(*b.value);
    }

    static bool MayAbort(CoreBinOp op) {
        return op == CoreBinOp::Add || op == CoreBinOp::Sub || op == CoreBinOp::Mul ||
               op == CoreBinOp::Div || op == CoreBinOp::Mod;
    }

    void Stmt(const CoreStmt &s) {
        switch (s.kind) {
            case CoreStmtKind::Let: Ex(*s.expr); break;
            case CoreStmtKind::Assign:
                Pl(*s.place);
                Ex(*s.expr);
                // Storing a slice through a reference rebinds the variable it
                // refers to.
                if (m.IsRefOrSlice(s.expr->type)) fx->rebinds.Add(PlaceT(*s.place));
                else fx->writes.Add(PlaceT(*s.place));
                break;
            case CoreStmtKind::AssignOp:
                Pl(*s.place);
                Ex(*s.expr);
                fx->reads.Add(PlaceT(*s.place));
                fx->writes.Add(PlaceT(*s.place));
                if (MayAbort(s.bin)) fx->aborts = true;
                break;
            case CoreStmtKind::Rebind:
                Ex(*s.expr);
                if (s.var < (int)Impl().params.size()) {
                    Targets t;
                    t.set_.insert(CoreTarget { false, s.var });
                    fx->rebinds.Add(t);
                }
                break;
            case CoreStmtKind::Expr: Ex(*s.expr); break;
            case CoreStmtKind::Append:
                Pl(*s.place);
                Vw(*s.view);
                fx->grows.Add(PlaceT(*s.place));
                fx->reads.Add(ViewT(*s.view));
                break;
            case CoreStmtKind::If:
                Ex(*s.expr);
                Block(*s.then);
                if (s.otherwise) Block(*s.otherwise);
                break;
            case CoreStmtKind::While:
                Ex(*s.expr);
                Block(*s.then);
                break;
            case CoreStmtKind::ForRange:
                Ex(*s.expr);
                Ex(*s.expr2);
                Block(*s.then);
                break;
            case CoreStmtKind::ForEach:
                Vw(*s.view);
                fx->reads.Add(ViewT(*s.view));
                Block(*s.then);
                break;
            case CoreStmtKind::Ret:
                if (s.expr) Ex(*s.expr);
                break;
            case CoreStmtKind::Print:
                fx->outputs = true;
                for (auto &a : s.print) if (!a.text) Ex(*a.expr);
                break;
            case CoreStmtKind::Assert:
            case CoreStmtKind::Exit:
                Ex(*s.expr);
                fx->aborts = true;
                break;
            case CoreStmtKind::Abort: fx->aborts = true; break;
            case CoreStmtKind::Break:
            case CoreStmtKind::Continue: break;
        }
    }

    // The sub-expressions of a place; an element access may abort.
    void Pl(const CorePlace &p) {
        switch (p.kind) {
            case CorePlace::Local: case CorePlace::Global: break;
            case CorePlace::Deref: Ex(*p.expr); break;
            case CorePlace::Elem:
                Vw(*p.view);
                Ex(*p.expr);
                fx->aborts = true;
                break;
        }
    }

    void Vw(const CoreView &v) {
        if (v.kind == CoreView::Of) Pl(*v.place);
        else Ex(*v.expr);
    }

    void Ex(const CoreExpr &e) {
        switch (e.kind) {
            case CoreExprKind::Lit: case CoreExprKind::Bool: break;
            case CoreExprKind::Read:
                Pl(*e.place);
                fx->reads.Add(PlaceT(*e.place));
                break;
            case CoreExprKind::Ref: Pl(*e.place); break;
            case CoreExprKind::Slice:
                Vw(*e.view);
                if (e.lo.expr) Ex(*e.lo.expr);
                if (e.hi.expr) Ex(*e.hi.expr);
                fx->reads.Add(ViewT(*e.view));
                fx->aborts = true;
                break;
            case CoreExprKind::Len:
                Vw(*e.view);
                fx->reads.Add(ViewT(*e.view));
                break;
            case CoreExprKind::Un:
                Ex(*e.a);
                if (e.un == CoreUnOp::Neg) fx->aborts = true;
                break;
            case CoreExprKind::Bin:
                Ex(*e.a);
                Ex(*e.b);
                if (MayAbort(e.bin)) fx->aborts = true;
                break;
            case CoreExprKind::Cmp: case CoreExprKind::And: case CoreExprKind::Or:
                Ex(*e.a);
                Ex(*e.b);
                break;
            case CoreExprKind::Not: Ex(*e.a); break;
            case CoreExprKind::Conv:
                Ex(*e.a);
                if (e.conv == CoreConvKind::As) fx->aborts = true;
                break;
            case CoreExprKind::Call: Call(e); break;
            case CoreExprKind::Push:
                Pl(*e.place);
                Ex(*e.a);
                fx->grows.Add(PlaceT(*e.place));
                break;
            case CoreExprKind::If:
                Ex(*e.a);
                Block(*e.then);
                Block(*e.otherwise);
                break;
            case CoreExprKind::Block: Block(*e.then); break;
            case CoreExprKind::Arr:
                for (auto &el : e.elems) Ex(*el);
                break;
            case CoreExprKind::Fill: Ex(*e.a); break;
        }
    }

    void Call(const CoreExpr &e) {
        for (auto &a : e.args) {
            if (a.kind == CoreArg::Val) Ex(*a.expr);
            else Pl(*a.place);
        }
        auto &callee = m.impls[m.contexts[e.ctx].impl].summary;
        if (callee.unknown) { fx->unknown = true; return; }
        // The callee's parameters are what this call passes for them.
        auto map = [&](const vector<CoreTarget> &from, Targets &to) {
            for (auto &t : from) {
                if (t.global) to.set_.insert(t);
                else to.Add(ArgT(e.args[t.index]));
            }
        };
        map(callee.reads, fx->reads);
        map(callee.writes, fx->writes);
        map(callee.grows, fx->grows);
        fx->aborts |= callee.aborts;
        fx->outputs |= callee.outputs;
    }
};

}  // namespace goose
