// Goose compiler — Typed Goose Core, effect summaries.
//
// The summary of an implementation must contain the effects the validator
// recomputes from its body in the implementation's context. Those are found
// by one traversal that carries the set of roots of every place, view and
// reference-typed value, taking a variable's roots from the context's
// annotation: the storage a read, a write, a growth reaches is the global or
// parameter roots of the place it goes through, and locals are not targets.
// A call contributes its callee's declared summary with each callee parameter
// replaced by the targets of the roots of the argument. This pass repeats
// that traversal and declares what it finds, to a fixed point, so recursion
// needs no special case; a callee with an unknown summary makes the caller's
// unknown. Each implementation has exactly one context, so the context's
// annotation is the one in force.
#pragma once

namespace goose {

class CoreSummarizer {
public:
    explicit CoreSummarizer(CoreModule &module) : m(module) {}

    void Run() {
        for (auto changed = true; changed;) {
            changed = false;
            for (size_t i = 0; i < m.impls.size(); i++) {
                auto s = Summarize(i);
                if (!Same(s, m.impls[i].summary)) {
                    m.impls[i].summary = std::move(s);
                    changed = true;
                }
            }
        }
    }

private:
    CoreModule &m;

    using Roots = vector<CoreRootRef>;

    struct Effects {
        set<CoreTarget> reads, writes, grows, shrinks, rebinds;
        bool aborts = false, outputs = false, unknown = false;
    };

    size_t ci = 0;       // The implementation (and context) being walked.
    Effects *fx = nullptr;

    // The lowered form of a module has no root annotations: a parameter is
    // rooted at itself and a local at whatever flowed into it. The traversal
    // can be run that way too (`flow`), so that the summary also contains what
    // a validator of the lowered form finds.
    bool flow = false;
    vector<Roots> flowroots;
    bool flowchanged = false;

    void Bind(int var, const Roots &rho) {
        if (!flow || !m.IsRefOrSlice(Impl().vars[var].type)) return;
        auto &dst = flowroots[var];
        for (auto &r : rho)
            if (find(dst.begin(), dst.end(), r) == dst.end()) {
                dst.push_back(r);
                flowchanged = true;
            }
    }

    CoreImpl &Impl() { return m.impls[ci]; }

    static bool Same(const CoreSummary &a, const CoreSummary &b) {
        return a.unknown == b.unknown && a.reads == b.reads && a.writes == b.writes &&
               a.grows == b.grows && a.shrinks == b.shrinks && a.rebinds == b.rebinds &&
               a.aborts == b.aborts &&
               a.outputs == b.outputs;
    }

    static Roots Union(Roots a, const Roots &b) {
        for (auto &r : b) if (find(a.begin(), a.end(), r) == a.end()) a.push_back(r);
        return a;
    }

    static void AddTargets(set<CoreTarget> &to, const Roots &rs) {
        for (auto &r : rs) {
            if (r.kind == CoreRootRef::Global) to.insert(CoreTarget { true, r.index });
            else if (r.kind == CoreRootRef::Param) to.insert(CoreTarget { false, r.index });
        }
    }

    const Roots *Annotation(int var) {
        if (flow) return &flowroots[var];
        for (auto &vr : m.contexts[ci].varroots)
            if (vr.first == var) return &vr.second;
        return nullptr;
    }

    // The content roots the context declares for a reference to a slice.
    Roots Content(int var) {
        auto &c = m.contexts[ci];
        for (size_t i = 0; i < c.varroots.size(); i++)
            if (c.varroots[i].first == var && i < c.hascontent.size() && c.hascontent[i]) return c.content[i];
        return {};
    }

    // ---------------------------------------------------------------------

    // What the traversal finds is declared in terms of the parameters where it
    // can be: a global that a reference parameter is annotated with is declared
    // as that parameter, which the validator expands back to the annotation.
    // A parameter target that no parameter's annotation covers cannot be
    // declared, and the summary is unknown.
    CoreSummary Summarize(size_t i) {
        ci = i;
        Effects e;
        flow = false;
        fx = &e;
        Block(Impl().body);
        // Again as the lowered form is judged; what that finds is declared as
        // found, and joins what the annotated traversal declares.
        Effects g;
        flow = true;
        fx = &g;
        flowroots.assign(Impl().vars.size(), Roots {});
        for (auto &p : Impl().params)
            if (m.IsRefOrSlice(Impl().vars[p.var].type))
                flowroots[p.var] = { CoreRootRef { CoreRootRef::Param, p.var } };
        do {
            flowchanged = false;
            g = Effects {};
            Block(Impl().body);
        } while (flowchanged);
        flow = false;
        fx = nullptr;
        CoreSummary s;
        if (e.unknown || g.unknown) { s.unknown = true; return s; }
        auto &impl = Impl();
        auto declare = [&](const set<CoreTarget> &found, vector<CoreTarget> &out) {
            set<CoreTarget> d;
            for (auto &t : found) {
                if (!t.global) {
                    // Declared as itself; the validator expands it through the
                    // annotation, which must cover it.
                    auto ann = t.index < (int)impl.vars.size() &&
                                       m.IsRefOrSlice(impl.vars[t.index].type)
                                   ? Annotation(t.index) : nullptr;
                    if (ann && find(ann->begin(), ann->end(),
                                    CoreRootRef { CoreRootRef::Param, t.index }) == ann->end()) {
                        s.unknown = true;
                        return;
                    }
                    d.insert(t);
                    continue;
                }
                auto covered = false;
                for (auto &p : impl.params) {
                    auto ann = m.IsRefOrSlice(impl.vars[p.var].type) ? Annotation(p.var) : nullptr;
                    if (ann && find(ann->begin(), ann->end(),
                                    CoreRootRef { CoreRootRef::Global, t.index }) != ann->end()) {
                        d.insert(CoreTarget { false, p.var });
                        covered = true;
                        break;
                    }
                }
                if (!covered) d.insert(t);
            }
            out.assign(d.begin(), d.end());
        };
        declare(e.reads, s.reads);
        declare(e.writes, s.writes);
        declare(e.grows, s.grows);
        declare(e.shrinks, s.shrinks);
        auto join = [](vector<CoreTarget> &to, const set<CoreTarget> &more) {
            set<CoreTarget> all(to.begin(), to.end());
            all.insert(more.begin(), more.end());
            to.assign(all.begin(), all.end());
        };
        join(s.reads, g.reads);
        join(s.writes, g.writes);
        join(s.grows, g.grows);
        join(s.shrinks, g.shrinks);
        s.rebinds.assign(e.rebinds.begin(), e.rebinds.end());
        join(s.rebinds, g.rebinds);
        s.aborts = e.aborts || g.aborts;
        s.outputs = e.outputs || g.outputs;
        if (s.unknown) s = CoreSummary { true, {}, {}, {}, {}, {}, false, false };
        return s;
    }

    static bool MayAbort(CoreBinOp op) {
        return op == CoreBinOp::Add || op == CoreBinOp::Sub || op == CoreBinOp::Mul ||
               op == CoreBinOp::Div || op == CoreBinOp::Mod;
    }

    // A block's statements, then its value; the roots of the value.
    Roots Block(const CoreBlock &b) {
        for (auto &s : b.stmts) Stmt(s);
        return b.value ? Ex(*b.value) : Roots {};
    }

    void Stmt(const CoreStmt &s) {
        switch (s.kind) {
            case CoreStmtKind::Let: Bind(s.var, Ex(*s.expr)); break;
            case CoreStmtKind::Assign: {
                auto rho = Pl(*s.place);
                Ex(*s.expr);
                AddTargets(fx->writes, rho);
                // A slice stored through a reference parameter replaces the
                // slice the variable it refers to holds: a rebind of the parameter.
                if (m.Type(s.expr->type).kind == CoreType::Slice && s.place->kind == CorePlace::Deref &&
                    s.place->expr->kind == CoreExprKind::Read && s.place->expr->place->kind == CorePlace::Local &&
                    s.place->expr->place->index < (int)Impl().params.size())
                    fx->rebinds.insert(CoreTarget { false, s.place->expr->place->index });
                break;
            }
            case CoreStmtKind::AssignOp: {
                auto rho = Pl(*s.place);
                Ex(*s.expr);
                AddTargets(fx->reads, rho);
                AddTargets(fx->writes, rho);
                if (MayAbort(s.bin)) fx->aborts = true;
                break;
            }
            case CoreStmtKind::Rebind:
                Bind(s.var, Ex(*s.expr));
                if (s.var < (int)Impl().params.size()) fx->rebinds.insert(CoreTarget { false, s.var });
                break;
            case CoreStmtKind::Expr: Ex(*s.expr); break;
            case CoreStmtKind::Append: {
                auto rho = Pl(*s.place);
                Vw(*s.view);
                if (m.profile == CoreProfile::Shrink) AddTargets(fx->writes, rho);
                AddTargets(fx->grows, rho);
                break;
            }
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
            case CoreStmtKind::ForEach: {
                auto rho = Vw(*s.view);
                // Each element is copied out of the run, which reads it; an
                // element bound by reference is not read until it is used.
                if (s.byRef) Bind(s.var, rho);
                else AddTargets(fx->reads, rho);
                Block(*s.then);
                break;
            }
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

    Roots Pl(const CorePlace &p) {
        switch (p.kind) {
            case CorePlace::Local: return { CoreRootRef { CoreRootRef::Local, p.index } };
            case CorePlace::Global: return { CoreRootRef { CoreRootRef::Global, p.index } };
            case CorePlace::Deref: return Ex(*p.expr);
            case CorePlace::Elem: {
                auto rho = Vw(*p.view);
                Ex(*p.expr);
                fx->aborts = true;
                return rho;
            }
            case CorePlace::Field: return Pl(*p.base);
        }
        return {};
    }

    // Sampling an owner's run reads it.
    Roots Vw(const CoreView &v) {
        if (v.kind == CoreView::Val) return Ex(*v.expr);
        auto rho = Pl(*v.place);
        AddTargets(fx->reads, rho);
        return rho;
    }

    Roots Ex(const CoreExpr &e) {
        switch (e.kind) {
            case CoreExprKind::Lit: case CoreExprKind::Bool: return {};
            case CoreExprKind::Read: {
                auto rho = Pl(*e.place);
                AddTargets(fx->reads, rho);
                // A slice read through a reference parameter is rooted where
                // the context says what that parameter's slice may be rooted at.
                if (m.Type(e.type).kind == CoreType::Slice && e.place->kind == CorePlace::Deref &&
                    e.place->expr->kind == CoreExprKind::Read && e.place->expr->place->kind == CorePlace::Local)
                    return Content(e.place->expr->place->index);
                if (e.place->kind == CorePlace::Local && m.IsRefOrSlice(Impl().vars[e.place->index].type))
                    if (auto ann = Annotation(e.place->index)) return *ann;
                return {};
            }
            case CoreExprKind::Ref: return Pl(*e.place);
            case CoreExprKind::Slice: {
                auto rho = Vw(*e.view);
                if (e.lo.expr) Ex(*e.lo.expr);
                if (e.hi.expr) Ex(*e.hi.expr);
                fx->aborts = true;
                return rho;
            }
            case CoreExprKind::Len: Vw(*e.view); return {};
            case CoreExprKind::Un:
                Ex(*e.a);
                if (e.un == CoreUnOp::Neg) fx->aborts = true;
                return {};
            case CoreExprKind::Bin:
                Ex(*e.a);
                Ex(*e.b);
                if (MayAbort(e.bin)) fx->aborts = true;
                return {};
            case CoreExprKind::Cmp: case CoreExprKind::And: case CoreExprKind::Or:
                Ex(*e.a);
                Ex(*e.b);
                return {};
            case CoreExprKind::Not: Ex(*e.a); return {};
            case CoreExprKind::Conv:
                Ex(*e.a);
                if (e.conv == CoreConvKind::As) fx->aborts = true;
                return {};
            case CoreExprKind::Call: return Call(e);
            case CoreExprKind::Push: {
                auto rho = Pl(*e.place);
                Ex(*e.a);
                if (m.profile == CoreProfile::Shrink) AddTargets(fx->writes, rho);
                AddTargets(fx->grows, rho);
                return rho;
            }
            case CoreExprKind::If: {
                Ex(*e.a);
                auto t = Block(*e.then);
                return Union(t, Block(*e.otherwise));
            }
            case CoreExprKind::Block: return Block(*e.then);
            case CoreExprKind::Arr:
            case CoreExprKind::Struct:
                for (auto &el : e.elems) Ex(*el);
                return {};
            case CoreExprKind::Fill: Ex(*e.a); return {};
        }
        return {};
    }

    Roots Call(const CoreExpr &e) {
        vector<Roots> argroots;
        for (auto &a : e.args)
            argroots.push_back(a.kind == CoreArg::Val ? Ex(*a.expr) : Pl(*a.place));
        auto &ctx = m.contexts[e.ctx];
        auto &callee = m.impls[ctx.impl];
        if (callee.summary.unknown) fx->unknown = true;
        else {
            auto map = [&](const vector<CoreTarget> &from, set<CoreTarget> &to) {
                for (auto &t : from) {
                    if (t.global) to.insert(t);
                    else if (t.index < (int)argroots.size()) {
                        AddTargets(to, argroots[t.index]);
                        // And the globals the callee's context lists for the
                        // parameter, which an entry for it stands for there too.
                        for (auto &vr : ctx.varroots)
                            if (vr.first == t.index && m.IsRefOrSlice(callee.vars[t.index].type))
                                for (auto &r : vr.second)
                                    if (r.kind == CoreRootRef::Global) to.insert(CoreTarget { true, r.index });
                    }
                }
            };
            map(callee.summary.reads, fx->reads);
            map(callee.summary.writes, fx->writes);
            map(callee.summary.grows, fx->grows);
            map(callee.summary.shrinks, fx->shrinks);
            fx->aborts |= callee.summary.aborts;
            fx->outputs |= callee.summary.outputs;
        }
        Roots out;
        if (callee.results.size() == 1 && m.IsRefOrSlice(callee.results[0]) && ctx.resultroots.size() == 1)
            for (auto &r : ctx.resultroots[0]) {
                if (r.kind == CoreRootRef::Param && r.index < (int)argroots.size())
                    out = Union(out, argroots[r.index]);
                else if (r.kind == CoreRootRef::Global) out = Union(out, { r });
            }
        return out;
    }
};

}  // namespace goose
