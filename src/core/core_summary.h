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
        set<CoreResultId> constructs;
        set<CoreTargetId> needs, escapes;
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

    bool Flat(CoreTypeId type) const {
        auto &t = m.Type(type);
        if (t.kind == CoreType::Int || t.kind == CoreType::Bool || t.kind == CoreType::Struct) return true;
        return t.kind == CoreType::Arr && t.count > 0 && Flat(t.elem);
    }

    bool VariableElement(CoreTypeId type) const {
        auto &t = m.Type(type);
        if (t.kind == CoreType::Arr) return VariableElement(t.elem);
        if (t.kind == CoreType::VarArr) return Flat(t.elem) || VariableElement(t.elem);
        return false;
    }

    bool Nonfixed(CoreTypeId type) const {
        auto &t = m.Type(type);
        if (t.kind == CoreType::VarArr || t.kind == CoreType::Grow || t.kind == CoreType::GrowShrink)
            return true;
        return t.kind == CoreType::Arr && VariableElement(type);
    }

    bool HandlesTarget(CoreTargetId target, CoreImplId impl) const {
        return target >= 0 && target < (int)m.targets.size() &&
               find(m.targets[target].members.begin(), m.targets[target].members.end(), impl) !=
                   m.targets[target].members.end();
    }

    void NoteResultConstruction() {
        for (size_t i = 0; i < Impl().results.size(); i++)
            if (Nonfixed(Impl().results[i].type)) fx->constructs.insert((CoreResultId)i);
    }

    void NoteTargetTransfer(CoreTargetId target) {
        if (HandlesTarget(target, (CoreImplId)ci)) NoteResultConstruction();
        else {
            fx->needs.insert(target);
            fx->escapes.insert(target);
        }
    }

    bool IsLimitedOwner(const CorePlace &place) const {
        auto type = m.PlaceType((int)ci, place);
        return type && m.Type(*type).kind == CoreType::Limited;
    }

    optional<uint64_t> MaximumElements(CoreTypeId type) const {
        if (type < 0 || type >= (int)m.types.size()) return {};
        auto &t = m.Type(type);
        if (t.kind == CoreType::Arr || t.kind == CoreType::Limited)
            return t.count >= 0 ? optional<uint64_t>(t.count) : nullopt;
        if (t.kind == CoreType::VarArr) return uint64_t(UINT32_MAX);
        return {};
    }

    optional<uint64_t> DescriptorMaximum(const CoreResultDescriptor &descriptor) const {
        if (m.Type(descriptor.type).kind == CoreType::VarArr &&
            descriptor.request == CoreRequest::ElementRun) return {};
        return MaximumElements(descriptor.type);
    }

    optional<uint64_t> ExpressionMaximum(const CoreExpr &expression) const {
        switch (expression.kind) {
            case CoreExprKind::Bytes: return expression.bytes.size();
            case CoreExprKind::Arr: return expression.elems.size();
            case CoreExprKind::Fill: return MaximumElements(expression.type);
            case CoreExprKind::Copy: {
                auto type = m.PlaceType((int)ci, *expression.place);
                return type ? MaximumElements(*type) : nullopt;
            }
            case CoreExprKind::If: {
                auto left = BlockMaximum(*expression.then);
                auto right = BlockMaximum(*expression.otherwise);
                return left && right ? optional<uint64_t>(max(*left, *right)) : nullopt;
            }
            case CoreExprKind::Block: return BlockMaximum(*expression.then);
            case CoreExprKind::String: {
                uint64_t count = 0;
                for (auto &part : expression.print) {
                    if (part.kind != CorePrintArg::Text) return {};
                    if (part.str.size() > UINT64_MAX - count) return {};
                    count += part.str.size();
                }
                return count;
            }
            case CoreExprKind::Call: {
                auto &callee = m.impls[m.contexts[expression.ctx].impl];
                return callee.results.size() == 1 ? DescriptorMaximum(callee.results[0]) : nullopt;
            }
            case CoreExprKind::Values: return {};
            case CoreExprKind::Read: {
                auto type = m.PlaceType((int)ci, *expression.place);
                return type ? MaximumElements(*type) : nullopt;
            }
            case CoreExprKind::ResultLocal:
                return MaximumElements(m.impls[ci].vars[expression.var].type);
            default: return MaximumElements(expression.type);
        }
    }

    optional<uint64_t> BlockMaximum(const CoreBlock &block) const {
        return block.value ? ExpressionMaximum(*block.value) : nullopt;
    }

    using ChannelMaxima = vector<optional<uint64_t>>;

    static optional<ChannelMaxima> MergeProducerMaxima(optional<ChannelMaxima> left,
                                                      optional<ChannelMaxima> right) {
        if (!left || !right) return {};
        if (left->empty()) return right;
        if (right->empty()) return left;
        if (left->size() != right->size()) return {};
        for (size_t i = 0; i < left->size(); i++)
            (*left)[i] = (*left)[i] && (*right)[i]
                             ? optional<uint64_t>(max(*(*left)[i], *(*right)[i])) : nullopt;
        return left;
    }

    optional<ChannelMaxima> ProducerMaximum(const CoreExpr &producer) const {
        switch (producer.kind) {
            case CoreExprKind::Values: {
                ChannelMaxima maxima;
                for (auto &value : producer.values) maxima.push_back(ExpressionMaximum(*value));
                return maxima;
            }
            case CoreExprKind::Call: {
                ChannelMaxima maxima;
                for (auto &descriptor : m.impls[m.contexts[producer.ctx].impl].results)
                    maxima.push_back(DescriptorMaximum(descriptor));
                return maxima;
            }
            case CoreExprKind::If:
                return MergeProducerMaxima(BlockProducerMaximum(*producer.then),
                                           BlockProducerMaximum(*producer.otherwise));
            case CoreExprKind::Block: {
                auto maxima = BlockProducerMaximum(*producer.then);
                if (maxima && maxima->empty()) return {};
                return maxima;
            }
            default: return ChannelMaxima {ExpressionMaximum(producer)};
        }
    }

    optional<ChannelMaxima> BlockProducerMaximum(const CoreBlock &block) const {
        auto breaks = StatementBreakMaximum(block.stmts);
        auto normal = block.value ? ProducerMaximum(*block.value) : optional<ChannelMaxima>(ChannelMaxima {});
        return MergeProducerMaxima(std::move(breaks), std::move(normal));
    }

    optional<ChannelMaxima> StatementBreakMaximum(const vector<CoreStmt> &statements) const {
        optional<ChannelMaxima> maxima = ChannelMaxima {};
        for (auto &statement : statements) {
            optional<ChannelMaxima> current = ChannelMaxima {};
            if (statement.kind == CoreStmtKind::BreakValue) current = ProducerMaximum(*statement.expr);
            else if (statement.kind == CoreStmtKind::If) {
                current = StatementBreakMaximum(statement.then->stmts);
                if (statement.otherwise)
                    current = MergeProducerMaxima(std::move(current),
                                                   StatementBreakMaximum(statement.otherwise->stmts));
            } else if (statement.kind == CoreStmtKind::While || statement.kind == CoreStmtKind::ForRange ||
                       statement.kind == CoreStmtKind::ForEach)
                current = StatementBreakMaximum(statement.then->stmts);
            maxima = MergeProducerMaxima(std::move(maxima), std::move(current));
        }
        return maxima;
    }

    optional<uint64_t> ReceivingCapacity(CoreTypeId type, CoreRequest request) const {
        auto &t = m.Type(type);
        if (t.kind == CoreType::Limited) return MaximumElements(type);
        if (t.kind == CoreType::VarArr && request == CoreRequest::Value) return uint64_t(UINT32_MAX);
        return {};
    }

    void NoteReceivingCapacity(CoreTypeId type, CoreRequest request, const CoreExpr &expression) {
        if (!CoreHasConstruction(m.profile)) return;
        auto capacity = ReceivingCapacity(type, request);
        if (!capacity) return;
        auto maximum = ExpressionMaximum(expression);
        if (!maximum || *maximum > *capacity) fx->aborts = true;
    }

    void NoteProducerCapacities(const vector<CoreResultDescriptor> &descriptors, const CoreExpr &producer) {
        if (!CoreHasConstruction(m.profile)) return;
        auto maxima = ProducerMaximum(producer);
        for (size_t i = 0; i < descriptors.size(); i++) {
            auto capacity = ReceivingCapacity(descriptors[i].type, descriptors[i].request);
            if (!capacity) continue;
            if (!maxima || maxima->size() != descriptors.size() || !(*maxima)[i] ||
                *(*maxima)[i] > *capacity) fx->aborts = true;
        }
    }

    void NoteOperandCapacities(const vector<CoreResultDescriptor> &descriptors,
                               const vector<CoreExprP> &operands) {
        for (size_t i = 0; i < min(descriptors.size(), operands.size()); i++)
            NoteReceivingCapacity(descriptors[i].type, descriptors[i].request, *operands[i]);
    }

    static bool Same(const CoreSummary &a, const CoreSummary &b) {
        return a.unknown == b.unknown && a.reads == b.reads && a.writes == b.writes &&
               a.grows == b.grows && a.shrinks == b.shrinks && a.rebinds == b.rebinds &&
               a.constructs == b.constructs && a.needs == b.needs && a.escapes == b.escapes &&
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
        if (Impl().body.value) {
            NoteResultConstruction();
            NoteProducerCapacities(Impl().results, *Impl().body.value);
        }
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
            if (Impl().body.value) {
                NoteResultConstruction();
                NoteProducerCapacities(Impl().results, *Impl().body.value);
            }
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
        s.constructs.assign(e.constructs.begin(), e.constructs.end());
        s.constructs.insert(s.constructs.end(), g.constructs.begin(), g.constructs.end());
        sort(s.constructs.begin(), s.constructs.end());
        s.constructs.erase(unique(s.constructs.begin(), s.constructs.end()), s.constructs.end());
        s.needs.assign(e.needs.begin(), e.needs.end());
        s.needs.insert(s.needs.end(), g.needs.begin(), g.needs.end());
        sort(s.needs.begin(), s.needs.end());
        s.needs.erase(unique(s.needs.begin(), s.needs.end()), s.needs.end());
        s.escapes.assign(e.escapes.begin(), e.escapes.end());
        s.escapes.insert(s.escapes.end(), g.escapes.begin(), g.escapes.end());
        sort(s.escapes.begin(), s.escapes.end());
        s.escapes.erase(unique(s.escapes.begin(), s.escapes.end()), s.escapes.end());
        s.aborts = e.aborts || g.aborts;
        s.outputs = e.outputs || g.outputs;
        if (s.unknown) s = CoreSummary { true, {}, {}, {}, {}, {}, {}, {}, {}, false, false };
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
            case CoreStmtKind::Let:
                Bind(s.var, Ex(*s.expr));
                NoteReceivingCapacity(Impl().vars[s.var].type, CoreRequest::Value, *s.expr);
                break;
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
                if (CoreHasShrink(m.profile)) AddTargets(fx->writes, rho);
                AddTargets(fx->grows, rho);
                if (IsLimitedOwner(*s.place)) fx->aborts = true;
                break;
            }
            case CoreStmtKind::AssignWhole: {
                auto rho = Pl(*s.place);
                Ex(*s.expr);
                if (auto type = m.PlaceType((int)ci, *s.place))
                    NoteReceivingCapacity(*type, CoreRequest::Value, *s.expr);
                AddTargets(fx->reads, rho);
                AddTargets(fx->shrinks, rho);
                AddTargets(fx->writes, rho);
                AddTargets(fx->grows, rho);
                break;
            }
            case CoreStmtKind::PopN: {
                auto rho = Pl(*s.place);
                Ex(*s.expr);
                AddTargets(fx->reads, rho);
                AddTargets(fx->shrinks, rho);
                fx->aborts = true;
                break;
            }
            case CoreStmtKind::Resize: {
                auto rho = Pl(*s.place);
                Ex(*s.expr);
                if (s.expr2) Ex(*s.expr2);
                AddTargets(fx->reads, rho);
                AddTargets(fx->shrinks, rho);
                fx->aborts = true;
                if (s.expr2) {
                    AddTargets(fx->writes, rho);
                    AddTargets(fx->grows, rho);
                }
                break;
            }
            case CoreStmtKind::Clear: {
                auto rho = Pl(*s.place);
                AddTargets(fx->reads, rho);
                AddTargets(fx->shrinks, rho);
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
            case CoreStmtKind::Receive: {
                vector<Roots> results;
                if (s.expr->kind == CoreExprKind::Call) Call(*s.expr, &results);
                else if (s.expr->kind == CoreExprKind::Values) {
                    for (auto &value : s.expr->values) results.push_back(Ex(*value));
                } else Ex(*s.expr);
                for (size_t i = 0; i < s.vars.size() && i < results.size(); i++) Bind(s.vars[i], results[i]);
                vector<CoreResultDescriptor> descriptors;
                for (auto var : s.vars) {
                    auto type = Impl().vars[var].type;
                    descriptors.push_back({type, Nonfixed(type) ? CoreRequest::Value : CoreRequest::Register});
                }
                NoteProducerCapacities(descriptors, *s.expr);
                break;
            }
            case CoreStmtKind::AppendValue:
            case CoreStmtKind::AppendConstruct: {
                auto rho = Pl(*s.place);
                Ex(*s.expr);
                if (CoreHasShrink(m.profile)) AddTargets(fx->writes, rho);
                AddTargets(fx->grows, rho);
                if (IsLimitedOwner(*s.place)) fx->aborts = true;
                break;
            }
            case CoreStmtKind::Ret:
                if (s.expr) Ex(*s.expr);
                if (s.expr) NoteResultConstruction();
                if (s.expr && !Impl().results.empty())
                    NoteReceivingCapacity(Impl().results[0].type, Impl().results[0].request, *s.expr);
                break;
            case CoreStmtKind::RetValues:
                for (auto &value : s.values) Ex(*value);
                if (!s.values.empty()) NoteResultConstruction();
                NoteOperandCapacities(Impl().results, s.values);
                break;
            case CoreStmtKind::ReturnFrom:
                for (auto &value : s.values) Ex(*value);
                NoteTargetTransfer(s.target);
                NoteOperandCapacities(m.impls[m.targets[s.target].members[0]].results, s.values);
                break;
            case CoreStmtKind::RetForward:
                Ex(*s.expr);
                NoteResultConstruction();
                NoteProducerCapacities(Impl().results, *s.expr);
                break;
            case CoreStmtKind::ReturnFromForward:
                Ex(*s.expr);
                NoteTargetTransfer(s.target);
                NoteProducerCapacities(m.impls[m.targets[s.target].members[0]].results, *s.expr);
                break;
            case CoreStmtKind::BreakValue:
                Ex(*s.expr);
                break;
            case CoreStmtKind::Print:
                fx->outputs = true;
                for (auto &a : s.print) {
                    if (a.kind == CorePrintArg::Expr) Ex(*a.expr);
                    if (a.kind == CorePrintArg::View) Vw(*a.view);
                }
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
            case CoreExprKind::Lit: case CoreExprKind::Bool:
            case CoreExprKind::ResultLocal: return {};
            case CoreExprKind::Bytes:
                if (CoreHasConstruction(m.profile) && m.Type(e.type).kind == CoreType::Limited &&
                    e.bytes.size() > (uint64_t)m.Type(e.type).count) fx->aborts = true;
                return {};
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
                if (CoreHasShrink(m.profile)) AddTargets(fx->writes, rho);
                AddTargets(fx->grows, rho);
                if (IsLimitedOwner(*e.place)) fx->aborts = true;
                return rho;
            }
            case CoreExprKind::Pop: {
                auto rho = Pl(*e.place);
                AddTargets(fx->reads, rho);
                AddTargets(fx->shrinks, rho);
                fx->aborts = true;
                return {};
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
                if (CoreHasConstruction(m.profile) && e.kind == CoreExprKind::Arr &&
                    m.Type(e.type).kind == CoreType::Limited &&
                    e.elems.size() > (uint64_t)m.Type(e.type).count) fx->aborts = true;
                return {};
            case CoreExprKind::Fill: Ex(*e.a); return {};
            case CoreExprKind::String:
                for (auto &part : e.print) {
                    if (part.kind == CorePrintArg::Expr) Ex(*part.expr);
                    if (part.kind == CorePrintArg::View) Vw(*part.view);
                }
                if (CoreHasConstruction(m.profile) && m.Type(e.type).kind == CoreType::Limited)
                    fx->aborts = true;
                return {};
            case CoreExprKind::Copy: {
                if (CoreHasConstruction(m.profile) && m.Type(e.type).kind == CoreType::Limited)
                    fx->aborts = true;
                auto rho = Pl(*e.place);
                AddTargets(fx->reads, rho);
                return {};
            }
            case CoreExprKind::Values: {
                Roots roots;
                for (auto &value : e.values) roots = Union(roots, Ex(*value));
                return roots;
            }
        }
        return {};
    }

    Roots Call(const CoreExpr &e, vector<Roots> *resultRoots = nullptr) {
        vector<Roots> argroots;
        for (auto &a : e.args)
            argroots.push_back(visit([&](const auto &arg) -> Roots {
                using Arg = decay_t<decltype(arg)>;
                if constexpr (is_same_v<Arg, CoreArgReference>) return Pl(*arg.place);
                else return Ex(*arg.expr);
            }, a));
        auto &ctx = m.contexts[e.ctx];
        auto &callee = m.impls[ctx.impl];
        for (size_t i = 0; i < min(callee.params.size(), e.args.size()); i++)
            if (auto argument = get_if<CoreArgConstruct>(&e.args[i]))
                NoteReceivingCapacity(callee.vars[callee.params[i].var].type, CoreRequest::Value,
                                      *argument->expr);
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
            for (auto target : callee.summary.needs)
                if (!HandlesTarget(target, (CoreImplId)ci)) fx->needs.insert(target);
            for (auto target : callee.summary.escapes) {
                if (HandlesTarget(target, (CoreImplId)ci)) NoteResultConstruction();
                else fx->escapes.insert(target);
            }
            fx->aborts |= callee.summary.aborts;
            fx->outputs |= callee.summary.outputs;
        }
        Roots out;
        for (size_t i = 0; i < callee.results.size() && i < ctx.resultroots.size(); i++) {
            Roots roots;
            if (m.IsRefOrSlice(callee.results[i].type))
                for (auto &r : ctx.resultroots[i]) {
                    if (r.kind == CoreRootRef::Param && r.index < (int)argroots.size())
                        roots = Union(roots, argroots[r.index]);
                    else if (r.kind == CoreRootRef::Global || r.kind == CoreRootRef::Static)
                        roots = Union(roots, { r });
                }
            out = Union(out, roots);
            if (resultRoots) resultRoots->push_back(std::move(roots));
        }
        return out;
    }
};

}  // namespace goose
