// Goose compiler — Typed Goose Core, export from the checked program.
//
// Reads the checked, unoptimized specializations reachable from `main` and
// builds the in-memory module (core_ir.h) without changing anything: it
// creates no types and no specializations and prints no warnings. What the
// checker left implicit is made explicit here. Reference transparency becomes
// a read through a dereference, array-to-slice coercions become slicing,
// implicit integer widening becomes a conversion, and a nested function
// becomes an ordinary implementation that takes each free variable as a
// trailing by-reference parameter. A program that uses anything outside the
// pilot profile throws CoreUnsupported with the feature's name.
#pragma once

namespace goose {

struct CoreUnsupported {
    string feature;
    Line at;
};

class CoreExporter {
public:
    CoreExporter(Ast &a, const string &entry)
        : ast(a), entrypath(entry), entrydir(filesystem::path(entry).parent_path().generic_string()) {}

    CoreModule Export() {
        auto mainsf = ast.MainFunction();
        if (!mainsf || mainsf->specs.empty()) Fail("no-entry", Line {});
        auto mainspec = mainsf->specs[0];
        if (!mainspec->params.empty() || !mainspec->rets.empty()) Fail("entry-signature", mainsf->line);
        FindReachable(mainspec);
        ExportGlobals();
        // Contexts are numbered as calls are met, so building an
        // implementation may add contexts after it.
        ContextOf(mainspec);
        for (size_t k = 0; k < ctxspecs.size(); k++) BuildImpl((int)k);
        ExpandGlobalClasses();
        mod.entry = 0;
        return std::move(mod);
    }

private:
    Ast &ast;
    string entrypath;
    string entrydir;
    CoreModule mod;

    unordered_map<const VarDef *, int> globalindex;
    unordered_map<const VarDef *, CoreUnsupported> skipped;   // Library globals left out, and why.
    unordered_map<int, int> filemap;            // AST file index -> module file index

    vector<FnSpec *> ctxspecs;
    unordered_map<const FnSpec *, int> ctxof;

    // The free variables of each reachable specialization, in the order the
    // legacy backend passes them.
    unordered_map<const FnSpec *, vector<VarDef *>> freevars;

    // ---------------------------------------------------------------------
    // The implementation under construction.

    struct Cur {
        FnSpec *spec = nullptr;          // Null in a global initializer.
        CoreImpl *impl = nullptr;
        vector<VarDef *> vardefs;        // Aligned with impl->vars; null for a free variable's parameter.
        unordered_map<const VarDef *, int> varid;
        int nextscope = 0;
        vector<VarDef *> *free = nullptr;
    } cur;

    // Control flow inside an expression block: how many such blocks are open,
    // and how many loops are open inside the innermost one. `return` may not
    // leave an expression block, and `break` or `continue` only a loop of the
    // block's own.
    int exprdepth = 0;
    int loops = 0;

    struct ExprBlockScope {
        CoreExporter &x;
        int savedloops;
        explicit ExprBlockScope(CoreExporter &e) : x(e), savedloops(e.loops) { x.exprdepth++; x.loops = 0; }
        ~ExprBlockScope() { x.exprdepth--; x.loops = savedloops; }
    };

    // The construct whose operations a coercion belongs to.
    CoreOrigin coerceorg;
    Line here;

    [[noreturn]] void Fail(const char *feature, Line at) { throw CoreUnsupported { feature, at }; }
    [[noreturn]] void Fail(const char *feature) { throw CoreUnsupported { feature, here }; }

    // ---------------------------------------------------------------------
    // Files, origins, types.

    string RelativeFile(const string &path) {
        auto p = filesystem::path(path).lexically_normal();
        auto base = filesystem::path(entrydir.empty() ? "." : entrydir).lexically_normal();
        auto rel = p.lexically_relative(base);
        auto text = rel.empty() || *rel.begin() == ".." ? p.generic_string() : rel.generic_string();
        for (auto &c : text) if (c == '\\') c = '/';
        return text;
    }

    CoreOrigin Org(Line l, CoreOriginKind kind) {
        auto it = filemap.find(l.fileidx);
        if (it == filemap.end()) {
            // The program's own files are named from the entry file's
            // directory, so that the name does not depend on where the compiler
            // was run; a package's, by the package, as the linter names them.
            string path = "?";
            if (l.fileidx >= 0 && l.fileidx < (int)ast.sources.size()) {
                auto inpackage = l.fileidx < (int)ast.filepkg.size() && ast.filepkg[l.fileidx] != 0;
                path = inpackage ? LintProjectPath(ast, l.fileidx, entrypath)
                                 : RelativeFile(ast.sources[l.fileidx].first);
            }
            if (!CoreIsUtf8(path)) Fail("non-utf8-text", l);
            mod.files.push_back(path);
            it = filemap.emplace(l.fileidx, (int)mod.files.size() - 1).first;
        }
        return CoreOrigin { it->second, l.line, kind };
    }

    CoreIntTy IntTy(IntStorage s) {
        switch (s) {
            case IS_I8: return CoreIntTy::I8;
            case IS_I16: return CoreIntTy::I16;
            case IS_I32: return CoreIntTy::I32;
            case IS_I64: return CoreIntTy::I64;
            case IS_U8: return CoreIntTy::U8;
            case IS_U16: return CoreIntTy::U16;
            case IS_U32: return CoreIntTy::U32;
            case IS_U64: return CoreIntTy::U64;
            default: Fail("varint");
        }
    }

    // The element of an array or slice must be flat fixed: integers, booleans
    // and fixed arrays of those.
    CoreTypeId ElementTy(TypeExpr *t) {
        auto id = Ty(t);
        switch (mod.Type(id).kind) {
            case CoreType::Int: case CoreType::Bool: case CoreType::Arr: return id;
            case CoreType::Ref: case CoreType::Slice: Fail("stored-reference");
            default: Fail("variable-element");
        }
    }

    CoreTypeId Ty(TypeExpr *t) {
        if (!t) Fail("untyped-expression");
        CoreType ct;
        switch (t->kind) {
            case TY_INT:
                ct.kind = CoreType::Int;
                ct.ity = IntTy(t->intstorage);
                break;
            case TY_BOOL: ct.kind = CoreType::Bool; break;
            case TY_VOID: ct.kind = CoreType::Unit; break;
            case TY_FLT: Fail("float");
            case TY_STRUCT: Fail("struct");
            case TY_ENUM: case TY_VARIANT: Fail("adt");
            case TY_FN: Fail("function-value");
            case TY_ARRAY: {
                auto a = t->arr;
                switch (a->akind) {
                    case A_FIXED:
                        if (a->size < 0) Fail("array-size");
                        if (a->size == 0) Fail("zero-size-value");
                        ct.kind = CoreType::Arr;
                        ct.count = a->size;
                        break;
                    case A_GROW: ct.kind = CoreType::Grow; break;
                    case A_VAR: Fail("variable-array");
                    case A_LIMITED: Fail("limited-array");
                    case A_GROWSHRINK: Fail("grow-shrink-array");
                }
                ct.elem = ElementTy(a->sub);
                break;
            }
            case TY_SLICE:
                ct.kind = CoreType::Slice;
                ct.mut = t->cq ? CoreMut::Const : CoreMut::Mut;
                ct.elem = ElementTy(t->sub);
                break;
            case TY_REF:
                if (t->ref->optional) Fail("optional");
                if (t->ref->lenstorage >= 0) Fail("relative-reference");
                ct.kind = CoreType::Ref;
                ct.mut = t->cq ? CoreMut::Const : CoreMut::Mut;
                ct.elem = Ty(t->ref->sub);
                if (mod.Type(ct.elem).kind == CoreType::Ref || mod.Type(ct.elem).kind == CoreType::Slice)
                    Fail("reference-to-slice");
                break;
            default: Fail("type");
        }
        return mod.Intern(ct);
    }

    CoreMut MutOf(const TypeExpr *t) { return t && t->cq ? CoreMut::Const : CoreMut::Mut; }

    // The value type behind a reference.
    static TypeExpr *Pointee(TypeExpr *t) {
        return t->kind == TY_REF && !t->ref->optional ? t->ref->sub : t;
    }

    static bool IsArrayTE(const TypeExpr *t) { return t && t->kind == TY_ARRAY; }

    // ---------------------------------------------------------------------
    // Reachability and free variables.

    // The reachable specializations, in discovery order, and for each its free
    // variables as codegen's frame pass computes them: the variables of other
    // activations its body names in order of first appearance, then those its
    // callees need, to a fixed point.
    void FindReachable(FnSpec *root) {
        vector<FnSpec *> order { root };
        unordered_set<const FnSpec *> seen { root };
        unordered_map<const FnSpec *, vector<FnSpec *>> callees;
        for (size_t i = 0; i < order.size(); i++) {
            auto sp = order[i];
            if (!sp->body) Fail("extern-fn", sp->sf->line);
            if (sp->isfunval) Fail("function-value", sp->sf->line);
            auto &fv = freevars[sp];
            unordered_set<const VarDef *> have;
            unordered_set<const FnSpec *> edge;
            auto &calls = callees[sp];
            function<void(Node *)> walk = [&](Node *n) {
                if (!n) return;
                if (auto id = Is<Ident>(n)) {
                    auto v = id->vdef;
                    if (v && v->ownerspec != sp && !v->isglobal && have.insert(v).second)
                        fv.push_back(v);
                }
                if (auto c = Is<Call>(n); c && c->builtin < 0 && c->spec) {
                    auto k = c->spec;
                    if (k != sp && edge.insert(k).second) calls.push_back(k);
                    if (seen.insert(k).second) order.push_back(k);
                }
                RunChildren(n, walk);
            };
            walk(sp->body);
        }
        for (auto changed = true; changed;) {
            changed = false;
            for (auto sp : order) {
                auto &mine = freevars[sp];
                unordered_set<const VarDef *> have(mine.begin(), mine.end());
                for (auto callee : callees[sp])
                    for (auto v : freevars[callee])
                        if (v->ownerspec != sp && have.insert(v).second) {
                            mine.push_back(v);
                            changed = true;
                        }
            }
        }
    }

    int ContextOf(FnSpec *spec) {
        if (auto it = ctxof.find(spec); it != ctxof.end()) return it->second;
        auto id = (int)ctxspecs.size();
        ctxspecs.push_back(spec);
        ctxof[spec] = id;
        return id;
    }

    // ---------------------------------------------------------------------
    // Globals.

    // Every global of the program is listed, used or not, in initialization
    // order. The exception is a global of the standard library that is outside
    // the pilot profile (it holds floats, say): the library is imported whole
    // whatever the program uses, so such a global is left out, and a body that
    // names it is the error.
    void ExportGlobals() {
        cur = Cur {};
        for (auto g : ast.globals) {
            here = g->line;
            auto stdlib = g->line.fileidx >= 0 && g->line.fileidx < (int)ast.filepkg.size() &&
                          ast.packages[ast.filepkg[g->line.fileidx]].stdlib;
            try {
                ExportGlobal(g);
            } catch (CoreUnsupported &u) {
                if (!stdlib) throw;
                // Types interned for the failed global stay in the table; the
                // writer numbers by mention, so they never reach the output.
                if (g->names.size() == 1 && g->defs.size() == 1 && g->defs[0]) skipped[g->defs[0]] = u;
            }
        }
    }

    void ExportGlobal(VarDecl *g) {
        if (g->names.size() != 1 || g->defs.size() != 1) Fail("multiple-results");
        if (g->reusable) Fail("reusable");
        auto v = g->defs[0];
        if (!v || g->inits.size() != 1 || !v->type) Fail("uninitialized-declaration");
        CoreGlobal cg;
        cg.name = string(v->name);
        if (!CoreIsUtf8(cg.name)) Fail("non-utf8-text");
        cg.type = Ty(v->type);
        if (mod.IsRefOrSlice(cg.type)) Fail("stored-reference");
        cg.kind = v->isvar ? CoreVarKind::Var : CoreVarKind::Let;
        cg.org = Org(g->line, CoreOriginKind::Global);
        coerceorg = cg.org;
        cg.init = Value(g->inits[0]);
        globalindex[v] = (int)mod.globals.size();
        mod.globals.push_back(std::move(cg));
    }

    // ---------------------------------------------------------------------
    // Implementations.

    string DeclKey(FnSpec *sp) {
        string s = cat(sp->sf->ns.empty() ? string_view("main") : sp->sf->ns, "::", sp->sf->name, "(");
        for (size_t i = 0; i < sp->argtypes.size(); i++) {
            if (i) s += ", ";
            sp->argtypes[i]->Dump(s);
        }
        s += ")";
        return s;
    }

    int NewVar(VarDef *vd, string_view name, CoreTypeId type, CoreVarKind kind, int scope,
               CoreOrigin org) {
        if (!cur.impl) Fail("global-initializer-block");
        CoreVar v;
        v.name = string(name);
        if (!CoreIsUtf8(v.name)) Fail("non-utf8-text");
        v.type = type;
        v.kind = kind;
        v.scope = scope;
        v.org = org;
        cur.impl->vars.push_back(std::move(v));
        cur.vardefs.push_back(vd);
        auto id = (int)cur.impl->vars.size() - 1;
        if (vd) cur.varid[vd] = id;
        return id;
    }

    void BuildImpl(int k) {
        auto sp = ctxspecs[k];
        here = sp->sf->line;
        mod.impls.emplace_back();
        mod.contexts.emplace_back();
        auto &impl = mod.impls.back();
        cur = Cur {};
        cur.spec = sp;
        cur.impl = &impl;
        cur.free = &freevars[sp];
        impl.name = string(sp->sf->name);
        if (!CoreIsUtf8(impl.name)) Fail("non-utf8-text");
        if (sp->rets.size() > 1) Fail("multiple-results");
        if (sp->sf->isthread) Fail("thread");
        for (auto rt : sp->rets) impl.results.push_back(Ty(rt));
        auto porg = Org(sp->sf->line, CoreOriginKind::Param);
        for (size_t i = 0; i < sp->params.size(); i++) {
            auto vd = sp->params[i];
            if (vd->reusable) Fail("reusable");
            auto ty = Ty(sp->argtypes[i]);
            auto id = NewVar(vd, vd->name, ty, vd->isvar ? CoreVarKind::Var : CoreVarKind::Let, 0, porg);
            impl.params.push_back({ id, mod.Type(ty).kind == CoreType::Ref });
        }
        // A free variable is a trailing by-reference parameter: a reference to
        // the caller's variable, writable only where the variable is.
        for (auto fv : *cur.free) {
            here = sp->sf->line;
            if (fv->type->kind == TY_REF) Fail("captured-reference");
            if (fv->type->kind == TY_SLICE) Fail("reference-to-slice");
            CoreType rt;
            rt.kind = CoreType::Ref;
            rt.mut = fv->isvar ? CoreMut::Mut : CoreMut::Const;
            rt.elem = Ty(fv->type);
            auto id = NewVar(nullptr, fv->name, mod.Intern(rt), CoreVarKind::Let, 0, porg);
            cur.varid[fv] = id;
            impl.params.push_back({ id, true });
        }
        impl.body = Body(sp->body);

        auto &ctx = mod.contexts.back();
        ctx.impl = k;
        ctx.declkey = DeclKey(sp);
        FillRoots(sp, ctx);
    }

    // The function body: a value-producing tail is its return.
    CoreBlock Body(Block *b) {
        CoreBlock cb;
        cb.scope = cur.nextscope++;
        for (auto s : b->stmts) Stmt(s, cb);
        if (b->tail) {
            here = b->tail->line;
            auto t = b->tail;
            if (t->exprtype && t->exprtype->kind != TY_VOID && !cur.impl->results.empty()) {
                CoreStmt st;
                st.kind = CoreStmtKind::Ret;
                st.org = Org(t->line, CoreOriginKind::Return);
                coerceorg = st.org;
                st.expr = Value(t);
                cb.stmts.push_back(std::move(st));
            } else {
                Stmt(t, cb);
            }
        }
        return cb;
    }

    // A block as a statement body or an expression's arm. `valued` blocks keep
    // a trailing value; others turn it into a statement.
    unique_ptr<CoreBlock> BlockOf(Block *b, bool valued) {
        auto cb = make_unique<CoreBlock>();
        cb->scope = cur.nextscope++;
        for (auto s : b->stmts) Stmt(s, *cb);
        if (b->tail) {
            if (valued) {
                here = b->tail->line;
                cb->value = Value(b->tail);
            } else {
                Stmt(b->tail, *cb);
            }
        } else if (valued) {
            Fail("diverging-branch", b->line);
        }
        return cb;
    }

    // ---------------------------------------------------------------------
    // Statements.

    CoreStmt MakeStmt(CoreStmtKind k, Line l, CoreOriginKind ok) {
        CoreStmt s;
        s.kind = k;
        s.org = Org(l, ok);
        coerceorg = s.org;
        return s;
    }

    // Restores the coercion origin when a statement, which sets its own, has
    // been converted: the enclosing statement's coercions after a nested block
    // belong to the enclosing statement.
    struct OriginScope {
        CoreExporter &x;
        CoreOrigin saved;
        explicit OriginScope(CoreExporter &e) : x(e), saved(e.coerceorg) {}
        ~OriginScope() { x.coerceorg = saved; }
    };

    void Stmt(Node *n, CoreBlock &out) {
        OriginScope keep(*this);
        here = n->line;
        switch (n->nkind) {
            case NK_FnDecl: return;   // A nested function is exported where it is called.
            case NK_VarDecl: return LetStmt((VarDecl *)n, out);
            case NK_Assign: return AssignStmt((Assign *)n, out);
            case NK_IncDec: {
                auto d = (IncDec *)n;
                auto s = MakeStmt(CoreStmtKind::AssignOp, n->line, CoreOriginKind::AssignOp);
                s.bin = d->op == T_INC ? CoreBinOp::Add : CoreBinOp::Sub;
                s.place = ToPlace(d->lval, true);
                auto ty = Ty(Pointee(d->lval->exprtype));
                if (mod.Type(ty).kind != CoreType::Int) Fail("non-integer-increment");
                s.expr = IntLiteral(ty, false, 1);
                out.stmts.push_back(std::move(s));
                return;
            }
            case NK_Call: return CallStmt((Call *)n, out);
            case NK_IfExpr: {
                auto x = (IfExpr *)n;
                if (x->exprtype && x->exprtype->kind != TY_VOID) return ExprStmt(n, out);
                auto s = MakeStmt(CoreStmtKind::If, n->line, CoreOriginKind::If);
                s.expr = Value(x->cond);
                s.then = BlockOf(x->thenb, false);
                if (x->elseb) {
                    if (auto eb = Is<Block>(x->elseb)) s.otherwise = BlockOf(eb, false);
                    else {
                        // `else if`: a block of its own holding the nested if.
                        s.otherwise = make_unique<CoreBlock>();
                        s.otherwise->scope = cur.nextscope++;
                        Stmt(x->elseb, *s.otherwise);
                    }
                }
                out.stmts.push_back(std::move(s));
                return;
            }
            case NK_While: {
                auto x = (While *)n;
                auto s = MakeStmt(CoreStmtKind::While, n->line, CoreOriginKind::While);
                s.expr = Value(x->cond);
                loops++;
                s.then = BlockOf(x->body, false);
                loops--;
                out.stmts.push_back(std::move(s));
                return;
            }
            case NK_ForLoop: return ForStmt((ForLoop *)n, out);
            case NK_Return: {
                auto r = (Return *)n;
                if (!r->from.empty()) Fail("return-from");
                if (exprdepth) Fail("control-in-expression");
                if (r->vals.size() > 1) Fail("multiple-results");
                auto s = MakeStmt(CoreStmtKind::Ret, n->line, CoreOriginKind::Return);
                if (r->vals.size() == 1) s.expr = Value(r->vals[0]);
                out.stmts.push_back(std::move(s));
                return;
            }
            case NK_Break: {
                if (((Break *)n)->val) Fail("break-value");
                if (exprdepth && !loops) Fail("control-in-expression");
                out.stmts.push_back(MakeStmt(CoreStmtKind::Break, n->line, CoreOriginKind::Break));
                return;
            }
            case NK_Continue:
                if (exprdepth && !loops) Fail("control-in-expression");
                out.stmts.push_back(MakeStmt(CoreStmtKind::Continue, n->line, CoreOriginKind::Continue));
                return;
            case NK_LoopExpr: Fail("loop-expression");
            case NK_EarlyBlock: Fail("early-block");
            case NK_MatchExpr: Fail("match");
            default: return ExprStmt(n, out);
        }
    }

    void ExprStmt(Node *n, CoreBlock &out) {
        auto s = MakeStmt(CoreStmtKind::Expr, n->line, CoreOriginKind::Expr);
        s.expr = Value(n);
        out.stmts.push_back(std::move(s));
    }

    // Whether a literal of magnitude `mag` (negated when `neg`) lies in the
    // range of an integer type.
    static bool LitFits(bool neg, uint64_t mag, CoreIntTy t) {
        auto bits = CoreIntBits(t);
        if (CoreIsUnsigned(t)) return !neg || mag == 0 ? (bits == 64 || mag < (1ull << bits)) : false;
        auto limit = 1ull << (bits - 1);   // |min|; max is one less.
        return neg ? mag <= limit : mag < limit;
    }

    CoreExprP Lit(CoreTypeId ty, string v) {
        auto e = NewExpr(CoreExprKind::Lit, ty);
        e->value = std::move(v);
        return e;
    }

    CoreExprP IntLiteral(CoreTypeId ty, bool neg, uint64_t mag) {
        if (!LitFits(neg, mag, mod.Type(ty).ity)) Fail("literal-range");
        return Lit(ty, mag == 0 ? string("0") : cat(neg ? "-" : "", to_string(mag)));
    }

    CoreExprP NewExpr(CoreExprKind k, CoreTypeId ty) {
        auto e = make_unique<CoreExpr>();
        e->kind = k;
        e->type = ty;
        return e;
    }

    void LetStmt(VarDecl *d, CoreBlock &out) {
        if (d->names.size() != 1 || d->defs.size() != 1) Fail("multiple-results");
        if (d->inits.size() != 1) Fail("uninitialized-declaration");
        if (d->reusable) Fail("reusable");
        auto vd = d->defs[0];
        auto s = MakeStmt(CoreStmtKind::Let, d->line, CoreOriginKind::Let);
        // The variable is numbered before its initializer, as it is written.
        s.var = NewVar(vd, vd->name, VarTy(vd), vd->isvar ? CoreVarKind::Var : CoreVarKind::Let,
                       out.scope, Org(d->line, CoreOriginKind::Let));
        s.expr = Value(d->inits[0]);
        out.stmts.push_back(std::move(s));
    }

    // The Core type of a variable. A reference bound over a read-only source
    // is a constant reference, whatever the checker's type for it says.
    CoreTypeId VarTy(VarDef *vd) {
        auto ty = Ty(vd->type);
        auto &t = mod.Type(ty);
        if (t.kind == CoreType::Ref && t.mut == CoreMut::Mut && vd->refrootknown && !vd->ref.writable &&
            !vd->isparam) {
            auto c = t;
            c.mut = CoreMut::Const;
            return mod.Intern(c);
        }
        return ty;
    }

    static CoreBinOp AssignOpOf(TType op) {
        switch (op) {
            case T_PLUSEQ: return CoreBinOp::Add;
            case T_MINUSEQ: return CoreBinOp::Sub;
            case T_MULEQ: return CoreBinOp::Mul;
            case T_DIVEQ: return CoreBinOp::Div;
            case T_MODEQ: return CoreBinOp::Mod;
            case T_ANDEQ: return CoreBinOp::BitAnd;
            case T_OREQ: return CoreBinOp::BitOr;
            case T_XOREQ: return CoreBinOp::BitXor;
            case T_SHLEQ: return CoreBinOp::Shl;
            default: return CoreBinOp::Shr;
        }
    }

    // The variable a rebind names: a local of this implementation.
    int RebindTarget(Node *lv) {
        auto id = Is<Ident>(lv);
        if (!id || !id->vdef) Fail("rebind-target");
        auto v = id->vdef;
        if (v->isglobal) Fail("stored-reference");
        auto it = cur.varid.find(v);
        if (it == cur.varid.end() || v->ownerspec != cur.spec) Fail("captured-reference");
        return it->second;
    }

    void AssignStmt(Assign *a, CoreBlock &out) {
        if (a->op == T_DOTASSIGN) {
            auto s = MakeStmt(CoreStmtKind::Rebind, a->line, CoreOriginKind::Rebind);
            s.var = RebindTarget(a->lval);
            s.expr = Value(a->rhs);
            out.stmts.push_back(std::move(s));
            return;
        }
        if (a->op == T_ASSIGN) {
            auto id = Is<Ident>(a->lval);
            if (id && id->vdef && !a->pointee &&
                (id->vdef->type->kind == TY_SLICE || id->vdef->type->kind == TY_REF)) {
                auto v = id->vdef;
                if (!v->isglobal && v->ownerspec != cur.spec) Fail("reference-to-slice");
                auto s = MakeStmt(CoreStmtKind::Rebind, a->line, CoreOriginKind::Rebind);
                s.var = RebindTarget(a->lval);
                s.expr = Value(a->rhs);
                out.stmts.push_back(std::move(s));
                return;
            }
            auto s = MakeStmt(CoreStmtKind::Assign, a->line, CoreOriginKind::Assign);
            if (a->lval->exprtype && IsArrayTE(Pointee(a->lval->exprtype)) &&
                Pointee(a->lval->exprtype)->arr->akind != A_FIXED)
                Fail("whole-assignment");
            s.place = ToPlace(a->lval, true);
            s.expr = Value(a->rhs);
            out.stmts.push_back(std::move(s));
            return;
        }
        auto s = MakeStmt(CoreStmtKind::AssignOp, a->line, CoreOriginKind::AssignOp);
        s.bin = AssignOpOf(a->op);
        // Only integer variables take a compound assignment; an array or a
        // boolean would be elementwise or logical arithmetic.
        if (!a->lval->exprtype || Pointee(a->lval->exprtype)->kind != TY_INT)
            Fail(Pointee(a->lval->exprtype ? a->lval->exprtype : ast.voidtype)->kind == TY_BOOL
                     ? "boolean-compound-assignment" : "elementwise-arithmetic");
        s.place = ToPlace(a->lval, true);
        s.expr = Value(a->rhs);
        out.stmts.push_back(std::move(s));
    }

    void ForStmt(ForLoop *f, CoreBlock &out) {
        if (f->vartype || f->idxtype) {
            if (f->vartype) Fail("loop-binder-type");
        }
        auto vd = f->vdef;
        auto org = Org(f->line, CoreOriginKind::For);
        CoreStmt s;
        s.org = org;
        coerceorg = org;
        if (f->iterkind == IK_RANGE || f->iterkind == IK_COUNT) {
            s.kind = CoreStmtKind::ForRange;
            auto vt = Ty(vd->type);
            if (mod.Type(vt).kind != CoreType::Int) Fail("non-integer-range");
            s.var = NewVar(vd, vd->name, vt, CoreVarKind::Let, out.scope, org);
            if (auto r = Is<RangeExpr>(f->iter)) {
                s.expr = Value(r->lo);
                s.expr2 = Value(r->hi);
            } else {
                s.expr = IntLiteral(vt, false, 0);
                s.expr2 = Value(f->iter);
            }
        } else {
            s.kind = CoreStmtKind::ForEach;
            s.byRef = f->byref;
            auto vt = Ty(vd->type);
            if (s.byRef) {
                // Elements of a read-only sequence bind as constant references.
                auto &t = mod.Type(vt);
                if (t.kind == CoreType::Ref && t.mut == CoreMut::Mut && !vd->ref.writable) {
                    auto c = t;
                    c.mut = CoreMut::Const;
                    vt = mod.Intern(c);
                }
            }
            s.var = NewVar(vd, vd->name, vt, CoreVarKind::Let, out.scope, org);
            if (f->idxdef)
                s.index = NewVar(f->idxdef, f->idxdef->name, Ty(f->idxdef->type), CoreVarKind::Let,
                                 out.scope, org);
            s.view = ToView(f->iter);
        }
        loops++;
        s.then = BlockOf(f->body, false);
        loops--;
        // The loop's variables belong to its body block.
        cur.impl->vars[s.var].scope = s.then->scope;
        if (s.index >= 0) cur.impl->vars[s.index].scope = s.then->scope;
        out.stmts.push_back(std::move(s));
    }

    void CallStmt(Call *c, CoreBlock &out) {
        if (c->spec && c->builtin < 0) return ExprStmt(c, out);
        switch (c->builtin) {
            case B_PRINT: {
                auto s = MakeStmt(CoreStmtKind::Print, c->line, CoreOriginKind::Print);
                for (auto a : c->ArgNodes()) {
                    CorePrintArg pa;
                    if (auto sl = Is<StrLit>(a)) {
                        if (!CoreIsUtf8(sl->val)) Fail("non-utf8-text", a->line);
                        pa.text = true;
                        pa.str = sl->val;
                    } else {
                        here = a->line;
                        pa.expr = Value(a);
                        auto k = mod.Type(pa.expr->type).kind;
                        if (k != CoreType::Int && k != CoreType::Bool) Fail("print-argument", a->line);
                    }
                    s.print.push_back(std::move(pa));
                }
                if (!c->fmtspecs.empty()) Fail("user-format");
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_ASSERT: {
                auto s = MakeStmt(CoreStmtKind::Assert, c->line, CoreOriginKind::Assert);
                s.expr = Value(c->ArgNodes()[0]);
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_ABORT: {
                auto s = MakeStmt(CoreStmtKind::Abort, c->line, CoreOriginKind::Abort);
                auto sl = Is<StrLit>(c->ArgNodes()[0]);
                if (!sl) Fail("abort-message");
                if (!CoreIsUtf8(sl->val)) Fail("non-utf8-text");
                s.message = sl->val;
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_EXIT: {
                auto s = MakeStmt(CoreStmtKind::Exit, c->line, CoreOriginKind::Exit);
                s.expr = Value(c->ArgNodes()[0]);
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_APPEND: {
                auto s = MakeStmt(CoreStmtKind::Append, c->line, CoreOriginKind::Expr);
                auto an = c->ArgNodes();
                s.place = OwnerPlace(an[0]);
                s.view = ToView(an[1]);
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_PUSH: {
                // The statement form keeps the reference push yields.
                auto s = MakeStmt(CoreStmtKind::Expr, c->line, CoreOriginKind::Expr);
                s.expr = PushExpr(c);
                out.stmts.push_back(std::move(s));
                return;
            }
            default: return ExprStmt(c, out);
        }
    }

    // ---------------------------------------------------------------------
    // Places and views.

    // The place a variable's storage is: a local, a global, or, for a free
    // variable, what the trailing parameter refers to.
    CorePlaceP VarPlace(VarDef *v) {
        auto p = make_unique<CorePlace>();
        if (v->isglobal) {
            auto it = globalindex.find(v);
            if (it == globalindex.end()) {
                if (auto sk = skipped.find(v); sk != skipped.end()) Fail(sk->second.feature.c_str());
                Fail("unknown-global");
            }
            p->kind = CorePlace::Global;
            p->index = it->second;
            return p;
        }
        auto it = cur.varid.find(v);
        if (it == cur.varid.end()) Fail("unknown-variable");
        if (v->ownerspec == cur.spec) {
            p->kind = CorePlace::Local;
            p->index = it->second;
            return p;
        }
        // A free variable: reached through its by-reference parameter.
        auto inner = make_unique<CorePlace>();
        inner->kind = CorePlace::Local;
        inner->index = it->second;
        auto read = NewExpr(CoreExprKind::Read, cur.impl->vars[it->second].type);
        read->place = std::move(inner);
        p->kind = CorePlace::Deref;
        p->expr = std::move(read);
        return p;
    }

    CorePlaceP DerefOf(CoreExprP ref) {
        auto p = make_unique<CorePlace>();
        p->kind = CorePlace::Deref;
        p->expr = std::move(ref);
        return p;
    }

    CoreExprP ReadOf(CorePlaceP place, CoreTypeId ty) {
        auto e = NewExpr(CoreExprKind::Read, ty);
        e->place = std::move(place);
        return e;
    }

    // The place an lvalue expression denotes. A reference variable stands for
    // its pointee unless `pointee` is false (a rebind names the variable).
    CorePlaceP ToPlace(Node *n, bool pointee) {
        here = n->line;
        if (auto id = Is<Ident>(n)) {
            auto v = id->vdef;
            if (!v) Fail("function-value");
            auto place = VarPlace(v);
            if (pointee && v->type->kind == TY_REF) {
                if (v->type->ref->optional) Fail("optional");
                auto ty = Ty(v->type);
                return DerefOf(ReadOf(std::move(place), ty));
            }
            return place;
        }
        if (auto ix = Is<Index>(n)) {
            auto p = make_unique<CorePlace>();
            p->kind = CorePlace::Elem;
            p->view = ToView(ix->obj);
            p->expr = Value(ix->idx);
            if (mod.Type(p->expr->type).kind != CoreType::Int) Fail("non-integer-index", ix->line);
            p->org = Org(ix->line, CoreOriginKind::Index);
            return p;
        }
        if (n->nkind == NK_Dot) Fail("struct");
        if (n->exprtype && n->exprtype->kind == TY_REF) return DerefOf(Value(n));
        Fail("temporary-place");
    }

    // The array a growth operation names: the receiver, through its reference.
    CorePlaceP OwnerPlace(Node *recv) {
        if (!recv->exprtype) Fail("temporary-place");
        auto vt = Pointee(recv->exprtype);
        if (!IsArrayTE(vt) || vt->arr->akind != A_GROW) Fail("growth-receiver");
        return ToPlace(recv, true);
    }

    // The sampled run of elements an array, reference to one, or slice stands
    // for.
    CoreViewP ToView(Node *obj) {
        here = obj->line;
        auto v = make_unique<CoreView>();
        TypeExpr *vt = obj->exprtype;
        if (auto id = Is<Ident>(obj); id && id->vdef) vt = id->vdef->type;
        if (!vt) Fail("temporary-slice");
        vt = Pointee(vt);
        if (vt->kind == TY_SLICE) {
            v->kind = CoreView::Val;
            // A slice variable's value, read as itself (no coercion applies).
            if (auto id = Is<Ident>(obj); id && id->vdef) {
                auto place = ToPlace(obj, true);
                v->expr = ReadOf(std::move(place), Ty(vt));
            } else {
                v->expr = ValueRaw(obj);
            }
            return v;
        }
        if (vt->kind != TY_ARRAY) Fail("view-source");
        if (Is<ArrayLit>(obj) || Is<Call>(obj)) Fail("temporary-slice");
        v->kind = CoreView::Of;
        v->place = ToPlace(obj, true);
        return v;
    }

    // ---------------------------------------------------------------------
    // Expressions.

    // The value of a node as the slot it fills wants it: a read through a
    // reference that was used as its pointee, an array sliced where a slice is
    // wanted, and an integer widened to the type the checker fitted.
    CoreExprP Value(Node *n) {
        here = n->line;
        auto e = ValueRaw(n);
        return Fit(std::move(e), n->exprtype, n);
    }

    // Widens an integer to the target the checker fitted the node to.
    CoreExprP Fit(CoreExprP e, TypeExpr *target, Node *n) {
        if (!target || target->kind != TY_INT) return e;
        auto &t = mod.Type(e->type);
        if (t.kind != CoreType::Int) return e;
        auto want = IntTy(target->intstorage);
        if (t.ity == want) return e;
        return Convert(std::move(e), want, n->line);
    }

    // Whether converting to a type can never change the value: to a wider type
    // of the same signedness, or from an unsigned type to a strictly wider
    // signed one.
    static bool IsWidening(CoreIntTy from, CoreIntTy to) {
        if (CoreIntBits(from) >= CoreIntBits(to)) return false;
        return CoreIsUnsigned(to) ? CoreIsUnsigned(from) : true;
    }

    // The implicit conversion of an integer to another integer type. Where the
    // checker fitted a value it knows to be non-negative to an unsigned type
    // (a comparison with a u64) the conversion is not a widening, and `as`
    // says so.
    CoreExprP Convert(CoreExprP e, CoreIntTy want, Line at) {
        auto from = mod.Type(e->type).ity;
        auto c = NewExpr(CoreExprKind::Conv, mod.IntType(want));
        c->conv = IsWidening(from, want) ? CoreConvKind::Widen : CoreConvKind::As;
        c->a = std::move(e);
        c->org = Org(at, CoreOriginKind::Cast);
        return c;
    }

    CoreExprP PushExpr(Call *c) {
        auto an = c->ArgNodes();
        if (an.size() != 2) Fail("push-arity");
        auto e = NewExpr(CoreExprKind::Push, 0);
        e->place = OwnerPlace(an[0]);
        auto vt = Pointee(an[0]->exprtype);
        auto elem = Ty(vt->arr->sub);
        e->a = Value(an[1]);
        CoreType rt;
        rt.kind = CoreType::Ref;
        rt.elem = elem;
        e->type = mod.Intern(rt);
        return e;
    }

    CoreExprP ValueRaw(Node *n) {
        here = n->line;
        switch (n->nkind) {
            case NK_IntLit: {
                auto l = (IntLit *)n;
                if (!n->exprtype || n->exprtype->kind != TY_INT) {
                    if (n->exprtype) (void)Ty(n->exprtype);
                    Fail("literal-type");
                }
                auto ty = Ty(n->exprtype);
                if (l->uns || l->val >= 0) return IntLiteral(ty, false, (uint64_t)l->val);
                return IntLiteral(ty, true, 0 - (uint64_t)l->val);
            }
            case NK_BoolLit: {
                auto e = NewExpr(CoreExprKind::Bool, mod.BoolType());
                e->flag = ((BoolLit *)n)->val;
                return e;
            }
            case NK_StrLit: Fail("string-value");
            case NK_FltLit: Fail("float");
            case NK_Ident: return IdentValue((Ident *)n);
            case NK_ArrayLit: return ArrayValue((ArrayLit *)n);
            case NK_Unary: return UnaryValue((Unary *)n);
            case NK_Binary: return BinaryValue((Binary *)n);
            case NK_Dot: return DotValue((Dot *)n);
            case NK_Call: return CallValue((Call *)n);
            case NK_Index: {
                auto ix = (Index *)n;
                auto place = ToPlace(ix, true);
                auto vt = IndexedType(ix);
                return ReadOf(std::move(place), Ty(vt));
            }
            case NK_SliceExpr: return SliceValue((SliceExpr *)n);
            case NK_AsCast: {
                auto a = (AsCast *)n;
                if (!a->totype) Fail("cast-target");
                auto e = NewExpr(CoreExprKind::Conv, Ty(a->totype));
                e->conv = a->unchecked ? CoreConvKind::AsUnchecked : CoreConvKind::As;
                e->a = Value(a->child);
                if (mod.Type(e->a->type).kind != CoreType::Int || mod.Type(e->type).kind != CoreType::Int)
                    Fail("non-integer-cast");
                e->org = Org(n->line, CoreOriginKind::Cast);
                return e;
            }
            case NK_IfExpr: {
                auto x = (IfExpr *)n;
                auto e = NewExpr(CoreExprKind::If, Ty(x->exprtype));
                e->a = Value(x->cond);
                ExprBlockScope inexpr(*this);
                e->then = BlockOf(x->thenb, true);
                if (!x->elseb) Fail("diverging-branch");
                if (auto eb = Is<Block>(x->elseb)) e->otherwise = BlockOf(eb, true);
                else {
                    e->otherwise = make_unique<CoreBlock>();
                    e->otherwise->scope = cur.nextscope++;
                    e->otherwise->value = Value(x->elseb);
                }
                return e;
            }
            case NK_Block: {
                auto b = (Block *)n;
                auto e = NewExpr(CoreExprKind::Block, Ty(b->exprtype ? b->exprtype : ast.voidtype));
                ExprBlockScope inexpr(*this);
                e->then = BlockOf(b, b->exprtype && b->exprtype->kind != TY_VOID);
                return e;
            }
            case NK_StructLit: Fail("struct");
            case NK_NullLit: Fail("optional");
            case NK_MatchExpr: Fail("match");
            case NK_LoopExpr: Fail("loop-expression");
            case NK_EarlyBlock: Fail("early-block");
            case NK_FunVal: Fail("function-value");
            default: Fail("expression");
        }
    }

    // The type of the element an index expression reads, as the container
    // holds it.
    TypeExpr *IndexedType(Index *ix) {
        TypeExpr *vt = ix->obj->exprtype;
        if (auto id = Is<Ident>(ix->obj); id && id->vdef) vt = id->vdef->type;
        if (!vt) Fail("view-source");
        vt = Pointee(vt);
        if (vt->kind == TY_SLICE) return vt->sub;
        if (vt->kind == TY_ARRAY) return vt->arr->sub;
        Fail("view-source");
    }

    CoreExprP IdentValue(Ident *id) {
        auto v = id->vdef;
        if (!v) Fail("function-value");
        auto vt = v->type;
        auto want = id->exprtype;
        if (vt->kind == TY_REF) {
            if (vt->ref->optional) Fail("optional");
            if (want && want->kind == TY_REF) {
                // The reference itself.
                auto place = VarPlace(v);
                return ReadOf(std::move(place), Ty(vt));
            }
        }
        auto inner = Pointee(vt);
        // An array where the checker fitted a slice: slice it whole.
        if (want && want->kind == TY_SLICE && IsArrayTE(inner)) {
            auto e = NewExpr(CoreExprKind::Slice, Ty(want));
            e->mut = MutOf(want);
            e->view = ToView(id);
            e->org = coerceorg;
            return e;
        }
        auto place = ToPlace(id, true);
        return ReadOf(std::move(place), Ty(inner));
    }

    CoreExprP ArrayValue(ArrayLit *a) {
        if (a->capexpr) Fail("limited-array");
        auto t = a->exprtype;
        if (!t) Fail("temporary-slice");
        if (t->kind == TY_SLICE) Fail("temporary-slice");
        if (t->kind != TY_ARRAY) Fail("array-literal-type");
        auto ty = Ty(t);
        auto &ct = mod.Type(ty);
        if (a->fillval) {
            if (ct.kind != CoreType::Arr) Fail("fill-grow");
            auto e = NewExpr(CoreExprKind::Fill, ty);
            e->a = Value(a->fillval);
            return e;
        }
        auto e = NewExpr(CoreExprKind::Arr, ty);
        for (auto el : a->elems) e->elems.push_back(Value(el));
        return e;
    }

    CoreExprP UnaryValue(Unary *u) {
        switch (u->op) {
            case T_BITAND: {
                auto e = NewExpr(CoreExprKind::Ref, Ty(u->exprtype));
                e->mut = MutOf(u->exprtype);
                e->place = ToPlace(u->child, true);
                return e;
            }
            case T_NOT: {
                auto e = NewExpr(CoreExprKind::Not, mod.BoolType());
                e->a = Value(u->child);
                return e;
            }
            case T_MINUS: {
                // A negated literal is one constant: the most negative value
                // of a type has no positive literal to negate.
                if (auto lit = Is<IntLit>(u->child); lit && u->exprtype && u->exprtype->kind == TY_INT) {
                    auto ty = Ty(u->exprtype);
                    return IntLiteral(ty, true, (uint64_t)lit->val);
                }
                auto e = NewExpr(CoreExprKind::Un, 0);
                e->un = CoreUnOp::Neg;
                e->a = Value(u->child);
                e->type = e->a->type;
                if (mod.Type(e->type).kind != CoreType::Int) Fail("non-integer-negation");
                e->org = Org(u->line, CoreOriginKind::Unary);
                return e;
            }
            case T_BITNOT: {
                auto e = NewExpr(CoreExprKind::Un, 0);
                e->un = CoreUnOp::BitNot;
                e->a = Value(u->child);
                e->type = e->a->type;
                if (mod.Type(e->type).kind != CoreType::Int) Fail("non-integer-complement");
                e->org = Org(u->line, CoreOriginKind::Unary);
                return e;
            }
            default: Fail("unary-operator");
        }
    }

    CoreExprP BinaryValue(Binary *b) {
        switch (b->op) {
            case T_ANDAND: case T_OROR: {
                auto e = NewExpr(b->op == T_ANDAND ? CoreExprKind::And : CoreExprKind::Or,
                                 mod.BoolType());
                e->a = Value(b->left);
                e->b = Value(b->right);
                return e;
            }
            case T_EQ: case T_NEQ: case T_LT: case T_GT: case T_LTEQ: case T_GTEQ: {
                auto e = NewExpr(CoreExprKind::Cmp, mod.BoolType());
                switch (b->op) {
                    case T_EQ: e->cmp = CoreCmpOp::Eq; break;
                    case T_NEQ: e->cmp = CoreCmpOp::Ne; break;
                    case T_LT: e->cmp = CoreCmpOp::Lt; break;
                    case T_GT: e->cmp = CoreCmpOp::Gt; break;
                    case T_LTEQ: e->cmp = CoreCmpOp::Le; break;
                    default: e->cmp = CoreCmpOp::Ge; break;
                }
                e->a = Value(b->left);
                e->b = Value(b->right);
                auto k = mod.Type(e->a->type).kind;
                if (k != CoreType::Int && k != CoreType::Bool) Fail("elementwise-arithmetic");
                return e;
            }
            default: break;
        }
        CoreBinOp op;
        switch (b->op) {
            case T_PLUS: op = CoreBinOp::Add; break;
            case T_MINUS: op = CoreBinOp::Sub; break;
            case T_MUL: op = CoreBinOp::Mul; break;
            case T_DIV: op = CoreBinOp::Div; break;
            case T_MOD: op = CoreBinOp::Mod; break;
            case T_BITAND: op = CoreBinOp::BitAnd; break;
            case T_BITOR: op = CoreBinOp::BitOr; break;
            case T_XOR: op = CoreBinOp::BitXor; break;
            case T_SHL: op = CoreBinOp::Shl; break;
            case T_SHR: op = CoreBinOp::Shr; break;
            default: Fail("binary-operator");
        }
        auto e = NewExpr(CoreExprKind::Bin, 0);
        e->bin = op;
        e->a = Value(b->left);
        e->b = Value(b->right);
        e->type = e->a->type;
        // A shift count may have any integer type. It is masked to the width
        // of the left operand, which keeps only its low bits, so truncating it
        // to that type changes nothing and gives both operands one type.
        if ((op == CoreBinOp::Shl || op == CoreBinOp::Shr) && mod.Type(e->type).kind == CoreType::Int &&
            mod.Type(e->b->type).kind == CoreType::Int && e->b->type != e->type) {
            auto c = NewExpr(CoreExprKind::Conv, e->type);
            c->conv = CoreConvKind::AsUnchecked;
            c->a = std::move(e->b);
            c->org = Org(b->right->line, CoreOriginKind::Cast);
            e->b = std::move(c);
        }
        if (mod.Type(e->type).kind != CoreType::Int) Fail("elementwise-arithmetic");
        e->org = Org(b->line, CoreOriginKind::Binary);
        return e;
    }

    CoreExprP DotValue(Dot *d) {
        if (d->member == B_LEN) {
            auto e = NewExpr(CoreExprKind::Len, mod.IntType(CoreIntTy::I64));
            e->view = ToView(d->obj);
            return e;
        }
        if (d->member >= 0) Fail("builtin-property");
        Fail("struct");
    }

    CoreExprP SliceValue(SliceExpr *s) {
        auto e = NewExpr(CoreExprKind::Slice, Ty(s->exprtype));
        e->mut = MutOf(s->exprtype);
        e->view = ToView(s->obj);
        auto bound = [&](Node *n, bool fromend, CoreBound &out) {
            if (!n) return;
            out.kind = fromend ? CoreBound::End : CoreBound::Expr;
            out.expr = Value(n);
            if (mod.Type(out.expr->type).kind != CoreType::Int) Fail("non-integer-bound");
        };
        bound(s->lo, s->lo_from_end, e->lo);
        bound(s->hi, s->hi_from_end, e->hi);
        e->org = Org(s->line, CoreOriginKind::Slice);
        return e;
    }

    // The place of a call argument bound to a by-reference parameter.
    CorePlaceP ArgPlace(Node *a) {
        if (auto u = Is<Unary>(a); u && u->op == T_BITAND) return ToPlace(u->child, true);
        if (a->exprtype && a->exprtype->kind == TY_REF) return DerefOf(Value(a));
        Fail("temporary-place");
    }

    CoreExprP CallValue(Call *c) {
        if (c->builtin >= 0 && !c->spec) return BuiltinValue(c);
        if (!c->spec) {
            if (!c->dispatch.empty()) Fail("adt");
            Fail("function-value");
        }
        if (c->spec->isfunval || c->fvbody || c->trailing) Fail("function-value");
        if (!c->dispatch.empty()) Fail("adt");
        if (!c->fmtspecs.empty()) Fail("user-format");
        if (!cur.spec) Fail("global-initializer-call");
        auto callee = c->spec;
        auto &rets = callee->rets;
        if (rets.size() > 1) Fail("multiple-results");
        auto e = NewExpr(CoreExprKind::Call, rets.empty() ? mod.UnitType() : Ty(rets[0]));
        auto savedorg = coerceorg;
        coerceorg = Org(c->line, CoreOriginKind::Call);
        auto an = c->ArgNodes();
        if (an.size() != callee->params.size()) Fail("call-arity");
        for (size_t i = 0; i < an.size(); i++) {
            here = an[i]->line;
            auto pt = callee->argtypes[i];
            CoreArg arg;
            if (pt->kind == TY_REF) {
                arg.kind = CoreArg::Ref;
                arg.mut = MutOf(pt);
                arg.place = ArgPlace(an[i]);
            } else {
                arg.kind = CoreArg::Val;
                arg.expr = Value(an[i]);
            }
            e->args.push_back(std::move(arg));
        }
        // The callee's free variables follow, as references to this
        // activation's variables of the same name.
        for (auto fv : freevars[callee]) {
            CoreArg arg;
            arg.kind = CoreArg::Ref;
            arg.mut = fv->isvar ? CoreMut::Mut : CoreMut::Const;
            arg.place = VarPlace(fv);
            e->args.push_back(std::move(arg));
        }
        coerceorg = savedorg;
        // The callee's number is taken once its arguments, which may call too,
        // have been met: calls are numbered in the order they run.
        e->ctx = ContextOf(callee);
        e->org = Org(c->line, CoreOriginKind::Call);
        return e;
    }

    CoreExprP BuiltinValue(Call *c) {
        switch (c->builtin) {
            case B_PUSH: {
                auto e = PushExpr(c);
                // A value-typed use reads the new element through the reference.
                if (c->exprtype && c->exprtype->kind != TY_REF) {
                    auto elem = mod.Type(e->type).elem;
                    return ReadOf(DerefOf(std::move(e)), elem);
                }
                return e;
            }
            case B_PRINT: case B_ASSERT: case B_ABORT: case B_EXIT: case B_APPEND:
                Fail("statement-as-value");
            case B_STR: case B_FORMAT: Fail("string-value");
            case B_COPY: Fail("copy");
            case B_POP: case B_POP_N: case B_RESIZE: case B_CLEAR: Fail("shrink-operation");
            case B_ALLOC_INDEX: case B_ALLOC_REF: case B_FREE: case B_ALLOC_SLICE:
            case B_REALLOC_SLICE: case B_FREE_SLICE:
                Fail("reusable");
            case B_THREAD_SPAWN: case B_THREAD_WAIT: case B_QPUT: case B_QGET: case B_QPOLL:
            case B_HARDWARE_THREADS:
                Fail("thread");
            case B_TO_BYTES: case B_BYTES_OF: case B_FROM_BYTES: Fail("serialization");
            // A declaration with only a type gets its type's default value
            // from the checker.
            case B_DEFAULT: Fail(c->implicit ? "uninitialized-declaration" : "default-value");
            case B_LEN: case B_CAP: case B_INDEX_OF: Fail("builtin-call");
            default: Fail("builtin-call");
        }
    }

    // ---------------------------------------------------------------------
    // Root annotations of a context.

    // The roots of one checked reference or slice, in the terms of this
    // implementation: its own variables, the globals, and its parameters.
    vector<CoreRootRef> RootsOf(const Roots &r, FnSpec *sp, vector<VarDef *> &globalclasses) {
        vector<CoreRootRef> out;
        for (auto &alt : r.alts) {
            auto v = alt.root;
            if (!v) continue;   // Static data.
            if (v->istemp) Fail("temporary-slice", sp->sf->line);
            if (v->isglobal) {
                auto it = globalindex.find(v);
                if (it == globalindex.end()) Fail("unknown-global", sp->sf->line);
                out.push_back({ CoreRootRef::Global, it->second });
                continue;
            }
            if (v->ownerspec == sp) {
                auto it = cur.varid.find(v);
                if (it == cur.varid.end()) Fail("unknown-variable", sp->sf->line);
                out.push_back({ CoreRootRef::Local, it->second });
                continue;
            }
            if (v->ownerspec) {
                // A variable of an enclosing activation: its trailing parameter.
                auto it = cur.varid.find(v);
                if (it == cur.varid.end()) Fail("unknown-variable", sp->sf->line);
                out.push_back({ CoreRootRef::Param, it->second });
                continue;
            }
            // The root a parameter's class stands for at the call: a global
            // where the class sits at the globals' depth, else whatever the
            // caller passed for any parameter of the class.
            if (v->depth == 0 && v->classfrom && v->classfrom->isglobal) {
                auto it = globalindex.find(v->classfrom);
                if (it == globalindex.end()) Fail("unknown-global", sp->sf->line);
                out.push_back({ CoreRootRef::Global, it->second });
                globalclasses.push_back(v);
                continue;
            }
            auto before = out.size();
            for (size_t i = 0; i < sp->params.size(); i++)
                for (auto &pa : sp->params[i]->ref.alts)
                    if (pa.root == v) { out.push_back({ CoreRootRef::Param, (int)i }); break; }
            if (out.size() == before) Fail("unknown-root", sp->sf->line);
        }
        sort(out.begin(), out.end());
        out.erase(unique(out.begin(), out.end()), out.end());
        return out;
    }

    void FillRoots(FnSpec *sp, CoreContext &ctx) {
        auto &impl = *cur.impl;
        auto k = (int)mod.contexts.size() - 1;
        for (size_t i = 0; i < impl.vars.size(); i++) {
            if (!mod.IsRefOrSlice(impl.vars[i].type)) continue;
            vector<CoreRootRef> roots;
            vector<VarDef *> classes;
            if (auto vd = cur.vardefs[i]) {
                if (vd->refrootknown) roots = RootsOf(vd->ref, sp, classes);
            } else {
                roots.push_back({ CoreRootRef::Param, (int)i });
            }
            for (auto c : classes) globalclasses.push_back({ k, false, (int)ctx.varroots.size(), c });
            ctx.varroots.push_back({ (int)i, std::move(roots) });
        }
        for (size_t i = 0; i < impl.results.size(); i++) {
            vector<CoreRootRef> roots;
            vector<VarDef *> classes;
            if (mod.IsRefOrSlice(impl.results[i]) && i < sp->record.retroots.size())
                roots = RootsOf(sp->record.retroots[i].alts, sp, classes);
            for (auto c : classes) globalclasses.push_back({ k, true, (int)i, c });
            ctx.resultroots.push_back(std::move(roots));
        }
    }

    // ---------------------------------------------------------------------
    // Parameter classes at the globals' depth.
    //
    // A specialization is shared by every call whose arguments sit at the
    // globals' depth, whichever global each names, so the root of such a
    // parameter is not one global but every global some call passes. The
    // first call's global is recorded as the root where the class is met;
    // this adds the others, which only the callers' bodies show.

    struct GlobalClassUse {
        int ctx;
        bool result;
        int index;         // Position in the context's varroots or resultroots.
        VarDef *cls;
    };
    vector<GlobalClassUse> globalclasses;

    using RootSet = set<CoreRootRef>;

    const vector<CoreRootRef> *VarRoots(int k, int var) {
        for (auto &vr : mod.contexts[k].varroots)
            if (vr.first == var) return &vr.second;
        return nullptr;
    }

    RootSet PlaceRoots(const CorePlace &p, int k) {
        switch (p.kind) {
            case CorePlace::Local: return { CoreRootRef { CoreRootRef::Local, p.index } };
            case CorePlace::Global: return { CoreRootRef { CoreRootRef::Global, p.index } };
            case CorePlace::Deref: return ExprRoots(*p.expr, k);
            case CorePlace::Elem: return ViewRoots(*p.view, k);
        }
        return {};
    }

    RootSet ViewRoots(const CoreView &v, int k) {
        return v.kind == CoreView::Of ? PlaceRoots(*v.place, k) : ExprRoots(*v.expr, k);
    }

    RootSet ArgRoots(const CoreArg &a, int k) {
        if (a.kind == CoreArg::Ref) return PlaceRoots(*a.place, k);
        return mod.IsRefOrSlice(a.expr->type) ? ExprRoots(*a.expr, k) : RootSet {};
    }

    // The roots of a reference- or slice-typed expression in context k.
    RootSet ExprRoots(const CoreExpr &e, int k) {
        RootSet out;
        switch (e.kind) {
            case CoreExprKind::Read:
                if (e.place->kind == CorePlace::Local)
                    if (auto r = VarRoots(k, e.place->index)) out.insert(r->begin(), r->end());
                break;
            case CoreExprKind::Ref: case CoreExprKind::Push: out = PlaceRoots(*e.place, k); break;
            case CoreExprKind::Slice: out = ViewRoots(*e.view, k); break;
            case CoreExprKind::Call: {
                auto &res = mod.contexts[e.ctx].resultroots;
                if (res.empty()) break;
                for (auto &r : res[0]) {
                    if (r.kind == CoreRootRef::Param) {
                        auto a = ArgRoots(e.args[r.index], k);
                        out.insert(a.begin(), a.end());
                    } else if (r.kind == CoreRootRef::Global) out.insert(r);
                }
                break;
            }
            case CoreExprKind::If: case CoreExprKind::Block: {
                for (auto b : { e.then.get(), e.otherwise.get() })
                    if (b && b->value) {
                        auto a = ExprRoots(*b->value, k);
                        out.insert(a.begin(), a.end());
                    }
                break;
            }
            default: break;
        }
        return out;
    }

    void ExpandGlobalClasses() {
        if (globalclasses.empty()) return;
        // The globals each class is passed, by use.
        for (auto changed = true; changed;) {
            changed = false;
            for (size_t k = 0; k < mod.impls.size(); k++) {
                CoreVisitExprs(mod.impls[k].body, [&](const CoreExpr &e) {
                    if (e.kind != CoreExprKind::Call) return;
                    for (auto &use : globalclasses) {
                        if (use.ctx != e.ctx) continue;
                        auto sp = ctxspecs[use.ctx];
                        auto &list = use.result ? mod.contexts[use.ctx].resultroots[use.index]
                                                : mod.contexts[use.ctx].varroots[use.index].second;
                        for (size_t i = 0; i < sp->params.size(); i++) {
                            auto member = false;
                            for (auto &pa : sp->params[i]->ref.alts) member |= pa.root == use.cls;
                            if (!member) continue;
                            for (auto &r : ArgRoots(e.args[i], (int)k)) {
                                if (r.kind != CoreRootRef::Global) continue;
                                if (find(list.begin(), list.end(), r) == list.end()) {
                                    list.push_back(r);
                                    changed = true;
                                }
                            }
                        }
                        sort(list.begin(), list.end());
                    }
                });
            }
        }
    }
};

}  // namespace goose
