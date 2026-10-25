#pragma once

namespace goose {

struct CoreUnsupported {
    string feature;
    Line at;
};

enum class CoreExportMode { Module, Report };

class CoreExporter {
public:
    CoreExporter(Ast &a, const string &entry, CoreExportMode mode = CoreExportMode::Module)
        : ast(a), entrypath(entry), entrydir(filesystem::path(entry).parent_path().generic_string()),
          reportonly(mode == CoreExportMode::Report) {}

    CoreModule Export() {
        auto mainsf = ast.MainFunction();
        if (!mainsf || mainsf->specs.empty()) {
            ReportOrFail("no-entry", Line {});
            return std::move(mod);
        }
        auto mainspec = mainsf->specs[0];
        if (!mainspec->params.empty() || !mainspec->rets.empty())
            ReportOrFail("entry-signature", mainsf->line);
        // The entry is context 0. The calls a global's initializer makes come
        // next, since they run first; building an implementation may add more.
        ContextOf(mainspec);
        ExportGlobals();
        FindReachable(ctxspecs);
        auto implementationscomplete = true;
        for (size_t k = 0; k < ctxspecs.size(); k++) {
            // Reachability records extern functions as unsupported, but they
            // have no body to build. Keep the remaining contexts reportable.
            if (reportonly && !ctxspecs[k]->body) {
                implementationscomplete = false;
                continue;
            }
            try {
                BuildImpl((int)k);
            } catch (CoreUnsupported &u) {
                if (!reportonly) throw;
                implementationscomplete = false;
                Remember(u);
                ProbeBody(ctxspecs[k]->body);
            }
        }
        if (reportonly) {
            if (implementationscomplete) {
                try {
                    ExpandGlobalClasses();
                    ComputeContentRoots();
                } catch (CoreUnsupported &u) {
                    Remember(u);
                }
            }
            return std::move(mod);
        }
        ExpandGlobalClasses();
        ComputeContentRoots();
        mod.entry = 0;
        return std::move(mod);
    }

    vector<string> UnsupportedFeatures() const {
        return vector<string>(unsupported.begin(), unsupported.end());
    }

private:
    Ast &ast;
    KeyMaker keys { ast };
    string entrypath;
    string entrydir;
    CoreModule mod;
    bool reportonly;
    bool exportingstdlibglobal = false;
    set<string> unsupported;

    unordered_map<const VarDef *, int> globalindex;
    unordered_map<const VarDef *, CoreUnsupported> skipped;   // Library globals left out, and why.
    unordered_map<int, int> filemap;            // AST file index -> module file index
    unordered_map<const StructInst *, int> structid;

    vector<FnSpec *> ctxspecs;
    vector<vector<CoreRequest>> ctxrequests;
    unordered_map<const FnSpec *, map<vector<CoreRequest>, int>> ctxvariants;
    map<vector<CoreImplId>, CoreTargetId> targetsetid;

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
        vector<CoreRequest> requests;
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

    void Remember(const CoreUnsupported &u) {
        // These names identify damage caused by a statement omitted after an
        // earlier unsupported construct. A checked AST cannot contain them as
        // independent source features.
        if (u.feature == "unknown-variable" || u.feature == "unknown-global" ||
            u.feature == "unknown-root") return;
        unsupported.insert(u.feature);
    }

    void ReportOrFail(const char *feature, Line at) {
        if (!reportonly) Fail(feature, at);
        Remember(CoreUnsupported { feature, at });
    }

    void ProbeChildren(Node *n) {
        if (!n) return;
        CoreBlock ignored;
        auto probe = [&](Node *child) { Stmt(child, ignored); };
        if (auto b = Is<Block>(n)) {
            for (auto s : b->stmts) probe(s);
            if (b->tail) probe(b->tail);
            return;
        }
        if (auto c = Is<Call>(n)) {
            if (c->builtin < 0 && c->spec) ContextOf(c->spec);
            for (auto a : c->args) probe(a);
            if (c->fvbody) probe(c->fvbody);
            if (c->defaultinit) probe(c->defaultinit);
            return;
        }
        RunChildren(n, probe);
    }

    void ProbeBody(Block *b) {
        if (!b) return;
        for (auto s : b->stmts) {
            CoreBlock ignored;
            Stmt(s, ignored);
        }
        if (b->tail) {
            try {
                (void)Value(b->tail);
            } catch (CoreUnsupported &u) {
                Remember(u);
                ProbeChildren(b->tail);
            }
        }
    }

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
            // A runtime diagnostic names the file as the compiler was given it.
            auto diag = l.fileidx >= 0 && l.fileidx < (int)ast.sources.size()
                            ? ast.sources[l.fileidx].first : string("?");
            for (auto &c : diag) if (c == '\\') c = '/';
            mod.diagfiles.push_back(diag);
            mod.filemodules.push_back(keys.ModuleOf(l.fileidx));
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

    bool FlatCoreType(CoreTypeId type) const {
        auto &t = mod.Type(type);
        switch (t.kind) {
            case CoreType::Int: case CoreType::Bool: case CoreType::Struct:
                return true;
            case CoreType::Arr:
                return t.count > 0 && FlatCoreType(t.elem);
            default:
                return false;
        }
    }

    bool VariableElementType(CoreTypeId type) const {
        auto &t = mod.Type(type);
        switch (t.kind) {
            case CoreType::Arr:
                return VariableElementType(t.elem);
            case CoreType::VarArr:
                return FlatCoreType(t.elem) || VariableElementType(t.elem);
            default:
                return false;
        }
    }

    bool NonfixedValueType(CoreTypeId type) const {
        auto &t = mod.Type(type);
        return t.kind == CoreType::VarArr || t.kind == CoreType::Grow ||
               t.kind == CoreType::GrowShrink ||
               (t.kind == CoreType::Arr && VariableElementType(type));
    }

    CoreTypeId CallResultType(FnSpec *spec) {
        if (spec->rets.empty()) return mod.UnitType();
        if (spec->rets.size() == 1) return ResultTy(spec, 0);
        CoreType type;
        type.kind = CoreType::Tuple;
        for (size_t i = 0; i < spec->rets.size(); i++) type.parts.push_back(ResultTy(spec, i));
        return mod.Intern(type);
    }

    bool HasNonfixedResult(FnSpec *spec) {
        for (size_t i = 0; i < spec->rets.size(); i++)
            if (NonfixedValueType(ResultTy(spec, i))) return true;
        return false;
    }

    CoreExprP ReturnValue(Node *value, FnSpec *target, size_t index, bool allowLocal) {
        auto type = ResultTy(target, index);
        if (allowLocal && NonfixedValueType(type)) {
            if (auto id = Is<Ident>(value); id && id->vdef) {
                auto found = cur.varid.find(id->vdef);
                if (found != cur.varid.end() && NonfixedValueType(cur.impl->vars[found->second].type) &&
                    found->second >= (int)cur.impl->params.size()) {
                    auto e = NewExpr(CoreExprKind::ResultLocal, type);
                    e->var = found->second;
                    e->org = Org(value->line, CoreOriginKind::Return);
                    return e;
                }
            }
        }
        if (auto call = Is<Call>(value); call && call->spec && call->spec->rets.size() == 1) {
            auto requests = DefaultRequests(call->spec);
            if (target == cur.spec && index < cur.requests.size()) requests[0] = cur.requests[index];
            else {
                auto targetrequests = TargetContext(target).second;
                if (index < targetrequests.size()) requests[0] = targetrequests[index];
            }
            return ReborrowTo(CallValue(call, false, std::move(requests)), type);
        }
        return ReborrowTo(Value(value), type);
    }

    CoreTypeId ElementTy(TypeExpr *t) {
        auto id = Ty(t);
        switch (mod.Type(id).kind) {
            case CoreType::Int: case CoreType::Bool: case CoreType::Struct: return id;
            case CoreType::Ref: case CoreType::Slice: Fail("stored-reference");
            default: break;
        }
        if (FlatCoreType(id)) return id;
        if (CoreHasConstruction(mod.profile) && VariableElementType(id)) return id;
        Fail("variable-element");
    }

    CoreTypeId OwnerElementTy(TypeExpr *t, bool allowVariable = false) {
        unordered_set<const StructInst *> open;
        if (!t || t->cq) Fail("nonflat-element", t ? t->line : here);
        auto id = Ty(t);
        if (FlatCoreType(id)) return id;
        if (allowVariable && CoreHasConstruction(mod.profile) && VariableElementType(id)) return id;
        if (!FlatFixedField(t, open)) Fail("nonflat-element", t->line);
        return id;
    }

    bool FlatFixedField(TypeExpr *t, unordered_set<const StructInst *> &open) {
        if (!t) return false;
        switch (t->kind) {
            case TY_INT: return t->intstorage != IS_VARINT;
            case TY_BOOL: return true;
            case TY_ARRAY:
                return t->arr->akind == A_FIXED && t->arr->size > 0 && t->arr->sub &&
                       !t->arr->sub->cq && FlatFixedField(t->arr->sub, open);
            case TY_STRUCT: {
                auto inst = t->struc ? t->struc->inst : nullptr;
                if (!inst || !inst->validated || !inst->flat || inst->sclass != SC_FIXED || !inst->st ||
                    inst->ftypes.size() != inst->st->fields.size() || !open.insert(inst).second)
                    return false;
                auto flat = true;
                for (size_t i = 0; i < inst->st->fields.size(); i++)
                    if (!inst->st->fields[i].ispad) flat &= FlatFixedField(inst->ftypes[i], open);
                open.erase(inst);
                return flat;
            }
            default: return false;
        }
    }

    string AggregateBoundary(TypeExpr *t, unordered_set<const StructInst *> &seen) {
        if (!t) return "";
        if (t->kind == TY_ARRAY) {
            switch (t->arr->akind) {
                case A_GROW: case A_GROWSHRINK: return "resizable-field";
                case A_LIMITED: return "limited-value";
                case A_FIXED: return AggregateBoundary(t->arr->sub, seen);
                case A_VAR: return "resizable-field";
            }
        }
        if (t->kind != TY_STRUCT || !t->struc || !t->struc->inst) return "";
        auto inst = t->struc->inst;
        if (!seen.insert(inst).second || !inst->st || inst->ftypes.size() != inst->st->fields.size()) return "";
        for (size_t i = 0; i < inst->st->fields.size(); i++) {
            if (inst->st->fields[i].ispad) continue;
            auto why = AggregateBoundary(inst->ftypes[i], seen);
            if (!why.empty()) { seen.erase(inst); return why; }
        }
        seen.erase(inst);
        return "";
    }

    int64_t FlatFieldSize(TypeExpr *t) {
        if (t->kind == TY_INT) {
            if (t->intstorage == IS_VARINT) Fail("varint");
            return IntBits(t->intstorage) / 8;
        }
        if (t->kind == TY_BOOL) return 1;
        if (t->kind == TY_ARRAY) {
            if (t->arr->akind != A_FIXED || t->arr->size <= 0) Fail("struct");
            auto element = FlatFieldSize(t->arr->sub);
            if (t->arr->size > INT64_MAX / element) Fail("array-size");
            return t->arr->size * element;
        }
        if (t->kind == TY_STRUCT) {
            auto inst = t->struc ? t->struc->inst : nullptr;
            if (!inst || !inst->st || inst->ftypes.size() != inst->st->fields.size()) Fail("struct");
            auto layout = PackedFieldLayout(inst->st->fields, inst->ftypes,
                                            [&](TypeExpr *field) { return FlatFieldSize(field); },
                                            [&](TypeExpr *field) { return PackedPadAlign(field); });
            if (layout.size <= 0) Fail("zero-size-value");
            return layout.size;
        }
        Fail("struct");
    }

    CoreTypeId FieldType(TypeExpr *t) {
        if (!t) Fail("struct");
        CoreType ct;
        switch (t->kind) {
            case TY_INT:
                ct.kind = CoreType::Int;
                ct.ity = IntTy(t->intstorage);
                return mod.Intern(ct);
            case TY_BOOL: return mod.BoolType();
            case TY_ARRAY:
                if (t->arr->akind != A_FIXED || t->arr->size <= 0) Fail("struct");
                ct.kind = CoreType::Arr;
                ct.count = t->arr->size;
                ct.elem = FieldType(t->arr->sub);
                return mod.Intern(ct);
            case TY_STRUCT:
                ct.kind = CoreType::Struct;
                ct.structid = StructIdFor(t, true);
                return mod.Intern(ct);
            default: Fail("struct");
        }
    }

    int StructIdFor(TypeExpr *t, bool fieldtype = false) {
        if (t->cq && !fieldtype) Fail("struct-whole-const", t->line);
        if (!t->struc) Fail("struct", t->line);
        auto inst = t->struc->inst;
        unordered_set<const StructInst *> seen;
        if (auto why = AggregateBoundary(t, seen); !why.empty()) Fail(why.c_str(), t->line);
        if (!inst || !inst->validated || !inst->flat || inst->sclass != SC_FIXED)
            Fail("struct", t->line);
        if (auto it = structid.find(inst); it != structid.end()) return it->second;
        if (!inst->st || inst->ftypes.size() != inst->st->fields.size()) Fail("struct", t->line);

        unordered_set<const StructInst *> open;
        if (!FlatFixedField(t, open)) Fail("struct", t->line);

        auto layout = PackedFieldLayout(inst->st->fields, inst->ftypes,
                                        [&](TypeExpr *field) { return FlatFieldSize(field); },
                                        [&](TypeExpr *field) { return PackedPadAlign(field); });
        if (layout.size <= 0) Fail("zero-size-value", t->line);

        // Reserve nominal identity before visiting components, so nested
        // structs keep first-mention ids while the type table remains
        // component-before-parent.
        auto id = (int)mod.structs.size();
        structid.emplace(inst, id);
        mod.profile = CoreWithShrink(mod.profile);
        mod.structs.push_back(CoreStruct { layout.size, {} });
        CoreStruct descriptor;
        descriptor.size = layout.size;
        auto displaytype = *t;
        displaytype.cq = false;
        displaytype.Dump(descriptor.displayName);
        for (size_t i = 0; i < inst->st->fields.size(); i++) {
            auto &field = inst->st->fields[i];
            if (field.ispad) continue;
            auto *fieldtype = inst->ftypes[i];
            descriptor.fields.push_back({ FieldType(fieldtype),
                                          field.isconst ? CoreVarKind::Let : CoreVarKind::Var,
                                          MutOf(fieldtype), layout.offs[i] });
        }
        mod.structs[id] = std::move(descriptor);
        return id;
    }

    CoreTypeId ReportTypeFallback(TypeExpr *t) {
        if (t && t->kind == TY_BOOL) return mod.BoolType();
        if (t && t->kind == TY_VOID) return mod.UnitType();
        if (t && t->kind == TY_INT && t->intstorage != IS_VARINT) return mod.IntType(IntTy(t->intstorage));
        // Report mode never writes this partial module. An integer placeholder
        // lets sibling expressions continue through the same exporter paths.
        return mod.IntType(CoreIntTy::I64);
    }

    enum class TypePosition { Value, Parameter };

    CoreTypeId Ty(TypeExpr *t) { return TyAt(t, TypePosition::Value); }

    CoreTypeId TyAt(TypeExpr *t, TypePosition position) {
        // Unsupported stdlib globals are skipped at the global boundary in
        // normal export. Let that boundary see the failure in report mode too.
        if (!reportonly || exportingstdlibglobal) return TyChecked(t, position);
        try {
            return TyChecked(t, position);
        } catch (CoreUnsupported &u) {
            Remember(u);
            return ReportTypeFallback(t);
        }
    }

    CoreTypeId TyChecked(TypeExpr *t, TypePosition position) {
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
            case TY_STRUCT:
                ct.kind = CoreType::Struct;
                ct.structid = StructIdFor(t);
                break;
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
                    case A_GROW:
                        if (position == TypePosition::Parameter) mod.profile = CoreProfile::Construction;
                        ct.kind = CoreType::Grow;
                        break;
                    case A_VAR:
                        if (a->lenstorage >= 0) Fail("array-prefix", t->line);
                        mod.profile = CoreProfile::Construction;
                        ct.kind = CoreType::VarArr;
                        break;
                    case A_LIMITED:
                        if (position == TypePosition::Parameter) Fail("limited-value", t->line);
                        if (!a->sizeexpr) Fail("runtime-capacity", t->line);
                        if (a->size <= 0) Fail("zero-size", t->line);
                        if (a->size > INT32_MAX) Fail("capacity-limit", t->line);
                        ct.kind = CoreType::Limited;
                        ct.count = a->size;
                        mod.profile = CoreWithShrink(mod.profile);
                        break;
                    case A_GROWSHRINK:
                        if (position == TypePosition::Parameter) mod.profile = CoreProfile::Construction;
                        ct.kind = CoreType::GrowShrink;
                        mod.profile = CoreWithShrink(mod.profile);
                        break;
                }
                ct.elem = (a->akind == A_GROW || a->akind == A_GROWSHRINK || a->akind == A_LIMITED)
                              ? OwnerElementTy(a->sub, a->akind == A_GROW)
                              : ElementTy(a->sub);
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
                if (mod.Type(ct.elem).kind == CoreType::Ref) Fail("reference-to-reference");
                // A reference to a slice is a parameter's type and nothing else.
                if (mod.Type(ct.elem).kind == CoreType::Slice && position != TypePosition::Parameter)
                    Fail("reference-to-slice");
                break;
            default: Fail("type");
        }
        return mod.Intern(ct);
    }

    bool IsSliceRef(CoreTypeId t) const {
        auto &c = mod.Type(t);
        return c.kind == CoreType::Ref && mod.Type(c.elem).kind == CoreType::Slice;
    }

    // The same reference or slice type, read-only.
    CoreTypeId Constify(CoreTypeId t) {
        auto c = mod.Type(t);
        if ((c.kind != CoreType::Ref && c.kind != CoreType::Slice) || c.mut == CoreMut::Const) return t;
        c.mut = CoreMut::Const;
        return mod.Intern(c);
    }

    // A parameter's type as this specialization has it: a reference or slice
    // parameter whose arguments are all read-only is a read-only one, whatever
    // the declaration says, since a caller could not pass it otherwise.
    CoreTypeId ParamTy(FnSpec *sp, size_t i) {
        auto t = TyAt(sp->argtypes[i], TypePosition::Parameter);
        if (i < sp->roots.size() && !sp->roots[i].writable) t = Constify(t);
        return t;
    }

    // A result's type likewise: read-only where some return of it is.
    CoreTypeId ResultTy(FnSpec *sp, size_t i) {
        auto *result = sp->rets[i];
        if (result && result->kind == TY_ARRAY) {
            if (result->arr->akind == A_LIMITED) Fail("limited-value", result->line);
            if (result->arr->akind == A_VAR || result->arr->akind == A_GROW ||
                result->arr->akind == A_GROWSHRINK ||
                (result->arr->akind == A_FIXED && result->arr->sub &&
                 result->arr->sub->kind == TY_ARRAY && result->arr->sub->arr->akind == A_VAR))
                mod.profile = CoreProfile::Construction;
        }
        auto t = Ty(sp->rets[i]);
        if (i < sp->record.retroots.size() && sp->record.retroots[i].set && !sp->record.retroots[i].writable)
            t = Constify(t);
        return t;
    }

    bool OwnerLiteralRun(Node *n) const {
        if (!n) return false;
        if (Is<StrLit>(n)) return true;
        if (Is<ArrayLit>(n)) {
            auto a = (ArrayLit *)n;
            return !a->fillval && !a->capexpr;
        }
        if (auto x = Is<IfExpr>(n)) {
            if (!OwnerLiteralRun(x->thenb)) return false;
            return x->elseb && OwnerLiteralRun(x->elseb);
        }
        if (auto b = Is<Block>(n)) return b->tail && OwnerLiteralRun(b->tail);
        return false;
    }

    bool OwnerContainsString(Node *n) const {
        if (!n) return false;
        if (Is<StrLit>(n)) return true;
        if (auto x = Is<IfExpr>(n))
            return OwnerContainsString(x->thenb) || OwnerContainsString(x->elseb);
        if (auto b = Is<Block>(n)) return OwnerContainsString(b->tail);
        return false;
    }

    bool OwnerFillLiteral(Node *n) const {
        if (auto a = Is<ArrayLit>(n)) return a->fillval != nullptr;
        if (auto x = Is<IfExpr>(n)) return OwnerFillLiteral(x->thenb) || OwnerFillLiteral(x->elseb);
        if (auto b = Is<Block>(n)) return OwnerFillLiteral(b->tail);
        return false;
    }

    void RequireOwnerLiteralRun(Node *n, TypeExpr *owner) {
        if (OwnerFillLiteral(n)) Fail("owner-fill-literal", n->line);
        if (auto a = Is<ArrayLit>(n); a && a->capexpr) Fail("runtime-capacity", n->line);
        if (!OwnerLiteralRun(n))
            Fail(owner->arr->akind == A_LIMITED ? "limited-initializer" : "nonfixed-construction",
                 n ? n->line : owner->line);
        if (owner->arr->akind == A_LIMITED) {
            if (auto a = Is<ArrayLit>(n); a && (int64_t)a->elems.size() > owner->arr->size)
                Fail("limited-initializer", n->line);
            if (auto x = Is<IfExpr>(n)) {
                RequireOwnerLiteralRun(x->thenb, owner);
                RequireOwnerLiteralRun(x->elseb, owner);
            } else if (auto b = Is<Block>(n)) {
                RequireOwnerLiteralRun(b->tail, owner);
            }
        }
    }

    CoreMut MutOf(const TypeExpr *t) { return t && t->cq ? CoreMut::Const : CoreMut::Mut; }

    // Capture mutability follows the checked effects: read-only owners stay
    // const, while a callee that changes one needs writable contents.
    CoreMut CaptureMut(FnSpec *sp, VarDef *v) {
        if (v->isvar) return CoreMut::Mut;
        auto t = v->type;
        if (!t || t->cq || t->kind != TY_ARRAY || !t->arr) return CoreMut::Const;
        auto grows = sp->record.growexternals.contains(v);
        auto shrinks = sp->record.shrinkexternals.contains(v);
        auto writes = sp->record.writeexternals.contains(v);
        if (!grows && !shrinks && !writes) return CoreMut::Const;
        switch (t->arr->akind) {
            case A_GROW:
                if (shrinks) mod.profile = CoreWithShrink(mod.profile);
                return CoreMut::Mut;
            case A_GROWSHRINK:
                mod.profile = CoreWithShrink(mod.profile);
                return CoreMut::Mut;
            case A_LIMITED:
                Fail("limited-capture-mutation", v->line);
            default: return CoreMut::Const;
        }
    }

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
    void FindReachable(const vector<FnSpec *> &roots) {
        vector<FnSpec *> order = roots;
        unordered_set<const FnSpec *> seen(roots.begin(), roots.end());
        unordered_map<const FnSpec *, vector<FnSpec *>> callees;
        for (size_t i = 0; i < order.size(); i++) {
            auto sp = order[i];
            if (!sp->body) {
                ReportOrFail("extern-fn", sp->sf->line);
                continue;
            }
            if (sp->isfunval) ReportOrFail("function-value", sp->sf->line);
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
                // A captured slice variable's content roots must name what the
                // slice may point into, so each local of an enclosing function
                // that it may be rooted at is a parameter too.
                for (size_t k = 0; k < mine.size(); k++) {
                    auto v = mine[k];
                    if (v->type->kind != TY_SLICE) continue;
                    for (auto &alt : v->ref.alts) {
                        auto r = alt.root;
                        if (r && r->ownerspec && r->ownerspec != sp && !r->isglobal && !r->istemp &&
                            have.insert(r).second) {
                            mine.push_back(r);
                            changed = true;
                        }
                    }
                }
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
        return ContextOf(spec, DefaultRequests(spec));
    }

    vector<CoreRequest> DefaultRequests(FnSpec *spec) {
        vector<CoreRequest> requests;
        for (size_t i = 0; i < spec->rets.size(); i++) {
            auto type = ResultTy(spec, i);
            requests.push_back(NonfixedValueType(type) ? CoreRequest::Value : CoreRequest::Register);
        }
        return requests;
    }

    int ContextOf(FnSpec *spec, const vector<CoreRequest> &requests) {
        if (requests.size() != spec->rets.size()) Fail("result-request");
        for (size_t i = 0; i < requests.size(); i++) {
            auto type = ResultTy(spec, i);
            auto nonfixed = NonfixedValueType(type);
            if ((!nonfixed && requests[i] != CoreRequest::Register) ||
                (nonfixed && requests[i] == CoreRequest::Register))
                Fail("result-request");
            if (requests[i] == CoreRequest::ElementRun && !nonfixed) Fail("result-request");
        }
        auto &variants = ctxvariants[spec];
        if (auto it = variants.find(requests); it != variants.end()) return it->second;
        auto id = (int)ctxspecs.size();
        ctxspecs.push_back(spec);
        ctxrequests.push_back(requests);
        variants[requests] = id;
        return id;
    }

    string ContextStableKey(FnSpec *spec, const vector<CoreRequest> &requests) {
        auto key = keys.Context(spec).total.Short();
        if (requests == DefaultRequests(spec)) return key;
        key += "/requests-";
        for (auto request : requests)
            key += request == CoreRequest::Register ? 'r' : request == CoreRequest::Value ? 'v' : 'e';
        return key;
    }

    pair<CoreImplId, vector<CoreRequest>> TargetContext(FnSpec *spec) {
        auto variants = ctxvariants.find(spec);
        if (variants == ctxvariants.end() || variants->second.size() != 1) Fail("return-from-request");
        return { variants->second.begin()->second, variants->second.begin()->first };
    }

    CoreTargetId TargetSetOf(FnSpec *spec) {
        auto [member, requests] = TargetContext(spec);
        vector<CoreImplId> members { member };
        if (auto found = targetsetid.find(members); found != targetsetid.end()) return found->second;
        auto id = (CoreTargetId)mod.targets.size();
        targetsetid.emplace(members, id);
        mod.targets.push_back({ std::move(members) });
        mod.profile = CoreProfile::Construction;
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
            auto nctx = ctxspecs.size();
            auto ntypes = mod.types.size();
            auto nstructs = mod.structs.size();
            auto oldprofile = mod.profile;
            auto wasexportingstdlibglobal = exportingstdlibglobal;
            exportingstdlibglobal = stdlib;
            try {
                ExportGlobal(g);
            } catch (CoreUnsupported &u) {
                if (!stdlib && !reportonly) throw;
                if (reportonly && !stdlib) Remember(u);
                // What it called is not part of the program.
                while (ctxspecs.size() > nctx) {
                    auto spec = ctxspecs.back();
                    auto requests = ctxrequests.back();
                    if (auto variants = ctxvariants.find(spec); variants != ctxvariants.end()) {
                        variants->second.erase(requests);
                        if (variants->second.empty()) ctxvariants.erase(variants);
                    }
                    ctxspecs.pop_back();
                    ctxrequests.pop_back();
                }
                // A skipped initializer must not leave struct descriptors
                // without a corresponding global or field that uses them.
                mod.types.resize(ntypes);
                mod.structs.resize(nstructs);
                for (auto it = structid.begin(); it != structid.end();) {
                    if (it->second >= (int)nstructs) it = structid.erase(it);
                    else ++it;
                }
                mod.profile = oldprofile;
                if (g->names.size() == 1 && g->defs.size() == 1 && g->defs[0]) skipped[g->defs[0]] = u;
                if (reportonly && !stdlib)
                    for (auto v : g->defs) if (v && v->type) (void)Ty(v->type);
                if (reportonly && !stdlib && !g->inits.empty()) ProbeChildren(g->inits[0]);
            }
            exportingstdlibglobal = wasexportingstdlibglobal;
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
        cg.module = keys.ModuleOf(g->line.fileidx);
        coerceorg = cg.org;
        if (OwnerContainsString(g->inits[0])) Fail("nonfixed-construction", g->inits[0]->line);
        if (v->type->kind == TY_ARRAY && v->type->arr->akind != A_FIXED)
            RequireOwnerLiteralRun(g->inits[0], v->type);
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
        for (auto &unsupported : sp->record.coreShrinkUnsupported)
            ReportOrFail(CoreShrinkBoundaryName(unsupported.boundary), unsupported.at);
        here = sp->sf->line;
        mod.impls.emplace_back();
        mod.contexts.emplace_back();
        auto &impl = mod.impls.back();
        cur = Cur {};
        cur.spec = sp;
        cur.impl = &impl;
        cur.free = &freevars[sp];
        cur.requests = ctxrequests[k];
        impl.name = string(sp->sf->name);
        if (!CoreIsUtf8(impl.name)) Fail("non-utf8-text");
        if (sp->sf->isthread) ReportOrFail("thread", sp->sf->line);
        for (size_t r = 0; r < sp->rets.size(); r++) {
            auto type = ResultTy(sp, r);
            impl.results.push_back({ type, cur.requests[r], {} });
        }
        auto porg = Org(sp->sf->line, CoreOriginKind::Param);
        for (size_t i = 0; i < sp->params.size(); i++) {
            auto vd = sp->params[i];
            if (vd->reusable) ReportOrFail("reusable", vd->line);
            auto ty = ParamTy(sp, i);
            auto id = NewVar(vd, vd->name, ty, vd->isvar ? CoreVarKind::Var : CoreVarKind::Let, 0, porg);
            impl.params.push_back({ id, mod.Type(ty).kind == CoreType::Ref });
        }
        // A free variable is a trailing by-reference parameter: a reference to
        // the caller's variable, writable only where the variable is.
        for (auto fv : *cur.free) {
            here = sp->sf->line;
            if (fv->type->kind == TY_REF) ReportOrFail("captured-reference", sp->sf->line);
            CoreType rt;
            rt.kind = CoreType::Ref;
            rt.mut = CaptureMut(sp, fv);
            rt.elem = Ty(fv->type);
            auto id = NewVar(nullptr, fv->name, mod.Intern(rt), CoreVarKind::Let, 0, porg);
            cur.varid[fv] = id;
            impl.params.push_back({ id, true });
        }
        impl.body = Body(sp->body);
        FillNamedResults(sp);

        auto &ctx = mod.contexts.back();
        ctx.impl = k;
        ctx.declkey = DeclKey(sp);
        ctx.stablekey = ContextStableKey(sp, cur.requests);
        ctx.module = keys.ModuleOf(sp->sf->line.fileidx);
        if (!reportonly) {
            FillRoots(sp, ctx);
        } else {
            try {
                FillRoots(sp, ctx);
            } catch (CoreUnsupported &u) {
                Remember(u);
            }
        }
    }

    void FillNamedResults(FnSpec *sp) {
        set<CoreVarId> named;
        for (size_t i = 0; i < cur.impl->results.size(); i++) {
            auto &result = cur.impl->results[i];
            if (result.request != CoreRequest::Value || !NonfixedValueType(result.type)) continue;
            auto local = NamedResultOf(sp->body, sp->sf, sp->rets.size(), i);
            if (!local) continue;
            auto found = cur.varid.find(local);
            if (found == cur.varid.end() || found->second < (int)cur.impl->params.size() ||
                named.count(found->second)) continue;
            auto source = cur.impl->vars[found->second].type;
            auto &sourceType = mod.Type(source);
            auto &resultType = mod.Type(result.type);
            auto resizableToVar = (sourceType.kind == CoreType::Grow ||
                                   sourceType.kind == CoreType::GrowShrink) &&
                                  resultType.kind == CoreType::VarArr &&
                                  sourceType.elem == resultType.elem;
            if (source != result.type && !resizableToVar) continue;
            result.namedLocal = found->second;
            named.insert(found->second);
        }
    }

    // The function body: a value-producing tail is its return.
    CoreBlock Body(Block *b) {
        CoreBlock cb;
        cb.scope = cur.nextscope++;
        for (auto s : b->stmts) Stmt(s, cb);
        if (b->tail) {
            here = b->tail->line;
            auto t = b->tail;
            try {
                if (t->exprtype && t->exprtype->kind != TY_VOID && !cur.impl->results.empty()) {
                    CoreStmt st;
                    st.org = Org(t->line, CoreOriginKind::Return);
                    coerceorg = st.org;
                    auto call = Is<Call>(t);
                    if (call && call->spec && call->spec->rets.size() > 1) {
                        st.kind = CoreStmtKind::RetForward;
                        st.expr = CallValue(call, true, cur.requests);
                    } else {
                        st.kind = CoreStmtKind::Ret;
                        st.expr = ReturnValue(t, cur.spec, 0, true);
                    }
                    cb.stmts.push_back(std::move(st));
                } else {
                    Stmt(t, cb);
                }
            } catch (CoreUnsupported &u) {
                if (!reportonly) throw;
                Remember(u);
                ProbeChildren(t);
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
                try {
                    cb->value = Value(b->tail);
                } catch (CoreUnsupported &u) {
                    if (!reportonly) throw;
                    Remember(u);
                    ProbeChildren(b->tail);
                }
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
        if (!reportonly) return StmtChecked(n, out);
        try {
            StmtChecked(n, out);
        } catch (CoreUnsupported &u) {
            Remember(u);
            ProbeChildren(n);
        }
    }

    void StmtChecked(Node *n, CoreBlock &out) {
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
                if (exprdepth) Fail("control-in-expression");
                auto target = r->targetspec ? r->targetspec : cur.spec;
                if (!target) Fail("return-outside-function");
                auto nonlocal = !r->from.empty() || target != cur.spec;
                auto forward = r->vals.size() == 1 && Is<Call>(r->vals[0]) &&
                               ((Call *)r->vals[0])->spec && ((Call *)r->vals[0])->spec->rets.size() > 1;
                auto s = MakeStmt(CoreStmtKind::Ret, n->line, CoreOriginKind::Return);
                if (nonlocal) s.target = TargetSetOf(target);
                if (forward) {
                    s.kind = nonlocal ? CoreStmtKind::ReturnFromForward : CoreStmtKind::RetForward;
                    s.expr = CallValue((Call *)r->vals[0], true,
                                       nonlocal ? TargetContext(target).second : cur.requests);
                } else if (r->vals.size() > 1 || nonlocal) {
                    s.kind = nonlocal ? CoreStmtKind::ReturnFrom : CoreStmtKind::RetValues;
                    for (size_t i = 0; i < r->vals.size(); i++)
                        s.values.push_back(ReturnValue(r->vals[i], target, i, true));
                } else if (r->vals.size() == 1) {
                    s.expr = ReturnValue(r->vals[0], target, 0, true);
                }
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
        if (d->reusable) Fail("reusable");
        if (d->inits.size() == 1 && d->names.size() > 1) {
            if (!Is<Call>(d->inits[0]) || d->defs.size() != d->names.size()) Fail("multiple-results");
            auto call = (Call *)d->inits[0];
            if (!call->spec || call->spec->rets.size() != d->defs.size()) Fail("multiple-results");
            auto s = MakeStmt(CoreStmtKind::Receive, d->line, CoreOriginKind::Let);
            for (size_t i = 0; i < d->defs.size(); i++) {
                auto vd = d->defs[i];
                s.vars.push_back(NewVar(vd, vd->name, VarTy(vd), vd->isvar ? CoreVarKind::Var : CoreVarKind::Let,
                                        out.scope, Org(d->line, CoreOriginKind::Let)));
            }
            s.expr = CallValue(call, true);
            s.org = Org(d->line, CoreOriginKind::Let);
            out.stmts.push_back(std::move(s));
            return;
        }
        if (d->inits.size() != d->names.size() || d->defs.size() != d->names.size())
            Fail(d->inits.empty() ? "uninitialized-declaration" : "multiple-results");
        for (size_t i = 0; i < d->defs.size(); i++) {
            auto vd = d->defs[i];
            auto s = MakeStmt(CoreStmtKind::Let, d->line, CoreOriginKind::Let);
            s.var = NewVar(vd, vd->name, VarTy(vd), vd->isvar ? CoreVarKind::Var : CoreVarKind::Let,
                           out.scope, Org(d->line, CoreOriginKind::Let));
            auto value = Value(d->inits[i]);
            if (vd->type->kind == TY_ARRAY && vd->type->arr->akind == A_LIMITED)
                RequireOwnerLiteralRun(d->inits[i], vd->type);
            else if (IsArrayTE(vd->type) && vd->type->arr->akind != A_FIXED &&
                     !CoreHasConstruction(mod.profile))
                RequireOwnerLiteralRun(d->inits[i], vd->type);
            s.expr = ReborrowTo(std::move(value), cur.impl->vars[s.var].type);
            out.stmts.push_back(std::move(s));
        }
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
                if (!v->isglobal && v->ownerspec != cur.spec) {
                    // A slice variable of an enclosing function: the new slice
                    // is stored in the variable its parameter refers to.
                    if (v->type->kind != TY_SLICE) Fail("captured-reference");
                    auto s = MakeStmt(CoreStmtKind::Assign, a->line, CoreOriginKind::Rebind);
                    s.place = VarPlace(v);
                    s.expr = Value(a->rhs);
                    out.stmts.push_back(std::move(s));
                    return;
                }
                auto s = MakeStmt(CoreStmtKind::Rebind, a->line, CoreOriginKind::Rebind);
                s.var = RebindTarget(a->lval);
                s.expr = Value(a->rhs);
                out.stmts.push_back(std::move(s));
                return;
            }
            auto *assigned = a->lval->exprtype ? Pointee(a->lval->exprtype) : nullptr;
            if (IsArrayTE(assigned) && assigned->arr->akind == A_LIMITED)
                Fail("limited-value", a->line);
            if (IsArrayTE(assigned) &&
                (assigned->arr->akind == A_GROW || assigned->arr->akind == A_GROWSHRINK)) {
                auto s = MakeStmt(CoreStmtKind::AssignWhole, a->line, CoreOriginKind::Assign);
                mod.profile = CoreWithShrink(mod.profile);
                s.place = ToPlace(a->lval, true);
                if (OwnerContainsString(a->rhs)) Fail("nonfixed-construction", a->rhs->line);
                RequireOwnerLiteralRun(a->rhs, assigned);
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
                        pa.kind = CorePrintArg::Text;
                        pa.str = sl->val;
                    } else {
                        here = a->line;
                        auto *type = a->exprtype ? Pointee(a->exprtype) : nullptr;
                        if (CoreHasConstruction(mod.profile) && type &&
                            (type->kind == TY_ARRAY || type->kind == TY_SLICE)) {
                            pa.kind = CorePrintArg::View;
                            pa.view = ToView(a);
                        } else {
                            pa.kind = CorePrintArg::Expr;
                            pa.expr = Value(a);
                            auto k = mod.Type(pa.expr->type).kind;
                            if (k != CoreType::Int && k != CoreType::Bool) Fail("print-argument", a->line);
                        }
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
                auto an = c->ArgNodes();
                auto source = Pointee(an[1]->exprtype);
                auto sourceType = Ty(source);
                if (CoreHasConstruction(mod.profile) && IsArrayTE(source) &&
                    source->arr->akind == A_FIXED && !NonfixedValueType(sourceType)) {
                    auto s = MakeStmt(CoreStmtKind::AppendValue, c->line, CoreOriginKind::Expr);
                    s.place = OwnerPlace(an[0]);
                    s.expr = Value(an[1]);
                    out.stmts.push_back(std::move(s));
                } else if (CoreHasConstruction(mod.profile) && IsArrayTE(source) && NonfixedValueType(sourceType) &&
                           (Is<ArrayLit>(an[1]) || Is<Call>(an[1]))) {
                    auto s = MakeStmt(CoreStmtKind::AppendConstruct, c->line, CoreOriginKind::Expr);
                    s.place = OwnerPlace(an[0]);
                    if (auto producer = Is<Call>(an[1]); producer && producer->spec &&
                        producer->spec->rets.size() == 1) {
                        auto requests = DefaultRequests(producer->spec);
                        requests[0] = CoreRequest::ElementRun;
                        s.expr = CallValue(producer, false, std::move(requests));
                    } else {
                        s.expr = Value(an[1]);
                    }
                    out.stmts.push_back(std::move(s));
                } else {
                    auto s = MakeStmt(CoreStmtKind::Append, c->line, CoreOriginKind::Expr);
                    s.place = OwnerPlace(an[0]);
                    s.view = ToView(an[1]);
                    out.stmts.push_back(std::move(s));
                }
                return;
            }
            case B_POP_N: {
                auto an = c->ArgNodes();
                auto s = MakeStmt(CoreStmtKind::PopN, c->line, CoreOriginKind::Expr);
                mod.profile = CoreWithShrink(mod.profile);
                s.place = OwnerPlace(an[0]);
                s.expr = Value(an[1]);
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_RESIZE: {
                auto an = c->ArgNodes();
                auto s = MakeStmt(CoreStmtKind::Resize, c->line, CoreOriginKind::Expr);
                mod.profile = CoreWithShrink(mod.profile);
                s.place = OwnerPlace(an[0]);
                s.expr = Value(an[1]);
                if (an.size() == 3) s.expr2 = Value(an[2]);
                out.stmts.push_back(std::move(s));
                return;
            }
            case B_CLEAR: {
                auto an = c->ArgNodes();
                auto s = MakeStmt(CoreStmtKind::Clear, c->line, CoreOriginKind::Expr);
                mod.profile = CoreWithShrink(mod.profile);
                s.place = OwnerPlace(an[0]);
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

    // Reuse the type established for this variable. A reference-to-slice
    // parameter may have been made read-only by its context roots.
    CoreTypeId VarCoreType(VarDef *v) {
        auto it = cur.varid.find(v);
        if (it == cur.varid.end()) Fail("unknown-variable");
        return cur.impl->vars[it->second].type;
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
                auto ty = VarCoreType(v);
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
        if (auto dot = Is<Dot>(n)) {
            if (!dot->IsField() || dot->fieldidx < 0) Fail("struct");
            auto *owner = dot->obj->exprtype;
            if (!owner) Fail("struct");
            owner = Pointee(owner);
            if (owner->kind != TY_STRUCT) Fail("struct");
            if (dot->obj->exprtype->kind != TY_REF && !Is<Ident>(dot->obj) &&
                !Is<Index>(dot->obj) && !Is<Dot>(dot->obj))
                Fail("struct-temporary-projection", dot->line);

            auto inst = owner->struc->inst;
            if (!inst || !inst->st || dot->fieldidx >= (int)inst->st->fields.size()) Fail("struct");
            auto real = 0;
            for (auto i = 0; i < dot->fieldidx; i++)
                if (!inst->st->fields[i].ispad) real++;
            if (inst->st->fields[dot->fieldidx].ispad) Fail("struct");
            (void)StructIdFor(owner);
            auto p = make_unique<CorePlace>();
            p->kind = CorePlace::Field;
            p->index = real;
            p->base = ToPlace(dot->obj, true);
            return p;
        }
        if (n->exprtype && n->exprtype->kind == TY_REF) return DerefOf(Value(n));
        Fail("temporary-place");
    }

    // The array a growth operation names: the receiver, through its reference.
    CorePlaceP OwnerPlace(Node *recv) {
        if (!recv->exprtype) Fail("temporary-place");
        auto vt = Pointee(recv->exprtype);
        if (!IsArrayTE(vt) || (vt->arr->akind != A_GROW && vt->arr->akind != A_GROWSHRINK &&
                               vt->arr->akind != A_LIMITED)) Fail("growth-receiver");
        if (vt->arr->akind == A_LIMITED) {
            if (auto id = Is<Ident>(recv); id && id->vdef && !id->vdef->isvar &&
                id->vdef->ownerspec != cur.spec)
                Fail("limited-capture-mutation", id->line);
        }
        (void)Ty(vt);
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
        // A mutable reference or slice where a read-only one is wanted is
        // reborrowed read-only: its type is not the target's.
        if (target && target->cq && (target->kind == TY_REF || target->kind == TY_SLICE)) {
            auto &c = mod.Type(e->type);
            if (target->kind == TY_REF && c.kind == CoreType::Ref && c.mut == CoreMut::Mut) {
                auto r = NewExpr(CoreExprKind::Ref, Constify(e->type));
                r->mut = CoreMut::Const;
                r->place = DerefOf(std::move(e));
                return r;
            }
            if (target->kind == TY_SLICE && c.kind == CoreType::Slice && c.mut == CoreMut::Mut) {
                auto sl = NewExpr(CoreExprKind::Slice, Constify(e->type));
                sl->mut = CoreMut::Const;
                sl->view = make_unique<CoreView>();
                sl->view->kind = CoreView::Val;
                sl->view->expr = std::move(e);
                sl->org = coerceorg;
                return sl;
            }
            return e;
        }
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

    // A mutable reference or slice where the slot has a read-only one of the
    // same elements: reborrowed read-only.
    CoreExprP ReborrowTo(CoreExprP e, CoreTypeId want) {
        if (want < 0 || !e || e->type == want) return e;
        auto &w = mod.Type(want);
        auto et = e->type;
        auto &c = mod.Type(et);
        if (w.kind != c.kind || w.elem != c.elem || w.mut != CoreMut::Const || c.mut != CoreMut::Mut) return e;
        if (c.kind == CoreType::Ref) {
            auto r = NewExpr(CoreExprKind::Ref, want);
            r->mut = CoreMut::Const;
            r->place = DerefOf(std::move(e));
            return r;
        }
        if (c.kind == CoreType::Slice) {
            auto sl = NewExpr(CoreExprKind::Slice, want);
            sl->mut = CoreMut::Const;
            sl->view = make_unique<CoreView>();
            sl->view->kind = CoreView::Val;
            sl->view->expr = std::move(e);
            sl->org = coerceorg;
            return sl;
        }
        return e;
    }

    CoreExprP PushExpr(Call *c) {
        auto an = c->ArgNodes();
        if (an.size() != 2) Fail("push-arity");
        auto e = NewExpr(CoreExprKind::Push, 0);
        e->place = OwnerPlace(an[0]);
        e->org = Org(c->line, CoreOriginKind::Expr);
        auto vt = Pointee(an[0]->exprtype);
        auto elem = OwnerElementTy(vt->arr->sub);
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
            case NK_StrLit: {
                auto literal = (StrLit *)n;
                auto type = Ty(n->exprtype);
                auto &array = mod.Type(type);
                if (array.kind != CoreType::Grow || mod.Type(array.elem).kind != CoreType::Int ||
                    mod.Type(array.elem).ity != CoreIntTy::U8)
                    Fail("string-value", n->line);
                auto e = NewExpr(CoreExprKind::Bytes, type);
                for (auto byte : literal->val) e->bytes.push_back((uint8_t)byte);
                e->org = Org(n->line, CoreOriginKind::Expr);
                mod.profile = CoreProfile::Construction;
                return e;
            }
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
                e->org = Org(n->line, CoreOriginKind::Expr);
                return e;
            }
            case NK_Block: {
                auto b = (Block *)n;
                auto e = NewExpr(CoreExprKind::Block, Ty(b->exprtype ? b->exprtype : ast.voidtype));
                ExprBlockScope inexpr(*this);
                e->then = BlockOf(b, b->exprtype && b->exprtype->kind != TY_VOID);
                e->org = Org(n->line, CoreOriginKind::Expr);
                return e;
            }
            case NK_StructLit: return StructValue((StructLit *)n);
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
                return ReadOf(std::move(place), VarCoreType(v));
            }
        }
        if (v->constnot && (!want || want->kind == TY_INT)) {
            // A named `~c` takes the integer width at its use; reading its
            // stored i64 value would turn that complement into a checked cast.
            auto target = want ? want : vt;
            auto ty = Ty(target);
            auto operand = ~static_cast<uint64_t>(v->constval);
            auto e = NewExpr(CoreExprKind::Un, ty);
            e->un = CoreUnOp::BitNot;
            e->a = IntLiteral(ty, false, operand);
            e->org = Org(id->line, CoreOriginKind::Unary);
            return e;
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
        if (IsArrayTE(inner) && inner->arr->akind != A_FIXED)
            Fail(inner->arr->akind == A_LIMITED ? "limited-value" : "nonfixed-construction", id->line);
        auto place = ToPlace(id, true);
        return ReadOf(std::move(place), Ty(inner));
    }

    CoreExprP UnreachableElementValue(CoreTypeId type) {
        auto t = mod.Type(type);
        switch (t.kind) {
            case CoreType::Int: return IntLiteral(type, false, 0);
            case CoreType::Bool: return NewExpr(CoreExprKind::Bool, type);
            case CoreType::Arr: {
                auto e = NewExpr(CoreExprKind::Fill, type);
                e->a = UnreachableElementValue(t.elem);
                e->org = Org(here, CoreOriginKind::Expr);
                return e;
            }
            case CoreType::VarArr: {
                auto e = NewExpr(CoreExprKind::Arr, type);
                e->org = Org(here, CoreOriginKind::Expr);
                return e;
            }
            case CoreType::Struct: {
                auto e = NewExpr(CoreExprKind::Struct, type);
                for (auto &field : mod.structs[t.structid].fields)
                    e->elems.push_back(UnreachableElementValue(field.type));
                return e;
            }
            default: Fail("unreachable-element-type");
        }
    }

    bool NeverReturns(Node *n) const {
        if (!n) return false;
        if (auto call = Is<Call>(n)) {
            if (call->builtin == B_ABORT || call->builtin == B_EXIT) return true;
            return call->spec && !call->spec->inprogress && !call->spec->record.mayreturn;
        }
        if (auto block = Is<Block>(n)) {
            for (auto stmt : block->stmts)
                if (NeverReturns(stmt)) return true;
            return NeverReturns(block->tail);
        }
        if (auto branch = Is<IfExpr>(n))
            return NeverReturns(branch->cond) ||
                   (NeverReturns(branch->thenb) && NeverReturns(branch->elseb));
        return Is<Return>(n) != nullptr;
    }

    CoreExprP ElementValue(Node *n, CoreTypeId type) {
        if (!n->exprtype || n->exprtype->kind != TY_VOID) return Value(n);
        if (!NeverReturns(n)) Fail("bottom-element", n->line);
        here = n->line;
        auto e = NewExpr(CoreExprKind::Block, type);
        e->org = Org(n->line, CoreOriginKind::Expr);
        ExprBlockScope inexpr(*this);
        e->then = make_unique<CoreBlock>();
        e->then->scope = cur.nextscope++;
        Stmt(n, *e->then);
        here = n->line;
        e->then->value = UnreachableElementValue(type);
        return e;
    }

    CoreExprP ArrayValue(ArrayLit *a) {
        if (a->capexpr) Fail("runtime-capacity");
        auto t = a->exprtype;
        if (!t) Fail("temporary-slice");
        if (t->kind == TY_SLICE) Fail("temporary-slice");
        if (t->kind != TY_ARRAY) Fail("array-literal-type");
        auto ty = Ty(t);
        auto &ct = mod.Type(ty);
        if (a->fillval) {
            if (ct.kind == CoreType::Grow || ct.kind == CoreType::GrowShrink || ct.kind == CoreType::Limited)
                Fail("owner-fill-literal", a->line);
            if (ct.kind != CoreType::Arr) Fail("fill-grow");
            auto e = NewExpr(CoreExprKind::Fill, ty);
            e->a = ElementValue(a->fillval, ct.elem);
            e->org = Org(a->line, CoreOriginKind::Expr);
            return e;
        }
        auto e = NewExpr(CoreExprKind::Arr, ty);
        auto element = ct.elem;
        for (auto el : a->elems) e->elems.push_back(ElementValue(el, element));
        e->org = Org(a->line, CoreOriginKind::Expr);
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
                auto k = mod.Type(e->a->type).kind, k2 = mod.Type(e->b->type).kind;
                if ((k != CoreType::Int && k != CoreType::Bool) || k2 != k) Fail("elementwise-arithmetic");
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
        // Both operands are integers: a scalar with an array or struct is
        // elementwise arithmetic, whichever side the aggregate is on.
        if (mod.Type(e->type).kind != CoreType::Int || mod.Type(e->b->type).kind != CoreType::Int)
            Fail("elementwise-arithmetic");
        e->org = Org(b->line, CoreOriginKind::Binary);
        return e;
    }

    CoreExprP DotValue(Dot *d) {
        if (d->member == B_LEN) {
            auto e = NewExpr(CoreExprKind::Len, mod.IntType(CoreIntTy::I64));
            e->view = ToView(d->obj);
            return e;
        }
        if (d->member == B_CAP) {
            auto recv = d->obj->exprtype ? Pointee(d->obj->exprtype) : nullptr;
            if (IsArrayTE(recv) && recv->arr->akind == A_LIMITED) Fail("limited-capacity", d->line);
            Fail("builtin-call", d->line);
        }
        if (d->member >= 0) Fail("builtin-property");
        if (!d->IsField()) Fail("struct");
        return ReadOf(ToPlace(d, true), Ty(d->exprtype));
    }

    CoreExprP StructValue(StructLit *literal) {
        auto inst = literal->sinst;
        if (!inst || !inst->st || literal->einst || literal->variant) Fail("struct");
        auto type = Ty(literal->type);
        auto e = NewExpr(CoreExprKind::Struct, type);
        for (size_t i = 0; i < inst->st->fields.size(); i++) {
            if (inst->st->fields[i].ispad) continue;
            auto init = literal->InitFor((int)i);
            if (!init) Fail("struct");
            e->elems.push_back(ElementValue(init, Ty(inst->ftypes[i])));
        }
        return e;
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

    CoreExprP CallValue(Call *c, bool multiResult = false, vector<CoreRequest> requests = {}) {
        if (c->builtin >= 0 && !c->spec) {
            if (multiResult) Fail("multiple-results", c->line);
            return BuiltinValue(c);
        }
        if (!c->spec) {
            if (!c->dispatch.empty()) Fail("adt");
            Fail("function-value");
        }
        if (c->spec->isfunval || c->fvbody || c->trailing) Fail("function-value");
        if (!c->dispatch.empty()) Fail("adt");
        if (!c->fmtspecs.empty()) Fail("user-format");
        auto callee = c->spec;
        if (!multiResult && callee->rets.size() > 1 && HasNonfixedResult(callee))
            Fail("multiple-results", c->line);
        auto type = multiResult ? CallResultType(callee)
                                : callee->rets.empty() ? mod.UnitType() : ResultTy(callee, 0);
        auto e = NewExpr(CoreExprKind::Call, type);
        auto savedorg = coerceorg;
        coerceorg = Org(c->line, CoreOriginKind::Call);
        auto an = c->ArgNodes();
        if (an.size() != callee->params.size()) Fail("call-arity");
        for (size_t i = 0; i < an.size(); i++) {
            here = an[i]->line;
            auto pt = callee->argtypes[i];
            CoreArg arg;
            if (pt->kind == TY_REF) {
                arg = CoreArgReference { mod.Type(ParamTy(callee, i)).mut, ArgPlace(an[i]) };
            } else {
                auto value = Value(an[i]);
                if (NonfixedValueType(ParamTy(callee, i))) arg = CoreArgConstruct { std::move(value) };
                else arg = CoreArgValue { std::move(value) };
            }
            e->args.push_back(std::move(arg));
        }
        // The callee's free variables follow, as references to this
        // activation's variables of the same name.
        for (auto fv : freevars[callee]) {
            CoreArg arg;
            arg = CoreArgReference { CaptureMut(callee, fv), VarPlace(fv) };
            e->args.push_back(std::move(arg));
        }
        coerceorg = savedorg;
        // The callee's number is taken once its arguments, which may call too,
        // have been met: calls are numbered in the order they run.
        if (requests.empty()) requests = DefaultRequests(callee);
        e->ctx = ContextOf(callee, requests);
        e->org = Org(c->line, CoreOriginKind::Call);
        return e;
    }

    CoreExprP BuiltinValue(Call *c) {
        switch (c->builtin) {
            case B_POP: {
                auto an = c->ArgNodes();
                auto owner = Pointee(an[0]->exprtype);
                auto e = NewExpr(CoreExprKind::Pop, OwnerElementTy(owner->arr->sub));
                mod.profile = CoreWithShrink(mod.profile);
                e->place = OwnerPlace(an[0]);
                e->org = Org(c->line, CoreOriginKind::Expr);
                return e;
            }
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
            case B_COPY: {
                auto an = c->ArgNodes();
                auto t = an.empty() ? nullptr : Pointee(an[0]->exprtype);
                if (!t || (!IsArrayTE(t) && t->kind != TY_SLICE)) Fail("copy", c->line);
                if (IsArrayTE(t) && t->arr->akind == A_LIMITED) Fail("limited-value", c->line);
                auto e = NewExpr(CoreExprKind::Copy, Ty(c->exprtype));
                e->place = ToPlace(an[0], true);
                e->org = Org(c->line, CoreOriginKind::Expr);
                mod.profile = CoreProfile::Construction;
                return e;
            }
            case B_POP_N: case B_RESIZE: case B_CLEAR: Fail("statement-as-value");
            case B_ALLOC_INDEX: case B_ALLOC_REF: case B_FREE: case B_ALLOC_SLICE:
            case B_REALLOC_SLICE: case B_FREE_SLICE:
                Fail("reusable");
            case B_THREAD_SPAWN: case B_THREAD_WAIT: case B_QPUT: case B_QGET: case B_QPOLL:
            case B_HARDWARE_THREADS:
                Fail("thread");
            case B_TO_BYTES: case B_BYTES_OF: case B_FROM_BYTES: Fail("serialization");
            // A declaration with only a type gets its type's default value
            // from the checker.
            case B_DEFAULT: {
                auto t = c->tyargs.empty() ? nullptr : c->tyargs[0];
                if (IsArrayTE(t) && t->arr->akind != A_FIXED)
                    Fail(t->arr->akind == A_LIMITED ? "limited-value" : "nonfixed-construction", c->line);
                Fail(c->implicit ? "uninitialized-declaration" : "default-value");
            }
            case B_CAP: {
                auto an = c->ArgNodes();
                auto t = an.empty() || !an[0]->exprtype ? nullptr : Pointee(an[0]->exprtype);
                if (IsArrayTE(t) && t->arr->akind == A_LIMITED) Fail("limited-capacity", c->line);
                Fail("builtin-call");
            }
            case B_LEN: case B_INDEX_OF: Fail("builtin-call");
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
            if (!v) {
                out.push_back({ CoreRootRef::Static, 0 });
                continue;
            }
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
            auto toslice = IsSliceRef(impl.vars[i].type);
            if (toslice) {
                // Rooted at what the caller passed for it; what the slice it
                // refers to may be rooted at is the content roots, below.
                roots.push_back({ CoreRootRef::Param, (int)i });
            } else if (auto vd = cur.vardefs[i]) {
                if (vd->refrootknown) roots = RootsOf(vd->ref, sp, classes);
                // A parameter is rooted at what the caller passed for it: where
                // the class it shares with other parameters is not a global,
                // that is the parameter itself, and a local bound to the class
                // keeps the whole class.
                if (i < impl.params.size() && !roots.empty() &&
                    all_of(roots.begin(), roots.end(),
                           [](const CoreRootRef &r) { return r.kind == CoreRootRef::Param; }))
                    roots = { CoreRootRef { CoreRootRef::Param, (int)i } };
            } else {
                roots.push_back({ CoreRootRef::Param, (int)i });
            }
            for (auto c : classes) globalclasses.push_back({ k, false, (int)ctx.varroots.size(), c });
            ctx.varroots.push_back({ (int)i, std::move(roots) });
            ctx.content.emplace_back();
            ctx.hascontent.push_back(toslice);
        }
        for (size_t i = 0; i < impl.results.size(); i++) {
            vector<CoreRootRef> roots;
            vector<VarDef *> classes;
            if (mod.IsRefOrSlice(impl.results[i].type) && i < sp->record.retroots.size())
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
            case CorePlace::Field: return PlaceRoots(*p.base, k);
        }
        return {};
    }

    RootSet ViewRoots(const CoreView &v, int k) {
        return v.kind == CoreView::Of ? PlaceRoots(*v.place, k) : ExprRoots(*v.expr, k);
    }

    RootSet ArgRoots(const CoreArg &a, int k) {
        return visit([&](const auto &arg) -> RootSet {
            using Arg = decay_t<decltype(arg)>;
            if constexpr (is_same_v<Arg, CoreArgReference>) return PlaceRoots(*arg.place, k);
            else return mod.IsRefOrSlice(arg.expr->type) ? ExprRoots(*arg.expr, k) : RootSet {};
        }, a);
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
                auto &context = mod.contexts[e.ctx];
                for (auto &roots : context.resultroots)
                    for (auto &r : roots) {
                        if (r.kind == CoreRootRef::Param) {
                            auto a = ArgRoots(e.args[r.index], k);
                            out.insert(a.begin(), a.end());
                        } else if (r.kind == CoreRootRef::Global || r.kind == CoreRootRef::Static) out.insert(r);
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

    // ---------------------------------------------------------------------
    // Content roots of a reference to a slice variable.
    //
    // What the slice a `T[:]&` parameter (or a captured slice variable) refers
    // to may be rooted at is named in the callee's terms: a global as itself,
    // and each local or parameter of the caller as the callee parameter it is
    // passed as. At every call, with those replaced by the arguments' roots, it
    // is exactly the root set of the slice variable passed, which is what the
    // callers' own annotations say; so it is read off the callers, to a fixed
    // point, since a caller may pass on a reference to a slice it was given.

    vector<CoreRootRef> ContentOf(int k, int var) {
        auto &c = mod.contexts[k];
        for (size_t i = 0; i < c.varroots.size(); i++)
            if (c.varroots[i].first == var && c.hascontent[i]) return c.content[i];
        return {};
    }

    void ComputeContentRoots() {
        using Key = pair<int, int>;   // Context and the parameter.
        map<Key, vector<CoreRootRef>> current;
        for (size_t round = 0; round <= mod.contexts.size() + 2; round++) {
            map<Key, vector<CoreRootRef>> next;
            string conflict;
            Line conflictat;
            for (size_t k = 0; k < mod.impls.size(); k++) {
                CoreVisitExprs(mod.impls[k].body, [&](const CoreExpr &e) {
                    if (e.kind != CoreExprKind::Call) return;
                    auto &callee = mod.impls[mod.contexts[e.ctx].impl];
                    for (size_t j = 0; j < callee.params.size() && j < e.args.size(); j++) {
                        if (!IsSliceRef(callee.vars[callee.params[j].var].type)) continue;
                        here = ctxspecs[e.ctx]->sf->line;
                        // The slice variable passed, and the roots it has here.
                        auto &a = e.args[j];
                        auto argument = get_if<CoreArgReference>(&a);
                        if (!argument) Fail("reference-to-slice");
                        RootSet slice;
                        auto &p = *argument->place;
                        if (p.kind == CorePlace::Local) {
                            if (auto r = VarRoots((int)k, p.index)) slice.insert(r->begin(), r->end());
                        } else if (p.kind == CorePlace::Deref && p.expr->kind == CoreExprKind::Read &&
                                   p.expr->place->kind == CorePlace::Local) {
                            auto r = round ? ContentOfRound(current, (int)k, p.expr->place->index)
                                           : vector<CoreRootRef> {};
                            slice.insert(r.begin(), r.end());
                        } else {
                            Fail("reference-to-slice");
                        }
                        // Each root as the callee parameter it is passed as.
                        RootSet args, named, covered;
                        vector<RootSet> argroots;
                        for (size_t i = 0; i < e.args.size(); i++)
                            argroots.push_back(i == j ? RootSet {} : ArgRoots(e.args[i], (int)k));
                        for (auto &x : slice) {
                            if (x.kind == CoreRootRef::Global || x.kind == CoreRootRef::Static) {
                                named.insert(x);
                                covered.insert(x);
                                continue;
                            }
                            auto found = false;
                            for (size_t i = 0; i < argroots.size() && !found; i++) {
                                if (i == j || !argroots[i].count(x)) continue;
                                if (!includes(slice.begin(), slice.end(), argroots[i].begin(), argroots[i].end()))
                                    continue;
                                named.insert({ CoreRootRef::Param, (int)i });
                                covered.insert(argroots[i].begin(), argroots[i].end());
                                found = true;
                            }
                            // A root no argument is passed for cannot be named.
                            if (!found) Fail("reference-to-slice");
                        }
                        if (covered != slice) Fail("reference-to-slice");
                        vector<CoreRootRef> kappa(named.begin(), named.end());
                        Key key { e.ctx, callee.params[j].var };
                        auto it = next.find(key);
                        if (it != next.end() && it->second != kappa) { conflict = "x"; conflictat = here; }
                        next[key] = std::move(kappa);
                    }
                });
            }
            if (next == current) {
                if (!conflict.empty()) Fail("reference-to-slice", conflictat);
                break;
            }
            current = std::move(next);
        }
        for (auto &[key, kappa] : current) {
            auto &c = mod.contexts[key.first];
            for (size_t i = 0; i < c.varroots.size(); i++)
                if (c.varroots[i].first == key.second) c.content[i] = kappa;
        }
    }

    vector<CoreRootRef> ContentOfRound(const map<pair<int, int>, vector<CoreRootRef>> &table, int k, int var) {
        auto it = table.find({ k, var });
        return it == table.end() ? vector<CoreRootRef> {} : it->second;
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
