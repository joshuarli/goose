// Goose compiler — stable keys. A key names a declaration, a type or a
// checked context by what it is, never by where it sits: no line number, no
// table index and no pointer reaches a digest, so an edit elsewhere in the
// program leaves it alone. Each key is the SHA-256 of a canonical byte string
// in which every string is length-prefixed, so two different inputs cannot
// serialize alike.
#pragma once

#include "sha256.h"

namespace goose {

// The writer every key is built with. The tag characters keep one kind of
// field from reading as another; strings carry their length.
class Canon {
    string s;

public:
    Canon &Tag(char c) {
        s += c;
        return *this;
    }
    Canon &U(uint64_t v) {
        s += to_string(v);
        s += ';';
        return *this;
    }
    Canon &I(int64_t v) {
        s += to_string(v);
        s += ';';
        return *this;
    }
    Canon &B(bool v) {
        s += v ? 'T' : 'F';
        return *this;
    }
    Canon &Str(string_view v) {
        U(v.size());
        s.append(v.data(), v.size());
        return *this;
    }
    Canon &Dig(const Digest &d) {
        s.append((const char *)d.b, sizeof d.b);
        return *this;
    }
    const string &Text() const { return s; }
    Digest Hash() const { return Sha256::Of(s); }
};

// The identity of a source declaration: its module, namespace and name, the
// canonical form of its written parameter types, and, for a nested function,
// the enclosing declaration and its ordinal among same-named siblings.
struct DeclKey {
    Digest digest;
};

// A type: structural for the built-in constructors, a declaration and the
// argument types for a nominal one.
struct TypeKey {
    Digest digest;
};

// The checker compares a call's context with each earlier specialization of
// the callee along these dimensions (and no others) before it reuses one.
// Order is the order the digests are mixed into the context key.
enum class SpecDim {
    LexicalParent,
    Escaped,
    NarrowedEnv,
    EnvReads,
    ArgTypes,
    TypeBindings,
    LiteralParams,
    FunctionValues,
    RootClass,
    RootProvenance,
    RootPool,
    RootHeldExact,
    RootGrowShrinkElems,
    RootOneArray,
    RootDepthKey,
    SlotViews,
    NonlocalTargets,
    Count
};
constexpr int kSpecDims = (int)SpecDim::Count;

inline const char *SpecDimName(SpecDim d) {
    static const char *names[] = { "lexical_parent", "escaped", "narrowed_env", "env_reads",
                                   "arg_types", "type_bindings", "literal_params",
                                   "function_values", "root_class", "root_provenance",
                                   "root_pool", "root_held_exact", "root_grow_shrink_elems",
                                   "root_one_array", "root_depth_key", "slot_views",
                                   "nonlocal_targets" };
    static_assert(sizeof names / sizeof *names == kSpecDims);
    return names[(int)d];
}

// A checked context: the declaration and one digest per dimension, so a
// report can say which dimension separates two contexts of one function.
struct ContextKey {
    Digest decl;
    Digest dims[kSpecDims];
    Digest total;
};

// Makes the keys of one finished typecheck. Everything is computed on demand
// and memoized; nothing here runs unless a caller asks for a key.
class KeyMaker {
    const Ast &ast;
    unordered_map<const TypeExpr *, Digest> types;
    unordered_map<const SFunction *, Digest> decls;
    unordered_map<const SFunction *, int> ordinals;       // Among same-named nested siblings, or duplicates.
    bool ordinalsbuilt = false;
    struct Base {
        Digest key;
        Digest dims[kSpecDims];
    };
    unordered_map<const FnSpec *, Base> bases;
    unordered_set<const FnSpec *> basing, keying;
    unordered_map<const FnSpec *, ContextKey> contexts;
    unordered_map<const FnSpec *, int> funvalordinal;
    unordered_map<const VarDef *, int> varordinal;
    unordered_map<const VarDef *, string> varnames;
    unordered_map<const VarDef *, string_view> globalns;
    unordered_map<const Node *, string> funvalnames;
    bool varsbuilt = false, funvalsbuilt = false;

    static string Slashes(string p) {
        for (auto &c : p) if (c == '\\') c = '/';
        return p;
    }

    // `/./` and `/x/../` removed, enough to make two spellings of one
    // import path equal.
    static string Normal(const string &path) {
        vector<string> parts;
        size_t i = 0;
        auto rooted = !path.empty() && path[0] == '/';
        while (i <= path.size()) {
            auto j = path.find('/', i);
            if (j == string::npos) j = path.size();
            auto part = path.substr(i, j - i);
            if (part == "..") {
                if (!parts.empty() && parts.back() != "..") parts.pop_back();
                else parts.push_back(part);
            } else if (!part.empty() && part != ".") {
                parts.push_back(part);
            }
            i = j + 1;
        }
        string out = rooted ? "/" : "";
        for (size_t k = 0; k < parts.size(); k++) out += (k ? "/" : "") + parts[k];
        return out;
    }

    void BuildOrdinals() {
        if (ordinalsbuilt) return;
        ordinalsbuilt = true;
        map<tuple<const SFunction *, string_view>, int> nested;
        map<string, int> seen;
        for (auto sf : ast.functions) {
            if (sf->isnested) {
                ordinals[sf] = nested[{ sf->outer, sf->name }]++;
                continue;
            }
            // Top-level declarations that spell alike (an extern and a
            // wrapper, say) are told apart by order of appearance.
            Canon c;
            Spelling(c, sf);
            ordinals[sf] = seen[c.Text()]++;
        }
    }

    void Spelling(Canon &c, const SFunction *sf) {
        c.Tag('D').Str(ModuleOf(sf->line.fileidx)).Str(sf->ns).Str(sf->name);
        c.U(sf->params.size());
        for (auto &p : sf->params) {
            if (p.type) c.Dig(Type(p.type).digest);
            else c.Tag('_');
        }
    }

    // Plain constants and names spell themselves; anything else is a tag, so
    // an array size written as an expression keys by its shape.
    void ExprText(Canon &c, const Node *n, int depth = 0) {
        if (!n || depth > 16) { c.Tag('?'); return; }
        if (auto lit = Is<IntLit>(n)) { c.Tag('n').I(lit->val); return; }
        if (auto id = Is<Ident>(n)) { c.Tag('i').Str(id->name); return; }
        if (auto un = Is<Unary>(n)) {
            c.Tag('u').I((int)un->op);
            ExprText(c, un->child, depth + 1);
            return;
        }
        if (auto bin = Is<Binary>(n)) {
            c.Tag('b').I((int)bin->op);
            ExprText(c, bin->left, depth + 1);
            ExprText(c, bin->right, depth + 1);
            return;
        }
        c.Tag('x').I((int)n->nkind);
    }

    void BuildVars() {
        if (varsbuilt) return;
        varsbuilt = true;
        for (auto g : ast.globals)
            for (auto d : g->defs) globalns[d] = g->ns;
        unordered_map<const FnSpec *, int> perowner;
        map<string, int> pername;
        for (auto v : ast.vardefs) {
            if (v->ownerspec) varordinal[v] = perowner[v->ownerspec]++;
            else if (!v->isglobal)
                varordinal[v] = pername[cat(v->line.fileidx, ":", v->name)]++;
        }
    }

    // The function values and block literals of a function body, numbered in
    // source order within the body that holds them.
    void BuildFunVals() {
        if (funvalsbuilt) return;
        funvalsbuilt = true;
        unordered_set<const Node *> seen;
        auto walk = [&](const string &owner, Node *root) {
            int next = 0;
            function<void(Node *)> go = [&](Node *n) {
                if (!n || !seen.insert(n).second) return;
                if (Is<FunVal>(n)) funvalnames[n] = cat(owner, "#", next++);
                n->Children([&](Node *c) { go(c); });
            };
            go(root);
        };
        for (auto sf : ast.functions)
            if (sf->body) walk(Decl(sf).digest.Hex(), sf->body);
        for (auto g : ast.globals) {
            auto owner = cat("global:", ModuleOf(g->line.fileidx), ":", g->ns, ":",
                             g->names.empty() ? string_view() : g->names[0]);
            for (auto init : g->inits) walk(owner, init);
        }
    }

    string FunValName(const FunVal *fv) {
        BuildFunVals();
        for (const Node *n : { (const Node *)fv, fv ? fv->Origin() : nullptr }) {
            auto it = funvalnames.find(n);
            if (it != funvalnames.end()) return it->second;
        }
        return "unnamed-function-value";
    }

    // A variable by what a reader of the source can point at: a global by its
    // module, namespace and name; a local by the key of the context that
    // owns it and its ordinal among that context's variables in declaration
    // order. A synthetic root stands for the variable it was made from.
    string VarName(const VarDef *v) {
        if (!v) return "static";
        BuildVars();
        auto cached = varnames.find(v);
        if (cached != varnames.end()) return cached->second;
        string out;
        if (v->isglobal) {
            auto ns = globalns.find(v);
            out = cat("g:", ModuleOf(v->line.fileidx), ":", ns == globalns.end() ? string_view() : ns->second,
                      ":", v->name);
        } else if (v->classfrom) {
            out = cat("class:", VarName(v->classfrom));
        } else if (v->ownerspec) {
            out = cat("l:", BaseKey(v->ownerspec).Hex(), ":", varordinal[v]);
        } else {
            out = cat("i:", ModuleOf(v->line.fileidx), ":", v->name, ":", varordinal[v]);
        }
        return varnames[v] = out;
    }

    void TypeList(Canon &c, const vector<TypeExpr *> &ts) {
        c.U(ts.size());
        for (auto t : ts) {
            if (t) c.Dig(Type(t).digest);
            else c.Tag('_');
        }
    }

    void RootList(Canon &c, const Roots &r) {
        vector<string> alts;
        for (auto &a : r.alts) {
            Canon x;
            x.Str(VarName(a.root)).B(a.exact).Str(VarName(a.from)).B(a.slotread).B(a.classread);
            alts.push_back(x.Text());
        }
        sort(alts.begin(), alts.end());
        c.B(r.unknown).U(alts.size());
        for (auto &a : alts) c.Str(a);
    }

    void ProvOf(Canon &c, const Prov &p) {
        RootList(c, p);
        c.B(p.writable).B(p.byteview).B(p.freshview).I(p.reusable);
        if (p.reached) c.Dig(Type(p.reached).digest);
        else c.Tag('_');
    }

    // The fields RootArg::operator== compares.
    void RootFields(Canon &c, const RootArg &r) {
        c.I(r.cls).B(r.writable).I(r.reusable).B(r.growshrink).B(r.gsvia).B(r.slotread)
            .B(r.byteview).Str(VarName(r.pool)).B(r.heldexact).B(r.unknown);
    }

    // The dimensions that do not name another context beyond the lexical
    // chain. They suffice to name a context where another one refers to it.
    // Most contexts of a program repeat the same few dimension values, so a
    // digest is looked up by its canonical bytes before it is computed.
    unordered_map<string, Digest> memo;
    Digest Memo(const Canon &c) {
        auto [it, fresh] = memo.emplace(c.Text(), Digest());
        if (fresh) it->second = c.Hash();
        return it->second;
    }

    void BaseDims(const FnSpec *s, Digest *dims) {
        auto &d = dims;
        {
            Canon c;
            c.B(s->isfunval);
            if (s->lexparent) c.Dig(BaseKey(s->lexparent));
            else c.Tag('_');
            d[(int)SpecDim::LexicalParent] = Memo(c);
        }
        d[(int)SpecDim::Escaped] = Memo(Canon().B(s->escaped));
        { Canon c; TypeList(c, s->argtypes); d[(int)SpecDim::ArgTypes] = Memo(c); }
        {
            vector<pair<string_view, const TypeExpr *>> b(s->bindings.begin(), s->bindings.end());
            sort(b.begin(), b.end(), [](auto &x, auto &y) { return x.first < y.first; });
            Canon c;
            c.U(b.size());
            for (auto &[name, t] : b) c.Str(name).Dig(Type(t).digest);
            d[(int)SpecDim::TypeBindings] = Memo(c);
        }
        {
            Canon c;
            c.U(s->litparams.size());
            for (auto p : s->litparams) c.I(p);
            d[(int)SpecDim::LiteralParams] = Memo(c);
        }
        Canon cls, prov, pool, held, gs, one, depth, views;
        for (auto &r : s->roots) {
            cls.I(r.cls).B(r.writable).I(r.reusable);
            prov.B(r.growshrink).B(r.gsvia).B(r.slotread).B(r.byteview).B(r.unknown);
            pool.Str(VarName(r.pool));
            held.B(r.heldexact);
            TypeList(gs, r.gselems);
            TypeList(one, r.onearray);
            depth.I(r.depthkey);
        }
        for (auto &r : s->views) {
            RootFields(views, r);
            TypeList(gs, r.gselems);
            TypeList(one, r.onearray);
            depth.I(r.depthkey);
        }
        d[(int)SpecDim::RootClass] = Memo(cls);
        d[(int)SpecDim::RootProvenance] = Memo(prov);
        d[(int)SpecDim::RootPool] = Memo(pool);
        d[(int)SpecDim::RootHeldExact] = Memo(held);
        d[(int)SpecDim::RootGrowShrinkElems] = Memo(gs);
        d[(int)SpecDim::RootOneArray] = Memo(one);
        d[(int)SpecDim::RootDepthKey] = Memo(depth);
        d[(int)SpecDim::SlotViews] = Memo(views);
    }

public:
    explicit KeyMaker(const Ast &_ast) : ast(_ast) {}

    // The module a file is: its package and its path within it, so the same
    // program checked out elsewhere has the same modules.
    string ModuleOf(int fileidx) {
        if (fileidx < 0 || (size_t)fileidx >= ast.sources.size()) return "?";
        auto path = Slashes(ast.sources[fileidx].first);
        string pkgname = "?";
        if ((size_t)fileidx < ast.filepkg.size() && ast.filepkg[fileidx] >= 0 &&
            (size_t)ast.filepkg[fileidx] < ast.packages.size()) {
            auto &pkg = ast.packages[ast.filepkg[fileidx]];
            pkgname = pkg.stdlib ? "stdlib" : pkg.name;
            auto root = Slashes(pkg.root);
            if (!root.empty() && path.compare(0, root.size(), root) == 0) {
                return cat(pkgname, ":", Normal(path.substr(root.size())));
            }
        }
        // A file outside any package root is named relative to the program's
        // own directory.
        auto base = Slashes(ast.sources[0].first);
        auto slash = base.rfind('/');
        auto dir = slash == string::npos ? string() : base.substr(0, slash + 1);
        if (!dir.empty() && path.compare(0, dir.size(), dir) == 0) path = path.substr(dir.size());
        return cat(pkgname, ":", Normal(path));
    }

    TypeKey Type(const TypeExpr *t) {
        if (!t) return { Canon().Tag('_').Hash() };
        auto it = types.find(t);
        if (it != types.end()) return { it->second };
        Canon c;
        c.Tag('T').B(t->cq);
        switch (t->kind) {
            case TY_INT: c.Tag('i').I(t->intstorage); break;
            case TY_FLT: c.Tag('f').I(t->fltstorage); break;
            case TY_BOOL: c.Tag('b'); break;
            case TY_VOID: c.Tag('v'); break;
            case TY_STRUCT:
                c.Tag('S').Str(ModuleOf(t->struc->st->line.fileidx)).Str(t->struc->st->ns)
                    .Str(t->struc->st->name);
                for (auto a : t->struc->args) c.Dig(Type(a).digest);
                break;
            case TY_ENUM:
                c.Tag('E').Str(ModuleOf(t->enu->en->line.fileidx)).Str(t->enu->en->ns)
                    .Str(t->enu->en->name).B(t->enu->varmode);
                for (auto a : t->enu->args) c.Dig(Type(a).digest);
                break;
            case TY_GENERIC:
            case TY_UNRESOLVED:
                c.Tag('G').Str(t->named->name).B(t->named->varmode);
                for (auto a : t->named->args) c.Dig(Type(a).digest);
                break;
            case TY_FN:
                c.Tag('F').B(t->fn->has_sig);
                TypeList(c, t->fn->args);
                TypeList(c, t->fn->rets);
                break;
            case TY_ARRAY:
                c.Tag('A').I(t->arr->akind).Dig(Type(t->arr->sub).digest).I(t->arr->lenstorage);
                if (t->arr->size >= 0) c.Tag('k').I(t->arr->size);
                else ExprText(c, t->arr->sizeexpr);
                break;
            case TY_SLICE: c.Tag('L').Dig(Type(t->sub).digest); break;
            case TY_REF:
                c.Tag('R').Dig(Type(t->ref->sub).digest).I(t->ref->lenstorage).B(t->ref->optional)
                    .Str(t->ref->poolname).Str(t->ref->poolns);
                break;
            case TY_VARIANT:
                c.Tag('V').Dig(Type(t->var->adt).digest).Str(t->var->name);
                break;
        }
        return { types[t] = c.Hash() };
    }

    DeclKey Decl(const SFunction *sf) {
        auto it = decls.find(sf);
        if (it != decls.end()) return { it->second };
        BuildOrdinals();
        Canon c;
        Spelling(c, sf);
        if (sf->isnested) {
            c.Tag('N');
            if (sf->outer) c.Dig(Decl(sf->outer).digest);
            c.I(ordinals[sf]);
        } else if (ordinals[sf]) {
            c.Tag('#').I(ordinals[sf]);
        }
        return { decls[sf] = c.Hash() };
    }

    // The part of a context's key that does not depend on other contexts
    // but its lexical parents: what another context's key says in order to
    // name this one.
    Digest BaseKey(const FnSpec *s) { return BaseOf(s) ? bases[s].key : Canon().Tag('^').Hash(); }

private:
    // The base of a context, computed once: its dimensions that do not name
    // another context beyond the lexical chain, and the key they make. Null
    // where the context is already being keyed, which a reference leading
    // back to it stands for.
    const Base *BaseOf(const FnSpec *s) {
        auto it = bases.find(s);
        if (it != bases.end()) return &it->second;
        if (!basing.insert(s).second) return nullptr;
        Base b;
        BaseDims(s, b.dims);
        Canon c;
        c.Tag('X');
        if (s->sf) c.Dig(Decl(s->sf).digest);
        if (s->isfunval) {
            int ord = 0;
            for (auto e : ast.fvenvs) {
                if (e == s) break;
                ord += e->sf == s->sf && e->lexparent == s->lexparent;
            }
            c.Tag('f').I(ord);
        }
        for (int i = 0; i < kSpecDims; i++)
            if (i != (int)SpecDim::NarrowedEnv && i != (int)SpecDim::EnvReads &&
                i != (int)SpecDim::FunctionValues && i != (int)SpecDim::NonlocalTargets)
                c.Dig(b.dims[i]);
        b.key = c.Hash();
        basing.erase(s);
        return &(bases[s] = b);
    }

public:
    // How another context is named from inside a key: by its whole key, or,
    // for a function value's environment or a context whose key is being
    // made, by its base.
    Digest RefKey(const FnSpec *s) {
        if (s->isfunval || !keying.insert(s).second) return BaseKey(s);
        auto total = Context(s).total;
        keying.erase(s);
        return total;
    }

    const ContextKey &Context(const FnSpec *s) {
        auto it = contexts.find(s);
        if (it != contexts.end()) return it->second;
        keying.insert(s);
        ContextKey k;
        k.decl = s->sf ? Decl(s->sf).digest : Digest();
        if (auto b = BaseOf(s)) memcpy(k.dims, b->dims, sizeof k.dims);
        else BaseDims(s, k.dims);
        {
            Canon c;
            c.U(s->narrowedenv.size());
            for (auto v : s->narrowedenv) c.Str(VarName(v));
            k.dims[(int)SpecDim::NarrowedEnv] = Memo(c);
        }
        {
            vector<string> reads;
            for (auto &r : s->envreads) {
                Canon x;
                x.Str(VarName(r.var)).B(r.assigned).B(r.maybeassigned).B(r.refrootknown);
                ProvOf(x, r.ref);
                RootList(x, r.contents);
                x.B(r.contentbyteview).B(r.slotref);
                reads.push_back(x.Text());
            }
            sort(reads.begin(), reads.end());
            Canon c;
            c.U(reads.size());
            for (auto &r : reads) c.Str(r);
            k.dims[(int)SpecDim::EnvReads] = Memo(c);
        }
        {
            Canon c;
            c.U(s->fnvals.size());
            for (auto &[name, bind] : s->fnvals) {
                c.Str(name);
                if (bind.fv) c.Tag('v').Str(FunValName(bind.fv));
                if (bind.named) c.Tag('n').Dig(Decl(bind.named).digest);
                if (bind.env) c.Tag('e').Dig(RefKey(bind.env));
                if (bind.set) {
                    c.Tag('s').U(bind.set->size());
                    for (auto f : *bind.set) c.Dig(Decl(f).digest);
                }
            }
            k.dims[(int)SpecDim::FunctionValues] = Memo(c);
        }
        {
            vector<Digest> targets;
            for (auto t : s->needs) targets.push_back(RefKey(t));
            sort(targets.begin(), targets.end());
            Canon c;
            c.U(targets.size());
            for (auto &t : targets) c.Dig(t);
            k.dims[(int)SpecDim::NonlocalTargets] = Memo(c);
        }
        Canon total;
        total.Tag('C').Dig(k.decl);
        for (int i = 0; i < kSpecDims; i++) total.Dig(k.dims[i]);
        k.total = total.Hash();
        keying.erase(s);
        return contexts[s] = k;
    }
};

}  // namespace goose
