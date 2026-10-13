// Goose compiler — what each checked context depended on. Under
// `--build-report` the checker notes, per context, the things it consulted
// beyond the context's own text: the callees it called, the names it looked
// up (found or not), the nominal types whose layout it read, the function
// value bodies and embedded files it checked inline, and the warnings it
// gave. After the check this is turned into one digest per dependency, so
// that two reports of the same program before and after an edit say which
// contexts could have changed without comparing their results.
//
// Nothing here runs without the flag: every probe is a pointer test, and no
// key, digest or allocation is made. A dependency is never a digest of the
// whole program or an index into a table that spans it; a context's own
// names are its stable keys (keys.h).
//
// What a dependency covers is what the checker can read; what a result
// covers is what the checker leaves for later phases. One thing is read that
// is not a fact about the program: where a reference held by a global may
// point is whatever the stores checked so far made of it, so a body that
// names such a global found a different answer in a different checking order.
// That is recorded as an observation (subject `observed:`), which only
// checking the context again can confirm.
//
// Three things are deliberately outside dependencies and results:
//   * Facts that flow back from the call sites, such as whether every call
//     passed an exact array for a parameter. They are settled once all
//     contexts are checked and kept apart as `callers`.
//   * What a later phase reads that is not a checked result: the optimizer
//     replacing a variable global nothing assigns by its initializer, or
//     reachability making a context live. The optimizer and code generation
//     also read the summaries of what a function calls, which the callee
//     dependencies already carry.
//   * Files read by code outside the checker's reach: a shader's `#include`
//     is opened by the shader compiler, so only the shader's own file and
//     the blob it compiled to are recorded.
#pragma once

#include "keys.h"

namespace goose {

enum class DepKind {
    Body, Location, Interface, Summary, Layout, Lookup, Requests, Resource, Environment, Count
};
constexpr int kDepKinds = (int)DepKind::Count;

inline const char *DepKindName(DepKind k) {
    static const char *names[] = { "body", "location", "interface", "summary", "layout", "lookup",
                                   "requests", "resource", "environment" };
    static_assert(sizeof names / sizeof *names == kDepKinds);
    return names[(int)k];
}

// The tables a name is looked up in.
enum class DepLookup { Function, Global, Struct, Enum, Alias, Count };

inline const char *DepLookupName(DepLookup k) {
    static const char *names[] = { "function", "global", "struct", "enum", "alias" };
    return names[(int)k];
}

// A compile-time resource a body read: an embedded file or shader, named by
// the path it was resolved to and held by content.
struct DepResource {
    string kind, subject;
    Digest content;
};

// What the checker consulted while checking one context (or one global
// initializer). Sets, because a cycle checks its members in rounds and a
// cached callee is consulted again at every call.
struct DepEvents {
    unordered_set<const FnSpec *> callees;
    set<tuple<int, string_view, string_view>> lookups;     // (table, name, namespace)
    unordered_set<const TypeExpr *> types;                 // Nominal types instantiated.
    unordered_set<const FunVal *> funvals;                 // Origins of blocks checked inline.
    unordered_set<const VarDef *> envvars;                 // Variables outside the body it named.
    // What the check found of each global it named: where a reference the
    // global holds may point, as the stores checked so far left it. A store
    // in another context moves it, so it depends on the order contexts were
    // checked in. A new entry per change seen.
    struct GlobalState {
        Prov ref;
        Roots contents;
        bool refrootknown = false, slotref = false, contentbyteview = false;
        bool operator==(const GlobalState &o) const {
            return ref == o.ref && contents.Same(o.contents) &&
                   refrootknown == o.refrootknown && slotref == o.slotref &&
                   contentbyteview == o.contentbyteview;
        }
    };
    unordered_map<const VarDef *, vector<GlobalState>> globalstates;
    vector<DepResource> resources;
    set<pair<int, string>> warnings;                       // (code, message), no position.
    set<pair<bool, string>> verdicts;                      // A cast judged redundant, or not.
};

// Facts about declarations taken from the tree before checking: the
// checker clones function bodies and checks global initializers in place, so
// what the source said is read first.
struct DepDeclFacts {
    Digest body;        // The declaration's text: signature and body, no positions, no comments.
    Digest sig;         // What a caller reads of it: the signature with its defaults.
    Digest loc;         // Where its nodes are.
};

struct DepFunValFacts {
    const SFunction *owner = nullptr;      // The function (or global initializer) holding the block.
    const VarDecl *ownerglobal = nullptr;
    int ordinal = 0;                       // Among the blocks of that owner, in source order.
    Digest text, loc;
};

struct DepGlobalFacts {
    Digest text;        // Type and initializer as written, no positions.
    Digest readable;    // The part of it a size or an embed_file name can read.
    Digest loc;
};

struct DepEntry {
    DepKind kind;
    string subject;
    Digest digest;
};

// One checked context, or one global initializer, as the report says it.
struct DepContext {
    const SFunction *sf = nullptr;     // Null for a global initializer.
    string name;
    bool global = false;
    Digest key, decl;
    Digest result;      // Everything the check produced, no positions.
    Digest positions;   // Where the nodes it produced are.
    Digest callers;     // Facts that flow back from the call sites; see DepFinal.
    int duplicates = 1;
    vector<DepEntry> deps;
};

class DepRecorder {
public:
    unordered_map<const FnSpec *, DepEvents> specs;
    unordered_map<const VarDecl *, DepEvents> globals;
    vector<DepEvents *> stack;

    // Reads and probes are inputs of the frontend only; the build that
    // follows reads files of its own.
    bool frontend = true;

    // Every file the compile read, by the path it was opened at, and every
    // path it asked about and found absent.
    map<string, Digest> filesread;
    set<string> pathsabsent;

    unordered_map<const SFunction *, DepDeclFacts> decls;
    unordered_map<const FunVal *, DepFunValFacts> funvals;
    unordered_map<const VarDecl *, DepGlobalFacts> globalfacts;
    unordered_map<const SStruct *, Digest> structtext;
    unordered_map<const SEnum *, Digest> enumtext;
    unordered_map<const SAlias *, Digest> aliastext;

    // Filled once the check is over.
    vector<DepContext> contexts;

    DepEvents *Current() { return stack.empty() ? nullptr : stack.back(); }
};

inline unique_ptr<DepRecorder> g_deps;

inline void DepsStart() { g_deps = make_unique<DepRecorder>(); }

// Brackets the check of one context or one global initializer: what is
// consulted inside is attributed to it. A function value's body, checked
// inline in a call, belongs to the context making the call.
struct DepScope {
    bool active = false;
    explicit DepScope(const FnSpec *spec) {
        if (!g_deps) return;
        g_deps->stack.push_back(&g_deps->specs[spec]);
        active = true;
    }
    explicit DepScope(const VarDecl *global) {
        if (!g_deps) return;
        g_deps->stack.push_back(&g_deps->globals[global]);
        active = true;
    }
    ~DepScope() {
        if (active) g_deps->stack.pop_back();
    }
    DepScope(const DepScope &) = delete;
    DepScope &operator=(const DepScope &) = delete;
};

// The checker asked for a callee's context, new or cached, from a context.
inline void DepNoteCallee(const FnSpec *callee) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->callees.insert(callee);
}

// A name was looked up in a declaration table. Recorded whether or not it
// was found: a declaration added later can change what it finds.
inline void DepNoteLookup(DepLookup table, string_view name, string_view ns) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->lookups.insert({ (int)table, name, ns });
}

// The checker's lookups in the declaration tables, each noting what it asked
// for before it asks.
inline VarDecl *DepLookupGlobal(Ast &ast, string_view name, string_view ns) {
    DepNoteLookup(DepLookup::Global, name, ns);
    return ast.LookupGlobal(name, ns);
}

inline const vector<SFunction *> &DepLookupFunctions(Ast &ast, string_view name, string_view ns) {
    DepNoteLookup(DepLookup::Function, name, ns);
    return ast.LookupFunctions(name, ns);
}

inline SEnum *DepLookupEnum(Ast &ast, string_view name, string_view ns) {
    DepNoteLookup(DepLookup::Enum, name, ns);
    return ast.LookupEnum(name, ns);
}

// A nominal type was instantiated or its instantiation read.
inline void DepNoteType(const TypeExpr *t) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->types.insert(t);
}

inline void DepNoteFunVal(const FunVal *fv) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->funvals.insert((const FunVal *)fv->Origin());
}

// A variable of an enclosing activation, named from the body being checked.
inline void DepNoteEnvVar(const VarDef *v) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->envvars.insert(v);
}

// A global variable was named: its provenance as the checker has it now.
inline void DepNoteGlobalState(const VarDef *v) {
    if (!g_deps) return;
    auto cur = g_deps->Current();
    if (!cur) return;
    DepEvents::GlobalState now { v->ref, v->contents, v->refrootknown, v->slotref,
                                 v->contentbyteview };
    auto &seen = cur->globalstates[v];
    if (seen.empty() || !(seen.back() == now)) seen.push_back(std::move(now));
}

inline void DepNoteResource(string_view kind, const string &subject, const string &content) {
    if (!g_deps) return;
    auto cur = g_deps->Current();
    if (!cur) return;
    for (auto &r : cur->resources)
        if (r.kind == kind && r.subject == subject) return;
    cur->resources.push_back({ string(kind), subject, Sha256::Of(content) });
}

inline void DepNoteWarning(int code, const string &message) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->warnings.insert({ code, message });
}

inline void DepNoteVerdict(bool redundant, const string &text) {
    if (!g_deps) return;
    if (auto cur = g_deps->Current()) cur->verdicts.insert({ redundant, text });
}

inline void DepNoteFileRead(const string &path, const string &contents) {
    if (!g_deps || !g_deps->frontend) return;
    g_deps->filesread[path] = Sha256::Of(contents);
}

// A file a reader outside the checker's reach (the shader compiler) opened:
// read again here, so that its content is on record.
inline void DepNoteInput(const string &path) {
    if (!g_deps || !g_deps->frontend) return;
    string contents;
    if (LoadFile(path, contents)) g_deps->filesread[path] = Sha256::Of(contents);
    else g_deps->pathsabsent.insert(path);
}

inline void DepNotePathProbe(const string &path, bool exists) {
    if (!g_deps || !g_deps->frontend) return;
    if (!exists) g_deps->pathsabsent.insert(path);
}

// ---------------------------------------------------------------------------
// Canonical text of declarations as the source has them. Positions go to a
// second writer so that moving a declaration changes its location digest and
// nothing else.

// The module of each source file, named once: the key maker builds the name
// each time it is asked.
class DepModules {
    KeyMaker &keys;
    vector<string> names;
    vector<bool> known;

public:
    DepModules(KeyMaker &k, size_t files) : keys(k), names(files), known(files, false) {}
    const string &ModuleOf(int fileidx) {
        static const string unknown = "?";
        if (fileidx < 0 || (size_t)fileidx >= names.size()) return unknown;
        if (!known[fileidx]) {
            names[fileidx] = keys.ModuleOf(fileidx);
            known[fileidx] = true;
        }
        return names[fileidx];
    }
};

class DepAst {
    DepModules &mod;
    Canon &c;
    Canon &p;
    // Called for each block written inside what is being digested.
    function<void(const FunVal *)> onfunval;

    void Pos(const Line &l) { p.U((uint64_t)l.line).Str(mod.ModuleOf(l.fileidx)); }

    void Exprs(const vector<Node *> &v) {
        c.U(v.size());
        for (auto n : v) Expr(n);
    }

    void Types(const vector<TypeExpr *> &v) {
        c.U(v.size());
        for (auto t : v) Type(t);
    }

public:
    DepAst(DepModules &m, Canon &content, Canon &positions) : mod(m), c(content), p(positions) {}

    void OnFunVal(function<void(const FunVal *)> f) { onfunval = std::move(f); }

    // A type as written: sizes stay expressions, because what they evaluate
    // to is a fact about the constants they name, which a lookup records.
    void Type(const TypeExpr *t) {
        if (!t) { c.Tag('_'); return; }
        c.Tag('T').B(t->cq);
        switch (t->kind) {
            case TY_INT: c.Tag('i').I(t->intstorage); break;
            case TY_FLT: c.Tag('f').I(t->fltstorage); break;
            case TY_BOOL: c.Tag('b'); break;
            case TY_VOID: c.Tag('v'); break;
            case TY_STRUCT:
                c.Tag('S').Str(mod.ModuleOf(t->struc->st->line.fileidx)).Str(t->struc->st->ns)
                    .Str(t->struc->st->name);
                Types(t->struc->args);
                break;
            case TY_ENUM:
                c.Tag('E').Str(mod.ModuleOf(t->enu->en->line.fileidx)).Str(t->enu->en->ns)
                    .Str(t->enu->en->name).B(t->enu->varmode);
                Types(t->enu->args);
                break;
            case TY_GENERIC:
            case TY_UNRESOLVED:
                c.Tag('G').Str(t->named->name).Str(t->named->ns).B(t->named->varmode);
                Types(t->named->args);
                break;
            case TY_FN:
                c.Tag('F').B(t->fn->has_sig);
                Types(t->fn->args);
                Types(t->fn->rets);
                break;
            case TY_ARRAY:
                c.Tag('A').I(t->arr->akind).I(t->arr->lenstorage);
                Type(t->arr->sub);
                Expr(t->arr->sizeexpr);
                break;
            case TY_SLICE: c.Tag('L'); Type(t->sub); break;
            case TY_REF:
                c.Tag('R').I(t->ref->lenstorage).B(t->ref->optional).Str(t->ref->poolname)
                    .Str(t->ref->poolns);
                Type(t->ref->sub);
                break;
            case TY_VARIANT:
                c.Tag('V').Str(t->var->name);
                Type(t->var->adt);
                break;
        }
    }

    void Param_(const Param &q) {
        c.Str(q.name).B(q.isvar);
        Type(q.type);
        Expr(q.defaultval);
    }

    // What a caller reads of a function: its names, type parameters,
    // parameters with their defaults, result types and kind.
    void Signature(const SFunction *sf) {
        c.Tag('D').Str(mod.ModuleOf(sf->line.fileidx)).Str(sf->ns).Str(sf->name).Str(sf->cname);
        c.B(sf->isrec).B(sf->isinline).B(sf->issimd).B(sf->isthread).B(sf->isextern)
            .B(sf->isexport).B(sf->isnested).B(sf->has_rets);
        c.U(sf->generics.size());
        for (auto &g : sf->generics) {
            c.Str(g.name);
            Type(g.bound);
        }
        c.U(sf->params.size());
        for (auto &q : sf->params) Param_(q);
        Types(sf->rets);
        Pos(sf->line);
    }

    void Field_(const Field &f) {
        c.Str(f.name).B(f.isconst).B(f.ispad).I(f.padsize);
        Type(f.type);
        Expr(f.defaultval);
    }

    void StructDecl_(const SStruct *st) {
        c.Tag('d').Str(mod.ModuleOf(st->line.fileidx)).Str(st->ns).Str(st->name);
        c.U(st->generics.size());
        for (auto &g : st->generics) c.Str(g.name);
        c.U(st->fields.size());
        for (auto &f : st->fields) Field_(f);
    }

    void EnumDecl_(const SEnum *en) {
        c.Tag('e').Str(mod.ModuleOf(en->line.fileidx)).Str(en->ns).Str(en->name);
        c.U(en->generics.size());
        for (auto &g : en->generics) c.Str(g.name);
        c.U(en->variants.size());
        for (auto &v : en->variants) {
            c.Str(v.name).B(v.has_payload).U(v.fields.size());
            for (auto &f : v.fields) Field_(f);
        }
    }

    void AliasDecl_(const SAlias *al) {
        c.Tag('a').Str(mod.ModuleOf(al->line.fileidx)).Str(al->ns).Str(al->name);
        Type(al->type);
    }

    void Expr(const Node *n) {
        if (!n) { c.Tag('_'); return; }
        c.Tag('N').U(n->nkind);
        Pos(n->line);
        switch (n->nkind) {
            case NK_IntLit: {
                auto x = (const IntLit *)n;
                c.I(x->val).B(x->uns).Str(x->text);
                break;
            }
            case NK_FltLit: {
                auto x = (const FltLit *)n;
                uint64_t bits;
                memcpy(&bits, &x->val, sizeof bits);
                c.U(bits).Str(x->text);
                break;
            }
            case NK_BoolLit: c.B(((const BoolLit *)n)->val); break;
            case NK_StrLit: {
                auto x = (const StrLit *)n;
                c.Str(x->val).B(x->multiline);
                break;
            }
            case NK_Ident: {
                auto x = (const Ident *)n;
                c.Str(x->name).Str(x->ns);
                break;
            }
            case NK_ArrayLit: {
                auto x = (const ArrayLit *)n;
                Exprs(x->elems);
                Expr(x->fillval);
                Expr(x->fillcount);
                Expr(x->capexpr);
                break;
            }
            case NK_StructLit: {
                auto x = (const StructLit *)n;
                Type(x->type);
                c.B(x->defaultall).B(x->implicit).U(x->inits.size());
                for (auto &fi : x->inits) {
                    c.Str(fi.name).B(fi.fromdefault);
                    Expr(fi.val);
                }
                break;
            }
            case NK_Unary: {
                auto x = (const Unary *)n;
                c.I(x->op);
                Expr(x->child);
                break;
            }
            case NK_Binary: {
                auto x = (const Binary *)n;
                c.I(x->op);
                Expr(x->left);
                Expr(x->right);
                break;
            }
            case NK_Dot: {
                auto x = (const Dot *)n;
                c.Str(x->name).Str(x->ns);
                Expr(x->obj);
                break;
            }
            case NK_Call: {
                auto x = (const Call *)n;
                c.B(x->implicit);
                Expr(x->callee);
                Types(x->tyargs);
                Exprs(x->args);
                Expr(x->trailing);
                break;
            }
            case NK_Index: {
                auto x = (const Index *)n;
                Expr(x->obj);
                Expr(x->idx);
                break;
            }
            case NK_SliceExpr: {
                auto x = (const SliceExpr *)n;
                c.B(x->lo_from_end).B(x->hi_from_end);
                Expr(x->obj);
                Expr(x->lo);
                Expr(x->hi);
                break;
            }
            case NK_AsCast: {
                auto x = (const AsCast *)n;
                c.B(x->unchecked).B(x->implicit);
                Type(x->type);
                Expr(x->child);
                break;
            }
            case NK_RangeExpr: {
                auto x = (const RangeExpr *)n;
                Expr(x->lo);
                Expr(x->hi);
                break;
            }
            case NK_Block: {
                auto x = (const Block *)n;
                Exprs(x->stmts);
                Expr(x->tail);
                break;
            }
            case NK_IfExpr: {
                auto x = (const IfExpr *)n;
                Expr(x->cond);
                Expr(x->thenb);
                Expr(x->elseb);
                break;
            }
            case NK_MatchExpr: {
                auto x = (const MatchExpr *)n;
                Expr(x->scrutinee);
                c.U(x->arms.size());
                for (auto &arm : x->arms) {
                    c.I(arm.pat.kind).Str(arm.pat.binder).B(arm.pat.byref).U(arm.pat.items.size());
                    for (auto &pi : arm.pat.items) {
                        Expr(pi.lo);
                        Expr(pi.hi);
                    }
                    Expr(arm.body);
                }
                break;
            }
            case NK_EarlyBlock: Expr(((const EarlyBlock *)n)->body); break;
            case NK_While: {
                auto x = (const While *)n;
                Expr(x->cond);
                Expr(x->body);
                break;
            }
            case NK_LoopExpr: Expr(((const LoopExpr *)n)->body); break;
            case NK_ForLoop: {
                auto x = (const ForLoop *)n;
                c.B(x->byref).Str(x->var).Str(x->idxvar);
                Type(x->vartype);
                Type(x->idxtype);
                Expr(x->iter);
                Expr(x->body);
                break;
            }
            case NK_Return: {
                auto x = (const Return *)n;
                c.Str(x->from).Str(x->ns);
                Exprs(x->vals);
                break;
            }
            case NK_Break: Expr(((const Break *)n)->val); break;
            case NK_FunVal: {
                auto x = (const FunVal *)n;
                if (onfunval) onfunval(x);
                c.B(x->explicit_params).U(x->params.size());
                for (auto &q : x->params) Param_(q);
                p.U((uint64_t)x->col);
                Expr(x->body);
                break;
            }
            case NK_VarDecl: {
                auto x = (const VarDecl *)n;
                c.B(x->isvar).B(x->isconst).I(x->reusable).B(x->isglobal).B(x->byref)
                    .B(x->inline_arg).Str(x->ns).U(x->names.size());
                for (auto nm : x->names) c.Str(nm);
                Type(x->type);
                Exprs(x->inits);
                break;
            }
            case NK_Assign: {
                auto x = (const Assign *)n;
                c.I(x->op);
                Expr(x->lval);
                Expr(x->rhs);
                break;
            }
            case NK_IncDec: {
                auto x = (const IncDec *)n;
                c.I(x->op);
                Expr(x->lval);
                break;
            }
            // A nested function is a declaration of its own, with contexts of
            // its own: here only what the enclosing body can read of it.
            case NK_FnDecl: Signature(((const FnDecl *)n)->sf); break;
            case NK_StructDecl: StructDecl_(((const StructDecl *)n)->st); break;
            case NK_EnumDecl: EnumDecl_(((const EnumDecl *)n)->en); break;
            case NK_AliasDecl: AliasDecl_(((const AliasDecl *)n)->al); break;
            case NK_NullLit: case NK_SelfRef: case NK_Continue: case NK_InlineBlock: break;
        }
    }

    // The part of a global's initializer that a constant size, a fill count
    // or an embedded file's name can read: for a variable, the extent of an
    // array or string it is initialized to; for a constant, all of it.
    void Readable(const Node *n, bool isvar) {
        if (!isvar) { Expr(n); return; }
        if (!n) { c.Tag('_'); return; }
        if (auto al = Is<ArrayLit>(n); al && !al->capexpr) {
            c.Tag('A');
            if (al->fillcount) Expr(al->fillcount);
            else c.U(al->elems.size());
        } else if (auto s = Is<StrLit>(n)) {
            c.Tag('s').U(s->val.size());
        } else if (auto id = Is<Ident>(n)) {
            c.Tag('i').Str(id->name).Str(id->ns);
        } else {
            c.Tag('x');
        }
    }
};

// The names and source-order numbers the finished checker's variables are
// given in a report. A local is its owning context's key and its ordinal
// among that context's variables in declaration order; a parameter class root
// is its context's key and class number, never the call site that first made
// it. The full key, not its base: contexts that differ only by the blocks they
// run each check blocks of their own, with variables of the same names.
class DepNamer {
    KeyMaker &keys;
    DepModules &mods;
    unordered_map<const VarDef *, string> names;
    unordered_map<const VarDef *, int> ordinal;
    unordered_map<const VarDef *, pair<const FnSpec *, int>> classroot;
    unordered_map<const VarDef *, string_view> globalns;

public:
    DepNamer(Ast &ast, KeyMaker &k, DepModules &m) : keys(k), mods(m) {
        for (auto g : ast.globals)
            for (auto d : g->defs) globalns[d] = g->ns;
        unordered_map<const FnSpec *, int> perowner;
        map<string, int> pername;
        for (auto v : ast.vardefs) {
            if (v->ownerspec) ordinal[v] = perowner[v->ownerspec]++;
            else if (!v->isglobal) ordinal[v] = pername[cat(v->line.fileidx, ":", v->name)]++;
        }
        for (auto s : ast.fnspecs)
            for (size_t i = 0; i < s->classroots.size(); i++)
                if (s->classroots[i]) classroot[s->classroots[i]] = { s, (int)i };
    }

    const string &Var(const VarDef *v) {
        static const string none = "static";
        if (!v) return none;
        auto it = names.find(v);
        if (it != names.end()) return it->second;
        // Guard against a class root that names itself through classfrom.
        names[v] = "?";
        string out;
        if (v->isglobal) {
            auto ns = globalns.find(v);
            out = cat("g:", mods.ModuleOf(v->line.fileidx), ":",
                      ns == globalns.end() ? string_view() : ns->second, ":", v->name);
        } else if (v->istemp) {
            out = "temp";
        } else if (auto cr = classroot.find(v); cr != classroot.end()) {
            out = cat("c:", keys.Context(cr->second.first).total.Stored(), ":", cr->second.second);
        } else if (v->classfrom) {
            out = cat("class:", Var(v->classfrom));
        } else if (v->ownerspec) {
            out = cat("l:", keys.Context(v->ownerspec).total.Stored(), ":", ordinal[v]);
        } else {
            out = cat("i:", mods.ModuleOf(v->line.fileidx), ":", v->name, ":", ordinal[v]);
        }
        return names[v] = out;
    }
};


// ---------------------------------------------------------------------------
// Before checking: what the source says of each declaration.

// The text of every function, global, type and block, taken from the
// resolved tree before the checker clones, rewrites or annotates it.
inline void DepsBeforeCheck(Ast &ast) {
    auto &rec = *g_deps;
    KeyMaker keys(ast);
    DepModules mods(keys, ast.sources.size());
    // The blocks written in a body, numbered in source order within the
    // declaration that holds them.
    auto blocks = [&](const SFunction *sf, const VarDecl *global, const Node *root) {
        int next = 0;
        function<void(const Node *)> go = [&](const Node *n) {
            if (!n) return;
            if (auto fv = Is<FunVal>(n)) {
                DepFunValFacts f;
                f.owner = sf;
                f.ownerglobal = global;
                f.ordinal = next++;
                Canon text, pos;
                DepAst w(mods, text, pos);
                w.Expr(fv);
                f.text = text.Hash();
                f.loc = pos.Hash();
                rec.funvals[fv] = f;
            }
            if (Is<FnDecl>(n)) return;
            n->Children([&](Node *ch) { go(ch); });
        };
        go(root);
    };
    for (auto sf : ast.functions) {
        DepDeclFacts f;
        Canon sig, sigpos;
        DepAst(mods, sig, sigpos).Signature(sf);
        f.sig = sig.Hash();
        Canon text, pos;
        DepAst w(mods, text, pos);
        w.Signature(sf);
        w.Expr(sf->body);
        f.body = text.Hash();
        f.loc = pos.Hash();
        rec.decls[sf] = f;
        blocks(sf, nullptr, sf->body);
        for (auto &q : sf->params) blocks(sf, nullptr, q.defaultval);
    }
    for (auto g : ast.globals) {
        DepGlobalFacts f;
        Canon text, pos, readable, rpos;
        DepAst w(mods, text, pos);
        w.Expr(g);
        f.text = text.Hash();
        f.loc = pos.Hash();
        DepAst r(mods, readable, rpos);
        readable.B(g->isvar).B(g->byref).I(g->reusable).Str(g->ns);
        r.Type(g->type);
        for (auto init : g->inits) r.Readable(init, g->isvar);
        f.readable = readable.Hash();
        rec.globalfacts[g] = f;
        for (auto init : g->inits) blocks(nullptr, g, init);
    }
    for (auto st : ast.structs) {
        Canon text, pos;
        DepAst(mods, text, pos).StructDecl_(st);
        rec.structtext[st] = text.Hash();
        for (auto &fld : st->fields) blocks(nullptr, nullptr, fld.defaultval);
    }
    for (auto en : ast.enums) {
        Canon text, pos;
        DepAst(mods, text, pos).EnumDecl_(en);
        rec.enumtext[en] = text.Hash();
    }
    for (auto al : ast.aliases) {
        Canon text, pos;
        DepAst(mods, text, pos).AliasDecl_(al);
        rec.aliastext[al] = text.Hash();
    }
}

// ---------------------------------------------------------------------------
// After checking: one digest per dependency, and a digest of the result.

class DepFinal {
    Ast &ast;
    KeyMaker &keys;
    DepRecorder &rec;
    DepModules mods;
    DepNamer names;
    unordered_map<Digest, Digest, DigestHash> layouts;
    unordered_set<Digest, DigestHash> layingout;
    unordered_map<const string *, Digest> blobs;
    unordered_map<const FnSpec *, vector<const FnSpec *>> nested;
    unordered_map<const FnSpec *, vector<const FnSpec *>> groups;   // By cycle head.
    unordered_map<const FnSpec *, Digest> summaries;
    // Many contexts consult the same names and callees.
    unordered_map<string, Digest> lookups;
    map<pair<const FnSpec *, bool>, Digest> interfaces;
    unordered_map<const VarDecl *, Digest> globals;
    // A variant's position in its enum, which is its tag.
    unordered_map<const SVariant *, int> variantindex;
    // A global initializer is named by its module, namespace and names; two
    // that spell alike are told apart by order of appearance.
    unordered_map<const VarDecl *, Digest> globalkeys;

    static const FnSpec *HeadOf(const FnSpec *s) {
        while (s->cyclelink) s = s->cyclelink;
        return s;
    }

    Digest Key(const FnSpec *s) { return keys.Context(s).total; }
    Digest TypeD(const TypeExpr *t) { return keys.Type(t).digest; }

    // ---- variables, roots -------------------------------------------------

    void RootsC(Canon &c, const Roots &r, bool bound = false) {
        vector<string> alts;
        for (auto &a : r.alts) {
            Canon x;
            x.Str(names.Var(a.root)).B(a.exact && !bound).Str(names.Var(a.from)).B(a.slotread)
                .B(a.classread && !bound);
            alts.push_back(x.Text());
        }
        sort(alts.begin(), alts.end());
        c.B(r.unknown).U(alts.size());
        for (auto &a : alts) c.Str(a);
    }

    void ProvC(Canon &c, const Prov &p, bool bound = false) {
        RootsC(c, p, bound);
        c.B(p.writable).B(p.byteview).B(p.freshview).I(p.reusable);
        if (p.reached) c.Dig(TypeD(p.reached));
        else c.Tag('_');
    }

    // The value of a named constant. Both fields keep whatever the last
    // initializer gave them, which says nothing of a variable.
    static void ConstC(Canon &c, const VarDef *v) {
        c.B(v->constlit).B(v->constflt);
        if (v->constlit) c.B(v->constuns).I(v->constval).B(v->constnot);
        if (v->constflt) {
            uint64_t bits;
            memcpy(&bits, &v->constfval, sizeof bits);
            c.U(bits);
        }
    }

    // A variable by what its declaration and its uses made of it. A
    // parameter's references say whether they are exact only once every call
    // site has been seen, which is a fact about the callers and left out.
    void VarC(Canon &c, const VarDef *v) {
        c.Str(names.Var(v)).Str(v->name);
        if (v->type) c.Dig(TypeD(v->type));
        else c.Tag('_');
        c.B(v->isvar).B(v->copybind).B(v->isglobal).B(v->isparam).B(v->istemp).I(v->reusable)
            .B(v->nonneg);
        ConstC(c, v);
        c.B(v->captured).B(v->unsized).B(v->slotref).B(v->refrootknown)
            .B(v->contentbyteview).B(v->poolclass).B(v->growshrink).B(v->gsvia);
        ProvC(c, v->ref, v->isparam);
        RootsC(c, v->contents, v->isparam);
    }

    // What a body outside a variable's activation can read of it: how it was
    // declared, not how it stood at any call.
    void DeclaredVarC(Canon &c, const VarDef *v) {
        c.Str(names.Var(v)).Str(v->name).B(v->isvar).B(v->copybind).B(v->isparam).B(v->istemp)
            .I(v->reusable);
        ConstC(c, v);
        if (v->type) c.Dig(TypeD(v->type));
        else c.Tag('_');
    }

    // ---- the checked tree -------------------------------------------------

    class Tree {
        DepFinal &f;
        Canon &c;
        Canon &p;
        unordered_set<const VarDef *> seen;
        unordered_set<const TypeExpr *> &used;
        // The context whose body this is. Its own variables are written out
        // as the check left them; any other's, a global or one of a lexical
        // parent, only as declared: how the others' code used them is theirs.
        const FnSpec *owner;
        // The contexts the body's `return from` leaves to.
        unordered_set<const FnSpec *> &targets;

        void Collect(const TypeExpr *t, int depth = 0) {
            if (!t || depth > 8) return;
            switch (t->kind) {
                case TY_STRUCT:
                    used.insert(t);
                    for (auto a : t->struc->args) Collect(a, depth + 1);
                    break;
                case TY_ENUM:
                    used.insert(t);
                    for (auto a : t->enu->args) Collect(a, depth + 1);
                    break;
                case TY_VARIANT: Collect(t->var->adt, depth + 1); break;
                case TY_ARRAY: Collect(t->arr->sub, depth + 1); break;
                case TY_SLICE: Collect(t->sub, depth + 1); break;
                case TY_REF: Collect(t->ref->sub, depth + 1); break;
                case TY_FN:
                    for (auto a : t->fn->args) Collect(a, depth + 1);
                    for (auto a : t->fn->rets) Collect(a, depth + 1);
                    break;
                default: break;
            }
        }

        void Ty(const TypeExpr *t) {
            if (!t) { c.Tag('_'); return; }
            Collect(t);
            c.Dig(f.TypeD(t));
        }

        void Types(const vector<TypeExpr *> &v) {
            c.U(v.size());
            for (auto t : v) Ty(t);
        }

        void Var(const VarDef *v) {
            if (!v) { c.Tag('_'); return; }
            c.Str(f.names.Var(v));
            if (seen.insert(v).second) {
                c.Tag('+');
                if (owner && v->ownerspec == owner) f.VarC(c, v);
                else f.DeclaredVarC(c, v);
            }
        }

        void Vars(const vector<VarDef *> &v) {
            c.U(v.size());
            for (auto x : v) Var(x);
        }

        void Spec(const FnSpec *s) {
            if (!s) c.Tag('_');
            else c.Dig(f.Key(s));
        }

        // The context a `return from` leaves to. What the body checked is
        // that target's contract, which its base key says; which block it
        // runs is for the target to answer.
        void Target(const FnSpec *s) {
            if (!s) { c.Tag('_'); return; }
            targets.insert(s);
            c.Dig(f.keys.BaseKey(s));
        }

        void Decl(const SFunction *sf) {
            if (!sf) c.Tag('_');
            else c.Dig(f.keys.Decl(sf).digest);
        }

        void Kids(const vector<Node *> &v) {
            c.U(v.size());
            for (auto n : v) Walk(n);
        }

        void Variant(const SVariant *v) {
            if (!v) { c.Tag('_'); return; }
            auto it = f.variantindex.find(v);
            c.Str(v->name).I(it == f.variantindex.end() ? -1 : it->second);
        }

        void Inst(const StructInst *i) {
            if (!i) { c.Tag('_'); return; }
            c.Tag('I').U(i->args.size());
            for (auto a : i->args) Ty(a);
        }

        void Inst(const EnumInst *i) {
            if (!i) { c.Tag('_'); return; }
            c.Tag('I').U(i->args.size());
            for (auto a : i->args) Ty(a);
        }

        const Digest &Blob(const string *s) {
            auto it = f.blobs.find(s);
            if (it == f.blobs.end()) it = f.blobs.emplace(s, Sha256::Of(*s)).first;
            return it->second;
        }

    public:
        Tree(DepFinal &fin, Canon &content, Canon &positions, unordered_set<const TypeExpr *> &types,
             unordered_set<const FnSpec *> &returnsto, const FnSpec *spec)
            : f(fin), c(content), p(positions), used(types), owner(spec), targets(returnsto) {}

        void Walk(const Node *n) {
            if (!n) { c.Tag('_'); return; }
            c.Tag('N').U(n->nkind).B(n->nftemp);
            Ty(n->exprtype);
            p.U((uint64_t)n->line.line).Str(f.mods.ModuleOf(n->line.fileidx));
            switch (n->nkind) {
                case NK_IntLit: c.I(((const IntLit *)n)->val).B(((const IntLit *)n)->uns); break;
                case NK_FltLit: {
                    uint64_t bits;
                    memcpy(&bits, &((const FltLit *)n)->val, sizeof bits);
                    c.U(bits);
                    break;
                }
                case NK_BoolLit: c.B(((const BoolLit *)n)->val); break;
                case NK_StrLit: c.Str(((const StrLit *)n)->val); break;
                case NK_Ident: {
                    auto x = (const Ident *)n;
                    c.Str(x->name);
                    Var(x->vdef);
                    Decl(x->fnref);
                    break;
                }
                case NK_ArrayLit: {
                    auto x = (const ArrayLit *)n;
                    Kids(x->elems);
                    Walk(x->fillval);
                    Walk(x->fillcount);
                    Walk(x->capexpr);
                    break;
                }
                case NK_StructLit: {
                    auto x = (const StructLit *)n;
                    Ty(x->type);
                    Inst(x->sinst);
                    Inst(x->einst);
                    Variant(x->variant);
                    c.B(x->defaultall).B(x->implicit).U(x->fieldindices.size());
                    for (auto i : x->fieldindices) c.I(i);
                    c.U(x->sourcefieldindices.size());
                    for (auto i : x->sourcefieldindices) c.I(i);
                    c.U(x->inits.size());
                    for (auto &fi : x->inits) {
                        c.Str(fi.name).B(fi.fromdefault);
                        Walk(fi.val);
                    }
                    break;
                }
                case NK_Unary: {
                    auto x = (const Unary *)n;
                    c.I(x->op).B(x->synth).B(x->litfloat).B(x->flexint);
                    Walk(x->child);
                    break;
                }
                case NK_Binary: {
                    auto x = (const Binary *)n;
                    c.I(x->op).B(x->litfloat).B(x->flexint);
                    Vars(x->rightkills);
                    Walk(x->left);
                    Walk(x->right);
                    break;
                }
                case NK_Dot: {
                    auto x = (const Dot *)n;
                    c.Str(x->name).I(x->fieldidx).I(x->member);
                    Variant(x->variantconst);
                    Inst(x->einst);
                    Walk(x->obj);
                    break;
                }
                case NK_Call: {
                    auto x = (const Call *)n;
                    c.B(x->implicit).I(x->builtin).I(x->dispatcharg).I(x->firstdefault)
                        .I(x->ndefaults).B(x->poolcheck);
                    Spec(x->spec);
                    c.U(x->dispatch.size());
                    for (auto s : x->dispatch) Spec(s);
                    c.U(x->fmtspecs.size());
                    for (auto &[t, s] : x->fmtspecs) {
                        Ty(t);
                        Spec(s);
                    }
                    Types(x->rettypes);
                    Types(x->tyargs);
                    Vars(x->fvparams);
                    Decl(x->fvtarget);
                    if (x->shaderblob) c.Tag('b').Dig(Blob(x->shaderblob));
                    else c.Tag('_');
                    if (x->trailing) {
                        auto it = f.rec.funvals.find((const FunVal *)x->trailing->Origin());
                        if (it != f.rec.funvals.end()) c.Dig(it->second.text);
                    }
                    Walk(x->callee);
                    Kids(x->args);
                    Walk(x->fvbody);
                    Walk(x->defaultinit);
                    break;
                }
                case NK_Index: {
                    auto x = (const Index *)n;
                    Walk(x->obj);
                    Walk(x->idx);
                    break;
                }
                case NK_SliceExpr: {
                    auto x = (const SliceExpr *)n;
                    c.B(x->lo_from_end).B(x->hi_from_end).B(x->cmpview);
                    Walk(x->obj);
                    Walk(x->lo);
                    Walk(x->hi);
                    break;
                }
                case NK_AsCast: {
                    auto x = (const AsCast *)n;
                    c.B(x->unchecked).B(x->implicit);
                    Ty(x->totype);
                    Walk(x->child);
                    break;
                }
                case NK_RangeExpr: {
                    auto x = (const RangeExpr *)n;
                    Walk(x->lo);
                    Walk(x->hi);
                    break;
                }
                case NK_Block: {
                    auto x = (const Block *)n;
                    Kids(x->stmts);
                    Walk(x->tail);
                    break;
                }
                case NK_IfExpr: {
                    auto x = (const IfExpr *)n;
                    c.B(x->flat);
                    Walk(x->cond);
                    Walk(x->thenb);
                    Walk(x->elseb);
                    break;
                }
                case NK_MatchExpr: {
                    auto x = (const MatchExpr *)n;
                    Walk(x->scrutinee);
                    c.U(x->arms.size());
                    for (auto &arm : x->arms) {
                        c.I(arm.pat.kind).B(arm.pat.byref).U(arm.pat.items.size());
                        for (auto &pi : arm.pat.items) {
                            Walk(pi.lo);
                            Walk(pi.hi);
                        }
                        c.U(arm.variants.size());
                        for (auto v : arm.variants) Variant(v);
                        Var(arm.binder);
                        c.U(arm.ranges.size());
                        for (auto &r : arm.ranges) c.I(r.lo).I(r.hi);
                        Walk(arm.body);
                    }
                    break;
                }
                case NK_EarlyBlock: {
                    auto x = (const EarlyBlock *)n;
                    c.U(x->breaks.size());
                    Walk(x->body);
                    break;
                }
                case NK_While: {
                    auto x = (const While *)n;
                    Walk(x->cond);
                    Walk(x->body);
                    break;
                }
                case NK_LoopExpr: {
                    auto x = (const LoopExpr *)n;
                    c.U(x->breaks.size());
                    Walk(x->body);
                    break;
                }
                case NK_ForLoop: {
                    auto x = (const ForLoop *)n;
                    c.B(x->byref).I(x->iterkind);
                    Var(x->vdef);
                    Var(x->idxdef);
                    Walk(x->iter);
                    Walk(x->body);
                    break;
                }
                case NK_Return: {
                    auto x = (const Return *)n;
                    Decl(x->target);
                    Target(x->targetspec);
                    Kids(x->vals);
                    break;
                }
                case NK_Break: Walk(((const Break *)n)->val); break;
                case NK_FunVal: {
                    // A block passed as an argument: the callee checks its
                    // text, so here it is only the text.
                    auto it = f.rec.funvals.find((const FunVal *)n->Origin());
                    if (it != f.rec.funvals.end()) c.Dig(it->second.text);
                    break;
                }
                case NK_VarDecl: {
                    auto x = (const VarDecl *)n;
                    c.B(x->isvar).B(x->isconst).I(x->reusable).B(x->byref).B(x->inline_arg);
                    Vars(x->defs);
                    Kids(x->inits);
                    break;
                }
                case NK_Assign: {
                    auto x = (const Assign *)n;
                    c.I(x->op).B(x->pointee);
                    Walk(x->lval);
                    Walk(x->rhs);
                    break;
                }
                case NK_IncDec: {
                    auto x = (const IncDec *)n;
                    c.I(x->op);
                    Walk(x->lval);
                    break;
                }
                case NK_FnDecl: Decl(((const FnDecl *)n)->sf); break;
                case NK_StructDecl: case NK_EnumDecl: case NK_AliasDecl:
                case NK_NullLit: case NK_SelfRef: case NK_Continue: case NK_InlineBlock: break;
            }
        }
    };

    // ---- summaries --------------------------------------------------------

    void EnvReadC(Canon &c, const EnvRead &r) {
        c.Str(names.Var(r.var)).B(r.assigned).B(r.maybeassigned).B(r.refrootknown);
        ProvC(c, r.ref);
        RootsC(c, r.contents);
        c.B(r.contentbyteview).B(r.slotref);
    }

    void StoreC(Canon &c, const StoreEvent &e) {
        c.Str(names.Var(e.container)).Str(names.Var(e.root)).Str(names.Var(e.src)).B(e.exact)
            .B(e.byteview).B(e.bound).B(e.slot).B(e.sliceref).B(e.classread);
        if (e.pointee) c.Dig(TypeD(e.pointee));
        else c.Tag('_');
        if (e.reached) c.Dig(TypeD(e.reached));
        else c.Tag('_');
    }

    template<typename Map> void BalanceC(Canon &c, const Map &m) {
        vector<string> out;
        for (auto &[k, b] : m) {
            Canon x;
            if constexpr (is_pointer_v<remove_cvref_t<decltype(k)>>) x.Str(names.Var(k));
            else x.I(k);
            x.I(b);
            out.push_back(x.Text());
        }
        sort(out.begin(), out.end());
        c.U(out.size());
        for (auto &o : out) c.Str(o);
    }

    template<typename K> void BoundsC(Canon &c, const vector<BoundShrink<K>> &v) {
        vector<string> out;
        for (auto &b : v) {
            Canon x;
            if constexpr (is_pointer_v<K>) x.Str(names.Var(b.key));
            else x.I(b.key);
            x.I(b.balance);
            if (b.type) x.Dig(TypeD(b.type));
            out.push_back(x.Text());
        }
        sort(out.begin(), out.end());
        c.U(out.size());
        for (auto &o : out) c.Str(o);
    }

    // What a call to the context can come to know of it besides its
    // signature: what it shrinks, grows, writes through, rebinds and stores,
    // what it reads of and leaves in the variables around it, and where its
    // returns point.
    Digest SummaryOf(const FnSpec *s) {
        auto it = summaries.find(s);
        if (it != summaries.end()) return it->second;
        Canon c;
        auto &r = s->record;
        c.Tag('M').B(r.mayreturn).U(r.retroots.size());
        for (auto &rr : r.retroots) {
            RootsC(c, rr.alts);
            c.B(rr.writable).B(rr.byteview).B(rr.freshview).B(rr.set);
        }
        {
            vector<string> v;
            for (auto x : r.reboundoptionals) v.push_back(names.Var(x));
            sort(v.begin(), v.end());
            c.U(v.size());
            for (auto &x : v) c.Str(x);
        }
        BalanceC(c, r.shrinkexternals);
        BalanceC(c, r.shrinkparams);
        BoundsC(c, r.shrinkexternalbounds);
        BoundsC(c, r.shrinkparambounds);
        c.U(r.liveshrinks.size());
        for (auto &l : r.liveshrinks) {
            c.Str(names.Var(l.shrunk)).B(l.shrunkexact).Str(names.Var(l.live)).B(l.liveexact)
                .B(l.byteview).B(l.growonly).Str(l.name).B(l.contents).B(l.inplace);
            for (auto t : { l.bound, l.pointee }) {
                if (t) c.Dig(TypeD(t));
                else c.Tag('_');
            }
        }
        {
            auto types = [&](Canon &out, const vector<TypeExpr *> &arrays) {
                vector<string> v;
                for (auto t : arrays) {
                    Canon x;
                    if (t) x.Dig(TypeD(t));
                    else x.Tag('_');
                    v.push_back(x.Text());
                }
                sort(v.begin(), v.end());
                v.erase(unique(v.begin(), v.end()), v.end());
                out.U(v.size());
                for (auto &x : v) out.Str(x);
            };
            vector<string> v;
            for (auto &[root, arrays] : r.growexternals) {
                Canon x;
                x.Str(names.Var(root));
                types(x, arrays);
                v.push_back(x.Text());
            }
            sort(v.begin(), v.end());
            c.U(v.size());
            for (auto &x : v) c.Str(x);
            c.U(r.growparams.size());
            for (auto &[i, arrays] : r.growparams) {
                c.I(i);
                types(c, arrays);
            }
        }
        {
            vector<string> v;
            for (auto x : r.writeexternals) v.push_back(names.Var(x));
            sort(v.begin(), v.end());
            c.U(v.size());
            for (auto &x : v) c.Str(x);
            c.U(r.writeparams.size());
            for (auto i : r.writeparams) c.I(i);
        }
        {
            vector<string> stores;
            for (auto &e : r.classevents) {
                Canon x;
                StoreC(x, e);
                stores.push_back(x.Text());
            }
            sort(stores.begin(), stores.end());
            stores.erase(unique(stores.begin(), stores.end()), stores.end());
            c.U(stores.size());
            for (auto &x : stores) c.Str(x);
        }
        for (auto *list : { &s->envreads, &s->envexits }) {
            vector<string> v;
            for (auto &e : *list) {
                Canon x;
                EnvReadC(x, e);
                v.push_back(x.Text());
            }
            sort(v.begin(), v.end());
            c.U(v.size());
            for (auto &x : v) c.Str(x);
        }
        for (auto &oe : s->outerexits) {
            c.Dig(keys.BaseKey(oe.target));
            for (auto *set : { &oe.assigned, &oe.maybeassigned }) {
                vector<string> v;
                for (auto x : *set) v.push_back(names.Var(x));
                sort(v.begin(), v.end());
                c.U(v.size());
                for (auto &x : v) c.Str(x);
            }
        }
        {
            vector<Digest> need;
            for (auto t : s->needs) need.push_back(keys.BaseKey(t));
            sort(need.begin(), need.end());
            c.U(need.size());
            for (auto &d : need) c.Dig(d);
        }
        c.B(s->storesout).B(s->relnamedresult).B(s->incycle);
        c.U(s->litparams.size());
        for (auto i : s->litparams) c.I(i);
        c.U(s->litadapts.size());
        for (auto &la : s->litadapts) {
            c.I(la.param);
            if (la.type) c.Dig(TypeD(la.type));
        }
        c.U(s->litflows.size());
        for (auto &lf : s->litflows) c.I(lf.param).Dig(Key(lf.to)).I(lf.toparam);
        return summaries[s] = c.Hash();
    }

    // What a caller reads of the context's signature: its result types, the
    // roots its returns lead to and whether it can return at all. The
    // declaration's own text, which the caller also reads, is `sig`.
    Digest InterfaceOf(const FnSpec *s, bool withdecl) {
        auto cached = interfaces.find({ s, withdecl });
        if (cached != interfaces.end()) return cached->second;
        Canon c;
        c.Tag('J').Dig(Key(s)).B(s->retsknown).U(s->rets.size());
        for (auto t : s->rets) c.Dig(TypeD(t));
        c.B(s->record.mayreturn).U(s->record.retroots.size());
        for (auto &rr : s->record.retroots) {
            RootsC(c, rr.alts);
            c.B(rr.writable).B(rr.byteview).B(rr.freshview).B(rr.set);
        }
        if (withdecl) {
            auto d = rec.decls.find(s->sf);
            if (d != rec.decls.end()) c.Dig(d->second.sig);
        }
        return c.Hash();
    }

    // ---- layouts, lookups -------------------------------------------------

    static bool Nominal(const TypeExpr *t) {
        return t->kind == TY_STRUCT || t->kind == TY_ENUM || t->kind == TY_VARIANT;
    }

    // Nominal types held by value: what a type's size and class are made of.
    void HeldNominals(const TypeExpr *t, vector<const TypeExpr *> &out, int depth = 0) {
        if (!t || depth > 16) return;
        if (t->kind == TY_ARRAY) { HeldNominals(t->arr->sub, out, depth + 1); return; }
        if (Nominal(t)) out.push_back(t);
    }

    // What the checker can read of a struct or enum: how it was declared, the
    // classes it settled on, and the same of everything it holds by value.
    Digest LayoutOf(const TypeExpr *t) {
        if (t->kind == TY_VARIANT) t = t->var->adt;
        auto key = TypeD(t);
        auto it = layouts.find(key);
        if (it != layouts.end()) return it->second;
        if (!layingout.insert(key).second) return Canon().Tag('^').Hash();
        Canon c;
        c.Tag('Y').Dig(key);
        vector<const TypeExpr *> held;
        if (t->kind == TY_STRUCT) {
            auto st = t->struc->st;
            if (auto d = rec.structtext.find(st); d != rec.structtext.end()) c.Dig(d->second);
            if (auto i = t->struc->inst) {
                c.B(true).I(i->sclass).B(i->flat).B(i->frameobj);
                c.U(i->ftypes.size());
                for (auto ft : i->ftypes) {
                    if (ft) {
                        c.Dig(TypeD(ft));
                        HeldNominals(ft, held);
                    } else {
                        c.Tag('_');
                    }
                }
            } else {
                c.B(false);
            }
        } else if (t->kind == TY_ENUM) {
            auto en = t->enu->en;
            if (auto d = rec.enumtext.find(en); d != rec.enumtext.end()) c.Dig(d->second);
            if (auto i = t->enu->inst) {
                c.B(true).I(i->varclass).B(i->allfixed).B(i->selfrel).B(i->flat);
                c.U(i->vftypes.size());
                for (auto &vf : i->vftypes) {
                    c.U(vf.size());
                    for (auto ft : vf) {
                        if (ft) {
                            c.Dig(TypeD(ft));
                            HeldNominals(ft, held);
                        } else {
                            c.Tag('_');
                        }
                    }
                }
            } else {
                c.B(false);
            }
        }
        c.U(held.size());
        for (auto h : held) c.Dig(LayoutOf(h));
        layingout.erase(key);
        return layouts[key] = c.Hash();
    }

    Digest GlobalOf(const VarDecl *g) {
        auto cached = globals.find(g);
        if (cached != globals.end()) return cached->second;
        Canon c;
        c.Tag('Z');
        if (auto it = rec.globalfacts.find(g); it != rec.globalfacts.end()) c.Dig(it->second.readable);
        c.U(g->defs.size());
        for (auto d : g->defs) DeclaredVarC(c, d);
        return globals[g] = c.Hash();
    }

    Digest FunctionSetOf(const vector<SFunction *> &set) {
        Canon c;
        c.U(set.size());
        for (auto sf : set) {
            c.Dig(keys.Decl(sf).digest);
            if (auto d = rec.decls.find(sf); d != rec.decls.end()) c.Dig(d->second.sig);
        }
        return c.Hash();
    }

    // The candidates a name has where the checker looked it up: the first
    // namespace that declares it at all, as Ast::Lookup finds it, and what is
    // declared there. A name found nowhere has a digest of its own.
    Digest LookupOf(DepLookup table, string_view name, string_view usens) {
        auto memo = cat((int)table, "|", usens, "|", name);
        auto cached = lookups.find(memo);
        if (cached != lookups.end()) return cached->second;
        return lookups[memo] = CandidatesOf(table, name, usens);
    }

    Digest CandidatesOf(DepLookup table, string_view name, string_view usens) {
        auto ref = SplitName(name, usens);
        Canon c;
        c.Tag('Q').I((int)table);
        for (int stage = 0; stage < 2; stage++) {
            auto nsname = stage == 0 ? ref.ns : string_view();
            if (stage == 1 && (ref.qualified || ref.ns.empty())) break;
            auto n = ast.FindNS(nsname);
            if (!n) continue;
            switch (table) {
                case DepLookup::Function: {
                    auto it = n->functionmap.find(ref.leaf);
                    if (it == n->functionmap.end()) continue;
                    c.Tag('f').Str(nsname).Dig(FunctionSetOf(it->second));
                    return c.Hash();
                }
                case DepLookup::Global: {
                    auto it = n->globalmap.find(ref.leaf);
                    if (it == n->globalmap.end()) continue;
                    c.Tag('g').Str(nsname).Dig(GlobalOf(it->second));
                    return c.Hash();
                }
                default: {
                    // Structs, enums and aliases share one namespace of names.
                    if (!n->TypeNameExists(ref.leaf)) continue;
                    c.Tag('t').Str(nsname);
                    if (auto it = n->structmap.find(ref.leaf); it != n->structmap.end())
                        c.Tag('S').Dig(rec.structtext[it->second]);
                    if (auto it = n->enummap.find(ref.leaf); it != n->enummap.end())
                        c.Tag('E').Dig(rec.enumtext[it->second]);
                    if (auto it = n->aliasmap.find(ref.leaf); it != n->aliasmap.end())
                        c.Tag('A').Dig(rec.aliastext[it->second]);
                    return c.Hash();
                }
            }
        }
        c.Tag('0');
        return c.Hash();
    }

    // A path named from the program's own directory where it lies under it.
    string ProgramRelative(const string &path) {
        auto &root = ast.sources[0].first;
        auto slash = root.find_last_of("/\\");
        auto dir = slash == string::npos ? string() : root.substr(0, slash + 1);
        if (!dir.empty() && path.compare(0, dir.size(), dir) == 0) return path.substr(dir.size());
        return path;
    }

    // ---- a context --------------------------------------------------------

    void Add(DepContext &ctx, DepKind kind, string subject, const Digest &d) {
        ctx.deps.push_back({ kind, std::move(subject), d });
    }

    // Everything the events say about what a context consulted.
    void EventDeps(DepContext &ctx, const DepEvents &ev, unordered_set<const TypeExpr *> &types,
                   const FnSpec *self) {
        for (auto callee : ev.callees) {
            // A call back into the context itself is a fact about the
            // context, not a dependency on another.
            if (!callee->sf || callee == self) continue;
            auto key = Key(callee).Stored();
            Add(ctx, DepKind::Requests, cat("context:", key), Key(callee));
            Add(ctx, DepKind::Interface, cat("context:", key), InterfaceOf(callee, true));
            Add(ctx, DepKind::Summary, cat("context:", key), SummaryOf(callee));
        }
        for (auto &[table, name, ns] : ev.lookups)
            Add(ctx, DepKind::Lookup, cat(DepLookupName((DepLookup)table), ":", ns, "|", name),
                LookupOf((DepLookup)table, name, ns));
        for (auto t : ev.types) types.insert(t);
        for (auto &r : ev.resources)
            Add(ctx, DepKind::Resource, cat(r.kind, ":", ProgramRelative(r.subject)), r.content);
        for (auto fv : ev.funvals) {
            auto it = rec.funvals.find(fv);
            if (it == rec.funvals.end()) continue;
            auto &f = it->second;
            string owner = f.owner ? keys.Decl(f.owner).digest.Stored()
                                   : cat("global:", globalkeys[f.ownerglobal].Stored());
            auto subject = cat("block:", owner, "#", f.ordinal);
            Add(ctx, DepKind::Body, subject, f.text);
            Add(ctx, DepKind::Location, subject, f.loc);
        }
        for (auto v : ev.envvars) {
            Canon c;
            DeclaredVarC(c, v);
            Add(ctx, DepKind::Environment, cat("variable:", names.Var(v)), c.Hash());
        }
        // What the check found of each global's provenance. Only this
        // context's own check can say it again, so it is an observation, not
        // a fact about the program: the subject is named for what was seen.
        for (auto &[v, states] : ev.globalstates) {
            Canon c;
            c.U(states.size());
            for (auto &st : states) {
                ProvC(c, st.ref);
                RootsC(c, st.contents);
                c.B(st.refrootknown).B(st.slotref).B(st.contentbyteview);
            }
            Add(ctx, DepKind::Environment, cat("observed:", names.Var(v)), c.Hash());
        }
    }

    void TypeDeps(DepContext &ctx, unordered_set<const TypeExpr *> &types) {
        unordered_set<Digest, DigestHash> done;
        for (auto t : types) {
            if (!Nominal(t)) continue;
            auto key = TypeD(t->kind == TY_VARIANT ? t->var->adt : t);
            if (!done.insert(key).second) continue;
            Add(ctx, DepKind::Layout, cat("type:", key.Stored()), LayoutOf(t));
        }
    }

public:
    vector<DepContext> out;

    DepFinal(Ast &a, KeyMaker &k, DepRecorder &r)
        : ast(a), keys(k), rec(r), mods(k, a.sources.size()), names(a, k, mods) {
        for (auto en : ast.enums)
            for (size_t i = 0; i < en->variants.size(); i++) variantindex[&en->variants[i]] = (int)i;
        map<string, int> seen;
        for (auto g : ast.globals) {
            Canon k;
            k.Tag('G').Str(mods.ModuleOf(g->line.fileidx)).Str(g->ns).U(g->names.size());
            for (auto nm : g->names) k.Str(nm);
            auto spelling = k.Text();
            k.I(seen[spelling]++);
            globalkeys[g] = k.Hash();
        }
        for (auto s : ast.fnspecs) {
            if (!s->sf) continue;
            if (s->incycle) groups[HeadOf(s)].push_back(s);
            // A nested function belongs to the activation it is declared in,
            // however many blocks stand between.
            auto up = s->lexparent;
            while (up && up->isfunval) up = up->lexparent;
            if (up) nested[up].push_back(s);
        }
    }

    // The callee-side facts that flow back from call sites: which arguments
    // the call sites agreed were exact and concrete arrays. They are settled
    // after every context is checked and are not part of any one result.
    Digest CallerFacts(const FnSpec *s) {
        Canon c;
        c.Tag('P').U(s->roots.size());
        for (auto &r : s->roots) c.B(r.exact).B(r.concrete);
        for (auto &r : s->views) c.B(r.exact).B(r.concrete);
        for (auto p : s->params) {
            Canon x;
            ProvC(x, p->ref);
            c.Dig(x.Hash());
        }
        return c.Hash();
    }

    void Function(const FnSpec *s) {
        DepContext ctx;
        auto &key = keys.Context(s);
        ctx.key = key.total;
        ctx.decl = key.decl;
        ctx.sf = s->sf;
        auto ev = rec.specs.find(s);
        static const DepEvents none;
        auto &events = ev == rec.specs.end() ? none : ev->second;

        Canon rc, pc;
        unordered_set<const TypeExpr *> types;
        unordered_set<const FnSpec *> targets;
        rc.Tag('R').Dig(InterfaceOf(s, false)).Dig(SummaryOf(s));
        {
            Canon tc;
            Tree tree(*this, tc, pc, types, targets, s);
            tree.Walk(s->body);
            rc.Dig(tc.Hash());
        }
        for (auto p : s->params) {
            Canon x;
            VarC(x, p);
            rc.Dig(x.Hash());
        }
        rc.U(events.warnings.size());
        for (auto &[code, msg] : events.warnings) rc.I(code).Str(msg);
        rc.U(events.verdicts.size());
        for (auto &[red, text] : events.verdicts) rc.B(red).Str(text);
        ctx.result = rc.Hash();
        ctx.positions = pc.Hash();
        ctx.callers = CallerFacts(s);

        if (auto d = rec.decls.find(s->sf); d != rec.decls.end()) {
            Add(ctx, DepKind::Body, cat("declaration:", ctx.decl.Stored()), d->second.body);
            Add(ctx, DepKind::Location, cat("declaration:", ctx.decl.Stored()), d->second.loc);
        }
        Add(ctx, DepKind::Resource, cat("module:", mods.ModuleOf(s->sf->line.fileidx)),
            ModuleIdentity(s->sf->line.fileidx));
        EventDeps(ctx, events, types, s);
        // The contracts of the contexts it returns to.
        for (auto t : s->needs) targets.insert(t);
        for (auto &oe : s->outerexits) targets.insert(oe.target);
        targets.erase(s);
        for (auto t : targets) {
            if (!t->sf) continue;
            Canon x;
            x.Tag('K').B(t->retsknown).U(t->rets.size());
            for (auto r : t->rets) x.Dig(TypeD(r));
            Add(ctx, DepKind::Summary, cat("target:", keys.BaseKey(t).Stored()), x.Hash());
        }
        if (s->incycle) {
            auto &members = groups[HeadOf(s)];
            Canon g;
            g.Tag('W');
            vector<string> rows;
            for (auto m : members) {
                Canon x;
                x.Dig(Key(m)).Dig(SummaryOf(m)).Dig(InterfaceOf(m, true));
                if (auto d = rec.decls.find(m->sf); d != rec.decls.end()) x.Dig(d->second.body);
                rows.push_back(x.Text());
            }
            sort(rows.begin(), rows.end());
            g.U(rows.size());
            for (auto &r : rows) g.Str(r);
            Add(ctx, DepKind::Summary, cat("cycle:", Key(HeadOf(s)).Stored()), g.Hash());
        }
        // The environment: what the functions and blocks declared in this
        // activation made of its variables, and what they leave in them.
        if (auto it = nested.find(s); it != nested.end()) {
            for (auto child : it->second) {
                Canon x;
                x.Dig(SummaryOf(child)).U(child->envreads.size());
                for (auto &e : child->envreads) EnvReadC(x, e);
                Add(ctx, DepKind::Environment, cat("nested:", Key(child).Stored()), x.Hash());
            }
        }
        TypeDeps(ctx, types);
        out.push_back(std::move(ctx));
    }

    Digest ModuleIdentity(int fileidx) {
        Canon c;
        c.Tag('m');
        if (fileidx >= 0 && (size_t)fileidx < ast.filepkg.size() && ast.filepkg[fileidx] >= 0) {
            auto &pkg = ast.packages[ast.filepkg[fileidx]];
            c.Str(pkg.name).B(pkg.stdlib).Str(pkg.cachekey);
        }
        return c.Hash();
    }

    void Global(const VarDecl *g) {
        DepContext ctx;
        ctx.global = true;
        ctx.name = cat("global ", g->names.empty() ? string_view("?") : g->names[0]);
        ctx.key = ctx.decl = globalkeys[g];
        auto ev = rec.globals.find(g);
        static const DepEvents none;
        auto &events = ev == rec.globals.end() ? none : ev->second;

        Canon rc, pc;
        unordered_set<const TypeExpr *> types;
        rc.Tag('R');
        {
            Canon tc;
            unordered_set<const FnSpec *> returnsto;
            Tree tree(*this, tc, pc, types, returnsto, nullptr);
            for (auto init : g->inits) tree.Walk(init);
            rc.Dig(tc.Hash());
        }
        // What other contexts stored into a global is theirs, so only how it
        // was declared.
        for (auto d : g->defs) {
            Canon x;
            DeclaredVarC(x, d);
            rc.Dig(x.Hash());
        }
        rc.U(events.warnings.size());
        for (auto &[code, msg] : events.warnings) rc.I(code).Str(msg);
        rc.U(events.verdicts.size());
        for (auto &[red, text] : events.verdicts) rc.B(red).Str(text);
        ctx.result = rc.Hash();
        ctx.positions = pc.Hash();
        if (auto d = rec.globalfacts.find(g); d != rec.globalfacts.end()) {
            Add(ctx, DepKind::Body, cat("global:", ctx.key.Stored()), d->second.text);
            Add(ctx, DepKind::Location, cat("global:", ctx.key.Stored()), d->second.loc);
        }
        Add(ctx, DepKind::Resource, cat("module:", mods.ModuleOf(g->line.fileidx)),
            ModuleIdentity(g->line.fileidx));
        EventDeps(ctx, events, types, nullptr);
        TypeDeps(ctx, types);
        out.push_back(std::move(ctx));
    }
};

// Run once the checker has finished and before the optimizer rewrites what it
// left: every dependency of every context, as digests.
inline void DepsAfterCheck(Ast &ast, KeyMaker &keys) {
    auto &rec = *g_deps;
    rec.frontend = false;
    DepFinal fin(ast, keys, rec);
    for (auto s : ast.fnspecs)
        if (s->sf) fin.Function(s);
    for (auto g : ast.globals) fin.Global(g);
    rec.contexts = std::move(fin.out);
}

}  // namespace goose
