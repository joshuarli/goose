// Stable keys: SHA-256 against published vectors, and the canonical forms of
// DeclKey, TypeKey and ContextKey. A key must change when what it names
// changes and must not change when only its surroundings do. Keep assertions
// active even in an optimized test build.
#ifdef NDEBUG
#undef NDEBUG
#endif
#include "../src/includes.h"
#include "../src/utils.h"
#include "../src/small_vector.h"
#include "../src/lexer.h"
#include "../src/ast.h"
#include "../src/ident/keys.h"
#include "../src/ident/deps.h"

using namespace goose;

void ConstFor::Dump(string &, int) const {}
Node *ConstFor::Clone1(Ast &) const { return nullptr; }
void ConstFor::Children(const function<void(Node *)> &) const {}
Val ConstFor::Check(TypeCheck &, TypeExpr *) { return {}; }
Node *ConstFor::Cp1(Inliner &) const { return nullptr; }
Node *ConstFor::Opt(Optimizer &) { return nullptr; }
string ConstFor::CgX(CodeGen &) { return {}; }
void ConstFor::CgAny(CodeGen &, const Dst &) {}
void ConstFor::CgStmt(CodeGen &) {}
bool Node::BceWalk(BCE &) { return true; }
void Node::BceMark(BCE &) {}

static string Sha(string_view s) { return Sha256::Of(s).Hex(); }

static void TestSha256() {
    // FIPS 180-4 examples.
    assert(Sha("") == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert(Sha("abc") == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert(Sha("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
           "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1");
    assert(Sha("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") ==
           "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1");
    // Lengths around the padding boundaries, from a reference implementation.
    struct Case { size_t n; const char *hex; };
    for (auto &c : { Case { 55, "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318" },
                     Case { 56, "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a" },
                     Case { 63, "7d3e74a05d7db15bce4ad9ec0658ea98e3f06eeecf16b4c6fff2da457ddc2f34" },
                     Case { 64, "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb" },
                     Case { 65, "635361c48bb9eab14198e76ea8ab7f1a41685d6ad62aa9146d301d4f17eb0ae0" },
                     Case { 119, "31eba51c313a5c08226adf18d4a359cfdfd8d2e816b13f4af952f7ea6584dcfb" },
                     Case { 120, "2f3d335432c70b580af0e8e1b3674a7c020d683aa5f73aaaedfdc55af904c21c" } })
        assert(Sha(string(c.n, 'a')) == c.hex);
    // One million 'a', fed in uneven pieces.
    Sha256 sha;
    string piece(997, 'a');
    size_t left = 1000000;
    while (left) {
        auto n = min(left, piece.size());
        sha.Update(piece.data(), n);
        left -= n;
    }
    assert(sha.Final().Hex() == "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
    // Short and stored forms are prefixes.
    auto d = Sha256::Of("abc");
    assert(d.Short() == "ba7816bf8f01cfea");
    assert(d.Stored() == "ba7816bf8f01cfea414140de5dae2223");
}

static void TestCanon() {
    // A length prefix keeps neighbouring strings apart.
    assert(Canon().Str("ab").Str("c").Hash() != Canon().Str("a").Str("bc").Hash());
    assert(Canon().Str("ab").Str("c").Hash() == Canon().Str("ab").Str("c").Hash());
    // Order and kind of field matter.
    assert(Canon().U(1).U(2).Hash() != Canon().U(2).U(1).Hash());
    assert(Canon().U(12).Hash() != Canon().U(1).U(2).Hash());
    assert(Canon().Tag('a').Hash() != Canon().Tag('b').Hash());
    assert(Canon().B(true).Hash() != Canon().B(false).Hash());
}

// A program the tests can describe without parsing one.
struct Program {
    Ast ast;
    Program() {
        ast.sources.emplace_back("proj/main.goose", make_unique<string>());
        ast.sources.emplace_back("proj/util.goose", make_unique<string>());
        ast.packages.push_back(Package { "app", "proj/", false });
        ast.filepkg = { 0, 0 };
    }
    SFunction *Fn(string_view name, vector<TypeExpr *> params, int line = 1, int file = 0,
                  string_view ns = "") {
        auto sf = new SFunction();
        sf->name = name;
        sf->ns = ns;
        sf->qname = name;
        sf->line = Line { line, file };
        for (auto t : params) sf->params.push_back(Param { "p", Line {}, t });
        ast.functions.push_back(sf);
        return sf;
    }
    TypeExpr *I(IntStorage s) { return ast.inttypes[s]; }
    TypeExpr *Slice(TypeExpr *e) { return ast.SliceOf(e, Line {}); }
};

static void TestDeclKey() {
    Program a;
    auto f = a.Fn("sum", { a.Slice(a.I(IS_I64)) }, 10);
    KeyMaker ka(a.ast);
    auto base = ka.Decl(f).digest;

    // Unrelated edits: another function appears first, lines move, the
    // declaration moves within its file.
    Program b;
    b.Fn("other", {}, 3);
    b.Fn("another", { b.I(IS_U8) }, 4);
    auto g = b.Fn("sum", { b.Slice(b.I(IS_I64)) }, 99);
    KeyMaker kb(b.ast);
    assert(kb.Decl(g).digest == base);

    // Renaming, another module, another namespace, another written
    // parameter type: each is a different declaration.
    Program c;
    auto renamed = c.Fn("total", { c.Slice(c.I(IS_I64)) });
    auto moved = c.Fn("sum", { c.Slice(c.I(IS_I64)) }, 10, 1);
    auto spaced = c.Fn("sum", { c.Slice(c.I(IS_I64)) }, 10, 0, "geo");
    auto retyped = c.Fn("sum", { c.Slice(c.I(IS_I32)) });
    auto arity = c.Fn("sum", {});
    KeyMaker kc(c.ast);
    for (auto x : { renamed, moved, spaced, retyped, arity }) assert(kc.Decl(x).digest != base);

    // Nested functions: the enclosing declaration and the ordinal among
    // same-named siblings, not the position in the table.
    Program d;
    auto outer = d.Fn("run", {});
    auto n0 = d.Fn("step", {}), n1 = d.Fn("step", {}), m0 = d.Fn("walk", {});
    for (auto n : { n0, n1, m0 }) { n->isnested = true; n->outer = outer; }
    KeyMaker kd(d.ast);
    assert(kd.Decl(n0).digest != kd.Decl(n1).digest);
    assert(kd.Decl(n0).digest != kd.Decl(m0).digest);
    // An unrelated function inserted before them changes none of the three.
    Program e;
    e.Fn("unrelated", {});
    auto outer2 = e.Fn("run", {});
    auto p0 = e.Fn("step", {}), p1 = e.Fn("step", {}), q0 = e.Fn("walk", {});
    for (auto n : { p0, p1, q0 }) { n->isnested = true; n->outer = outer2; }
    KeyMaker ke(e.ast);
    assert(ke.Decl(p0).digest == kd.Decl(n0).digest);
    assert(ke.Decl(p1).digest == kd.Decl(n1).digest);
    assert(ke.Decl(q0).digest == kd.Decl(m0).digest);
    // The same name under another outer function is another declaration.
    auto other = e.Fn("run2", {});
    auto r0 = e.Fn("step", {});
    r0->isnested = true;
    r0->outer = other;
    KeyMaker kf(e.ast);
    assert(kf.Decl(r0).digest != kf.Decl(p0).digest);
}

static void TestTypeKey() {
    Program a;
    KeyMaker k(a.ast);
    // Structural: two separately built slices of i64 are one type.
    assert(k.Type(a.Slice(a.I(IS_I64))).digest == k.Type(a.Slice(a.I(IS_I64))).digest);
    assert(k.Type(a.Slice(a.I(IS_I64))).digest != k.Type(a.Slice(a.I(IS_I32))).digest);
    assert(k.Type(a.I(IS_I64)).digest != k.Type(a.I(IS_U64)).digest);
    auto array_a = a.ast.NewVarDef();
    array_a->name = "a";
    array_a->isglobal = true;
    array_a->line = Line { 1, 0 };
    auto array_b = a.ast.NewVarDef();
    array_b->name = "b";
    array_b->isglobal = true;
    array_b->line = Line { 2, 0 };
    auto index_a = a.ast.IndexTypeOf(IS_U32, array_a, false, Line {});
    auto index_b = a.ast.IndexTypeOf(IS_U32, array_b, false, Line {});
    auto bound_a = a.ast.IndexTypeOf(IS_U32, array_a, true, Line {});
    assert(k.Type(index_a).digest != k.Type(index_b).digest);
    assert(k.Type(index_a).digest != k.Type(bound_a).digest);
    // `const` is part of the identity.
    auto cs = a.Slice(a.I(IS_I64));
    auto cc = a.Slice(a.I(IS_I64));
    cc->cq = true;
    assert(k.Type(cs).digest != k.Type(cc).digest);
    // Nominal: the declaration and the argument types.
    auto st = new SStruct();
    st->name = st->qname = "Point";
    st->line = Line { 1, 0 };
    a.ast.structs.push_back(st);
    auto sub = a.ast.StructOf(st, {}, Line {});
    auto arg = a.ast.StructOf(st, { a.I(IS_I64) }, Line {});
    assert(k.Type(sub).digest != k.Type(arg).digest);
    assert(k.Type(arg).digest == k.Type(a.ast.StructOf(st, { a.I(IS_I64) }, Line {})).digest);
    // The same struct declared in another file is another type; moving it
    // within its file is not.
    Program b;
    auto st2 = new SStruct();
    st2->name = st2->qname = "Point";
    st2->line = Line { 40, 0 };
    b.ast.structs.push_back(st2);
    KeyMaker kb(b.ast);
    assert(kb.Type(b.ast.StructOf(st2, {}, Line {})).digest == k.Type(sub).digest);
    st2->line = Line { 40, 1 };
    KeyMaker kb2(b.ast);
    assert(kb2.Type(b.ast.StructOf(st2, {}, Line {})).digest != k.Type(sub).digest);
}

static Digest WrittenTypeDigest(Program &p, TypeExpr *type) {
    KeyMaker keys(p.ast);
    DepModules modules(keys, p.ast.sources.size());
    Canon content, positions;
    DepAst(modules, content, positions).Type(type);
    return content.Hash();
}

static Digest WrittenSignatureDigest(Program &p, SFunction *sf) {
    KeyMaker keys(p.ast);
    DepModules modules(keys, p.ast.sources.size());
    Canon content, positions;
    DepAst(modules, content, positions).Signature(sf);
    return content.Hash();
}

static Digest WrittenExpressionDigest(Program &p, Node *node) {
    KeyMaker keys(p.ast);
    DepModules modules(keys, p.ast.sources.size());
    Canon content, positions;
    DepAst(modules, content, positions).Expr(node);
    return content.Hash();
}

static void TestWrittenIdentity() {
    Program p;
    auto a = p.ast.NewVarDef();
    a->name = "a";
    a->isglobal = true;
    a->line = Line { 1, 0 };
    auto b = p.ast.NewVarDef();
    b->name = "b";
    b->isglobal = true;
    b->line = Line { 2, 0 };
    auto ia = p.ast.IndexTypeOf(IS_U32, a, false, Line {});
    auto ib = p.ast.IndexTypeOf(IS_U32, b, false, Line {});
    auto ba = p.ast.IndexTypeOf(IS_U32, a, true, Line {});
    ia->ix->ns = ib->ix->ns = ba->ix->ns = "";
    assert(WrittenTypeDigest(p, ia) != WrittenTypeDigest(p, ib));
    assert(WrittenTypeDigest(p, ia) != WrittenTypeDigest(p, ba));

    auto sf = p.Fn("f", {});
    auto signature = WrittenSignatureDigest(p, sf);
    sf->checkfree = true;
    assert(WrittenSignatureDigest(p, sf) != signature);

    auto expansion = p.ast.New<ConstFor>(Line {});
    expansion->source = ES_CONSTANTS;
    expansion->names = { "N" };
    auto expansion_digest = WrittenExpressionDigest(p, expansion);
    expansion->names[0] = "M";
    assert(WrittenExpressionDigest(p, expansion) != expansion_digest);
    expansion->names[0] = "N";
    expansion->source = ES_TYPES;
    assert(WrittenExpressionDigest(p, expansion) != expansion_digest);
}

// A specialization of `f` taking one slice, with an extra variable of its
// own that a nested context may read.
static FnSpec *Spec(Program &p, SFunction *f) {
    auto spec = p.ast.NewFnSpec();
    spec->sf = f;
    spec->argtypes = { p.Slice(p.I(IS_I64)) };
    RootArg r;
    r.cls = 1;
    spec->roots = { r };
    RootArg none;
    none.cls = -1;
    spec->views = { none };
    f->specs.push_back(spec);
    return spec;
}

static void TestContextKey() {
    Program a;
    auto f = a.Fn("sum", { a.Slice(a.I(IS_I64)) });
    auto s1 = Spec(a, f);
    KeyMaker ka(a.ast);
    auto k1 = ka.Context(s1);

    // Another table position, other functions around: the same key.
    Program b;
    for (int i = 0; i < 5; i++) b.Fn("noise", {});
    auto g = b.Fn("sum", { b.Slice(b.I(IS_I64)) }, 77);
    Spec(b, b.ast.functions[0]);
    auto s2 = Spec(b, g);
    KeyMaker kb(b.ast);
    auto k2 = kb.Context(s2);
    assert(k1.total == k2.total);
    for (int d = 0; d < kSpecDims; d++) assert(k1.dims[d] == k2.dims[d]);

    // Changing one dimension changes that digest and the total, no other.
    struct Change { SpecDim dim; function<void(FnSpec *)> apply; };
    vector<Change> changes = {
        { SpecDim::RootClass, [](FnSpec *s) { s->roots[0].writable = !s->roots[0].writable; } },
        { SpecDim::RootProvenance, [](FnSpec *s) { s->roots[0].growshrink = true; } },
        { SpecDim::RootHeldExact, [](FnSpec *s) { s->roots[0].heldexact = true; } },
        { SpecDim::RootDepthKey, [](FnSpec *s) { s->roots[0].depthkey = -2; } },
        { SpecDim::SlotViews, [](FnSpec *s) { s->views[0].cls = 1; } },
        { SpecDim::LiteralParams, [](FnSpec *s) { s->litparams = { 0 }; } },
    };
    for (auto &c : changes) {
        Program p;
        auto fn = p.Fn("sum", { p.Slice(p.I(IS_I64)) });
        auto spec = Spec(p, fn);
        c.apply(spec);
        KeyMaker kp(p.ast);
        auto &k = kp.Context(spec);
        assert(k.total != k1.total);
        for (int d = 0; d < kSpecDims; d++)
            assert((k.dims[d] != k1.dims[d]) == (d == (int)c.dim));
    }
    // Concrete argument types and type bindings.
    {
        Program p;
        auto fn = p.Fn("sum", { p.Slice(p.I(IS_I64)) });
        auto spec = Spec(p, fn);
        spec->argtypes = { p.Slice(p.I(IS_U8)) };
        KeyMaker kp(p.ast);
        assert(kp.Context(spec).dims[(int)SpecDim::ArgTypes] != k1.dims[(int)SpecDim::ArgTypes]);
        spec->bindings = { { "T", p.I(IS_U8) }, { "U", p.I(IS_I64) } };
        KeyMaker kq(p.ast);
        auto swapped = p.ast.NewFnSpec();
        *swapped = FnSpec();
        swapped->sf = fn;
        swapped->argtypes = spec->argtypes;
        swapped->roots = spec->roots;
        swapped->views = spec->views;
        swapped->bindings = { { "U", p.I(IS_I64) }, { "T", p.I(IS_U8) } };
        // Bindings are compared in any order.
        assert(kq.Context(spec).dims[(int)SpecDim::TypeBindings] ==
               kq.Context(swapped).dims[(int)SpecDim::TypeBindings]);
    }
    // A function's contexts are told apart by the dimension that differs,
    // and the same context built twice is one key.
    assert(ka.Context(s1).total == k1.total);

    // A caller-local root is named by the caller's key and the variable's
    // ordinal in its declaration, never by the variable table.
    auto build = [](int noise) {
        auto p = make_unique<Program>();
        for (int i = 0; i < noise; i++) p->ast.NewVarDef();
        auto outer = p->Fn("outer", {});
        auto inner = p->Fn("inner", {});
        inner->isnested = true;
        inner->outer = outer;
        auto os = Spec(*p, outer);
        auto v0 = p->ast.NewVarDef();
        v0->name = "a";
        v0->ownerspec = os;
        auto v1 = p->ast.NewVarDef();
        v1->name = "b";
        v1->ownerspec = os;
        auto is = Spec(*p, inner);
        is->lexparent = os;
        is->envreads.push_back(EnvRead { v1, true });
        return make_tuple(std::move(p), is, v0, v1);
    };
    auto [p1, i1, a0, a1] = build(0);
    auto [p2, i2, b0, b1] = build(9);
    KeyMaker k_1(p1->ast), k_2(p2->ast);
    assert(k_1.Context(i1).total == k_2.Context(i2).total);
    // Reading the other variable is another context.
    i2->envreads.clear();
    i2->envreads.push_back(EnvRead { b0, true });
    KeyMaker k_3(p2->ast);
    assert(k_3.Context(i2).dims[(int)SpecDim::EnvReads] != k_1.Context(i1).dims[(int)SpecDim::EnvReads]);
    assert(k_3.Context(i2).dims[(int)SpecDim::ArgTypes] == k_1.Context(i1).dims[(int)SpecDim::ArgTypes]);
    // The state the body found the variable in is part of the key.
    i2->envreads.clear();
    i2->envreads.push_back(EnvRead { b1, false });
    KeyMaker k_4(p2->ast);
    assert(k_4.Context(i2).dims[(int)SpecDim::EnvReads] != k_1.Context(i1).dims[(int)SpecDim::EnvReads]);
}

static void TestRelativeStoreSummary() {
    Program p;
    auto callee = Spec(p, p.Fn("callee", { p.Slice(p.I(IS_I64)) }));
    auto caller = Spec(p, p.Fn("caller", { p.Slice(p.I(IS_I64)) }));
    DepRecorder recorder;
    recorder.specs[caller].callees.insert(callee);
    auto summary = [&] {
        KeyMaker keys(p.ast);
        DepFinal report(p.ast, keys, recorder);
        report.Function(caller);
        for (auto &dependency : report.out.back().deps)
            if (dependency.kind == DepKind::Summary) return dependency.digest;
        abort();
    };
    auto empty = summary();
    callee->record.relativestores.push_back({});
    auto stored = summary();
    assert(stored != empty);
    callee->record.relativestores[0].source.unknown = true;
    auto source = summary();
    assert(source != stored);
    callee->record.relativestores[0].destination.unknown = true;
    auto destination = summary();
    assert(destination != source);
    callee->record.relativestores[0].result = 0;
    auto result = summary();
    assert(result != destination);
    auto other = callee->record.relativestores[0];
    other.result = 1;
    callee->record.relativestores.push_back(other);
    auto multiple = summary();
    assert(multiple != result);
    reverse(callee->record.relativestores.begin(), callee->record.relativestores.end());
    assert(summary() == multiple);
    callee->record.relativestores.push_back(other);
    assert(summary() == multiple);
}

int main() {
    TestSha256();
    TestCanon();
    TestDeclKey();
    TestTypeKey();
    TestWrittenIdentity();
    TestContextKey();
    TestRelativeStoreSummary();
    puts("ok");
    return 0;
}
