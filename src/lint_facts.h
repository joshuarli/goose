// Goose compiler — the private, versioned boundary between the canonical
// frontend and the Goose-native linter.
#pragma once

namespace goose {

inline string LintJsonString(string_view value) {
    string out = "\"";
    for (auto c : value) {
        auto b = (unsigned char)c;
        switch (b) {
            case '"': out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\b': out += "\\b"; break;
            case '\f': out += "\\f"; break;
            case '\n': out += "\\n"; break;
            case '\r': out += "\\r"; break;
            case '\t': out += "\\t"; break;
            default:
                if (b < 0x20) {
                    char hex[7];
                    snprintf(hex, sizeof hex, "\\u%04x", b);
                    out += hex;
                } else out += (char)b;
        }
    }
    out += '"';
    return out;
}

inline uint64_t LintHashBytes(uint64_t hash, string_view bytes) {
    for (auto c : bytes) {
        hash ^= (uint8_t)c;
        hash *= UINT64_C(1099511628211);
    }
    return hash;
}

inline string LintHashHex(uint64_t value) {
    char hex[17];
    snprintf(hex, sizeof hex, "%016llx", (unsigned long long)value);
    return hex;
}

inline string LintDisplayPath(const string &path) {
    if (path.empty()) return {};
    auto sourcepath = filesystem::path(path).lexically_normal();
    if (sourcepath.is_absolute()) {
        std::error_code ec;
        auto cwd = filesystem::current_path(ec);
        if (!ec) {
            auto relative = sourcepath.lexically_relative(cwd);
            if (!relative.empty() && *relative.begin() != "..")
                return ForwardSlashes(relative.generic_string());
        }
        auto hash = LintHashBytes(UINT64_C(14695981039346656037), sourcepath.generic_string());
        return cat("external/", LintHashHex(hash), "/", sourcepath.filename().generic_string());
    }
    auto relative = sourcepath.generic_string();
    if (relative.rfind("../", 0) == 0) {
        auto hash = LintHashBytes(UINT64_C(14695981039346656037), relative);
        return cat("external/", LintHashHex(hash), "/", sourcepath.filename().generic_string());
    }
    return ForwardSlashes(relative);
}

inline string LintProjectPath(const Ast &ast, int fileidx, const string &entry) {
    if (fileidx < 0 || (size_t)fileidx >= ast.sources.size()) return "<unknown>";
    auto &path = ast.sources[fileidx].first;
    auto pkgidx = fileidx < (int)ast.filepkg.size() ? ast.filepkg[fileidx] : 0;
    if (pkgidx == 0) {
        auto sourcepath = filesystem::path(path).lexically_normal();
        std::error_code ec;
        auto cwd = filesystem::current_path(ec);
        if (sourcepath.is_absolute()) {
            if (!ec) {
                auto relative = sourcepath.lexically_relative(cwd);
                if (!relative.empty() && *relative.begin() != "..")
                    return ForwardSlashes(relative.generic_string());
            }
            auto root = filesystem::path(ast.packages[0].root).lexically_normal();
            auto relative = sourcepath.lexically_relative(root);
            if (!relative.empty() && *relative.begin() != "..")
                return ForwardSlashes(relative.generic_string());
            auto hash = LintHashBytes(UINT64_C(14695981039346656037), sourcepath.generic_string());
            return cat("external/", LintHashHex(hash), "/", sourcepath.filename().generic_string());
        }
        auto relative = sourcepath.generic_string();
        if (relative.rfind("../", 0) == 0) {
            auto root = filesystem::path(DirOf(entry)).lexically_normal();
            auto rooted = sourcepath.lexically_relative(root);
            if (!rooted.empty() && *rooted.begin() != "..")
                return ForwardSlashes(rooted.generic_string());
            auto hash = LintHashBytes(UINT64_C(14695981039346656037), relative);
            return cat("external/", LintHashHex(hash), "/", sourcepath.filename().generic_string());
        }
        return ForwardSlashes(relative);
    }
    string base = DirOf(entry), prefix;
    if (pkgidx >= 0 && (size_t)pkgidx < ast.packages.size()) {
        auto &pkg = ast.packages[pkgidx];
        base = pkg.root;
        if (pkgidx != 0) prefix = pkg.stdlib ? "stdlib/" : cat("packages/", pkg.name, "/");
    }
    auto rel = ForwardSlashes(RelativeTo(path, base));
    if (rel.empty()) rel = LintDisplayPath(path);
    return cat(prefix, rel);
}

inline size_t LintLineAt(string_view source, size_t byte) {
    byte = min(byte, source.size());
    return 1 + (size_t)count(source.begin(), source.begin() + byte, '\n');
}

inline size_t LintColumnAt(string_view source, size_t byte) {
    byte = min(byte, source.size());
    auto prev = byte ? source.rfind('\n', byte - 1) : string_view::npos;
    auto start = prev == string_view::npos ? 0 : prev + 1;
    return byte - start + 1;
}

inline const SourceSpan *LintSpan(const Ast &ast, const Node *node) {
    if (!node) return nullptr;
    node = node->Origin();
    if (auto it = ast.source_spans.find(node); it != ast.source_spans.end()) return &it->second;
    return nullptr;
}

inline string LintLineEndings(string_view source) {
    auto crlf = source.find("\r\n") != string_view::npos;
    auto lf = false;
    auto cr = false;
    for (size_t i = 0; i < source.size(); i++)
        if (source[i] == '\n' && (!i || source[i - 1] != '\r')) lf = true;
        else if (source[i] == '\r' && (i + 1 == source.size() || source[i + 1] != '\n')) cr = true;
    auto kinds = (int)crlf + (int)lf + (int)cr;
    return kinds > 1 ? "mixed" : crlf ? "crlf" : lf ? "lf" : cr ? "cr" : "none";
}

inline string LintTypeContext(const TypeExpr *type) {
    if (!type) return "?";
    string text;
    type->Dump(text);
    return text;
}

inline string LintRootContext(const RootArg &root) {
    return cat(root.cls, ":w", root.writable, ":r", root.reusable,
               ":gs", root.growshrink, ":via", root.gsvia, ":slot", root.slotread,
               ":unknown", root.unknown, ":byteview", root.byteview,
               ":exact", root.exact, ":concrete", root.concrete,
               ":heldexact", root.heldexact);
}

inline string LintSpecializationContext(const FnSpec &spec) {
    string context = "args(";
    for (size_t i = 0; i < spec.argtypes.size(); i++) {
        if (i) context += ",";
        context += LintTypeContext(spec.argtypes[i]);
    }
    context += ") roots(";
    for (size_t i = 0; i < spec.roots.size(); i++) {
        if (i) context += ",";
        context += LintRootContext(spec.roots[i]);
    }
    context += ") views(";
    for (size_t i = 0; i < spec.views.size(); i++) {
        if (i) context += ",";
        context += LintRootContext(spec.views[i]);
    }
    context += ") bindings(";
    for (size_t i = 0; i < spec.bindings.size(); i++) {
        if (i) context += ",";
        context += spec.bindings[i].first;
        context += "=";
        context += LintTypeContext(spec.bindings[i].second);
    }
    return cat(context, ") escaped=", spec.escaped, " funval=", spec.isfunval);
}

inline bool LintConstantInt(const Node *node, int64_t &value, bool &uns, int depth = 0) {
    if (!node || depth > 64) return false;
    if (auto literal = Is<IntLit>(node)) {
        value = literal->val;
        uns = literal->uns;
        return true;
    }
    if (auto ident = Is<Ident>(node); ident && ident->vdef && ident->vdef->constlit) {
        value = ident->vdef->constval;
        uns = ident->vdef->constuns;
        return true;
    }
    if (auto unary = Is<Unary>(node); unary &&
        (unary->op == T_MINUS || unary->op == T_BITNOT)) {
        int64_t child = 0;
        bool child_uns = false;
        if (!LintConstantInt(unary->child, child, child_uns, depth + 1) || child_uns ||
            !unary->exprtype || unary->exprtype->kind != TY_INT ||
            unary->exprtype->intstorage == IS_VARINT) return false;
        if (unary->op == T_BITNOT) value = ~child;
        else if (!FoldIntOp(T_MINUS, 0, child, unary->exprtype->intstorage, value)) return false;
        uns = false;
        return true;
    }
    if (auto binary = Is<Binary>(node)) {
        int64_t left = 0, right = 0;
        bool left_uns = false, right_uns = false;
        if (!LintConstantInt(binary->left, left, left_uns, depth + 1) ||
            !LintConstantInt(binary->right, right, right_uns, depth + 1) || left_uns != right_uns ||
            !binary->exprtype || binary->exprtype->kind != TY_INT ||
            binary->exprtype->intstorage == IS_VARINT) return false;
        switch (binary->op) {
            case T_PLUS: case T_MINUS: case T_MUL: case T_DIV: case T_MOD:
            case T_BITAND: case T_BITOR: case T_XOR: case T_SHL: case T_SHR:
                if (!FoldIntOp(binary->op, left, right, binary->exprtype->intstorage, value)) return false;
                uns = IsUnsigned(binary->exprtype->intstorage);
                return true;
            default: return false;
        }
    }
    return false;
}

// This is intentionally narrower than a general effect analysis: it proves
// only source expressions built from local reads and constant operations for
// which the selected typed operation cannot trap in a debug build.
inline bool LintPureExpression(const Node *node, int depth = 0) {
    if (!node || depth > 64) return false;
    if (Is<IntLit>(node) || Is<FltLit>(node) || Is<BoolLit>(node) || Is<StrLit>(node)) return true;
    if (auto ident = Is<Ident>(node)) return ident->vdef != nullptr;
    if (auto unary = Is<Unary>(node)) {
        if (unary->op != T_MINUS && unary->op != T_NOT && unary->op != T_BITNOT) return false;
        if (!LintPureExpression(unary->child, depth + 1)) return false;
        if (unary->op == T_MINUS && unary->exprtype && unary->exprtype->kind == TY_INT) {
            int64_t value = 0, folded = 0;
            bool uns = false;
            return LintConstantInt(unary->child, value, uns, depth + 1) && !uns &&
                   unary->exprtype->intstorage != IS_VARINT &&
                   FoldIntOp(T_MINUS, 0, value, unary->exprtype->intstorage, folded);
        }
        return true;
    }
    if (auto binary = Is<Binary>(node)) {
        if (!LintPureExpression(binary->left, depth + 1) ||
            !LintPureExpression(binary->right, depth + 1)) return false;
        switch (binary->op) {
            case T_EQ: case T_NEQ: case T_LT: case T_GT: case T_LTEQ: case T_GTEQ:
            case T_ANDAND: case T_OROR:
                return true;
            case T_PLUS: case T_MINUS: case T_MUL: case T_DIV: case T_MOD:
            case T_BITAND: case T_BITOR: case T_XOR: case T_SHL: case T_SHR: {
                if (!binary->exprtype || binary->exprtype->kind != TY_INT) {
                    return binary->exprtype && binary->exprtype->kind == TY_FLT;
                }
                int64_t left = 0, right = 0, folded = 0;
                bool left_uns = false, right_uns = false;
                return binary->exprtype->intstorage != IS_VARINT &&
                       LintConstantInt(binary->left, left, left_uns, depth + 1) &&
                       LintConstantInt(binary->right, right, right_uns, depth + 1) &&
                       left_uns == right_uns &&
                       FoldIntOp(binary->op, left, right, binary->exprtype->intstorage, folded);
            }
            default: return false;
        }
    }
    return false;
}

inline string LintPureExpressionKind(const Node *node) {
    if (Is<IntLit>(node)) return "integer_literal";
    if (Is<FltLit>(node)) return "float_literal";
    if (Is<BoolLit>(node)) return "boolean_literal";
    if (Is<StrLit>(node)) return "string_literal";
    if (auto binary = Is<Binary>(node)) {
        if (binary->exprtype && binary->exprtype->kind == TY_FLT) return "floating_expression";
        if (binary->exprtype && binary->exprtype->kind == TY_BOOL) return "boolean_expression";
        return "constant_integer_expression";
    }
    if (auto unary = Is<Unary>(node)) {
        if (unary->exprtype && unary->exprtype->kind == TY_FLT) return "floating_expression";
        if (unary->exprtype && unary->exprtype->kind == TY_BOOL) return "boolean_expression";
        return "constant_integer_expression";
    }
    return "pure_expression";
}

inline string LintFunctionIdentity(const Ast &ast, const SFunction *function) {
    if (!function) return {};
    auto fileidx = function->line.fileidx;
    if (fileidx < 0 || (size_t)fileidx >= ast.filepkg.size() ||
        ast.filepkg[fileidx] < 0 || (size_t)ast.filepkg[fileidx] >= ast.packages.size())
        return cat("unknown::", function->qname);
    auto &package = ast.packages[ast.filepkg[fileidx]];
    auto package_name = package.stdlib ? string("stdlib") : package.name;
    return cat(package_name, "::", function->qname);
}

inline VarDef *LintIdentifier(Node *node) {
    auto ident = Is<Ident>(node);
    return ident ? ident->vdef : nullptr;
}

inline Node *LintUnwrapAutoRef(Node *node) {
    for (;;) {
        auto unary = Is<Unary>(node);
        if (!unary || !unary->synth || unary->op != T_BITAND) break;
        node = unary->child;
    }
    return node;
}

inline bool LintIsUnsignedType(const TypeExpr *type) {
    return type && type->kind == TY_INT && type->intstorage != IS_VARINT &&
           IsUnsigned(type->intstorage);
}

inline bool LintKnownNonnegative(Node *node) {
    if (auto literal = Is<IntLit>(node)) return !literal->uns && literal->val >= 0;
    if (auto ident = Is<Ident>(node); ident && ident->vdef)
        return ident->vdef->nonneg || LintIsUnsignedType(ident->vdef->type);
    return LintIsUnsignedType(node ? node->exprtype : nullptr);
}

inline bool LintIsCurrentLastIndex(Node *node, VarDef *root) {
    auto minus = Is<Binary>(node);
    if (!minus || minus->op != T_MINUS) return false;
    auto length = Is<Dot>(minus->left);
    auto length_root = length ? LintIdentifier(length->obj) : nullptr;
    auto one = Is<IntLit>(minus->right);
    return length && length->member == B_LEN && length_root == root &&
           one && !one->uns && one->val == 1;
}

inline VarDef *LintCurrentLengthRoot(Node *node) {
    auto minus = Is<Binary>(node);
    auto length = minus ? Is<Dot>(minus->left) : nullptr;
    auto one = minus ? Is<IntLit>(minus->right) : nullptr;
    if (!minus || minus->op != T_MINUS || !length || length->member != B_LEN ||
        !one || one->uns || one->val != 1) return nullptr;
    return LintIdentifier(length->obj);
}

inline pair<size_t, size_t> LintExactSpan(const Ast &ast, const Node *node) {
    auto span = LintSpan(ast, node);
    return span ? pair<size_t, size_t> { span->start_byte, span->end_byte }
                : pair<size_t, size_t> { string::npos, string::npos };
}

template<typename F>
inline void LintWalkTyped(Node *node, unordered_set<const Node *> &seen, F visit) {
    if (!node || !seen.insert(node).second) return;
    visit(node);
    node->Children([&](Node *child) { LintWalkTyped(child, seen, visit); });
    if (auto call = Is<Call>(node); call && call->fvbody)
        LintWalkTyped(call->fvbody, seen, visit);
}

inline string LintCallUseShape(const Call *call, Node *parent) {
    if (!parent) return "unknown";
    if (auto block = Is<Block>(parent)) {
        if (find(block->stmts.begin(), block->stmts.end(), (Node *)call) != block->stmts.end())
            return "statement";
        return "scalar";
    }
    if (auto decl = Is<VarDecl>(parent)) {
        if (decl->inits.size() == 1 && decl->inits[0] == call &&
            decl->names.size() == call->rettypes.size() && decl->defs.size() == decl->names.size())
            return "tuple_binding";
        return decl->inits.size() == 1 && decl->inits[0] == call && decl->names.size() == 1
                   ? "scalar" : "unknown";
    }
    if (auto ret = Is<Return>(parent))
        return ret->vals.size() == 1 && ret->vals[0] == call ? "return" : "scalar";
    return "scalar";
}

inline string BuildLintFacts(const Ast &ast, const vector<LintWarning> &warnings,
                             const string &entry, int optlevel, bool allow_fetch) {
    struct SourceRef { int oldid; string path; };
    vector<SourceRef> sources;
    for (size_t i = 0; i < ast.sources.size(); i++)
        sources.push_back({ (int)i, LintProjectPath(ast, (int)i, entry) });
    stable_sort(sources.begin(), sources.end(), [](const auto &a, const auto &b) {
        return a.path < b.path;
    });
    vector<int> fileids(ast.sources.size());
    vector<string> source_paths(ast.sources.size());
    for (size_t i = 0; i < sources.size(); i++) {
        fileids[sources[i].oldid] = (int)i;
        source_paths[sources[i].oldid] = sources[i].path;
    }
    const string unknown_path = "<unknown>";
    auto project_path = [&](int fileidx) -> const string & {
        return fileidx >= 0 && (size_t)fileidx < source_paths.size()
                   ? source_paths[fileidx] : unknown_path;
    };

    string out;
    auto hash = UINT64_C(14695981039346656037);
    size_t record_count = 0;
    constexpr size_t MAX_FACTS = 64u * 1024u * 1024u;
    constexpr size_t MAX_RECORD = 16u * 1024u * 1024u;
    constexpr size_t MAX_RECORDS = 1000000;
    auto record = [&](string line) {
        if (line.size() > MAX_RECORD)
            throw CompileError { "a lint facts record exceeds the 16 MiB record limit", CompileErrorKind::Tool };
        if (record_count >= MAX_RECORDS)
            throw CompileError { "lint facts exceed the one million record limit", CompileErrorKind::Tool };
        if (line.size() >= MAX_FACTS || out.size() > MAX_FACTS - line.size() - 1)
            throw CompileError { "lint facts exceed the 64 MiB stream limit", CompileErrorKind::Tool };
        out += line;
        out += '\n';
        hash = LintHashBytes(hash, line);
        hash = LintHashBytes(hash, "\n");
        record_count++;
    };
    record(cat("{\"kind\":\"header\",\"facts_version\":1,\"compiler\":\"goose\","
               "\"compiler_revision\":", LintJsonString(RuntimeVersion()),
               ",\"entries\":[", LintJsonString(project_path(0)),
               "],\"profile\":\"O", optlevel,
               "\",\"frontend_options\":{\"debug\":false,\"unsafe_no_rf_check\":false,"
               "\"allow_fetch\":", allow_fetch, "}}"));

    for (size_t id = 0; id < sources.size(); id++) {
        auto oldid = sources[id].oldid;
        auto &contents = *ast.sources[oldid].second;
        auto source_hash = LintHashBytes(UINT64_C(14695981039346656037), contents);
        record(cat("{\"kind\":\"source\",\"file_id\":", id, ",\"path\":",
                   LintJsonString(sources[id].path), ",\"content_hash\":\"fnv1a64:",
                   LintHashHex(source_hash), "\",\"byte_length\":", contents.size(),
                   ",\"line_endings\":\"", LintLineEndings(contents), "\"}"));
    }

    struct WarningRef { const LintWarning *warning; int fileidx; string path; size_t start; };
    vector<WarningRef> ordered_warnings;
    for (auto &warning : warnings) {
        auto fileidx = warning.at ? warning.at->line.fileidx : -1;
        auto span = LintSpan(ast, warning.at);
        ordered_warnings.push_back({ &warning, fileidx,
            project_path(fileidx), span ? span->start_byte : 0 });
    }
    stable_sort(ordered_warnings.begin(), ordered_warnings.end(), [](const auto &a, const auto &b) {
        return tie(a.path, a.start, a.warning->code, a.warning->message) <
               tie(b.path, b.start, b.warning->code, b.warning->message);
    });
    size_t warning_id = 0;
    for (auto &ref : ordered_warnings) {
        auto &warning = *ref.warning;
        auto span = LintSpan(ast, warning.at);
        auto fileidx = ref.fileidx;
        auto start_line = warning.at ? warning.at->line.line : 0;
        auto sourceidx = fileidx >= 0 && (size_t)fileidx < ast.sources.size() ? fileidx : -1;
        auto precision = span && sourceidx >= 0 && span->end_byte >= span->start_byte
                             ? "exact" : "line";
        string_view contents;
        if (sourceidx >= 0) contents = *ast.sources[sourceidx].second;
        auto start_byte = precision == string("exact") ? span->start_byte : 0;
        auto end_byte = precision == string("exact") ? span->end_byte : 0;
        auto start_line_exact = precision == string("exact")
                                    ? LintLineAt(contents, start_byte) : (size_t)start_line;
        auto end_line_exact = precision == string("exact")
                                  ? LintLineAt(contents, end_byte) : (size_t)0;
        vector<string> contexts;
        contexts.reserve(warning.specializations.size());
        for (auto spec : warning.specializations)
            if (spec) contexts.push_back(cat(LintFunctionIdentity(ast, spec->sf), " (",
                                             LintSpecializationContext(*spec), ")"));
        sort(contexts.begin(), contexts.end());
        contexts.erase(unique(contexts.begin(), contexts.end()), contexts.end());
        string contexts_json = "[";
        for (size_t i = 0; i < contexts.size(); i++) {
            if (i) contexts_json += ",";
            contexts_json += LintJsonString(contexts[i]);
        }
        contexts_json += "]";
        record(cat("{\"kind\":\"warning\",\"id\":", warning_id++,
                   ",\"code\":", LintJsonString(LintWarningCodeName(warning.code)),
                   ",\"message\":", LintJsonString(warning.message), ",\"source\":{"
                   "\"file_id\":", sourceidx >= 0 ? cat(fileids[sourceidx]) : string("null"),
                   ",\"line\":", start_line_exact, ",\"start_line\":", start_line_exact,
                   ",\"start_column\":",
                   precision == string("exact") ? cat(LintColumnAt(contents, start_byte)) : string("null"),
                   ",\"end_line\":",
                   precision == string("exact") ? cat(end_line_exact) : string("null"),
                   ",\"end_column\":",
                   precision == string("exact") ? cat(LintColumnAt(contents, end_byte)) : string("null"),
                   ",\"start_byte\":",
                   precision == string("exact") ? cat(start_byte) : string("null"),
                   ",\"end_byte\":",
                   precision == string("exact") ? cat(end_byte) : string("null"),
                   ",\"precision\":\"", precision, "\"},\"specializations\":", contexts_json, "}"));
    }

    vector<pair<const Node *, SourceSpan>> statements(ast.statement_spans.begin(),
                                                       ast.statement_spans.end());
    stable_sort(statements.begin(), statements.end(), [&](const auto &a, const auto &b) {
        const auto &ap = project_path(a.first->line.fileidx);
        const auto &bp = project_path(b.first->line.fileidx);
        return tie(ap, a.second.start_byte, a.second.end_byte, a.second.source_order) <
               tie(bp, b.second.start_byte, b.second.end_byte, b.second.source_order);
    });
    for (auto &[node, span] : statements) {
        auto fileidx = node->line.fileidx;
        if (fileidx < 0 || (size_t)fileidx >= ast.sources.size()) continue;
        auto &contents = *ast.sources[fileidx].second;
        auto start_line = LintLineAt(contents, span.start_byte);
        auto end_line = LintLineAt(contents, span.end_byte);
        record(cat("{\"kind\":\"statement\",\"file_id\":", fileids[fileidx],
                   ",\"path\":", LintJsonString(project_path(fileidx)),
                   ",\"start_byte\":", span.start_byte, ",\"end_byte\":", span.end_byte,
                   ",\"start_line\":", start_line, ",\"end_line\":", end_line,
                   ",\"source_order\":", span.source_order, "}"));
    }

    auto comments = ast.lint_comments;
    stable_sort(comments.begin(), comments.end(), [&](const auto &a, const auto &b) {
        auto ap = a.fileidx >= 0 && (size_t)a.fileidx < ast.sources.size()
                      ? project_path(a.fileidx) : string();
        auto bp = b.fileidx >= 0 && (size_t)b.fileidx < ast.sources.size()
                      ? project_path(b.fileidx) : string();
        return tie(ap, a.start_byte, a.end_byte) < tie(bp, b.start_byte, b.end_byte);
    });
    size_t comment_id = 0;
    for (auto &comment : comments) {
        if (comment.fileidx < 0 || (size_t)comment.fileidx >= ast.sources.size()) continue;
        record(cat("{\"kind\":\"comment\",\"id\":", comment_id++,
                   ",\"file_id\":", fileids[comment.fileidx],
                   ",\"path\":", LintJsonString(project_path(comment.fileidx)),
                   ",\"start_byte\":", comment.start_byte, ",\"end_byte\":", comment.end_byte,
                   ",\"line\":", comment.line, ",\"form\":\"",
                   comment.block ? "block" : "line", "\"",
                   ",\"text\":", LintJsonString(comment.text), "}"));
    }

    struct SpecRef {
        FnSpec *spec;
        int oldfile;
        int fileid;
        string path;
        string name;
        string context;
        int line;
        size_t start;
        size_t end;
        int start_line;
        int end_line;
        size_t start_column;
        size_t end_column;
        bool exact;
    };
    unordered_map<const SFunction *, const Node *> declarations;
    for (auto node : ast.allnodes) {
        auto fn = Is<FnDecl>(node);
        if (fn) declarations.try_emplace(fn->sf, node->Origin());
    }
    vector<SpecRef> specializations;
    for (auto spec : ast.fnspecs) {
        if (!spec || !spec->sf) continue;
        auto oldfile = spec->sf->line.fileidx;
        auto path = project_path(oldfile);
        auto it = declarations.find(spec->sf);
        auto decl = it == declarations.end() ? nullptr : it->second;
        auto span = LintSpan(ast, decl);
        string_view contents;
        if (oldfile >= 0 && (size_t)oldfile < ast.sources.size())
            contents = *ast.sources[oldfile].second;
        auto exact = span && oldfile >= 0 && (size_t)oldfile < ast.sources.size() &&
                     span->end_byte >= span->start_byte;
        auto start = exact ? span->start_byte : 0;
        auto end = exact ? span->end_byte : 0;
        auto start_line = exact ? (int)LintLineAt(contents, start) : spec->sf->line.line;
        auto end_line = exact ? (int)LintLineAt(contents, end) : start_line;
        auto start_column = exact ? LintColumnAt(contents, start) : 0;
        auto end_column = exact ? LintColumnAt(contents, end) : 0;
        specializations.push_back({ spec, oldfile,
            oldfile >= 0 && (size_t)oldfile < fileids.size() ? fileids[oldfile] : -1,
            std::move(path), LintFunctionIdentity(ast, spec->sf),
            LintSpecializationContext(*spec), spec->sf->line.line,
            start, end, start_line, end_line, start_column, end_column, exact });
    }
    stable_sort(specializations.begin(), specializations.end(), [](const auto &a, const auto &b) {
        return tie(a.path, a.line, a.name, a.context, a.start) <
               tie(b.path, b.line, b.name, b.context, b.start);
    });
    unordered_map<const FnSpec *, int> specialization_ids;
    for (size_t id = 0; id < specializations.size(); id++)
        specialization_ids[specializations[id].spec] = (int)id;

    unordered_set<const FnSpec *> entry_reachable_specs;
    unordered_set<const FnSpec *> scanned_specs;
    vector<const FnSpec *> pending_specs;
    bool reachability_complete = true;
    auto enqueue = [&](const FnSpec *spec) {
        if (spec && entry_reachable_specs.insert(spec).second) pending_specs.push_back(spec);
    };
    auto mainsf = const_cast<Ast &>(ast).MainFunction();
    if (mainsf) for (auto spec : mainsf->specs) enqueue(spec);
    auto scan_calls = [&](Node *root) {
        unordered_set<const Node *> seen;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || !seen.insert(node).second) return;
            if (auto call = Is<Call>(node)) {
                enqueue(call->spec);
                for (auto spec : call->dispatch) enqueue(spec);
                for (auto &[type, spec] : call->fmtspecs) enqueue(spec);
                if (call->builtin == B_THREAD_SPAWN && !call->args.empty()) {
                    if (auto ident = Is<Ident>(call->args[0]); ident && ident->fnref)
                        for (auto spec : ident->fnref->specs) enqueue(spec);
                }
                if (call->builtin < 0 && !call->spec && call->dispatch.empty() &&
                    !call->fvbody && call->fmtspecs.empty())
                    reachability_complete = false;
                for (auto arg : call->args) walk(arg);
                walk(call->callee);
                if (call->fvbody) walk(call->fvbody);
                return;
            }
            if (Is<FunVal>(node) || Is<FnDecl>(node)) return;
            node->Children([&](Node *child) { walk(child); });
        };
        walk(root);
    };
    for (auto global : ast.globals) scan_calls(global);
    for (size_t next = 0; next < pending_specs.size(); next++) {
        auto spec = pending_specs[next];
        if (!scanned_specs.insert(spec).second) continue;
        scan_calls(spec->body);
    }

    auto type_span_fields = [&](int oldfile, const Node *node) {
        auto span = LintSpan(ast, node);
        if (oldfile < 0 || (size_t)oldfile >= ast.sources.size() || !span ||
            span->end_byte < span->start_byte) {
            auto line = node ? node->line.line : 0;
            return cat("\"start_byte\":null,\"end_byte\":null,\"start_line\":", line,
                       ",\"end_line\":", line, ",\"start_column\":null,\"end_column\":null,"
                       "\"precision\":\"line\"");
        }
        auto &contents = *ast.sources[oldfile].second;
        return cat("\"start_byte\":", span->start_byte, ",\"end_byte\":", span->end_byte,
                   ",\"start_line\":", LintLineAt(contents, span->start_byte),
                   ",\"end_line\":", LintLineAt(contents, span->end_byte),
                   ",\"start_column\":", LintColumnAt(contents, span->start_byte),
                   ",\"end_column\":", LintColumnAt(contents, span->end_byte),
                   ",\"precision\":\"exact\"");
    };

    struct CallRef {
        Call *call;
        FnSpec *owner;
        Node *parent;
        int owner_id;
        int oldfile;
        string path;
        string use_shape;
        string callee;
        string builtin;
        size_t start;
        size_t end;
    };
    vector<CallRef> calls;
    auto collect_calls = [&](FnSpec *owner, Node *root) {
        auto owner_id = owner ? specialization_ids.at(owner) : -1;
        function<void(Node *, Node *)> visit = [&](Node *node, Node *parent) {
            if (!node) return;
            if (auto call = Is<Call>(node)) {
                auto oldfile = call->line.fileidx;
                auto path = project_path(oldfile);
                auto span = LintSpan(ast, call);
                auto callee = call->spec ? LintFunctionIdentity(ast, call->spec->sf) : string();
                auto builtin = call->builtin >= 0
                                   ? cat("goose::builtin::", BuiltinByKind(call->builtin).name)
                                   : string();
                calls.push_back({ call, owner, parent, owner_id, oldfile, std::move(path),
                    LintCallUseShape(call, parent), std::move(callee), std::move(builtin),
                    span ? span->start_byte : 0, span ? span->end_byte : 0 });
                visit(call->callee, node);
                for (auto arg : call->args) visit(arg, node);
                if (call->trailing) visit((Node *)call->trailing, node);
                if (call->fvbody) visit(call->fvbody, node);
                return;
            }
            node->Children([&](Node *child) { visit(child, node); });
        };
        visit(root, nullptr);
    };
    for (auto &ref : specializations) collect_calls(ref.spec, ref.spec->body);
    for (auto global : ast.globals) collect_calls(nullptr, global);
    stable_sort(calls.begin(), calls.end(), [](const auto &a, const auto &b) {
        return tie(a.owner_id, a.path, a.start, a.end, a.use_shape, a.callee, a.builtin) <
               tie(b.owner_id, b.path, b.start, b.end, b.use_shape, b.callee, b.builtin);
    });

    unordered_map<const Call *, int> call_ids;
    for (size_t id = 0; id < calls.size(); id++) call_ids[calls[id].call] = (int)id;
    unordered_map<const VarDef *, string> variable_ids;
    auto add_variable_ids = [&](Node *root) {
        unordered_set<const Node *> seen;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || !seen.insert(node).second) return;
            if (auto declaration = Is<VarDecl>(node)) {
                auto span = LintSpan(ast, declaration);
                auto fileidx = declaration->line.fileidx;
                auto fileid = fileidx >= 0 && (size_t)fileidx < fileids.size() ? fileids[fileidx] : -1;
                for (size_t i = 0; i < declaration->defs.size(); i++) {
                    auto def = declaration->defs[i];
                    if (!def || variable_ids.count(def)) continue;
                    auto identity = span && fileid >= 0
                        ? cat("v", fileid, ":", span->start_byte, ":", i)
                        : cat("v", fileid, ":line", declaration->line.line, ":", def->name, ":", i);
                    variable_ids.emplace(def, std::move(identity));
                }
            }
            node->Children([&](Node *child) { walk(child); });
        };
        walk(root);
    };
    for (auto &ref : specializations) {
        auto declaration = declarations.find(ref.spec->sf);
        auto span = declaration == declarations.end() ? nullptr : LintSpan(ast, declaration->second);
        auto fileid = ref.oldfile >= 0 && (size_t)ref.oldfile < fileids.size() ? fileids[ref.oldfile] : -1;
        for (size_t i = 0; i < ref.spec->params.size(); i++) {
            auto parameter = ref.spec->params[i];
            if (!parameter || variable_ids.count(parameter)) continue;
            auto identity = span && fileid >= 0
                ? cat("v", fileid, ":", span->start_byte, ":p", i)
                : cat("v", fileid, ":line", parameter->line.line, ":", parameter->name, ":p", i);
            variable_ids.emplace(parameter, std::move(identity));
        }
        add_variable_ids(ref.spec->body);
    }
    for (auto global : ast.globals) add_variable_ids(global);

    unordered_set<const VarDef *> referenced_bindings;
    auto scan_references = [&](Node *root) {
        unordered_set<const Node *> seen;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || !seen.insert(node).second) return;
            if (auto assignment = Is<Assign>(node)) {
                auto direct_target = Is<Ident>(assignment->lval);
                if (assignment->op != T_ASSIGN || !direct_target) walk(assignment->lval);
                walk(assignment->rhs);
                return;
            }
            if (auto incdec = Is<IncDec>(node)) {
                walk(incdec->lval);
                return;
            }
            if (auto ident = Is<Ident>(node); ident && ident->vdef)
                referenced_bindings.insert(ident->vdef);
            node->Children([&](Node *child) { walk(child); });
            if (auto call = Is<Call>(node); call && call->fvbody) walk(call->fvbody);
        };
        walk(root);
    };
    for (auto spec : ast.fnspecs) if (spec) scan_references(spec->body);
    for (auto global : ast.globals) scan_references(global);

    unordered_set<const VarDef *> overwritten_before_read;
    auto has_read_of = [&](Node *root, const VarDef *binding) {
        unordered_set<const Node *> seen;
        bool found = false;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || found || !seen.insert(node).second) return;
            if (auto assignment = Is<Assign>(node)) {
                auto direct_target = Is<Ident>(assignment->lval);
                if (assignment->op != T_ASSIGN || !direct_target || direct_target->vdef != binding)
                    walk(assignment->lval);
                walk(assignment->rhs);
                return;
            }
            if (auto incdec = Is<IncDec>(node)) { walk(incdec->lval); return; }
            if (auto ident = Is<Ident>(node); ident && ident->vdef == binding) { found = true; return; }
            node->Children([&](Node *child) { walk(child); });
            if (auto call = Is<Call>(node); call && call->fvbody) walk(call->fvbody);
        };
        walk(root);
        return found;
    };
    auto has_write_of = [&](Node *root, const VarDef *binding) {
        unordered_set<const Node *> seen;
        bool found = false;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || found || !seen.insert(node).second) return;
            if (auto assignment = Is<Assign>(node)) {
                auto target = Is<Ident>(assignment->lval);
                if (target && target->vdef == binding) { found = true; return; }
            }
            if (auto incdec = Is<IncDec>(node)) {
                auto target = Is<Ident>(incdec->lval);
                if (target && target->vdef == binding) { found = true; return; }
            }
            node->Children([&](Node *child) { walk(child); });
            if (auto call = Is<Call>(node); call && call->fvbody) walk(call->fvbody);
        };
        walk(root);
        return found;
    };
    auto collect_overwritten_bindings = [&](Node *root) {
        unordered_set<const Node *> seen;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || !seen.insert(node).second) return;
            if (auto block = Is<Block>(node)) {
                for (size_t i = 0; i < block->stmts.size(); i++) {
                    if (auto declaration = Is<VarDecl>(block->stmts[i])) {
                        for (auto binding : declaration->defs) {
                            if (!binding || overwritten_before_read.count(binding)) continue;
                            for (size_t j = i + 1; j < block->stmts.size(); j++) {
                                auto statement = block->stmts[j];
                                if (auto assignment = Is<Assign>(statement)) {
                                    auto target = Is<Ident>(assignment->lval);
                                    if (assignment->op == T_ASSIGN && target && target->vdef == binding) {
                                        if (!has_read_of(assignment->rhs, binding))
                                            overwritten_before_read.insert(binding);
                                        break;
                                    }
                                }
                                if (has_read_of(statement, binding) || has_write_of(statement, binding)) break;
                            }
                        }
                    }
                    walk(block->stmts[i]);
                }
                walk(block->tail);
                return;
            }
            node->Children([&](Node *child) { walk(child); });
            if (auto call = Is<Call>(node); call && call->fvbody) walk(call->fvbody);
        };
        walk(root);
    };
    for (auto spec : ast.fnspecs) if (spec) collect_overwritten_bindings(spec->body);
    for (auto global : ast.globals) collect_overwritten_bindings(global);

    for (size_t id = 0; id < specializations.size(); id++) {
        auto &ref = specializations[id];
        record(cat("{\"kind\":\"specialization\",\"id\":", id,
                   ",\"file_id\":", ref.fileid >= 0 ? cat(ref.fileid) : string("null"),
                   ",\"path\":", LintJsonString(ref.path), ",\"start_byte\":",
                   ref.exact ? cat(ref.start) : string("null"), ",\"end_byte\":",
                   ref.exact ? cat(ref.end) : string("null"), ",\"start_line\":", ref.start_line,
                   ",\"end_line\":", ref.exact ? cat(ref.end_line) : cat(ref.start_line),
                   ",\"start_column\":", ref.exact ? cat(ref.start_column) : string("null"),
                   ",\"end_column\":", ref.exact ? cat(ref.end_column) : string("null"),
                   ",\"precision\":\"", ref.exact ? "exact" : "line", "\"",
                   ",\"name\":", LintJsonString(ref.name),
                   ",\"context\":", LintJsonString(ref.context),
                   ",\"entry_reachable\":",
                   entry_reachable_specs.count(ref.spec) ? string("true")
                   : reachability_complete ? string("false") : string("null"), "}"));
    }

    size_t call_id = 0;
    for (auto &ref : calls) {
        auto oldfile = ref.oldfile;
        auto fileid = oldfile >= 0 && (size_t)oldfile < fileids.size() ? fileids[oldfile] : -1;
        record(cat("{\"kind\":\"call\",\"id\":", call_id,
                   ",\"specialization_id\":",
                   ref.owner_id >= 0 ? cat(ref.owner_id) : string("null"),
                   ",\"file_id\":", fileid >= 0 ? cat(fileid) : string("null"),
                   ",\"path\":", LintJsonString(ref.path), ",",
                   type_span_fields(oldfile, ref.call),
                   ",\"callee_id\":", ref.callee.empty() ? string("null") : LintJsonString(ref.callee),
                   ",\"builtin_id\":", ref.builtin.empty() ? string("null") : LintJsonString(ref.builtin),
                   ",\"result_arity\":", ref.call->rettypes.size(),
                   ",\"arg_count\":", ref.call->ArgNodes().size(),
                   ",\"use_shape\":", LintJsonString(ref.use_shape), "}"));
        call_id++;
    }

    call_id = 0;
    for (auto &ref : calls) {
        auto decl = ref.use_shape == "tuple_binding" || ref.use_shape == "scalar"
                        ? Is<VarDecl>(ref.parent) : nullptr;
        for (size_t result_index = 0; result_index < ref.call->rettypes.size(); result_index++) {
            auto state = string("unknown");
            VarDef *binding = nullptr;
            if (ref.use_shape == "statement") state = "discarded";
            else if (ref.use_shape == "return") state = "returned";
            else if (ref.use_shape == "tuple_binding" && decl && result_index < decl->defs.size()) {
                state = "bound";
                binding = decl->defs[result_index];
            } else if (ref.use_shape == "scalar") {
                if (result_index > 0) state = "discarded";
                else if (decl && decl->defs.size() == 1) {
                    state = "bound";
                    binding = decl->defs[0];
                }
            }
            if (binding && overwritten_before_read.count(binding)) state = "overwritten";
            record(cat("{\"kind\":\"result_use\",\"call_id\":", call_id,
                       ",\"result_index\":", result_index,
                       ",\"state\":", LintJsonString(state), ",\"binding_name\":",
                       binding ? LintJsonString(binding->name) : string("null"),
                       ",\"referenced\":",
                       binding ? (referenced_bindings.count(binding) &&
                                  !overwritten_before_read.count(binding) ? string("true") : string("false"))
                               : string("null"), "}"));
        }
        call_id++;
    }

    for (size_t id = 0; id < calls.size(); id++) {
        auto &ref = calls[id];
        auto args = ref.call->ArgNodes();
        for (size_t arg_index = 0; arg_index < args.size(); arg_index++) {
            auto argument = LintUnwrapAutoRef(args[arg_index]);
            auto shape = string("other");
            string variable_id;
            int nested_call_id = -1;
            if (auto ident = Is<Ident>(argument); ident && ident->vdef) {
                if (auto it = variable_ids.find(ident->vdef); it != variable_ids.end()) {
                    shape = "identifier";
                    variable_id = it->second;
                }
            } else if (auto slice = Is<SliceExpr>(argument); slice && !slice->lo && !slice->hi) {
                auto base = LintIdentifier(slice->obj);
                if (base) if (auto it = variable_ids.find(base); it != variable_ids.end()) {
                    shape = "slice";
                    variable_id = it->second;
                }
            } else if (auto nested = Is<Call>(argument)) {
                if (auto it = call_ids.find(nested); it != call_ids.end()) {
                    shape = "call";
                    nested_call_id = it->second;
                }
            }
            record(cat("{\"kind\":\"call_argument\",\"call_id\":", id,
                       ",\"index\":", arg_index, ",\"shape\":", LintJsonString(shape),
                       ",\"variable_id\":", variable_id.empty() ? string("null") : LintJsonString(variable_id),
                       ",\"nested_call_id\":", nested_call_id < 0 ? string("null") : cat(nested_call_id), "}"));
        }
    }

    struct PureValueRef {
        const Node *node;
        int owner_id;
        int fileid;
        string path;
        string expression_kind;
        size_t start;
        size_t end;
        int start_line;
        int end_line;
    };
    vector<PureValueRef> pure_values;
    auto collect_pure_values = [&](FnSpec *owner, Node *root) {
        unordered_set<const Node *> seen;
        auto owner_id = owner ? specialization_ids.at(owner) : -1;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || !seen.insert(node).second) return;
            if (auto block = Is<Block>(node)) {
                for (auto statement : block->stmts) {
                    auto expression_kind = LintPureExpressionKind(statement);
                    if (LintPureExpression(statement)) {
                        auto source = LintSpan(ast, statement);
                        auto fileidx = statement->line.fileidx;
                        if (source && source->end_byte >= source->start_byte && fileidx >= 0 &&
                            (size_t)fileidx < ast.sources.size()) {
                            auto &contents = *ast.sources[fileidx].second;
                            pure_values.push_back({ statement, owner_id, fileids[fileidx],
                                project_path(fileidx), std::move(expression_kind),
                                source->start_byte, source->end_byte,
                                (int)LintLineAt(contents, source->start_byte),
                                (int)LintLineAt(contents, source->end_byte) });
                        }
                    }
                    walk(statement);
                }
                walk(block->tail);
                return;
            }
            if (auto call = Is<Call>(node)) {
                walk(call->callee);
                for (auto arg : call->args) walk(arg);
                if (call->trailing) walk((Node *)call->trailing);
                if (call->fvbody) walk(call->fvbody);
                return;
            }
            node->Children([&](Node *child) { walk(child); });
        };
        walk(root);
    };
    for (auto &ref : specializations) collect_pure_values(ref.spec, ref.spec->body);
    for (auto global : ast.globals) collect_pure_values(nullptr, global);
    stable_sort(pure_values.begin(), pure_values.end(), [](const auto &a, const auto &b) {
        return tie(a.path, a.start, a.end, a.expression_kind, a.owner_id) <
               tie(b.path, b.start, b.end, b.expression_kind, b.owner_id);
    });
    for (size_t id = 0; id < pure_values.size(); id++) {
        auto &value = pure_values[id];
        record(cat("{\"kind\":\"pure_value\",\"id\":", id,
                   ",\"specialization_id\":",
                   value.owner_id >= 0 ? cat(value.owner_id) : string("null"),
                   ",\"file_id\":", value.fileid, ",\"path\":", LintJsonString(value.path),
                   ",\"start_byte\":", value.start, ",\"end_byte\":", value.end,
                   ",\"start_line\":", value.start_line, ",\"end_line\":", value.end_line,
                   ",\"expression_kind\":", LintJsonString(value.expression_kind),
                   ",\"proof\":\"typed-subtree-effect-free-and-nontrapping\"}"));
    }

    struct OverflowGuardRef {
        FnSpec *owner;
        int owner_id;
        int fileid;
        string path;
        Binary *arithmetic;
        Binary *comparison;
        VarDecl *declaration;
        IfExpr *guard;
        string operation;
        string relation;
        string result_name;
        string source_name;
        bool is_signed;
        bool right_nonnegative;
        bool result_matches;
        bool source_matches;
        int width;
    };
    vector<OverflowGuardRef> overflow_guards;
    auto collect_overflow_guards = [&](FnSpec *owner, Node *root) {
        auto owner_id = owner ? specialization_ids.at(owner) : -1;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node) return;
            if (auto block = Is<Block>(node)) {
                for (size_t i = 0; i + 1 < block->stmts.size(); i++) {
                    auto declaration = Is<VarDecl>(block->stmts[i]);
                    auto guard = Is<IfExpr>(block->stmts[i + 1]);
                    if (!declaration || !guard || declaration->defs.size() != 1 ||
                        declaration->inits.size() != 1) continue;
                    auto arithmetic = Is<Binary>(declaration->inits[0]);
                    auto comparison = Is<Binary>(guard->cond);
                    if (!arithmetic || !comparison ||
                        (arithmetic->op != T_PLUS && arithmetic->op != T_MINUS) ||
                        (comparison->op != T_LT && comparison->op != T_GT)) continue;
                    auto type = arithmetic->exprtype;
                    if (!type || type->kind != TY_INT || type->intstorage == IS_VARINT) continue;
                    auto compared_result = LintIdentifier(comparison->left);
                    auto compared_source = LintIdentifier(comparison->right);
                    auto source = LintIdentifier(arithmetic->left);
                    if (!compared_result || !compared_source || !source) continue;
                    auto arithmetic_span = LintSpan(ast, arithmetic);
                    auto guard_span = LintSpan(ast, guard);
                    if (!arithmetic_span || !guard_span ||
                        arithmetic_span->end_byte < arithmetic_span->start_byte ||
                        guard_span->end_byte < guard_span->start_byte) continue;
                    auto fileidx = arithmetic->line.fileidx;
                    if (fileidx < 0 || (size_t)fileidx >= fileids.size() ||
                        guard->line.fileidx != fileidx) continue;
                    overflow_guards.push_back({ owner, owner_id, fileids[fileidx],
                        project_path(fileidx), arithmetic, comparison,
                        declaration, guard,
                        arithmetic->op == T_PLUS ? "add" : "subtract",
                        comparison->op == T_LT ? "lt" : "gt",
                        string(declaration->defs[0]->name),
                        string(source->name),
                        !IsUnsigned(type->intstorage),
                        LintKnownNonnegative(arithmetic->right),
                        compared_result == declaration->defs[0],
                        compared_source == source,
                        IntBits(type->intstorage) });
                }
                for (auto statement : block->stmts) walk(statement);
                walk(block->tail);
                return;
            }
            node->Children([&](Node *child) { walk(child); });
        };
        walk(root);
    };
    for (auto &ref : specializations) collect_overflow_guards(ref.spec, ref.spec->body);
    for (auto global : ast.globals) collect_overflow_guards(nullptr, global);
    stable_sort(overflow_guards.begin(), overflow_guards.end(), [](const auto &a, const auto &b) {
        return tie(a.owner_id, a.path, a.arithmetic->line.line, a.operation, a.relation) <
               tie(b.owner_id, b.path, b.arithmetic->line.line, b.operation, b.relation);
    });
    for (size_t id = 0; id < overflow_guards.size(); id++) {
        auto &ref = overflow_guards[id];
        auto arithmetic = LintSpan(ast, ref.arithmetic);
        auto guard = LintSpan(ast, ref.guard);
        auto &contents = *ast.sources[ref.arithmetic->line.fileidx].second;
        record(cat("{\"kind\":\"overflow_guard\",\"id\":", id,
                   ",\"specialization_id\":", ref.owner_id,
                   ",\"file_id\":", ref.fileid, ",\"path\":", LintJsonString(ref.path),
                   ",\"operation\":", LintJsonString(ref.operation),
                   ",\"signed\":", ref.is_signed, ",\"width\":", ref.width,
                   ",\"right_nonnegative\":", ref.right_nonnegative,
                   ",\"result_matches\":", ref.result_matches,
                   ",\"source_matches\":", ref.source_matches,
                   ",\"relation\":", LintJsonString(ref.relation),
                   ",\"result_name\":", LintJsonString(ref.result_name),
                   ",\"source_name\":", LintJsonString(ref.source_name),
                   ",\"arithmetic_start_byte\":", arithmetic->start_byte,
                   ",\"arithmetic_end_byte\":", arithmetic->end_byte,
                   ",\"arithmetic_start_line\":", LintLineAt(contents, arithmetic->start_byte),
                   ",\"arithmetic_end_line\":", LintLineAt(contents, arithmetic->end_byte),
                   ",\"arithmetic_start_column\":", LintColumnAt(contents, arithmetic->start_byte),
                   ",\"arithmetic_end_column\":", LintColumnAt(contents, arithmetic->end_byte),
                   ",\"guard_start_byte\":", guard->start_byte,
                   ",\"guard_end_byte\":", guard->end_byte,
                   ",\"guard_start_line\":", LintLineAt(contents, guard->start_byte),
                   ",\"guard_end_line\":", LintLineAt(contents, guard->end_byte),
                   ",\"guard_start_column\":", LintColumnAt(contents, guard->start_byte),
                   ",\"guard_end_column\":", LintColumnAt(contents, guard->end_byte), "}"));
    }

    struct SliceCaptureRef { size_t statement; VarDecl *declaration; VarDef *view; VarDef *root; SliceExpr *slice; };
    struct SliceGrowthRef { size_t statement; Call *call; VarDef *root; };
    struct SliceUseRef { size_t statement; Index *index; VarDef *view; VarDef *root; };
    struct SliceLengthRef {
        int owner_id;
        int fileid;
        string path;
        string view_name;
        string root_name;
        SliceExpr *capture;
        Call *growth;
        Index *use;
    };
    vector<SliceLengthRef> stale_slice_shapes;
    auto collect_slice_shapes = [&](FnSpec *owner, Node *root) {
        auto owner_id = owner ? specialization_ids.at(owner) : -1;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node) return;
            if (auto block = Is<Block>(node)) {
                vector<SliceCaptureRef> captures;
                vector<SliceGrowthRef> growths;
                vector<SliceUseRef> uses;
                for (size_t i = 0; i < block->stmts.size(); i++) {
                    auto declaration = Is<VarDecl>(block->stmts[i]);
                    if (declaration && declaration->defs.size() == 1 && declaration->inits.size() == 1) {
                        auto slice = Is<SliceExpr>(declaration->inits[0]);
                        auto base = slice && !slice->lo && !slice->hi ? LintIdentifier(slice->obj) : nullptr;
                        auto view = declaration->defs[0];
                        auto base_type = base ? base->type : nullptr;
                        bool growable = (base_type && IsArrayKind(base_type, A_GROW)) ||
                            (base_type && base_type->kind == TY_REF && IsArrayKind(base_type->ref->sub, A_GROW));
                        if (slice && base && growable && view->type && view->type->kind == TY_SLICE)
                            captures.push_back({ i, declaration, view, base, slice });
                    }
                    if (auto call = Is<Call>(block->stmts[i]); call &&
                        (call->builtin == B_APPEND || call->builtin == B_PUSH)) {
                        auto base = LintIdentifier(call->FirstArg());
                        bool grows = call->builtin == B_PUSH;
                        if (call->builtin == B_APPEND) {
                            auto args = call->ArgNodes();
                            if (args.size() > 1) {
                                if (auto literal = Is<ArrayLit>(args[1])) {
                                    grows = !literal->elems.empty() ||
                                        (Is<IntLit>(literal->fillcount) && Is<IntLit>(literal->fillcount)->val > 0);
                                } else if (auto ident = Is<Ident>(args[1]); ident && ident->vdef &&
                                           ident->vdef->type && ident->vdef->type->kind == TY_ARRAY &&
                                           ident->vdef->type->arr->akind == A_FIXED) {
                                    grows = ident->vdef->type->arr->size > 0;
                                }
                            }
                        }
                        if (base && grows) growths.push_back({ i, call, base });
                    }
                    // A use under a conditional has control-flow-dependent
                    // ordering, so only unconditional statements contribute.
                    auto stmt = block->stmts[i];
                    if (Is<IfExpr>(stmt) || Is<While>(stmt) || Is<ForLoop>(stmt) ||
                        Is<LoopExpr>(stmt) || Is<MatchExpr>(stmt)) continue;
                    unordered_set<const Node *> seen;
                    function<void(Node *)> find_indexes = [&](Node *inside) {
                        if (!inside || !seen.insert(inside).second) return;
                        if (auto index = Is<Index>(inside)) {
                            auto view = LintIdentifier(index->obj);
                            if (view) {
                                auto base = LintCurrentLengthRoot(index->idx);
                                if (base) uses.push_back({ i, index, view, base });
                            }
                        }
                        inside->Children([&](Node *child) { find_indexes(child); });
                    };
                    find_indexes(stmt);
                }
                for (auto &capture : captures) {
                    for (auto &growth : growths) {
                        if (growth.statement <= capture.statement || growth.root != capture.root) continue;
                        for (auto &use : uses) {
                            if (use.statement <= growth.statement || use.view != capture.view ||
                                use.root != capture.root || !LintIsCurrentLastIndex(use.index->idx, capture.root)) continue;
                            auto source_file = capture.slice->line.fileidx;
                            if (source_file < 0 || (size_t)source_file >= fileids.size() ||
                                growth.call->line.fileidx != source_file || use.index->line.fileidx != source_file ||
                                !LintSpan(ast, capture.slice) || !LintSpan(ast, growth.call) || !LintSpan(ast, use.index)) continue;
                            stale_slice_shapes.push_back({ owner_id, fileids[source_file],
                                project_path(source_file),
                                string(capture.view->name), string(capture.root->name),
                                capture.slice, growth.call, use.index });
                        }
                    }
                }
                for (auto statement : block->stmts) walk(statement);
                walk(block->tail);
                return;
            }
            node->Children([&](Node *child) { walk(child); });
        };
        walk(root);
    };
    for (auto &ref : specializations) collect_slice_shapes(ref.spec, ref.spec->body);
    for (auto global : ast.globals) collect_slice_shapes(nullptr, global);
    stable_sort(stale_slice_shapes.begin(), stale_slice_shapes.end(), [](const auto &a, const auto &b) {
        return tie(a.owner_id, a.path, a.capture->line.line, a.growth->line.line, a.use->line.line) <
               tie(b.owner_id, b.path, b.capture->line.line, b.growth->line.line, b.use->line.line);
    });
    for (size_t id = 0; id < stale_slice_shapes.size(); id++) {
        auto &ref = stale_slice_shapes[id];
        auto capture = LintSpan(ast, ref.capture);
        auto growth = LintSpan(ast, ref.growth);
        auto use = LintSpan(ast, ref.use);
        auto &contents = *ast.sources[ref.capture->line.fileidx].second;
        record(cat("{\"kind\":\"slice_length\",\"id\":", id,
                   ",\"specialization_id\":", ref.owner_id,
                   ",\"file_id\":", ref.fileid, ",\"path\":", LintJsonString(ref.path),
                   ",\"view_name\":", LintJsonString(ref.view_name),
                   ",\"root_name\":", LintJsonString(ref.root_name),
                   ",\"capture_before_growth\":true,\"growth_before_use\":true,"
                   "\"same_root\":true,\"index_uses_current_length\":true,"
                   "\"capture_start_byte\":", capture->start_byte, ",\"capture_end_byte\":", capture->end_byte,
                   ",\"capture_start_line\":", LintLineAt(contents, capture->start_byte),
                   ",\"capture_start_column\":", LintColumnAt(contents, capture->start_byte),
                   ",\"capture_end_column\":", LintColumnAt(contents, capture->end_byte),
                   ",\"growth_start_byte\":", growth->start_byte, ",\"growth_end_byte\":", growth->end_byte,
                   ",\"growth_start_line\":", LintLineAt(contents, growth->start_byte),
                   ",\"growth_start_column\":", LintColumnAt(contents, growth->start_byte),
                   ",\"growth_end_column\":", LintColumnAt(contents, growth->end_byte),
                   ",\"use_start_byte\":", use->start_byte, ",\"use_end_byte\":", use->end_byte,
                   ",\"use_start_line\":", LintLineAt(contents, use->start_byte),
                   ",\"use_end_line\":", LintLineAt(contents, use->end_byte),
                   ",\"use_start_column\":", LintColumnAt(contents, use->start_byte),
                   ",\"use_end_column\":", LintColumnAt(contents, use->end_byte), "}"));
    }

    for (size_t id = 0; id < sources.size(); id++) {
        auto oldid = sources[id].oldid;
        int unchecked_generics = 0, checked_specializations = 0;
        for (auto sf : ast.functions) {
            if (sf->line.fileidx != oldid) continue;
            if (!sf->generics.empty() && sf->specs.empty()) unchecked_generics++;
        }
        for (auto &ref : specializations)
            if (ref.fileid == (int)id && entry_reachable_specs.count(ref.spec))
                checked_specializations++;
        record(cat("{\"kind\":\"coverage\",\"file_id\":", id,
                   ",\"path\":", LintJsonString(sources[id].path),
                   ",\"parse\":\"complete\",\"semantic\":\"entry-reachable-specializations\","
                   "\"checked_specializations\":", checked_specializations,
                   ",\"unchecked_generics\":", unchecked_generics,
                   ",\"unsupported\":[",
                   reachability_complete ? string() : string("\"specialization_reachability\",\"specialization_fanout\""), "]}"));
    }
    record(cat("{\"kind\":\"end\",\"record_count\":", record_count,
               ",\"integrity\":\"fnv1a64:", LintHashHex(hash), "\"}"));
    return out;
}

}  // namespace goose
