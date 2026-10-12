// Goose compiler — Typed Goose Core, the `--emit-core` entry point.
#pragma once

namespace goose {

// Exports the checked program as a Core module and writes it to `path`. A
// program outside the pilot profile is a compile error and no file is written.
inline void EmitCore(Ast &ast, const string &entry, const string &path) {
    CoreModule mod;
    try {
        mod = CoreExporter(ast, entry).Export();
    } catch (CoreUnsupported &u) {
        string where = u.at.fileidx >= 0 && u.at.fileidx < (int)ast.sources.size()
                           ? cat(ast.sources[u.at.fileidx].first, ":", u.at.line) : string("?");
        auto msg = cat(where, ": error: unsupported in core-pilot: ", u.feature);
        if (u.at.fileidx >= 0 && u.at.fileidx < (int)ast.sources.size() && u.at.line > 0) {
            auto p = ast.sources[u.at.fileidx].second->c_str();
            for (auto ln = 1; *p && ln < u.at.line; p++) if (*p == '\n') ln++;
            auto end = p;
            while (*end && *end != '\n' && *end != '\r') end++;
            Append(msg, "\n", string_view(p, (size_t)(end - p)));
        }
        throw CompileError { msg };
    }
    CoreSummarizer(mod).Run();
    auto text = CoreWriter(mod).Write();
    // The limits of the reader: a module larger than 64 MiB, or nested more
    // than 256 deep, would only be refused there.
    auto where = ast.sources.empty() ? entry : cat(ast.sources[0].first, ":1");
    constexpr size_t MAX_BYTES = size_t(64) << 20;
    constexpr int MAX_DEPTH = 256;
    if (text.size() > MAX_BYTES)
        throw CompileError { cat(where, ": error: unsupported in core-pilot: module-size") };
    int depth = 0;
    bool instring = false;
    for (size_t i = 0; i < text.size(); i++) {
        auto c = text[i];
        if (instring) {
            if (c == '\\') i++;
            else if (c == '"') instring = false;
        } else if (c == '"') instring = true;
        else if (c == '[' && ++depth > MAX_DEPTH)
            throw CompileError { cat(where, ": error: unsupported in core-pilot: nesting-depth") };
        else if (c == ']') depth--;
    }
    auto f = fopen(path.c_str(), "wb");
    if (!f) throw CompileError { cat("cannot write Core file: ", path) };
    auto ok = fwrite(text.data(), 1, text.size(), f) == text.size();
    ok = fclose(f) == 0 && ok;
    if (!ok) {
        remove(path.c_str());
        throw CompileError { cat("cannot write Core file: ", path) };
    }
}

}  // namespace goose
