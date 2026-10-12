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
