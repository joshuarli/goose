#pragma once

namespace goose {

struct GirProgramText {
    string head, result;
    UnitSource unit;
};

struct CoreEmitRequest {
    string entry;
    string corePath;
    string highGirPath;
    string lowGirPath;
    GirProgramText *program = nullptr;
    optional<string> constructionTracePath;
};

inline void EmitCore(Ast &ast, const CoreEmitRequest &request) {
    if (request.constructionTracePath && !request.program)
        throw CompileError { "construction trace requires GIR compilation" };
    auto prefix = request.program ? "pipeline gir" : "core-pilot";
    CoreModule mod;
    try {
        mod = CoreExporter(ast, request.entry).Export();
    } catch (CoreUnsupported &u) {
        string where = u.at.fileidx >= 0 && u.at.fileidx < (int)ast.sources.size()
                           ? cat(ast.sources[u.at.fileidx].first, ":", u.at.line) : string("?");
        auto msg = cat(where, ": error: unsupported in ", prefix, ": ", u.feature);
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
    auto where = ast.sources.empty() ? request.entry : cat(ast.sources[0].first, ":1");
    constexpr size_t MAX_BYTES = size_t(64) << 20;
    constexpr int MAX_DEPTH = 256;
    if (text.size() > MAX_BYTES)
        throw CompileError { cat(where, ": error: unsupported in ", prefix, ": module-size") };
    int depth = 0;
    bool instring = false;
    for (size_t i = 0; i < text.size(); i++) {
        auto c = text[i];
        if (instring) {
            if (c == '\\') i++;
            else if (c == '"') instring = false;
        } else if (c == '"') instring = true;
        else if (c == '[' && ++depth > MAX_DEPTH)
            throw CompileError { cat(where, ": error: unsupported in ", prefix, ": nesting-depth") };
        else if (c == ']') depth--;
    }
    string girtext, lowtext;
    if (!request.highGirPath.empty() || !request.lowGirPath.empty() || request.program) {
        auto numbering = [&] { CoreWriter w(mod); w.Write(); return w; }();
        GirLowerer lowerer(mod, numbering.FileTable(), numbering.OriginTable(),
                           [&](const CoreOrigin &o) { return numbering.OriginId(o); });
        auto gir = lowerer.Lower();
        gir.diagfiles = numbering.DiagFileTable();
        gir.filemodules = numbering.FileModuleTable();
        if (auto v = GirVerifier(gir).Verify())
            throw CompileError { cat("internal compiler error: ", v->code, ": ", v->message) };
        NormalizeGirEvidenceInputs(gir);
        ProposeGirEvidence(gir);
        if (auto v = GirVerifier(gir).Verify())
            throw CompileError { cat("internal compiler error: ", v->code, ": ", v->message) };
        if (!request.highGirPath.empty()) girtext = GirWriter(gir).Write();
        if (!request.lowGirPath.empty() || request.program) {
            GirModule low;
            try {
                low = GirToLow(gir).Lower();
            } catch (GirLowerUnsupported &u) {
                string where = "?";
                if (u.org >= 0 && u.org < (int)gir.origins.size()) {
                    auto &o = gir.origins[u.org];
                    where = cat(o.file < (int)gir.diagfiles.size() ? gir.diagfiles[o.file] : string("?"), ":", o.line);
                }
                throw CompileError { cat(where, ": error: unsupported in ", prefix, ": ", u.feature,
                                         " (in ", u.where, ")") };
            }
            if (auto v = GirVerifier(low).Verify())
                throw CompileError { cat("internal compiler error: ", v->code, ": ", v->message) };
            if (!request.lowGirPath.empty()) lowtext = GirWriter(low).WriteLow();
            if (request.program) {
                auto c = GirCEmitter(low, request.constructionTracePath).Emit();
                request.program->head = std::move(c.head);
                request.program->result = std::move(c.result);
                request.program->unit = std::move(c.unit);
            }
        }
    }
    auto write = [&](const string &file, const string &contents, const char *what) {
        auto f = fopen(file.c_str(), "wb");
        if (!f) throw CompileError { cat("cannot write ", what, " file: ", file) };
        auto ok = fwrite(contents.data(), 1, contents.size(), f) == contents.size();
        ok = fclose(f) == 0 && ok;
        if (!ok) {
            remove(file.c_str());
            throw CompileError { cat("cannot write ", what, " file: ", file) };
        }
    };
    if (!request.corePath.empty()) write(request.corePath, text, "Core");
    if (!request.highGirPath.empty()) write(request.highGirPath, girtext, "GIR-H");
    if (!request.lowGirPath.empty()) write(request.lowGirPath, lowtext, "GIR-L");
}

inline void EmitCoreReport(Ast &ast, const string &entry) {
    CoreExporter exporter(ast, entry, CoreExportMode::Report);
    try {
        (void)exporter.Export();
    } catch (CoreUnsupported &u) {
        throw CompileError { cat("cannot complete Core feature report: ", u.feature) };
    }
    auto features = exporter.UnsupportedFeatures();
    fputs("{\"unsupported\":[", stdout);
    for (size_t i = 0; i < features.size(); i++) {
        if (i) fputc(',', stdout);
        fprintf(stdout, "\"%s\"", features[i].c_str());
    }
    fputs("]}\n", stdout);
}

}  // namespace goose
