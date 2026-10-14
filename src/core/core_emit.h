// Goose compiler — Typed Goose Core, the `--emit-core` entry point.
#pragma once

namespace goose {

// Exports the checked program as a Core module and writes it to `path`, and
// when `girpath` is given lowers it to GIR-H, verifies that and writes it
// there. Either path may be empty. A
// program outside the pilot profile is a compile error and no file is written.
// Under `--pipeline gir` (`program` given) the module goes on to GIR-L and
// the C text of the program, which is left in `program`; the diagnostics of a
// feature outside the profile then say `pipeline gir`.
struct GirProgramText {
    string head, result;
    UnitSource unit;
};

inline void EmitCore(Ast &ast, const string &entry, const string &path, const string &girpath = {},
                     const string &lowpath = {}, GirProgramText *program = nullptr) {
    auto prefix = program ? "pipeline gir" : "core-pilot";
    CoreModule mod;
    try {
        mod = CoreExporter(ast, entry).Export();
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
    // The limits of the reader: a module larger than 64 MiB, or nested more
    // than 256 deep, would only be refused there.
    auto where = ast.sources.empty() ? entry : cat(ast.sources[0].first, ":1");
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
    // Lowered before anything is written, so that a module the verifier
    // refuses leaves no file behind.
    string girtext, lowtext;
    if (!girpath.empty() || !lowpath.empty() || program) {
        auto numbering = [&] { CoreWriter w(mod); w.Write(); return w; }();
        GirLowerer lowerer(mod, numbering.FileTable(), numbering.OriginTable(),
                           [&](const CoreOrigin &o) { return numbering.OriginId(o); });
        auto gir = lowerer.Lower();
        gir.diagfiles = numbering.DiagFileTable();
        gir.filemodules = numbering.FileModuleTable();
        if (auto v = GirVerifier(gir).Verify())
            throw CompileError { cat("internal compiler error: ", v->code, ": ", v->message) };
        ProposeGirEvidence(gir);
        if (auto v = GirVerifier(gir).Verify())
            throw CompileError { cat("internal compiler error: ", v->code, ": ", v->message) };
        if (!girpath.empty()) girtext = GirWriter(gir).Write();
        if (!lowpath.empty() || program) {
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
            if (!lowpath.empty()) lowtext = GirWriter(low).WriteLow();
            if (program) {
                auto c = GirCEmitter(low).Emit();
                program->head = std::move(c.head);
                program->result = std::move(c.result);
                program->unit = std::move(c.unit);
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
    if (!path.empty()) write(path, text, "Core");
    if (!girpath.empty()) write(girpath, girtext, "GIR-H");
    if (!lowpath.empty()) write(lowpath, lowtext, "GIR-L");
}

// Reports the complete set of Core profile features the checked program uses.
// It writes one machine-readable JSON record and never writes a Core module.
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
