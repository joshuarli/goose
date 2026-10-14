// Goose compiler — `goose build --units`: the program as units, compiled to
// objects that persist from one build to the next, and linked.
//
// Everything a build writes lives in one store directory per program build
// directory and contract:
//
//   <builddir>/store/<contract>/
//       units/          the unit sources of the last build and the runtime header
//       obj/            <unit>.<text digest>.o and, once it is whole, its record
//       tmp/            where the C compiler writes before an object is published
//       link.rec        the link digest and the executable it made
//       last.rec        what the last successful build read, for the no-op check
//       last.stdout, last.stderr   what that build printed, replayed on a no-op
//       units.rec       the unit text digests of the last successful build
//       .lock           held for the length of a build
//
// An object is a function of its unit's text, the headers the C compiler read
// and the contract, so its key holds all three. A different contract is a
// different directory, which is never touched by this one.
#pragma once

#include <atomic>
#include <mutex>
#include <thread>
#include "contract.h"

namespace goose {

// ---- What a build did, for the report's native_compile section. ----

struct UnitsBuildReport {
    bool enabled = false;
    bool no_op = false;
    string no_op_note;                     // Why the no-op check did not apply, if it did not.
    string store, contract;
    long long units_written = 0;
    vector<string> text_changed;           // Units whose text differs from the last build's.
    struct Invocation {
        vector<string> units;
        double wall = 0, cpu = -1;
        long long peak_rss = -1;
    };
    vector<Invocation> compiles;
    vector<Invocation> verification;       // Recompiles of reused objects, under --verify-reuse.
    long long reused = 0, missed = 0;
    struct Link {
        bool ran = false;
        double wall = 0, cpu = -1;
        long long peak_rss = -1;
    } link;
    vector<pair<string, string>> corrupt;  // Unit and what was wrong with its entry.
};
inline UnitsBuildReport units_build;

// ---- Small file helpers; this is the build step, not the compile. ----

inline bool UnitReadFile(const string &path, string &out) {
    auto f = fopen(path.c_str(), "rb");
    if (!f) return false;
    out.clear();
    char buf[1 << 16];
    for (;;) {
        auto n = fread(buf, 1, sizeof buf, f);
        if (!n) break;
        out.append(buf, n);
    }
    fclose(f);
    return true;
}

inline bool UnitWriteFile(const string &path, string_view text) {
    auto f = fopen(path.c_str(), "wb");
    if (!f) return false;
    auto ok = fwrite(text.data(), 1, text.size(), f) == text.size();
    return fclose(f) == 0 && ok;
}

// Writes under a temporary name in the same directory, then renames: the name
// others read is never a partial file.
inline bool UnitPublish(const string &path, string_view text) {
    auto tmp = path + ".tmp";
    if (!UnitWriteFile(tmp, text)) return false;
    std::error_code ec;
    filesystem::rename(filesystem::path(tmp), filesystem::path(path), ec);
    return !ec;
}

inline long long UnitFileSize(const string &path) {
    std::error_code ec;
    auto n = filesystem::file_size(filesystem::path(path), ec);
    return ec ? -1 : (long long)n;
}

inline string UnitFileDigest(const string &path) {
    string data;
    return UnitReadFile(path, data) ? Sha256::Of(data).Hex() : string();
}

inline bool UnitExecutableIdentityOf(const string &path, long long &size, string &digest) {
    string contents;
    if (!UnitReadFile(path, contents)) return false;
    size = (long long)contents.size();
    digest = Sha256::Of(contents).Hex();
    return true;
}

inline bool UnitExecutableMatches(const string &path, long long size, const string &digest) {
    long long actual_size;
    string actual_digest;
    return UnitExecutableIdentityOf(path, actual_size, actual_digest) &&
           actual_size == size && actual_digest == digest;
}

// The digest of a program the build runs or links with, found again only when
// its size or modification time changes.
inline string UnitBinaryDigest(string path) {
    if (path.find_first_of("/\\") == string::npos) {
        auto found = FindOnPath(path);
        if (!found.empty()) path = found;
    }
    std::error_code ec;
    auto real = filesystem::weakly_canonical(filesystem::path(path), ec).string();
    if (real.empty()) real = path;
    auto size = UnitFileSize(real);
    auto mtime = (long long)filesystem::last_write_time(filesystem::path(real), ec).time_since_epoch().count();
    auto cache = cat(GooseHome(), "/build/digests/", Hex8(real));
    string text;
    auto want = cat(size, " ", mtime, " ");
    if (UnitReadFile(cache, text) && text.compare(0, want.size(), want) == 0 && text.size() > want.size())
        return text.substr(want.size(), 64);
    auto digest = UnitFileDigest(real);
    if (digest.empty()) return "unreadable";
    WriteFileMakingDirs(cache, want + digest + "\n");
    return digest;
}

inline vector<string> UnitLines(const string &text) {
    vector<string> out;
    for (size_t a = 0; a < text.size();) {
        auto e = text.find('\n', a);
        if (e == string::npos) e = text.size();
        out.push_back(text.substr(a, e - a));
        a = e + 1;
    }
    return out;
}

inline UnitContractTarget UnitHostTarget() {
    string arch;
    #if defined(__x86_64__) || defined(_M_X64)
        arch = "x86_64";
    #elif defined(__aarch64__) || defined(_M_ARM64)
        arch = "aarch64";
    #else
        arch = "other";
    #endif
    string os;
    #if defined(_WIN32)
        os = "windows";
    #elif defined(__APPLE__)
        os = "macos";
    #else
        os = "unix";
    #endif
    return { arch, os, sizeof(void *) };
}

inline UnitContract MakeContract(const vector<string> &args, const string &goose_exe,
                                 const Builder &b) {
    UnitContractValues values;
    values.goose_digest = UnitBinaryDigest(goose_exe);
    values.runtime_version = RuntimeVersion();
    values.args = args;
    auto &tc = b.tc;
    values.c_compiler_digest = UnitBinaryDigest(tc.cc);
    values.c_compiler_version = tc.version;
    values.c_compiler_name = tc.name;
    values.c_compiler_style = tc.style;
    values.c_flags = b.CFlags();
    values.system_libs = b.SystemLibs();
    values.target = UnitHostTarget();
    for (auto name : { "GOOSE_STDLIB", "GOOSE_CC", "GOOSE_RUNTIME" }) {
        auto value = getenv(name);
        values.environment.push_back({ name, value ? value : "" });
    }
    return MakeContract(values);
}

// ---- Recording what a compile reads, and the no-op check. ----

class RecordedInputs : public InputRecorder {
    struct Entry {
        char kind;              // 'R' read, 'X' unreadable, 'P' exists, 'A' absent.
        string digest;
    };
    map<string, Entry> entries;
    std::mutex lock;

public:
    void Read(const string &path, const string *content) override {
        std::lock_guard<std::mutex> g(lock);
        entries[path] = content ? Entry { 'R', Sha256::Of(*content).Hex() } : Entry { 'X', "" };
    }
    void Probe(const string &path, bool exists) override {
        std::lock_guard<std::mutex> g(lock);
        entries.emplace(path, Entry { exists ? 'P' : 'A', "" });
    }
    // One line each, in path order.
    string Text() const {
        string t;
        for (auto &[path, e] : entries) t += cat(string(1, e.kind), "\t", e.digest, "\t", path, "\n");
        return t;
    }
};

// Whether every input a record names is as it was: each file read has the
// content it had, each unreadable one still is, and each path probed still
// exists or still does not. Reads nothing through the recorder.
inline bool InputsUnchanged(const vector<string> &lines) {
    for (auto &line : lines) {
        if (line.size() < 4 || line[1] != '\t') return false;
        auto tab = line.find('\t', 2);
        if (tab == string::npos) return false;
        auto digest = line.substr(2, tab - 2), path = line.substr(tab + 1);
        std::error_code ec;
        switch (line[0]) {
            case 'R': if (UnitFileDigest(path) != digest) return false; break;
            case 'X': { string d; if (UnitReadFile(path, d)) return false; break; }
            case 'P': case 'A': {
                bool exists;
                if (!path.empty() && path.back() == '/') {
                    // A directory is probed with a trailing slash.
                    exists = filesystem::is_directory(filesystem::path(path.substr(0, path.size() - 1)), ec);
                } else {
                    exists = filesystem::exists(filesystem::path(path), ec);
                }
                if (exists != (line[0] == 'P')) return false;
                break;
            }
            default: return false;
        }
    }
    return true;
}

// ---- The store. ----

struct UnitStore {
    string dir;                      // <builddir>/store/<contract>
    string Units() const { return dir + "/units"; }
    string Obj() const { return dir + "/obj"; }
    string Tmp() const { return dir + "/tmp"; }
    string Lock() const { return dir + "/.lock"; }
};

struct UnitObject {
    long long size = -1;
    string digest, text;
    vector<pair<string, string>> headers;   // Path and digest of each non-toolchain header read.
};

inline string UnitObjectBase(const string &unit, const string &textdigest) {
    return unit.substr(0, unit.size() - 2) + "." + textdigest.substr(0, 16);
}

inline bool ReadObjectRecord(const string &path, UnitObject &rec) {
    string text;
    if (!UnitReadFile(path, text)) return false;
    auto lines = UnitLines(text);
    if (lines.empty() || lines[0] != "goose-unit-object/1") return false;
    auto complete = false;
    for (size_t i = 1; i < lines.size(); i++) {
        auto &l = lines[i];
        if (l.compare(0, 5, "size ") == 0) rec.size = atoll(l.c_str() + 5);
        else if (l.compare(0, 7, "digest ") == 0) rec.digest = l.substr(7);
        else if (l.compare(0, 5, "text ") == 0) rec.text = l.substr(5);
        else if (l.compare(0, 7, "header ") == 0) {
            auto tab = l.find('\t', 7);
            if (tab == string::npos) return false;
            rec.headers.push_back({ l.substr(7, tab - 7), l.substr(tab + 1) });
        } else if (l == "end") complete = true;
    }
    return complete;
}

// The headers a compiler's dependency file names, other than the source
// itself: `a.o: a.c h1.h h2.h \` with continuations and escaped spaces.
inline vector<string> DependencyHeaders(const string &depfile, const string &source) {
    string text;
    vector<string> out;
    if (!UnitReadFile(depfile, text)) return out;
    auto colon = text.find(": ");
    if (colon == string::npos) return out;
    string tok;
    auto flush = [&]() {
        if (!tok.empty() && tok != source) out.push_back(tok);
        tok.clear();
    };
    for (size_t i = colon + 2; i < text.size(); i++) {
        auto c = text[i];
        if (c == '\\' && i + 1 < text.size() && text[i + 1] == '\n') { flush(); i++; }
        else if (c == '\\' && i + 1 < text.size() && text[i + 1] == ' ') { tok += ' '; i++; }
        else if (c == ' ' || c == '\n' || c == '\r') flush();
        else tok += c;
    }
    flush();
    return out;
}

// What the build needs from the compile and the command line.
struct UnitsBuildInput {
    const Toolchain *tc = nullptr;
    const BuildOptions *opts = nullptr;
    UnitStore store;
    UnitContract contract;
    string exe;
    vector<string> rsps;                 // The native parts' response files.
    vector<string> include_headers;      // --include, absolute.
    bool rebuild = false, verify = false;
    FILE *msgs = nullptr;
};

// The units in link order: by file name, which is by unit key.
struct UnitToBuild {
    string file, text, textdigest;
    string source;                        // The unit's path in the store.
    string objbase;                       // obj/<unit>.<digest>, without extension.
    string objkey;                        // The object's key once known.
    UnitObject rec;
    bool reused = false;
};

inline string ObjectKeyOf(const UnitToBuild &u, const string &contract) {
    Canon c;
    c.Tag('O').Str(u.textdigest).Str(contract);
    vector<string> headers;
    for (auto &[path, digest] : u.rec.headers) headers.push_back(path + "\t" + digest);
    sort(headers.begin(), headers.end());
    c.U(headers.size());
    for (auto &h : headers) c.Str(h);
    return c.Hash().Hex();
}

// Compiles `units` (in one process where the compiler takes several) to
// objects in the store's tmp directory, and publishes each with its record.
// `want` says which of them to compile.
class NativeCompiler {
    const UnitsBuildInput &in;
    std::mutex lock;
    bool failed = false;

public:
    explicit NativeCompiler(const UnitsBuildInput &i) : in(i) {}

    string TmpObject(const UnitToBuild &u) const {
        auto stem = u.file.substr(0, u.file.size() - 2);
        return cat(in.store.Tmp(), "/", stem, in.tc->style == "msvc" ? ".obj" : ".o");
    }

    vector<string> Command(const vector<const UnitToBuild *> &batch) const {
        auto &tc = *in.tc;
        vector<string> argv = { tc.cc };
        for (auto &f : in.contract.c_flags) argv.push_back(f);
        if (tc.style == "msvc") {
            argv.push_back("/c");
            argv.push_back(batch[0]->source);
            argv.push_back(cat("/Fo:", TmpObject(*batch[0])));
            if (in.opts->debug) argv.push_back(cat("/Fd:", TmpObject(*batch[0]), ".pdb"));
        } else {
            // The compiler's own account of the headers it reads, except the
            // system's: the dependencies of the object besides its unit.
            argv.push_back("-MMD");
            argv.push_back("-c");
            for (auto u : batch) argv.push_back(u->source);
        }
        return argv;
    }

    // Runs one batch; false when the compiler failed, after saying so.
    bool Compile(const vector<const UnitToBuild *> &batch, UnitsBuildReport::Invocation &inv) {
        auto argv = Command(batch);
        if (in.opts->dryrun || in.opts->verbose) {
            std::lock_guard<std::mutex> g(lock);
            fprintf(in.msgs, "%s\n", CommandLineText(argv).c_str());
        }
        for (auto u : batch) inv.units.push_back(u->file);
        if (in.opts->dryrun) return true;
        for (auto u : batch) {
            std::error_code ec;
            filesystem::remove(filesystem::path(TmpObject(*u)), ec);
        }
        ProcessUsage usage;
        auto r = RunProcess(argv, in.store.Tmp(), in.opts->verbose, &usage);
        inv.wall = usage.wall;
        inv.cpu = usage.cpu;
        inv.peak_rss = usage.peak_rss;
        if (r.started && r.code == 0) return true;
        std::lock_guard<std::mutex> g(lock);
        failed = true;
        string names;
        for (auto u : batch) names += " " + u->file;
        fprintf(stderr, "compiling%s failed%s:\n    %s\n", names.c_str(),
                r.started ? cat(" (exit ", r.code, ")").c_str() : "", CommandLineText(argv).c_str());
        if (!in.opts->verbose) fputs(r.output.c_str(), stderr);
        return false;
    }

    // Moves a compiled object into the store: the object first, under its
    // final name by rename, and only then the record that makes it usable.
    bool Publish(UnitToBuild &u) {
        auto tmp = TmpObject(u);
        auto size = UnitFileSize(tmp);
        if (size < 0) return false;
        string data;
        UnitReadFile(tmp, data);
        u.rec = UnitObject();
        u.rec.size = size;
        u.rec.digest = Sha256::Of(data).Hex();
        u.rec.text = u.textdigest;
        auto stem = u.file.substr(0, u.file.size() - 2);
        for (auto &h : DependencyHeaders(cat(in.store.Tmp(), "/", stem, ".d"), u.source)) {
            auto path = h;
            if (!path.empty() && path[0] != '/') path = cat(in.store.Tmp(), "/", path);
            u.rec.headers.push_back({ path, UnitFileDigest(path) });
        }
        // Without a dependency file (MSVC gives none), the headers the build
        // knows of: the runtime's, and the program's own. Where there is one it
        // is the compiler's own account, which names each unit's headers only.
        if (u.rec.headers.empty()) {
            auto header = in.store.Units() + "/goose_runtime.h";
            u.rec.headers.push_back({ header, UnitFileDigest(header) });
            for (auto &h : in.include_headers) u.rec.headers.push_back({ h, UnitFileDigest(h) });
        }
        auto obj = cat(in.store.Obj(), "/", u.objbase, in.tc->style == "msvc" ? ".obj" : ".o");
        std::error_code ec;
        filesystem::rename(filesystem::path(tmp), filesystem::path(obj), ec);
        if (ec) return false;
        string rec = cat("goose-unit-object/1\nsize ", u.rec.size, "\ndigest ", u.rec.digest, "\ntext ",
                         u.rec.text, "\n");
        for (auto &[p, d] : u.rec.headers) rec += cat("header ", p, "\t", d, "\n");
        rec += "end\n";
        return UnitPublish(cat(in.store.Obj(), "/", u.objbase, ".rec"), rec);
    }

    bool Failed() const { return failed; }
};

inline string UnitObjectPath(const UnitsBuildInput &in, const UnitToBuild &u) {
    return cat(in.store.Obj(), "/", u.objbase, in.tc->style == "msvc" ? ".obj" : ".o");
}

// What the store holds for a unit, if it can be used: the object exists, its
// completion record is whole, the size is the recorded one, and the headers it
// was compiled against are as they were. In verification mode the object's
// digest is checked too. A bad entry is removed and reported.
inline bool LookupObject(const UnitsBuildInput &in, UnitToBuild &u) {
    auto obj = UnitObjectPath(in, u);
    auto recpath = cat(in.store.Obj(), "/", u.objbase, ".rec");
    std::error_code ec;
    auto have = PathExists(obj), haverec = PathExists(recpath);
    auto discard = [&](const string &why) {
        filesystem::remove(filesystem::path(obj), ec);
        filesystem::remove(filesystem::path(recpath), ec);
        units_build.corrupt.push_back({ u.file, why });
        return false;
    };
    if (!have && !haverec) return false;
    if (have && !haverec) return discard("an object without its completion record");
    UnitObject rec;
    if (!have) return discard("a completion record without its object");
    if (!ReadObjectRecord(recpath, rec)) return discard("an unreadable completion record");
    if (rec.text != u.textdigest) return discard("a record for other text");
    if (UnitFileSize(obj) != rec.size) return discard("an object whose size is not the recorded one");
    if (in.verify && UnitFileDigest(obj) != rec.digest)
        return discard("an object whose digest is not the recorded one");
    for (auto &[path, digest] : rec.headers)
        if (UnitFileDigest(path) != digest) return false;     // A header changed: not corrupt, stale.
    u.rec = rec;
    return true;
}

// The command that links `objects` with the runtime object and the native
// parts, as today's single-file link does without the C file.
inline vector<string> UnitLinkCommand(const UnitsBuildInput &in, const vector<string> &objects,
                                      const string &runtime_object) {
    auto &tc = *in.tc;
    vector<string> argv = { tc.cc };
    for (auto &f : in.contract.c_flags) argv.push_back(f);
    if (tc.style == "msvc") {
        argv.push_back(cat("/Fe:", in.exe));
        argv.push_back(cat("/Fo:", in.store.Tmp(), "\\"));
        for (auto &o : objects) argv.push_back(o);
        if (!runtime_object.empty()) argv.push_back(runtime_object);
        for (auto &r : in.rsps) argv.push_back(cat("@", r));
    } else {
        for (auto &o : objects) argv.push_back(o);
        if (!runtime_object.empty()) argv.push_back(runtime_object);
        argv.push_back("-o");
        argv.push_back(in.exe);
        for (auto &r : in.rsps) argv.push_back(cat("@", r));
        for (auto &l : in.contract.system_libs) argv.push_back(l);
    }
    return argv;
}

// Everything after the compile: the objects, the link, the records and the
// clean-up. The units' text is in unit_stats.files and on disk in the store.
// `runtime_object` is the runtime's object ("" for none). The exit code.
inline int BuildUnitObjects(UnitsBuildInput &in, const string &runtime_object) {
    auto &rep = units_build;
    auto &tc = *in.tc;
    auto &opts = *in.opts;
    std::error_code ec;
    for (auto d : { in.store.Obj(), in.store.Tmp() })
        filesystem::create_directories(filesystem::path(d), ec);

    // The units, in link order.
    vector<UnitToBuild> units;
    for (auto &[file, text] : unit_stats.files) {
        if (file.size() < 2 || file.compare(file.size() - 2, 2, ".c") != 0) continue;
        UnitToBuild u;
        u.file = file;
        u.text = text;
        u.textdigest = Sha256::Of(text).Hex();
        u.source = cat(in.store.Units(), "/", file);
        u.objbase = UnitObjectBase(file, u.textdigest);
        units.push_back(std::move(u));
    }
    sort(units.begin(), units.end(), [](auto &a, auto &b) { return a.file < b.file; });
    rep.units_written = (long long)units.size();

    // Which units' text is not what the last successful build had.
    {
        string last;
        map<string, string> before;
        if (UnitReadFile(in.store.dir + "/units.rec", last))
            for (auto &l : UnitLines(last)) {
                auto tab = l.find('\t');
                if (tab != string::npos) before[l.substr(0, tab)] = l.substr(tab + 1);
            }
        for (auto &u : units)
            if (before[u.file] != u.textdigest) rep.text_changed.push_back(u.file);
    }

    // What the store can give.
    vector<UnitToBuild *> missing;
    for (auto &u : units) {
        if (!in.rebuild && !opts.dryrun && LookupObject(in, u)) {
            u.reused = true;
            rep.reused++;
        } else {
            missing.push_back(&u);
            rep.missed++;
        }
    }

    // Compile what it cannot: small units together, several processes at once.
    NativeCompiler compiler(in);
    auto compile_missing = [&](vector<UnitToBuild *> list, vector<UnitsBuildReport::Invocation> &record) -> bool {
        sort(list.begin(), list.end(), [](auto *a, auto *b) { return a->text.size() > b->text.size(); });
        constexpr size_t kBatchBytes = 256 * 1024;
        constexpr size_t kBatchUnits = 16;
        vector<vector<const UnitToBuild *>> batches;
        vector<const UnitToBuild *> cur;
        size_t bytes = 0;
        for (auto u : list) {
            if (tc.style == "msvc" || u->text.size() >= kBatchBytes) {
                batches.push_back({ u });
                continue;
            }
            cur.push_back(u);
            bytes += u->text.size();
            if (bytes >= kBatchBytes || cur.size() >= kBatchUnits) {
                batches.push_back(std::move(cur));
                cur.clear();
                bytes = 0;
            }
        }
        if (!cur.empty()) batches.push_back(std::move(cur));
        vector<UnitsBuildReport::Invocation> invs(batches.size());
        vector<char> ok(batches.size(), 1);
        std::atomic<size_t> next { 0 };
        auto jobs = opts.verbose ? 1u : max(1u, std::thread::hardware_concurrency());
        auto worker = [&]() {
            for (;;) {
                auto i = next++;
                if (i >= batches.size()) return;
                ok[i] = compiler.Compile(batches[i], invs[i]);
            }
        };
        vector<std::thread> pool;
        for (unsigned t = 1; t < min<size_t>(jobs, batches.size()); t++) pool.emplace_back(worker);
        worker();
        for (auto &t : pool) t.join();
        for (auto &i : invs) if (!i.units.empty()) record.push_back(std::move(i));
        for (auto c : ok) if (!c) return false;
        return true;
    };
    if (!compile_missing(missing, rep.compiles)) return 1;
    if (!opts.dryrun)
        for (auto u : missing)
            if (!compiler.Publish(*u)) {
                fprintf(stderr, "cannot publish the object of %s\n", u->file.c_str());
                return 1;
            }

    // Verification: every reused object recompiled and compared.
    if (in.verify && !opts.dryrun) {
        vector<UnitToBuild *> again;
        for (auto &u : units) if (u.reused) again.push_back(&u);
        if (!compile_missing(again, rep.verification)) return 1;
        for (auto u : again) {
            string stored, fresh;
            UnitReadFile(UnitObjectPath(in, *u), stored);
            UnitReadFile(compiler.TmpObject(*u), fresh);
            filesystem::remove(filesystem::path(compiler.TmpObject(*u)), ec);
            if (stored != fresh) {
                fprintf(stderr, "--verify-reuse: the object of %s recompiled differs from the stored one\n",
                        u->file.c_str());
                return 1;
            }
        }
    }
    for (auto &u : units) u.objkey = ObjectKeyOf(u, in.contract.digest);

    // The link, unless what it would make is there.
    vector<string> objects;
    for (auto &u : units) objects.push_back(UnitObjectPath(in, u));
    Canon link;
    link.Tag('L').Str(in.exe);
    for (auto &u : units) link.Str(u.objkey);
    link.Str(runtime_object).Str(runtime_object.empty() ? "" : UnitFileDigest(runtime_object));
    for (auto &r : in.rsps) link.Str(r).Str(UnitFileDigest(r));
    auto command = UnitLinkCommand(in, objects, runtime_object);
    for (auto &f : in.contract.c_flags) link.Str(f);
    for (auto &f : in.contract.system_libs) link.Str(f);
    auto linkdigest = link.Hash().Hex();
    string linkrec;
    auto skip = false;
    if (!in.rebuild && !opts.dryrun && UnitReadFile(in.store.dir + "/link.rec", linkrec)) {
        auto lines = UnitLines(linkrec);
        if (lines.size() == 5 && lines[0] == "goose-unit-link/2" && lines[1] == linkdigest &&
            lines[2] == in.exe &&
            UnitExecutableMatches(in.exe, atoll(lines[3].c_str()), lines[4]))
            skip = true;
    }
    if (opts.dryrun || opts.verbose) {
        if (!skip) fprintf(in.msgs, "%s\n", CommandLineText(command).c_str());
    }
    if (!skip && !opts.dryrun) {
        // An interrupted link must not leave a record that says it finished.
        filesystem::remove(filesystem::path(in.store.dir + "/link.rec"), ec);
        ProcessUsage usage;
        fflush(in.msgs);
        auto r = RunProcess(command, "", opts.verbose, &usage);
        rep.link.ran = true;
        rep.link.wall = usage.wall;
        rep.link.cpu = usage.cpu;
        rep.link.peak_rss = usage.peak_rss;
        if (!(r.started && r.code == 0)) {
            fprintf(stderr, "building %s failed%s:\n    %s\n", in.exe.c_str(),
                    r.started ? cat(" (exit ", r.code, ")").c_str() : "", CommandLineText(command).c_str());
            if (!opts.verbose) fputs(r.output.c_str(), stderr);
            return 1;
        }
        UnitPublish(in.store.dir + "/link.rec",
                    cat("goose-unit-link/2\n", linkdigest, "\n", in.exe, "\n",
                        UnitFileSize(in.exe), "\n", UnitFileDigest(in.exe), "\n"));
    }
    if (opts.dryrun) return 0;

    // The build succeeded: record its units, and drop what nothing refers to.
    string recorded;
    for (auto &u : units) recorded += u.file + "\t" + u.textdigest + "\n";
    UnitPublish(in.store.dir + "/units.rec", recorded);
    set<string> keep;
    for (auto &u : units) {
        keep.insert(u.objbase + ".o");
        keep.insert(u.objbase + ".obj");
        keep.insert(u.objbase + ".rec");
    }
    for (auto &e : filesystem::directory_iterator(filesystem::path(in.store.Obj()), ec)) {
        auto name = e.path().filename().string();
        if (!keep.count(name)) filesystem::remove(e.path(), ec);
    }
    set<string> current = { "goose_runtime.h" };
    for (auto &u : units) current.insert(u.file);
    for (auto &e : filesystem::directory_iterator(filesystem::path(in.store.Units()), ec)) {
        auto name = e.path().filename().string();
        if (!current.count(name) && name != "units.txt") filesystem::remove(e.path(), ec);
    }
    for (auto &e : filesystem::directory_iterator(filesystem::path(in.store.Tmp()), ec))
        filesystem::remove(e.path(), ec);
    return 0;
}

// ---- Output of the units build to the report. ----

inline void ReportNativeCompileJson(JsonOut &j) {
    auto &r = units_build;
    if (!r.enabled) {
        j.Null();
        return;
    }
    j.Obj();
    j.F("mode", "units").F("no_op", r.no_op).F("store", r.store).F("contract", r.contract);
    j.Key("no_op_unavailable");
    if (r.no_op_note.empty()) j.Null();
    else j.Str(r.no_op_note);
    j.Key("frontend_phases").Arr();
    if (g_build_report)
        for (int p = 0; p < kPhases; p++)
            if (g_build_report->rec.phase[p].ran && (Phase)p != Phase::ReportCollection)
                j.Str(PhaseName((Phase)p));
    j.EndArr();
    j.F("units_written", r.units_written);
    j.Key("units_text_changed").Arr();
    for (auto &u : r.text_changed) j.Str(u);
    j.EndArr();
    j.Key("native_compiler_invocations").Arr();
    for (auto &c : r.compiles) {
        j.Obj();
        j.Key("units").Arr();
        for (auto &u : c.units) j.Str(u);
        j.EndArr();
        j.F("wall_seconds", c.wall);
        j.Key("cpu_seconds");
        if (c.cpu < 0) j.Null(); else j.Num(c.cpu);
        j.Key("peak_rss_bytes").OptInt(c.peak_rss);
        j.EndObj();
    }
    j.EndArr();
    // Under --verify-reuse the reused objects are compiled again; those
    // processes are not the build's own.
    j.Key("verification_invocations").Arr();
    for (auto &c : r.verification) {
        j.Obj().Key("units").Arr();
        for (auto &u : c.units) j.Str(u);
        j.EndArr().F("wall_seconds", c.wall).Key("peak_rss_bytes").OptInt(c.peak_rss).EndObj();
    }
    j.EndArr();
    j.F("objects_reused", r.reused).F("objects_missed", r.missed);
    j.Key("link").Obj().F("ran", r.link.ran).F("wall_seconds", r.link.wall);
    j.Key("cpu_seconds");
    if (r.link.cpu < 0) j.Null(); else j.Num(r.link.cpu);
    j.Key("peak_rss_bytes").OptInt(r.link.peak_rss);
    j.EndObj();
    j.Key("corrupt_entries").Arr();
    for (auto &[unit, why] : r.corrupt) j.Obj().F("unit", unit).F("what", why).EndObj();
    j.EndArr();
    j.EndObj();
}

// The report of a build that ran nothing.
inline void WriteNoOpReport(const string &path, const string &input) {
    JsonOut j;
    j.Obj().F("format", kBuildReportFormat);
    j.Key("input").Obj().F("file", input).F("mode", "no-op").EndObj();
    j.Key("extensions").Obj();
    j.Key("sharing").Null().Key("units").Null();
    j.Key("native_compile");
    ReportNativeCompileJson(j);
    j.EndObj().EndObj();
    if (!UnitWriteFile(path, j.Text() + "\n")) throw CompileError { cat("cannot write build report: ", path) };
}

}  // namespace goose
