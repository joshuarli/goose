// Goose compiler — the emission post-pass: merging emitted functions whose
// bodies are equal (--share) and naming emitted functions from stable keys
// (--stable-names). It runs on the finished text of the code section, so it
// changes nothing about what is emitted until it has decided what the new
// text is, and a program built without either option never reaches it.
//
// Equality is textual. A function's text, with every reference to another
// emitted function replaced by that function's class, is what the C compiler
// sees of it; two functions with equal text and equal callee classes behave
// alike wherever they are called, whatever contexts they were checked for.
// Classes are the coarsest partition that is consistent with this: they start
// from the text with callees erased and are split until the callees' classes
// agree. That is the fixpoint of the bottom-up computation over strongly
// connected components, reached without ordering the members of a component,
// so it does not depend on the order in which functions were created.
#pragma once

namespace goose {

// Calls f(true, token, member) for each identifier in C text and
// f(false, text, false) for what lies between them; `member` says the
// identifier follows `.` or `->`, so it names a field and not a function. String and character literals, comments and
// numbers are never identifiers, so a literal that spells a function's name
// is not a reference to it.
template<typename F> void ScanC(string_view t, F &&f) {
    size_t i = 0, n = t.size(), start = 0;
    auto flush = [&](size_t upto) {
        if (upto > start) f(false, t.substr(start, upto - start), false);
    };
    while (i < n) {
        auto c = t[i];
        if (c == '"' || c == '\'') {
            auto j = i + 1;
            while (j < n && t[j] != c) j += t[j] == '\\' ? 2 : 1;
            i = min(j + 1, n);
        } else if (c == '/' && i + 1 < n && t[i + 1] == '*') {
            auto e = t.find("*/", i + 2);
            i = e == string_view::npos ? n : e + 2;
        } else if (c == '/' && i + 1 < n && t[i + 1] == '/') {
            auto e = t.find('\n', i);
            i = e == string_view::npos ? n : e;
        } else if (isdigit((unsigned char)c)) {
            while (i < n && (isalnum((unsigned char)t[i]) || t[i] == '_' || t[i] == '.')) i++;
        } else if (isalpha((unsigned char)c) || c == '_') {
            auto j = i;
            while (j < n && (isalnum((unsigned char)t[j]) || t[j] == '_')) j++;
            flush(i);
            auto k = i;
            while (k > 0 && (t[k - 1] == ' ' || t[k - 1] == '\n')) k--;
            auto member = k > 0 && (t[k - 1] == '.' || (t[k - 1] == '>' && k > 1 && t[k - 2] == '-'));
            f(true, t.substr(i, j - i), member);
            i = start = j;
        } else {
            i++;
        }
    }
    flush(n);
}

struct NameHash {
    using is_transparent = void;
    size_t operator()(string_view s) const { return hash<string_view>()(s); }
};
using NameMap = unordered_map<string, string, NameHash, equal_to<>>;

inline string RenameC(string_view text, const NameMap &names) {
    string out;
    out.reserve(text.size());
    ScanC(text, [&](bool ident, string_view tok, bool member) {
        if (ident && !member) {
            auto it = names.find(tok);
            if (it != names.end()) { out += it->second; return; }
        }
        out.append(tok.data(), tok.size());
    });
    return out;
}

struct PostPassFn {
    EmitSeg *seg = nullptr;
    Digest skeleton;                 // The text with every emitted function's name erased.
    vector<int> refs;                // The functions it names, in order of appearance.
    string signature;
    // The lines of the skeleton and whether each is a bounds check, to say
    // how two bodies differ.
    vector<pair<uint64_t, bool>> lines;
    int cls = 0;
    Digest instance;                 // Declaration key and lowering key.
    string candidate;                // Its name in the stable scheme, before disambiguation.
    Digest context;
};

// The lowering key of an emitted function: what can change its body or its
// signature, with the context-dependent facts the optimizing
// passes used. Facts available but unused are not recorded by the passes and
// so are not in it; a fact recorded and not used only makes the key finer.
inline Digest LoweringInstanceKey(CodeGen &cg, const EmitSeg &seg) {
    auto sp = seg.sp;
    auto &km = cg.Keys();
    auto &ctx = km.Context(sp);
    Canon c;
    c.Tag('I').Dig(km.Decl(sp->sf).digest).B(seg.twin);
    c.U(sp->argtypes.size());
    for (size_t i = 0; i < sp->argtypes.size(); i++) {
        c.Dig(km.Type(sp->argtypes[i]).digest);
        // The physical form of a reference parameter: address, header and
        // stack, or pool reference.
        c.I(cg.IsPoolParam(sp, i) ? 2 : cg.IsFatRef(sp->argtypes[i]) ? 1 : 0);
        c.B(cg.IsResz(sp->argtypes[i]));
    }
    c.U(sp->rets.size());
    for (auto r : sp->rets) c.Dig(km.Type(r).digest);
    auto &info = cg.sinfo[sp];
    c.U(info.freevars.size());
    for (auto fv : info.freevars) {
        c.Dig(km.Type(fv->type).digest);
        c.B(fv->reusable != 0);
    }
    // Bound function values and literal parameters; the targets it may
    // propagate to, and whether it catches one.
    c.Dig(ctx.dims[(int)SpecDim::FunctionValues]).Dig(ctx.dims[(int)SpecDim::LiteralParams]);
    c.Dig(ctx.dims[(int)SpecDim::NonlocalTargets]).B(cg.fromids.count(sp) != 0);
    // Consumed assumptions: the exactness and concreteness the code
    // generator reads to cache a stack top, the entry facts of
    // bounds-check elimination, and each call inlined into the body.
    c.U(sp->roots.size());
    for (auto &r : sp->roots) c.B(r.exact).B(r.concrete);
    auto entry = consumed_assumptions.entry.find(sp);
    c.Str(entry == consumed_assumptions.entry.end() ? string_view() : string_view(entry->second));
    vector<Digest> inlined;
    auto it = consumed_assumptions.inlined.find(sp);
    if (it != consumed_assumptions.inlined.end())
        for (auto callee : it->second) inlined.push_back(km.Context(callee).total);
    sort(inlined.begin(), inlined.end());
    c.U(inlined.size());
    for (auto &d : inlined) c.Dig(d);
    return c.Hash();
}

inline void EmitPostPass(CodeGen &cg) {
    auto &segs = cg.emitsegs;
    if (segs.empty()) return;
    auto wall0 = BuildRecorder::Wall(), cpu0 = BuildRecorder::Cpu();
    auto share = emit_options.share, stable = emit_options.stable_names;
    auto n = (int)segs.size();
    vector<PostPassFn> fns(n);
    unordered_map<string_view, int> byname;
    for (int i = 0; i < n; i++) {
        fns[i].seg = &segs[i];
        byname[segs[i].name] = i;
    }

    // The skeleton of each body: its text with the names of emitted
    // functions erased, and the order in which it named them.
    for (int i = 0; i < n; i++) {
        auto &f = fns[i];
        string skeleton;
        ScanC(string_view(cg.code).substr(f.seg->begin, f.seg->end - f.seg->begin),
              [&](bool ident, string_view tok, bool member) {
                  if (ident && !member) {
                      auto it = byname.find(tok);
                      if (it != byname.end()) {
                          skeleton += '\x01';
                          f.refs.push_back(it->second);
                          return;
                      }
                  }
                  skeleton.append(tok.data(), tok.size());
              });
        f.skeleton = Sha256::Of(skeleton);
        f.signature = skeleton.substr(0, skeleton.find('\n'));
        if (emit_options.explain) {
            for (size_t a = 0; a < skeleton.size();) {
                auto e = skeleton.find('\n', a);
                if (e == string::npos) e = skeleton.size();
                auto line = string_view(skeleton).substr(a, e - a);
                f.lines.push_back({ hash<string_view>()(line),
                                    line.find("GS_IDX(") != string_view::npos });
                a = e + 1;
            }
        }
    }

    // Classes.
    int nclasses = 0;
    if (share) {
        map<Digest, int> ids;
        for (auto &f : fns) f.cls = ids.emplace(f.skeleton, (int)ids.size()).first->second;
        nclasses = (int)ids.size();
        // Split classes whose members name different classes, and look again
        // only at the classes that name a class that was just split: a body
        // is recomputed when something it calls changed, not on every round.
        vector<vector<int>> mem(nclasses);
        for (int i = 0; i < n; i++) mem[fns[i].cls].push_back(i);
        vector<vector<int>> users(n);
        for (int i = 0; i < n; i++)
            for (auto r : fns[i].refs) users[r].push_back(i);
        vector<int> work;
        vector<char> queued(nclasses, 0);
        for (int c = 0; c < nclasses; c++)
            if (mem[c].size() > 1) { work.push_back(c); queued[c] = 1; }
        while (!work.empty()) {
            auto round = std::move(work);
            work.clear();
            for (auto c : round) queued[c] = 0;
            for (auto c : round) {
                if (mem[c].size() < 2) continue;
                unordered_map<string, vector<int>> groups;
                vector<string> order;
                for (auto m : mem[c]) {
                    string key;
                    key.reserve(fns[m].refs.size() * sizeof(int));
                    for (auto r : fns[m].refs) key.append((const char *)&fns[r].cls, sizeof(int));
                    auto [it, fresh] = groups.try_emplace(std::move(key));
                    it->second.push_back(m);
                    if (fresh) order.push_back(it->first);
                }
                if (groups.size() < 2) continue;
                auto old = std::move(mem[c]);
                mem[c] = std::move(groups[order[0]]);
                for (size_t g = 1; g < order.size(); g++) {
                    auto id = (int)mem.size();
                    mem.push_back(std::move(groups[order[g]]));
                    queued.push_back(0);
                    for (auto m : mem[id]) fns[m].cls = id;
                }
                for (auto m : old)
                    for (auto u : users[m])
                        if (!queued[fns[u].cls]) { queued[fns[u].cls] = 1; work.push_back(fns[u].cls); }
            }
        }
        nclasses = (int)mem.size();
    } else {
        for (int i = 0; i < n; i++) fns[i].cls = i;
        nclasses = n;
    }
    vector<vector<int>> members(nclasses);
    for (int i = 0; i < n; i++) members[fns[i].cls].push_back(i);

    // Names.
    vector<string> finalname(nclasses);
    vector<int> rep(nclasses);
    auto less_name = [&](int a, int b) { return segs[a].name < segs[b].name; };
    share_stats = ShareStats();
    share_stats.stable = stable;
    if (!stable) {
        for (int c = 0; c < nclasses; c++) {
            rep[c] = *min_element(members[c].begin(), members[c].end(), less_name);
            finalname[c] = segs[rep[c]].name;
        }
    } else {
        for (int i = 0; i < n; i++) {
            auto &f = fns[i];
            f.instance = LoweringInstanceKey(cg, segs[i]);
            f.context = cg.Keys().Context(segs[i].sp).total;
            f.candidate = cat(cg.Sanitize(segs[i].sp->sf->ns, segs[i].sp->sf->name),
                              segs[i].twin ? "_er_" : "_", f.instance.Short());
        }
        auto less_cand = [&](int a, int b) { return fns[a].candidate < fns[b].candidate; };
        map<string, vector<int>> bycand;
        for (int c = 0; c < nclasses; c++) {
            rep[c] = *min_element(members[c].begin(), members[c].end(), less_cand);
            bycand[fns[rep[c]].candidate].push_back(c);
        }
        for (auto &[cand, group] : bycand) {
            if (group.size() == 1) {
                finalname[group[0]] = cand;
                continue;
            }
            // Equal declaration and lowering keys, different classes: the
            // key missed something that shaped the body. Order the classes
            // by their content and context, which do not depend on the
            // order of creation.
            auto mincontext = [&](int c) {
                Digest best = fns[members[c][0]].context;
                for (auto m : members[c]) best = min(best, fns[m].context);
                return best;
            };
            sort(group.begin(), group.end(), [&](int a, int b) {
                return make_tuple(fns[rep[a]].skeleton, mincontext(a), segs[rep[a]].sp->id) <
                       make_tuple(fns[rep[b]].skeleton, mincontext(b), segs[rep[b]].sp->id);
            });
            for (size_t k = 1; k < group.size(); k++)
                if (fns[rep[group[k]]].skeleton != fns[rep[group[0]]].skeleton) {
                    share_stats.incomplete_lowering_keys++;
                    break;
                }
            for (size_t k = 0; k < group.size(); k++) {
                auto c = group[k];
                Canon d;
                d.Str(cand).Dig(fns[rep[c]].skeleton).Dig(mincontext(c)).U(k);
                auto prefix = cand.substr(0, cand.size() - 16);
                finalname[c] = prefix + d.Hash().Short();
            }
        }
    }

    // The renaming: every emitted function to its class's name.
    NameMap rename;
    unordered_set<string> removed;
    for (int i = 0; i < n; i++) {
        auto &to = finalname[fns[i].cls];
        if (segs[i].name != to) rename[segs[i].name] = to;
        if (rep[fns[i].cls] != i) removed.insert(segs[i].name);
    }
    if (stable) {
        for (auto &[sp, name] : cg.thunks) {
            auto it = byname.find(cg.sinfo[sp].cname);
            if (it == byname.end()) continue;
            rename[name] = cat("gs_tmain_", fns[it->second].candidate.substr(0, fns[it->second].candidate.size() - 17),
                               "_", Sha256::Of(finalname[fns[it->second].cls]).Short());
        }
        // A new name that is already a symbol of the program, or that two
        // entities share, is an error.
        unordered_set<string> old, seen;
        for (auto &seg : segs) old.insert(seg.name);
        for (auto &[sp, name] : cg.thunks) old.insert(name);
        auto claim = [&](const string &name) {
            if (!seen.insert(name).second || (cg.used.count(name) && !old.count(name)))
                cg.Fail(Line {}, cat("symbol collision: ", name));
        };
        for (int c = 0; c < nclasses; c++) claim(finalname[c]);
        for (auto &[sp, name] : cg.thunks) {
            auto it = rename.find(name);
            if (it != rename.end()) claim(it->second);
        }
    }

    // Rebuild the code section: removed bodies dropped, the others and all
    // between them renamed.
    auto oldcode = std::move(cg.code);
    string code;
    code.reserve(oldcode.size());
    size_t cursor = 0;
    long long bytes_before = 0, bytes_after = 0;
    vector<size_t> newlen(n, 0);
    for (int i = 0; i < n; i++) {
        auto &seg = segs[i];
        bytes_before += (long long)(seg.end - seg.begin);
        code += RenameC(string_view(oldcode).substr(cursor, seg.begin - cursor), rename);
        cursor = seg.end;
        if (rep[fns[i].cls] != i) continue;
        auto before = code.size();
        code += RenameC(string_view(oldcode).substr(seg.begin, seg.end - seg.begin), rename);
        newlen[i] = code.size() - before;
        bytes_after += (long long)newlen[i];
    }
    code += RenameC(string_view(oldcode).substr(cursor), rename);
    cg.code = std::move(code);

    // Prototypes: those of removed functions go, the rest are renamed.
    string protos;
    for (size_t a = 0; a < cg.protos.size();) {
        auto e = cg.protos.find('\n', a);
        if (e == string::npos) e = cg.protos.size();
        auto line = string_view(cg.protos).substr(a, min(e - a + 1, cg.protos.size() - a));
        a = e + 1;
        auto paren = line.find('(');
        auto start = paren == string_view::npos ? 0 : line.rfind(' ', paren) + 1;
        if (paren != string_view::npos && removed.count(string(line.substr(start, paren - start))))
            continue;
        protos += RenameC(line, rename);
    }
    cg.protos = std::move(protos);
    cg.data = RenameC(cg.data, rename);

    for (int c = 0; c < nclasses; c++) cg.classrep[finalname[c]] = segs[rep[c]].sp;
    // What the rest of the compiler reads of the names.
    for (auto &seg : segs) {
        auto it = rename.find(seg.name);
        if (it == rename.end()) continue;
        if (seg.twin) cg.ernames[seg.sp] = it->second;
        else cg.sinfo[seg.sp].cname = it->second;
    }
    for (auto &[sp, name] : cg.thunks) {
        auto it = rename.find(name);
        if (it != rename.end()) name = it->second;
    }

    // The build report reads the bytes of each body.
    if (build_recorder) {
        build_recorder->body_bytes = 0;
        for (auto &[sf, e] : build_recorder->emitted) e.bytes = 0;
        for (int i = 0; i < n; i++) {
            build_recorder->emitted[segs[i].sp->sf].bytes += (long long)newlen[i];
            build_recorder->body_bytes += (long long)newlen[i];
        }
    }

    // What was found.
    auto &st = share_stats;
    st.ran = true;
    st.wall_seconds = BuildRecorder::Wall() - wall0;
    st.cpu_seconds = BuildRecorder::Cpu() - cpu0;
    st.functions_before = n;
    st.bytes_before = bytes_before;
    st.bytes_after = bytes_after;
    st.code_before = (long long)oldcode.size();
    st.code_after = (long long)cg.code.size();
    for (int c = 0; c < nclasses; c++) {
        if (members[c].size() > 1) st.multi_classes++;
        st.functions_after++;
    }
    unordered_map<const SFunction *, vector<int>> classes_of;
    for (int c = 0; c < nclasses; c++) classes_of[segs[rep[c]].sp->sf].push_back(rep[c]);
    for (auto &[sf, reps] : classes_of) {
        st.implementations[sf] = (long long)reps.size();
        // Classes of one declaration with equal signatures that stayed
        // apart: why, by the first cause that explains it.
        sort(reps.begin(), reps.end(), less_name);
        auto &a = fns[reps[0]];
        for (size_t k = 1; k < reps.size(); k++) {
            auto &b = fns[reps[k]];
            if (a.signature != b.signature) continue;
            if (a.seg->twin != b.seg->twin) continue;
            auto bytes = (long long)newlen[reps[k]];
            if (a.skeleton == b.skeleton) { st.distinct_callee++; st.callee_bytes += bytes; continue; }
            auto inl = [&](const PostPassFn &f) {
                vector<Digest> v;
                auto it = consumed_assumptions.inlined.find(f.seg->sp);
                if (it != consumed_assumptions.inlined.end())
                    for (auto cal : it->second) v.push_back(cg.Keys().Context(cal).total);
                sort(v.begin(), v.end());
                return v;
            };
            if (inl(a) != inl(b)) { st.distinct_inlined++; st.inlined_bytes += bytes; continue; }
            // Bodies of the same shape whose lines differ only where one
            // of them checks a bound.
            auto onlychecks = a.lines.size() == b.lines.size();
            auto diffs = 0;
            for (size_t l = 0; onlychecks && l < a.lines.size(); l++) {
                if (a.lines[l].first == b.lines[l].first) continue;
                diffs++;
                onlychecks = a.lines[l].second || b.lines[l].second;
            }
            onlychecks = onlychecks && diffs > 0;
            if (onlychecks) { st.distinct_bounds_checks++; st.bounds_check_bytes += bytes; }
            else { st.distinct_other++; st.other_bytes += bytes; }
        }
    }
}

}  // namespace goose
