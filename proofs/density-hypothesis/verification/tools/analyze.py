#!/usr/bin/env python3
"""Analyse the output of Scan.lean over a whole build.

usage: analyze.py <out-dir> <root-constant>[,<root-constant>...] <scan-file-or-dir>...

Each scan file is (gzipped) JSONL with one record per module (see Scan.lean). A directory argument
is tagged with its base name; all `*.jsonl.gz` files inside are read.

Outputs (in <out-dir>):
  summary.json        all headline numbers
  topo_order.tsv      idx, module, tag for every module, imports first
  reachable_axioms.txt, all_axioms.txt, duplicates.txt, anomalies.txt
"""
import array, collections, glob, gzip, json, os, sys, time

outdir, roots_arg, *inputs = sys.argv[1:]
roots = roots_arg.split(",")
os.makedirs(outdir, exist_ok=True)
t0 = time.time()

name_id = {}
names = []
def gid(s):
    i = name_id.get(s)
    if i is None:
        i = len(names); name_id[s] = i; names.append(s)
    return i

mod_id = {}
mods = []           # module names
mod_tag = []
mod_imports = []    # list of (import module name, importAll, isExported, isMeta)
mod_parts = []
mod_ismodule = []

occ_name = array.array("I")
occ_mod = array.array("I")
occ_kind = array.array("B")
occ_flags = array.array("B")
occ_thash = array.array("Q")
occ_vhash = array.array("Q")
occ_nlvl = array.array("H")
occ_estart = array.array("Q")
edges = array.array("I")

pub_kind_pairs = collections.Counter()   # (tag, publicKind, privateKind)
pub_codes = collections.Counter()        # (tag, code)
pub_bad = []
errors = []
dup_in_part = []
priv_kinds = collections.Counter()       # (tag, kind)
flag_counts = collections.Counter()
n_pub = collections.Counter()

files = []
for inp in inputs:
    if os.path.isdir(inp):
        tag = os.path.basename(os.path.normpath(inp))
        for f in sorted(glob.glob(os.path.join(inp, "*.jsonl.gz"))):
            files.append((tag, f))
    else:
        files.append((os.path.basename(inp).split(".")[0], inp))

for tag, f in files:
    with gzip.open(f, "rt") as fh:
        for line in fh:
            d = json.loads(line)
            if "error" in d:
                errors.append((tag, d["m"], d["error"])); continue
            m = d["m"]
            if m in mod_id:
                errors.append((tag, m, "module scanned twice")); continue
            mid = len(mods); mod_id[m] = mid; mods.append(m); mod_tag.append(tag)
            mod_imports.append([tuple(x) for x in d["imports"]])
            mod_parts.append(d["parts"]); mod_ismodule.append(d["isModule"])
            for x in d["dup"]:
                dup_in_part.append((m, x))
            loc = [gid(s) for s in d["names"]]
            for c in d["priv"]:
                i, kind, flags, thash, vhash, nlvl, used = c
                occ_name.append(loc[i]); occ_mod.append(mid); occ_kind.append(ord(kind)); occ_flags.append(flags)
                occ_thash.append(thash); occ_vhash.append(vhash); occ_nlvl.append(min(nlvl, 65535))
                occ_estart.append(len(edges))
                edges.extend(loc[j] for j in used)
                priv_kinds[(tag, kind)] += 1
                if flags:
                    flag_counts[(tag, flags)] += 1
            for c in d["pub"]:
                i, pk, qk, code, hasval = c
                pub_kind_pairs[(tag, pk, qk, hasval)] += 1
                pub_codes[(tag, code)] += 1
                n_pub[tag] += 1
                if code != 15:
                    pub_bad.append((m, d["names"][i], pk, qk, code))
    print(f"read {f}: modules={len(mods)} occ={len(occ_name)} names={len(names)} edges={len(edges)} t={time.time()-t0:.0f}s", flush=True)
occ_estart.append(len(edges))
nocc = len(occ_name)

# name -> occurrences
by_name = collections.defaultdict(list)
for o in range(nocc):
    by_name[occ_name[o]].append(o)

# duplicates: same name declared in more than one module
dups = {n: os_ for n, os_ in by_name.items() if len(os_) > 1}
dup_stats = collections.Counter()
dup_lines = []
for n, os_ in dups.items():
    kinds = "".join(sorted(chr(occ_kind[o]) for o in os_))
    same_type = len({(occ_thash[o], occ_nlvl[o]) for o in os_}) == 1
    same_val = len({occ_vhash[o] for o in os_}) == 1
    tags = ",".join(sorted({mod_tag[occ_mod[o]] for o in os_}))
    key = (kinds if len(kinds) <= 4 else kinds[:4] + "+", same_type, same_val)
    dup_stats[key] += 1
    if len(dup_lines) < 200000:
        dup_lines.append(f"{names[n]}\t{kinds}\tsameType={same_type}\tsameValue={same_val}\t{tags}\t" + ",".join(mods[occ_mod[o]] for o in os_[:6]))
with open(os.path.join(outdir, "duplicates.txt"), "w") as fh:
    fh.write("\n".join(dup_lines) + "\n")

# ---------------- import graph and topological order ----------------
missing_imports = collections.Counter()
import_all = []
adj = []
for mid, imps in enumerate(mod_imports):
    a = []
    for (im, ia, ie, imeta) in imps:
        j = mod_id.get(im)
        if j is None:
            missing_imports[im] += 1
        else:
            a.append(j)
        if ia:
            import_all.append((mods[mid], im))
    adj.append(a)

# iterative DFS post-order from every module (imports first); deterministic
state = bytearray(len(mods))
order = []
cycle = []
for root in range(len(mods)):
    if state[root]:
        continue
    stack = [(root, 0)]
    state[root] = 1
    while stack:
        v, i = stack.pop()
        if i < len(adj[v]):
            stack.append((v, i + 1))
            u = adj[v][i]
            if state[u] == 0:
                state[u] = 1
                stack.append((u, 0))
            elif state[u] == 1:
                cycle.append((mods[v], mods[u]))
        else:
            state[v] = 2
            order.append(v)
pos = [0] * len(mods)
for i, v in enumerate(order):
    pos[v] = i
bad_order = sum(1 for v in range(len(mods)) for u in adj[v] if pos[u] >= pos[v])

def closure_of(module_names):
    seen = set()
    st = [mod_id[m] for m in module_names if m in mod_id]
    seen.update(st)
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u); st.append(u)
    return seen

# ---------------- reachability over constants ----------------
def reach(root_names, allowed_mods):
    """Constants reachable from the roots. A name is resolved to *every* declaration of that name
    in a module of `allowed_mods` (the import closure of the root's module), so the result is an
    upper bound whichever duplicate Lean picks."""
    seen = bytearray(len(names))
    parent = {}
    st = []
    missing_roots = []
    for r in root_names:
        i = name_id.get(r)
        if i is None or i not in by_name:
            missing_roots.append(r); continue
        seen[i] = 1; st.append(i)
    undefined = set()
    reached_occ = bytearray(nocc)
    while st:
        n = st.pop()
        os_ = [o for o in by_name.get(n, ()) if occ_mod[o] in allowed_mods]
        if not os_:
            undefined.add(n); continue
        for o in os_:
            reached_occ[o] = 1
            for e in range(occ_estart[o], occ_estart[o + 1]):
                u = edges[e]
                if not seen[u]:
                    seen[u] = 1; st.append(u); parent[u] = n
    return seen, undefined, missing_roots, reached_occ, parent

summary = {
    "modules": len(mods),
    "modules_by_tag": dict(collections.Counter(mod_tag)),
    "modules_not_module_system": [mods[i] for i in range(len(mods)) if not mod_ismodule[i]][:50],
    "modules_with_parts": {str(k): v for k, v in collections.Counter(mod_parts).items()},
    "constant_occurrences": nocc,
    "distinct_names": len(names),
    "edges": len(edges),
    "scan_errors": errors[:50],
    "duplicate_within_one_part": dup_in_part[:50],
    "private_part_kinds": {f"{t}:{k}": v for (t, k), v in sorted(priv_kinds.items())},
    "unsafe_or_partial": {f"{t}:{fl}": v for (t, fl), v in sorted(flag_counts.items())},
    "public_part_constants": dict(n_pub),
    "public_vs_private_kinds": {f"{t}:{pk}->{qk}:hasValue={hv}": v for (t, pk, qk, hv), v in sorted(pub_kind_pairs.items())},
    "public_vs_private_codes": {f"{t}:{c}": v for (t, c), v in sorted(pub_codes.items())},
    "public_not_view_of_private": pub_bad[:50],
    "names_declared_in_several_modules": len(dups),
    "duplicate_stats": {f"{k[0]}:sameType={k[1]}:sameValue={k[2]}": v for k, v in sorted(dup_stats.items(), key=lambda kv: -kv[1])[:60]},
    "imports_not_scanned": dict(missing_imports),
    "import_all_edges": len(import_all),
    "import_all_examples": import_all[:20],
    "import_cycles": cycle[:10],
    "topological_order_violations": bad_order,
}

# all genuine axioms (kind A in the most private part)
all_axioms = collections.defaultdict(list)
for o in range(nocc):
    if occ_kind[o] == ord("A"):
        all_axioms[names[occ_name[o]]].append(mods[occ_mod[o]])
with open(os.path.join(outdir, "all_axioms.txt"), "w") as fh:
    for n in sorted(all_axioms):
        fh.write(f"{n}\t{','.join(all_axioms[n][:5])}\n")
summary["axioms_declared_anywhere"] = len(all_axioms)
summary["axioms_declared_by_tag"] = dict(collections.Counter(mod_tag[mod_id[ms[0]]] for ms in all_axioms.values()))

kindname = {ord("A"): "axiom", ord("D"): "definition", ord("T"): "theorem", ord("O"): "opaque", ord("Q"): "quot",
            ord("I"): "inductive", ord("C"): "constructor", ord("R"): "recursor"}
anomalies = []
summary["roots"] = {}
for r in roots:
    root_mods = [mods[occ_mod[o]] for o in by_name.get(name_id.get(r, -1), [])]
    allowed = closure_of(root_mods)
    seen, undefined, missing_roots, reached_occ, parent = reach([r], allowed)
    kinds = collections.Counter(); tags = collections.Counter(); flags = collections.Counter()
    ax = set(); modset = set()
    flagged = []
    for o in range(nocc):
        if reached_occ[o]:
            kinds[kindname[occ_kind[o]]] += 1
            tags[mod_tag[occ_mod[o]]] += 1
            modset.add(occ_mod[o])
            if occ_flags[o]:
                flags[occ_flags[o]] += 1
                if len(flagged) < 20:
                    flagged.append(names[occ_name[o]])
            if occ_kind[o] == ord("A"):
                ax.add(names[occ_name[o]])
    def chain(nm):
        out = [nm]; i = name_id[nm]
        while i in parent and len(out) < 40:
            i = parent[i]; out.append(names[i])
        return out
    info = {
        "found": not missing_roots,
        "declared_in": root_mods,
        "import_closure_modules": len(allowed),
        "import_closure_by_tag": dict(collections.Counter(mod_tag[v] for v in allowed)),
        "reachable_names": int(sum(seen)),
        "reachable_declarations": int(sum(reached_occ)),
        "reachable_flagged_examples": flagged,
        "axiom_chains": {a: chain(a) for a in sorted(ax) if a not in ("propext", "Classical.choice", "Quot.sound")},
        "reachable_by_kind": dict(kinds),
        "reachable_by_tag": dict(tags),
        "reachable_modules": len(modset),
        "reachable_unsafe_or_partial": {str(k): v for k, v in flags.items()},
        "axioms": sorted(ax),
        "referenced_but_declared_nowhere": sorted(names[u] for u in undefined)[:100],
        "referenced_but_declared_nowhere_count": len(undefined),
    }
    summary["roots"][r] = info
    with open(os.path.join(outdir, f"reachable_axioms_{r.replace('.', '_')}.txt"), "w") as fh:
        fh.write("\n".join(sorted(ax)) + "\n")

# dependency edges must respect the module order: a constant may only refer to constants declared
# in its own module or in a module that comes earlier in the topological order (some occurrence)
viol = 0
viol_examples = []
undefined_all = 0
first_pos = {}
for n, os_ in by_name.items():
    first_pos[n] = min(pos[occ_mod[o]] for o in os_)
for o in range(nocc):
    pm = pos[occ_mod[o]]
    for e in range(occ_estart[o], occ_estart[o + 1]):
        u = edges[e]
        fp = first_pos.get(u)
        if fp is None:
            undefined_all += 1
            if len(anomalies) < 200:
                anomalies.append(f"undeclared\t{names[occ_name[o]]}\t{mods[occ_mod[o]]}\t->\t{names[u]}")
        elif fp > pm:
            viol += 1
            if len(viol_examples) < 50:
                viol_examples.append((names[occ_name[o]], mods[occ_mod[o]], names[u]))
summary["references_to_undeclared_names"] = undefined_all
summary["references_to_later_modules"] = viol
summary["references_to_later_modules_examples"] = viol_examples
with open(os.path.join(outdir, "anomalies.txt"), "w") as fh:
    fh.write("\n".join(anomalies) + "\n")

with open(os.path.join(outdir, "topo_order.tsv"), "w") as fh:
    for i, v in enumerate(order):
        fh.write(f"{i}\t{mods[v]}\t{mod_tag[v]}\n")

# import closures of the modules that declare the roots
for r in roots:
    root_mods = sorted({mods[occ_mod[o]] for o in by_name.get(name_id.get(r, -1), [])})
    if not root_mods:
        continue
    cl = closure_of(root_mods)
    tag0 = r.replace(".", "_")
    with open(os.path.join(outdir, f"closure_{tag0}.tsv"), "w") as fh:
        for v in sorted(cl, key=lambda v: pos[v]):
            fh.write(f"{pos[v]}\t{mods[v]}\t{mod_tag[v]}\n")
    # direct imports that cross from one tag to another, per importing tag
    ext = collections.defaultdict(collections.Counter)
    for v in cl:
        for (im, ia, ie, imeta) in mod_imports[v]:
            j = mod_id.get(im)
            if j is None or mod_tag[j] != mod_tag[v]:
                ext[mod_tag[v]][("all:" if ia else "") + im] += 1
    summary.setdefault("closures", {})[r] = {
        "declared_in": root_mods,
        "modules": len(cl),
        "by_tag": dict(collections.Counter(mod_tag[v] for v in cl)),
        "cross_tag_direct_imports": {t: len(c) for t, c in ext.items()},
    }
    with open(os.path.join(outdir, f"cross_imports_{tag0}.json"), "w") as fh:
        json.dump({t: sorted(c) for t, c in ext.items()}, fh)

ia_targets = collections.defaultdict(set)
for mid, imps in enumerate(mod_imports):
    for (im, ia, ie, imeta) in imps:
        if ia:
            ia_targets[im].add(mods[mid])
with open(os.path.join(outdir, "import_all.tsv"), "w") as fh:
    for tgt in sorted(ia_targets):
        ttag = mod_tag[mod_id[tgt]] if tgt in mod_id else "?"
        for src in sorted(ia_targets[tgt]):
            fh.write(f"{tgt}\t{ttag}\t{src}\t{mod_tag[mod_id[src]]}\n")
summary["import_all_targets_by_tag_pair"] = dict(collections.Counter(
    f"{mod_tag[mod_id[src]]}->{mod_tag[mod_id[tgt]] if tgt in mod_id else '?'}"
    for tgt, srcs in ia_targets.items() for src in srcs))
summary["import_all_distinct_targets_by_tag"] = dict(collections.Counter(
    (mod_tag[mod_id[tgt]] if tgt in mod_id else "?") for tgt in ia_targets))
summary["seconds"] = round(time.time() - t0)
with open(os.path.join(outdir, "summary.json"), "w") as fh:
    json.dump(summary, fh, indent=1)
print(json.dumps({k: v for k, v in summary.items() if k not in ("duplicate_stats",)}, indent=1)[:6000])
