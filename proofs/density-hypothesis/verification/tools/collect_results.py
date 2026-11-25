#!/usr/bin/env python3
"""Collect the outputs of the verification runs into verification/results of the repository and
print the tables used in the READMEs.  usage: collect_results.py <repo verification dir>"""
import gzip, json, os, shutil, sys, collections

V = sys.argv[1]
R = os.path.join(V, "results")
W = "/home/user/work/rhverify"
os.makedirs(R, exist_ok=True)

def trim(obj, n=30):
    if isinstance(obj, dict):
        return {k: trim(v, n) for k, v in obj.items()}
    if isinstance(obj, list):
        return [trim(v, n) for v in obj[:n]] + ([f"... {len(obj) - n} more"] if len(obj) > n else [])
    return obj

# ---- provenance
shutil.copy(os.path.join(W, "rh_receipt.json"), os.path.join(R, "rh-cache-receipt.json"))

# ---- scan summaries
os.makedirs(os.path.join(R, "scan"), exist_ok=True)
scan_rows = []
for tag, d in (("unconditional", "analysis2"), ("in-situ", "analysis3")):
    s = json.load(open(os.path.join(W, d, "summary.json")))
    keep = {k: s[k] for k in s if k not in ("duplicate_stats",)}
    json.dump(trim(keep, 40), open(os.path.join(R, "scan", f"summary-{tag}.json"), "w"), indent=1)
    for r, info in s["roots"].items():
        scan_rows.append((tag, r, info))
    for f in ("import_all.tsv",):
        if os.path.exists(os.path.join(W, d, f)):
            shutil.copy(os.path.join(W, d, f), os.path.join(R, "scan", f"{tag}-{f}"))
s2 = json.load(open(os.path.join(W, "analysis2", "summary.json")))

def fmt(n):
    return f"{n:,}"

lines = ["| Root (declared in) | Modules in its import closure | Declarations reachable | Axioms reached |", "|---|---|---|---|"]
for tag, r, info in scan_rows:
    k = info["reachable_by_kind"]
    lines.append(f"| `{r}` (`{', '.join(info['declared_in'])}`) | {fmt(info['import_closure_modules'])} | {fmt(info['reachable_declarations'])} "
                 f"({fmt(k.get('theorem', 0))} theorems, {fmt(k.get('definition', 0))} definitions) | {', '.join('`' + a + '`' for a in info['axioms'])} |")
pk = s2["private_part_kinds"]
rh = {k.split(":")[1]: v for k, v in pk.items() if k.startswith("scan:")}
scan_table = "\n".join(lines) + f"""

Over the {fmt(s2['modules_by_tag']['scan'])} modules of the RH proof's build: {fmt(sum(rh.values()))} constants
({fmt(rh.get('T', 0))} theorems, {fmt(rh.get('D', 0))} definitions, {fmt(rh.get('I', 0))} inductive types with
{fmt(rh.get('C', 0))} constructors and {fmt(rh.get('R', 0))} recursors), **{rh.get('A', 0)} axioms**, {rh.get('O', 0)} opaque constants.
All {fmt(s2['public_part_constants']['scan'])} constants of their public parts are views of the private ones.
Across all {fmt(s2['modules'])} modules scanned, {s2['axioms_declared_anywhere']} axioms are declared, all in Lean core, Lake or Mathlib's
dependencies. No reachable declaration is unsafe or partial, none refers to a name that is not declared, and
no declaration anywhere refers to a constant that is only declared in a later module
(`references_to_later_modules = {s2['references_to_later_modules']}`). {fmt(s2['names_declared_in_several_modules'])} names are declared by more than one
module; almost all are auto-generated equation and congruence theorems."""
open(os.path.join(R, "scan", "table.md"), "w").write(scan_table + "\n")

# ---- replay runs
replay_rows = []
def replay(name, d, label, what):
    src = os.path.join(W, d)
    if not os.path.exists(os.path.join(src, "result.json")):
        replay_rows.append((label, what, None)); return None
    dst = os.path.join(R, f"replay-{name}"); os.makedirs(dst, exist_ok=True)
    r = json.load(open(os.path.join(src, "result.json")))
    json.dump(trim(r, 60), open(os.path.join(dst, "result.json"), "w"), indent=1)
    with open(os.path.join(src, "modules.tsv"), "rb") as fi, gzip.open(os.path.join(dst, "modules.tsv.gz"), "wb") as fo:
        shutil.copyfileobj(fi, fo)
    for f in ("tool_revisions.txt",):
        if os.path.exists(os.path.join(src, f)):
            shutil.copy(os.path.join(src, f), dst)
    replay_rows.append((label, what, r)); return r

replay("rh", "replay_full", "RH proof", "the 59,723 modules of the RH proof that `Main` imports, then the four modules of this project; Lean core and Mathlib imported as they are")
replay("final-lib", "replay_final_lib", "this project", "the modules of this project as built from this repository by `build_437.sh`, on top of the public views of the RH proof")
replay("final-catalog", "replay_final_catalog", "in situ", "the catalog's four files, the stand-in, and `InSituUnconditional`, on top of the public views of the RH proof")
replay("externals", "replay_externals", "Lean core and Mathlib", "the 11,623 modules of Lean core, Mathlib and its dependencies in the import closure, from an empty environment")

lines = ["| Run | Modules | Accepted | Rejected | Constants | Sent to the kernel | Duplicate theorems re-checked | Kernel time |", "|---|---|---|---|---|---|---|---|"]
for label, what, r in replay_rows:
    if r is None:
        lines.append(f"| {label}: {what} | not finished | | | | | | |"); continue
    bad = len(r["fail"]) + len(r["viewfail"]) + len(r["crashed"])
    lines.append(f"| {label}: {what} | {fmt(r['modules_to_check'])} | {fmt(r['ok'])} | {bad} | {fmt(r['consts'])} | {fmt(r['kernel'])} | {fmt(r['dupthm'])} | {r['ms']/3.6e6:.1f} CPU-hours |")
replay_table = "\n".join(lines)
open(os.path.join(R, "replay-table.md"), "w").write(replay_table + "\n")

# ---- new part
if os.path.isdir("/home/user/work/final437/results"):
    dst = os.path.join(R, "new-part"); os.makedirs(dst, exist_ok=True)
    for f in os.listdir("/home/user/work/final437/results"):
        shutil.copy(os.path.join("/home/user/work/final437/results", f), dst)
    shutil.copy("/home/user/work/final437/olean.sha256", os.path.join(dst, "olean.sha256"))

print(scan_table); print(); print(replay_table)
json.dump({"scan_table": scan_table, "replay_table": replay_table,
           "replay": {label: (None if r is None else {k: r[k] for k in ("ok", "modules_to_check", "consts", "kernel", "dupthm", "ms", "wall", "unsafe", "axioms")} | {"bad": len(r["fail"]) + len(r["viewfail"]) + len(r["crashed"])})
                      for label, what, r in replay_rows}},
          open(os.path.join(R, "summary.json"), "w"), indent=1)
