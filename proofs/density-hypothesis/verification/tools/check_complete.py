#!/usr/bin/env python3
"""Independent completeness check of a pass2.py run: every module that had to be checked has an
`OK` row in modules.tsv, there is no `FAIL` row, and no worker log contains a `FAIL` or `VIEWFAIL`
line that is not explained by a later `OK` row of the same module.

usage: check_complete.py <config.json>      (the configuration the run used)
exit status 0 only if the run is complete and clean.
"""
import glob, json, os, sys

cfg = json.load(open(sys.argv[1]))
out = cfg["out"]
tags = set(cfg["tags"])
expected = []
for line in open(cfg["order"]):
    idx, m, tag = line.rstrip("\n").split("\t")
    if tag in tags:
        expected.append(m)
if cfg.get("limit"):
    expected = expected[:cfg["limit"]]
in_order = len(expected)
expected += [m for m, _ in cfg.get("extra", [])]
if cfg.get("only"):
    only = set(cfg["only"])
    expected = [m for m in expected if m in only]
assert len(set(expected)) == len(expected), "a module is listed twice"

ok = {}; fail = {}; crash = {}
for line in open(os.path.join(out, "modules.tsv")):
    f = line.rstrip("\n").split("\t")
    if len(f) < 3:
        continue
    {"OK": ok, "FAIL": fail, "CRASH": crash}.get(f[2], {}).setdefault(f[1], []).append(f)
missing = [m for m in expected if m not in ok]
extra_ok = [m for m in ok if m not in set(expected)]
twice = [m for m, rows in ok.items() if len(rows) > 1]

viewfail = []; logfail = []
for lf in sorted(glob.glob(os.path.join(out, "worker*.log"))):
    for line in open(lf, errors="replace"):
        if line.startswith("VIEWFAIL\t"):
            viewfail.append((os.path.basename(lf), line.rstrip("\n")[:300]))
        elif line.startswith("FAIL\t"):
            f = line.rstrip("\n").split("\t")
            logfail.append((os.path.basename(lf), f[2], f[3][:200] if len(f) > 3 else ""))
unexplained = [x for x in logfail if x[1] not in ok]

consts = sum(int(r[0][3]) for r in ok.values()); kernel = sum(int(r[0][4]) for r in ok.values())
dupthm = sum(int(r[0][5]) for r in ok.values()); axioms = sum(int(r[0][7]) for r in ok.values())
ms = sum(int(r[0][9]) for r in ok.values())
report = {
    "expected_modules": len(expected), "from_order_file": in_order, "modules_with_OK_row": len(ok),
    "missing": missing[:20], "missing_count": len(missing), "OK_rows_for_unexpected_modules": extra_ok[:20],
    "modules_with_two_OK_rows": twice[:20], "FAIL_rows": {m: r[0][12][:300] for m, r in list(fail.items())[:20]},
    "modules_that_crashed_a_worker_once_and_passed_later": sorted(m for m in crash if m in ok),
    "modules_that_crashed_and_never_passed": sorted(m for m in crash if m not in ok),
    "VIEWFAIL_lines_in_worker_logs": viewfail[:20], "VIEWFAIL_count": len(viewfail),
    "FAIL_lines_in_worker_logs_without_later_OK": unexplained[:20],
    "FAIL_lines_in_worker_logs_with_later_OK": sorted({x[1] for x in logfail if x[1] in ok}),
    "constants": consts, "declarations_sent_to_kernel": kernel, "duplicate_theorems_rechecked": dupthm,
    "axioms_declared_in_checked_modules": axioms, "kernel_ms": ms,
}
clean = not missing and not fail and not extra_ok and not twice and not viewfail and not unexplained \
    and all(m in ok for m in crash)
report["complete_and_clean"] = clean
print(json.dumps(report, indent=1))
sys.exit(0 if clean else 1)
