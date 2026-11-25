#!/usr/bin/env python3
"""Download the RH build-cache artifacts named in the CI receipt's module manifest and verify
each one against the manifest's SHA-256. Own implementation (does not run any script from the
downloaded repository). usage: fetch_artifacts.py <sha256.json> <dest-dir>"""
import hashlib, json, os, subprocess, sys, tempfile

BASE = "https://rh-cache.taucetiproject.org/artifacts/leanprover-community/riemann-hypothesis/"
shas = json.load(open(sys.argv[1]))
dest = sys.argv[2]
os.makedirs(dest, exist_ok=True)

def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()

def missing():
    out = []
    for name, want in shas.items():
        p = os.path.join(dest, name)
        if not os.path.isfile(p):
            out.append(name)
    return out

for attempt in range(1, 7):
    todo = missing()
    print(f"pass {attempt}: {len(shas) - len(todo)}/{len(shas)} present, {len(todo)} to download", flush=True)
    if not todo:
        break
    with tempfile.TemporaryDirectory(dir=dest) as t:
        conf = os.path.join(t, "curl.conf")
        with open(conf, "w") as f:
            for n in todo:
                assert n.endswith(".ltar") and "/" not in n and ".." not in n
                f.write(f'url = "{BASE}{n[:-5]}.art"\noutput = "{t}/{n}"\n')
        r = subprocess.run(["curl", "--disable", "--fail", "--silent", "--show-error", "--location",
                            "--retry", "3", "--parallel", "--parallel-max", "100", "--config", conf],
                           capture_output=True, text=True)
        errs = [l for l in r.stderr.splitlines() if l.strip()]
        bad = 0
        for n in todo:
            src = os.path.join(t, n)
            if os.path.isfile(src):
                if sha256(src) == shas[n]:
                    os.replace(src, os.path.join(dest, n))
                else:
                    bad += 1
        print(f"pass {attempt}: curl exit {r.returncode}, {len(errs)} error lines, {bad} checksum mismatches", flush=True)
        for l in errs[:5]:
            print("  ", l, flush=True)

todo = missing()
total = sum(os.path.getsize(os.path.join(dest, n)) for n in shas if os.path.isfile(os.path.join(dest, n)))
print(f"done: {len(shas) - len(todo)}/{len(shas)} artifacts present and SHA-256 verified at download; {total/1e9:.2f} GB", flush=True)
sys.exit(1 if todo else 0)
