#!/usr/bin/env python3
"""Pass 1 over the Riemann Hypothesis build cache.

For each chunk of modules: unpack the (already SHA-256-verified) `.ltar` artifacts with `leantar`,
scan every module's three olean parts with Scan.lean, then delete the bulky files that are not
needed afterwards (`.olean.private`, `.ilean`, `.c`), keeping the public `.olean`, `.olean.server`,
`.ir`, `.ir.sig` and `.trace` files.

usage: pass1.py <module-manifest.jsonl.gz> <artifact-dir> <build-dir> <scan-out-dir> <lean-bin-dir> <Scan.lean> [chunk]
"""
import gzip, json, os, subprocess, sys, time

manifest, artdir, builddir, scandir, leanbin, scanlean = sys.argv[1:7]
chunk = int(sys.argv[7]) if len(sys.argv) > 7 else 1500
libdir = os.path.join(builddir, "lib", "lean")
irdir = os.path.join(builddir, "ir")
os.makedirs(libdir, exist_ok=True); os.makedirs(irdir, exist_ok=True); os.makedirs(scandir, exist_ok=True)

rows = []
with gzip.open(manifest, "rt") as fh:
    for i, line in enumerate(fh):
        obj = json.loads(line)
        if isinstance(obj, dict):
            continue            # header
        rows.append(obj)        # [module, inputHash, "<hash16>.ltar", sha256]
print(f"{len(rows)} modules, chunk size {chunk}", flush=True)

env = dict(os.environ)
env["PATH"] = leanbin + os.pathsep + env.get("PATH", "")
t0 = time.time()
nchunks = (len(rows) + chunk - 1) // chunk
for k in range(nchunks):
    done_marker = os.path.join(scandir, f"chunk_{k:04d}.done")
    if os.path.exists(done_marker):
        continue
    part = rows[k * chunk:(k + 1) * chunk]
    jobs = []
    for mod, ihash, ltar, _sha in part:
        rel = mod.replace(".", "/")
        parent = os.path.dirname(rel)
        art = os.path.join(artdir, ltar[:-5] + ".art") if not os.path.exists(os.path.join(artdir, ltar)) else os.path.join(artdir, ltar)
        jobs.append({"file": art, "hash": ihash,
                     "base": [os.path.join(libdir, parent), os.path.join(irdir, parent)]})
        os.makedirs(os.path.join(libdir, parent), exist_ok=True)
        os.makedirs(os.path.join(irdir, parent), exist_ok=True)
    t1 = time.time()
    r = subprocess.run([os.path.join(leanbin, "leantar"), "--jobs", "4", "-f", "-x", "-j", "-"],
                       input=json.dumps(jobs).encode(), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode != 0:
        print(f"chunk {k}: leantar failed rc={r.returncode}: {r.stdout[-2000:].decode(errors='replace')}", flush=True)
        sys.exit(1)
    t2 = time.time()
    listfile = os.path.join(scandir, f"chunk_{k:04d}.list")
    with open(listfile, "w") as fh:
        for mod, *_ in part:
            p = os.path.join(libdir, mod.replace(".", "/") + ".olean")
            if not os.path.exists(p):
                print(f"chunk {k}: missing {p}", flush=True); sys.exit(1)
            fh.write(f"{mod}\t{p}\n")
    outfile = os.path.join(scandir, f"chunk_{k:04d}.jsonl")
    if os.path.exists(outfile):
        os.remove(outfile)
    r = subprocess.run([os.path.join(leanbin, "lean"), "--run", scanlean, listfile, outfile],
                       env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if r.returncode != 0:
        print(f"chunk {k}: scan failed rc={r.returncode}: {r.stdout[-2000:].decode(errors='replace')}", flush=True)
        sys.exit(1)
    t3 = time.time()
    subprocess.run(["gzip", "-1", "-f", outfile], check=True)
    freed = 0; privbytes = 0
    with open(os.path.join(scandir, f"chunk_{k:04d}.sizes"), "w") as szf:
        for mod, *_ in part:
            rel = mod.replace(".", "/")
            sizes = {}
            for base, exts in ((libdir, (".olean", ".olean.server", ".olean.private", ".ilean", ".ir")), (irdir, (".c",))):
                for ext in exts:
                    p = os.path.join(base, rel + ext)
                    try:
                        sizes[ext] = os.path.getsize(p)
                    except OSError:
                        sizes[ext] = -1
            szf.write(json.dumps([mod, sizes]) + "\n")
            privbytes += max(0, sizes[".olean.private"])
            for base, ext in ((libdir, ".olean.private"), (libdir, ".ilean"), (irdir, ".c")):
                p = os.path.join(base, rel + ext)
                try:
                    freed += os.path.getsize(p); os.remove(p)
                except OSError:
                    pass
    open(done_marker, "w").write(r.stdout.decode(errors="replace"))
    el = time.time() - t0
    print(f"chunk {k+1}/{nchunks}: unpack {t2-t1:.0f}s scan {t3-t2:.0f}s private={privbytes/1e9:.2f}GB freed={freed/1e9:.2f}GB "
          f"elapsed {el/60:.1f} min  [{r.stdout.decode(errors='replace').strip()}]", flush=True)
print("pass1 complete", flush=True)
