#!/usr/bin/env python3
"""Unpack the build artifacts of the modules listed (one per line, or TSV with the module in
column 2) into the Lake build directory.  usage: unpack_mods.py <manifest> <artdir> <builddir> <leanbin> <list> [--keep-all]"""
import gzip, json, os, subprocess, sys
manifest_f, artdir, builddir, leanbin, listf = sys.argv[1:6]
keep_all = "--keep-all" in sys.argv
libdir = os.path.join(builddir, "lib", "lean"); irdir = os.path.join(builddir, "ir")
manifest = {}
with gzip.open(manifest_f, "rt") as fh:
    for line in fh:
        o = json.loads(line)
        if isinstance(o, list):
            manifest[o[0]] = (o[1], o[2])
mods = []
for line in open(listf):
    f = line.rstrip("\n").split("\t")
    mods.append(f[1] if len(f) > 1 else f[0])
jobs = []
for m in mods:
    ihash, ltar = manifest[m]
    parent = os.path.dirname(m.replace(".", "/"))
    jobs.append({"file": os.path.join(artdir, ltar), "hash": ihash,
                 "base": [os.path.join(libdir, parent), os.path.join(irdir, parent)]})
env = dict(os.environ); env["PATH"] = leanbin + os.pathsep + env["PATH"]
r = subprocess.run([os.path.join(leanbin, "leantar"), "--jobs", "4", "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs).encode(), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
if r.returncode != 0:
    print(r.stdout[-2000:].decode(errors="replace")); sys.exit(1)
if not keep_all:
    for m in mods:
        rel = m.replace(".", "/")
        for base, ext in ((libdir, ".ilean"), (irdir, ".c")):
            try: os.remove(os.path.join(base, rel + ext))
            except OSError: pass
print(f"unpacked {len(mods)} modules")
