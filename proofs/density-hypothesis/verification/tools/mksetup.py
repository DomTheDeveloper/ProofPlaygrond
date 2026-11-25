#!/usr/bin/env python3
"""Write a `lean --setup` file that tells Lean to load only the *public* part of every module of
the Riemann Hypothesis build (the private parts are not kept on disk).

usage: mksetup.py <module-name> <rh-lib-dir> <module-list.tsv> <out.json>
"""
import json, os, sys
name, lib, listfile, out = sys.argv[1:5]
arts = {}
for line in open(listfile):
    parts = line.rstrip("\n").split("\t")
    mod = parts[1] if len(parts) >= 3 else parts[0]
    base = os.path.join(lib, mod.replace(".", "/"))
    if not os.path.exists(base + ".olean"):
        continue
    arts[mod] = [[base + ".olean", base + ".olean.server"], [base + ".ir.sig", base + ".ir"]]
json.dump({"name": name, "isModule": True, "importArts": arts, "dynlibs": [], "plugins": [],
           "options": {"autoImplicit": False, "relaxedAutoImplicit": False}}, open(out, "w"))
print(f"{len(arts)} modules listed for {name}")
