#!/usr/bin/env python3
"""Pass 2: module-wise kernel replay of the Riemann Hypothesis build (and of anything appended).

The modules are taken in a topological order of the import graph and split into rounds (by size of
their private parts, which are not kept on disk between rounds). For every round:

  1. the round's `.ltar` artifacts are unpacked again;
  2. fresh worker processes are started (`Replay.lean`); each worker pulls the next unassigned
     module, is sent every module it has not seen yet with `check = 0` (their public views, to
     bring its environment up to date) and the pulled module with `check = 1`;
  3. when the round is exhausted the workers exit and the round's private parts are deleted.

Workers are restarted between rounds because a worker never unmaps a private part (see
`Replay.lean`). If a worker dies, the module it was checking is recorded as `crashed` and a new
worker takes over.

usage: pass2.py <config.json>

config keys:
  order        TSV: idx, module, tag  (topological order; only rows whose tag is in `tags` are used)
  tags         list of tags to process
  manifest     module manifest (.jsonl.gz) of the build cache: [module, inputHash, ltar, sha256]
  artifacts    directory with the .ltar artifacts
  build        Lake build dir of the proof repository (lib/lean and ir below it)
  sizes        directory with chunk_*.sizes from pass 1
  extra        list of [module, path-to-.olean] appended after the order (fully on disk already)
  externals    list of external module names for the workers (`all:` prefix = import all)
  private_view list of modules that must enter the environment with their private view
  only         optional list of modules: check only these (everything else is `check = 0`)
  leanbin, replay, lean_path, out, workers, round_bytes, limit, tstack_kb, max_respawns
"""
import gzip, json, os, queue, resource, subprocess, sys, threading, time

cfg = json.load(open(sys.argv[1]))
out = cfg["out"]
os.makedirs(out, exist_ok=True)
libdir = os.path.join(cfg["build"], "lib", "lean")
irdir = os.path.join(cfg["build"], "ir")
W = cfg["workers"]
priv_view = set(cfg.get("private_view", []))
tags = set(cfg["tags"])
only = set(cfg["only"]) if cfg.get("only") else None

mods = []
for line in open(cfg["order"]):
    idx, m, tag = line.rstrip("\n").split("\t")
    if tag in tags:
        mods.append(m)
if cfg.get("limit"):
    mods = mods[:cfg["limit"]]
nrepo = len(mods)
# where a module's .olean is: by default under the build directory; `path_lists` (TSV files
# `module<TAB>path`, e.g. the lists written for Scan.lean) override that, for modules of other packages
path_of = {}
for f in cfg.get("path_lists", []):
    for line in open(f):
        m, p = line.rstrip("\n").split("\t")[:2]
        path_of[m] = p
paths = [path_of.get(m, os.path.join(libdir, m.replace(".", "/") + ".olean")) for m in mods]
for m, p in cfg.get("extra", []):
    mods.append(m); paths.append(p)
N = len(mods)

manifest = {}
with gzip.open(cfg["manifest"], "rt") as fh:
    for line in fh:
        o = json.loads(line)
        if isinstance(o, list):
            manifest[o[0]] = (o[1], o[2])

psize = {}
for f in sorted(os.listdir(cfg["sizes"])):
    if f.endswith(".sizes"):
        for line in open(os.path.join(cfg["sizes"], f)):
            m, sz = json.loads(line)
            psize[m] = max(1, sz.get(".olean.private", 1))

for i, m in enumerate(mods):
    if m not in psize:
        try:
            psize[m] = max(1, os.path.getsize(paths[i] + ".private"))
        except OSError:
            psize[m] = 1

def wanted(i):
    return only is None or mods[i] in only

# ---- rounds: [start, end) index ranges
rounds = []
start = 0; acc = 0
for i in range(N):
    if wanted(i):
        acc += psize.get(mods[i], 1)
    if acc >= cfg["round_bytes"]:
        rounds.append((start, i + 1)); start = i + 1; acc = 0
if start < N:
    rounds.append((start, N))
total_bytes = sum(psize.get(mods[i], 1) for i in range(N) if wanted(i))
n_wanted = sum(1 for i in range(N) if wanted(i))
print(f"{N} modules ({nrepo} from the build, {N - nrepo} extra); {n_wanted} to check, {total_bytes/1e9:.1f} GB of private data, "
      f"{len(rounds)} rounds, {W} workers", flush=True)

env = dict(os.environ)
env["PATH"] = cfg["leanbin"] + os.pathsep + env.get("PATH", "")
env["LEAN_PATH"] = cfg["lean_path"]

def set_limits():
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))

state_file = os.path.join(out, "state.json")
st = {"ok": 0, "fail": [], "viewfail": [], "crashed": [], "notes": 0, "consts": 0,
      "kernel": 0, "dupthm": 0, "unsafe": 0, "axioms": 0, "pub": 0, "ms": 0, "dups": {}, "viewdups": {},
      "slow": [], "other": [], "wall": 0.0, "respawns": 0, "segments": 0}
if os.path.exists(state_file):
    old = json.load(open(state_file))
    for k in ("wall", "respawns", "segments", "viewfail", "other", "viewdups", "notes"):
        st[k] = old.get(k, st[k])
st["segments"] += 1
# modules.tsv is the record of truth: one row per finished module
# idx, module, status, consts, kernel, dupthm, unsafe, axioms, pub, ms, worker, dups, slow
done = {}          # module -> status (OK / FAIL)
crash_count = {}
tsv_path = os.path.join(out, "modules.tsv")
if os.path.exists(tsv_path):
    for line in open(tsv_path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 13:
            continue
        if f[2] == "OK":
            done[f[1]] = "OK"; st["ok"] += 1
            for k, v in zip(("consts", "kernel", "dupthm", "unsafe", "axioms", "pub", "ms"), f[3:10]):
                st[k] += int(v or 0)
            for tok in f[11].split(" "):
                if "=" in tok:
                    k, v = tok.rsplit("=", 1); st["dups"][k] = st["dups"].get(k, 0) + int(v)
            if f[12]:
                st["slow"].append((f[1], f[12]))
        elif f[2] == "FAIL":
            done[f[1]] = "FAIL"; st["fail"].append([f[0], f[1], f[12]])
        elif f[2] == "CRASH":
            crash_count[f[1]] = crash_count.get(f[1], 0) + 1
for m, c in crash_count.items():
    if c >= 2 and m not in done:
        done[m] = "CRASH"; st["crashed"].append([m, c])
lock = threading.Lock()
results_tsv = open(tsv_path, "a")

def record(line, w):
    f = line.split("\t")
    with lock:
        if f[0] == "OK":
            st["ok"] += 1
            d = {}
            for tok in f[3].split(" "):
                if "=" in tok and not tok.startswith(("dups=", "slow=")):
                    k, v = tok.split("=", 1)
                    if k in ("consts", "kernel", "dupthm", "unsafe", "axioms", "pub", "ms") and v.isdigit():
                        st[k] += int(v); d[k] = v
            dups = ""; slow = ""
            if "dups=[" in f[3]:
                dups = f[3].split("dups=[", 1)[1].split("]", 1)[0]
                for tok in dups.split(" "):
                    if "=" in tok:
                        k, v = tok.rsplit("=", 1)
                        st["dups"][k] = st["dups"].get(k, 0) + int(v)
            if "slow=[" in f[3]:
                slow = f[3].split("slow=[", 1)[1].split("]", 1)[0]
                st["slow"].append((f[2], slow))
            cols = [d.get(k, "0") for k in ("consts", "kernel", "dupthm", "unsafe", "axioms", "pub", "ms")]
            results_tsv.write("\t".join([f[1], f[2], "OK"] + cols + [str(w), dups, slow]) + "\n"); results_tsv.flush()
        elif f[0] == "FAIL":
            st["fail"].append(f[1:])
            results_tsv.write("\t".join([f[1], f[2], "FAIL"] + ["0"] * 7 + [str(w), "", f[3][:2000]]) + "\n"); results_tsv.flush()
        elif f[0] == "VIEWFAIL":
            st["viewfail"].append(f[1:] + [w])
        elif f[0] == "NOTE":
            st["notes"] += 1
            if "viewdups=[" in f[3]:
                inner = f[3].split("viewdups=[", 1)[1].split("]", 1)[0]
                for tok in inner.split(" "):
                    if "=" in tok:
                        k, v = tok.rsplit("=", 1)
                        st["viewdups"][k] = st["viewdups"].get(k, 0) + int(v)
        elif line.startswith(("READY", "SYNCED", "END", "HAS", "===")):
            pass
        else:
            st["other"].append(line[:400])

class Worker:
    def __init__(self, w, gen):
        self.w = w
        self.log = open(os.path.join(out, f"worker{w}.log"), "a")
        self.log.write(f"=== start generation {gen}\n")
        if cfg.get("replay_bin"):
            # native build of Replay.lean (`lake build` in the directory that holds it)
            cmd = [cfg["replay_bin"]] + cfg["externals"]
        else:
            cmd = [os.path.join(cfg["leanbin"], "lean"), f"--tstack={cfg.get('tstack_kb', 4000000)}",
                   "--run", cfg["replay"]] + cfg["externals"]
        self.p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                  env=env, preexec_fn=set_limits, text=True, bufsize=1)
        self.q = queue.Queue()
        self.pos = 0          # every module with index < pos has been sent
        threading.Thread(target=self.reader, daemon=True).start()
    def reader(self):
        for line in self.p.stdout:
            self.log.write(line); self.log.flush()
            self.q.put(line.rstrip("\n"))
        self.q.put(None)
    def wait_for(self, pred):
        """Record lines until one satisfies `pred`; False if the worker died first."""
        while True:
            line = self.q.get()
            if line is None:
                return False
            record(line, self.w)
            if pred(line):
                return True
    def close(self):
        try:
            self.p.stdin.close()
        except Exception:
            pass
        self.wait_for(lambda l: l.startswith("END"))
        self.p.wait()

def unpack(idxs):
    jobs = []
    for i in idxs:
        m = mods[i]
        if m not in manifest:
            continue
        ihash, ltar = manifest[m]
        parent = os.path.dirname(m.replace(".", "/"))
        jobs.append({"file": os.path.join(cfg["artifacts"], ltar), "hash": ihash,
                     "base": [os.path.join(libdir, parent), os.path.join(irdir, parent)]})
    for a in range(0, len(jobs), 2000):
        r = subprocess.run([os.path.join(cfg["leanbin"], "leantar"), "--jobs", "4", "-f", "-x", "-j", "-"],
                           input=json.dumps(jobs[a:a + 2000]).encode(), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if r.returncode != 0:
            raise RuntimeError(f"leantar failed: {r.stdout[-1500:].decode(errors='replace')}")
    for i in idxs:
        rel = mods[i].replace(".", "/")
        for base, ext in ((libdir, ".ilean"), (irdir, ".c")):
            try: os.remove(os.path.join(base, rel + ext))
            except OSError: pass

def prune(idxs):
    for i in idxs:
        m = mods[i]
        if m in priv_view or m not in manifest:
            continue
        try: os.remove(os.path.join(libdir, m.replace(".", "/") + ".olean.private"))
        except OSError: pass

def line_for(i, check):
    view = "priv" if mods[i] in priv_view else "pub"
    return f"{i}\t{mods[i]}\t{paths[i]}\t{view}\t{1 if check else 0}\n"

t_start = time.time()
status = "complete"
bytes_done = sum(psize.get(m, 1) for m in done)
for r, (a, b) in enumerate(rounds):
    t0 = time.time()
    todo = [i for i in range(a, b) if wanted(i) and mods[i] not in done]
    if not todo:
        continue
    todo_set = set(todo)
    need = list(todo) + [i for i in range(b) if mods[i] in priv_view and i not in todo_set
                         and not os.path.exists(paths[i] + ".private")]
    unpack(need)
    t1 = time.time()
    nxt = [0]                      # index into todo
    respawns = [0]
    gen = [0]
    def serve(w):
        wk = Worker(w, r)
        if not wk.wait_for(lambda l: l.startswith("READY")):
            with lock: st["other"].append(f"worker {w} died at start-up in round {r}")
            return
        while True:
            with lock:
                if nxt[0] >= len(todo):
                    break
                i = todo[nxt[0]]; nxt[0] += 1
            try:
                buf = "".join(line_for(j, False) for j in range(wk.pos, i)) + line_for(i, True)
                wk.p.stdin.write(buf); wk.p.stdin.flush()
                alive = wk.wait_for(lambda l: l.startswith(("OK\t", "FAIL\t")) and l.split("\t")[1] == str(i))
            except (BrokenPipeError, OSError):
                alive = False
            if not alive:
                with lock:
                    st["crashed"].append([i, mods[i], w, r])
                    results_tsv.write("\t".join([str(i), mods[i], "CRASH"] + ["0"] * 7 + [str(w), "", ""]) + "\n"); results_tsv.flush()
                    respawns[0] += 1; st["respawns"] += 1
                    give_up = respawns[0] > cfg.get("max_respawns", 12)
                try: wk.p.kill()
                except Exception: pass
                if give_up:
                    return
                wk = Worker(w, f"{r}.respawn{respawns[0]}")
                if not wk.wait_for(lambda l: l.startswith("READY")):
                    return
                continue
            wk.pos = i + 1
        wk.close()
    ts = [threading.Thread(target=serve, args=(w,)) for w in range(W)]
    for t in ts: t.start()
    # progress while the round runs
    last_print = time.time()
    while any(t.is_alive() for t in ts):
        time.sleep(2)
        if time.time() - last_print < 120:
            continue
        last_print = time.time()
        with lock:
            done_n = nxt[0]
        print(f"   round {r+1}/{len(rounds)}: {done_n}/{len(todo)} assigned, ok={st['ok']} fail={len(st['fail'])} "
              f"crashed={len(st['crashed'])} t={time.time()-t0:.0f}s", flush=True)
        with lock:
            snap = dict(st); snap["wall"] = st["wall"] + (time.time() - t0)
            json.dump(snap, open(state_file, "w"))
    for t in ts: t.join()
    prune(todo)
    results_tsv.flush()
    with lock:
        bytes_done += sum(psize.get(mods[i], 1) for i in todo)
        st["wall"] += time.time() - t0
        json.dump(st, open(state_file, "w"))
        eta = st["wall"] / max(bytes_done, 1) * (total_bytes - bytes_done)
        print(f"round {r+1}/{len(rounds)} [{a},{b}): {len(todo)} modules, unpack {t1-t0:.0f}s, total {time.time()-t0:.0f}s | "
              f"ok={st['ok']} fail={len(st['fail'])} viewfail={len(st['viewfail'])} crashed={len(st['crashed'])} "
              f"kernel_decls={st['kernel']} | {bytes_done/1e9:.1f}/{total_bytes/1e9:.1f} GB, wall {st['wall']/60:.1f} min, "
              f"eta {eta/60:.0f} min", flush=True)
        if nxt[0] < len(todo):
            status = f"round {r} not finished (workers gave up)"
    if status != "complete":
        break
    if cfg.get("stop_on_fail") and (st["fail"] or st["viewfail"] or st["crashed"]):
        status = f"stopped after round {r} because of a failure"; break

st["status"] = status
st["modules_total"] = N
st["modules_to_check"] = n_wanted
json.dump(st, open(os.path.join(out, "result.json"), "w"), indent=1)
print(json.dumps({k: (v if not isinstance(v, list) else v[:8]) for k, v in st.items()}, indent=1)[:6000], flush=True)
print("pass2", status, flush=True)
good = status == "complete" and not st["fail"] and not st["viewfail"] and not st["crashed"] and st["ok"] == n_wanted
sys.exit(0 if good else 1)
