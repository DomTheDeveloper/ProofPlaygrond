#!/usr/bin/env python3
"""Count or materialize either reduced proof over the pinned Mathlib."""

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

RELEASE = "40e56bab026552e089d7afcfeff08d2defb9c005"
MIRROR = "https://github.com/leanprover-community/riemann-hypothesis.git"
HERE = Path(__file__).resolve().parent
ROOTS = {"OrdinaryRH": ["PrincipalWindows", "OrdinaryRH"], "AllClaims": ["Statements", "AllClaims"]}
LOCAL = {"OrdinaryRH", "PrincipalWindows", "AllClaims"}
PACKAGES = {"Mathlib", "Lean", "Batteries", "Aesop", "Qq", "Std", "Init", "Plausible",
            "LeanSearchClient", "ProofWidgets", "ImportGraph", "Lake", "Cli"}
IMPORT = re.compile(rb"^import[ \t]+([^\r\n]+)", re.M)


def release_tree(repo):
    sha = subprocess.check_output(["git", "-C", repo, "rev-parse", "HEAD"], text=True).strip()
    if sha != RELEASE:
        raise ValueError(f"Expected the original release at {RELEASE}, found {sha}")
    subprocess.run(["git", "-C", repo, "diff", "--quiet", "HEAD", "--",
                    "src", "lakefile.toml", "lean-toolchain", "lake-manifest.json"], check=True)
    if subprocess.check_output(["git", "-C", repo, "ls-files", "--others", "--exclude-standard",
                                "--", "src"]):
        raise ValueError("Unexpected untracked files in the archive source tree")


def write_project(repo, dest, target):
    for name in ("lean-toolchain", "lake-manifest.json"):
        shutil.copyfile(repo / name, dest / name)
    config = (repo / "lakefile.toml").read_text()
    config = re.sub(r"^defaultTargets = .*?$", f'defaultTargets = ["{target}"]', config, flags=re.M)
    config = config.replace('name = "Main"\nroots = ["Statements", "Main"]',
                            f'name = "{target}"\nroots = {json.dumps(ROOTS[target])}')
    (dest / "lakefile.toml").write_text(config)


def project(repo, target, dest=None):
    release_tree(repo)
    stack = [target]
    seen = set()
    archive_lines = local_lines = archive_bytes = local_bytes = 0
    while stack:
        module = stack.pop()
        if module in seen or module.split(".")[0] in PACKAGES:
            continue
        seen.add(module)
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = (HERE if module in LOCAL else repo / "src") / relative
        data = source.read_bytes()
        if module in LOCAL:
            local_lines += data.count(b"\n")
            local_bytes += len(data)
        else:
            archive_lines += data.count(b"\n")
            archive_bytes += len(data)
        for statement in IMPORT.findall(data):
            stack.extend(statement.split(b"--", 1)[0].decode().split())
        if dest:
            output = dest / "src" / relative
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(data)
    if dest:
        write_project(repo, dest, target)
    print(f"Archive: {len(seen - LOCAL):,} files, {archive_lines:,} lines, {archive_bytes:,} bytes")
    print(f"Local:   {len(seen & LOCAL):,} files, {local_lines:,} lines, {local_bytes:,} bytes")
    print(f"Total:   {len(seen):,} files, {archive_lines + local_lines:,} lines, "
          f"{archive_bytes + local_bytes:,} bytes, excluding Mathlib and Lean")
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help=f"Clean checkout of {MIRROR} at {RELEASE}")
    parser.add_argument("--target", choices=ROOTS, default="OrdinaryRH")
    parser.add_argument("--output", type=Path, help="Create a complete native Lake project here")
    args = parser.parse_args()
    if args.output is None:
        project(args.archive.resolve(), args.target)
        return
    out = args.output.resolve()
    if out.exists():
        parser.error("Choose a new output directory")
    out.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=out.parent) as tmp:
        stage = Path(tmp) / "reduced"
        stage.mkdir()
        project(args.archive.resolve(), args.target, stage)
        stage.rename(out)


if __name__ == "__main__":
    main()
