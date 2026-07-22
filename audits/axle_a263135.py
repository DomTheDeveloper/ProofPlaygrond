#!/usr/bin/env python3
"""Flatten and verify the complete OEIS A263135 Lean proof with AXLE."""

from __future__ import annotations

import json
import os
import re
import sys
import urllib.error
import urllib.request
from pathlib import Path

AXLE_URL = "https://axle.axiommath.ai/api/v1/verify_proof"
PROOF_SHA = "7b4ef15d1a63473504da104c6759f05bf67fda5d"


def strip_imports(source: str) -> str:
    return "\n".join(
        line for line in source.splitlines()
        if not line.lstrip().startswith(("import ", "public import ", "public meta import "))
    ) + "\n"


def strip_project_attributes(source: str) -> str:
    """Remove only Formal Conjectures metadata, preserving simp and other Lean attributes."""

    pattern = re.compile(r"@\[(.*?)\]", re.DOTALL)

    def replace(match: re.Match[str]) -> str:
        raw = match.group(1)
        parts = [part.strip() for part in raw.split(",")]
        kept = [
            part for part in parts
            if part
            and not part.startswith("category ")
            and not part.startswith("AMS ")
            and not part.startswith("formal_proof ")
        ]
        return "@[" + ", ".join(kept) + "]" if kept else ""

    return pattern.sub(replace, source)


def canonical_prefix(repo: Path) -> str:
    path = repo / "FormalConjectures/OEIS/263135.lean"
    source = path.read_text(encoding="utf-8")
    marker = "@[category research open, AMS 05]"
    if marker not in source:
        raise RuntimeError(f"canonical theorem marker not found in {path}")
    prefix = source.split(marker, 1)[0]
    # The theorem is the final declaration in the namespace.
    prefix += "end OeisA263135\n"
    return strip_project_attributes(strip_imports(prefix))


def module_name(path: Path, repo: Path) -> str:
    return ".".join(path.relative_to(repo).with_suffix("").parts)


def ordered_scratch_files(repo: Path) -> list[Path]:
    files = sorted((repo / "Scratch").glob("A263135*.lean"))
    files = [path for path in files if path.name != "A263135Audit.lean"]
    by_module = {module_name(path, repo): path for path in files}
    dependencies: dict[str, set[str]] = {name: set() for name in by_module}
    import_re = re.compile(r"^\s*(?:public\s+|public\s+meta\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)
    for name, path in by_module.items():
        source = path.read_text(encoding="utf-8")
        dependencies[name] = {
            dep for dep in import_re.findall(source)
            if dep in by_module
        }

    ordered: list[str] = []
    temporary: set[str] = set()
    permanent: set[str] = set()

    def visit(name: str) -> None:
        if name in permanent:
            return
        if name in temporary:
            raise RuntimeError(f"cyclic Scratch import at {name}")
        temporary.add(name)
        for dep in sorted(dependencies[name]):
            visit(dep)
        temporary.remove(name)
        permanent.add(name)
        ordered.append(name)

    for name in sorted(by_module):
        visit(name)
    return [by_module[name] for name in ordered]


def build_sources(repo: Path) -> tuple[str, str]:
    prefix = canonical_prefix(repo)
    theorem_type = """
namespace OeisA263135

 theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, IsNatCeilSqrt (3 * n) r ∧
      IsMaximumContact (2 * n) (3 * n - r) := by
"""
    statement = "import Mathlib\n\n" + prefix + theorem_type + "  sorry\n\nend OeisA263135\n"

    chunks = ["import Mathlib\n\n", prefix]
    for path in ordered_scratch_files(repo):
        source = path.read_text(encoding="utf-8")
        source = strip_project_attributes(strip_imports(source))
        chunks.append(f"\n-- BEGIN {path.relative_to(repo)}\n{source}\n-- END {path.relative_to(repo)}\n")
    chunks.append(theorem_type + "  exact conjecture_solved n hn\n\nend OeisA263135\n")
    content = "".join(chunks)

    # Candidate proof modules must be genuinely complete. Ignore prose occurrences in comments.
    code_without_comments = re.sub(r"/-.*?-/", "", content, flags=re.DOTALL)
    code_without_comments = re.sub(r"--.*", "", code_without_comments)
    if re.search(r"\b(sorry|admit)\b", code_without_comments):
        raise RuntimeError("flattened A263135 candidate still contains a proof placeholder")
    return statement, content


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: axle_a263135.py PATH_TO_FORMAL_CONJECTURES", file=sys.stderr)
        return 2
    repo = Path(sys.argv[1]).resolve()
    statement, content = build_sources(repo)

    flat_output = Path(os.environ.get("A263135_FLAT_OUTPUT", "/tmp/A263135Flat.lean"))
    json_output = Path(os.environ.get("A263135_AXLE_OUTPUT", "/tmp/a263135-axle.json"))
    flat_output.write_text(content, encoding="utf-8")

    payload = {
        "formal_statement": statement,
        "content": content,
        "environment": "lean-4.27.0",
        "mathlib_options": True,
        "ignore_imports": False,
        "use_def_eq": True,
        "timeout_seconds": 900,
    }
    request = urllib.request.Request(
        AXLE_URL,
        data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=960) as response:
            result = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        print(f"AXLE HTTP {exc.code}: {body}", file=sys.stderr)
        return 3
    except Exception as exc:
        print(f"AXLE request failed: {exc}", file=sys.stderr)
        return 4

    json_output.write_text(json.dumps(result, indent=2, sort_keys=True), encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    okay = bool(result.get("okay"))
    if not okay:
        for section in ("lean_messages", "tool_messages"):
            messages = result.get(section, {})
            for error in messages.get("errors", []):
                print(f"{section}: {error}", file=sys.stderr)
        return 1
    print(f"AXLE verified OEIS A263135 against Lean 4.27.0 at proof SHA {PROOF_SHA}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
