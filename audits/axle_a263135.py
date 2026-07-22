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
PROOF_SHA = "2ec5e1247a6337070eb21d70160da4849ea673fa"


def strip_imports(source: str) -> str:
    return "\n".join(
        line for line in source.splitlines()
        if not line.lstrip().startswith(("import ", "public import ", "public meta import "))
    ) + "\n"


def strip_project_attributes(source: str) -> str:
    """Remove Formal Conjectures metadata while preserving ordinary Lean attributes."""
    pattern = re.compile(r"@\[(.*?)\]", re.DOTALL)

    def replace(match: re.Match[str]) -> str:
        parts = [part.strip() for part in match.group(1).split(",")]
        kept = [
            part for part in parts
            if part
            and not part.startswith("category ")
            and not part.startswith("AMS ")
            and not part.startswith("formal_proof ")
        ]
        return "@[" + ", ".join(kept) + "]" if kept else ""

    return pattern.sub(replace, source)


def namespace_private_helpers(source: str, module_stem: str) -> str:
    """Give named private declarations module-unique source names before flattening.

    Native Lean compilation gives private declarations module-qualified internal names.
    Concatenating many source modules into one AXLE request removes that boundary, so two
    otherwise-valid modules could collide on a helper such as `foo`. Private declarations
    cannot be referenced from another source module by their source name, making this
    within-module alpha-renaming semantics-preserving.
    """
    declaration_re = re.compile(
        r"(?m)^(\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+)([A-Za-z_][A-Za-z0-9_']*)"
    )
    names = list(dict.fromkeys(match.group(2) for match in declaration_re.finditer(source)))
    renamed = source
    safe_stem = re.sub(r"[^A-Za-z0-9_]", "_", module_stem)
    for name in names:
        unique = f"_flat_{safe_stem}_{name}"
        renamed = re.sub(
            rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])",
            unique,
            renamed,
        )
    return renamed


def canonical_prefix(repo: Path) -> str:
    path = repo / "FormalConjectures/OEIS/263135.lean"
    source = path.read_text(encoding="utf-8")
    marker = "@[category research open, AMS 05]"
    if marker not in source:
        raise RuntimeError(f"canonical theorem marker not found in {path}")
    prefix = source.split(marker, 1)[0]
    doc_start = prefix.rfind("/--")
    if doc_start == -1 or not prefix[doc_start:].strip().endswith("-/"):
        raise RuntimeError("could not isolate the canonical theorem docstring")
    prefix = prefix[:doc_start] + "end OeisA263135\n"
    return strip_project_attributes(strip_imports(prefix))


def module_name(path: Path, repo: Path) -> str:
    return ".".join(path.relative_to(repo).with_suffix("").parts)


def ordered_scratch_files(repo: Path) -> list[Path]:
    files = sorted((repo / "Scratch").glob("A263135*.lean"))
    files = [path for path in files if path.name != "A263135Audit.lean"]
    if len(files) < 20:
        raise RuntimeError(f"expected complete A263135 modules, found only {len(files)}")

    by_module = {module_name(path, repo): path for path in files}
    if "Scratch.A263135Final" not in by_module:
        raise RuntimeError("Scratch.A263135Final is missing")

    import_re = re.compile(
        r"^\s*(?:public\s+|public\s+meta\s+)?import\s+([A-Za-z0-9_.]+)",
        re.MULTILINE,
    )
    dependencies: dict[str, set[str]] = {}
    for name, path in by_module.items():
        imports = import_re.findall(path.read_text(encoding="utf-8"))
        dependencies[name] = {dependency for dependency in imports if dependency in by_module}

    ordered: list[str] = []
    temporary: set[str] = set()
    permanent: set[str] = set()

    def visit(name: str) -> None:
        if name in permanent:
            return
        if name in temporary:
            raise RuntimeError(f"cyclic Scratch import at {name}")
        temporary.add(name)
        for dependency in sorted(dependencies[name]):
            visit(dependency)
        temporary.remove(name)
        permanent.add(name)
        ordered.append(name)

    for name in sorted(by_module):
        visit(name)
    return [by_module[name] for name in ordered]


def build_sources(repo: Path) -> tuple[str, str]:
    prefix = canonical_prefix(repo)
    theorem = """
namespace OeisA263135

theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, IsNatCeilSqrt (3 * n) r ∧
      IsMaximumContact (2 * n) (3 * n - r) := by
"""
    statement = "import Mathlib\n\n" + prefix + theorem + "  sorry\n\nend OeisA263135\n"

    chunks = ["import Mathlib\n\n", prefix]
    for path in ordered_scratch_files(repo):
        source = path.read_text(encoding="utf-8")
        source = namespace_private_helpers(source, path.stem)
        source = strip_project_attributes(strip_imports(source))
        chunks.append(
            f"\n-- BEGIN {path.relative_to(repo)}\n{source}\n-- END {path.relative_to(repo)}\n"
        )
    chunks.append(theorem + "  exact conjecture_solved n hn\n\nend OeisA263135\n")
    content = "".join(chunks)

    code = re.sub(r"/-.*?-\/", "", content, flags=re.DOTALL)
    code = re.sub(r"--.*", "", code)
    if re.search(r"\b(sorry|admit)\b", code):
        raise RuntimeError("flattened A263135 candidate contains a proof placeholder")
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
    headers = {
        "Content-Type": "application/json",
        "X-Request-Source": "proof-playgrond-oeis-a263135",
    }
    if api_key := os.environ.get("AXLE_API_KEY"):
        headers["Authorization"] = f"Bearer {api_key}"
    request = urllib.request.Request(
        AXLE_URL,
        data=json.dumps(payload).encode("utf-8"),
        headers=headers,
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
    errors = result.get("lean_messages", {}).get("errors", [])
    tool_errors = result.get("tool_messages", {}).get("errors", [])
    failed = result.get("failed_declarations", [])
    if not bool(result.get("okay")) or errors or tool_errors or failed:
        for error in errors:
            print(f"lean_messages: {error}", file=sys.stderr)
        for error in tool_errors:
            print(f"tool_messages: {error}", file=sys.stderr)
        if failed:
            print(f"failed_declarations: {failed}", file=sys.stderr)
        return 1

    print(f"AXLE verified OEIS A263135 with Lean 4.27.0 at proof SHA {PROOF_SHA}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
