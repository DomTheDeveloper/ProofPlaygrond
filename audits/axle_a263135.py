#!/usr/bin/env python3
"""Flatten and check the A263135 scratch proof with AXLE."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import sys
import urllib.request

ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("formal-conjectures")
ENTRY = ROOT / "Scratch/A263135Audit.lean"
BASE_MODULE = "FormalConjectures.OEIS.«263135»"
BASE_PATH = ROOT / "FormalConjectures/OEIS/263135.lean"
LOCAL_PREFIX = "Scratch.A263135"

visited: set[Path] = set()
ordered: list[Path] = []


def module_path(module: str) -> Path | None:
    if module == BASE_MODULE:
        return BASE_PATH
    if module.startswith(LOCAL_PREFIX):
        return ROOT / (module.replace(".", "/") + ".lean")
    return None


def visit(path: Path) -> None:
    path = path.resolve()
    if path in visited:
        return
    if not path.is_file():
        raise SystemExit(f"Missing local module: {path}")
    visited.add(path)
    text = path.read_text()
    for line in text.splitlines():
        match = re.fullmatch(r"\s*import\s+(.+?)\s*", line)
        if not match:
            continue
        dep = module_path(match.group(1))
        if dep is not None:
            visit(dep)
    ordered.append(path)


def clean(path: Path, text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines():
        match = re.fullmatch(r"\s*import\s+(.+?)\s*", line)
        if match and module_path(match.group(1)) is not None:
            continue
        if match and match.group(1) == "FormalConjecturesUtil":
            if not any(candidate.strip() == "import Mathlib" for candidate in lines):
                lines.append("import Mathlib")
            continue
        if line.strip().startswith("@[category"):
            continue
        lines.append(line)
    text = "\n".join(lines) + "\n"
    if path.resolve() == BASE_PATH.resolve():
        marker = "/--\n**OEIS A263135, stronger even-index form.**"
        start = text.find(marker)
        if start < 0:
            raise SystemExit("Could not locate original open A263135 theorem block")
        end_marker = "end OeisA263135"
        end = text.rfind(end_marker)
        if end < start:
            raise SystemExit("Could not locate end of A263135 namespace")
        text = text[:start] + end_marker + "\n"
    return text


visit(ENTRY)
parts = [
    "/- Flattened by ProofPlaygrond/audits/axle_a263135.py. -/\n",
]
for path in ordered:
    parts.append(f"\n/- ===== {path.relative_to(ROOT)} ===== -/\n")
    parts.append(clean(path, path.read_text()))
content = "".join(parts)

out_path = Path(os.environ.get("A263135_FLAT_OUTPUT", "/tmp/A263135Flat.lean"))
out_path.write_text(content)
print(f"Flattened {len(ordered)} modules to {out_path} ({len(content)} bytes)")

payload = {
    "content": content,
    "environment": "lean-4.27.0",
    "ignore_imports": False,
    "mathlib_options": True,
    "timeout_seconds": 900,
    "verbosity": 2,
}
headers = {
    "Content-Type": "application/json",
    "X-Request-Source": "proof-playgrond-a263135",
}
api_key = os.environ.get("AXLE_API_KEY")
if api_key:
    headers["Authorization"] = f"Bearer {api_key}"
request = urllib.request.Request(
    "https://axle.axiommath.ai/api/v1/check",
    data=json.dumps(payload).encode(),
    headers=headers,
    method="POST",
)
with urllib.request.urlopen(request, timeout=1200) as response:
    result = json.load(response)
result_path = Path(os.environ.get("A263135_AXLE_OUTPUT", "/tmp/a263135-axle.json"))
result_path.write_text(json.dumps(result, indent=2, sort_keys=True))
print(json.dumps(result, indent=2, sort_keys=True))

errors = result.get("lean_messages", {}).get("errors", [])
tool_errors = result.get("tool_messages", {}).get("errors", [])
failed = result.get("failed_declarations", [])
if not result.get("okay", False) or errors or tool_errors or failed:
    raise SystemExit(1)
