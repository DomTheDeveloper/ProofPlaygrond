#!/usr/bin/env python3
"""Convert a CHCEXP01 Chomp strategy binary into a Lean data module."""
from __future__ import annotations

import argparse
import struct
from pathlib import Path

MAGIC = b"CHCEXP01"
ROOTS = {
    (42,42,42,42,35,35,35,35,35,35),
    (42,42,42,42,42,42,29,29,29,29),
    (42,42,42,42,42,42,42,25,25,25),
}

def unpack_position(key: int) -> tuple[int, ...]:
    return tuple((key >> (6 * i)) & 63 for i in range(10))

def parse(path: Path):
    raw = memoryview(path.read_bytes())
    if len(raw) < 24 or bytes(raw[:8]) != MAGIC:
        raise ValueError("bad certificate header")
    n, total_records = struct.unpack_from("<QQ", raw, 8)
    offset = 24
    keys = list(struct.unpack_from(f"<{n}Q", raw, offset))
    offset += 8 * n
    positions = [unpack_position(k) for k in keys]
    if not ROOTS.issubset(set(positions)):
        raise ValueError("target root missing")
    replies: list[list[list[tuple[int,int,int]]]] = []
    seen = 0
    for p in positions:
        (count,) = struct.unpack_from("<I", raw, offset)
        offset += 4
        if count != sum(p) - 1:
            raise ValueError("response count mismatch")
        rows: list[list[tuple[int,int,int]]] = []
        for row, width in enumerate(p):
            row_entries: list[tuple[int,int,int]] = []
            if row == 0:
                row_entries.append((0,0,0))
            low = 1 if row == 0 else 0
            for _target in range(low, width):
                next_idx, reply_row, reply_target, reserved = struct.unpack_from("<IBBH", raw, offset)
                offset += 8
                if reserved != 0 or next_idx >= n:
                    raise ValueError("invalid response record")
                row_entries.append((next_idx, reply_row, reply_target))
                seen += 1
            rows.append(row_entries)
        replies.append(rows)
    if seen != total_records or offset != len(raw):
        raise ValueError("certificate length mismatch")
    return positions, replies, total_records

def lean_list(xs) -> str:
    return "[" + ",".join(map(str, xs)) + "]"

def emit(path: Path, positions, replies, total_records: int, source_sha256: str | None):
    with path.open("w", encoding="utf-8") as out:
        print("/-", file=out)
        print("Copyright 2026 The Formal Conjectures Authors.", file=out)
        print("", file=out)
        print('Licensed under the Apache License, Version 2.0 (the "License");', file=out)
        print("you may not use this file except in compliance with the License.", file=out)
        print("You may obtain a copy of the License at", file=out)
        print("", file=out)
        print("    https://www.apache.org/licenses/LICENSE-2.0", file=out)
        print("", file=out)
        print("Unless required by applicable law or agreed to in writing, software", file=out)
        print('distributed under the License is distributed on an "AS IS" BASIS,', file=out)
        print("WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.", file=out)
        print("See the License for the specific language governing permissions and", file=out)
        print("limitations under the License.", file=out)
        print("-/", file=out)
        print("", file=out)
        print("import FormalConjectures.OEIS.A147983.ExplicitStrategyData", file=out)
        print("", file=out)
        print("/-!", file=out)
        print("# Generated explicit strategy for OEIS A147983", file=out)
        print("", file=out)
        print(f"Carrier positions: `{len(positions)}`. Response records: `{total_records}`.", file=out)
        if source_sha256:
            print(f"Source certificate SHA-256: `{source_sha256}`.", file=out)
        print("-/", file=out)
        print("", file=out)
        print("namespace OeisA147983", file=out)
        print("namespace CompactStrategy", file=out)
        print("", file=out)
        print("private def response (next row target : ℕ) : ExplicitReply :=", file=out)
        print("  { next := next, row := row, target := target }", file=out)
        print("", file=out)
        print("def positions : Array (List ℕ) := #[", file=out)
        for idx, p in enumerate(positions):
            comma = "," if idx + 1 != len(positions) else ""
            print(f"  {lean_list(p)}{comma}", file=out)
        print("]", file=out)
        print("", file=out)
        print("def replies : Array (Array (Array ExplicitReply)) := #[", file=out)
        for pi, rows in enumerate(replies):
            print("  #[", file=out)
            for ri, entries in enumerate(rows):
                cells = ", ".join(f"response {a} {b} {c}" for a,b,c in entries)
                comma = "," if ri + 1 != len(rows) else ""
                print(f"    #[{cells}]{comma}", file=out)
            comma = "," if pi + 1 != len(replies) else ""
            print(f"  ]{comma}", file=out)
        print("]", file=out)
        print("", file=out)
        print("def data : ExplicitStrategyData :=", file=out)
        print("  { positions := positions, replies := replies }", file=out)
        print("", file=out)
        print("set_option maxRecDepth 1000000 in", file=out)
        print("set_option maxHeartbeats 0 in", file=out)
        print("theorem data_valid : data.Valid := by", file=out)
        print("  decide", file=out)
        print("", file=out)
        print("@[category research solved, AMS 5]", file=out)
        print("theorem chomp_10x42_three_openings :", file=out)
        print("    IsWinningOpening rectangle child₁ ∧", file=out)
        print("      IsWinningOpening rectangle child₂ ∧", file=out)
        print("      IsWinningOpening rectangle child₃ ∧", file=out)
        print("      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ :=", file=out)
        print("  ExplicitStrategyData.three_openings data data_valid", file=out)
        print("", file=out)
        print("#print axioms data_valid", file=out)
        print("#print axioms chomp_10x42_three_openings", file=out)
        print("", file=out)
        print("end CompactStrategy", file=out)
        print("end OeisA147983", file=out)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--sha256")
    args = parser.parse_args()
    positions, replies, records = parse(args.certificate)
    emit(args.output, positions, replies, records, args.sha256)
    print(f"generated {args.output}: carrier={len(positions)} records={records}")

if __name__ == "__main__":
    main()
