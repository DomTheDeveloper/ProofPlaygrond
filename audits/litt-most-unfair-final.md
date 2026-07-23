# Litt most-unfair final audit

This is the sole active verification lane for the Ekhad–Zeilberger / Litt most-unfair fair-binary coin-word proof.

The workflow checks the current `agent/litt-most-unfair-proof` branch and records the resolved immutable SHA in every artifact. It:

- rejects `sorry`, `admit`, `native_decide`, unsafe declarations, custom axioms, and compiler-trust shortcuts across every `LittMostUnfairBet*.lean` module;
- replays the exact rational exhaustive certificate for all lengths `2 ≤ n ≤ 10`;
- checks all `1,047,552` ordered distinct pairs at `n = 10`;
- builds the terminal universal theorem;
- executes the terminal axiom audit and rejects `sorryAx` or compiler-trust dependencies.

The finite replay remains green. The current rerun tests the latest orbit, endpoint, sum-flattening, energy-translation, and diagonal-energy compatibility repairs rather than the obsolete `f036e066` snapshot.