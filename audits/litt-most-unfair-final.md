# Litt most-unfair final audit

This is the sole active verification lane for the Ekhad–Zeilberger / Litt most-unfair fair-binary coin-word proof.

The workflow checks `DomTheDeveloper/formal-conjectures@2411488aa849ab83034e6d4a4c5a189edef12f35` and records the resolved immutable SHA in every artifact. It:

- rejects `sorry`, `admit`, `native_decide`, unsafe declarations, custom axioms, and compiler-trust shortcuts across every `LittMostUnfairBet*.lean` module;
- replays the exact rational exhaustive certificate for all lengths `2 ≤ n ≤ 10`;
- checks all `1,047,552` ordered distinct pairs at `n = 10`;
- builds the terminal universal theorem;
- executes the terminal axiom audit and rejects `sorryAx` or compiler-trust dependencies.

The finite replay remains green. Source commit `2411488a` replaces the fragile four-case endpoint arithmetic tactic with explicit cases and closes the diagonal subtype sum with `Finset.sum_attach`.
