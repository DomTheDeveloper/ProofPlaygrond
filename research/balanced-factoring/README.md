# Reproducing the balanced-semiprime experiments

The question is whether a deterministic classical algorithm can factor every input in time polynomial in its binary length. These files give two successful input-only recoveries and a concrete failure of the combined search. The accompanying draft proves limitations for several specified searches. It makes no priority claim.

## Run the experiments

Python 3.10 or later suffices. The Python programs have no third-party dependencies. Run these commands from the extracted directory. The full replay performs several hundred two-stage curve computations.

~~~sh
python verify.py
python verify.py --replay
python recover.py 199604481618592988980642015258549902581
python recover.py 4146671484449439226230522340054012195065466778887760737680147961
python recover.py 2326981664014727582718789409779272096176399345327619480698638841
~~~

Each search receives one integer. The recovery interface assumes a product of two distinct odd primes p < q < 2p. It first tests the bounded multiplier schedule, then the bounded elliptic-curve schedule if needed. Optional arguments select a single method. On success it calculates the divisor-sum word and sends it to the earlier midpoint decoder, which recomputes the factor pair independently. On exhaustion it reports that outcome. The programs make no success-rate extrapolation from these three inputs.

| Input length | Multiplier method | Curve method | Recovered word, hexadecimal |
|---|---|---|---|
| 128 | Exhausted | Seed 19, second stage | 3587e5c0f45b |
| 212 | Multiplier 63, offset 0 | Exhausted | 955b707abcaa6d41816c10 |
| 211 | Exhausted | Exhausted | None |

The JSON fixture file keeps the values used for verification separate from both search implementations. The full replay runs both methods independently. The fast verifier independently checks all six primes by Lucas certificates in prime-witnesses.json, recomputes the successful gcd witnesses, directly multiplies the curve point by both possible second-stage scalars, checks both divisor-sum words and decodings, and enumerates small four-square and elliptic-point examples. Run Python with assertions enabled.

## Input provenance

- The 128-bit number is the test semiprime from the earlier divisor-sum bit-window project. The earlier demo supplied oracle replies from its known factors.
- For the 212-bit number, start separately at the integer parts of 7·2^106/10 and 9·2^106/10. Take the first prime strictly above each value that equals 3 modulo 4. Their product has a particularly close rational approximation to the factor ratio.
- For the 211-bit number, separately hash the ASCII strings “balanced-factoring-note/v1/A” and “balanced-factoring-note/v1/B” with SHA-256. Read each digest as an unsigned big-endian integer, retain the lowest 105 bits, and set bit 105. For each starting integer take the first strictly larger prime congruent to 3 modulo 4. Supply only their product to the searches. The single negative example refutes completeness for the specified budgets. Its construction provides no estimates of average-case success.

## Lean verification

The lean-toolchain and Lake manifest pin Lean 4.33.1 and Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. In a Lean environment run the following.

~~~sh
lake exe cache get
lake build
~~~

BalancedFactorCertificates.lean includes the original divisor-sum and decoder definitions and uses Mathlib's Lucas primality theorem and explicit factorizations of the predecessors to certify all six primes. It proves the two original divisor-sum words as the natural numbers 58857791485019 (width 48) and 180561757351988294691417104 (width 88), the first gcd, the weighted square identity and the explicit prime factorizations. Its audit commands list axiom dependencies. The searches and their exhaustive failures are reproduced in Python. The asymptotic density argument and four-square sampling proof are written in the manuscript.

The TeX source is split across BalancedFactoring.tex, OrdersAndSamples.tex and Evidence.tex. Compile BalancedFactoring.tex with pdfLaTeX.
