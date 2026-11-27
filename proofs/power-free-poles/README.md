# Poles of the Dirichlet series for power-free integers

For every integer $k\ge2$, let $Q_k(x)$ count the positive integers up to $x$ divisible by no prime $k$th power. Its Dirichlet series on $\operatorname{Re}s>1$ continues meromorphically as $F_k(s)=\zeta(s)/\zeta(ks)$. The Lean theorem `PowerFree.all_pole_locations` classifies the poles on the entire complex plane using the published RH theorem.

| Point | Local behavior of $F_k$ |
| --- | --- |
| $s=1$ | A simple pole with residue $1/\zeta(k)$. |
| $s=\rho/k$, where $\rho$ is a nontrivial zeta zero of multiplicity $m$ | A pole of order $m$ on $\operatorname{Re}s=1/(2k)$. |
| $s=-2n/k$, $n\ge1$, $k\nmid n$ | A simple pole with residue $\zeta(-2n/k)/(k\zeta'(-2n))$. |
| $s=-2n/k$, $n\ge1$, $k\mid n$ | The zeros cancel. The continued value is $\zeta'(-2n/k)/(k\zeta'(-2n))$, which is nonzero. |

These exhaust the poles. In particular, for squarefree integers the negative odd integers are simple poles and the negative even integers are removable. The other squarefree poles occur at $1$ and the points $\rho/2$ on the quarter-line.

## Multiplicities and residues

At $a=\rho/k$, the formalization proves the nonzero limit

$$
\lim_{s\to a}(s-a)^mF_k(s)=\frac{m!\,\zeta(a)}{k^m\,\zeta^{(m)}(\rho)}.
$$

Here $m$ is the order of the particular zero. If $m=1$, the residue of $F_k$ is $\zeta(a)/(k\zeta'(\rho))$. The residue of $F_k(s)/s$ is $\zeta(a)/(\rho\zeta'(\rho))$. On $\operatorname{Re}s>1$ the latter function equals $\int_1^\infty Q_k(t)t^{-s-1}\,dt$. This individual coefficient occurs in Meng's explicit formula. The estimates needed to sum over zeros and bound the counting error are a further analytic problem. [Meng, Lemmas 3 and 4](https://arxiv.org/pdf/1408.0429)

The proof derives the Euler product from the prime-power coefficients, then identifies the counting integral by partial summation. RH prevents numerator cancellation at scaled nontrivial zeros. For the negative half-plane, the functional equation expresses zeta locally as a cosine times a nonvanishing differentiable factor. This proves that each trivial zero is simple. Dividing two first-order expansions gives the nonzero limit at a cancellation. All evaluations at singular points are stated as meromorphic orders or punctured-neighborhood limits. [NIST DLMF, reflection formulas](https://dlmf.nist.gov/25.4)

The earlier pole-line criterion is included. For each fixed $k\ge2$, RH is equivalent to every pole in $0<\operatorname{Re}s<1/k$ lying on $\operatorname{Re}s=1/(2k)$. The first noncancelled pole along a chain of divisions by $k$ also has a proof independent of RH.

The squarefree specialization is related to [Erdős problem 969](https://www.erdosproblems.com/969). That problem asks for the order of the counting error, including a matching lower bound. The theorem here classifies the singularities of the generating function. A pointwise upper bound also requires control of the inverse Mellin integral.

## Lean sources

| File | Contents |
| --- | --- |
| `PowerFreeGlobal.lean` | Full-plane pole locations, simplicity of the negative zeros, exact negative grid orders, negative residues and limits at cancellations. |
| `PowerFreeCounting.lean` | Euler product for the actual coefficients, counting integral, residue at 1, and leading coefficients for arbitrary multiplicity. |
| `PowerFreeResidues.lean` | Applies the published `riemannHypothesis` to the global classification and the coefficient theorems. |
| `FreePoles.lean`, `PoleDescent.lean`, `PowerFreePoles.lean` | Exact meromorphic order, the right-half-plane classification, the pole-line criterion and the division-chain argument. |
| `verification/PoleAudit.lean` | Checks the RH interface, ten theorem applications and the axiom dependencies of 24 declarations. |
| `verification/*.txt` | Compiler and axiom-audit records for the analytic modules and the sieve. |
| `examples/` | An independently verified integer sieve using floor division and least common multiples. Its examples include the squarefree and cubefree counts through 1,000. |

## Reproduce

The pins are Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` and the compact edition of `lsernau/grh-lean` at `72fead102f663d5c7a407964a13dc0cf9d977207`. With an existing checkout, run the following command to compile the sources and their direct imports of `Main`.

```sh
bash check.sh /path/to/grh-lean/grh-compact
```

To reproduce the local compositional check in a matching Mathlib checkout with its cache installed, use the bundled upstream declaration. The script verifies its SHA-256 before using it.

```sh
bash check.sh /path/to/mathlib4 --interface-only
```

The upstream proof is Levent Alpöge's with Claude. `Verification.md` records the local compiler runs, the origin of the upstream binary and the independent checks of RH. [Published compact endpoint](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Main.lean) · [Sutherland's independent verification](https://math.mit.edu/~drew/shortgrh/)
