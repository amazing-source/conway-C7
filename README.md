# No automorphism of order 7 in a Conway 99-graph

**Theorem.** A strongly regular graph with parameters (99, 14, 1, 2) (a *Conway 99-graph*) has no
automorphism of order 7. Consequently 7 does not divide the order of its automorphism group.

The exclusion of order 7 was known before only through the computer-aided orbit-matrix computations of
Behbahani and Lam (2011). Cesarz and Woldar (*Algebraic Combinatorics* 8 (2025), 379–398) proved without a
computer that if 7 divides |Aut Γ| then Aut Γ ≅ Z₇. This repository contains a computer-free proof that
excludes the remaining cyclic case, and a complete formal verification in Lean 4 / Mathlib.

| path | content |
|---|---|
| [`order7.pdf`](order7.pdf), [`tex/order7.tex`](tex/order7.tex) | the manuscript (D. Djematene, 14 pages) |
| [`lean/`](lean) | the Lean 4 formalization; [`lean/Challenge.lean`](lean/Challenge.lean) is the statement, [`lean/README.md`](lean/README.md) the details |
| [`checks/`](checks) | independent exact-arithmetic sanity checks of the finite steps (not part of the proof) |
| [`scripts/`](scripts) | the exact checks of the first draft, including `fullsearch.c` (brute force over the symmetric 12×12 matrices with entries in 0..4 satisfying the quotient identities, without the Gram reasoning) |

## Proof outline

1. An automorphism of order 7 fixes exactly one vertex `x`; the 14 neighbours of `x` form two 7-orbits
   `L, R`, and the 84 other vertices form twelve 7-orbits (3 `LL`, 3 `RR`, 6 mixed) [Cesarz–Woldar].
2. The exterior orbit matrix `C` (12×12, symmetric, nonnegative, integral) satisfies `C1 = 12·1`, `Cu = 0`,
   `C² + C = 12I + 12J − 2uuᵀ` [Cesarz–Woldar].
3. Rationality of the eigenspaces (`Φ₇` is irreducible over ℚ) forces `tr C = 0`, so `C` has zero diagonal.
4. `G = 3C + 12I − 4J − 2uuᵀ` is 21 times an orthogonal projection of rank 4: twelve vectors in ℝ⁴.
5. The `LL/RR` block has six possible configurations; in each one the mixed orbits are classified by hand, and
   one row of `C` gets an impossible sum of squares.

Steps 4–5 are new; the paper states precisely what is taken from earlier work.

## Status

* **Paper:** complete, all finite steps by hand, independently audited; not yet refereed.
* **Lean:** no `sorry`, axioms `propext, Classical.choice, Quot.sound` only. `lake comparator` (statement in
  `lean/Challenge.lean`, proofs in `lean/Solution.lean`) accepts the proofs; logs in `lean/logs/`. The
  workflow `.github/workflows/lean-verify.yml` rebuilds everything on a clean Linux machine and runs
  `lake comparator` inside its sandbox, then `lake comparator --paranoid` (five more independent checkers).
* **History:** the strategy (zero diagonal, rank-4 Gram compression, case analysis) first appeared in a
  candidate argument produced with ChatGPT; it was audited, completed and rewritten with Claude, which also wrote
  the formalization. See the paper for details.
