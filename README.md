# conway99-order7

A computer-free proof that a strongly regular graph with parameters (99,14,1,2)
(a putative *Conway 99-graph*) has **no automorphism of order 7**, together with
independent exact verifications and a Lean 4 / Mathlib formalization.

| path | content |
|---|---|
| `order7.pdf`, `tex/order7.tex` | the write-up (hand-checkable proof) |
| `scripts/` | exact-arithmetic sanity checks (not part of the proof) |
| `lean/` | Lean 4 formalization (work in progress, status and hand-off notes in `lean/README.md`) |

## Proof outline
1. An order-7 automorphism fixes exactly one vertex `x`; the 14 neighbours form two 7-orbits `L, R`
   and the 84 vertices at distance 2 form twelve 7-orbits (3 `LL`, 3 `RR`, 6 mixed).
2. The exterior orbit quotient `C` (12×12, symmetric, nonnegative integral) satisfies
   `C1 = 12·1`, `Cu = 0`, `C² + C = 12I + 12J − 2uuᵀ`.
3. Rational representation theory of `C₇` (dimension of nontrivial isotypic parts divisible by 6)
   forces `tr C = 0`, hence zero diagonal.
4. `G = 3C + 12I − 4J − 2uuᵀ` is 21 × a rank-4 projection: twelve vectors in `R⁴`.
5. The `LL/RR` block has exactly six possible configurations; in each, the mixed orbits are
   classified by hand (orthogonal splitting `W ⊕ S`), and one row of `C` gets contradictory
   first and second moments.

## Status
* Proof: complete on paper (draft, not refereed). Origin: a candidate argument produced with
  ChatGPT (2 Oct 2026), audited and rewritten here with all finite steps done by hand.
* Exact checks: `scripts/census6.py`, `scripts/mixed6b.py`, `scripts/residuals.py`,
  `scripts/fullsearch.c` (brute force: no 12×12 solution).
* Lean: see `lean/README.md`.
