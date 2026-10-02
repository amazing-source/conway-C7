# Lean 4 formalization: hand-off notes

Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `master` as pinned in `lake-manifest.json`.

```bash
cd lean
lake exe cache get        # prebuilt Mathlib (was blocked in the cloud session; fine locally)
lake build Ordre7.Setup   # general lemmas, builds in a few minutes
```

**Memory:** each generated `Gen/Blocks*.lean` file needed about 5 GB when elaborated. Building all
four in parallel on a 15 GB machine got the processes killed. Build them one at a time
(`lake build Ordre7.Gen.Blocks0`, then `…Blocks1`, and so on) or on a machine with more RAM.

## What is being proved

`Ordre7.no_orbit_matrix (C : Matrix (Fin 12) (Fin 12) ℤ) : ¬ IsOrbitMatrix C` (in `Main.lean`), where
`IsOrbitMatrix C` says that `C` is symmetric and nonnegative with zero diagonal, and that

* `∑ j, C i j = 12`,
* `∑ j, C i j * u j = 0`,
* `∑ k, C i k * C k j + C i j = 12 δᵢⱼ + 12 - 2 uᵢ uⱼ`,

with `u = (1,1,1,-1,-1,-1,0,0,0,0,0,0)`. This is the matrix core of the paper (Sections 6–8).

## File status

| file | content | status |
|---|---|---|
| `Ordre7/Imports.lean` | Mathlib imports | builds |
| `Ordre7/Basic.lean` | `u`, `IsOrbitMatrix`, `G = 3C+12I-4J-2uuᵀ`; `G_mul_G : G*G = 21•G`; `quad_nonneg`, `quad_zero` (positivity and kernel); **`IsOrbitMatrix.factor`**: if `Adj * G_S = D • 1` with `D > 0` and `Adj` symmetric, then `D • G = G_{·,S} Adj G_{S,·}` (the "rank 4" statement, proved from `G² = 21G` and `tr G = 84`); relabelling invariance `perm`; bounds `le4`; expanded row identities | **builds, no `sorry`** |
| `Ordre7/Setup.lean` | combination vectors, `G 1 = 0`, `G u = 0`, `quad_le : yᵀGy ≤ 21‖y‖²`, `nozero` (no zero edge inside `A`/`B`), `h_ge`, `h_le` (`3 ≤ h ≤ 5`), margins | **builds, no `sorry`** |
| `Ordre7/Gen/Blocks{0..3}.lean` | 29 generated block lemmas (mixed-orbit classification plus final row contradiction, one per labelled `A∪B` block with canonical `P,Q`) | one block (`P=Q=R=T111`) checked on its own (about 65 s); the full files are **not yet built** (memory) |
| `Ordre7/Gen/Census_*.lean` | generated census of `R` for the six canonical `(P,Q)` pairs (factorization through `S={0,1,2,3}`; PSD certificates for inadmissible first columns) | **not yet built** |
| `Ordre7/Main.lean` | normalization of `P` and `Q` by transpositions, dispatch to the census lemmas, `no_orbit_matrix` | type-checked against axiom stand-ins for the census lemmas; **not yet built** against the real ones |

The generated files come from `../scripts/gen_lean.py` (`cd scripts && python3 gen_lean.py`, needs `sympy`).
Every certificate in them (the basis `S`, adjugate `Adj`, `D`, PSD vectors) is computed there with exact
arithmetic and re-checked by Lean.

### How a block lemma works

For a mixed index `m`, `factor_apply` gives two linear equations and one quadratic equation in
`x_j = C m j` (`j < 6`), and `usum_expand` gives `Σ_A x = Σ_B x`. The dependent variables are
substituted, the free ones are split with `interval_cases`, and `omega` closes each leaf. The
conclusion `C m r ∈ V` for the chosen row `r` is then combined with `row_expand r` and `sq_expand r`.

If a generated file fails, the likely causes are `simp` normal forms (look at `f0 f1 fq` after the
`simp` call) or heartbeats (`maxHeartbeats` is set to 4,000,000 in the header).

## Still to formalize (graph → matrix)

1. **Orbit structure.** `G : SimpleGraph (Fin 99)` with `G.IsSRGWith 99 14 1 2` and `σ : G ≃g G` of
   order 7 has exactly one fixed vertex `x`. Use `MulAction.card_modEq_card_fixedPoints` for
   `zpowers σ` (a 7-group). Then build the labels `ℓᵢ, rᵢ` and the twelve exterior orbits.
2. **Quotient equations.** `IsOrbitMatrix.symm/row/usum/sq` for the exterior orbit matrix. These are
   double-counting arguments (paper, Proposition 4.1); `sq` and `usum` count walks `y → w → z`.
3. **Zero diagonal (spectral step).** `tr C = 0`. Ingredients:
   * eigenvalue-3 eigenspace of `A` over `ℚ` has dimension 54 (from `A² + A = 12I + 2J`, `tr A = 0`);
   * for a `ℚ`-linear `T` with `T⁷ = 1`, `dim E − dim Fix(T) ≡ 0 (mod 6)`, because `ker Φ₇(T)` is a
     vector space over `ℚ[X]/(Φ₇)` (`Polynomial.cyclotomic.irreducible_rat`, `Module.finrank_mul_finrank`);
   * `tr(A|_Fix) = tr C = 7d − 42`, and the exclusion of `d ∈ {0,12}` (paper, Proposition 5.2).
   The paper's §9 records that a brute-force search finds no matrix solution for any diagonal with
   `C_ii ∈ {0,2}` and `tr C = 14` either. A purely matrix-level proof of that case would remove the
   representation theory, but it is not needed.
4. **Reindexing.** Once (2) holds for some indexing of the 12 exterior orbits, pull it back to
   `Fin 12` with `u` in the canonical order (the counts 3/3/6 follow from the orbit description).

Final target: `theorem no_order7 (G : SimpleGraph (Fin 99)) [DecidableRel G.Adj]
(h : G.IsSRGWith 99 14 1 2) (σ : G ≃g G) (hσ : orderOf σ = 7) : False`.
