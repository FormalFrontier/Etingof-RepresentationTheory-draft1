# Review — Ch9 Problem 9.4.6: path-algebra homological dimension + Cartan matrix + `finite_path` infrastructure

- **Issue:** #7003 (review, report-only)
- **Reviewer session:** `/review` worker, branch `agent/064706b1`
- **Target:** `EtingofRepresentationTheory/Chapter9/Problem9_4_6.lean` (557 lines), sorry-free on `main`
- **Fidelity reference:** `blobs/Chapter9/Problem9.4.6.md`
- **Focus areas:** statement fidelity + axiom cleanliness (report-only)
- **Overall verdict:** **SOUND.** All headline declarations are axiom-clean, no
  proposition is weakened to `True`, no `def`/`abbrev`/`instance` body is sorried, and the
  `hacyclic`-is-load-bearing claim in the header docstring is concretely true. Two
  non-blocking observations (scope of part (i); upstream projective-cover identification) are
  recorded below — neither is a defect in the audited file.

---

## 1. Axiom-cleanliness audit

Built `EtingofRepresentationTheory.Chapter9.Problem9_4_6` (exit 0; two style-lint warnings only,
see §4) and ran `#print axioms` on every headline declaration plus the definitions the issue
asked to spot-check. **Every** result is exactly `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, no stray custom axiom:

| Declaration | `#print axioms` result |
|---|---|
| `hasHomologicalDimensionLE_pathAlgebra_one` | `[propext, Classical.choice, Quot.sound]` |
| `homologicalDimension_pathAlgebra_eq_one` | `[propext, Classical.choice, Quot.sound]` |
| `homologicalDimension_freeAlgebra_eq_one` | `[propext, Classical.choice, Quot.sound]` |
| `cartanMatrix_pathAlgebra_eq_pathCount` | `[propext, Classical.choice, Quot.sound]` |
| `cartanMatrix_pathAlgebra_eq_pathCount'` | `[propext, Classical.choice, Quot.sound]` |
| `finite_path` | `[propext, Classical.choice, Quot.sound]` |
| `path_length_lt_card` | `[propext, Classical.choice, Quot.sound]` |
| `freePathEquiv` | `[propext, Classical.choice, Quot.sound]` |
| `not_hasHomologicalDimensionLE_zero_freeAlgebra` | `[propext, Classical.choice, Quot.sound]` |
| `pathCountMatrix` | `[propext, Classical.choice, Quot.sound]` |
| `freeToPath` | `[propext, Classical.choice, Quot.sound]` |
| `pathToFree` | `[propext, Classical.choice, Quot.sound]` |

Because a sorried definition body would inject `sorryAx` into every downstream theorem, the clean
axiom sets on `freePathEquiv`, `freeToPath`, `pathToFree`, `pathCountMatrix` and on the headline
theorems (which transitively use `pathAlgebraProj`, `pathAlgebraHomEquiv`, `algebraCartanMatrix`,
`standardResolution_shortExact`) also certify that none of those upstream definitions is sorried.

## 2. `hacyclic` is genuinely load-bearing (not decorative)

The docstring (lines 52–56) claims acyclicity is what makes each `Quiver.Path i j` finite, derived
from `hacyclic` rather than assumed. Confirmed concretely:

- **Where it is used.** In both Cartan theorems the path-finiteness instance is produced *only* by
  `finite_path hacyclic`:
  `Chapter9/Problem9_4_6.lean:531` —
  `haveI : ∀ i j : Q, Finite (Quiver.Path i j) := fun i j => finite_path hacyclic i j`.
  `finite_path` (line 176) takes `hacyclic` as an explicit argument and feeds it to
  `path_length_lt_card hacyclic` (line 184), which feeds `pathSupport_nodup hacyclic` (line 131),
  which uses `hacyclic` to derive the vertex-repetition contradiction (lines 116–118). The whole
  chain genuinely consumes acyclicity.

- **No competing instance shortcut.** I checked that `Finite (Quiver.Path i j)` cannot be
  synthesized from the ambient instances `[Fintype Q] [DecidableEq Q] [∀ i j, Finite (i ⟶ j)]`
  alone (i.e. without `hacyclic`): a scratch `example ... : Finite (Quiver.Path i j) := by
  infer_instance` under exactly those hypotheses **fails** with `synthInstanceFailed`. So there is
  no global `arrow-finite ⇒ path-finite` instance in scope that would make `hacyclic` removable;
  the `finite_path hacyclic` supply at line 531 is the sole source. This is mathematically
  necessary: a cyclic finite quiver (e.g. the one-vertex loop quiver `LoopVertex`) has an infinite
  path type, so no acyclicity-free instance could exist.

The `[∀ i j : Q, Finite (i ⟶ j)]` retype (arrow-finiteness) promised by the PR is present in both
Cartan theorem signatures (lines 524, 551); path-finiteness is derived internally, matching the
docstring's "not assumed" claim.

## 3. Fidelity to `blobs/Chapter9/Problem9.4.6.md`

Book statement:
> (i) the path algebra `P_Q` of any quiver `Q` with at least one edge has homological dimension 1;
> in particular the free algebra `k⟨x₁,…,xₙ⟩` has homological dimension 1 (`n ≥ 1`).
> (ii) for a finite oriented graph `Q` without oriented cycles, find the Cartan matrix of `P_Q`.

| Book claim | Lean statement | Verdict |
|---|---|---|
| (i) "at least one edge" ⇒ hom. dim. `= 1` | `homologicalDimension_pathAlgebra_eq_one` (line 251): hyp `hQ : ∃ a b, Nonempty (a ⟶ b)`, concl `homologicalDimension (PathAlgebra k Q) = 1` | **Faithful.** "at least one edge" = `∃ a b, Nonempty (a ⟶ b)`; proved as an equality (upper bound `≤ 1` via `hasHomologicalDimensionLE_pathAlgebra_one`, lower bound `≠ 0` via non-semisimplicity), not merely `≤ 1`. |
| (i) free algebra, `n ≥ 1`, hom. dim. `= 1` | `homologicalDimension_freeAlgebra_eq_one` (line 485): hyp `hn : 1 ≤ n`, concl `homologicalDimension (FreeAlgebra k (Fin n)) = 1` | **Faithful.** The realization `k⟨x₁,…,xₙ⟩ ≅ P_{Q₀}` is a genuine `AlgEquiv` (`freePathEquiv`, line 396, built from mutually-inverse `freeToPath`/`pathToFree`), and the universe-lift transfer is handled explicitly. Lower bound is a direct domain argument on the augmentation module (`not_hasHomologicalDimensionLE_zero_freeAlgebra`). |
| (ii) Cartan matrix of finite acyclic `P_Q` | `cartanMatrix_pathAlgebra_eq_pathCount'` (line 548): finite (`Fintype Q`), acyclic (`hacyclic`), arrow-finite ⇒ `algebraCartanMatrix (pathAlgebraProj k Q) = pathCountMatrix Q`, where `pathCountMatrix i j = Nat.card (Quiver.Path i j)` (line 508) | **Faithful.** "finite oriented graph without oriented cycles" = `[Fintype Q]` + `hacyclic`; the computed answer `cᵢⱼ = #{paths i → j}` is the standard textbook result. `algebraCartanMatrix` entry is `Module.finrank k (Pᵢ →ₗ[A] Pⱼ)` (`Definition9_3_1.lean`), exactly the book's `dim_k Hom_A(Pᵢ, Pⱼ)`. |

The two-form packaging (abstract `hcover` version `cartanMatrix_pathAlgebra_eq_pathCount` +
unconditional `…'` discharging it via `pathAlgebraHomEquiv`) is accurately described in the header
docstring (lines 43–49).

### No-vacuous-statement / definition checks (issue deliverable 2)

- Comment-stripped scan: **no** `sorry`, `admit`, or `stop` term in the file; **no** `: True` /
  `:= True` proposition placeholder.
- Spot-checked definition bodies are all genuine constructions:
  `LoopVertex := PUnit` (line 274); `loopQuiver := ⟨fun _ _ => ULift (Fin n)⟩` (line 282);
  `Fintype`/`DecidableEq`/`Unique` loop instances via `inferInstanceAs` (lines 276–278);
  `freeToPath := FreeAlgebra.lift …` (line 296); `pathToFree := (pathToFree_exists …).choose`
  (line 327, genuine `Classical.choose` of a proved `∃!`); `freePathEquiv := AlgEquiv.ofAlgHom …`
  (line 396); `pathCountMatrix := Matrix.of fun i j => Nat.card (Quiver.Path i j)` (line 508);
  `pathSuccEquiv` (line 137) supplies all four `Equiv` fields. Combined with §1, no data is sorried.

## 4. Observations (non-blocking, no fix required for this issue)

1. **Part (i) is proved for finite-vertex quivers.** Both hom-dimension theorems require
   `[Fintype Q] [DecidableEq Q]`, whereas the book says "any quiver `Q`". This is a reasonable and
   standard formalization choice — the semisimple vertex subalgebra `S = Q → k` and the
   sum-of-idempotents `∑ eᵢ = 1` underlying the standard resolution need a finite vertex set — and
   Etingof's path algebras are finite-quiver by default. Recorded as a scope note, not a defect;
   the free-algebra corollary (the book's headline "in particular") is fully covered. No follow-up
   filed.

2. **Projective-cover identification lives upstream in prose.** `algebraCartanMatrix P` is defined
   as `dim_k Hom_A(Pᵢ, Pⱼ)` for *whatever* family `P` is supplied; the theorem computes this for
   `P = pathAlgebraProj` (`= A·eᵢ`) and gets `#paths`. For the result to be literally "the Cartan
   matrix" one needs `A·eᵢ` to be the projective covers of the simple modules. That identification
   is asserted in `PathAlgebraProjectiveCover.lean` docstrings but is not certified there as a
   theorem (no `IsProjective`/`ProjectiveCover`/simple-module lemma). The computation in the
   audited file is nonetheless fully correct and sorry-free as a statement about the concrete
   `pathAlgebraProj` family. Pre-existing modularization boundary, unrelated to the `finite_path`
   PR under audit; recorded here for traceability, no follow-up filed.

3. **Two style-lint warnings** (cosmetic, from the build): unused binder `n` at
   `Chapter9/Problem9_4_6.lean:274` (`def LoopVertex (n : ℕ)` — `n` is intentionally part of the
   API surface, so `_n` would lose readability), and a >100-char line at line 303. Neither affects
   correctness or fidelity. Left as-is to avoid touching proof source in a report-only review and
   to avoid conflicting with any open PR; a future style pass can address them.

## Verification summary

- `#print axioms` quoted for all 8 required headline declarations plus 4 spot-checked definitions —
  every one clean (§1).
- `hacyclic`-load-bearing claim checked concretely: `finite_path hacyclic` at line 531 is the sole
  path-finiteness source, and `Finite (Quiver.Path i j)` provably does **not** synthesize without it
  (§2).
- Each fidelity row cites the specific book passage it validates (§3).
- `lake build EtingofRepresentationTheory.Chapter9.Problem9_4_6` succeeds (exit 0). **No source
  change was made** — this is a report-only review; the two lint warnings are pre-existing.
- No follow-up `feature` issue filed: no fidelity or soundness defect found.
