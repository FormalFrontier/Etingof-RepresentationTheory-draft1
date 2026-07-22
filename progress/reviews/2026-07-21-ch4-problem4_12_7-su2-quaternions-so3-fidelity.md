# Review: Ch4 Problem 4.12.7 — SU(2) ↔ unit quaternions → SO(3): statement-fidelity + non-vacuity audit

**Issue:** #7208 (review, report-only)
**File:** `EtingofRepresentationTheory/Chapter4/Problem4_12_7.lean` (1204 lines)
**Book reference:** `blobs/Chapter4/Problem4.12.7.md`
**Date:** 2026-07-21 (UTC)

## Verdict

**FAITHFUL — all six book parts (a)–(f) are rendered faithfully, non-vacuously, and
axiom-clean.** No defects found. In particular the two crux requirements the issue flags —
part (f)'s surjectivity onto **all** of `SO(3)` and its kernel being **exactly** `{1, -1}`,
and part (b)'s identification of `ℍ` as the *commutant* division algebra — are both genuinely
established. Report-only: no Lean changes made in this review.

One piece of stale bookkeeping was found and corrected (not a code defect): `progress/items.json`
still carried `coverage_note: "... part (b) commutant description of ℍ as End of real rep not
yet formalized"`, but part (b) **is** fully formalized in the file (`commutant`,
`finrank_commutant = 4`, `commutant_isUnit_of_ne_zero`). The note and the (previously unset)
`fidelity` field are updated below.

## Build / axiom hygiene

- `lake build EtingofRepresentationTheory.Chapter4.Problem4_12_7` exits 0 (8580 jobs). Only
  style/lint warnings (unused-simp-arg, `tac1 <;> tac2` vs `(tac1; tac2)`, redundant
  `linear_combination` constant); none affect correctness. The single `sorry` token in the file
  is the word inside the module docstring ("proved sorry-free").
- `#print axioms` on all 18 headline / supporting declarations shows only
  `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. Checked:
  `real_irreducible`, `commutant_isUnit_of_ne_zero`, `finrank_commutant`, `finrank_quaternion`,
  `quaternionBasis`, `Q8_mul_mem`, `Q8_star_mem`, `Q8_subset_unitary`, `one_mem_Q8`,
  `qI_mul_qJ`, `qJ_mul_qI`, `star_mul_rev`, `normSq_mul`, `unit_quaternions_mulEquiv_SU2`,
  `rotHom`, `rotHom_surjective`, `rotMat_eq_one_iff`, `exists_surjective_hom_to_SO3`.

## Part-by-part fidelity adjudication

### (a) `V = ℂ²` irreducible as a *real* representation — FAITHFUL
`real_irreducible` (`:69`) quantifies over `W : Submodule ℝ (Fin 2 → ℂ)` invariant under
`(A : specialUnitaryGroup (Fin 2) ℂ).mulVec` for **every** `A`, and concludes `W = ⊥ ∨ W = ⊤`.
This is genuine irreducibility of the *real* 4-dim rep (submodules over `ℝ`, not `ℂ`), and the
action is the honest standard action of `SU(2)` on `ℂ²` restricted to `ℝ`-scalars. The proof
exhibits four explicit images of a nonzero `v` (under `diag(i,-i)`, the swap `J`, and their
product) forming a real basis, forcing `W = ⊤`. Not the complex rep, not a surrogate.

### (b) `ℍ = End_{SU(2),ℝ}(V)` is a 4-dim division algebra — FAITHFUL
`commutant` (`:984`) is `Subalgebra.centralizer ℝ (Set.range su2Act)` where `su2Act A` is the
honest `ℝ`-linear `v ↦ A.mulVec v`. `mem_commutant_iff` (`:987`) confirms membership is
"commutes with **every** group element's action", i.e. genuine `End` in the category of real
`SU(2)`-reps — not a bare 4-dim algebra asserted without the commutant identification. As a
`Subalgebra` it is automatically closed under composition (multiplication) and contains the real
scalars, faithfully rendering "closed under multiplication".
- `commutant_isUnit_of_ne_zero` (`:1018`): **every nonzero element is a unit** (invertible),
  via a genuine Schur argument — `ker f`/`range f` are `SU(2)`-invariant, so by (a) a nonzero
  `f` is bijective, with inverse shown again in the commutant. This is the division-algebra
  claim.
- `finrank_commutant = 4` (`:1197`) is over `ℝ` (`Module.finrank ℝ commutant`), via the
  `ℝ`-linear iso `ev : commutant ≃ ℂ²` (evaluation at `e₀`; injectivity = real irreducibility,
  surjectivity witnessed by the explicit `1, iMap, jMap, iMap∘jMap`).

### (c) Hamilton relations, `1,i,j,k` basis, `Q₈ ⊆ ℍˣ` — FAITHFUL
**All** the stated relations are proved (not a subset): `qI²=qJ²=qK²=-1` (`:411–413`),
`ij=k`/`ji=-k` (`:415–416`), `jk=i`/`kj=-i` (`:417–418`), `ki=j`/`ik=-j` (`:419–420`).
`quaternionBasis` (`:424`) is a genuine `Module.Basis (Fin 4) ℝ ℍ[ℝ]` (Mathlib's `basisOneIJK`),
with `quaternionBasis_{zero,one,two,three} = 1, qI, qJ, qK`, hence `finrank_quaternion = 4`
(`:445`). `Q8 = {1,-1,qI,-qI,qJ,-qJ,qK,-qK}` (`:465`) is shown closed under multiplication
(`Q8_mul_mem`), under `star` = inverse (`Q8_star_mem`), containing `1` (`one_mem_Q8`), and a
subset of `unitary ℍ[ℝ]` (`Q8_subset_unitary`) — the subgroup-of-`ℍˣ` property witnessed
constructively (see Minor notes on packaging).

### (d) conjugation reverses products; norm is multiplicative — FAITHFUL
`star_mul_rev` (`:201`): `star (q₁ q₂) = star q₂ * star q₁`, quantified over all `q₁,q₂` — the
order-reversing conjugation identity `overline(q₁q₂) = q̄₂ q̄₁`. `normSq_mul` (`:207`):
`normSq (q₁ q₂) = normSq q₁ * normSq q₂`, genuine multiplicativity, quantified over all
`q₁,q₂` (see Minor notes on `normSq` vs `‖·‖`).

### (e) unit quaternions ≅ SU(2) — FAITHFUL
`unit_quaternions_mulEquiv_SU2` (`:349`): `Nonempty (unitary ℍ[ℝ] ≃* specialUnitaryGroup (Fin 2) ℂ)`
— a genuine `MulEquiv` (group isomorphism), built as `MulEquiv.ofBijective qmatHom ⟨inj, surj⟩`,
not a mere injection or set bijection. `unitary ℍ[ℝ]` is exactly the norm-1 quaternions
(`mem_unitary_iff_normSq`, `:267`), matching the book's "group of quaternions of norm 1"; the
target is the genuine `SU(2)`.

### (f) surjective `SU(2) → SO(3)` with kernel `{1,-1}` — FAITHFUL (crux confirmed)
`exists_surjective_hom_to_SO3` (`:899`) is a single headline carrying **both** properties:
a `h : specialUnitaryGroup (Fin 2) ℂ →* specialOrthogonalGroup (Fin 3) ℝ` (genuine `SU(2)`,
genuine `SO(3)`) with `Function.Surjective h` **and**
`∀ A, A ∈ h.ker ↔ (A : Matrix) = 1 ∨ (A : Matrix) = -1` — the kernel pinned *exactly* to `{±1}`.
- **Surjectivity onto all of `SO(3)`:** `rotHom_surjective` (`:872`) lifts an arbitrary
  `R ∈ SO(3)` via `so3_euler_zyz` (`:718`), which is proved for **every**
  `R ∈ specialOrthogonalGroup (Fin 3) ℝ` (both the generic `sin β ≠ 0` and the degenerate
  `sin β = 0`, `R 2 2 = ±1` branches are handled), giving honest `Rz`/`Ry` rotation matrices.
  `Rz`, `Ry` are the standard rotation matrices; the half-angle bridges `rotMat_{z,y}Axis_half`
  and `rotMat_mul` transport the decomposition to a unit quaternion `q` with `rotMat q = R`.
- **Kernel exactly `{±1}`:** `rotMat_eq_one_iff` (`:584`) proves `rotMat q = 1 ↔ q = 1 ∨ q = -1`
  for unit `q` (conjugation fixes `i,j,k` iff `q` is central/real, and a unit real quaternion is
  `±1`); `exists_surjective_hom_to_SO3` transports this along `qmat`/`e.symm` and uses
  `qmat_injective`, `qmat_one`, `qmat_neg_one` to land on `A = 1 ∨ A = -1`. Not implicit, not
  missing.

## Non-vacuity

Hypotheses are simultaneously satisfiable and the objects are non-degenerate:
`specialUnitaryGroup (Fin 2) ℂ` and `specialOrthogonalGroup (Fin 3) ℝ` are inhabited groups
(contain `1`); `commutant` is nonzero (contains `1`, and `finrank = 4`); `Q8` is inhabited;
the equivalences/homomorphisms are between the genuine, nonzero groups. `real_irreducible` is a
statement about a genuine nonzero module (`e0 ≠ 0` is used), not vacuously true. `unitary ℍ[ℝ]`
is nontrivial (contains `±1, ±i, ±j, ±k`).

## Minor notes (no action required)

- **(d) `normSq` vs `‖·‖`.** The book states `‖q₁q₂‖ = ‖q₁‖·‖q₂‖`; the file proves the
  equivalent norm-**squared** identity `normSq (q₁q₂) = normSq q₁ · normSq q₂`. Since
  `normSq = ‖·‖²` and `‖·‖ ≥ 0`, the two are equivalent (take square roots), and `normSq` is the
  natural polynomial/algebraic object over `ℝ`. Faithful rendering.
- **(c) `Q8` packaging.** `Q8` is a `Set ℍ[ℝ]` with the three closure lemmas (mul, star=inverse,
  one) plus `⊆ unitary`, rather than a bundled `Subgroup ℍ[ℝ]ˣ` term. All group axioms are
  witnessed, so "Q₈ is a subgroup of ℍˣ" is faithfully established; bundling as a `Subgroup`
  would be a cosmetic improvement only.

## Items.json update

- `fidelity` (previously unset) → `verified`.
- `coverage_note` corrected: part (b) commutant / division-algebra / 4-dimensionality **is**
  formalized (`commutant`, `commutant_isUnit_of_ne_zero`, `finrank_commutant`); the old note
  claiming it "not yet formalized" was stale.
