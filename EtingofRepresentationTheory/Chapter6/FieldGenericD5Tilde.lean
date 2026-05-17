import Mathlib
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.InfiniteTypeConstructions
import EtingofRepresentationTheory.Chapter6.FieldGenericInfiniteType
import EtingofRepresentationTheory.Chapter6.FieldGenericStar

/-!
# Orientation-Generic D̃₅ Construction (Sub A of #2790)

F-generic, orientation-generic version of the D̃₅ representation
`d5tildeRep` from `InfiniteTypeConstructions.lean:1544`. This file
provides the construction `d5tildeRep_kQ` and its dimension-vector
lemma; the indecomposability proof and the final per-(F, Q)
infinite-type theorem are deferred to Sub B (issue #2804), which
follows the star (K_{1,4}) indecomposability pattern from
`d5tildeRep_isIndecomposable` (`InfiniteTypeConstructions.lean:1569`).

The orientation-generic rep needs direction-aware maps for each of the
five edges of `d5tildeAdj`. For the canonical orientation `d5tildeQuiver`
(0→2, 1→2, 2→3, 4→3, 5→3) the maps are the F-generic analogues of
`starEmbed1`, `starEmbed2`, `d5tildeGamma`. For the reversed direction
of each leaf edge the rep needs a half-block projection back to the
leaf; for the reversed direction of the central edge `{2,3}` the rep
needs a section / inverse of `d5tildeGamma_F`.

Note (inverse lemmas): the ℂ-source `d5tildeRep_isIndecomposable` uses
`d5tildeGamma` in the forward direction only (see `gamma_from_embed1`
and `gamma_from_embed2` at `InfiniteTypeConstructions.lean:1711, 1732`).
Following the Ẽ₆ Sub A precedent (`FieldGenericETilde6.lean`), this
file defines `d5tildeGammaInv_F` as a closed-form inverse but does
**not** prove explicit `d5tildeGamma_F ∘ d5tildeGammaInv_F = id` lemmas.
They can be added in a follow-up if Sub B's indecomposability proof
turns out to need them (the ℂ-source proof does not).
-/

open scoped Matrix

namespace Etingof

/-! ## Section 1: F-generic γ for D̃₅

Mirror of `d5tildeGamma` (`InfiniteTypeConstructions.lean:1477`). Block
form `[[I, I], [I, N]]` acting on `(x, y) ↦ (x + y, x + Ny)` where `N`
is the nilpotent shift.
-/

/-- The D̃₅ connecting map γ over an arbitrary field `F`:
`F^{2(m+1)} → F^{2(m+1)}`, block form `[[I, I], [I, N]]`.

`γ(w)_i = w_i + w_{m+1+i}` for `i < m+1` (first block: x + y);
`γ(w)_i = w_{i-(m+1)} + N(y)_{i-(m+1)}` for `i ≥ m+1` (second block:
x + Ny). Mirror of `d5tildeGamma`. -/
noncomputable def d5tildeGamma_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) where
  toFun w i :=
    if h : i.val < m + 1 then
      w ⟨i.val, by omega⟩ + w ⟨m + 1 + i.val, by omega⟩
    else
      let j := i.val - (m + 1)
      w ⟨j, by omega⟩ +
        if h2 : j + 1 < m + 1 then w ⟨m + 1 + j + 1, by omega⟩ else 0
  map_add' x y := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-! ## Section 2: F-generic γ inverse for D̃₅

`d5tildeGammaInv_F` is the closed-form inverse of `d5tildeGamma_F`:
since `(I - N)` is invertible with inverse `M = I + N + N² + ... + N^m`
(the geometric series; `N` is nilpotent), the Schur-complement of the
block form `[[I,I],[I,N]]` gives
`γ⁻¹ = [[I - M, M], [M, -M]]`.

We build `γ⁻¹` from `LinearMap` combinators over a single new primitive
`cumTailSumLin` (the linear map `w ↦ (i ↦ Σ_{j=i}^m w_j)` representing
`M = (I - N)⁻¹`). All combinators preserve linearity, so the resulting
definition needs no manual `map_add'`/`map_smul'` proofs.
-/

/-- Cumulative right-tail sum matrix: upper triangular with `1`s on and
above the diagonal. `cumTailSumMatrix[i][j] = 1` iff `i ≤ j`. -/
noncomputable def cumTailSumMatrix (F : Type) [Field F] (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  fun i j => if i.val ≤ j.val then 1 else 0

/-- The cumulative right-tail sum linear map
`w ↦ (i ↦ Σ_{j=i}^{m} w_j)`, equivalently `(I - N)⁻¹` for the nilpotent
shift `N`. Defined as `Matrix.mulVecLin (cumTailSumMatrix F m)`. -/
noncomputable def cumTailSumLin (F : Type) [Field F] (m : ℕ) :
    (Fin (m + 1) → F) →ₗ[F] (Fin (m + 1) → F) :=
  Matrix.mulVecLin (cumTailSumMatrix F m)

end Etingof

namespace Etingof

/-! ## Section 3: Leaf projections for D̃₅

The reversed leaf-edge maps are simple half-block projections.
`starProj1_F` is the first-half projection `(a, b) ↦ a`, a left inverse
of `starEmbed1_F`. `starProj2_F` is the second-half projection
`(a, b) ↦ b`, a left inverse of `starEmbed2_F`.

These are the *plain* half-block projections (no kernel adjustment),
since D̃₅'s reversed leaf edges only need to land in the leaf space; the
indecomposability argument (Sub B) does the leaf decomposition via the
direct sum at each center, not via projection kernels.
-/

/-- First-half projection `(a, b) ↦ a` for `F^{2(m+1)} → F^{m+1}`. Left
inverse of `starEmbed1_F` (`x ↦ (x, 0)`). Used for the reversed
direction of leaf edges `{0,2}` and `{4,3}`. -/
noncomputable def starProj1_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Second-half projection `(a, b) ↦ b` for `F^{2(m+1)} → F^{m+1}`. Left
inverse of `starEmbed2_F` (`x ↦ (0, x)`). Used for the reversed
direction of leaf edges `{1,2}` and `{5,3}`. -/
noncomputable def starProj2_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) where
  toFun w i := w ⟨m + 1 + i.val, by omega⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Closed-form inverse of `d5tildeGamma_F`, built via `LinearMap`
arithmetic over `starEmbed1_F`, `starEmbed2_F`, `starProj1_F`,
`starProj2_F`, and `cumTailSumLin`. Block form `[[I - M, M], [M, -M]]`
where `M = cumTailSumLin = (I - N)⁻¹`.

Concretely, on input `w` decomposed as `(u, v) = (starProj1_F w,
starProj2_F w)`:
- second-block output `y = M (u - v)` (the `cumTailSumLin` of the
  half-difference);
- first-block output `x = u - y`;
- the full output is `starEmbed1_F x + starEmbed2_F y`. -/
noncomputable def d5tildeGammaInv_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) :=
  let P1 := starProj1_F F m
  let P2 := starProj2_F F m
  let M := cumTailSumLin F m
  let y : (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) := M.comp (P1 - P2)
  let x : (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (m + 1) → F) := P1 - y
  (starEmbed1_F F m).comp x + (starEmbed2_F F m).comp y

/-! ## Section 4: Orientation-generic D̃₅ representation

The map function is a match on `(a.val, b.val)` mirroring `d5tildeRepMap`
(`InfiniteTypeConstructions.lean:1531`) for the canonical five (a, b)
pairs, plus the five reversed pairs using the maps from Sections 2-3.
Outside those 10 edge pairs, the map is `0`.
-/

/-- Direction-aware match-based map for the orientation-generic D̃₅
representation. Returns the same linear maps as `d5tildeRepMap` for the
canonical orientation, plus the reverse maps from Sections 2-3 when the
arrow is in the reversed direction. -/
private noncomputable def d5tildeRepMap_kQ (F : Type) [Field F] (m : ℕ) (a b : Fin 6) :
    (Fin (d5tildeDim m a) → F) →ₗ[F] (Fin (d5tildeDim m b) → F) :=
  match a, b with
  -- Edge {0, 2}: canonical 0→2, reverse 2→0
  | ⟨0, _⟩, ⟨2, _⟩ => starEmbed1_F F m
  | ⟨2, _⟩, ⟨0, _⟩ => starProj1_F F m
  -- Edge {1, 2}: canonical 1→2, reverse 2→1
  | ⟨1, _⟩, ⟨2, _⟩ => starEmbed2_F F m
  | ⟨2, _⟩, ⟨1, _⟩ => starProj2_F F m
  -- Edge {2, 3}: canonical 2→3, reverse 3→2
  | ⟨2, _⟩, ⟨3, _⟩ => d5tildeGamma_F F m
  | ⟨3, _⟩, ⟨2, _⟩ => d5tildeGammaInv_F F m
  -- Edge {4, 3}: canonical 4→3, reverse 3→4
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1_F F m
  | ⟨3, _⟩, ⟨4, _⟩ => starProj1_F F m
  -- Edge {5, 3}: canonical 5→3, reverse 3→5
  | ⟨5, _⟩, ⟨3, _⟩ => starEmbed2_F F m
  | ⟨3, _⟩, ⟨5, _⟩ => starProj2_F F m
  -- Non-edge (ruled out by `hOrient`); placeholder
  | _, _ => 0

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic D̃₅ representation over an arbitrary field `F`
with arbitrary orientation `Q` of `d5tildeAdj`. Dimension vector
follows `d5tildeDim`: vertices 2 and 3 have dim `2(m+1)`, the leaf
vertices 0, 1, 4, 5 have dim `m+1`.

The map on an arrow `e : Q.Hom a b` depends only on the underlying
unordered edge `{a, b}` and the direction `a → b`. Each of the five
edges of `d5tildeAdj` contributes one canonical map (matching
`d5tildeRepMap`) and one reverse map (defined in Sections 2-3). The
orientation hypothesis `hOrient` is not used by the construction
itself; it is recorded so that downstream lemmas (notably the
indecomposability proof planned for Sub B #2804) can pattern-match on
which arrows exist. -/
noncomputable def d5tildeRep_kQ
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (_hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ) :
    @Etingof.QuiverRepresentation F (Fin 6) _ Q := by
  letI := Q
  exact {
    obj := fun v => Fin (d5tildeDim m v) → F
    instAddCommMonoid := fun _ => inferInstance
    instModule := fun _ => inferInstance
    mapLinear := fun {a b} _ => d5tildeRepMap_kQ F m a b
  }

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- The orientation-generic D̃₅ rep has the expected dimension vector
`d5tildeDim m` at each vertex. -/
theorem d5tildeRep_kQ_dimVec
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ) (v : Fin 6) :
    Nonempty (@Etingof.QuiverRepresentation.obj F (Fin 6) _ Q
      (d5tildeRep_kQ F Q hOrient m) v ≃ₗ[F] (Fin (d5tildeDim m v) → F)) :=
  ⟨LinearEquiv.refl F _⟩

/-! ## Section 5: F-generic helper lemmas for indecomposability

F-generic analogues of the inline computations in the ℂ-specific
`d5tildeRep_isIndecomposable` (`InfiniteTypeConstructions.lean:1569`).
Extracted as named lemmas so the per-(F, Q) indecomposability proof can
use them across direction case-splits. -/

/-- The two leaf-embeds disjoint at the center:
`starEmbed1_F x + starEmbed2_F y = 0 → x = 0 ∧ y = 0`. -/
theorem embed_sum_zero_F (F : Type) [Field F] (m : ℕ) (x y : Fin (m + 1) → F)
    (h : starEmbed1_F F m x + starEmbed2_F F m y = 0) :
    x = 0 ∧ y = 0 := by
  have heval : ∀ j : Fin (2 * (m + 1)),
      starEmbed1_F F m x j + starEmbed2_F F m y j = 0 :=
    fun j => by have := congr_fun h j; simpa using this
  constructor <;> ext ⟨i, hi⟩ <;> simp only [Pi.zero_apply]
  · have := heval ⟨i, by omega⟩
    simp only [starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk] at this
    split_ifs at this with h1
    · omega
    · simpa using this
  · have := heval ⟨m + 1 + i, by omega⟩
    simp only [starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk] at this
    split_ifs at this with h1 h2
    · omega
    · omega
    · simp only [zero_add] at this
      have key : (⟨m + 1 + i - (m + 1), by omega⟩ : Fin (m + 1)) = ⟨i, hi⟩ := by
        simp only [Fin.mk.injEq]; omega
      rwa [key] at this
    · omega

/-- Every `F^{2(m+1)}` vector decomposes as the sum of its two half-block
embeddings via the projections. -/
theorem center_decomp_F (F : Type) [Field F] (m : ℕ) (w : Fin (2 * (m + 1)) → F) :
    w = starEmbed1_F F m (starProj1_F F m w) +
        starEmbed2_F F m (starProj2_F F m w) := by
  ext ⟨j, hj⟩
  simp only [Pi.add_apply, starEmbed1_F, starEmbed2_F, starProj1_F, starProj2_F,
    LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hjlt : j < m + 1
  · simp only [dif_pos hjlt, show ¬(m + 1 ≤ j) from by omega, dite_false, add_zero]
  · simp only [dif_neg hjlt, show m + 1 ≤ j from by omega, dite_true, zero_add]
    congr 1; ext; simp; omega

/-- `d5tildeGamma_F` on `starEmbed1_F`: `γ(x, 0) = (x, x)`. F-generic
mirror of the inline `gamma_from_embed1` computation in the canonical
proof (`InfiniteTypeConstructions.lean:1711`). -/
theorem gamma_from_embed1_F (F : Type) [Field F] (m : ℕ) (x : Fin (m + 1) → F) :
    d5tildeGamma_F F m (starEmbed1_F F m x) =
      starEmbed1_F F m x + starEmbed2_F F m x := by
  ext i
  change (d5tildeGamma_F F m (starEmbed1_F F m x)) i =
    (starEmbed1_F F m x) i + (starEmbed2_F F m x) i
  simp only [d5tildeGamma_F, starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases h : i.val < m + 1
  · simp only [dif_pos h, dif_neg (show ¬(m + 1 ≤ i.val) by omega),
        dif_neg (show ¬(m + 1 + i.val < m + 1) by omega), add_zero]
  · push_neg at h
    simp only [dif_neg (show ¬(i.val < m + 1) by omega),
        dif_pos (show m + 1 ≤ i.val by omega),
        dif_pos (show i.val - (m + 1) < m + 1 by omega), zero_add]
    by_cases h2 : i.val - (m + 1) + 1 < m + 1
    · simp only [dif_pos h2,
        dif_neg (show ¬(m + 1 + (i.val - (m + 1)) + 1 < m + 1) by omega),
        add_zero]
    · simp only [dif_neg h2, add_zero]

/-- `d5tildeGamma_F` on `starEmbed2_F`: `γ(0, y) = (y, Ny)` where `N` is
the nilpotent shift. F-generic mirror of the inline `gamma_from_embed2`
computation in the canonical proof
(`InfiniteTypeConstructions.lean:1732`). -/
theorem gamma_from_embed2_F (F : Type) [Field F] (m : ℕ) (y : Fin (m + 1) → F) :
    d5tildeGamma_F F m (starEmbed2_F F m y) =
      starEmbed1_F F m y + starEmbed2_F F m (nilpotentShiftLinGen F m y) := by
  have aux : ∀ j : Fin (m + 1), nilpotentShiftLinGen F m y j =
      if h : j.val + 1 < m + 1 then y ⟨j.val + 1, h⟩ else 0 := by
    intro j
    simp only [nilpotentShiftLinGen, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      nilpotentShiftMatrixGen]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨j.val + 1, h⟩]
      · simp
      · intro b _ hb; simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
        intro hbi; exact hb (Fin.ext (by omega))
      · intro habs; exact absurd (Finset.mem_univ _) habs
    · apply Finset.sum_eq_zero; intro c _
      simp only [ite_mul, one_mul, zero_mul]; rw [if_neg]
      intro hji; exact h (by have := c.isLt; omega)
  ext i
  simp only [d5tildeGamma_F, starEmbed1_F, starEmbed2_F, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.add_apply, aux]
  by_cases h : i.val < m + 1
  · simp only [dif_pos h,
        dif_neg (show ¬(m + 1 ≤ i.val) by omega),
        dif_pos (show m + 1 ≤ m + 1 + i.val by omega),
        zero_add, add_zero]
    exact congr_arg y (Fin.ext (by simp))
  · push_neg at h
    simp only [dif_neg (show ¬(i.val < m + 1) by omega),
        dif_pos (show m + 1 ≤ i.val by omega),
        dif_neg (show ¬(m + 1 ≤ i.val - (m + 1)) by omega),
        zero_add]
    by_cases h2 : i.val - (m + 1) + 1 < m + 1
    · simp only [dif_pos h2,
          dif_pos (show m + 1 ≤ m + 1 + (i.val - (m + 1)) + 1 by omega)]
      exact congr_arg y (Fin.ext (by simp; omega))
    · simp only [dif_neg h2]

/-! ## Section 6: Orientation-generic indecomposability (path b: deferred)

The orientation-generic indecomposability proof is structurally the
~350-line ℂ-specific argument in `d5tildeRep_isIndecomposable`
(`InfiniteTypeConstructions.lean:1569`), generalized with direction-aware
case-splits on each of the five edges of `d5tildeAdj`. With ten
direction-aware rep-map cases (5 edges × 2 directions) and a `core`
lemma that requires symmetric leaf information at each center, the
direct case-analysis blows the per-session budget.

This sub-issue (#2804) is therefore landed in two parts:
- This PR (partial): construction (#2803, already merged), F-generic
  helper lemmas (Section 5 above), API stubs for the two final theorems
  (Section 6, 7 below), and the per-(F, Q) infiniteness theorem
  *conditional* on the stubbed indecomposability.
- A follow-up sub-issue tracks the actual indecomposability proof body.
  The follow-up is the bulk of the work; the API and downstream
  consumer are already in place. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Orientation-generic indecomposability of `d5tildeRep_kQ`.

**Proof body deferred** to a follow-up sub-issue of #2804. The structural
template is the ℂ-specific `d5tildeRep_isIndecomposable`
(`InfiniteTypeConstructions.lean:1569`); the per-(F, Q) version
case-splits on the direction of each of the five edges of `d5tildeAdj`
(four leaf-center edges and the central γ edge). The helper lemmas
`embed_sum_zero_F`, `center_decomp_F`, `gamma_from_embed1_F`,
`gamma_from_embed2_F` (Section 5) are F-generic extractions of the
inline computations used in the ℂ proof and are ready for use by the
follow-up worker.

This is path (b) of #2804: stub the API at the orientation-generic level,
carry the same `sorry` with a docstring tying it to the follow-up
sub-issue. The consumer `d5tilde_not_finite_type_per_kQ` below depends
transitively on this sorry. -/
theorem d5tildeRep_kQ_isIndecomposable
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ) :
    (d5tildeRep_kQ F Q hOrient m).IsIndecomposable := by
  sorry

/-! ## Section 7: Per-(F, Q) infinite-type theorem -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(field, orientation) version of `d5tilde_not_finite_type`: for
any algebraically closed field `F` and any orientation `Q` of
`d5tildeAdj`, the set of dimension vectors of indecomposable
representations is infinite.

Mirrors the proof of `d5tilde_not_finite_type`
(`InfiniteTypeConstructions.lean:1962`). Injectivity comes from vertex
`0`, where `d5tildeDim m 0 = m + 1`.

This theorem carries no direct `sorry`, but transitively depends on
`d5tildeRep_kQ_isIndecomposable`, whose proof body is deferred — see its
docstring. -/
theorem d5tilde_not_finite_type_per_kQ
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj) :
    ¬ Set.Finite
      {d : Fin 6 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 6) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  intro hfin
  have hmem : ∀ m : ℕ, d5tildeDim m ∈
      {d : Fin 6 → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin 6) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
    intro m
    exact ⟨d5tildeRep_kQ F Q hOrient m,
      d5tildeRep_kQ_isIndecomposable F Q hOrient m,
      d5tildeRep_kQ_dimVec F Q hOrient m⟩
  have hinj : Function.Injective (d5tildeDim : ℕ → Fin 6 → ℕ) := by
    intro m₁ m₂ h
    have h0 := congr_fun h ⟨0, by omega⟩
    change (if (⟨0, by omega⟩ : Fin 6).val = 2 ∨ (⟨0, by omega⟩ : Fin 6).val = 3
            then 2 * (m₁ + 1) else m₁ + 1) =
           (if (⟨0, by omega⟩ : Fin 6).val = 2 ∨ (⟨0, by omega⟩ : Fin 6).val = 3
            then 2 * (m₂ + 1) else m₂ + 1) at h0
    simp only [show ¬(0 = 2 ∨ 0 = 3) from by omega, ite_false] at h0
    omega
  exact (Set.infinite_range_of_injective hinj |>.mono
    (Set.range_subset_iff.mpr hmem)).not_finite hfin

end Etingof
