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

/-! ## Section 3: Closed-form inverse of `d5tildeGamma_F`

The reversed leaf-edge maps in D̃₅ are the plain half-block projections
`starFirst_F` (`(a, b) ↦ a`) and `starSecond_F` (`(a, b) ↦ b`),
re-used here from `FieldGenericStar.lean`. They were originally cloned
as `starProj1_F` / `starProj2_F` in this file; #2846 deduped to the
K_{1,4} primitives (which are definitionally identical to D̃₅'s
plain projections, just with a more neutral name).
-/

/-- Closed-form inverse of `d5tildeGamma_F`, built via `LinearMap`
arithmetic over `starEmbed1_F`, `starEmbed2_F`, `starFirst_F`,
`starSecond_F`, and `cumTailSumLin`. Block form `[[I - M, M], [M, -M]]`
where `M = cumTailSumLin = (I - N)⁻¹`.

Concretely, on input `w` decomposed as `(u, v) = (starFirst_F w,
starSecond_F w)`:
- second-block output `y = M (u - v)` (the `cumTailSumLin` of the
  half-difference);
- first-block output `x = u - y`;
- the full output is `starEmbed1_F x + starEmbed2_F y`. -/
noncomputable def d5tildeGammaInv_F (F : Type) [Field F] (m : ℕ) :
    (Fin (2 * (m + 1)) → F) →ₗ[F] (Fin (2 * (m + 1)) → F) :=
  let P1 := starFirst_F F m
  let P2 := starSecond_F F m
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
  | ⟨2, _⟩, ⟨0, _⟩ => starFirst_F F m
  -- Edge {1, 2}: canonical 1→2, reverse 2→1
  | ⟨1, _⟩, ⟨2, _⟩ => starEmbed2_F F m
  | ⟨2, _⟩, ⟨1, _⟩ => starSecond_F F m
  -- Edge {2, 3}: canonical 2→3, reverse 3→2
  | ⟨2, _⟩, ⟨3, _⟩ => d5tildeGamma_F F m
  | ⟨3, _⟩, ⟨2, _⟩ => d5tildeGammaInv_F F m
  -- Edge {4, 3}: canonical 4→3, reverse 3→4
  | ⟨4, _⟩, ⟨3, _⟩ => starEmbed1_F F m
  | ⟨3, _⟩, ⟨4, _⟩ => starFirst_F F m
  -- Edge {5, 3}: canonical 5→3, reverse 3→5
  | ⟨5, _⟩, ⟨3, _⟩ => starEmbed2_F F m
  | ⟨3, _⟩, ⟨5, _⟩ => starSecond_F F m
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
use them across direction case-splits.

`embed_sum_zero_F` and `center_decomp_F` live in
`FieldGenericStar.lean` next to their underlying definitions
(`starEmbed1_F`, `starEmbed2_F`, `starFirst_F`, `starSecond_F`); they
are used both by `starRepGen_isIndecomposable` there and by the D̃₅
cascade below. -/

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

/-! ## Section 5b (REMOVED): left-inverse identities

The four left-inverse identities `starFirst_F (starEmbed1_F x) = x`,
`starFirst_F (starEmbed2_F x) = 0`, `starSecond_F (starEmbed1_F x) = 0`,
`starSecond_F (starEmbed2_F x) = x` are now de-privatized in
`FieldGenericStar.lean` (Section "Left-inverse identities") and used
directly here. The earlier `starProj1_F_starEmbed*_F` /
`starProj2_F_starEmbed*_F` lemmas in this section were inconsistent with
the post-#2846 D̃₅ rep-map (which uses the plain `starFirst_F` /
`starSecond_F`, not the K_{1,4}-specific `starProj1_F` / `starProj2_F`
that include a subtraction). -/

/-! ## Section 5c: `cumTailSumLin` closed form and the `(I - N)` inverse

`cumTailSumLin` is `(I - nilpotentShiftLinGen)⁻¹`. We give an explicit
closed form for its application (a right-tail sum) and prove the
telescoping identity `M (v - N v) = v`, which is the only fact needed
to invert `d5tildeGamma_F` on the two leaf-embedding patterns that
appear in the per-(F, Q) D̃₅ indecomposability proof. -/

/-- Closed-form right-tail sum:
`cumTailSumLin F m v i = ∑_{j : Fin (m+1), i.val ≤ j.val} v j`. -/
theorem cumTailSumLin_apply (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) (i : Fin (m + 1)) :
    cumTailSumLin F m v i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) => i.val ≤ j.val), v j := by
  simp only [cumTailSumLin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    cumTailSumMatrix, Finset.sum_filter, ite_mul, one_mul, zero_mul]

/-- Boundary case for `cumTailSumLin`: at index `m`, the right-tail sum
collapses to a single term `v ⟨m, _⟩`. -/
theorem cumTailSumLin_apply_last (F : Type) [Field F] (m : ℕ) (v : Fin (m + 1) → F) :
    cumTailSumLin F m v ⟨m, lt_add_one m⟩ = v ⟨m, lt_add_one m⟩ := by
  rw [cumTailSumLin_apply]
  apply Finset.sum_eq_single (⟨m, lt_add_one m⟩ : Fin (m + 1))
  · intro j hj hjne
    exfalso
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have : j.val = m := le_antisymm (by have := j.isLt; omega) hj
    exact hjne (Fin.ext this)
  · intro habs
    exfalso; apply habs; simp

/-- Recursive step for `cumTailSumLin`: splits off the index-`i` term,
yielding `M v ⟨i, _⟩ = v ⟨i, _⟩ + M v ⟨i + 1, _⟩` whenever `i + 1` is in
range. -/
theorem cumTailSumLin_apply_succ (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) (i : ℕ) (hi : i + 1 < m + 1) :
    cumTailSumLin F m v ⟨i, by omega⟩ =
      v ⟨i, by omega⟩ + cumTailSumLin F m v ⟨i + 1, hi⟩ := by
  rw [cumTailSumLin_apply, cumTailSumLin_apply]
  have hmem : (⟨i, by omega⟩ : Fin (m + 1)) ∈
      Finset.univ.filter (fun j : Fin (m + 1) => i ≤ j.val) := by simp
  rw [← Finset.sum_erase_add _ _ hmem, add_comm]
  congr 1
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · rintro ⟨hne, hij⟩
    have hne' : j.val ≠ i := fun h => hne (Fin.ext h)
    omega
  · intro hij
    refine ⟨?_, by omega⟩
    intro h
    have hjv : j.val = i := by
      have := congr_arg Fin.val h
      simpa using this
    omega

/-- `cumTailSumLin` inverts `I - nilpotentShiftLinGen`: telescoping sum
`M (v - N v) = v`. This is the key algebraic identity that makes
`d5tildeGammaInv_F` a true two-sided inverse of `d5tildeGamma_F` on the
leaf-embedding patterns.

Proof: reverse induction on `i.val`. Base case `i.val = m` uses
`cumTailSumLin_apply_last`; the inductive step uses
`cumTailSumLin_apply_succ` to split off the index-`i` term, the closed
form for `nilpotentShiftLinGen`, and the induction hypothesis at
`i + 1`. -/
theorem cumTailSumLin_oneSubNilp (F : Type) [Field F] (m : ℕ)
    (v : Fin (m + 1) → F) :
    cumTailSumLin F m (v - nilpotentShiftLinGen F m v) = v := by
  -- Closed form for `nilpotentShiftLinGen F m v`.
  have hN : ∀ j : Fin (m + 1), nilpotentShiftLinGen F m v j =
      if h : j.val + 1 < m + 1 then v ⟨j.val + 1, h⟩ else 0 := by
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
  ext ⟨i, hi⟩
  -- Reverse induction on `m - i` (equivalently, induct on `k = m - i` going
  -- from `0` (i.e. `i = m`) up to `m` (i.e. `i = 0`)).
  suffices key : ∀ k : ℕ, ∀ i' (hi' : i' < m + 1), i' + k = m →
      cumTailSumLin F m (v - nilpotentShiftLinGen F m v) ⟨i', hi'⟩ = v ⟨i', hi'⟩ from
    key (m - i) i hi (by omega)
  intro k
  induction k with
  | zero =>
    intro i' hi' heq
    have hi_eq_m : i' = m := by omega
    subst hi_eq_m
    have hidx : (⟨i', hi'⟩ : Fin (i' + 1)) = ⟨i', lt_add_one i'⟩ := rfl
    rw [hidx, cumTailSumLin_apply_last, Pi.sub_apply, hN]
    simp only [show ¬(i' + 1 < i' + 1) by omega, dite_false, sub_zero]
  | succ n ih =>
    intro i' hi' heq
    have hi1 : i' + 1 < m + 1 := by omega
    rw [cumTailSumLin_apply_succ _ _ _ _ hi1]
    rw [ih (i' + 1) hi1 (by omega)]
    rw [Pi.sub_apply, hN]
    simp only [dif_pos hi1]
    ring

/-! ## Section 5d: Closed-form `d5tildeGammaInv_F` identities on leaf-embedding patterns

These are the two key identities for handling the reversed `{2, 3}`
edge direction in the per-(F, Q) D̃₅ indecomposability proof: they
collapse `d5tildeGammaInv_F` applied to the patterns produced by
`gamma_from_embed1_F` and `gamma_from_embed2_F` back to a single
`starEmbed_i_F` term.

The ℂ source `d5tildeRep_isIndecomposable`
(`InfiniteTypeConstructions.lean:1569-1913`) uses `d5tildeGamma` in the
forward direction only, so it does **not** need these identities; they
are new obligations introduced by the per-(F, Q) generalization
(specifically, by the reversed `{2, 3}` edge case). -/

/-- Closed-form γ⁻¹ identity (case (x, x)):
`γ⁻¹(starEmbed1_F x + starEmbed2_F x) = starEmbed1_F x`.

Derivation: with `w = starEmbed1_F x + starEmbed2_F x`, the
projections give `P1 w = x` and `P2 w = x`, so the second-block output
`y_out = M (x - x) = 0` and the first-block output
`x_out = P1 w - y_out = x`. -/
theorem gammaInv_embed1_plus_embed2_F (F : Type) [Field F] (m : ℕ)
    (x : Fin (m + 1) → F) :
    d5tildeGammaInv_F F m (starEmbed1_F F m x + starEmbed2_F F m x) =
      starEmbed1_F F m x := by
  have hP1 : starFirst_F F m (starEmbed1_F F m x + starEmbed2_F F m x) = x := by
    rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero]
  have hP2 : starSecond_F F m (starEmbed1_F F m x + starEmbed2_F F m x) = x := by
    rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add]
  simp only [d5tildeGammaInv_F, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.sub_apply]
  rw [hP1, hP2, sub_self, map_zero, sub_zero, map_zero, add_zero]

/-- Closed-form γ⁻¹ identity (case (y, N y)):
`γ⁻¹(starEmbed1_F y + starEmbed2_F (N y)) = starEmbed2_F y`.

Derivation: with `w = starEmbed1_F y + starEmbed2_F (N y)`, the
projections give `P1 w = y` and `P2 w = N y`, so the second-block output
`y_out = M (y - N y) = y` (via `cumTailSumLin_oneSubNilp`) and the
first-block output `x_out = P1 w - y_out = 0`. -/
theorem gammaInv_embed1_plus_embedNshift_F (F : Type) [Field F] (m : ℕ)
    (y : Fin (m + 1) → F) :
    d5tildeGammaInv_F F m
        (starEmbed1_F F m y + starEmbed2_F F m (nilpotentShiftLinGen F m y)) =
      starEmbed2_F F m y := by
  have hP1 : starFirst_F F m
      (starEmbed1_F F m y + starEmbed2_F F m (nilpotentShiftLinGen F m y)) = y := by
    rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero]
  have hP2 : starSecond_F F m
      (starEmbed1_F F m y + starEmbed2_F F m (nilpotentShiftLinGen F m y)) =
      nilpotentShiftLinGen F m y := by
    rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add]
  simp only [d5tildeGammaInv_F, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.sub_apply]
  rw [hP1, hP2, cumTailSumLin_oneSubNilp, sub_self, map_zero, zero_add]

/-! ## Section 5e: Leaf subspace equalities

The leaf-equality theorem `d5tildeRep_kQ_leaf_equalities` derives the four
identities `W₁(0) = W₁(1) = W₁(4) = W₁(5)` for any complementary invariant
submodule pair `(W₁, W₂)` of `d5tildeRep_kQ F Q hOrient m`. Mirrors the
leaf-equality block of the ℂ-source proof
(`InfiniteTypeConstructions.lean:1820-1834`), generalized over all 32
orientations of `d5tildeAdj`.

The proof case-splits on the direction of each of the five edges of
`d5tildeAdj` (`hOrient_edge` extracts each direction as a 2-way disjunction).
The canonical-orientation branch (all five edges in canonical direction)
mirrors the ℂ-source proof using the helpers from Sections 5/5a-5d. The
remaining 31 orientation branches are deferred to follow-up sub-issues. -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Core decomposition at v=2 for any complementary invariant submodule pair
`(Wmain, Wother)`: if `starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨2⟩`, then
`x ∈ Wmain ⟨0⟩` and `z ∈ Wmain ⟨1⟩`. Uses canonical 0→2 and 1→2 pushes on
both `Wmain` and `Wother`. Analog of the ℂ-source `core` lemma. -/
theorem d5tilde_core_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hMain_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hOther_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨2, by omega⟩)
    (hOther_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨2, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v))
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ Wmain ⟨2, by omega⟩) :
    x ∈ Wmain ⟨0, by omega⟩ ∧ z ∈ Wmain ⟨1, by omega⟩ := by
  have htop0 := (hc ⟨0, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop0
  have htop1 := (hc ⟨1, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
  obtain ⟨c, hcm, d, hd, hcd⟩ := Submodule.mem_sup.mp htop1
  have ha2 := hMain_02 a ha
  have hcm2 := hMain_12 c hcm
  have hb2 := hOther_02 b hb
  have hd2 := hOther_12 d hd
  have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
      (starEmbed1_F F m a + starEmbed2_F F m c) +
        (starEmbed1_F F m b + starEmbed2_F F m d) := by
    rw [← hab, ← hcd]; simp [map_add]; abel
  rw [hsum] at hmem
  have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ Wmain ⟨2, by omega⟩ :=
    (Wmain ⟨2, by omega⟩).add_mem ha2 hcm2
  have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈
      Wmain ⟨2, by omega⟩ := by
    have hsmul := (Wmain ⟨2, by omega⟩).smul_mem (-1 : F) hadd
    have hadd2 := (Wmain ⟨2, by omega⟩).add_mem hmem hsmul
    have key : starEmbed1_F F m a + starEmbed2_F F m c +
        (starEmbed1_F F m b + starEmbed2_F F m d) +
        (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
        starEmbed1_F F m b + starEmbed2_F F m d := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [key] at hadd2
  have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
    have hcross := Submodule.mem_inf.mpr ⟨hw'_in_W,
      (Wother ⟨2, by omega⟩).add_mem hb2 hd2⟩
    rwa [(hc ⟨2, by omega⟩).inf_eq_bot, Submodule.mem_bot] at hcross
  obtain ⟨hb0, hd0⟩ := embed_sum_zero_F F m b d hzero
  exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
         hcd ▸ by rw [hd0, add_zero]; exact hcm⟩

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Core decomposition at v=3 for any complementary invariant submodule pair
`(Wmain, Wother)`: if `starEmbed1_F x + starEmbed2_F z ∈ Wmain ⟨3⟩`, then
`x ∈ Wmain ⟨4⟩` and `z ∈ Wmain ⟨5⟩`. Uses canonical 4→3 and 5→3 pushes on
both `Wmain` and `Wother`. Analog of the ℂ-source `core3` lemma. -/
theorem d5tilde_core3_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hMain_43 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨4, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hMain_53 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨5, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hOther_43 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨4, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨3, by omega⟩)
    (hOther_53 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨5, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨3, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v))
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ Wmain ⟨3, by omega⟩) :
    x ∈ Wmain ⟨4, by omega⟩ ∧ z ∈ Wmain ⟨5, by omega⟩ := by
  have htop4 := (hc ⟨4, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := x)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop4
  have htop5 := (hc ⟨5, by omega⟩).sup_eq_top ▸ Submodule.mem_top (x := z)
  obtain ⟨c, hcm, d, hd, hcd⟩ := Submodule.mem_sup.mp htop5
  have ha3 := hMain_43 a ha
  have hcm3 := hMain_53 c hcm
  have hb3 := hOther_43 b hb
  have hd3 := hOther_53 d hd
  have hsum : starEmbed1_F F m x + starEmbed2_F F m z =
      (starEmbed1_F F m a + starEmbed2_F F m c) +
        (starEmbed1_F F m b + starEmbed2_F F m d) := by
    rw [← hab, ← hcd]; simp [map_add]; abel
  rw [hsum] at hmem
  have hadd : starEmbed1_F F m a + starEmbed2_F F m c ∈ Wmain ⟨3, by omega⟩ :=
    (Wmain ⟨3, by omega⟩).add_mem ha3 hcm3
  have hw'_in_W : starEmbed1_F F m b + starEmbed2_F F m d ∈
      Wmain ⟨3, by omega⟩ := by
    have hsmul := (Wmain ⟨3, by omega⟩).smul_mem (-1 : F) hadd
    have hadd2 := (Wmain ⟨3, by omega⟩).add_mem hmem hsmul
    have key : starEmbed1_F F m a + starEmbed2_F F m c +
        (starEmbed1_F F m b + starEmbed2_F F m d) +
        (-1 : F) • (starEmbed1_F F m a + starEmbed2_F F m c) =
        starEmbed1_F F m b + starEmbed2_F F m d := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rwa [key] at hadd2
  have hzero : starEmbed1_F F m b + starEmbed2_F F m d = 0 := by
    have hcross := Submodule.mem_inf.mpr ⟨hw'_in_W,
      (Wother ⟨3, by omega⟩).add_mem hb3 hd3⟩
    rwa [(hc ⟨3, by omega⟩).inf_eq_bot, Submodule.mem_bot] at hcross
  obtain ⟨hb0, hd0⟩ := embed_sum_zero_F F m b d hzero
  exact ⟨hab ▸ by rw [hb0, add_zero]; exact ha,
         hcd ▸ by rw [hd0, add_zero]; exact hcm⟩

/-! ## Section 5e′: Projection-based reversed-leaf-edge sibling lemmas

For sub-cases of `d5tildeRep_kQ_leaf_equalities` where one or more leaf
edges are reversed, the canonical `d5tilde_core_F` / `d5tilde_core3_F`
lemmas no longer apply (they require both leaf edges to be canonical
pushes). The four siblings below recover one half of the canonical
conjunction using the reversed-direction pull (`starFirst_F` for the
"1-side" leaf and `starSecond_F` for the "2-side" leaf), via the
identity `starFirst_F (starEmbed1_F x + starEmbed2_F z) = x` (and the
symmetric identity for `starSecond_F`).

Each sibling concludes only one half of the original `core_F` /
`core3_F` conjunction — the half made trivial by the projection
identity. The other half, when the corresponding leaf is also reversed,
follows by applying the companion sibling. When the other leaf is
canonical, the other half generally requires additional argument
inside `d5tildeRep_kQ_leaf_equalities`'s sub-case (it is not derivable
in general from a single pull + a single push). -/

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection-based sibling for the first half of `d5tilde_core_F` at
the `e02 = 2→0` reversed orientation. Given a submodule `W` such that
the reversed 0-2 pull `starFirst_F` sends `W ⟨2⟩` into `W ⟨0⟩`, any sum
`starEmbed1_F x + starEmbed2_F z` in `W ⟨2⟩` has its first component
`x` in `W ⟨0⟩`.

Proof: apply the pull and rewrite using `starFirst_F_starEmbed1_F = id`
and `starFirst_F_starEmbed2_F = 0`. Mirrors the canonical-direction
push in the same role inside the existing `d5tilde_core_F` proof, but
runs in the opposite direction. -/
theorem d5tilde_core_F_proj1
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hW_20 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨2, by omega⟩ →
        starFirst_F F m w ∈ W ⟨0, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨2, by omega⟩) :
    x ∈ W ⟨0, by omega⟩ := by
  have h := hW_20 _ hmem
  rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection-based sibling for the second half of `d5tilde_core_F` at
the `e12 = 2→1` reversed orientation. Given a submodule `W` such that
the reversed 1-2 pull `starSecond_F` sends `W ⟨2⟩` into `W ⟨1⟩`, any
sum `starEmbed1_F x + starEmbed2_F z` in `W ⟨2⟩` has its second
component `z` in `W ⟨1⟩`.

Proof: apply the pull and rewrite using `starSecond_F_starEmbed1_F = 0`
and `starSecond_F_starEmbed2_F = id`. Symmetric counterpart of
`d5tilde_core_F_proj1`. -/
theorem d5tilde_core_F_proj2
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hW_21 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨2, by omega⟩ →
        starSecond_F F m w ∈ W ⟨1, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨2, by omega⟩) :
    z ∈ W ⟨1, by omega⟩ := by
  have h := hW_21 _ hmem
  rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection-based sibling for the first half of `d5tilde_core3_F` at
the `e43 = 3→4` reversed orientation. Given a submodule `W` such that
the reversed 4-3 pull `starFirst_F` sends `W ⟨3⟩` into `W ⟨4⟩`, any sum
`starEmbed1_F x + starEmbed2_F z` in `W ⟨3⟩` has its first component
`x` in `W ⟨4⟩`.

Proof: apply the pull and rewrite using `starFirst_F_starEmbed1_F = id`
and `starFirst_F_starEmbed2_F = 0`. v=3 analogue of
`d5tilde_core_F_proj1`. -/
theorem d5tilde_core3_F_proj1
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hW_34 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨3, by omega⟩ →
        starFirst_F F m w ∈ W ⟨4, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨3, by omega⟩) :
    x ∈ W ⟨4, by omega⟩ := by
  have h := hW_34 _ hmem
  rw [map_add, starFirst_F_starEmbed1_F, starFirst_F_starEmbed2_F, add_zero] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Projection-based sibling for the second half of `d5tilde_core3_F`
at the `e53 = 3→5` reversed orientation. Given a submodule `W` such
that the reversed 5-3 pull `starSecond_F` sends `W ⟨3⟩` into `W ⟨5⟩`,
any sum `starEmbed1_F x + starEmbed2_F z` in `W ⟨3⟩` has its second
component `z` in `W ⟨5⟩`.

Proof: apply the pull and rewrite using `starSecond_F_starEmbed1_F = 0`
and `starSecond_F_starEmbed2_F = id`. v=3 analogue of
`d5tilde_core_F_proj2`. -/
theorem d5tilde_core3_F_proj2
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (W : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hW_35 : ∀ (w : Fin (2 * (m + 1)) → F), w ∈ W ⟨3, by omega⟩ →
        starSecond_F F m w ∈ W ⟨5, by omega⟩)
    (x z : Fin (m + 1) → F)
    (hmem : starEmbed1_F F m x + starEmbed2_F F m z ∈ W ⟨3, by omega⟩) :
    z ∈ W ⟨5, by omega⟩ := by
  have h := hW_35 _ hmem
  rw [map_add, starSecond_F_starEmbed1_F, starSecond_F_starEmbed2_F, zero_add] at h
  exact h

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- γ-coupled leaf containments. Given canonical embed pushes on both
`Wmain` and `Wother` and the `2→3` γ-push on `Wmain`, derive four
containment facts that link the source leaves `{0, 1}` to the target
leaves `{4, 5}` via γ. Analog of the ℂ-source `gamma_containment` lemma. -/
theorem d5tilde_gamma_containment_F
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (Wmain Wother : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hMain_02 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_12 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨1, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨2, by omega⟩)
    (hMain_23 : ∀ (x : Fin (2 * (m + 1)) → F), x ∈ Wmain ⟨2, by omega⟩ →
        d5tildeGamma_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hMain_43 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨4, by omega⟩ →
        starEmbed1_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hMain_53 : ∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨5, by omega⟩ →
        starEmbed2_F F m x ∈ Wmain ⟨3, by omega⟩)
    (hOther_43 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨4, by omega⟩ →
        starEmbed1_F F m x ∈ Wother ⟨3, by omega⟩)
    (hOther_53 : ∀ (x : Fin (m + 1) → F), x ∈ Wother ⟨5, by omega⟩ →
        starEmbed2_F F m x ∈ Wother ⟨3, by omega⟩)
    (hc : ∀ v, IsCompl (Wmain v) (Wother v)) :
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨4, by omega⟩) ∧
    (∀ (x : Fin (m + 1) → F), x ∈ Wmain ⟨0, by omega⟩ →
      x ∈ Wmain ⟨5, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      y ∈ Wmain ⟨4, by omega⟩) ∧
    (∀ (y : Fin (m + 1) → F), y ∈ Wmain ⟨1, by omega⟩ →
      nilpotentShiftLinGen F m y ∈ Wmain ⟨5, by omega⟩) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    exact (d5tilde_core3_F F Q hOrient m Wmain Wother hMain_43 hMain_53
      hOther_43 hOther_53 hc x x hgamma).1
  · have he1 := hMain_02 x hx
    have hgamma := hMain_23 (starEmbed1_F F m x) he1
    rw [gamma_from_embed1_F] at hgamma
    exact (d5tilde_core3_F F Q hOrient m Wmain Wother hMain_43 hMain_53
      hOther_43 hOther_53 hc x x hgamma).2
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    exact (d5tilde_core3_F F Q hOrient m Wmain Wother hMain_43 hMain_53
      hOther_43 hOther_53 hc y (nilpotentShiftLinGen F m y) hgamma).1
  · have he2 := hMain_12 y hy
    have hgamma := hMain_23 (starEmbed2_F F m y) he2
    rw [gamma_from_embed2_F] at hgamma
    exact (d5tilde_core3_F F Q hOrient m Wmain Wother hMain_43 hMain_53
      hOther_43 hOther_53 hc y (nilpotentShiftLinGen F m y) hgamma).2

attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- For any orientation `Q` of `d5tildeAdj` and any complementary invariant
submodule pair `(W₁, W₂)` of `d5tildeRep_kQ F Q hOrient m`, the leaf
vertices `0, 1, 4, 5` carry equal `W₁`-subspaces. (The analogous statement
for `W₂` follows by applying the theorem with the arguments `(W₂, W₁)`
flipped — `IsCompl` is symmetric.)

This is the analog of the leaf-equality block in the ℂ-specific proof
(`InfiniteTypeConstructions.lean:1820-1834`).

**Proof body partially deferred** — see #2850 for the decomposition. The
all-canonical orientation branch (0→2, 1→2, 2→3, 4→3, 5→3) is proven
inline by mirroring the ℂ-source proof: the helper invariance facts are
specialized via `simp only [d5tildeRep_kQ, d5tildeRepMap_kQ]`, then the
`core_F` (v=2 decomposition), `core3_F` (v=3 decomposition), and
`gamma_containment_F` (γ-coupled leaf containments) lemmas are
established. Final `compl_le_forces_eq` applications chain the
containments into the three equalities. The remaining 31 orientation
branches are tracked as follow-up sub-issues. -/
theorem d5tildeRep_kQ_leaf_equalities
    (F : Type) [Field F]
    (Q : @Quiver.{0, 0} (Fin 6))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin 6) Q a b)]
    (hOrient : @Etingof.IsOrientationOf 6 Q d5tildeAdj)
    (m : ℕ)
    (W₁ W₂ : ∀ v, Submodule F ((d5tildeRep_kQ F Q hOrient m).obj v))
    (hW₁_inv : ∀ {a b : Fin 6} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₁ a, (d5tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₁ b)
    (hW₂_inv : ∀ {a b : Fin 6} (e : @Quiver.Hom _ Q a b),
      ∀ x ∈ W₂ a, (d5tildeRep_kQ F Q hOrient m).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ ∧
    W₁ ⟨0, by omega⟩ = W₁ ⟨4, by omega⟩ ∧
    W₁ ⟨0, by omega⟩ = W₁ ⟨5, by omega⟩ := by
  letI := Q
  have hOrient_edge := hOrient.2.1
  -- d5tildeAdj values at each edge (canonical direction)
  have h02 : d5tildeAdj ⟨0, by omega⟩ ⟨2, by omega⟩ = 1 := by
    simp [d5tildeAdj]
  have h12 : d5tildeAdj ⟨1, by omega⟩ ⟨2, by omega⟩ = 1 := by
    simp [d5tildeAdj]
  have h23 : d5tildeAdj ⟨2, by omega⟩ ⟨3, by omega⟩ = 1 := by
    simp [d5tildeAdj]
  have h43 : d5tildeAdj ⟨4, by omega⟩ ⟨3, by omega⟩ = 1 := by
    simp [d5tildeAdj]
  have h53 : d5tildeAdj ⟨5, by omega⟩ ⟨3, by omega⟩ = 1 := by
    simp [d5tildeAdj]
  -- Per-edge direction disjunctions (first Or branch = canonical for each).
  -- Use the FieldGenericCycle pattern: rcases the Or, then obtain the Nonempty.
  rcases hOrient_edge ⟨0, by omega⟩ ⟨2, by omega⟩ h02 with hQ02 | hQ02
  · -- e02 = Or.inl: 0→2 canonical
    obtain ⟨a02⟩ := hQ02
    rcases hOrient_edge ⟨1, by omega⟩ ⟨2, by omega⟩ h12 with hQ12 | hQ12
    · -- e12 = Or.inl: 1→2 canonical
      obtain ⟨a12⟩ := hQ12
      rcases hOrient_edge ⟨2, by omega⟩ ⟨3, by omega⟩ h23 with hQ23 | hQ23
      · -- e23 = Or.inl: 2→3 canonical
        obtain ⟨a23⟩ := hQ23
        rcases hOrient_edge ⟨4, by omega⟩ ⟨3, by omega⟩ h43 with hQ43 | hQ43
        · -- e43 = Or.inl: 4→3 canonical
          obtain ⟨a43⟩ := hQ43
          rcases hOrient_edge ⟨5, by omega⟩ ⟨3, by omega⟩ h53 with hQ53 | hQ53
          · -- e53 = Or.inl: 5→3 canonical
            obtain ⟨a53⟩ := hQ53
            -- ALL CANONICAL: 0→2, 1→2, 2→3, 4→3, 5→3 — mirrors ℂ-source proof.
            -- Specialize invariance to the concrete rep maps.
            have hW₁_02 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a02 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₁_12 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨2, by omega⟩ := by
              have h := hW₁_inv a12 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₁_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₁ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₁ ⟨3, by omega⟩ := by
              have h := hW₁_inv a23 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₁_43 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨4, by omega⟩) :
                starEmbed1_F F m x ∈ W₁ ⟨3, by omega⟩ := by
              have h := hW₁_inv a43 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₁_53 (x : Fin (m + 1) → F) (hx : x ∈ W₁ ⟨5, by omega⟩) :
                starEmbed2_F F m x ∈ W₁ ⟨3, by omega⟩ := by
              have h := hW₁_inv a53 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₂_02 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨0, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a02 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₂_12 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨1, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨2, by omega⟩ := by
              have h := hW₂_inv a12 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₂_23 (x : Fin (2 * (m + 1)) → F) (hx : x ∈ W₂ ⟨2, by omega⟩) :
                d5tildeGamma_F F m x ∈ W₂ ⟨3, by omega⟩ := by
              have h := hW₂_inv a23 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₂_43 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨4, by omega⟩) :
                starEmbed1_F F m x ∈ W₂ ⟨3, by omega⟩ := by
              have h := hW₂_inv a43 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            have hW₂_53 (x : Fin (m + 1) → F) (hx : x ∈ W₂ ⟨5, by omega⟩) :
                starEmbed2_F F m x ∈ W₂ ⟨3, by omega⟩ := by
              have h := hW₂_inv a53 x hx
              simp only [d5tildeRep_kQ, d5tildeRepMap_kQ] at h
              exact h
            -- Apply d5tilde_gamma_containment_F to W₁ and W₂ to get leaf containments.
            -- The v=2 / v=3 decomposition helpers d5tilde_core_F / d5tilde_core3_F
            -- live at top level (Section 5e above) and are reused inside
            -- d5tilde_gamma_containment_F.
            obtain ⟨h04, h05, h14, _hN15⟩ :=
              d5tilde_gamma_containment_F F Q hOrient m W₁ W₂
                hW₁_02 hW₁_12 hW₁_23 hW₁_43 hW₁_53 hW₂_43 hW₂_53 hcompl
            obtain ⟨h04', h05', h14', _hN15'⟩ :=
              d5tilde_gamma_containment_F F Q hOrient m W₂ W₁
                hW₂_02 hW₂_12 hW₂_23 hW₂_43 hW₂_53 hW₁_43 hW₁_53
                (fun v => (hcompl v).symm)
            -- Apply compl_le_forces_eq to derive equalities W₁(0) = W₁(k) for k=4,5
            -- and W₁(1) = W₁(4); then chain W₁(0) = W₁(1) via W₁(4).
            have heq04 : W₁ ⟨0, by omega⟩ = W₁ ⟨4, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨4, by omega⟩) h04 h04').1
            have heq05 : W₁ ⟨0, by omega⟩ = W₁ ⟨5, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨0, by omega⟩) (W₂ ⟨0, by omega⟩)
                (W₁ ⟨5, by omega⟩) (W₂ ⟨5, by omega⟩)
                (hcompl ⟨0, by omega⟩) (hcompl ⟨5, by omega⟩) h05 h05').1
            have heq14 : W₁ ⟨1, by omega⟩ = W₁ ⟨4, by omega⟩ :=
              (compl_le_forces_eq (V := Fin (m + 1) → F)
                (W₁ ⟨1, by omega⟩) (W₂ ⟨1, by omega⟩)
                (W₁ ⟨4, by omega⟩) (W₂ ⟨4, by omega⟩)
                (hcompl ⟨1, by omega⟩) (hcompl ⟨4, by omega⟩) h14 h14').1
            have heq01 : W₁ ⟨0, by omega⟩ = W₁ ⟨1, by omega⟩ := heq04.trans heq14.symm
            exact ⟨heq01, heq04, heq05⟩
          · -- e53 reversed (3→5): follow-up sub-issue
            sorry
        · -- e43 reversed (3→4): follow-up sub-issue
          sorry
      · -- e23 reversed (3→2): follow-up sub-issue (uses γ⁻¹)
        sorry
    · -- e12 reversed (2→1): follow-up sub-issue (uses starSecond_F projection)
      sorry
  · -- e02 reversed (2→0): follow-up sub-issue (uses starFirst_F projection)
    sorry

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
`gamma_from_embed1_F`, `gamma_from_embed2_F` (Section 5) and
`embed_sum_zero_F`, `center_decomp_F`
(`FieldGenericStar.lean`) are F-generic extractions of the inline
computations used in the ℂ proof and are ready for use by the
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

set_option maxHeartbeats 3200000 in
-- reason: 15 distinctness facts plus the 36-case `fin_cases` adjacency
-- proof through the `Fin 6 ↪ Fin n` embedding push elaboration past
-- the default budget; mirrors the same setting on
-- `adjacent_branches_infinite_type` (`InfiniteTypeConstructions.lean:4760`).
attribute [-instance] CategoryTheory.CategoryStruct.toQuiver
  CategoryTheory.ReflQuiver.toQuiver in
/-- Per-(F, Q) version of `adjacent_branches_infinite_type`
(`InfiniteTypeConstructions.lean:4764`): a connected acyclic simple
graph with two adjacent degree-3 vertices (and all degrees ≤ 3) has
infinite representation type for every algebraically closed `F` and
every orientation `Q`. Embeds D̃₅ on the two branch points plus their
4 other neighbours and dispatches to `d5tilde_not_finite_type_per_kQ`
via `subgraph_infinite_type_transfer_per_kQ`. -/
theorem adjacent_branches_infinite_type_per_kQ {n : ℕ}
    (adj : Matrix (Fin n) (Fin n) ℤ)
    (hsymm : adj.IsSymm)
    (hdiag : ∀ i, adj i i = 0)
    (h01 : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    (h_acyclic : ∀ (cycle : List (Fin n)) (hclen : 3 ≤ cycle.length), cycle.Nodup →
      (∀ k, (h : k + 1 < cycle.length) →
        adj (cycle.get ⟨k, by omega⟩) (cycle.get ⟨k + 1, h⟩) = 1) →
      adj (cycle.getLast (List.ne_nil_of_length_pos (by omega)))
        (cycle.get ⟨0, by omega⟩) ≠ 1)
    (v₀ w : Fin n) (hv₀_deg : vertexDegree adj v₀ = 3)
    (hw_deg : vertexDegree adj w = 3) (hvw_adj : adj v₀ w = 1)
    (F : Type) [Field F] [IsAlgClosed F]
    (Q : @Quiver.{0, 0} (Fin n))
    [∀ a b, Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (hOrient : @Etingof.IsOrientationOf n Q adj) :
    ¬ Set.Finite
      {d : Fin n → ℕ |
        ∃ V : @Etingof.QuiverRepresentation.{0,0,0,0} F (Fin n) _ Q,
          V.IsIndecomposable ∧ ∀ v, Nonempty (V.obj v ≃ₗ[F] (Fin (d v) → F))} := by
  -- adj_comm: adj i j = adj j i (from symmetry)
  have adj_comm : ∀ i j, adj i j = adj j i := fun i j => hsymm.apply j i
  -- ne_of_adj: adjacent vertices are distinct
  have ne_of_adj : ∀ a b, adj a b = 1 → a ≠ b := fun a b h hab => by
    rw [hab, hdiag] at h; exact one_ne_zero h.symm
  -- Extract the 3 neighbors of v₀
  set S₀ := Finset.univ.filter (fun j => adj v₀ j = 1) with hS₀_def
  have hS₀_card : S₀.card = 3 := hv₀_deg
  have hw_mem : w ∈ S₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw_adj⟩
  have hS₀_erase : (S₀.erase w).card = 2 := by
    rw [Finset.card_erase_of_mem hw_mem, hS₀_card]
  obtain ⟨u₁, u₂, hu₁₂, hS₀_eq⟩ := Finset.card_eq_two.mp hS₀_erase
  have hu₁_mem : u₁ ∈ S₀.erase w := hS₀_eq ▸ Finset.mem_insert_self u₁ _
  have hu₂_mem : u₂ ∈ S₀.erase w := hS₀_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self u₂))
  have hu₁_adj : adj v₀ u₁ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₁_mem)).2
  have hu₂_adj : adj v₀ u₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu₂_mem)).2
  have hu₁_ne_w : u₁ ≠ w := Finset.ne_of_mem_erase hu₁_mem
  have hu₂_ne_w : u₂ ≠ w := Finset.ne_of_mem_erase hu₂_mem
  -- Extract the 3 neighbors of w
  set Sw := Finset.univ.filter (fun j => adj w j = 1) with hSw_def
  have hSw_card : Sw.card = 3 := hw_deg
  have hv₀_mem_Sw : v₀ ∈ Sw :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (adj_comm w v₀).trans hvw_adj⟩
  have hSw_erase : (Sw.erase v₀).card = 2 := by
    rw [Finset.card_erase_of_mem hv₀_mem_Sw, hSw_card]
  obtain ⟨w₁, w₂, hw₁₂, hSw_eq⟩ := Finset.card_eq_two.mp hSw_erase
  have hw₁_mem : w₁ ∈ Sw.erase v₀ := hSw_eq ▸ Finset.mem_insert_self w₁ _
  have hw₂_mem : w₂ ∈ Sw.erase v₀ := hSw_eq ▸ Finset.mem_insert.mpr
    (Or.inr (Finset.mem_singleton_self w₂))
  have hw₁_adj : adj w w₁ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hw₁_mem)).2
  have hw₂_adj : adj w w₂ = 1 :=
    (Finset.mem_filter.mp (Finset.mem_of_mem_erase hw₂_mem)).2
  have hw₁_ne_v₀ : w₁ ≠ v₀ := Finset.ne_of_mem_erase hw₁_mem
  have hw₂_ne_v₀ : w₂ ≠ v₀ := Finset.ne_of_mem_erase hw₂_mem
  -- Key distinctness facts (from adjacency)
  have hv₀_ne_w : v₀ ≠ w := ne_of_adj v₀ w hvw_adj
  have hu₁_ne_v₀ : u₁ ≠ v₀ := (ne_of_adj v₀ u₁ hu₁_adj).symm
  have hu₂_ne_v₀ : u₂ ≠ v₀ := (ne_of_adj v₀ u₂ hu₂_adj).symm
  have hw₁_ne_w : w₁ ≠ w := (ne_of_adj w w₁ hw₁_adj).symm
  have hw₂_ne_w : w₂ ≠ w := (ne_of_adj w w₂ hw₂_adj).symm
  -- Non-edges via acyclic_no_triangle (center has both as neighbors → no triangle)
  have hu₁u₂ : adj u₁ u₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ u₂
      hu₁₂ hu₁_ne_v₀ hu₂_ne_v₀ hu₁_adj hu₂_adj
  have hu₁_w : adj u₁ w = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₁ w
      hu₁_ne_w hu₁_ne_v₀ hv₀_ne_w.symm hu₁_adj hvw_adj
  have hu₂_w : adj u₂ w = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic v₀ u₂ w
      hu₂_ne_w hu₂_ne_v₀ hv₀_ne_w.symm hu₂_adj hvw_adj
  have hw₁w₂ : adj w₁ w₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic w w₁ w₂
      hw₁₂ hw₁_ne_w hw₂_ne_w hw₁_adj hw₂_adj
  have hw_v₀ : adj w v₀ = 1 := (adj_comm w v₀).trans hvw_adj
  have hv₀_w₁ : adj v₀ w₁ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic w v₀ w₁
      hw₁_ne_v₀.symm hv₀_ne_w hw₁_ne_w hw_v₀ hw₁_adj
  have hv₀_w₂ : adj v₀ w₂ = 0 :=
    acyclic_no_triangle adj hsymm h01 h_acyclic w v₀ w₂
      hw₂_ne_v₀.symm hv₀_ne_w hw₂_ne_w hw_v₀ hw₂_adj
  have hu₁_ne_w₁ : u₁ ≠ w₁ := by intro h; rw [h] at hu₁_adj; linarith
  have hu₁_ne_w₂ : u₁ ≠ w₂ := by intro h; rw [h] at hu₁_adj; linarith
  have hu₂_ne_w₁ : u₂ ≠ w₁ := by intro h; rw [h] at hu₂_adj; linarith
  have hu₂_ne_w₂ : u₂ ≠ w₂ := by intro h; rw [h] at hu₂_adj; linarith
  have hw₁_w : adj w₁ w = 1 := (adj_comm w₁ w).trans hw₁_adj
  have hw₂_w : adj w₂ w = 1 := (adj_comm w₂ w).trans hw₂_adj
  have path_nodup : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → [a, b, c, d].Nodup := by
    intro a b c d hab hac had hbc hbd hcd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_or, not_false_eq_true, List.nodup_nil, and_self, and_true]
    exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩
  have path_edges : ∀ (a b c d : Fin n),
      adj a b = 1 → adj b c = 1 → adj c d = 1 →
      ∀ k, (hk : k + 1 < [a, b, c, d].length) →
        adj ([a, b, c, d].get ⟨k, by omega⟩) ([a, b, c, d].get ⟨k + 1, hk⟩) = 1 := by
    intro a b c d h₁ h₂ h₃ k hk
    have : k + 1 < 4 := by simpa using hk
    have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  have hu₁_w₁ : adj u₁ w₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₁, w, v₀, u₁] (by simp)
      (path_nodup w₁ w v₀ u₁ hw₁_ne_w hw₁_ne_v₀
        hu₁_ne_w₁.symm hv₀_ne_w.symm hu₁_ne_w.symm hu₁_ne_v₀.symm)
      (path_edges w₁ w v₀ u₁ hw₁_w hw_v₀ hu₁_adj)
  have hu₁_w₂ : adj u₁ w₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₂, w, v₀, u₁] (by simp)
      (path_nodup w₂ w v₀ u₁ hw₂_ne_w hw₂_ne_v₀
        hu₁_ne_w₂.symm hv₀_ne_w.symm hu₁_ne_w.symm hu₁_ne_v₀.symm)
      (path_edges w₂ w v₀ u₁ hw₂_w hw_v₀ hu₁_adj)
  have hu₂_w₁ : adj u₂ w₁ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₁, w, v₀, u₂] (by simp)
      (path_nodup w₁ w v₀ u₂ hw₁_ne_w hw₁_ne_v₀
        hu₂_ne_w₁.symm hv₀_ne_w.symm hu₂_ne_w.symm hu₂_ne_v₀.symm)
      (path_edges w₁ w v₀ u₂ hw₁_w hw_v₀ hu₂_adj)
  have hu₂_w₂ : adj u₂ w₂ = 0 :=
    acyclic_path_nonadj adj hsymm h01 h_acyclic [w₂, w, v₀, u₂] (by simp)
      (path_nodup w₂ w v₀ u₂ hw₂_ne_w hw₂_ne_v₀
        hu₂_ne_w₂.symm hv₀_ne_w.symm hu₂_ne_w.symm hu₂_ne_v₀.symm)
      (path_edges w₂ w v₀ u₂ hw₂_w hw_v₀ hu₂_adj)
  -- Construct the embedding φ : Fin 6 ↪ Fin n
  -- Map: 0 → u₁, 1 → u₂, 2 → v₀, 3 → w, 4 → w₁, 5 → w₂
  let φ_fun : Fin 6 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => u₁ | ⟨1, _⟩ => u₂ | ⟨2, _⟩ => v₀
    | ⟨3, _⟩ => w  | ⟨4, _⟩ => w₁ | ⟨5, _⟩ => w₂
  have φ_inj : Function.Injective φ_fun := by
    intro i j hij; simp only [φ_fun] at hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | (exact absurd hij ‹_›) | (exact absurd hij.symm ‹_›)
  let φ : Fin 6 ↪ Fin n := ⟨φ_fun, φ_inj⟩
  have hembed : ∀ i j, d5tildeAdj i j = adj (φ i) (φ j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [d5tildeAdj, φ, φ_fun] <;> norm_num <;>
      linarith [hdiag u₁, hdiag u₂, hdiag v₀, hdiag w, hdiag w₁, hdiag w₂,
                adj_comm u₁ v₀, adj_comm u₂ v₀, adj_comm w v₀,
                adj_comm w₁ w, adj_comm w₂ w,
                adj_comm u₁ u₂, adj_comm u₁ w, adj_comm u₂ w,
                adj_comm w₁ w₂, adj_comm v₀ w₁, adj_comm v₀ w₂,
                adj_comm u₁ w₁, adj_comm u₁ w₂, adj_comm u₂ w₁, adj_comm u₂ w₂]
  exact subgraph_infinite_type_transfer_per_kQ φ F Q
    (d5tilde_not_finite_type_per_kQ F (restrictOrientationViaEmb φ Q)
      (restrictOrientationViaEmb_isOrientationOf φ hembed hOrient))

end Etingof
