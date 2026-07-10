import Mathlib

/-!
# Problem 2.16.2: Irreducible representations of the 2-dimensional Lie algebra `[X, Y] = Y`

Let `𝔤` be the two-dimensional Lie algebra with basis `X, Y` and commutation relation
`[X, Y] = Y`. We realize it as the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units
`X = e₁₁` and `Y = e₁₂` (which satisfy `[e₁₁, e₁₂] = e₁₂`).

The problem asks to classify the irreducible finite-dimensional representations in characteristic
`0` and characteristic `p`, and whether Lie's theorem holds in characteristic `p`. We render the
book's *answers* as the statements:

* **Characteristic `0`** (algebraically closed, so Lie's theorem applies): every irreducible
  finite-dimensional representation is `1`-dimensional, and on such a representation `Y` acts as
  `0`. So the irreducibles are classified by the scalar `X ↦ λ ∈ k` (with `Y ↦ 0`).
* **Characteristic `p`**: Lie's theorem is **false** — there exist irreducible finite-dimensional
  representations of dimension `> 1` (in fact of dimension `p`).

The characteristic-`0` cluster (`bracket_X_Y`, `charZero_irreducible_finrank_one`,
`charZero_Y_acts_zero`) is proved sorry-free below, along with the supporting fact that `𝔤` is
solvable (`instIsSolvable`). The characteristic-`p` failure `lie_theorem_fails_charP` remains a
`sorry` (it needs the construction of a `p`-dimensional irreducible `𝔤`-module); see issue #6132.
-/

namespace Etingof.Problem2_16_2

open scoped Matrix
open Module (finrank)

-- `LieRing.ofAssociativeRing` is a local instance from Mathlib v4.31 onward (to avoid a bracket
-- diamond when a ring acts on itself); re-enable it locally so the matrix Lie algebra elaborates.
-- Together with the global `LieAlgebra.ofAssociativeAlgebra` this provides the `k`-linear bracket
-- structure on `Matrix (Fin 2) (Fin 2) k`.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]

/-- The two-dimensional Lie algebra `𝔤 = ⟨X, Y | [X, Y] = Y⟩`, realized as the Lie subalgebra of
`𝔤𝔩(2, k)` spanned by the matrix units `X = e₁₁` and `Y = e₁₂`. (Etingof Problem 2.16.2) -/
noncomputable def g : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieSubalgebra.lieSpan k _ {Matrix.single 0 0 1, Matrix.single 0 1 1}

/-- The generator `X = e₁₁` of `𝔤`. -/
noncomputable def X : g k :=
  ⟨Matrix.single 0 0 1, LieSubalgebra.subset_lieSpan (by left; rfl)⟩

/-- The generator `Y = e₁₂` of `𝔤`. -/
noncomputable def Y : g k :=
  ⟨Matrix.single 0 1 1, LieSubalgebra.subset_lieSpan (by right; rfl)⟩

/-! ## Matrix-unit bracket computations

The four brackets of the matrix units `e₁₁ = single 0 0 1`, `e₁₂ = single 0 1 1`. The remaining two
(`⁅e₁₁, e₁₁⁆` and `⁅e₁₂, e₁₂⁆`) are `0` by `lie_self`. -/

/-- The matrix unit `e₁₁ = single 0 0 1` in `𝔤𝔩(2, k)`. -/
private abbrev e11 : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 0 1

/-- The matrix unit `e₁₂ = single 0 1 1` in `𝔤𝔩(2, k)`. -/
private abbrev e12 : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 1 1

/-- `⁅e₁₁, e₁₂⁆ = e₁₂`. -/
private theorem bracket_e11_e12 : ⁅e11 k, e12 k⁆ = e12 k := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [e11, e12, LieRing.of_associative_ring_bracket, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h]

/-- `⁅e₁₂, e₁₁⁆ = -e₁₂`. -/
private theorem bracket_e12_e11 : ⁅e12 k, e11 k⁆ = - e12 k := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [e11, e12, LieRing.of_associative_ring_bracket, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h]

/-- Bracket of two arbitrary elements of `span{e₁₁, e₁₂}`: it is a scalar multiple of `e₁₂`. This
is the key computation showing `span{e₁₁, e₁₂}` is closed under the bracket (a Lie subalgebra) and
that its derived algebra lands in `span{e₁₂}`. -/
private theorem bracket_expand (a b c d : k) :
    ⁅a • e11 k + b • e12 k, c • e11 k + d • e12 k⁆ = (a * d - b * c) • e12 k := by
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, bracket_e11_e12 k,
    bracket_e12_e11 k, smul_zero, add_zero, zero_add, smul_neg]
  module

/-- The defining commutation relation `[X, Y] = Y` of `𝔤`. -/
theorem bracket_X_Y : ⁅X k, Y k⁆ = Y k := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  exact bracket_e11_e12 k

/-! ## The underlying submodule and solvability

`g k` is spanned (as a submodule) by `e₁₁, e₁₂`; we only need the `≤` direction, obtained by
exhibiting `span{e₁₁, e₁₂}` as a Lie subalgebra. From this, every bracket in `g k` is a scalar
multiple of `Y`, the derived algebra `⁅g, g⁆` lands in `span{Y}` (which is abelian), and hence `g`
is solvable. -/

/-- `span{e₁₁, e₁₂}` packaged as a Lie subalgebra of `𝔤𝔩(2, k)` (it is closed under the bracket by
`bracket_expand`). -/
private noncomputable def spanB : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  { Submodule.span k {e11 k, e12 k} with
    lie_mem' := by
      intro x y hx hy
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [bracket_expand]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)) }

private theorem g_le_spanB : g k ≤ spanB k :=
  LieSubalgebra.lieSpan_le.mpr (by
    intro z hz
    rcases hz with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp))

private theorem coe_mem_span (x : g k) :
    (x : Matrix (Fin 2) (Fin 2) k) ∈ Submodule.span k {e11 k, e12 k} :=
  g_le_spanB k x.2

/-- Every bracket of elements of `g k` is a scalar multiple of `Y`. -/
private theorem bracket_mem_span_Y (x y : g k) : ⁅x, y⁆ ∈ Submodule.span k {Y k} := by
  obtain ⟨a, b, hx⟩ := Submodule.mem_span_pair.mp (coe_mem_span k x)
  obtain ⟨c, d, hy⟩ := Submodule.mem_span_pair.mp (coe_mem_span k y)
  rw [Submodule.mem_span_singleton]
  refine ⟨a * d - b * c, ?_⟩
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, ← hx, ← hy, bracket_expand]
  rfl

/-- The first derived algebra `⁅g, g⁆` is contained in `span{Y}`. -/
private theorem derivedSeries_one_le_span_Y (x : g k)
    (hx : x ∈ LieAlgebra.derivedSeries k (g k) 1) : x ∈ Submodule.span k {Y k} := by
  have hx' : x ∈ (LieAlgebra.derivedSeries k (g k) 1 : Submodule k (g k)) := hx
  rw [LieAlgebra.coe_derivedSeries_one_eq] at hx'
  refine Submodule.span_le.mpr ?_ hx'
  rintro z ⟨a, b, rfl⟩
  exact bracket_mem_span_Y k a b

/-- `𝔤` is solvable: its derived series reaches `0` after two steps (the derived algebra lands in
`span{Y}`, which is abelian since `⁅Y, Y⁆ = 0`). -/
instance instIsSolvable : LieAlgebra.IsSolvable (g k) := by
  refine LieAlgebra.IsSolvable.mk (?_ : LieAlgebra.derivedSeries k (g k) 2 = ⊥)
  have key : ⁅LieAlgebra.derivedSeries k (g k) 1, LieAlgebra.derivedSeries k (g k) 1⁆ = ⊥ := by
    rw [LieSubmodule.lie_eq_bot_iff]
    intro x hx m hm
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp (derivedSeries_one_le_span_Y k x hx)
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp (derivedSeries_one_le_span_Y k m hm)
    simp [smul_lie, lie_smul]
  have e2 : LieAlgebra.derivedSeries k (g k) 2
      = ⁅LieAlgebra.derivedSeries k (g k) 1, LieAlgebra.derivedSeries k (g k) 1⁆ := rfl
  rw [e2]; exact key

/-! ## Characteristic 0: Lie's theorem -/

/-- **Characteristic `0`.** Every irreducible finite-dimensional representation of `𝔤` is
`1`-dimensional (Lie's theorem, `k` algebraically closed of characteristic `0`).

The proof follows Problem 2.16.1 (`Etingof.Problem2_16_1.finrank_eq_one_of_isSolvable`): a common
eigenvector `v` for all of `𝔤` exists (Mathlib's Lie theorem, applicable since `𝔤` is solvable and
`k` is algebraically closed hence triangularizable), and the line `k ∙ v` is a nonzero
subrepresentation, so by irreducibility it is everything. -/
theorem charZero_irreducible_finrank_one [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] :
    Module.finrank k M = 1 := by
  have : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (g k) M
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k (g k) M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace M χ)
  rw [LieModule.mem_weightSpace] at hv
  have hv0 : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  let N : LieSubmodule k (g k) M :=
    { __ := Submodule.span k {v}
      lie_mem := fun {x m} hm => by
        have hm' : m ∈ Submodule.span k {v} := hm
        rw [Submodule.mem_span_singleton] at hm'
        obtain ⟨c, rfl⟩ := hm'
        exact Submodule.mem_span_singleton.mpr ⟨c * χ x, by rw [lie_smul, hv x, smul_smul]⟩ }
  have hN : N ≠ ⊥ := fun h => hv0 (by
    have : v ∈ N := Submodule.mem_span_singleton_self v
    rwa [h, LieSubmodule.mem_bot] at this)
  have hspan : Submodule.span k {v} = ⊤ := by
    have : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
    rwa [← LieSubmodule.toSubmodule_eq_top] at this
  rw [← finrank_top k M, ← hspan, finrank_span_singleton hv0]

/-- **Characteristic `0`.** On an irreducible (hence `1`-dimensional) representation, the generator
`Y` acts as `0`; thus the irreducibles are classified by the scalar `λ` with which `X` acts.

Since `M` is `1`-dimensional, each `𝔤`-element acts by a scalar (`toEnd` is a homothety), and these
homotheties commute. As `Y = ⁅X, Y⁆`, its action is the commutator `[ρX, ρY] = 0`. -/
theorem charZero_Y_acts_zero [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] (m : M) :
    ⁅Y k, m⁆ = 0 := by
  have d1 : Module.finrank k M = 1 := charZero_irreducible_finrank_one k M
  obtain ⟨cX, hcX, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 (LieModule.toEnd k (g k) M (X k))
  obtain ⟨cY, hcY, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 (LieModule.toEnd k (g k) M (Y k))
  have eX : ∀ w : M, ⁅X k, w⁆ = cX • w := fun w => by
    have := LinearMap.congr_fun hcX w; simpa [LieModule.toEnd_apply_apply] using this
  have eY : ∀ w : M, ⁅Y k, w⁆ = cY • w := fun w => by
    have := LinearMap.congr_fun hcY w; simpa [LieModule.toEnd_apply_apply] using this
  rw [← bracket_X_Y k, lie_lie, eY, eX, eX, eY, smul_smul, smul_smul, mul_comm cX cY, sub_self]

/-- **Characteristic `p`.** Lie's theorem fails: it is **not** the case that every irreducible
finite-dimensional representation of `𝔤` is `1`-dimensional.

TODO (issue #6132): construct the `p`-dimensional irreducible module (`X` diagonal with distinct
eigenvalues `0, …, p-1`, `Y` the cyclic shift) and instantiate the statement at it. -/
theorem lie_theorem_fails_charP [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
        [LieModule k (g k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M],
        Module.finrank k M = 1 :=
  sorry

end Etingof.Problem2_16_2
