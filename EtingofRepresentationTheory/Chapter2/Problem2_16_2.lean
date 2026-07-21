import Mathlib

/-!
# Problem 2.16.2: Irreducible representations of the 2-dimensional Lie algebra `[X, Y] = Y`

Let `𝔤` be the two-dimensional Lie algebra with basis `X, Y` and commutation relation
`[X, Y] = Y`. We realize it as the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units
`X = e₁₁` and `Y = e₁₂` (which satisfy `[e₁₁, e₁₂] = e₁₂`).

The problem asks to classify the irreducible finite-dimensional representations in characteristic
`0` and characteristic `p`, and whether Lie's theorem holds in characteristic `p`. We render the
book's answers as the statements:

* **Characteristic `0`** (algebraically closed, so Lie's theorem applies): every irreducible
  finite-dimensional representation is `1`-dimensional, and on such a representation `Y` acts as
  `0`. So the irreducibles are classified by the scalar `X ↦ λ ∈ k` (with `Y ↦ 0`).
* **Characteristic `p`**: Lie's theorem is false: there exist irreducible finite-dimensional
  representations of dimension `> 1` (in fact of dimension `p`).

The characteristic-`0` results (`bracket_X_Y`, `charZero_irreducible_finrank_one`,
`charZero_Y_acts_zero`) are established below, along with the supporting fact that `𝔤` is
solvable (`instIsSolvable`). The characteristic-`p` failure `lie_theorem_fails_charP` follows from
`section CharP`, which constructs the `p`-dimensional irreducible `𝔤`-module (`X` diagonal with
distinct eigenvalues `0, …, p-1`, `Y` the cyclic shift) and instantiates the statement at it.
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

/-! ## Characteristic 0: existence and classification

The necessary direction above shows every f.d. irreducible is `1`-dimensional with `Y ↦ 0`. Here
we supply the existence / realization half: for each scalar `μ ∈ k` we build the `1`-dimensional
`𝔤`-module `X ↦ μ, Y ↦ 0` (`oneDimModule μ`), prove it is irreducible, and prove that distinct
`μ` give non-isomorphic modules. Combined with `charZero_irreducible_finrank_one` /
`charZero_Y_acts_zero` (and `charZero_X_scalar` below), over an algebraically closed field of
characteristic `0` the f.d. irreducibles are classified exactly by the scalar `μ ∈ k`. -/

/-- The `(0,0)` entry of any bracket `⁅A, B⁆` of elements of `g k` vanishes: the bracket is a
scalar multiple of `e₁₂`, whose `(0,0)` entry is `0`. -/
private theorem bracket_coe_00 (A B : g k) :
    (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
  obtain ⟨a, b, hx⟩ := Submodule.mem_span_pair.mp (coe_mem_span k A)
  obtain ⟨c, d, hy⟩ := Submodule.mem_span_pair.mp (coe_mem_span k B)
  have hbr : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) = (a * d - b * c) • e12 k := by
    rw [LieSubalgebra.coe_bracket, ← hx, ← hy, bracket_expand]
  rw [hbr]
  simp [e12, Matrix.smul_apply]

/-- Underlying space of the `1`-dimensional representation `X ↦ μ, Y ↦ 0`: a copy of `k`. The
scalar `μ` is carried as a type index so that different `μ` give distinct module structures
(the `𝔤`-action below is opaque to typeclass resolution). -/
def oneDimModule (μ : k) : Type _ := k

instance (μ : k) : AddCommGroup (oneDimModule k μ) := inferInstanceAs (AddCommGroup k)
instance (μ : k) : Module k (oneDimModule k μ) := inferInstanceAs (Module k k)
instance (μ : k) : FiniteDimensional k (oneDimModule k μ) := inferInstanceAs (FiniteDimensional k k)
instance (μ : k) : Nontrivial (oneDimModule k μ) := inferInstanceAs (Nontrivial k)

/-- The `1`-dimensional representation `ρ_μ : 𝔤 → End k (oneDimModule μ)` with `X ↦ μ`, `Y ↦ 0`.
On a matrix `A ∈ 𝔤` it acts as `(A₀₀ · μ) • id`. The bracket relation is respected because the
`(0,0)` entry of every bracket in `𝔤` vanishes (`bracket_coe_00`) and `End k` of a
`1`-dimensional space is commutative. -/
noncomputable def oneDimRep (μ : k) : g k →ₗ⁅k⁆ Module.End k (oneDimModule k μ) where
  toFun A := ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
  map_add' A B := by
    show (((A + B : g k) : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
          + ((B : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
    rw [AddMemClass.coe_add, Matrix.add_apply, add_mul, add_smul]
  map_smul' c A := by
    show (((c • A : g k) : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = (RingHom.id k) c • ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
    rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul, mul_assoc]
  map_lie' := by
    intro A B
    have h00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := bracket_coe_00 k A B
    show ((↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = ⁅((↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id,
            ((↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id⁆
    rw [h00, zero_mul, zero_smul]
    simp only [smul_lie, lie_smul, lie_self, smul_zero]

@[simp] theorem oneDimRep_apply (μ : k) (A : g k) :
    oneDimRep k μ A = ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id := rfl

/-- The `𝔤`-module structure on `oneDimModule μ` induced by `oneDimRep μ`. -/
noncomputable instance (μ : k) : LieRingModule (g k) (oneDimModule k μ) :=
  LieRingModule.compLieHom (oneDimModule k μ) (oneDimRep k μ)

/-- The induced structure is a Lie module. -/
noncomputable instance (μ : k) : LieModule k (g k) (oneDimModule k μ) :=
  LieModule.compLieHom (oneDimModule k μ) (oneDimRep k μ)

/-- In `oneDimModule μ`, the generator `X` acts by the scalar `μ`. -/
theorem oneDim_lie_X (μ : k) (x : oneDimModule k μ) : (⁅X k, x⁆ : oneDimModule k μ) = μ • x := by
  have h : (⁅X k, x⁆ : oneDimModule k μ) = oneDimRep k μ (X k) x := rfl
  have hX : (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by simp [X]
  rw [h, oneDimRep_apply, hX, one_mul, LinearMap.smul_apply, LinearMap.id_apply]

/-- In `oneDimModule μ`, the generator `Y` acts by `0`. -/
theorem oneDim_lie_Y (μ : k) (x : oneDimModule k μ) : (⁅Y k, x⁆ : oneDimModule k μ) = 0 := by
  have h : (⁅Y k, x⁆ : oneDimModule k μ) = oneDimRep k μ (Y k) x := rfl
  have hY : (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by simp [Y]
  rw [h, oneDimRep_apply, hY, zero_mul, zero_smul, LinearMap.zero_apply]

/-- **Existence half of the char-`0` classification.** For each `μ ∈ k` the `1`-dimensional module
`oneDimModule μ` is an irreducible `𝔤`-module (any `1`-dimensional module is irreducible: its only
submodules are `⊥` and `⊤`). -/
theorem oneDim_irreducible (μ : k) : LieModule.IsIrreducible k (g k) (oneDimModule k μ) := by
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push_neg at hN
  obtain ⟨v, hvN, hv0⟩ := hN
  rw [← LieSubmodule.toSubmodule_eq_top]
  have hle : Submodule.span k {v} ≤ (N : Submodule k (oneDimModule k μ)) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvN
  have hspan : Submodule.span k {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hv0]
    exact (Module.finrank_self k).symm
  exact top_unique (hspan ▸ hle)

/-- **Distinctness.** Distinct scalars give non-isomorphic modules: an isomorphism of
`𝔤`-modules intertwines the `X`-action, and `X` acts by the (distinct) scalars `μ₁`, `μ₂`, forcing
`μ₁ = μ₂`. -/
theorem oneDim_not_iso {μ₁ μ₂ : k} (h : μ₁ ≠ μ₂) :
    ¬ Nonempty (oneDimModule k μ₁ ≃ₗ⁅k, g k⁆ oneDimModule k μ₂) := by
  rintro ⟨φ⟩
  apply h
  obtain ⟨m, hm⟩ := exists_ne (0 : oneDimModule k μ₁)
  have hφm : φ m ≠ 0 := fun hh => hm (φ.injective (by rw [hh, map_zero]))
  have hint : φ ⁅X k, m⁆ = ⁅X k, φ m⁆ := LieModuleHom.map_lie φ.toLieModuleHom (X k) m
  rw [oneDim_lie_X, oneDim_lie_X, map_smul] at hint
  have hz : (μ₁ - μ₂) • φ m = 0 := by rw [sub_smul, hint, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 hφm

/-- **Uniqueness of the classifying scalar.** Over an algebraically closed field of characteristic
`0`, every f.d. irreducible `𝔤`-module has a unique scalar `μ` by which `X` acts (and `Y` acts by
`0`, `charZero_Y_acts_zero`). Together with `oneDim_irreducible` (each `μ` is realized) and
`oneDim_not_iso` (distinct `μ` are non-isomorphic), this classifies the char-`0` irreducibles by
`μ ∈ k`. -/
theorem charZero_X_scalar [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] :
    ∃! μ : k, ∀ m : M, ⁅X k, m⁆ = μ • m := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (g k) M
  have d1 : Module.finrank k M = 1 := charZero_irreducible_finrank_one k M
  obtain ⟨cX, hcX, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 (LieModule.toEnd k (g k) M (X k))
  have eX : ∀ w : M, ⁅X k, w⁆ = cX • w := fun w => by
    have := LinearMap.congr_fun hcX w; simpa [LieModule.toEnd_apply_apply] using this
  refine ⟨cX, eX, fun μ hμ => ?_⟩
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hz : (cX - μ) • m = 0 := by rw [sub_smul, ← eX, hμ, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 hm

/-! ## Characteristic `p`: an irreducible representation of dimension `p`

We realize the book's counterexample to Lie's theorem in characteristic `p`. Let `M = k^{ℤ/p}`
(functions on `ℤ/p`). We let `X` act by the diagonal operator `diagOp` with the `p` distinct
eigenvalues `0, 1, …, p-1` (the image of `ℤ/p` in `k` under the prime-field embedding) and `Y`
act by the cyclic shift `shiftOp`. These satisfy `[diagOp, shiftOp] = shiftOp`, matching
`[X, Y] = Y`, so they define a representation `ρ : 𝔤 → End k M`. The resulting module is
irreducible of dimension `p > 1`, so Lie's theorem fails.

Because the counterexample module `k^{ℤ/p}` lives in the same universe as `k`, and the theorem
`lie_theorem_fails_charP` quantifies over `M : Type` (universe `0`), we specialize `k` to
`Type` here (the char-`0` results above keep `k : Type*`). -/

section CharP

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The prime-field embedding `ℤ/p ↪ k`, whose values `0, 1, …, p-1` are the `p` distinct
eigenvalues of the diagonal operator. -/
noncomputable def lam : ZMod p →+* k := ZMod.castHom (dvd_refl p) k

theorem lam_injective : Function.Injective (lam k p) := by
  show Function.Injective ⇑(ZMod.castHom (dvd_refl p) k)
  exact ZMod.castHom_injective k

/-- The diagonal operator on `k^{ℤ/p}`: `(diagOp v) i = (i : k) * v i`, with distinct
eigenvalues indexed by `ℤ/p`. This is the action of `X`. -/
noncomputable def diagOp : Module.End k (ZMod p → k) where
  toFun v i := lam k p i * v i
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The cyclic shift on `k^{ℤ/p}`: `(shiftOp v) i = v (i - 1)`. This is the action of `Y`. -/
noncomputable def shiftOp : Module.End k (ZMod p → k) :=
  LinearMap.funLeft k k (fun i => i - 1)

variable {k p}

@[simp] theorem diagOp_apply (v : ZMod p → k) (i : ZMod p) : diagOp k p v i = lam k p i * v i :=
  rfl

@[simp] theorem shiftOp_apply (v : ZMod p → k) (i : ZMod p) : shiftOp k p v i = v (i - 1) :=
  rfl

/-- The key relation `[diagOp, shiftOp] = shiftOp`, mirroring `[X, Y] = Y`. It holds because the
prime-field embedding is a ring homomorphism, so consecutive eigenvalues differ by `lam 1 = 1`. -/
theorem bracket_diag_shift : ⁅diagOp k p, shiftOp k p⁆ = shiftOp k p := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    diagOp_apply, shiftOp_apply]
  rw [← sub_mul, ← map_sub, sub_sub_cancel, map_one, one_mul]

variable (k p)

/-- Auxiliary Lie subalgebra of `2×2` matrices whose second row vanishes. It contains the
generators `e₁₁, e₁₂`, hence contains all of `g k`; this pins down the entries of elements of
`g k` used in the bracket computation for `ρ`. -/
def rowZero : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) where
  carrier := {A | A 1 0 = 0 ∧ A 1 1 = 0}
  add_mem' {a b} ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c a ha := ⟨by simp [ha.1], by simp [ha.2]⟩
  lie_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, ha.1, ha.2, hb.1, hb.2, zero_mul, mul_zero, add_zero, sub_zero, and_self]

/-- Every element of `g k` has vanishing second row. -/
theorem mem_g_row (A : g k) :
    (↑A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧ (↑A : Matrix (Fin 2) (Fin 2) k) 1 1 = 0 := by
  have hg : g k = LieSubalgebra.lieSpan k (Matrix (Fin 2) (Fin 2) k)
      {Matrix.single 0 0 1, Matrix.single 0 1 1} := rfl
  have hle : g k ≤ rowZero k := by
    rw [hg, LieSubalgebra.lieSpan_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by simp [Matrix.single_apply], by simp [Matrix.single_apply]⟩
    · exact ⟨by simp [Matrix.single_apply], by simp [Matrix.single_apply]⟩
  exact hle A.2

/-- The representation `ρ : 𝔤 → End k M` sending `X ↦ diagOp`, `Y ↦ shiftOp`, defined on a
matrix `A ∈ 𝔤` by `A ↦ A₀₀ • diagOp + A₀₁ • shiftOp`. -/
noncomputable def ρ : g k →ₗ⁅k⁆ Module.End k (ZMod p → k) where
  toFun A := (A : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
    + (A : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p
  map_add' A B := by
    simp only [AddMemClass.coe_add, Matrix.add_apply, add_smul]; abel
  map_smul' c A := by
    simp only [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
  map_lie' := by
    intro A B
    -- The second row of any element of `g k` vanishes; use it to compute the two relevant
    -- entries of the matrix commutator `⁅A, B⁆`.
    obtain ⟨hA0, hA1⟩ := mem_g_row k A
    obtain ⟨hB0, hB1⟩ := mem_g_row k B
    have hds : ⁅shiftOp k p, diagOp k p⁆ = -shiftOp k p := by
      rw [← lie_skew, bracket_diag_shift]
    have hbr : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k)
        = (↑A : Matrix (Fin 2) (Fin 2) k) * (↑B : Matrix (Fin 2) (Fin 2) k)
          - (↑B : Matrix (Fin 2) (Fin 2) k) * (↑A : Matrix (Fin 2) (Fin 2) k) := by
      rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    have e00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA0, hB0, mul_zero,
        add_zero]
      ring
    have e01 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 =
        (↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑B : Matrix (Fin 2) (Fin 2) k) 0 1
          - (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA1, hB1, mul_zero,
        add_zero]
    show (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
        + (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p
      = ⁅(↑A : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
          + (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p,
        (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
          + (↑B : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p⁆
    rw [e00, e01]
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero, zero_add,
      bracket_diag_shift, hds, smul_neg, zero_smul]
    module

/-- Coercion of the generator `X = e₁₁` to the underlying matrix. -/
theorem coe_X : (↑(X k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 0 1 := rfl

/-- Coercion of the generator `Y = e₁₂` to the underlying matrix. -/
theorem coe_Y : (↑(Y k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 1 1 := rfl

/-- Under `ρ`, the generator `X` acts as the diagonal operator. -/
@[simp] theorem ρ_X : ρ k p (X k) = diagOp k p := by
  have h0 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    simp [Matrix.single_apply]
  show (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
      + (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p = diagOp k p
  rw [coe_X, h0, h1, one_smul, zero_smul, add_zero]

/-- Under `ρ`, the generator `Y` acts as the cyclic shift. -/
@[simp] theorem ρ_Y : ρ k p (Y k) = shiftOp k p := by
  have h0 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
    simp [Matrix.single_apply]
  show (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
      + (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p = shiftOp k p
  rw [coe_Y, h0, h1, zero_smul, one_smul, zero_add]

/-- The `𝔤`-module structure on `k^{ℤ/p}` induced by `ρ`. -/
noncomputable instance repModule : LieRingModule (g k) (ZMod p → k) :=
  LieRingModule.compLieHom _ (ρ k p)

/-- The induced module is a Lie module. -/
noncomputable instance repLieModule : LieModule k (g k) (ZMod p → k) :=
  LieModule.compLieHom _ (ρ k p)

/-- In the induced module, `X` acts as the diagonal operator. -/
theorem lie_X_eq_diag (v : ZMod p → k) : (⁅X k, v⁆ : ZMod p → k) = diagOp k p v := by
  have h : (⁅X k, v⁆ : ZMod p → k) = ρ k p (X k) v := rfl
  rw [h, ρ_X]

/-- In the induced module, `Y` acts as the cyclic shift. -/
theorem lie_Y_eq_shift (v : ZMod p → k) : (⁅Y k, v⁆ : ZMod p → k) = shiftOp k p v := by
  have h : (⁅Y k, v⁆ : ZMod p → k) = ρ k p (Y k) v := rfl
  rw [h, ρ_Y]

/-- The cyclic shift permutes the standard basis: `shiftOp (eⱼ) = eⱼ₊₁`. -/
theorem shift_single (j : ZMod p) (c : k) :
    shiftOp k p (Pi.single j c) = Pi.single (j + 1) c := by
  funext m
  rw [shiftOp_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  simp [sub_eq_iff_eq_add]

variable {k p}

open scoped Classical in
/-- The support (as a `Finset`) of a vector in `k^{ℤ/p}`. -/
noncomputable def vsupp (v : ZMod p → k) : Finset (ZMod p) :=
  Finset.univ.filter fun i => v i ≠ 0

theorem mem_vsupp {v : ZMod p → k} {i : ZMod p} : i ∈ vsupp v ↔ v i ≠ 0 := by
  simp [vsupp]

variable (k p)

/-- **The counterexample module is irreducible.** A nonzero `𝔤`-submodule `N` of `k^{ℤ/p}` is all
of `k^{ℤ/p}`: pick a nonzero `v ∈ N` of minimal support; the diagonal action forces the support
to be a single point (else `diagOp v - λⱼ v ∈ N` has strictly smaller support), so a standard
basis vector lies in `N`, and the shift action (a `p`-cycle) sweeps out all of them. -/
theorem repModule_irreducible : LieModule.IsIrreducible k (g k) (ZMod p → k) := by
  classical
  haveI : Nontrivial (ZMod p → k) := inferInstance
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  -- `N` is closed under the diagonal and shift operators.
  have hdiag : ∀ v, v ∈ N → diagOp k p v ∈ N := fun v hv => by
    rw [← lie_X_eq_diag]; exact N.lie_mem hv
  have hshift : ∀ v, v ∈ N → shiftOp k p v ∈ N := fun v hv => by
    rw [← lie_Y_eq_shift]; exact N.lie_mem hv
  -- From one standard basis vector, the shift `p`-cycle produces all of them.
  have horbit : ∀ i₀ : ZMod p, Pi.single i₀ (1 : k) ∈ N → ∀ m, Pi.single m (1 : k) ∈ N := by
    intro i₀ hbase m
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = i₀ + t :=
      ⟨(m - i₀).val, by rw [ZMod.natCast_zmod_val]; abel⟩
    induction t with
    | zero => simpa using hbase
    | succ n ih =>
      have h2 := hshift _ ih
      rw [shift_single] at h2
      rw [Nat.cast_succ, ← add_assoc]
      exact h2
  -- All standard basis vectors in `N` forces `N = ⊤`.
  have htop : (∀ m : ZMod p, Pi.single m (1 : k) ∈ N) → N = ⊤ := by
    intro hall
    rw [← LieSubmodule.toSubmodule_eq_top, Submodule.eq_top_iff']
    intro x
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun m _ => ?_
    have hsingle : Pi.single m (x m) = x m • Pi.single m (1 : k) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [hsingle]
    exact Submodule.smul_mem _ _ (hall m)
  -- Extract a nonzero element of `N`.
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push_neg at hN
  obtain ⟨w, hwN, hw0⟩ := hN
  -- Strong induction on the size of the support.
  suffices H : ∀ (n : ℕ) (v : ZMod p → k), v ∈ N → v ≠ 0 → (vsupp v).card = n → N = ⊤ from
    H _ w hwN hw0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro v hvN hv0 hcard
    have hne : (vsupp v).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      exact ⟨i, mem_vsupp.mpr hi⟩
    by_cases hone : (vsupp v).card = 1
    · -- Support is a single point: a basis vector lies in `N`, so `N = ⊤`.
      obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hone
      have hvi₀ : v i₀ ≠ 0 := mem_vsupp.mp (hi₀ ▸ Finset.mem_singleton_self i₀)
      have hzero : ∀ m, m ≠ i₀ → v m = 0 := by
        intro m hm
        by_contra hvm
        have : m ∈ vsupp v := mem_vsupp.mpr hvm
        rw [hi₀, Finset.mem_singleton] at this
        exact hm this
      have hbase : Pi.single i₀ (1 : k) ∈ N := by
        have hsm : (v i₀)⁻¹ • v ∈ N := N.smul_mem _ hvN
        have hval : (v i₀)⁻¹ • v = Pi.single i₀ (1 : k) := by
          funext m
          rw [Pi.smul_apply, smul_eq_mul]
          by_cases hm : m = i₀
          · subst hm; rw [Pi.single_eq_same, inv_mul_cancel₀ hvi₀]
          · rw [Pi.single_eq_of_ne hm, hzero m hm, mul_zero]
        rwa [hval] at hsm
      exact htop (horbit i₀ hbase)
    · -- Support has at least two points: subtract an eigenvalue to shrink it, then recurse.
      have h2 : 1 < (vsupp v).card := by
        have h1 := Finset.card_pos.mpr hne; omega
      obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp h2
      set w' := diagOp k p v - lam k p j • v with hw'def
      have hw'N : w' ∈ N := sub_mem (hdiag v hvN) (N.smul_mem _ hvN)
      have hw'coord : ∀ m, w' m = (lam k p m - lam k p j) * v m := fun m => by
        simp only [hw'def, Pi.sub_apply, diagOp_apply, Pi.smul_apply, smul_eq_mul]; ring
      have hlamij : lam k p i ≠ lam k p j := fun heq => hij (lam_injective k p heq)
      have hw'i : w' i ≠ 0 := by
        rw [hw'coord]
        exact mul_ne_zero (sub_ne_zero.mpr hlamij) (mem_vsupp.mp hi)
      have hw'0 : w' ≠ 0 := fun heq => hw'i (congrFun heq i)
      have hsub : vsupp w' ⊆ vsupp v := by
        intro m hm
        rw [mem_vsupp] at hm ⊢
        intro hvm
        exact hm (by rw [hw'coord, hvm, mul_zero])
      have hjnotin : j ∉ vsupp w' := by
        rw [mem_vsupp, not_not, hw'coord, sub_self, zero_mul]
      have hss : vsupp w' ⊂ vsupp v :=
        (Finset.ssubset_iff_of_subset hsub).mpr ⟨j, hj, hjnotin⟩
      have hlt : (vsupp w').card < n := hcard ▸ Finset.card_lt_card hss
      exact IH _ hlt w' hw'N hw'0 rfl

/-- **Characteristic `p`.** Lie's theorem fails: it is not the case that every irreducible
finite-dimensional representation of `𝔤` is `1`-dimensional. The `p`-dimensional module `k^{ℤ/p}`
built above is an explicit irreducible counterexample.

The statement quantifies over `M : Type` (universe `0`), and the witness `k^{ℤ/p}` lives in `k`'s
universe, so `k` is specialized to `Type` for this result. -/
theorem lie_theorem_fails_charP (k : Type) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
        [LieModule k (g k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M],
        Module.finrank k M = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  haveI := repModule_irreducible k p
  intro h
  have hfr : Module.finrank k (ZMod p → k) = 1 := h (ZMod p → k)
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card p] at hfr
  exact ((Fact.out : p.Prime).one_lt).ne' hfr

end CharP

end Etingof.Problem2_16_2
