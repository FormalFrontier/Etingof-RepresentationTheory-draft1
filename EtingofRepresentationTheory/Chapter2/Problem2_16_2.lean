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

/-! ## Coordinates on `𝔤` and the resulting module calculus

Every `Z ∈ 𝔤` is `Z₀₀ · X + Z₀₁ · Y`. Consequently the action of an arbitrary element of `𝔤` on a
module is determined by the actions of `X` and `Y`, and a subspace invariant under those two
actions is a `𝔤`-submodule. Both facts are used throughout the classification below. -/

/-- The coordinates of `Z ∈ 𝔤` in the basis `X, Y` are the matrix entries `Z₀₀` and `Z₀₁`. -/
theorem eq_smul_X_add_smul_Y (Z : g k) :
    Z = (Z : Matrix (Fin 2) (Fin 2) k) 0 0 • X k
      + (Z : Matrix (Fin 2) (Fin 2) k) 0 1 • Y k := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (coe_mem_span k Z)
  have h00 : (Z : Matrix (Fin 2) (Fin 2) k) 0 0 = a := by
    rw [← hab]; simp [e11, e12, Matrix.single_apply]
  have h01 : (Z : Matrix (Fin 2) (Fin 2) k) 0 1 = b := by
    rw [← hab]; simp [e11, e12, Matrix.single_apply]
  rw [h00, h01]
  apply Subtype.ext
  rw [AddMemClass.coe_add, SetLike.val_smul, SetLike.val_smul]
  exact hab.symm

/-- The action of an arbitrary `Z ∈ 𝔤` on a module is the corresponding combination of the actions
of the generators `X` and `Y`. -/
theorem lie_eq_smul_lie_X_add_smul_lie_Y (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (g k) M] [LieModule k (g k) M] (Z : g k) (m : M) :
    ⁅Z, m⁆ = (Z : Matrix (Fin 2) (Fin 2) k) 0 0 • ⁅X k, m⁆
      + (Z : Matrix (Fin 2) (Fin 2) k) 0 1 • ⁅Y k, m⁆ := by
  conv_lhs => rw [eq_smul_X_add_smul_Y k Z]
  rw [add_lie, smul_lie, smul_lie]

/-- A subspace invariant under the actions of `X` and `Y` is a `𝔤`-submodule. -/
def ofInvariantXY (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
    [LieModule k (g k) M] (N : Submodule k M)
    (hX : ∀ m ∈ N, ⁅X k, m⁆ ∈ N) (hY : ∀ m ∈ N, ⁅Y k, m⁆ ∈ N) : LieSubmodule k (g k) M where
  __ := N
  lie_mem {Z m} hm := by
    have hm' : m ∈ N := hm
    rw [lie_eq_smul_lie_X_add_smul_lie_Y k M Z m]
    exact N.add_mem (N.smul_mem _ (hX m hm')) (N.smul_mem _ (hY m hm'))

@[simp] theorem ofInvariantXY_toSubmodule (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (g k) M] [LieModule k (g k) M] (N : Submodule k M)
    (hX : ∀ m ∈ N, ⁅X k, m⁆ ∈ N) (hY : ∀ m ∈ N, ⁅Y k, m⁆ ∈ N) :
    (ofInvariantXY k M N hX hY : Submodule k M) = N := rfl

/-- An irreducible module is spanned by any invariant subspace containing a nonzero vector. -/
theorem eq_top_of_invariant_of_ne_zero (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (g k) M] [LieModule k (g k) M] [LieModule.IsIrreducible k (g k) M]
    (N : Submodule k M) (hX : ∀ m ∈ N, ⁅X k, m⁆ ∈ N) (hY : ∀ m ∈ N, ⁅Y k, m⁆ ∈ N)
    {m₀ : M} (hm₀N : m₀ ∈ N) (hm₀ : m₀ ≠ 0) : N = ⊤ := by
  have hne : ofInvariantXY k M N hX hY ≠ ⊥ := fun h => hm₀ (by
    have : m₀ ∈ ofInvariantXY k M N hX hY := hm₀N
    rwa [h, LieSubmodule.mem_bot] at this)
  have := (IsSimpleOrder.eq_bot_or_eq_top (ofInvariantXY k M N hX hY)).resolve_left hne
  rwa [← LieSubmodule.toSubmodule_eq_top, ofInvariantXY_toSubmodule] at this

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

/-! ## Realizing a one-dimensional module inside the named family

The next two results turn the scalar data of a one-dimensional module into an isomorphism with a
named member of the family `oneDimModule`. They are characteristic-free, and serve both the
characteristic-`0` classification and the `Y`-acts-by-zero branch of the characteristic-`p` one. -/

/-- The identification of the carrier of `oneDimModule μ` with `k`. -/
def oneDimEquivSelf (μ : k) : k ≃ₗ[k] oneDimModule k μ where
  toFun c := c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := c
  left_inv _ := rfl
  right_inv _ := rfl

/-- The action of an arbitrary `Z ∈ 𝔤` on `oneDimModule μ`, in closed form. -/
theorem oneDim_lie (μ : k) (Z : g k) (x : oneDimModule k μ) :
    (⁅Z, x⁆ : oneDimModule k μ) = ((Z : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • x := by
  have h : (⁅Z, x⁆ : oneDimModule k μ) = oneDimRep k μ Z x := rfl
  rw [h, oneDimRep_apply, LinearMap.smul_apply, LinearMap.id_apply]

/-- **Realization.** A one-dimensional module on which `X` acts by the scalar `μ` and `Y` acts by
`0` is isomorphic to `oneDimModule μ`. -/
theorem nonempty_equiv_oneDim (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
    [LieModule k (g k) M] {μ : k} (hX : ∀ m : M, ⁅X k, m⁆ = μ • m)
    (hY : ∀ m : M, ⁅Y k, m⁆ = 0) (hdim : Module.finrank k M = 1) :
    Nonempty (M ≃ₗ⁅k, g k⁆ oneDimModule k μ) := by
  have hlie : ∀ (Z : g k) (m : M),
      ⁅Z, m⁆ = ((Z : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • m := fun Z m => by
    rw [lie_eq_smul_lie_X_add_smul_lie_Y k M Z m, hX, hY, smul_zero, add_zero, smul_smul]
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := k) (by rw [hdim]; norm_num)
  haveI : FiniteDimensional k M := Module.finite_of_finrank_pos (R := k) (by rw [hdim]; norm_num)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hinj : Function.Injective (LinearMap.toSpanSingleton k M m₀) := by
    intro c d hcd
    have h0 : (c - d) • m₀ = 0 := by
      rw [sub_smul, ← LinearMap.toSpanSingleton_apply, ← LinearMap.toSpanSingleton_apply, hcd,
        sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hm₀
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k M m₀) := by
    have hspan : Submodule.span k {m₀} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hm₀, hdim]
    intro m
    have hm : m ∈ Submodule.span k {m₀} := hspan ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, LinearMap.toSpanSingleton_apply k M m₀ c⟩
  let e : M ≃ₗ[k] oneDimModule k μ :=
    (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm.trans (oneDimEquivSelf k μ)
  refine ⟨{ e with map_lie' := ?_ }⟩
  intro Z m
  show e ⁅Z, m⁆ = ⁅Z, e m⁆
  rw [hlie, map_smul, oneDim_lie]

/-- **The characteristic-`0` classification.** Over an algebraically closed field of characteristic
`0`, every finite-dimensional irreducible `𝔤`-module is isomorphic to exactly one member
`oneDimModule μ` of the named one-dimensional family. Together with `oneDim_irreducible` (every
member is irreducible) this is the existence-and-uniqueness statement asked for by the problem. -/
theorem charZero_exists_unique_iso_oneDim [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] :
    ∃! μ : k, Nonempty (M ≃ₗ⁅k, g k⁆ oneDimModule k μ) := by
  obtain ⟨μ, hμ, -⟩ := charZero_X_scalar k M
  obtain ⟨φ⟩ := nonempty_equiv_oneDim k M hμ (charZero_Y_acts_zero k M)
    (charZero_irreducible_finrank_one k M)
  refine ⟨μ, ⟨φ⟩, ?_⟩
  rintro ν ⟨ψ⟩
  by_contra hne
  exact oneDim_not_iso k (Ne.symm hne) ⟨φ.symm.trans ψ⟩

/-! ## Characteristic `p`: the family of `p`-dimensional irreducibles

Over an algebraically closed field of characteristic `p` the algebra `𝔤` has, besides the
one-dimensional modules `oneDimModule μ`, a family of `p`-dimensional irreducible modules.

For `γ ∈ kˣ` and `a ∈ k` let `V(γ, a) = k^{ℤ/p}` with `X` acting by the diagonal operator
`famDiag a` of eigenvalues `a + i`, `i ∈ ℤ/p`, and `Y` acting by `γ` times the cyclic shift
`famShift γ`. The relation `[famDiag a, famShift γ] = famShift γ` holds because consecutive
eigenvalues of `famDiag a` differ by `1`, so these operators define a representation of `𝔤`. The
module is irreducible: the diagonal action separates the coordinates and the shift, being
invertible, sweeps one coordinate line onto all the others.

Taking `γ = 1` and `a = 0` recovers the book's counterexample to Lie's theorem in characteristic
`p`, recorded at the end of the section. -/

section CharP

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

instance instNeZeroOfFactPrime : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The prime-field embedding `ℤ/p ↪ k`, whose values `0, 1, …, p-1` are the `p` distinct
eigenvalue offsets of the diagonal operator. -/
noncomputable def lam : ZMod p →+* k := ZMod.castHom (dvd_refl p) k

theorem lam_injective : Function.Injective (lam k p) := by
  show Function.Injective ⇑(ZMod.castHom (dvd_refl p) k)
  exact ZMod.castHom_injective k

variable {k p}

@[simp] theorem lam_natCast (n : ℕ) : lam k p (n : ZMod p) = (n : k) := map_natCast _ n

theorem lam_val (i : ZMod p) : lam k p i = (i.val : k) := by
  have h : ((i.val : ℕ) : ZMod p) = i := ZMod.natCast_zmod_val i
  calc lam k p i = lam k p ((i.val : ℕ) : ZMod p) := by rw [h]
    _ = (i.val : k) := lam_natCast i.val

variable (k p)

/-- The diagonal operator on `k^{ℤ/p}` with eigenvalues `a + i`. This is the action of `X` on
`V(γ, a)`; its `p` eigenvalues are distinct because the prime field embeds in `k`. -/
noncomputable def famDiag (a : k) : Module.End k (ZMod p → k) where
  toFun v i := (a + lam k p i) * v i
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The cyclic shift on `k^{ℤ/p}`: `(shiftOp v) i = v (i - 1)`. -/
noncomputable def shiftOp : Module.End k (ZMod p → k) :=
  LinearMap.funLeft k k (fun i => i - 1)

/-- `γ` times the cyclic shift: the action of `Y` on `V(γ, a)`. -/
noncomputable def famShift (γ : kˣ) : Module.End k (ZMod p → k) := (γ : k) • shiftOp k p

variable {k p}

@[simp] theorem famDiag_apply (a : k) (v : ZMod p → k) (i : ZMod p) :
    famDiag k p a v i = (a + lam k p i) * v i := rfl

@[simp] theorem shiftOp_apply (v : ZMod p → k) (i : ZMod p) : shiftOp k p v i = v (i - 1) := rfl

@[simp] theorem famShift_apply (γ : kˣ) (v : ZMod p → k) (i : ZMod p) :
    famShift k p γ v i = (γ : k) * v (i - 1) := rfl

/-- The cyclic shift moves a coordinate line one step forward. -/
theorem shift_single (j : ZMod p) (c : k) :
    shiftOp k p (Pi.single j c) = Pi.single (j + 1) c := by
  funext m
  rw [shiftOp_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  simp [sub_eq_iff_eq_add]

/-- The scaled shift moves a coordinate line one step forward and rescales it by `γ`. -/
theorem famShift_single (γ : kˣ) (j : ZMod p) (c : k) :
    famShift k p γ (Pi.single j c) = Pi.single (j + 1) ((γ : k) * c) := by
  funext m
  rw [famShift_apply, Pi.single_apply, Pi.single_apply]
  by_cases hm : m = j + 1
  · have h1 : m - 1 = j := by rw [hm]; ring
    rw [if_pos h1, if_pos hm]
  · have h1 : ¬ (m - 1 = j) := fun h => hm (by rw [← h]; ring)
    rw [if_neg h1, if_neg hm, mul_zero]

/-- The key relation `[famDiag a, famShift γ] = famShift γ`, mirroring `[X, Y] = Y`. It holds
because consecutive eigenvalues of the diagonal operator differ by `lam 1 = 1`; the offset `a`
cancels. -/
theorem bracket_famDiag_famShift (a : k) (γ : kˣ) :
    ⁅famDiag k p a, famShift k p γ⁆ = famShift k p γ := by
  refine LinearMap.ext fun v => funext fun i => ?_
  have h : lam k p i - lam k p (i - 1) = 1 := by rw [← map_sub, sub_sub_cancel, map_one]
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    famDiag_apply, famShift_apply]
  linear_combination ((γ : k) * v (i - 1)) * h

variable (k p)

/-- Auxiliary Lie subalgebra of `2×2` matrices whose second row vanishes. It contains the
generators `e₁₁, e₁₂`, hence all of `g k`; this pins down the entries of elements of `g k` used in
the bracket computation for `famRep`. -/
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

/-- The representation `𝔤 → End k (k^{ℤ/p})` underlying `V(γ, a)`: it sends `X ↦ famDiag a` and
`Y ↦ famShift γ`, so a matrix `A ∈ 𝔤` acts as `A₀₀ • famDiag a + A₀₁ • famShift γ`. -/
noncomputable def famRep (γ : kˣ) (a : k) : g k →ₗ⁅k⁆ Module.End k (ZMod p → k) where
  toFun A := (A : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
    + (A : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ
  map_add' A B := by
    simp only [AddMemClass.coe_add, Matrix.add_apply, add_smul]; abel
  map_smul' c A := by
    simp only [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
  map_lie' := by
    intro A B
    obtain ⟨hA0, hA1⟩ := mem_g_row k A
    obtain ⟨hB0, hB1⟩ := mem_g_row k B
    have hds : ⁅famShift k p γ, famDiag k p a⁆ = -famShift k p γ := by
      rw [← lie_skew, bracket_famDiag_famShift]
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
    change (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
        + (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ
      = ⁅(↑A : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
          + (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ,
        (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
          + (↑B : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ⁆
    rw [e00, e01]
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero, zero_add,
      bracket_famDiag_famShift, hds, smul_neg, zero_smul]
    module

/-- Coercion of the generator `X = e₁₁` to the underlying matrix. -/
theorem coe_X : (↑(X k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 0 1 := rfl

/-- Coercion of the generator `Y = e₁₂` to the underlying matrix. -/
theorem coe_Y : (↑(Y k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 1 1 := rfl

variable {k p}

/-- Under `famRep γ a`, the generator `X` acts as the diagonal operator. -/
@[simp] theorem famRep_X (γ : kˣ) (a : k) : famRep k p γ a (X k) = famDiag k p a := by
  have h0 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    simp [Matrix.single_apply]
  change (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
      + (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ = famDiag k p a
  rw [coe_X, h0, h1, one_smul, zero_smul, add_zero]

/-- Under `famRep γ a`, the generator `Y` acts as the scaled cyclic shift. -/
@[simp] theorem famRep_Y (γ : kˣ) (a : k) : famRep k p γ a (Y k) = famShift k p γ := by
  have h0 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
    simp [Matrix.single_apply]
  change (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
      + (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ = famShift k p γ
  rw [coe_Y, h0, h1, zero_smul, one_smul, zero_add]

variable (k p)

/-! ### The carrier `V(γ, a)` -/

/-- The carrier of the `p`-dimensional module `V(γ, a)`: a type synonym for `k^{ℤ/p}`.

The parameters `γ` and `a` are phantom. They do not change the underlying space, but they separate
the `𝔤`-module structures of `V(γ, a)` and `V(γ', a')`, which would otherwise be competing
instances on one and the same type. -/
def Fam (_γ : kˣ) (_a : k) : Type _ := ZMod p → k

instance (γ : kˣ) (a : k) : AddCommGroup (Fam k p γ a) :=
  inferInstanceAs (AddCommGroup (ZMod p → k))

instance (γ : kˣ) (a : k) : Module k (Fam k p γ a) := inferInstanceAs (Module k (ZMod p → k))

instance (γ : kˣ) (a : k) : FiniteDimensional k (Fam k p γ a) :=
  inferInstanceAs (FiniteDimensional k (ZMod p → k))

instance (γ : kˣ) (a : k) : Nontrivial (Fam k p γ a) := inferInstanceAs (Nontrivial (ZMod p → k))

/-- `famRep γ a` read as landing in the endomorphisms of the carrier `V(γ, a)`. Retyping it this
way (the two endomorphism algebras have the same underlying space) is what makes the action of the
generators reduce definitionally on `V(γ, a)`. -/
noncomputable def famRep' (γ : kˣ) (a : k) : g k →ₗ⁅k⁆ Module.End k (Fam k p γ a) :=
  famRep k p γ a

variable {k p}

theorem famRep'_X (γ : kˣ) (a : k) : famRep' k p γ a (X k) = famDiag k p a := famRep_X γ a

theorem famRep'_Y (γ : kˣ) (a : k) : famRep' k p γ a (Y k) = famShift k p γ := famRep_Y γ a

variable (k p)

/-- The `𝔤`-module structure on `V(γ, a)` induced by `famRep γ a`. -/
noncomputable instance famLieRingModule (γ : kˣ) (a : k) : LieRingModule (g k) (Fam k p γ a) :=
  LieRingModule.compLieHom (Fam k p γ a) (famRep' k p γ a)

/-- The induced structure is a Lie module. -/
noncomputable instance famLieModule (γ : kˣ) (a : k) : LieModule k (g k) (Fam k p γ a) :=
  LieModule.compLieHom (Fam k p γ a) (famRep' k p γ a)

variable {k p}

/-- In `V(γ, a)` the generator `X` acts by the diagonal operator. -/
theorem fam_lie_X (γ : kˣ) (a : k) (v : Fam k p γ a) :
    (⁅X k, v⁆ : Fam k p γ a) = famDiag k p a v := by
  have h : (⁅X k, v⁆ : Fam k p γ a) = famRep' k p γ a (X k) v := rfl
  rw [h, famRep'_X]
  exact rfl

/-- In `V(γ, a)` the generator `Y` acts by the scaled cyclic shift. -/
theorem fam_lie_Y (γ : kˣ) (a : k) (v : Fam k p γ a) :
    (⁅Y k, v⁆ : Fam k p γ a) = famShift k p γ v := by
  have h : (⁅Y k, v⁆ : Fam k p γ a) = famRep' k p γ a (Y k) v := rfl
  rw [h, famRep'_Y]
  exact rfl

omit [CharP k p] in
/-- `V(γ, a)` has dimension `p`. -/
theorem fam_finrank (γ : kˣ) (a : k) : Module.finrank k (Fam k p γ a) = p := by
  have h : Module.finrank k (Fam k p γ a) = Module.finrank k (ZMod p → k) := rfl
  rw [h, Module.finrank_fintype_fun_eq_card, ZMod.card p]

/-! ### Irreducibility -/

open scoped Classical in
/-- The support (as a `Finset`) of a vector in `k^{ℤ/p}`. -/
noncomputable def vsupp (v : ZMod p → k) : Finset (ZMod p) :=
  Finset.univ.filter fun i => v i ≠ 0

theorem mem_vsupp {v : ZMod p → k} {i : ZMod p} : i ∈ vsupp v ↔ v i ≠ 0 := by
  simp [vsupp]

/-- Rescaling a coordinate line. -/
private theorem smul_single (m : ZMod p) (c d : k) :
    c • (Pi.single m d : ZMod p → k) = Pi.single m (c * d) := by
  funext x
  rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero]

/-- **The classifying subspace lemma.** A subspace of `k^{ℤ/p}` invariant under `famDiag a` and
`famShift γ` is `⊥` or everything.

Pick a nonzero `v` in the subspace of minimal support. The diagonal action forces the support to be
a single point (otherwise `famDiag a v - (a + j) v` lies in the subspace with strictly smaller
support), so a coordinate line lies in the subspace; the shift, being a `p`-cycle, then sweeps out
all the others. -/
theorem eq_bot_or_eq_top_of_invariant (γ : kˣ) (a : k) (N : Submodule k (ZMod p → k))
    (hdiag : ∀ v ∈ N, famDiag k p a v ∈ N) (hshift : ∀ v ∈ N, famShift k p γ v ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr ?_
  -- a nonzero coordinate line can be normalized
  have hone : ∀ (m : ZMod p) (c : k), c ≠ 0 → (Pi.single m c : ZMod p → k) ∈ N →
      (Pi.single m (1 : k) : ZMod p → k) ∈ N := by
    intro m c hc hmem
    have h := N.smul_mem c⁻¹ hmem
    rwa [smul_single, inv_mul_cancel₀ hc] at h
  -- the shift advances a coordinate line
  have hstep : ∀ i : ZMod p, (Pi.single i (1 : k) : ZMod p → k) ∈ N →
      (Pi.single (i + 1) (1 : k) : ZMod p → k) ∈ N := by
    intro i hi
    have h2 := hshift _ hi
    rw [famShift_single, mul_one] at h2
    exact hone _ _ (Units.ne_zero γ) h2
  -- hence one coordinate line gives all of them
  have horbit : ∀ i₀ : ZMod p, (Pi.single i₀ (1 : k) : ZMod p → k) ∈ N →
      ∀ m : ZMod p, (Pi.single m (1 : k) : ZMod p → k) ∈ N := by
    intro i₀ hbase m
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = i₀ + t :=
      ⟨(m - i₀).val, by rw [ZMod.natCast_zmod_val]; abel⟩
    induction t with
    | zero => simpa using hbase
    | succ n ih =>
      have h := hstep _ ih
      rw [Nat.cast_succ, ← add_assoc]
      exact h
  -- all coordinate lines give everything
  have htop : (∀ m : ZMod p, (Pi.single m (1 : k) : ZMod p → k) ∈ N) → N = ⊤ := by
    intro hall
    rw [Submodule.eq_top_iff']
    intro x
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun m _ => ?_
    have hsingle : (Pi.single m (x m) : ZMod p → k) = x m • (Pi.single m (1 : k) : ZMod p → k) := by
      rw [smul_single, mul_one]
    rw [hsingle]
    exact Submodule.smul_mem _ _ (hall m)
  obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  -- strong induction on the size of the support
  suffices H : ∀ (n : ℕ) (v : ZMod p → k), v ∈ N → v ≠ 0 → (vsupp v).card = n → N = ⊤ from
    H _ w hwN hw0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro v hvN hv0 hcard
    have hne : (vsupp v).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      exact ⟨i, mem_vsupp.mpr hi⟩
    by_cases hsingleton : (vsupp v).card = 1
    · obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hsingleton
      have hvi₀ : v i₀ ≠ 0 := mem_vsupp.mp (hi₀ ▸ Finset.mem_singleton_self i₀)
      have hzero : ∀ m, m ≠ i₀ → v m = 0 := by
        intro m hm
        by_contra hvm
        have hmem : m ∈ vsupp v := mem_vsupp.mpr hvm
        rw [hi₀, Finset.mem_singleton] at hmem
        exact hm hmem
      have hbase : (Pi.single i₀ (1 : k) : ZMod p → k) ∈ N := by
        refine hone i₀ (v i₀) hvi₀ ?_
        have hval : (Pi.single i₀ (v i₀) : ZMod p → k) = v := by
          funext m
          rw [Pi.single_apply]
          by_cases hm : m = i₀
          · rw [if_pos hm, hm]
          · rw [if_neg hm, hzero m hm]
        rwa [hval]
      exact htop (horbit i₀ hbase)
    · have h2 : 1 < (vsupp v).card := by
        have h1 := Finset.card_pos.mpr hne; omega
      obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp h2
      set w' := famDiag k p a v - (a + lam k p j) • v with hw'def
      have hw'N : w' ∈ N := sub_mem (hdiag v hvN) (N.smul_mem _ hvN)
      have hw'coord : ∀ m, w' m = (lam k p m - lam k p j) * v m := fun m => by
        simp only [hw'def, Pi.sub_apply, famDiag_apply, Pi.smul_apply, smul_eq_mul]; ring
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

/-- **Every member of the family is irreducible.** -/
theorem fam_irreducible (γ : kˣ) (a : k) : LieModule.IsIrreducible k (g k) (Fam k p γ a) := by
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  have hdiag : ∀ v ∈ (N : Submodule k (Fam k p γ a)), famDiag k p a v ∈ N := by
    intro v hv
    rw [← fam_lie_X γ a v]
    exact N.lie_mem hv
  have hshift : ∀ v ∈ (N : Submodule k (Fam k p γ a)), famShift k p γ v ∈ N := by
    intro v hv
    rw [← fam_lie_Y γ a v]
    exact N.lie_mem hv
  rcases eq_bot_or_eq_top_of_invariant γ a (N : Submodule k (Fam k p γ a)) hdiag hshift with h | h
  · exact absurd (by rwa [← LieSubmodule.toSubmodule_eq_bot]) hN
  · rwa [← LieSubmodule.toSubmodule_eq_top]

/-- **Characteristic `p`.** Lie's theorem fails: it is not the case that every irreducible
finite-dimensional representation of `𝔤` is `1`-dimensional. The `p`-dimensional module `V(1, 0)`
is an explicit irreducible counterexample.

The statement quantifies over `M : Type` (universe `0`), and the witness lives in `k`'s universe,
so `k` is specialized to `Type` here. -/
theorem lie_theorem_fails_charP (k : Type) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
        [LieModule k (g k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M],
        Module.finrank k M = 1 := by
  haveI := fam_irreducible (k := k) (p := p) 1 0
  intro h
  have hfr : Module.finrank k (Fam k p 1 0) = 1 := h (Fam k p 1 0)
  rw [fam_finrank] at hfr
  exact ((Fact.out : p.Prime).one_lt).ne' hfr

end CharP

end Etingof.Problem2_16_2
