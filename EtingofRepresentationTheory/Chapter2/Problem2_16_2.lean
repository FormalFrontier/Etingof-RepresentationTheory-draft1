import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal


/-!
# Problem 2.16.2: Irreducible representations of the 2-dimensional Lie algebra `[X, Y] = Y`

Let `𝔤` be the two-dimensional Lie algebra with basis `X, Y` and commutation relation
`[X, Y] = Y`. We realize it as the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units
`X = e₁₁` and `Y = e₁₂` (which satisfy `[e₁₁, e₁₂] = e₁₂`).

The problem asks to classify the irreducible finite-dimensional representations in characteristic
`0` and characteristic `p`, and whether Lie's theorem holds in characteristic `p`. Over an
algebraically closed field the answers are:

* **Characteristic `0`**: every irreducible finite-dimensional representation is `1`-dimensional
  with `Y` acting as `0`, so the irreducibles are the modules `oneDimModule μ` given by `X ↦ μ`,
  `Y ↦ 0`, and `μ ∈ k` is a complete invariant.
* **Characteristic `p`**: besides the same one-dimensional family there is a family of
  `p`-dimensional irreducibles `Fam γ a = V(γ, a)` on `k^{ℤ/p}`, with `X` acting diagonally by
  `a + i` and `Y` by `γ` times the cyclic shift. Every finite-dimensional irreducible is one of
  these, `V(γ, a) ≅ V(γ', a')` exactly when `γ = γ'` and `a - a'` lies in the prime field, and no
  one-dimensional module meets the `p`-dimensional family. In particular Lie's theorem fails.

Main statements:

* `bracket_X_Y`, `instIsSolvable` — the defining relation and solvability of `𝔤`.
* `charZero_irreducible_finrank_one`, `charZero_Y_acts_zero`, `charZero_X_scalar` — the
  characteristic-`0` structure of an irreducible.
* `charZero_exists_unique_iso_oneDim` — the characteristic-`0` classification.
* `fam_irreducible`, `fam_finrank` — the `p`-dimensional family and its irreducibility.
* `fam_nonempty_equiv_iff`, `oneDim_not_equiv_fam` — the isomorphism criterion and disjointness of
  the two families.
* `charP_exists_iso`, `charP_exists_unique_iso` — the characteristic-`p` classification.
* `lie_theorem_fails_charP` — the resulting failure of Lie's theorem.
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
    rw [← hab]; simp [e11, e12]
  have h01 : (Z : Matrix (Fin 2) (Fin 2) k) 0 1 = b := by
    rw [← hab]; simp [e11, e12]
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

/-- A subspace invariant under X and Y defines a Lie submodule. -/
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

/-- To build an isomorphism of `𝔤`-modules from a linear isomorphism it is enough to intertwine
the actions of the two generators. -/
def lieEquivOfIntertwines {M N : Type*} [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
    [LieModule k (g k) M] [AddCommGroup N] [Module k N] [LieRingModule (g k) N]
    [LieModule k (g k) N] (e : M ≃ₗ[k] N) (hX : ∀ m : M, e ⁅X k, m⁆ = ⁅X k, e m⁆)
    (hY : ∀ m : M, e ⁅Y k, m⁆ = ⁅Y k, e m⁆) : M ≃ₗ⁅k, g k⁆ N where
  __ := e
  map_lie' {Z m} := by
    change e ⁅Z, m⁆ = ⁅Z, e m⁆
    rw [lie_eq_smul_lie_X_add_smul_lie_Y k M Z m, map_add, map_smul, map_smul, hX, hY,
      lie_eq_smul_lie_X_add_smul_lie_Y k N Z (e m)]

/-- An isomorphism of `𝔤`-modules commutes with the iterated action of any element. -/
theorem lieEquiv_toEnd_pow {M N : Type*} [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
    [LieModule k (g k) M] [AddCommGroup N] [Module k N] [LieRingModule (g k) N]
    [LieModule k (g k) N] (φ : M ≃ₗ⁅k,g k⁆ N) (Z : g k) (n : ℕ) (m : M) :
    φ (((LieModule.toEnd k (g k) M Z) ^ n) m)
      = ((LieModule.toEnd k (g k) N Z) ^ n) (φ m) := by
  induction n generalizing m with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih,
      LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply]
    exact congrArg _ (LieModuleHom.map_lie φ.toLieModuleHom Z m)

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
def oneDimModule (_μ : k) : Type _ := k

instance (μ : k) : AddCommGroup (oneDimModule k μ) := inferInstanceAs (AddCommGroup k)
instance (μ : k) : Module k (oneDimModule k μ) := inferInstanceAs (Module k k)
/-- The one-dimensional model is finite-dimensional. -/
instance (μ : k) : FiniteDimensional k (oneDimModule k μ) := inferInstanceAs (FiniteDimensional k k)
/-- The one-dimensional model is nontrivial. -/
instance (μ : k) : Nontrivial (oneDimModule k μ) := inferInstanceAs (Nontrivial k)

/-- The `1`-dimensional representation `ρ_μ : 𝔤 → End k (oneDimModule μ)` with `X ↦ μ`, `Y ↦ 0`.
On a matrix `A ∈ 𝔤` it acts as `(A₀₀ · μ) • id`. The bracket relation is respected because the
`(0,0)` entry of every bracket in `𝔤` vanishes (`bracket_coe_00`) and `End k` of a
`1`-dimensional space is commutative. -/
noncomputable def oneDimRep (μ : k) : g k →ₗ⁅k⁆ Module.End k (oneDimModule k μ) where
  toFun A := ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
  map_add' A B := by
    change (((A + B : g k) : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
          + ((B : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
    rw [AddMemClass.coe_add, Matrix.add_apply, add_mul, add_smul]
  map_smul' c A := by
    change (((c • A : g k) : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = (RingHom.id k) c • ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
    rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul, mul_assoc]
  map_lie' := by
    intro A B
    have h00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := bracket_coe_00 k A B
    change ((↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = ⁅((↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id,
            ((↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id⁆
    rw [h00, zero_mul, zero_smul]
    simp only [smul_lie, lie_smul, lie_self, smul_zero]

/-- Evaluation formula for `oneDimRep`. -/
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
  push Not at hN
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
  change e ⁅Z, m⁆ = ⁅Z, e m⁆
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

/-- A prime characteristic is nonzero. -/
instance instNeZeroOfFactPrime : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- The prime-field embedding `ℤ/p ↪ k`, whose values `0, 1, …, p-1` are the `p` distinct
eigenvalue offsets of the diagonal operator. -/
noncomputable def lam : ZMod p →+* k := ZMod.castHom (dvd_refl p) k

/-- `lam` is injective. -/
theorem lam_injective : Function.Injective (lam k p) := by
  change Function.Injective ⇑(ZMod.castHom (dvd_refl p) k)
  exact ZMod.castHom_injective k

variable {k p}

/-- Structural formula for `lam_natCast`. -/
theorem lam_natCast (n : ℕ) : lam k p (n : ZMod p) = (n : k) := map_natCast _ n

/-- Structural formula for `lam_val`. -/
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

/-- Evaluation formula for `famDiag`. -/
@[simp] theorem famDiag_apply (a : k) (v : ZMod p → k) (i : ZMod p) :
    famDiag k p a v i = (a + lam k p i) * v i := rfl

omit [CharP k p] in
/-- Evaluation formula for `shiftOp`. -/
@[simp] theorem shiftOp_apply (v : ZMod p → k) (i : ZMod p) : shiftOp k p v i = v (i - 1) := rfl

omit [CharP k p] in
/-- Evaluation formula for `famShift`. -/
@[simp] theorem famShift_apply (γ : kˣ) (v : ZMod p → k) (i : ZMod p) :
    famShift k p γ v i = (γ : k) * v (i - 1) := rfl

omit [CharP k p] in
/-- The cyclic shift moves a coordinate line one step forward. -/
theorem shift_single (j : ZMod p) (c : k) :
    shiftOp k p (Pi.single j c) = Pi.single (j + 1) c := by
  funext m
  rw [shiftOp_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  simp [sub_eq_iff_eq_add]

omit [CharP k p] in
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
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
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
    -- The generic scalar-bracket lemmas do not match this `Module.End` instance reliably under
    -- `simp only`, so state them with the exact type used below.
    have smul_lie' : ∀ (c : k) (u v : Module.End k (ZMod p → k)),
        ⁅c • u, v⁆ = c • ⁅u, v⁆ := fun c u v => smul_lie c u v
    have lie_smul' : ∀ (c : k) (u v : Module.End k (ZMod p → k)),
        ⁅u, c • v⁆ = c • ⁅u, v⁆ := fun c u v => lie_smul c u v
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
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero, add_zero, zero_add,
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
    simp
  have h1 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    simp
  change (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 0 • famDiag k p a
      + (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 1 • famShift k p γ = famDiag k p a
  rw [coe_X, h0, h1, one_smul, zero_smul, add_zero]

/-- Under `famRep γ a`, the generator `Y` acts as the scaled cyclic shift. -/
@[simp] theorem famRep_Y (γ : kˣ) (a : k) : famRep k p γ a (Y k) = famShift k p γ := by
  have h0 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    simp
  have h1 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
    simp
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

/-- The characteristic-p family is finite-dimensional. -/
instance (γ : kˣ) (a : k) : FiniteDimensional k (Fam k p γ a) :=
  inferInstanceAs (FiniteDimensional k (ZMod p → k))

/-- The characteristic-p family is nontrivial. -/
instance (γ : kˣ) (a : k) : Nontrivial (Fam k p γ a) := inferInstanceAs (Nontrivial (ZMod p → k))

/-- `famRep γ a` read as landing in the endomorphisms of the carrier `V(γ, a)`. Retyping it this
way (the two endomorphism algebras have the same underlying space) is what makes the action of the
generators reduce definitionally on `V(γ, a)`. -/
noncomputable def famRep' (γ : kˣ) (a : k) : g k →ₗ⁅k⁆ Module.End k (Fam k p γ a) :=
  famRep k p γ a

variable {k p}

/-- Structural formula for `famRep'_X`. -/
theorem famRep'_X (γ : kˣ) (a : k) : famRep' k p γ a (X k) = famDiag k p a := famRep_X γ a

/-- Structural formula for `famRep'_Y`. -/
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

omit [CharP k p] in
/-- Structural formula for `mem_vsupp`. -/
theorem mem_vsupp {v : ZMod p → k} {i : ZMod p} : i ∈ vsupp v ↔ v i ≠ 0 := by
  simp [vsupp]

omit [Fact (Nat.Prime p)] [CharP k p] in
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


/-! ### The isomorphism criterion

Two invariants separate the members of the family. The `p`-th power of the `Y`-action is the scalar
`γᵖ`, which pins down `γ` because the Frobenius map is injective; and the eigenvalues of the
`X`-action are `a + i` for `i` in the prime field, which pins down `a` modulo the prime field.
Conversely, translating the index by `n` is an isomorphism `V(γ, a) ≅ V(γ, a + n)`. -/

omit [CharP k p] in
/-- Iterating the cyclic shift `n` times moves a coordinate `n` steps back. -/
theorem shiftOp_pow_apply (n : ℕ) : ∀ (v : ZMod p → k) (i : ZMod p),
    ((shiftOp k p ^ n) v) i = v (i - n) := by
  induction n with
  | zero => intro v i; simp
  | succ m ih =>
    intro v i
    rw [pow_succ, Module.End.mul_apply, ih, shiftOp_apply]
    congr 1
    push_cast
    ring

omit [CharP k p] in
/-- The cyclic shift has order dividing `p`. -/
theorem shiftOp_pow_char : shiftOp k p ^ p = 1 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [shiftOp_pow_apply, ZMod.natCast_self, sub_zero, Module.End.one_apply]

omit [CharP k p] in
/-- The `p`-th power of the `Y`-operator of `V(γ, a)` is the scalar `γᵖ`. -/
theorem famShift_pow_char (γ : kˣ) :
    famShift k p γ ^ p = ((γ : k) ^ p) • (1 : Module.End k (ZMod p → k)) := by
  rw [famShift, smul_pow, shiftOp_pow_char]

/-- The `n`-fold action of `Y` on `V(γ, a)` is the `n`-th power of the scaled shift. -/
theorem toEnd_Y_pow_apply (γ : kˣ) (a : k) (n : ℕ) : ∀ v : Fam k p γ a,
    ((LieModule.toEnd k (g k) (Fam k p γ a) (Y k)) ^ n) v = (famShift k p γ ^ n) v := by
  induction n with
  | zero => intro v; simp
  | succ m ih =>
    intro v
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
      LieModule.toEnd_apply_apply, fam_lie_Y]
    exact ih _

/-- **The invariant pinning down `γ`.** The `p`-fold action of `Y` on `V(γ, a)` is the scalar
`γᵖ`. -/
theorem toEnd_Y_pow_char (γ : kˣ) (a : k) (v : Fam k p γ a) :
    ((LieModule.toEnd k (g k) (Fam k p γ a) (Y k)) ^ p) v = ((γ : k) ^ p) • v := by
  have hpow : (famShift k p γ ^ p) v =
      (((γ : k) ^ p) • (1 : Module.End k (ZMod p → k))) v :=
    congrArg (fun f : Module.End k (ZMod p → k) => f v) (famShift_pow_char γ)
  exact (toEnd_Y_pow_apply γ a p v).trans (hpow.trans (by rfl))

/-- The first standard basis vector of `V(γ, a)`. -/
def famUnit (γ : kˣ) (a : k) : Fam k p γ a := (Pi.single (0 : ZMod p) (1 : k) : ZMod p → k)

omit [CharP k p] in
/-- `famUnit` is nonzero. -/
theorem famUnit_ne_zero (γ : kˣ) (a : k) : famUnit γ a ≠ (0 : Fam k p γ a) := by
  intro h
  have h0 : (Pi.single (0 : ZMod p) (1 : k) : ZMod p → k) = 0 := h
  simpa using congrFun h0 (0 : ZMod p)

/-- The first standard basis vector is an eigenvector of the diagonal operator with eigenvalue
`a`. -/
theorem famDiag_single_zero (a : k) :
    famDiag k p a (Pi.single (0 : ZMod p) (1 : k)) = a • (Pi.single (0 : ZMod p) (1 : k)) := by
  funext i
  rw [famDiag_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = 0
  · rw [if_pos hi, mul_one, mul_one, hi, map_zero, add_zero]
  · rw [if_neg hi, mul_zero, mul_zero]

/-- **The invariant pinning down `a`.** Every eigenvalue of the diagonal operator of `V(γ, a)` is
of the form `a + i` with `i` in the prime field. -/
theorem exists_eq_add_lam_of_eigenvector (a c : k) (w : ZMod p → k) (hw : w ≠ 0)
    (h : famDiag k p a w = c • w) : ∃ i : ZMod p, c = a + lam k p i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨i, ?_⟩
  have h1 := congrFun h i
  rw [famDiag_apply, Pi.smul_apply, smul_eq_mul] at h1
  exact (mul_right_cancel₀ hi h1).symm

/-- Reindexing `k^{ℤ/p}` by the translation `i ↦ i + n`. -/
def reindexEquiv (n : ZMod p) : (ZMod p → k) ≃ₗ[k] (ZMod p → k) where
  toFun v i := v (i + n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w i := w (i - n)
  left_inv v := by funext i; simp
  right_inv w := by funext i; simp

omit [CharP k p] in
/-- Evaluation formula for `reindexEquiv`. -/
@[simp] theorem reindexEquiv_apply (n : ZMod p) (v : ZMod p → k) (i : ZMod p) :
    reindexEquiv n v i = v (i + n) := rfl

/-- Reindexing shifts the eigenvalues of the diagonal operator by `n`. -/
theorem reindexEquiv_famDiag (a : k) (n : ZMod p) (v : ZMod p → k) :
    reindexEquiv n (famDiag k p a v) = famDiag k p (a + lam k p n) (reindexEquiv n v) := by
  funext i
  simp only [reindexEquiv_apply, famDiag_apply, map_add]
  ring

omit [CharP k p] in
/-- Reindexing commutes with the shift. -/
theorem reindexEquiv_famShift (γ : kˣ) (n : ZMod p) (v : ZMod p → k) :
    reindexEquiv n (famShift k p γ v) = famShift k p γ (reindexEquiv n v) := by
  funext i
  simp only [reindexEquiv_apply, famShift_apply]
  congr 2
  ring

/-- **Translation of the parameter.** Reindexing by `n` is an isomorphism of `𝔤`-modules
`V(γ, a) ≅ V(γ, a + n)`: it shifts the eigenvalues of the diagonal operator by `n` and commutes
with the shift. -/
noncomputable def famTranslateEquiv (γ : kˣ) (a : k) (n : ZMod p) :
    Fam k p γ a ≃ₗ⁅k, g k⁆ Fam k p γ (a + lam k p n) := by
  refine lieEquivOfIntertwines k (reindexEquiv n) (fun m => ?_) (fun m => ?_)
  · rw [fam_lie_X, fam_lie_X]
    exact reindexEquiv_famDiag a n m
  · rw [fam_lie_Y, fam_lie_Y]
    exact reindexEquiv_famShift γ n m

/-- **The isomorphism criterion.** `V(γ, a)` and `V(γ', a')` are isomorphic exactly when `γ = γ'`
and `a` and `a'` differ by an element of the prime field. So the `p`-dimensional irreducibles are
parametrized by `kˣ` together with `k` modulo the prime field. -/
theorem fam_nonempty_equiv_iff (γ γ' : kˣ) (a a' : k) :
    Nonempty (Fam k p γ a ≃ₗ⁅k, g k⁆ Fam k p γ' a')
      ↔ γ = γ' ∧ ∃ n : ZMod p, a' = a + lam k p n := by
  constructor
  · rintro ⟨φ⟩
    have hu : φ (famUnit γ a) ≠ 0 := fun h =>
      famUnit_ne_zero γ a (by simpa using congrArg φ.symm h)
    refine ⟨?_, ?_⟩
    · -- the `p`-fold action of `Y` is the scalar `γᵖ`, and `φ` preserves it
      have h1 := lieEquiv_toEnd_pow k φ (Y k) p (famUnit γ a)
      rw [toEnd_Y_pow_char, toEnd_Y_pow_char, map_smul] at h1
      have h2 : ((γ : k) ^ p - (γ' : k) ^ p) • φ (famUnit γ a) = 0 := by
        rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · refine Units.ext ?_
        refine frobenius_inj k p ?_
        rw [frobenius_def, frobenius_def]
        exact sub_eq_zero.mp h
      · exact absurd h hu
    · -- The eigenvalue `a` of `X` transports to an eigenvalue of the diagonal operator of
      -- `V(γ', a')`.
      have hXu : (⁅X k, famUnit γ a⁆ : Fam k p γ a) = a • famUnit γ a := by
        rw [fam_lie_X]; exact famDiag_single_zero a
      have h1 : famDiag k p a' (φ (famUnit γ a)) = a • φ (famUnit γ a) := by
        have h := LieModuleHom.map_lie φ.toLieModuleHom (X k) (famUnit γ a)
        rw [hXu, map_smul, fam_lie_X] at h
        exact h.symm
      obtain ⟨i, hi⟩ := exists_eq_add_lam_of_eigenvector a' a (φ (famUnit γ a)) hu h1
      refine ⟨-i, ?_⟩
      rw [map_neg, hi]
      ring
  · rintro ⟨rfl, n, rfl⟩
    exact ⟨famTranslateEquiv γ a n⟩

/-- Distinct classified members are non-isomorphic. -/
theorem fam_not_equiv {γ γ' : kˣ} {a a' : k} (h : ¬ (γ = γ' ∧ ∃ n : ZMod p, a' = a + lam k p n)) :
    ¬ Nonempty (Fam k p γ a ≃ₗ⁅k, g k⁆ Fam k p γ' a') :=
  fun hh => h ((fam_nonempty_equiv_iff γ γ' a a').mp hh)

/-- A one-dimensional module is never isomorphic to a member of the `p`-dimensional family: the
dimensions `1` and `p` differ. -/
theorem oneDim_not_equiv_fam (μ : k) (γ : kˣ) (a : k) :
    ¬ Nonempty (oneDimModule k μ ≃ₗ⁅k, g k⁆ Fam k p γ a) := by
  rintro ⟨φ⟩
  have h : Module.finrank k (oneDimModule k μ) = Module.finrank k (Fam k p γ a) :=
    φ.toLinearEquiv.finrank_eq
  rw [fam_finrank] at h
  have h1 : Module.finrank k (oneDimModule k μ) = 1 :=
    (Module.finrank_self k).symm ▸ rfl
  rw [h1] at h
  exact ((Fact.out : p.Prime).one_lt).ne h


/-! ### Exhaustiveness

Let `M` be a finite-dimensional irreducible module and write `A`, `B` for the operators by which
`X`, `Y` act. The relation `[X, Y] = Y` reads `A B = B A + B`, whence `A Bⁿ = Bⁿ (A + n)`.

`ker B` is a submodule, so either `B = 0`, and `M` is one-dimensional, or `B` is invertible. In the
latter case `A Bᵖ = Bᵖ A` because `p = 0` in `k`, so the eigenspaces of `Bᵖ` are submodules and
`Bᵖ` is a nonzero scalar `β`. Choosing `c` with `cᵖ = β` and an eigenvector `v` of `A` with
eigenvalue `a`, the vectors `c⁻ⁿ Bⁿ v` depend only on `n` modulo `p`, are eigenvectors of `A` with
the `p` distinct eigenvalues `a + n`, and are permuted cyclically by `B` up to the factor `c`.
They therefore form a basis identifying `M` with `V(c, a)`. -/

variable (k p)

/-- The operator form of `[X, Y] = Y` on any module. -/
theorem lie_X_lie_Y (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
    [LieModule k (g k) M] (m : M) :
    ⁅X k, ⁅Y k, m⁆⁆ = ⁅Y k, ⁅X k, m⁆⁆ + ⁅Y k, m⁆ := by
  have h := lie_lie (X k) (Y k) m
  rw [bracket_X_Y] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- **The `Y`-acts-by-zero branch.** An irreducible module on which `Y` acts by `0` is
one-dimensional, hence a member of the family `oneDimModule`. -/
theorem exists_iso_oneDim_of_lie_Y_eq_zero [IsAlgClosed k] (M : Type*) [AddCommGroup M]
    [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (g k) M] (hY : ∀ m : M, ⁅Y k, m⁆ = 0) :
    ∃ μ : k, Nonempty (M ≃ₗ⁅k, g k⁆ oneDimModule k μ) := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (g k) M
  obtain ⟨μ, hev⟩ := Module.End.exists_eigenvalue (LieModule.toEnd k (g k) M (X k))
  obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
  have hvX : ⁅X k, v⁆ = μ • v := Module.End.mem_eigenspace_iff.mp hvmem
  have hspan : Submodule.span k {v} = ⊤ := by
    refine eq_top_of_invariant_of_ne_zero k M _ (fun m hm => ?_) (fun m _ => ?_)
      (Submodule.mem_span_singleton_self v) hv0
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
      rw [lie_smul, hvX, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [hY]; exact Submodule.zero_mem _
  have hdim : Module.finrank k M = 1 := by
    rw [← finrank_top k M, ← hspan, finrank_span_singleton hv0]
  refine ⟨μ, nonempty_equiv_oneDim k M (fun m => ?_) hY hdim⟩
  have hm : m ∈ Submodule.span k {v} := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
  rw [lie_smul, hvX, smul_smul, smul_smul, mul_comm]


/-- **The `Y`-invertible branch.** An irreducible module on which `Y` acts nontrivially is
isomorphic to a member of the `p`-dimensional family. -/
theorem exists_iso_fam_of_lie_Y_ne_zero [IsAlgClosed k] (M : Type*) [AddCommGroup M]
    [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (g k) M] (hYne : ∃ m : M, ⁅Y k, m⁆ ≠ 0) :
    ∃ (γ : kˣ) (a : k), Nonempty (M ≃ₗ⁅k, g k⁆ Fam k p γ a) := by
  classical
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (g k) M
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  -- name the two operators, keeping only the properties we need
  obtain ⟨A, hAapp⟩ : ∃ A : Module.End k M, ∀ m, A m = ⁅X k, m⁆ :=
    ⟨LieModule.toEnd k (g k) M (X k), fun _ => rfl⟩
  obtain ⟨B, hBapp⟩ : ∃ B : Module.End k M, ∀ m, B m = ⁅Y k, m⁆ :=
    ⟨LieModule.toEnd k (g k) M (Y k), fun _ => rfl⟩
  have hrel : ∀ m : M, A (B m) = B (A m) + B m := by
    intro m; simp only [hAapp, hBapp]; exact lie_X_lie_Y k M m
  -- `ker B` is a submodule, so `B` is injective
  have hBinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    obtain ⟨m₀, hm₀N, hm₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hX : ∀ m ∈ LinearMap.ker B, ⁅X k, m⁆ ∈ LinearMap.ker B := by
      intro m hm
      rw [LinearMap.mem_ker] at hm ⊢
      have h := hrel m
      rw [hm, map_zero, add_zero] at h
      rw [← hAapp]
      exact h.symm
    have hY : ∀ m ∈ LinearMap.ker B, ⁅Y k, m⁆ ∈ LinearMap.ker B := by
      intro m hm
      rw [LinearMap.mem_ker] at hm ⊢
      rw [← hBapp, hm, map_zero]
    have htop := eq_top_of_invariant_of_ne_zero k M (LinearMap.ker B) hX hY hm₀N hm₀
    obtain ⟨m, hm⟩ := hYne
    have hmem : m ∈ LinearMap.ker B := by rw [htop]; exact Submodule.mem_top
    exact hm (by rw [← hBapp]; exact LinearMap.mem_ker.mp hmem)
  have hBpow : ∀ n : ℕ, Function.Injective ((B : Module.End k M) ^ n) := by
    intro n
    induction n with
    | zero => intro x y h; simpa using h
    | succ j ih =>
      intro x y h
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply] at h
      exact hBinj (ih h)
  -- the commutation `A Bⁿ = Bⁿ (A + n)`
  have hApow : ∀ (n : ℕ) (m : M), A ((B ^ n) m) = (B ^ n) (A m) + (n : k) • (B ^ n) m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ j ih =>
      intro m
      simp only [pow_succ, Module.End.mul_apply]
      rw [ih (B m), hrel m, map_add, Nat.cast_succ]
      module
  -- `Bᵖ` commutes with everything, hence is a scalar
  obtain ⟨β, hβ⟩ : ∃ β : k, ∀ m : M, (B ^ p) m = β • m := by
    obtain ⟨β, hev⟩ := Module.End.exists_eigenvalue (B ^ p)
    obtain ⟨w, hwmem, hw0⟩ := hev.exists_hasEigenvector
    refine ⟨β, fun m => ?_⟩
    have hcomm : ∀ x : M, A ((B ^ p) x) = (B ^ p) (A x) := by
      intro x
      rw [hApow p x, CharP.cast_eq_zero k p, zero_smul, add_zero]
    have hBcomm : ∀ x : M, (B ^ p) (B x) = B ((B ^ p) x) := by
      intro x
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']
    have hX : ∀ x ∈ Module.End.eigenspace (B ^ p) β,
        ⁅X k, x⁆ ∈ Module.End.eigenspace (B ^ p) β := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [← hAapp, ← hcomm, hx, map_smul]
    have hY : ∀ x ∈ Module.End.eigenspace (B ^ p) β,
        ⁅Y k, x⁆ ∈ Module.End.eigenspace (B ^ p) β := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [← hBapp, hBcomm, hx, map_smul]
    have htop :=
      eq_top_of_invariant_of_ne_zero k M (Module.End.eigenspace (B ^ p) β) hX hY hwmem hw0
    have hmem : m ∈ Module.End.eigenspace (B ^ p) β := by rw [htop]; exact Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.mp hmem
  have hβ0 : β ≠ 0 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : M)
    exact hw (hBpow p (by rw [hβ, h, zero_smul, map_zero]))
  -- a `p`-th root of the scalar
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := k) β (Fact.out : p.Prime).pos
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hc
    exact hβ0 hc.symm
  -- an eigenvector of `A`
  obtain ⟨a, hev⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
  have hAv : A v = a • v := Module.End.mem_eigenspace_iff.mp hvmem
  -- the normalized orbit of `v` under `B`
  obtain ⟨t, htdef⟩ : ∃ t : ℕ → M, ∀ n, t n = (c⁻¹ ^ n) • (B ^ n) v :=
    ⟨fun n => (c⁻¹ ^ n) • (B ^ n) v, fun _ => rfl⟩
  have htA : ∀ n : ℕ, A (t n) = (a + (n : k)) • t n := by
    intro n
    rw [htdef n, map_smul, hApow n v, hAv, map_smul]
    module
  have htB : ∀ n : ℕ, B (t n) = c • t (n + 1) := by
    intro n
    have hcc : c * c⁻¹ ^ (n + 1) = c⁻¹ ^ n := by
      rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    rw [htdef n, htdef (n + 1), map_smul, smul_smul, hcc, ← Module.End.mul_apply, ← pow_succ']
  have ht0 : ∀ n : ℕ, t n ≠ 0 := by
    intro n h
    rw [htdef n] at h
    rcases smul_eq_zero.mp h with h2 | h2
    · exact pow_ne_zero _ (inv_ne_zero hc0) h2
    · exact hv0 (hBpow n (by rw [h2, map_zero]))
  have htper : ∀ n : ℕ, t (n + p) = t n := by
    intro n
    have h1 : (B ^ (n + p)) v = β • (B ^ n) v := by
      rw [pow_add, Module.End.mul_apply, hβ v, map_smul]
    have hpinv : c⁻¹ ^ p * c ^ p = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hc0, one_pow]
    have hscal : c⁻¹ ^ (n + p) * β = c⁻¹ ^ n := by
      rw [← hc, pow_add, mul_assoc, hpinv, mul_one]
    rw [htdef (n + p), htdef n, h1, smul_smul, hscal]
  have htmul : ∀ q n : ℕ, t (n + p * q) = t n := by
    intro q
    induction q with
    | zero => intro n; simp
    | succ j ih => intro n; rw [Nat.mul_succ, ← Nat.add_assoc, htper, ih]
  have htmod : ∀ n : ℕ, t (n % p) = t n := by
    intro n
    conv_rhs => rw [← Nat.mod_add_div n p]
    rw [htmul]
  -- reindex by `ℤ/p`
  obtain ⟨u, hudef⟩ : ∃ u : ZMod p → M, ∀ i, u i = t i.val := ⟨fun i => t i.val, fun _ => rfl⟩
  have huA : ∀ i : ZMod p, A (u i) = (a + lam k p i) • u i := by
    intro i
    rw [hudef i, htA, lam_val]
  have huB : ∀ i : ZMod p, B (u i) = c • u (i + 1) := by
    intro i
    rw [hudef i, hudef (i + 1), htB]
    congr 1
    rw [← htmod (i.val + 1)]
    congr 1
    rw [ZMod.val_add, ZMod.val_one]
  have hu0 : ∀ i : ZMod p, u i ≠ 0 := by
    intro i
    rw [hudef i]
    exact ht0 i.val
  -- the `u i` are eigenvectors of `A` with distinct eigenvalues, hence independent
  have hindep : LinearIndependent k u := by
    refine Module.End.eigenvectors_linearIndependent' A (fun i => a + lam k p i) ?_ u ?_
    · intro i j hij
      exact lam_injective k p (add_left_cancel hij)
    · intro i
      exact ⟨Module.End.mem_eigenspace_iff.mpr (huA i), hu0 i⟩
  -- their span is invariant, hence everything
  have hspanX : ∀ m ∈ Submodule.span k (Set.range u),
      ⁅X k, m⁆ ∈ Submodule.span k (Set.range u) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← hAapp, huA]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [lie_smul]; exact Submodule.smul_mem _ _ hx
  have hspanY : ∀ m ∈ Submodule.span k (Set.range u),
      ⁅Y k, m⁆ ∈ Submodule.span k (Set.range u) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← hBapp, huB]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + 1, rfl⟩)
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [lie_smul]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span k (Set.range u) = ⊤ :=
    eq_top_of_invariant_of_ne_zero k M _ hspanX hspanY
      (Submodule.subset_span ⟨0, rfl⟩) (hu0 0)
  -- so the `u i` form a basis
  let b : Module.Basis (ZMod p) k M := Module.Basis.mk hindep (le_of_eq hspan.symm)
  have hb : ∀ i, b i = u i := fun i => Module.Basis.mk_apply hindep _ i
  -- and the coordinate isomorphism intertwines the two actions
  have hXint : ∀ f : ZMod p → k,
      b.equivFun.symm (famDiag k p a f) = A (b.equivFun.symm f) := by
    intro f
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb i, huA i, famDiag_apply, smul_smul, mul_comm]
  have hYint : ∀ f : ZMod p → k,
      b.equivFun.symm (famShift k p (Units.mk0 c hc0) f) = B (b.equivFun.symm f) := by
    intro f
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    have hR : ∀ i : ZMod p, B (f i • b i) = (f i * c) • u (i + 1) := fun i => by
      rw [hb, map_smul, huB, smul_smul]
    have hL : ∀ i : ZMod p,
        (famShift k p (Units.mk0 c hc0) f) i • b i = (c * f (i - 1)) • u i := fun i => by
      rw [hb, famShift_apply, Units.val_mk0]
    simp only [hR, hL]
    exact (Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _
      (fun i => by simp [mul_comm])).symm
  have key : Fam k p (Units.mk0 c hc0) a ≃ₗ⁅k, g k⁆ M := by
    refine lieEquivOfIntertwines k b.equivFun.symm (fun f => ?_) (fun f => ?_)
    · rw [fam_lie_X, ← hAapp]
      exact hXint f
    · rw [fam_lie_Y, ← hBapp]
      exact hYint f
  exact ⟨Units.mk0 c hc0, a, ⟨key.symm⟩⟩


/-- **Characteristic-`p` exhaustiveness.** Over an algebraically closed field of characteristic
`p`, every finite-dimensional irreducible `𝔤`-module is isomorphic either to a one-dimensional
module `oneDimModule μ` or to a member `V(γ, a)` of the `p`-dimensional family. -/
theorem charP_exists_iso [IsAlgClosed k] (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (g k) M] [LieModule k (g k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (g k) M] :
    (∃ μ : k, Nonempty (M ≃ₗ⁅k, g k⁆ oneDimModule k μ))
      ∨ ∃ (γ : kˣ) (a : k), Nonempty (M ≃ₗ⁅k, g k⁆ Fam k p γ a) := by
  by_cases h : ∀ m : M, ⁅Y k, m⁆ = 0
  · exact Or.inl (exists_iso_oneDim_of_lie_Y_eq_zero k M h)
  · exact Or.inr (exists_iso_fam_of_lie_Y_ne_zero k p M (not_forall.mp h))

/-- **The characteristic-`p` classification.** Over an algebraically closed field of characteristic
`p`, a finite-dimensional irreducible `𝔤`-module is isomorphic to exactly one classified member:
either to `oneDimModule μ` for a unique `μ ∈ k`, or to `V(γ, a)` for a `γ ∈ kˣ` unique on the nose
and an `a ∈ k` unique modulo the prime field. The two cases are exclusive by
`oneDim_not_equiv_fam`, since `1 ≠ p`. -/
theorem charP_exists_unique_iso [IsAlgClosed k] (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (g k) M] [LieModule k (g k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (g k) M] :
    (∃! μ : k, Nonempty (M ≃ₗ⁅k, g k⁆ oneDimModule k μ))
      ∨ ∃ (γ : kˣ) (a : k), Nonempty (M ≃ₗ⁅k, g k⁆ Fam k p γ a)
          ∧ ∀ (γ' : kˣ) (a' : k), Nonempty (M ≃ₗ⁅k, g k⁆ Fam k p γ' a') →
              γ' = γ ∧ ∃ n : ZMod p, a' = a + lam k p n := by
  rcases charP_exists_iso k p M with ⟨μ, hμ⟩ | ⟨γ, a, hγa⟩
  · refine Or.inl ⟨μ, hμ, ?_⟩
    rintro ν ⟨ψ⟩
    obtain ⟨φ⟩ := hμ
    by_contra hne
    exact oneDim_not_iso k (Ne.symm hne) ⟨φ.symm.trans ψ⟩
  · refine Or.inr ⟨γ, a, hγa, ?_⟩
    rintro γ' a' ⟨ψ⟩
    obtain ⟨φ⟩ := hγa
    obtain ⟨hg, n, hn⟩ := (fam_nonempty_equiv_iff γ' γ a' a).mp ⟨ψ.symm.trans φ⟩
    refine ⟨hg, -n, ?_⟩
    rw [map_neg, hn]
    ring

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

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_2.g
  Etingof.Problem2_16_2.X
  Etingof.Problem2_16_2.Y
  Etingof.Problem2_16_2.ofInvariantXY
  Etingof.Problem2_16_2.lieEquivOfIntertwines
  Etingof.Problem2_16_2.oneDimModule
  Etingof.Problem2_16_2.instAddCommGroupOneDimModule
  Etingof.Problem2_16_2.instModuleOneDimModule
  Etingof.Problem2_16_2.oneDimRep
  Etingof.Problem2_16_2.instLieRingModuleSubtypeMatrixFinOfNatNatMemLieSubalgebraGOneDimModule
  Etingof.Problem2_16_2.oneDimEquivSelf
  Etingof.Problem2_16_2.lam
  Etingof.Problem2_16_2.famDiag
  Etingof.Problem2_16_2.shiftOp
  Etingof.Problem2_16_2.famShift
  Etingof.Problem2_16_2.rowZero
  Etingof.Problem2_16_2.famRep
  Etingof.Problem2_16_2.Fam
  Etingof.Problem2_16_2.instAddCommGroupFam
  Etingof.Problem2_16_2.instModuleFam
  Etingof.Problem2_16_2.famRep'
  Etingof.Problem2_16_2.famLieRingModule
  Etingof.Problem2_16_2.vsupp
  Etingof.Problem2_16_2.famUnit
  Etingof.Problem2_16_2.reindexEquiv
  Etingof.Problem2_16_2.famTranslateEquiv

-- These indices intentionally select distinct module structures on the same carrier types.
attribute [nolint defsWithUnderscore unusedArguments]
  Etingof.Problem2_16_2.oneDimModule
  Etingof.Problem2_16_2.Fam
