import Mathlib

/-!
# Problem 4.12.10: Every irreducible occurs in a tensor power of a faithful representation

**Problem 4.12.10.** Let `G` be a finite group and let `V` be a complex representation of
`G` which is faithful, i.e., the corresponding map `G → GL(V)` is injective. Show that any
irreducible representation of `G` occurs inside `SⁿV` (and hence inside `V^{⊗n}`) for some
`n`.

## Formalization

We formalize the "hence inside `V^{⊗n}`" form (the symmetric-power form implies it). The
`n`-th tensor power `⨂[ℂ]^n V` carries the **diagonal representation** `diagTensorPow ρ n`,
sending `g` to `⨂ⁿ (ρ g)`. "The irreducible `W` occurs inside `V^{⊗n}`" is formalized as
the existence of a **nonzero `G`-equivariant linear map** `W → ⨂[ℂ]^n V`; since `W` is
simple, such a map is automatically injective, so `W` is isomorphic to a subrepresentation.
-/

open scoped TensorProduct

set_option linter.unusedFintypeInType false

noncomputable section

variable {k : Type*} [CommRing k] {G : Type*} [Monoid G]
  {V : Type*} [AddCommGroup V] [Module k V]

/-- The diagonal action of `G` on the `n`-th tensor power `⨂[k]^n V`, obtained from a
representation `ρ` on `V` by applying `ρ g` in each tensor factor. -/
def diagTensorPow (ρ : Representation k G V) (n : ℕ) :
    Representation k G (⨂[k]^n V) where
  toFun g := PiTensorProduct.map (fun _ : Fin n => ρ g)
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_id
  map_mul' g h := by
    simp only [map_mul, Module.End.mul_eq_comp]
    rw [← PiTensorProduct.map_comp]

@[simp]
theorem diagTensorPow_apply (ρ : Representation k G V) (n : ℕ) (g : G) :
    diagTensorPow ρ n g = PiTensorProduct.map (fun _ : Fin n => ρ g) := rfl

end

section TracePow

open Module

/-- The trace of the diagonal endomorphism `⨂ⁿ f` (i.e. `PiTensorProduct.map (fun _ => f)`)
on the `n`-th tensor power `⨂[k]^n V` equals `(trace f) ^ n`. -/
theorem trace_piTensorProduct_map_const
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (n : ℕ) (f : V →ₗ[k] V) :
    LinearMap.trace k (⨂[k]^n V) (PiTensorProduct.map (fun _ : Fin n => f))
      = (LinearMap.trace k V f) ^ n := by
  classical
  set D := Module.finrank k V with hD
  let b : Basis (Fin D) k V := Module.finBasis k V
  -- Compute the trace as a sum of diagonal matrix entries in the tensor-product basis.
  have key : LinearMap.trace k (⨂[k]^n V) (PiTensorProduct.map (fun _ : Fin n => f))
      = ∑ s : Fin n → Fin D, ∏ i : Fin n, (LinearMap.toMatrix b b f) (s i) (s i) := by
    rw [LinearMap.trace_eq_matrix_trace k (Basis.piTensorProduct (fun _ : Fin n => b)),
      Matrix.trace]
    apply Finset.sum_congr rfl
    intro s _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Basis.piTensorProduct_apply,
      PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
    apply Finset.prod_congr rfl
    intro i _
    rw [LinearMap.toMatrix_apply]
  rw [key]
  have htr : LinearMap.trace k V f = ∑ j : Fin D, (LinearMap.toMatrix b b f) j j := by
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.diag_apply]
  rw [htr, Finset.sum_pow', Fintype.piFinset_univ]

/-- The character of the diagonal tensor-power representation is the `n`-th power of the
character of `ρ`: `χ_{V^{⊗n}}(g) = χ_V(g) ^ n`. -/
theorem character_diagTensorPow
    {k : Type*} [Field k] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (n : ℕ) (g : G) :
    (diagTensorPow ρ n).character g = (ρ.character g) ^ n := by
  rw [Representation.character, diagTensorPow_apply, trace_piTensorProduct_map_const]
  rfl

end TracePow

/-- **Problem 4.12.10.** Let `G` be a finite group with a faithful complex representation
`ρ` on `V`, and let `σ` be an irreducible complex representation on `W`. Then `W` occurs
inside `V^{⊗n}` for some `n`: there is a nonzero `G`-equivariant linear map
`W → ⨂[ℂ]^n V`. -/
theorem Etingof.Problem4_12_10 {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Function.Injective ρ)
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W)
    (hσ : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule) :
    ∃ (n : ℕ) (φ : W →ₗ[ℂ] (⨂[ℂ]^n V)),
      φ ≠ 0 ∧ ∀ g : G, φ ∘ₗ σ g = (diagTensorPow ρ n g) ∘ₗ φ := by
  sorry
