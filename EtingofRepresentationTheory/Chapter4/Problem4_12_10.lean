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
