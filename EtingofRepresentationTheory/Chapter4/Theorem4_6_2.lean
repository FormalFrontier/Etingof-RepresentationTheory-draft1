import Mathlib

/-!
# Theorem 4.6.2: Existence and Uniqueness of Unitary Structure

If G is a finite group, then:

(i) Any finite dimensional complex representation of G has a unitary structure.
The construction averages any positive definite Hermitian form B over G:
  B̄(v, w) = Σ_{g∈G} B(ρ(g)v, ρ(g)w)
which is G-invariant and positive definite.

(ii) If V is irreducible, this unitary structure is unique up to scaling by a
positive real number. This follows from Schur's lemma: if B₁, B₂ are two
G-invariant forms, the intertwiner B₂⁻¹ ∘ B₁ is a scalar multiple of identity.

## Formalization notes

A "positive definite Hermitian form" on a complex vector space `V` is exactly the
data of an `InnerProductSpace.Core ℂ V`: it bundles a sesquilinear form together
with Hermitian symmetry (`conj_inner_symm`), positive semidefiniteness
(`re_inner_nonneg`) and definiteness (`definite`). We therefore phrase the
existence statement as the existence of a `G`-invariant `InnerProductSpace.Core`,
and prove it by Weyl's averaging trick starting from any inner product transported
from `EuclideanSpace` along a basis.

## Mathlib correspondence

This is the unitarizability theorem. Not directly in Mathlib.
-/

namespace Etingof

open scoped ComplexConjugate

/-- A positive definite Hermitian form (`InnerProductSpace.Core`) on a complex vector
space `V`, obtained by pulling back the inner product of an inner product space `F`
along a linear equivalence `e : V ≃ₗ[ℂ] F`. -/
@[reducible] noncomputable def coreOfLinearEquiv
    {V F : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (e : V ≃ₗ[ℂ] F) :
    InnerProductSpace.Core ℂ V where
  inner v w := inner ℂ (e v) (e w)
  conj_inner_symm x y := by
    change (starRingEnd ℂ) (inner ℂ (e y) (e x)) = inner ℂ (e x) (e y)
    exact inner_conj_symm (e x) (e y)
  re_inner_nonneg x := by
    exact inner_self_nonneg
  add_left x y z := by
    change inner ℂ (e (x + y)) (e z) = inner ℂ (e x) (e z) + inner ℂ (e y) (e z)
    rw [map_add, inner_add_left]
  smul_left x y r := by
    change inner ℂ (e (r • x)) (e y) = (starRingEnd ℂ) r * inner ℂ (e x) (e y)
    rw [map_smul, inner_smul_left]
  definite x hx := by
    have hx' : inner ℂ (e x) (e x) = 0 := hx
    exact e.map_eq_zero_iff.mp (inner_self_eq_zero.mp hx')

/-- Weyl's averaging trick: from any positive definite Hermitian form `c` on the
carrier of a representation `ρ` of a finite group `G`, produce the averaged form
`B̄(v, w) = Σ_{g∈G} c(ρ(g)v, ρ(g)w)`, again a positive definite Hermitian form. -/
@[reducible] noncomputable def avgCore
    {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : InnerProductSpace.Core ℂ V) :
    InnerProductSpace.Core ℂ V where
  inner v w := ∑ g : G, c.inner (ρ g v) (ρ g w)
  conj_inner_symm x y := by
    change (starRingEnd ℂ) (∑ g : G, c.inner (ρ g y) (ρ g x))
        = ∑ g : G, c.inner (ρ g x) (ρ g y)
    rw [map_sum]
    exact Finset.sum_congr rfl (fun g _ => c.conj_inner_symm (ρ g x) (ρ g y))
  re_inner_nonneg x := by
    rw [map_sum]
    exact Finset.sum_nonneg (fun g _ => c.re_inner_nonneg (ρ g x))
  add_left x y z := by
    change (∑ g : G, c.inner (ρ g (x + y)) (ρ g z))
        = (∑ g : G, c.inner (ρ g x) (ρ g z)) + ∑ g : G, c.inner (ρ g y) (ρ g z)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [map_add, c.add_left]
  smul_left x y r := by
    change (∑ g : G, c.inner (ρ g (r • x)) (ρ g y))
        = (starRingEnd ℂ) r * ∑ g : G, c.inner (ρ g x) (ρ g y)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [map_smul, c.smul_left]
  definite x hx := by
    have hx' : (∑ g : G, c.inner (ρ g x) (ρ g x)) = 0 := hx
    -- The real part of the sum is a sum of nonnegative reals, hence each term is zero.
    have hre : (∑ g : G, RCLike.re (c.inner (ρ g x) (ρ g x))) = 0 := by
      rw [← map_sum, hx', map_zero]
    have hterm : ∀ g ∈ Finset.univ, 0 ≤ RCLike.re (c.inner (ρ g x) (ρ g x)) :=
      fun g _ => c.re_inner_nonneg (ρ g x)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hre
    -- In particular the `g = 1` term vanishes, and `ρ 1 x = x`.
    have h1 : RCLike.re (c.inner x x) = 0 := by
      have := hzero 1 (Finset.mem_univ 1)
      simpa using this
    -- `c.inner x x` is real (Hermitian symmetry), so real part zero forces it to be zero.
    have him : RCLike.im (c.inner x x) = 0 := by
      have hconj : (starRingEnd ℂ) (c.inner x x) = c.inner x x := c.conj_inner_symm x x
      have := RCLike.conj_eq_iff_im (z := c.inner x x).mp hconj
      simpa using this
    have : c.inner x x = 0 := by
      apply RCLike.ext <;> simp [h1, him]
    exact c.definite x this

set_option linter.unusedFintypeInType false in
/-- Any finite dimensional complex representation of a finite group admits a
`G`-invariant positive definite Hermitian form (a unitary structure).
(Etingof Theorem 4.6.2, part i) -/
theorem Theorem4_6_2_existence
    (G : Type*) [Group G] [Fintype G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ c : InnerProductSpace.Core ℂ V,
      ∀ (g : G) (v w : V), c.inner (ρ g v) (ρ g w) = c.inner v w := by
  -- Start from any inner product on `V`, transported from `EuclideanSpace` via a basis.
  let b := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    b.equivFun.trans (EuclideanSpace.equiv (Fin (Module.finrank ℂ V)) ℂ).symm.toLinearEquiv
  let c₀ := coreOfLinearEquiv e
  refine ⟨avgCore ρ c₀, ?_⟩
  intro h v w
  -- `(avgCore ρ c₀).inner a b = Σ g, c₀.inner (ρ g a) (ρ g b)`.
  change (∑ g : G, c₀.inner (ρ g (ρ h v)) (ρ g (ρ h w)))
      = ∑ g : G, c₀.inner (ρ g v) (ρ g w)
  have hstepv : ∀ g : G, ρ g (ρ h v) = ρ (g * h) v := fun g => by rw [map_mul]; rfl
  have hstepw : ∀ g : G, ρ g (ρ h w) = ρ (g * h) w := fun g => by rw [map_mul]; rfl
  calc
    (∑ g : G, c₀.inner (ρ g (ρ h v)) (ρ g (ρ h w)))
        = ∑ g : G, c₀.inner (ρ (g * h) v) (ρ (g * h) w) := by
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [hstepv g, hstepw g]
    _ = ∑ g : G, c₀.inner (ρ g v) (ρ g w) :=
          Equiv.sum_comp (Equiv.mulRight h) (fun g => c₀.inner (ρ g v) (ρ g w))

set_option linter.unusedFintypeInType false in
/-- For an irreducible representation, the unitary structure is unique up to scaling
by a positive real number: any two `G`-invariant positive definite Hermitian forms
`c₁`, `c₂` are proportional, `c₂ = λ • c₁` with `λ > 0`.
(Etingof Theorem 4.6.2, part ii)

Irreducibility is expressed as: `V` is nontrivial and has no proper nonzero
`ρ`-invariant subspace. -/
theorem Theorem4_6_2_uniqueness
    (G : Type*) [Group G] [Fintype G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hnontrivial : Nontrivial V)
    (hirr : ∀ W : Submodule ℂ V, (∀ g : G, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (c₁ c₂ : InnerProductSpace.Core ℂ V)
    (h₁ : ∀ (g : G) (v w : V), c₁.inner (ρ g v) (ρ g w) = c₁.inner v w)
    (h₂ : ∀ (g : G) (v w : V), c₂.inner (ρ g v) (ρ g w) = c₂.inner v w) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v w : V, c₂.inner v w = (lam : ℂ) * c₁.inner v w := by
  -- Both forms are nondegenerate, so `c₂(v, w) = c₁(A v, w)` for a unique linear `A`,
  -- which intertwines `ρ` by `G`-invariance of both forms. Schur's lemma (using `hirr`)
  -- forces `A = λ • id`, and positivity of both forms forces `λ > 0`.
  -- Requires building the Riesz/adjoint correspondence at the `InnerProductSpace.Core`
  -- level plus Schur's lemma for irreducible `ρ`.
  sorry

end Etingof
