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

/-!
### Tools for the uniqueness statement

A positive definite Hermitian form `c` is *nondegenerate*: the conjugate-linear map
`v ↦ c(v, ·)` into the dual `V →ₗ[ℂ] ℂ` is injective, and (in finite dimensions) bijective.
Composing the inverse of this map for `c₁` with the map for `c₂` yields a genuine
`ℂ`-linear endomorphism `A` of `V` with `c₁(A v, w) = c₂(v, w)`; this is the intertwiner
of the book proof.
-/

namespace Theorem4_6_2

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

open scoped ComplexConjugate

/-- Right additivity of an `InnerProductSpace.Core`, derived from left additivity and
Hermitian symmetry. -/
private lemma core_inner_add_right (c : InnerProductSpace.Core ℂ V) (x y z : V) :
    c.inner x (y + z) = c.inner x y + c.inner x z := by
  rw [← c.conj_inner_symm x (y + z), c.add_left, map_add, c.conj_inner_symm x y,
    c.conj_inner_symm x z]

/-- Right `ℂ`-linearity of an `InnerProductSpace.Core`. -/
private lemma core_inner_smul_right (c : InnerProductSpace.Core ℂ V) (x y : V) (r : ℂ) :
    c.inner x (r • y) = r * c.inner x y := by
  rw [← c.conj_inner_symm x (r • y), c.smul_left, map_mul, c.conj_inner_symm x y, Complex.conj_conj]

/-- Left subtractivity of an `InnerProductSpace.Core`. -/
private lemma core_inner_sub_left (c : InnerProductSpace.Core ℂ V) (x y z : V) :
    c.inner (x - y) z = c.inner x z - c.inner y z := by
  rw [sub_eq_add_neg, c.add_left, ← neg_one_smul ℂ y, c.smul_left]
  simp [sub_eq_add_neg]

/-- The functional `w ↦ c(v, w)` as an element of the dual `V →ₗ[ℂ] ℂ`. -/
private noncomputable def innerFunctional (c : InnerProductSpace.Core ℂ V) (v : V) :
    Module.Dual ℂ V where
  toFun w := c.inner v w
  map_add' y z := core_inner_add_right c v y z
  map_smul' r w := by simp only [RingHom.id_apply, smul_eq_mul]; exact core_inner_smul_right c v w r

@[simp] private lemma innerFunctional_apply (c : InnerProductSpace.Core ℂ V) (v w : V) :
    innerFunctional c v w = c.inner v w := rfl

/-- The conjugate-linear map `v ↦ c(v, ·)` from `V` into its dual. -/
private noncomputable def innerToDual (c : InnerProductSpace.Core ℂ V) :
    V →ₛₗ[starRingEnd ℂ] Module.Dual ℂ V where
  toFun := innerFunctional c
  map_add' v v' := by
    ext w; simp only [innerFunctional_apply, LinearMap.add_apply]; exact c.add_left v v' w
  map_smul' r v := by
    ext w
    simp only [innerFunctional_apply, LinearMap.smul_apply, smul_eq_mul]
    exact c.smul_left v w r

@[simp] private lemma innerToDual_apply (c : InnerProductSpace.Core ℂ V) (v w : V) :
    innerToDual c v w = c.inner v w := rfl

/-- Nondegeneracy: the conjugate-linear map into the dual is injective. -/
private lemma innerToDual_injective (c : InnerProductSpace.Core ℂ V) :
    Function.Injective (innerToDual c) := by
  intro u u' h
  have h' : ∀ w, c.inner u w = c.inner u' w := fun w => by
    have := DFunLike.congr_fun h w; simpa using this
  have hz : c.inner (u - u') (u - u') = 0 := by
    rw [core_inner_sub_left, h' (u - u'), sub_self]
  have := c.definite (u - u') hz
  exact sub_eq_zero.mp this

/-- In finite dimensions, the conjugate-linear map into the dual is surjective: it is an
injective conjugate-linear map between two `ℝ`-spaces of equal (real) dimension. -/
private lemma innerToDual_surjective (c : InnerProductSpace.Core ℂ V) [FiniteDimensional ℂ V] :
    Function.Surjective (innerToDual c) := by
  haveI : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  haveI : FiniteDimensional ℝ (Module.Dual ℂ V) := Module.Finite.trans ℂ (Module.Dual ℂ V)
  let fR : V →ₗ[ℝ] Module.Dual ℂ V :=
    { toFun := innerToDual c
      map_add' := (innerToDual c).map_add
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r v, LinearMap.map_smulₛₗ, RCLike.conj_ofReal,
          ← RCLike.real_smul_eq_coe_smul (K := ℂ) r (innerToDual c v)] }
  have hinj : Function.Injective fR := innerToDual_injective c
  have hfin : Module.finrank ℝ V = Module.finrank ℝ (Module.Dual ℂ V) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ V, ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ V),
      Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj

/-- The conjugate-linear equivalence `V ≃ V*` induced by a nondegenerate form in finite
dimensions. -/
private noncomputable def innerEquivDual (c : InnerProductSpace.Core ℂ V) [FiniteDimensional ℂ V] :
    V ≃ₛₗ[starRingEnd ℂ] Module.Dual ℂ V :=
  LinearEquiv.ofBijective (innerToDual c) ⟨innerToDual_injective c, innerToDual_surjective c⟩

@[simp] private lemma innerEquivDual_apply (c : InnerProductSpace.Core ℂ V) [FiniteDimensional ℂ V]
    (v w : V) : innerEquivDual c v w = c.inner v w := rfl

end Theorem4_6_2

open Theorem4_6_2 in
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
  classical
  haveI : Nontrivial V := hnontrivial
  -- The intertwiner `A`, characterised by `c₁(A v, w) = c₂(v, w)`.
  set A : Module.End ℂ V := ((innerEquivDual c₁).symm.toLinearMap).comp (innerToDual c₂) with hA_def
  -- Defining property of `A`.
  have hA : ∀ v w, c₁.inner (A v) w = c₂.inner v w := by
    intro v w
    have hval : innerEquivDual c₁ (A v) = innerToDual c₂ v :=
      (innerEquivDual c₁).apply_symm_apply (innerToDual c₂ v)
    have hw := DFunLike.congr_fun hval w
    rwa [innerEquivDual_apply, innerToDual_apply] at hw
  -- `g · g⁻¹` acts trivially.
  have hgg : ∀ (g : G) (x : V), ρ g (ρ g⁻¹ x) = x := fun g x => by
    have : ρ g (ρ g⁻¹ x) = ρ (g * g⁻¹) x := by rw [map_mul]; rfl
    rw [this, mul_inv_cancel, map_one]; rfl
  -- `A` intertwines `ρ`: it commutes with every `ρ g`.
  have hcomm : ∀ (g : G) (v : V), A (ρ g v) = ρ g (A v) := by
    intro g v
    apply innerToDual_injective c₁
    ext w
    change c₁.inner (A (ρ g v)) w = c₁.inner (ρ g (A v)) w
    have hR : c₁.inner (ρ g (A v)) w = c₂.inner (ρ g v) w := by
      calc c₁.inner (ρ g (A v)) w
          = c₁.inner (ρ g (A v)) (ρ g (ρ g⁻¹ w)) := by rw [hgg g w]
        _ = c₁.inner (A v) (ρ g⁻¹ w) := h₁ g (A v) (ρ g⁻¹ w)
        _ = c₂.inner v (ρ g⁻¹ w) := hA v (ρ g⁻¹ w)
        _ = c₂.inner (ρ g v) (ρ g (ρ g⁻¹ w)) := (h₂ g v (ρ g⁻¹ w)).symm
        _ = c₂.inner (ρ g v) w := by rw [hgg g w]
    rw [hA (ρ g v) w, hR]
  -- Schur: an intertwiner of an irreducible representation over `ℂ` is a scalar.
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  have hWinv : ∀ g : G, ∀ v ∈ Module.End.eigenspace A μ, ρ g v ∈ Module.End.eigenspace A μ := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hcomm g v, hv, map_smul]
  have hWtop : Module.End.eigenspace A μ = ⊤ := (hirr _ hWinv).resolve_left hμ
  have hAμ : ∀ v, A v = μ • v := by
    intro v
    have : v ∈ Module.End.eigenspace A μ := by rw [hWtop]; exact Submodule.mem_top
    rwa [Module.End.mem_eigenspace_iff] at this
  -- Hence `c₂ = conj μ • c₁` as forms.
  have hform : ∀ v w, c₂.inner v w = (starRingEnd ℂ) μ * c₁.inner v w := by
    intro v w
    rw [← hA v w, hAμ v]
    exact c₁.smul_left v w μ
  -- Positivity: for `c` positive definite and `v ≠ 0`, `c(v, v)` is a positive real.
  have hpos : ∀ (c : InnerProductSpace.Core ℂ V) {v : V}, v ≠ 0 →
      c.inner v v = (RCLike.re (c.inner v v) : ℂ) ∧ 0 < RCLike.re (c.inner v v) := by
    intro c v hv
    have him : RCLike.im (c.inner v v) = 0 :=
      RCLike.conj_eq_iff_im.mp (c.conj_inner_symm v v)
    have hreal : c.inner v v = (RCLike.re (c.inner v v) : ℂ) := by
      apply RCLike.ext <;> simp [him]
    refine ⟨hreal, ?_⟩
    rcases (c.re_inner_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (c.definite v (by rw [hreal, ← h]; simp)) hv
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨h1real, h1pos⟩ := hpos c₁ hv₀
  obtain ⟨h2real, h2pos⟩ := hpos c₂ hv₀
  set a : ℝ := RCLike.re (c₁.inner v₀ v₀) with ha_def
  set b : ℝ := RCLike.re (c₂.inner v₀ v₀) with hb_def
  refine ⟨b / a, div_pos h2pos h1pos, ?_⟩
  -- It remains to identify `conj μ` with the positive real `b / a`.
  have hconj : (starRingEnd ℂ) μ = ((b / a : ℝ) : ℂ) := by
    have hkey : c₂.inner v₀ v₀ = (starRingEnd ℂ) μ * c₁.inner v₀ v₀ := hform v₀ v₀
    rw [h1real, h2real] at hkey
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast h1pos.ne'
    rw [Complex.ofReal_div, eq_div_iff ha0]
    exact hkey.symm
  intro v w
  rw [hform v w, hconj]

end Etingof
