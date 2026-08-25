import EtingofRepresentationTheory.Chapter3.Problem3_9_1
import EtingofRepresentationTheory.Chapter2.Definition2_3_8
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Problem 3.9.2: `Ext¹` for polynomial algebras and algebras with zero multiplication

**(a)** Let `A = ℂ[x₁, …, xₙ]` and let `Vₐ, V_b` be the 1-dimensional representations in which
`xᵢ` acts by `aᵢ`, `bᵢ` respectively. Compute `Ext¹(Vₐ, V_b)` and classify the 2-dimensional
representations of `A`.

**(b)** Let `B = ℂ⟨x₁, …, xₙ⟩ / (xᵢxⱼ = 0)`. Show that for `n > 1`, `B` has infinitely many
nonisomorphic indecomposable representations.

We model the 1-dimensional representation `Vₐ` as the quotient `A ⧸ 𝔪ₐ` by the maximal
ideal `𝔪ₐ = (x₁ − a₁, …, xₙ − aₙ)`. This is an `A`-module and `ℂ`-module with the
scalar tower `ℂ → A → A⧸𝔪ₐ`, on which `xᵢ` acts by the scalar `aᵢ`, so it fits the
`Ext¹` framework of Problem 3.9.1 (`Etingof.Problem3_9_1.Ext1`). The convention there is that
`Ext1 k A V W` classifies extensions `0 → V → U → W → 0`, i.e. `Ext¹(W, V)`; so the book's
`Ext¹(Vₐ, V_b)` (extensions `0 → V_b → U → Vₐ → 0`) is `Ext1 ℂ A V_b Vₐ`.

The answer to (a): `Ext¹(Vₐ, V_b) ≅ ℂⁿ` if `a = b` and `= 0` if `a ≠ b`. Every 2-dimensional
representation is an extension of two 1-dimensional ones, so is classified by the pair
`(a, b)` together with a class in `Ext¹(Vₐ, V_b)`.

For (b) the algebra `B` is the free algebra `ℂ⟨x₁,…,xₙ⟩` modulo the two-sided relations
`xᵢxⱼ = 0`, constructed as a `RingQuot`.
-/

namespace Etingof.Problem3_9_2

open Etingof.Problem3_9_1 (Ext1)

/-! ## Part (a): the polynomial algebra `ℂ[x₁, …, xₙ]` -/

/-- The polynomial algebra `A = ℂ[x₁, …, xₙ]`. -/
abbrev polyAlg (n : ℕ) : Type := MvPolynomial (Fin n) ℂ

/-- The maximal ideal `𝔪ₐ = (x₁ − a₁, …, xₙ − aₙ)` of `ℂ[x₁, …, xₙ]` at the point `a`. -/
noncomputable def maxIdeal {n : ℕ} (a : Fin n → ℂ) : Ideal (polyAlg n) :=
  Ideal.span (Set.range fun i => MvPolynomial.X i - MvPolynomial.C (a i))

/-- The 1-dimensional representation `Vₐ`, in which `xᵢ` acts by the scalar `aᵢ`, modelled as
the quotient `A ⧸ 𝔪ₐ`. An `A`-module and `ℂ`-module with scalar tower. -/
abbrev Vrep {n : ℕ} (a : Fin n → ℂ) : Type := polyAlg n ⧸ maxIdeal a

open Etingof.Problem3_9_1
open MvPolynomial

/-! ### Shared infrastructure for the 1-dimensional representations `Vₐ`

The module `Vrep a = A ⧸ 𝔪ₐ` is 1-dimensional over `ℂ`, and any `p ∈ A` acts on it by the scalar
`p(a) = aeval a p`. The generator `xᵢ − aᵢ` lies in `𝔪ₐ`, and more precisely `p − p(a)` always lies
in `𝔪ₐ` (a Taylor expansion at `a`), which pins down both the scalar action and the isomorphism
`Vrep a ≃ₗ[ℂ] ℂ`. -/

/-- The generators `Xᵢ − C aᵢ` of the maximal ideal `𝔪ₐ`. -/
private lemma X_sub_C_mem_maxIdeal {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    (X i - C (a i) : polyAlg n) ∈ maxIdeal a :=
  Ideal.subset_span ⟨i, rfl⟩

/-- **Taylor expansion at `a`.** For every polynomial `p`, the difference `p − p(a)` lies in the
maximal ideal `𝔪ₐ`. -/
private lemma sub_C_aeval_mem {n : ℕ} (a : Fin n → ℂ) (p : polyAlg n) :
    p - C (aeval a p) ∈ maxIdeal a := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [aeval_C]; simp
  | add p q hp hq =>
    have : (p + q) - C (aeval a (p + q))
        = (p - C (aeval a p)) + (q - C (aeval a q)) := by rw [map_add, map_add]; ring
    rw [this]; exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    have key : p * X i - C (aeval a (p * X i))
        = p * (X i - C (a i)) + C (a i) * (p - C (aeval a p)) := by
      simp only [map_mul, aeval_X]; ring
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (X_sub_C_mem_maxIdeal a i))
      (Ideal.mul_mem_left _ _ hp)

/-- The easy inclusion `𝔪ₐ ⊆ ker(aeval a)`: every element of the maximal ideal vanishes at `a`. -/
private lemma aeval_eq_zero_of_mem_maxIdeal {n : ℕ} (a : Fin n → ℂ) {p : polyAlg n}
    (hp : p ∈ maxIdeal a) : aeval a p = 0 := by
  have hle : maxIdeal a ≤ RingHom.ker (aeval a : polyAlg n →ₐ[ℂ] ℂ).toRingHom := by
    rw [maxIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  exact RingHom.mem_ker.mp (hle hp)

/-- An element of `𝔪ₐ` annihilates `Vrep a`. -/
private lemma smul_quot_eq_zero {n : ℕ} (a : Fin n → ℂ) {r : polyAlg n} (hr : r ∈ maxIdeal a)
    (v : Vrep a) : r • v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H p =>
    rw [show r • (Submodule.Quotient.mk p : Vrep a) = Submodule.Quotient.mk (r * p) from rfl,
      Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right p _ hr

/-- **The action is by the scalar `p(a)`.** Any `q ∈ A` acts on `Vrep a` as multiplication by the
complex number `aeval a q`. -/
lemma Vrep_smul_eq {n : ℕ} (a : Fin n → ℂ) (q : polyAlg n) (v : Vrep a) :
    q • v = aeval a q • v := by
  rw [← algebraMap_smul (polyAlg n) (aeval a q) v, MvPolynomial.algebraMap_eq, ← sub_eq_zero,
    ← sub_smul]
  exact smul_quot_eq_zero a (sub_C_aeval_mem a q) v

/-- Every class `[p]` equals `p(a) • [1]`, a Taylor expansion at the level of `Vrep a`. -/
private lemma mk_eq_aeval_smul_mk_one {n : ℕ} (a : Fin n → ℂ) (p : polyAlg n) :
    (Submodule.Quotient.mk p : Vrep a) = aeval a p • Submodule.Quotient.mk 1 := by
  rw [← algebraMap_smul (polyAlg n) (aeval a p) (Submodule.Quotient.mk (1 : polyAlg n)),
    MvPolynomial.algebraMap_eq]
  change (Submodule.Quotient.mk p : Vrep a) = Submodule.Quotient.mk (C (aeval a p) * 1)
  rw [Submodule.Quotient.eq, mul_one]
  exact sub_C_aeval_mem a p

/-- The distinguished generator `w₀ = [1] ∈ Vrep a`, which spans it over `ℂ`. -/
lemma quot_mk_one_ne_zero {n : ℕ} (a : Fin n → ℂ) :
    (Submodule.Quotient.mk (1 : polyAlg n) : Vrep a) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  intro h
  have := aeval_eq_zero_of_mem_maxIdeal a h
  simp at this

/-- **`Vrep a ≃ₗ[ℂ] ℂ`.** The 1-dimensional representation is 1-dimensional: the map
`c ↦ c • [1]` is a linear isomorphism `ℂ ≃ₗ[ℂ] Vrep a`, whose inverse gives the identification. -/
private noncomputable def VrepEquivC {n : ℕ} (a : Fin n → ℂ) : Vrep a ≃ₗ[ℂ] ℂ := by
  refine (LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℂ (Vrep a) (Submodule.Quotient.mk 1)) ⟨?_, ?_⟩).symm
  · -- injective
    intro c₁ c₂ h
    simp only [LinearMap.toSpanSingleton_apply] at h
    have hsub : (c₁ - c₂) • (Submodule.Quotient.mk 1 : Vrep a) = 0 := by
      rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with hc | hc
    · exact sub_eq_zero.mp hc
    · exact absurd hc (quot_mk_one_ne_zero a)
  · -- surjective
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H p =>
      refine ⟨aeval a p, ?_⟩
      simp only [LinearMap.toSpanSingleton_apply]
      exact (mk_eq_aeval_smul_mk_one a p).symm

private lemma VrepEquivC_symm_apply {n : ℕ} (a : Fin n → ℂ) (c : ℂ) :
    (VrepEquivC a).symm c = c • (Submodule.Quotient.mk 1 : Vrep a) := rfl

-- Keep `VrepEquivC` opaque downstream: its `ofBijective`/`symm` internals are huge and unfolding
-- them during `whnf`/`isDefEq` blows the heartbeat budget.
attribute [irreducible] VrepEquivC

/-- `w₀ = [1]` spans `Vrep a`: every `w` equals `(coord w) • w₀`. -/
private lemma VrepEquivC_smul_mk_one {n : ℕ} (a : Fin n → ℂ) (w : Vrep a) :
    (VrepEquivC a w) • (Submodule.Quotient.mk 1 : Vrep a) = w := by
  rw [← VrepEquivC_symm_apply, LinearEquiv.symm_apply_apply]

/-- The coordinate of `w₀ = [1]` is `1`. -/
private lemma VrepEquivC_mk_one {n : ℕ} (a : Fin n → ℂ) :
    VrepEquivC a (Submodule.Quotient.mk 1) = 1 := by
  rw [← LinearEquiv.eq_symm_apply, VrepEquivC_symm_apply, one_smul]

/-- **Cocycle → derivation.** A 1-cocycle `f` (with both weights `a`) gives the derivation
`p ↦ f p [1]`; the Leibniz rule is the cocycle identity, using that the action on `Vrep a` is by
the scalar `p(a)`. -/
private noncomputable def cocycleToDer {n : ℕ} (a : Fin n → ℂ)
    (f : cocycles ℂ (polyAlg n) (Vrep a) (Vrep a)) : Derivation ℂ (polyAlg n) (Vrep a) where
  toFun p := f.val p (Submodule.Quotient.mk 1)
  map_add' p q := by simp
  map_smul' c p := by simp
  map_one_eq_zero' := by
    have hc := LinearMap.congr_fun (f.property 1 1) (Submodule.Quotient.mk 1 : Vrep a)
    simp only [mul_one, LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe,
      one_smul] at hc
    have h2 : f.val 1 (Submodule.Quotient.mk 1) + f.val 1 (Submodule.Quotient.mk 1)
        = f.val 1 (Submodule.Quotient.mk 1) + 0 := by rw [add_zero]; exact hc.symm
    exact add_left_cancel h2
  leibniz' p q := by
    have hc := LinearMap.congr_fun (f.property p q) (Submodule.Quotient.mk 1 : Vrep a)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
    change f.val (p * q) (Submodule.Quotient.mk 1)
      = p • f.val q (Submodule.Quotient.mk 1) + q • f.val p (Submodule.Quotient.mk 1)
    rw [hc, Vrep_smul_eq a q (Submodule.Quotient.mk 1), map_smul,
      ← Vrep_smul_eq a q (f.val p (Submodule.Quotient.mk 1))]

private lemma cocycleToDer_apply {n : ℕ} (a : Fin n → ℂ)
    (f : cocycles ℂ (polyAlg n) (Vrep a) (Vrep a)) (p : polyAlg n) :
    cocycleToDer a f p = f.val p (Submodule.Quotient.mk 1) := rfl

/-- **Derivation → cocycle map.** A derivation `D` gives the bundled map `p ↦ (D p)(a) • id`, i.e.
the endomorphism of `Vrep a` that is scalar multiplication by the coordinate `VrepEquivC a (D p)`.
Since `Vrep a` is 1-dimensional this equals `w ↦ (coord w) • D p`. -/
private noncomputable def derToCocycleMap {n : ℕ} (a : Fin n → ℂ)
    (D : Derivation ℂ (polyAlg n) (Vrep a)) : polyAlg n →ₗ[ℂ] (Vrep a →ₗ[ℂ] Vrep a) where
  toFun p := VrepEquivC a (D p) • (LinearMap.id : Vrep a →ₗ[ℂ] Vrep a)
  map_add' p q := by simp only [map_add, add_smul]
  map_smul' c p := by
    have hD : D (c • p) = c • D p := D.toLinearMap.map_smul c p
    rw [hD, map_smul (VrepEquivC a), RingHom.id_apply, smul_eq_mul, mul_smul]

private lemma derToCocycleMap_apply {n : ℕ} (a : Fin n → ℂ)
    (D : Derivation ℂ (polyAlg n) (Vrep a)) (p : polyAlg n) (w : Vrep a) :
    derToCocycleMap a D p w = VrepEquivC a (D p) • w := by
  simp only [derToCocycleMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq]

/-- Any endomorphism of the 1-dimensional space `Vrep a` is scalar multiplication by the
coordinate of its value on `[1]`. -/
private lemma end_eq_coord_smul {n : ℕ} (a : Fin n → ℂ) (g : Vrep a →ₗ[ℂ] Vrep a) (w : Vrep a) :
    VrepEquivC a (g (Submodule.Quotient.mk 1)) • w = g w := by
  apply (VrepEquivC a).injective
  rw [map_smul, smul_eq_mul]
  conv_rhs => rw [← VrepEquivC_smul_mk_one a w, map_smul, map_smul, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
-- The `Vrep a` quotient-module instances make the elaboration of the cocycle identity heavy.
private lemma derToCocycle_isCocycle {n : ℕ} (a : Fin n → ℂ)
    (D : Derivation ℂ (polyAlg n) (Vrep a)) :
    IsCocycle ℂ (polyAlg n) (Vrep a) (Vrep a) (derToCocycleMap a D) := by
  intro p q
  refine LinearMap.ext fun w => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, derToCocycleMap_apply, Algebra.lsmul_coe]
  rw [Derivation.leibniz, map_add, add_smul]
  congr 1
  · rw [Vrep_smul_eq a p (D q), map_smul, smul_eq_mul,
      Vrep_smul_eq a p (VrepEquivC a (D q) • w), smul_smul]
  · rw [Vrep_smul_eq a q (D p), map_smul, smul_eq_mul, Vrep_smul_eq a q w, smul_smul, mul_comm]

set_option maxHeartbeats 1000000 in
-- Assembling the equivalence repeatedly typechecks the `Vrep a` quotient-module instances.
private noncomputable def cocyclesEquivDer {n : ℕ} (a : Fin n → ℂ) :
    cocycles ℂ (polyAlg n) (Vrep a) (Vrep a) ≃ₗ[ℂ] Derivation ℂ (polyAlg n) (Vrep a) where
  toFun := cocycleToDer a
  invFun D := ⟨derToCocycleMap a D, derToCocycle_isCocycle a D⟩
  map_add' f g := by
    apply Derivation.ext; intro p
    rw [cocycleToDer_apply, Derivation.add_apply, cocycleToDer_apply, cocycleToDer_apply]
    rfl
  map_smul' c f := by
    apply Derivation.ext; intro p
    rw [cocycleToDer_apply, Derivation.smul_apply, cocycleToDer_apply]
    rfl
  left_inv f := by
    apply Subtype.ext
    refine LinearMap.ext fun p => LinearMap.ext fun w => ?_
    rw [derToCocycleMap_apply, cocycleToDer_apply]
    exact end_eq_coord_smul a (f.val p) w
  right_inv D := by
    apply Derivation.ext; intro p
    change derToCocycleMap a D p (Submodule.Quotient.mk 1) = D p
    rw [derToCocycleMap_apply]
    exact VrepEquivC_smul_mk_one a (D p)

/-- Coboundaries vanish when source and target weights agree: `dX = 0` since the two scalar actions
of `p` on `Vrep a` coincide. -/
private lemma coboundaries_eq_bot {n : ℕ} (a : Fin n → ℂ) :
    coboundaries ℂ (polyAlg n) (Vrep a) (Vrep a) = ⊥ := by
  rw [coboundaries, Submodule.span_eq_bot]
  rintro _ ⟨X, rfl⟩
  refine LinearMap.ext fun p => LinearMap.ext fun w => ?_
  simp only [coboundaryOf_apply, LinearMap.zero_apply]
  rw [Vrep_smul_eq a p w, map_smul X, Vrep_smul_eq a p (X w), sub_self]

/-- **Problem 3.9.2(a), equal weights.** `Ext¹(Vₐ, Vₐ) ≅ ℂⁿ`: self-extensions of the
1-dimensional rep are classified by the `n` "nilpotent directions" `xᵢ`. -/
theorem ext1_self {n : ℕ} (a : Fin n → ℂ) :
    Nonempty (Ext1 ℂ (polyAlg n) (Vrep a) (Vrep a) ≃ₗ[ℂ] (Fin n → ℂ)) := by
  have hbot : (coboundaries ℂ (polyAlg n) (Vrep a) (Vrep a)).submoduleOf
      (cocycles ℂ (polyAlg n) (Vrep a) (Vrep a)) = ⊥ := by
    rw [coboundaries_eq_bot, Submodule.submoduleOf, Submodule.comap_bot, Submodule.ker_subtype]
  refine ⟨?_⟩
  exact (Submodule.quotEquivOfEqBot _ hbot).trans
    ((cocyclesEquivDer a).trans
      (((MvPolynomial.mkDerivationEquiv ℂ).symm).trans
        (LinearEquiv.piCongrRight (fun _ => VrepEquivC a))))

/-- **Rigidity for twisted derivations.** An `(α, β)`-twisted derivation `h`, i.e. a linear map
with `h(pq) = β(p) • h(q) + α(q) • h(p)`, that vanishes on all generators `Xᵢ` is identically
zero. Proof by the three-case `MvPolynomial` induction. -/
private lemma twisted_deriv_eq_zero {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (α β : polyAlg n →ₐ[ℂ] ℂ) (h : polyAlg n →ₗ[ℂ] M)
    (hL : ∀ p q, h (p * q) = β p • h q + α q • h p) (hgen : ∀ i, h (X i) = 0) : h = 0 := by
  have h1 : h 1 = 0 := by
    have hone := hL 1 1
    simp only [mul_one, map_one, one_smul] at hone
    have h2 : h 1 + h 1 = h 1 + 0 := by rw [add_zero]; exact hone.symm
    exact add_left_cancel h2
  refine LinearMap.ext fun p => ?_
  rw [LinearMap.zero_apply]
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show (C c : polyAlg n) = c • 1 by rw [smul_eq_C_mul, mul_one], map_smul, h1, smul_zero]
  | add p q hp hq => rw [map_add, hp, hq, add_zero]
  | mul_X p i hp => rw [hL, hgen, hp, smul_zero, smul_zero, add_zero]

/-- **Problem 3.9.2(a), distinct weights.** `Ext¹(Vₐ, V_b) = 0` when `a ≠ b`: any extension
splits because some `xⱼ` has distinct eigenvalues `aⱼ ≠ bⱼ`. -/
theorem ext1_subsingleton_of_ne {n : ℕ} (a b : Fin n → ℂ) (hab : a ≠ b) :
    Subsingleton (Ext1 ℂ (polyAlg n) (Vrep b) (Vrep a)) := by
  -- It suffices that every cocycle is a coboundary, i.e. `coboundaries.submoduleOf cocycles = ⊤`.
  rw [Ext1, Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro f
  rw [Submodule.submoduleOf, Submodule.mem_comap, mem_coboundaries_iff]
  -- The map `p ↦ f p [1]`, a `(aeval a, aeval b)`-twisted derivation into `V_b`.
  set h : polyAlg n →ₗ[ℂ] Vrep b := f.val.flip (Submodule.Quotient.mk 1) with hh
  have h_apply : ∀ p, h p = f.val p (Submodule.Quotient.mk 1) := fun p => rfl
  have hL : ∀ p q, h (p * q) = aeval b p • h q + aeval a q • h p := by
    intro p q
    have hc := LinearMap.congr_fun (f.property p q) (Submodule.Quotient.mk 1 : Vrep a)
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Algebra.lsmul_coe] at hc
    rw [h_apply, h_apply, h_apply, hc, Vrep_smul_eq b p (f.val q (Submodule.Quotient.mk 1)),
      Vrep_smul_eq a q (Submodule.Quotient.mk 1), map_smul (f.val p)]
  -- Commutativity of `A` forces the generator-values to be proportional to `b - a`.
  have hcomm : ∀ i j, (b i - a i) • h (X j) = (b j - a j) • h (X i) := by
    intro i j
    have e1 := hL (X i) (X j)
    have e2 := hL (X j) (X i)
    rw [aeval_X, aeval_X] at e1 e2
    have heq : b i • h (X j) + a j • h (X i) = b j • h (X i) + a i • h (X j) := by
      rw [← e1, ← e2, mul_comm]
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]; exact heq
  -- Pick an index where the weights differ and set the proportionality constant `ξ`.
  obtain ⟨jj, hjj⟩ : ∃ j, a j ≠ b j := by
    by_contra hcon; push Not at hcon; exact hab (funext hcon)
  have hbaj : (b jj - a jj) ≠ 0 := sub_ne_zero.mpr (Ne.symm hjj)
  set ξ : Vrep b := (b jj - a jj)⁻¹ • h (X jj) with hξ
  -- The candidate coboundary datum `cb p = (b(p) - a(p)) • ξ`.
  set cbMap : polyAlg n →ₗ[ℂ] Vrep b :=
    (LinearMap.toSpanSingleton ℂ (Vrep b) ξ).comp ((aeval b).toLinearMap - (aeval a).toLinearMap)
    with hcbMap
  have cb_apply : ∀ p, cbMap p = (aeval b p - aeval a p) • ξ := by
    intro p; rw [hcbMap]; simp [LinearMap.toSpanSingleton_apply]
  -- `h - cb` is twisted and vanishes on generators, hence zero: `h = cb`.
  have he : h - cbMap = 0 := by
    refine twisted_deriv_eq_zero (aeval a) (aeval b) (h - cbMap) ?_ ?_
    · intro p q
      simp only [LinearMap.sub_apply]
      rw [hL p q, cb_apply, cb_apply, cb_apply, map_mul, map_mul]
      module
    · intro i
      simp only [LinearMap.sub_apply]
      rw [cb_apply, aeval_X, aeval_X, hξ, smul_smul, mul_comm, ← smul_smul, hcomm i jj, smul_smul,
        inv_mul_cancel₀ hbaj, one_smul, sub_self]
  have key : ∀ p, (aeval b p - aeval a p) • ξ = f.val p (Submodule.Quotient.mk 1) := by
    intro p
    have hz := LinearMap.congr_fun he p
    simp only [LinearMap.sub_apply, LinearMap.zero_apply] at hz
    rw [h_apply, cb_apply, sub_eq_zero] at hz
    exact hz.symm
  -- Assemble the coboundary map `X : W → V`, `w ↦ coord(w) • ξ`.
  set X : Vrep a →ₗ[ℂ] Vrep b :=
    (LinearMap.toSpanSingleton ℂ (Vrep b) ξ).comp (VrepEquivC a).toLinearMap with hX
  have X_apply : ∀ w, X w = VrepEquivC a w • ξ := by
    intro w; rw [hX]; simp [LinearMap.toSpanSingleton_apply]
  refine ⟨X, ?_⟩
  refine LinearMap.ext fun p => LinearMap.ext fun w => ?_
  conv_rhs => rw [← VrepEquivC_smul_mk_one a w, map_smul]
  rw [coboundaryOf_apply, Vrep_smul_eq b p (X w), Vrep_smul_eq a p w, map_smul X, ← sub_smul,
    X_apply, smul_comm, key p]
  rfl

/-! ### Classification of 2-dimensional representations

Over the algebraically closed field `ℂ`, any finite-dimensional representation of the commutative
algebra `A = ℂ[x₁, …, xₙ]` has a common eigenvector for all the generators `xᵢ`. Peeling one off
exhibits a 2-dimensional representation as an extension of two 1-dimensional ones. -/

/-- **Eigenvalue relation is multiplicative.** If every generator `Xᵢ` acts on `m₀` by the scalar
`cᵢ`, then any polynomial `p` acts by `p(c) = aeval c p`. Mirrors `Vrep_smul_eq`. -/
lemma eigen_smul_eq {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (polyAlg n) M] [IsScalarTower ℂ (polyAlg n) M]
    (c : Fin n → ℂ) (m₀ : M) (hc : ∀ i, (X i : polyAlg n) • m₀ = c i • m₀) (p : polyAlg n) :
    p • m₀ = aeval c p • m₀ := by
  haveI : SMulCommClass (polyAlg n) ℂ M := ⟨fun q r m => by
    rw [← algebraMap_smul (polyAlg n) r m, ← mul_smul, ← algebraMap_smul (polyAlg n) r (q • m),
      ← mul_smul, Algebra.commutes]⟩
  induction p using MvPolynomial.induction_on with
  | C x =>
    rw [aeval_C, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
    rw [algebraMap_smul]
  | add p q hp hq => rw [add_smul, hp, hq, ← add_smul, ← map_add]
  | mul_X p i hp => rw [mul_smul, hc i, smul_comm, hp, smul_smul, map_mul, aeval_X, mul_comm]

/-- A finite-dimensional 1-dimensional `A`-module `M` on which every generator `Xᵢ` acts on the
spanning vector `m₀` by the scalar `cᵢ` is isomorphic, as an `A`-module, to `Vrep c`. -/
noncomputable def oneDim_iso_Vrep {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (polyAlg n) M] [IsScalarTower ℂ (polyAlg n) M] [FiniteDimensional ℂ M]
    (c : Fin n → ℂ) (m₀ : M) (hm₀ : m₀ ≠ 0) (hdim : Module.finrank ℂ M = 1)
    (hc : ∀ i, (X i : polyAlg n) • m₀ = c i • m₀) :
    M ≃ₗ[polyAlg n] Vrep c := by
  let φ : polyAlg n →ₗ[polyAlg n] M := LinearMap.toSpanSingleton (polyAlg n) M m₀
  have hφ : ∀ p, φ p = p • m₀ := fun p => rfl
  have hker : LinearMap.ker φ = maxIdeal c := by
    ext p
    simp only [LinearMap.mem_ker, hφ]
    rw [eigen_smul_eq c m₀ hc p]
    constructor
    · intro h
      have hp0 : aeval c p = 0 := by
        rcases smul_eq_zero.mp h with h1 | h1
        · exact h1
        · exact absurd h1 hm₀
      have hmem := sub_C_aeval_mem c p
      rwa [hp0, map_zero, sub_zero] at hmem
    · intro h
      rw [aeval_eq_zero_of_mem_maxIdeal c h, zero_smul]
  have hsurj : Function.Surjective φ := by
    intro m
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' m₀ hm₀).mp hdim m
    refine ⟨C d, ?_⟩
    rw [hφ, ← hd, ← MvPolynomial.algebraMap_eq, algebraMap_smul]
  exact (LinearMap.quotKerEquivOfSurjective φ hsurj).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)

/-- On a 1-dimensional `A`-module every generator acts by a scalar, so any nonzero vector is a
common eigenvector. -/
private lemma oneDim_common_eigen {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    [Module (polyAlg n) M] [IsScalarTower ℂ (polyAlg n) M] [FiniteDimensional ℂ M]
    (hdim : Module.finrank ℂ M = 1) :
    ∃ (a : Fin n → ℂ) (m₀ : M), m₀ ≠ 0 ∧ ∀ i, (X i : polyAlg n) • m₀ = a i • m₀ := by
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hspan := (finrank_eq_one_iff_of_nonzero' m₀ hm₀).mp hdim
  have key : ∀ i, ∃ c : ℂ, (X i : polyAlg n) • m₀ = c • m₀ := by
    intro i
    obtain ⟨c, hc⟩ := hspan ((X i : polyAlg n) • m₀)
    exact ⟨c, hc.symm⟩
  choose a ha using key
  exact ⟨a, m₀, hm₀, ha⟩

/-- **Existence of a common eigenvector.** Over `ℂ`, any 2-dimensional representation of
`ℂ[x₁,…,xₙ]` has a nonzero vector `v` that is a simultaneous eigenvector for all the generators
`Xᵢ`. Either every generator already acts by a scalar, or some generator `X_j` has a proper
eigenspace `E` (necessarily 1-dimensional), and the commuting generators preserve `E`. -/
lemma exists_common_eigenvector {n : ℕ} (U : Type)
    [AddCommGroup U] [Module ℂ U] [Module (polyAlg n) U] [IsScalarTower ℂ (polyAlg n) U]
    [FiniteDimensional ℂ U] (hdim : Module.finrank ℂ U = 2) :
    ∃ (b : Fin n → ℂ) (v : U), v ≠ 0 ∧ ∀ i, (X i : polyAlg n) • v = b i • v := by
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : SMulCommClass (polyAlg n) ℂ U := ⟨fun q r m => by
    rw [← algebraMap_smul (polyAlg n) r m, ← mul_smul, ← algebraMap_smul (polyAlg n) r (q • m),
      ← mul_smul, Algebra.commutes]⟩
  by_cases hall : ∀ i, ∃ c : ℂ, ∀ u : U, (X i : polyAlg n) • u = c • u
  · choose b hb using hall
    obtain ⟨v, hv⟩ := exists_ne (0 : U)
    exact ⟨b, v, hv, fun i => hb i v⟩
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    let T : Module.End ℂ U :=
      { toFun := fun u => (X j : polyAlg n) • u
        map_add' := fun a b => smul_add _ _ _
        map_smul' := fun r u => by
          simp only [RingHom.id_apply]
          exact smul_comm (X j : polyAlg n) r u }
    have hTapp : ∀ u, T u = (X j : polyAlg n) • u := fun u => rfl
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v₀, hv₀⟩ := hμ.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff] at hv₀
    obtain ⟨hv₀mem, hv₀ne⟩ := hv₀
    rw [Module.End.mem_eigenspace_iff, hTapp] at hv₀mem
    set E := Module.End.eigenspace T μ with hE
    have hEtop : E ≠ ⊤ := by
      intro hEq
      obtain ⟨u, hu⟩ := hj μ
      apply hu
      have hmem : u ∈ E := hEq ▸ Submodule.mem_top
      rw [hE, Module.End.mem_eigenspace_iff, hTapp] at hmem
      exact hmem
    have hv₀E : v₀ ∈ E := by rw [hE, Module.End.mem_eigenspace_iff, hTapp]; exact hv₀mem
    have hEbot : E ≠ ⊥ := by rw [Submodule.ne_bot_iff]; exact ⟨v₀, hv₀E, hv₀ne⟩
    have hlt_bot : (⊥ : Submodule ℂ U) < E := bot_lt_iff_ne_bot.mpr hEbot
    have hlt_top : E < ⊤ := lt_top_iff_ne_top.mpr hEtop
    have h0 : 0 < Module.finrank ℂ E := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt_bot
      rwa [finrank_bot] at h
    have h2 : Module.finrank ℂ E < 2 := by
      have h := Submodule.finrank_lt_finrank_of_lt hlt_top
      rw [finrank_top, hdim] at h; exact h
    have hE1 : Module.finrank ℂ E = 1 := by omega
    have hv₀E' : (⟨v₀, hv₀E⟩ : E) ≠ 0 := by rw [Ne, Submodule.mk_eq_zero]; exact hv₀ne
    have hspanE := (finrank_eq_one_iff_of_nonzero' (⟨v₀, hv₀E⟩ : E) hv₀E').mp hE1
    have key : ∀ i, ∃ c : ℂ, (X i : polyAlg n) • v₀ = c • v₀ := by
      intro i
      have hi : (X i : polyAlg n) • v₀ ∈ E := by
        rw [hE, Module.End.mem_eigenspace_iff, hTapp, ← mul_smul, mul_comm, mul_smul, hv₀mem,
          smul_comm]
      obtain ⟨c, hc⟩ := hspanE ⟨(X i : polyAlg n) • v₀, hi⟩
      refine ⟨c, ?_⟩
      have hval := congrArg (Subtype.val) hc
      simp only [SetLike.val_smul] at hval
      exact hval.symm
    choose b hb using key
    exact ⟨b, v₀, hv₀ne, hb⟩

/-- **Problem 3.9.2(a), classification of 2-dimensional representations.** Every
2-dimensional representation `U` of `ℂ[x₁, …, xₙ]` is an extension of two 1-dimensional
representations: there is a pair of weights `a, b` and a subrepresentation `S ≅ V_b` with
quotient `U ⧸ S ≅ Vₐ`. Combined with the `Ext¹` computation above, this classifies the
2-dimensional representations. -/
theorem two_dim_is_extension {n : ℕ} (U : Type)
    [AddCommGroup U] [Module ℂ U] [Module (polyAlg n) U] [IsScalarTower ℂ (polyAlg n) U]
    [FiniteDimensional ℂ U] (hdim : Module.finrank ℂ U = 2) :
    ∃ (a b : Fin n → ℂ) (S : Submodule (polyAlg n) U),
      Nonempty (S ≃ₗ[polyAlg n] Vrep b) ∧ Nonempty ((U ⧸ S) ≃ₗ[polyAlg n] Vrep a) := by
  obtain ⟨b, v, hv, hb⟩ := exists_common_eigenvector (n := n) U hdim
  set S : Submodule (polyAlg n) U := Submodule.span (polyAlg n) {v} with hS
  have hvS : v ∈ S := by rw [hS]; exact Submodule.mem_span_singleton_self v
  -- `S.restrictScalars ℂ` is the ℂ-span of `v`, hence 1-dimensional.
  have hSspan : S.restrictScalars ℂ = Submodule.span ℂ {v} := by
    apply le_antisymm
    · rw [SetLike.le_def]
      intro x hx
      rw [Submodule.restrictScalars_mem, hS, Submodule.mem_span_singleton] at hx
      obtain ⟨p, rfl⟩ := hx
      rw [eigen_smul_eq b v hb p]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe, Submodule.restrictScalars_mem]
      exact hvS
  have hS'fin : Module.finrank ℂ (S.restrictScalars ℂ) = 1 := by
    rw [hSspan]; exact finrank_span_singleton hv
  have hSfin : Module.finrank ℂ ↥S = 1 := hS'fin
  haveI : FiniteDimensional ℂ ↥S :=
    inferInstanceAs (FiniteDimensional ℂ ↥(S.restrictScalars ℂ))
  -- S ≅ Vrep b as a polyAlg-module.
  have hSiso : Nonempty (↥S ≃ₗ[polyAlg n] Vrep b) := by
    refine ⟨oneDim_iso_Vrep b (⟨v, hvS⟩ : ↥S) ?_ hSfin ?_⟩
    · rw [Ne, Submodule.mk_eq_zero]; exact hv
    · intro i
      apply Subtype.ext
      change (X i : polyAlg n) • v = b i • v
      exact hb i
  -- U ⧸ S is 1-dimensional.
  have hQfin : Module.finrank ℂ (U ⧸ S) = 1 := by
    have e := Submodule.Quotient.restrictScalarsEquiv ℂ S
    have hadd := Submodule.finrank_quotient_add_finrank (S.restrictScalars ℂ)
    rw [e.finrank_eq, hS'fin, hdim] at hadd
    omega
  -- U ⧸ S ≅ Vrep a as a polyAlg-module.
  obtain ⟨a, m₀, hm₀, ha⟩ := oneDim_common_eigen (n := n) (M := U ⧸ S) hQfin
  exact ⟨a, b, S, hSiso, ⟨oneDim_iso_Vrep a m₀ hm₀ hQfin ha⟩⟩

/-! ## Part (b): the algebra with zero multiplication `B = ℂ⟨x₁,…,xₙ⟩/(xᵢxⱼ)` -/

/-- The defining relations of `B`: every product `xᵢ xⱼ` of generators is zero. -/
inductive BRel (n : ℕ) : FreeAlgebra ℂ (Fin n) → FreeAlgebra ℂ (Fin n) → Prop
  | mul (i j : Fin n) :
      BRel n (FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j) 0

/-- The algebra `B = ℂ⟨x₁, …, xₙ⟩ / (xᵢxⱼ = 0)`, the free algebra on `n` generators modulo
the two-sided ideal generated by all products of generators, constructed as a `RingQuot`. -/
abbrev zeroMulAlg (n : ℕ) : Type := RingQuot (BRel n)

/-! ### The family of indecomposable `B`-modules

For `n > 1` we exhibit a family `Mₖ = ℂ²` (`k ∈ ℕ`) of pairwise nonisomorphic indecomposable
`B`-modules. On `Mₖ` the generator `x₀` acts by the square-zero nilpotent `N : (a,b) ↦ (0,a)`,
`x₁` acts by `k • N`, and the remaining `xᵢ` act by `0`. Every product of generators acts by
`N² = 0`, so this is a `B = zeroMulAlg n`-module. The socle line `ℂ·v` (with
`v = (0,1) = N u`, `u = (1,0)`) sits inside every nonzero submodule, forcing indecomposability;
the scalar `k` (the ratio of the `x₁`- and `x₀`-actions on the socle) is preserved by any module
isomorphism, forcing pairwise non-isomorphism.

The carriers `Cyc n k` are per-index type copies of `ℂ²`, so each index `k` carries its own
`B`-action as a canonical instance (distinct types keep the two module structures unambiguous
when comparing `Mₖ` and `Mₗ`). -/

/-- The distinguished socle vector `v = (0,1) ∈ ℂ²` (raw). -/
def socleVecR : Fin 2 → ℂ := ![0, 1]

/-- The cyclic vector `u = (1,0) ∈ ℂ²` (raw), with `N u = v`. -/
def cycVecR : Fin 2 → ℂ := ![1, 0]

/-- The square-zero nilpotent `N : (a,b) ↦ (0,a)` on `ℂ²`. -/
noncomputable def nilOpR : Module.End ℂ (Fin 2 → ℂ) where
  toFun m := m 0 • socleVecR
  map_add' a b := by simp [add_smul]
  map_smul' c m := by simp [mul_smul]

@[simp] lemma nilOpR_apply (m : Fin 2 → ℂ) : nilOpR m = m 0 • socleVecR := rfl

lemma nilOpR_sq : nilOpR * nilOpR = (0 : Module.End ℂ (Fin 2 → ℂ)) := by
  ext m i
  fin_cases i <;> simp [Module.End.mul_apply, nilOpR_apply, socleVecR]

/-- The carrier of the `k`-th module: a type copy of `ℂ²` so each index carries its own action. -/
def Cyc (n k : ℕ) : Type := Fin 2 → ℂ

instance (n k : ℕ) : AddCommGroup (Cyc n k) := inferInstanceAs (AddCommGroup (Fin 2 → ℂ))
noncomputable instance (n k : ℕ) : Module ℂ (Cyc n k) := inferInstanceAs (Module ℂ (Fin 2 → ℂ))
instance (n k : ℕ) : Nontrivial (Cyc n k) := inferInstanceAs (Nontrivial (Fin 2 → ℂ))

/-- The socle vector `v` inside `Cyc n k`. -/
def socleVec (n k : ℕ) : Cyc n k := (socleVecR : Fin 2 → ℂ)

/-- The cyclic vector `u` inside `Cyc n k`. -/
def cycVec (n k : ℕ) : Cyc n k := (cycVecR : Fin 2 → ℂ)

/-- The square-zero nilpotent `N` on `Cyc n k`. -/
noncomputable def nilOp (n k : ℕ) : Module.End ℂ (Cyc n k) := nilOpR

@[simp] lemma nilOp_apply (n k : ℕ) (m : Cyc n k) : nilOp n k m = m 0 • socleVec n k := rfl

lemma nilOp_sq (n k : ℕ) : nilOp n k * nilOp n k = (0 : Module.End ℂ (Cyc n k)) := nilOpR_sq

lemma socleVec_ne_zero (n k : ℕ) : socleVec n k ≠ (0 : Cyc n k) := by
  have h : (socleVecR : Fin 2 → ℂ) ≠ 0 := by
    intro h; simpa [socleVecR] using congrFun h 1
  exact h

/-- The weight of generator `xᵢ` in the `k`-th module: `1` for `i = 0`, `k` for `i = 1`, and `0`
otherwise. -/
def wt (k : ℕ) {n : ℕ} (i : Fin n) : ℂ :=
  if (i : ℕ) = 0 then 1 else if (i : ℕ) = 1 then (k : ℂ) else 0

@[simp] lemma wt_zero (k : ℕ) {n : ℕ} [NeZero n] : wt k (0 : Fin n) = 1 := by simp [wt]

lemma wt_one (k : ℕ) {n : ℕ} [NeZero n] (hn : 1 < n) : wt k (1 : Fin n) = (k : ℂ) := by
  have h1 : ((1 : Fin n) : ℕ) = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt hn
  unfold wt
  rw [h1]
  norm_num

/-- The image of generator `xᵢ` in `End (Cyc n k)` for the `k`-th module: `wt k i • N`. -/
noncomputable def genImg (n k : ℕ) (i : Fin n) : Module.End ℂ (Cyc n k) := wt k i • nilOp n k

lemma genImg_mul (n k : ℕ) (i j : Fin n) : genImg n k i * genImg n k j = 0 := by
  simp only [genImg, smul_mul_assoc, mul_smul_comm, nilOp_sq, smul_zero]

/-- The `k`-th representation of the free algebra `ℂ⟨x₁,…,xₙ⟩` on `Cyc n k`. -/
noncomputable def freeRep (n k : ℕ) :
    FreeAlgebra ℂ (Fin n) →ₐ[ℂ] Module.End ℂ (Cyc n k) :=
  FreeAlgebra.lift ℂ (genImg n k)

lemma freeRep_rel (n k : ℕ) : ∀ ⦃a b⦄, BRel n a b → freeRep n k a = freeRep n k b := by
  intro a b hab
  cases hab with
  | mul i j =>
    simp only [freeRep, map_mul, map_zero, FreeAlgebra.lift_ι_apply]
    exact genImg_mul n k i j

/-- The `k`-th representation of `B = zeroMulAlg n` on `Cyc n k`. -/
noncomputable def rep (n k : ℕ) : zeroMulAlg n →ₐ[ℂ] Module.End ℂ (Cyc n k) :=
  RingQuot.liftAlgHom ℂ ⟨freeRep n k, freeRep_rel n k⟩

/-- The generator `xᵢ ∈ B`. -/
noncomputable def gen (n : ℕ) (i : Fin n) : zeroMulAlg n :=
  RingQuot.mkAlgHom ℂ (BRel n) (FreeAlgebra.ι ℂ i)

lemma rep_gen (n k : ℕ) (i : Fin n) : rep n k (gen n i) = wt k i • nilOp n k := by
  simp only [rep, gen, RingQuot.liftAlgHom_mkAlgHom_apply, freeRep, FreeAlgebra.lift_ι_apply,
    genImg]

/-- The `B`-module structure on `Cyc n k` given by the `k`-th representation. -/
noncomputable instance instModuleCyc (n k : ℕ) : Module (zeroMulAlg n) (Cyc n k) :=
  Module.compHom (Cyc n k) (rep n k).toRingHom

/-- Under the `k`-th module structure, `algebraMap ℂ B c` acts by the base scalar `c`. -/
lemma rep_algebraMap_smul (n k : ℕ) (c : ℂ) (y : Cyc n k) :
    rep n k (algebraMap ℂ (zeroMulAlg n) c) y = c • y := by
  rw [AlgHom.commutes, Module.algebraMap_end_apply]

/-- **Problem 3.9.2(b).** For `n > 1`, the algebra `B` has infinitely many nonisomorphic
indecomposable representations: there is a family `M : ℕ → Type` of pairwise nonisomorphic
indecomposable `B`-modules. -/
theorem infinitely_many_indecomposables {n : ℕ} (hn : 1 < n) :
    ∃ (M : ℕ → Type) (_ : ∀ k, AddCommGroup (M k)) (_ : ∀ k, Module (zeroMulAlg n) (M k)),
      (∀ k, Etingof.IsIndecomposable (zeroMulAlg n) (M k)) ∧
      (∀ k l, Nonempty ((M k) ≃ₗ[zeroMulAlg n] (M l)) → k = l) := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨fun k => Cyc n k, fun _ => inferInstance, fun _ => inferInstance, ?_, ?_⟩
  · -- Each `Mₖ` is indecomposable.
    intro k
    -- A `B`-submodule is closed under the base scalar action of `ℂ`.
    have csmul_mem : ∀ (c : ℂ) (x : Cyc n k) (W : Submodule (zeroMulAlg n) (Cyc n k)),
        x ∈ W → c • x ∈ W := by
      intro c x W hx
      have hc : c • x = (algebraMap ℂ (zeroMulAlg n) c) • x := (rep_algebraMap_smul n k c x).symm
      rw [hc]; exact W.smul_mem _ hx
    -- Every nonzero `B`-submodule contains the socle vector `v`.
    have mem_of_ne_bot : ∀ W : Submodule (zeroMulAlg n) (Cyc n k), W ≠ ⊥ → socleVec n k ∈ W := by
      intro W hW
      obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW
      by_cases h0 : w 0 = 0
      · -- `w` lies on the socle line already.
        set a : ℂ := w 1 with ha
        have hwv : w = a • socleVec n k := by
          funext j; fin_cases j
          · change w 0 = a • socleVec n k 0
            simp [socleVec, socleVecR, h0]
          · change w 1 = a • socleVec n k 1
            simp [socleVec, socleVecR, ha]
        have hw1 : a ≠ 0 := fun h1 => hw0 (by rw [hwv, h1, zero_smul])
        have hv : socleVec n k = a⁻¹ • w := by
          rw [hwv, smul_smul, inv_mul_cancel₀ hw1, one_smul]
        rw [hv]; exact csmul_mem _ _ _ hwW
      · -- Apply `x₀` (acting as `N`) to reach the socle line.
        have hxw : (gen n (0 : Fin n)) • w ∈ W := W.smul_mem _ hwW
        have hact : (gen n (0 : Fin n)) • w = w 0 • socleVec n k := by
          change rep n k (gen n 0) w = w 0 • socleVec n k
          rw [rep_gen, wt_zero]; simp
        rw [hact] at hxw
        have hv : socleVec n k = (w 0)⁻¹ • (w 0 • socleVec n k) := by
          rw [smul_smul, inv_mul_cancel₀ h0, one_smul]
        rw [hv]; exact csmul_mem _ _ _ hxw
    refine ⟨inferInstance, ?_⟩
    intro W₁ W₂ hcompl
    by_contra hcon
    push Not at hcon
    obtain ⟨hW1, hW2⟩ := hcon
    have hv : socleVec n k ∈ W₁ ⊓ W₂ := ⟨mem_of_ne_bot _ hW1, mem_of_ne_bot _ hW2⟩
    rw [disjoint_iff.mp hcompl.disjoint] at hv
    exact socleVec_ne_zero n k ((Submodule.mem_bot _).mp hv)
  · -- The modules are pairwise nonisomorphic: the socle scalar `k` is an isomorphism invariant.
    rintro k l ⟨φ⟩
    -- The equivalence intertwines the representation actions.
    have hmap : ∀ (r : zeroMulAlg n) (x : Cyc n k), φ (rep n k r x) = rep n l r (φ x) :=
      fun r x => map_smul φ r x
    -- `φ` is `ℂ`-linear, since `ℂ` acts through `algebraMap ℂ B`.
    have philin : ∀ (c : ℂ) (x : Cyc n k), φ (c • x) = c • φ x := by
      intro c x
      have h := hmap (algebraMap ℂ (zeroMulAlg n) c) x
      rw [rep_algebraMap_smul, rep_algebraMap_smul] at h
      exact h
    -- `φ` commutes with the `x₀`-action `N`.
    have hN : ∀ x, φ (nilOp n k x) = nilOp n l (φ x) := by
      intro x
      have h := hmap (gen n (0 : Fin n)) x
      rw [rep_gen, rep_gen, wt_zero, wt_zero, LinearMap.smul_apply, LinearMap.smul_apply,
        one_smul, one_smul] at h
      exact h
    -- The `x₁`-action scales by `k` on the source and by `l` on the target.
    have hK : φ ((k : ℂ) • nilOp n k (cycVec n k)) = (l : ℂ) • nilOp n l (φ (cycVec n k)) := by
      have h := hmap (gen n (1 : Fin n)) (cycVec n k)
      rw [rep_gen, rep_gen, wt_one _ hn, wt_one _ hn, LinearMap.smul_apply,
        LinearMap.smul_apply] at h
      exact h
    have hNu : nilOp n k (cycVec n k) = socleVec n k := by
      simp [nilOp_apply, cycVec, cycVecR]
    rw [hNu, philin] at hK
    rw [← hN (cycVec n k), hNu] at hK
    -- Now `hK : (k:ℂ) • φ v = (l:ℂ) • φ v`, with `φ v ≠ 0`.
    have hφv : φ (socleVec n k) ≠ 0 :=
      fun h => socleVec_ne_zero n k (φ.injective (by rw [map_zero]; exact h))
    have hkl : ((k : ℂ) - (l : ℂ)) • φ (socleVec n k) = 0 := by rw [sub_smul, hK, sub_self]
    rcases smul_eq_zero.mp hkl with hc | hc
    · rw [sub_eq_zero] at hc; exact_mod_cast hc
    · exact absurd hc hφv

end Etingof.Problem3_9_2
