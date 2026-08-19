/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.FiniteGroupRepresentations.Auxiliary
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Complex.RealEndomorphismCentralizer

open RepresentationTheory.FiniteGroupRepresentations.Auxiliary

section RealCentralizerAuxiliary

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
variable [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- The real subalgebra of real-linear endomorphisms that centralize a complex representation. -/
@[source_ref "Chapter5/Problem5.1.2" (role := supporting)]
noncomputable def Representation.realEndomorphismCentralizer (ρ : Representation ℂ G V) :
    Subalgebra ℝ (Module.End ℝ V) :=
  Subalgebra.centralizer ℝ (Set.range (fun g => LinearMap.restrictScalars ℝ (ρ g)))

/-- Embeds complex scalars as real-linear endomorphisms lying in the centralizer of a complex representation. -/
noncomputable def Representation.complexScalarAlgHomRealCentralizer (ρ : Representation ℂ G V) :
    ℂ →ₐ[ℝ] Representation.realEndomorphismCentralizer ρ :=
  (Algebra.lsmul ℝ ℝ V).codRestrict (Representation.realEndomorphismCentralizer ρ) (by
    intro z
    rw [Representation.realEndomorphismCentralizer, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply, Algebra.lsmul_apply,
      map_smul])

omit [Fintype G] [Module.Finite ℂ V] in
/-- The real-centralizer endomorphism associated with a complex scalar acts on a vector by scalar multiplication. -/
@[simp]
theorem Representation.complexScalarAlgHomRealCentralizer_apply (ρ : Representation ℂ G V) (z : ℂ) (v : V) :
    (Representation.complexScalarAlgHomRealCentralizer ρ z : Module.End ℝ V) v = z • v := rfl

omit [Fintype G] [Module.Finite ℂ V] in
/-- The complex-scalar homomorphism into the real endomorphism centralizer is injective when the representation space is nontrivial. -/
theorem Representation.complexScalarAlgHomRealCentralizer_injective (ρ : Representation ℂ G V) [Nontrivial V] :
    Function.Injective (Representation.complexScalarAlgHomRealCentralizer ρ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : (Representation.complexScalarAlgHomRealCentralizer ρ z : Module.End ℝ V) v = 0 := by rw [hz]; rfl
  rw [Representation.complexScalarAlgHomRealCentralizer_apply] at this
  rcases smul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hv

section ConjDecomp

private lemma ring_conj_comm {R : Type*} [Ring R] {j : R} (hj : j * j = -1) (f : R) :
    j * (f - j * f * j) = (f - j * f * j) * j := by
  have h2 : j * (j * f * j) = -(f * j) := by
    rw [← mul_assoc, ← mul_assoc, hj, neg_one_mul, neg_mul]
  have h3 : j * f * j * j = -(j * f) := by rw [mul_assoc, hj, mul_neg_one]
  rw [mul_sub, sub_mul, h2, h3]; abel

private lemma ring_conj_anticomm {R : Type*} [Ring R] {j : R} (hj : j * j = -1) (f : R) :
    j * (f + j * f * j) = -((f + j * f * j) * j) := by
  have h2 : j * (j * f * j) = -(f * j) := by
    rw [← mul_assoc, ← mul_assoc, hj, neg_one_mul, neg_mul]
  have h3 : j * f * j * j = -(j * f) := by rw [mul_assoc, hj, mul_neg_one]
  rw [mul_add, add_mul, h2, h3]; abel

variable (ρ : Representation ℂ G V)

/-- The element of the real endomorphism centralizer that realizes the complex structure of the representation space. -/
noncomputable def Representation.realCentralizerComplexStructure : Representation.realEndomorphismCentralizer ρ := Representation.complexScalarAlgHomRealCentralizer ρ Complex.I

/-- Auxiliary result concerning the real endomorphism centralizer and its complex-structure element; its formal type is unavailable in the displayed evidence. -/
theorem Representation.auxiliaryRealCentralizerComplexStructureTheorem : Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerComplexStructure ρ = -1 := by
  rw [Representation.realCentralizerComplexStructure, ← map_mul, Complex.I_mul_I, map_neg, map_one]

variable {ρ}

/-- Extracts from a real-centralizer element the component that commutes with the centralizer complex structure. -/
noncomputable def Representation.realCentralizerCommutingComponent (f : Representation.realEndomorphismCentralizer ρ) : Representation.realEndomorphismCentralizer ρ :=
  (2⁻¹ : ℝ) • (f - Representation.realCentralizerComplexStructure ρ * f * Representation.realCentralizerComplexStructure ρ)

/-- Extracts from a real-centralizer element the component that anticommutes with the centralizer complex structure. -/
noncomputable def Representation.realCentralizerAnticommutingComponent (f : Representation.realEndomorphismCentralizer ρ) : Representation.realEndomorphismCentralizer ρ :=
  (2⁻¹ : ℝ) • (f + Representation.realCentralizerComplexStructure ρ * f * Representation.realCentralizerComplexStructure ρ)

/-- The sum of the commuting and anticommuting components of a real-centralizer element is the original element. -/
theorem Representation.realCentralizerCommutingComponent_add_anticommutingComponent (f : Representation.realEndomorphismCentralizer ρ) :
    Representation.realCentralizerCommutingComponent f + Representation.realCentralizerAnticommutingComponent f = f := by
  rw [Representation.realCentralizerCommutingComponent, Representation.realCentralizerAnticommutingComponent, ← smul_add]
  have : (f - Representation.realCentralizerComplexStructure ρ * f * Representation.realCentralizerComplexStructure ρ) + (f + Representation.realCentralizerComplexStructure ρ * f * Representation.realCentralizerComplexStructure ρ) = (2 : ℝ) • f := by
    rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

/-- The complex-structure element commutes with the commuting component of every real-centralizer element. -/
theorem Representation.realCentralizerComplexStructure_mul_commutingComponent (f : Representation.realEndomorphismCentralizer ρ) :
    Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerCommutingComponent f = Representation.realCentralizerCommutingComponent f * Representation.realCentralizerComplexStructure ρ := by
  rw [Representation.realCentralizerCommutingComponent, mul_smul_comm, smul_mul_assoc, ring_conj_comm (Representation.auxiliaryRealCentralizerComplexStructureTheorem ρ)]

/-- The complex-structure element multiplied by the anticommuting component of a centralizer element is the negative of the product in the opposite order. -/
theorem Representation.realCentralizerComplexStructure_mul_anticommutingComponent (f : Representation.realEndomorphismCentralizer ρ) :
    Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerAnticommutingComponent f = -(Representation.realCentralizerAnticommutingComponent f * Representation.realCentralizerComplexStructure ρ) := by
  rw [Representation.realCentralizerAnticommutingComponent, mul_smul_comm, smul_mul_assoc, ring_conj_anticomm (Representation.auxiliaryRealCentralizerComplexStructureTheorem ρ), smul_neg]

end ConjDecomp

omit [Module ℝ V] [IsScalarTower ℝ ℂ V] in
open scoped ComplexConjugate in
/-- Every finite-dimensional complex representation of a finite group admits an invariant form whose diagonal has positive real part on nonzero vectors and whose transposed values are complex conjugates. -/
theorem Representation.exists_invariant_positive_conjSymmForm (ρ : Representation ℂ G V) :
    ∃ H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ,
      (∀ g v w, H (ρ g v) (ρ g w) = H v w) ∧ (∀ v, v ≠ 0 → 0 < (H v v).re) ∧
      (∀ v w, (starRingEnd ℂ) (H v w) = H w v) := by
  classical
  set b := Module.finBasis ℂ V with hb
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => ∑ g : G, ∑ i, b.repr (ρ g v) i * conj (b.repr (ρ g w) i))
      ?_ ?_ ?_ ?_, ?_, ?_, ?_⟩
  · -- additive in the first slot
    intro v₁ v₂ w
    simp only [map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]
  · -- ℂ-linear in the first slot
    intro c v w
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc]
  · -- additive in the second slot
    intro v w₁ w₂
    simp only [map_add, Finsupp.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  · -- conjugate-linear in the second slot
    intro c v w
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => by ring
  · -- G-invariance
    intro h v w
    simp only [LinearMap.mk₂'ₛₗ_apply]
    have hcomp : ∀ (g : G) (x : V), ρ g (ρ h x) = ρ (g * h) x := fun g x => by
      rw [map_mul]; rfl
    simp_rw [hcomp]
    exact Equiv.sum_comp (Equiv.mulRight h)
      (fun g : G => ∑ i, b.repr (ρ g v) i * conj (b.repr (ρ g w) i))
  · -- positive-definiteness
    intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    have hcast : (∑ g : G, ∑ i, (Complex.normSq (b.repr (ρ g v) i) : ℂ))
        = ((∑ g : G, ∑ i, Complex.normSq (b.repr (ρ g v) i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast, Complex.ofReal_re]
    refine Finset.sum_pos' (fun g _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) ?_
    refine ⟨1, Finset.mem_univ 1, ?_⟩
    simp only [map_one, Module.End.one_apply]
    obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (b.repr.injective (by ext i; simp [hcon i]))
    exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  · -- conjugate symmetry: `conj (H v w) = H w v`
    intro v w
    simp only [LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

section ComplexTypeProof

open scoped ComplexConjugate

variable {ρ : Representation ℂ G V}

private lemma real_coe_smul (r : ℝ) (v : V) : (r : ℂ) • v = r • v := by
  rw [← IsScalarTower.algebraMap_smul ℂ r v, Complex.coe_algebraMap]

private lemma complex_smul_eq_real (c : ℂ) (v : V) :
    c • v = c.re • v + c.im • (Complex.I • v) := by
  rw [← real_coe_smul c.re v, ← real_coe_smul c.im (Complex.I • v), smul_smul, ← add_smul,
    Complex.re_add_im]

private lemma invSubmodule_eq_bot_or_top
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (W : Submodule ℂ V) (hW : ∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hirr
  rcases eq_bot_or_eq_top (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ) with h | h
  · exact Or.inl congr(Subrepresentation.toSubmodule $h)
  · exact Or.inr congr(Subrepresentation.toSubmodule $h)

private def toCLinear (T : Module.End ℝ V)
    (hI : ∀ v, T (Complex.I • v) = Complex.I • T v) : V →ₗ[ℂ] V where
  toFun := T
  map_add' := T.map_add
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [complex_smul_eq_real c v, map_add, map_smul, map_smul, hI,
      complex_smul_eq_real c (T v)]

private def toAntilinear (T : Module.End ℝ V)
    (hI : ∀ v, T (Complex.I • v) = -(Complex.I • T v)) : V →ₗ⋆[ℂ] V where
  toFun := T
  map_add' := T.map_add
  map_smul' c v := by
    change T (c • v) = (starRingEnd ℂ) c • T v
    rw [complex_smul_eq_real c v, map_add, map_smul, map_smul, hI,
      complex_smul_eq_real ((starRingEnd ℂ) c) (T v), Complex.conj_re, Complex.conj_im,
      smul_neg, neg_smul]

/-- Flips a map that is complex-linear in its first argument and conjugate-linear in its second into a conjugate-linear map from the space to its complex dual. -/
noncomputable def LinearMap.flipToConjLinearDual (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : V →ₗ⋆[ℂ] Module.Dual ℂ V where
  toFun w :=
    { toFun := fun v => H v w
      map_add' := fun a b => by
        change H (a + b) w = H a w + H b w; simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c v => by
        change H (c • v) w = c • H v w; simp only [map_smul, LinearMap.smul_apply] }
  map_add' w₁ w₂ := by ext v; change H v (w₁ + w₂) = H v w₁ + H v w₂; rw [map_add]
  map_smul' c w := by
    ext v; change H v (c • w) = (starRingEnd ℂ) c • H v w; rw [map_smulₛₗ]

/-- Evaluating the flipped conjugate-linear dual map at `w` and then `v` gives the original form evaluated at `v` and then `w`. -/
@[simp] theorem LinearMap.flipToConjLinearDual_apply (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (w v : V) :
    (LinearMap.flipToConjLinearDual H w) v = H v w := rfl

/-- If the form is invariant under a finite-group representation, its flipped conjugate-linear dual map intertwines that representation with the dual representation. -/
theorem LinearMap.flipToConjLinearDual_intertwines (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hinv : ∀ g v w, H (ρ g v) (ρ g w) = H v w) (g : G) (w : V) :
    LinearMap.flipToConjLinearDual H (ρ g w) = ρ.dual g (LinearMap.flipToConjLinearDual H w) := by
  ext v
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    LinearMap.flipToConjLinearDual_apply, LinearMap.flipToConjLinearDual_apply]
  have hgg : (ρ g) ((ρ g⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := hinv g (ρ g⁻¹ v) w
  rwa [hgg] at this

/-- If the real part of the form on every nonzero diagonal input is positive, the flipped conjugate-linear dual map is injective. -/
theorem LinearMap.flipToConjLinearDual_injective (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hpos : ∀ v, v ≠ 0 → 0 < (H v v).re) :
    Function.Injective (LinearMap.flipToConjLinearDual H) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra hwne
  have h2 : H w w = 0 := by
    have := DFunLike.congr_fun hw w
    simpa using this
  have hp := hpos w hwne
  rw [h2] at hp
  simp at hp

private lemma schur_scalar
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (φ : V →ₗ[ℂ] V) (hφ : ∀ g v, φ (ρ g v) = ρ g (φ v)) :
    ∃ c : ℂ, ∀ v, φ v = c • v := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  refine ⟨c, ?_⟩
  have hinv : ∀ (g : G) (v : V), v ∈ Module.End.eigenspace φ c → ρ g v ∈ Module.End.eigenspace φ c := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hφ, hv, map_smul]
  rcases invSubmodule_eq_bot_or_top hirr (Module.End.eigenspace φ c) hinv with hbot | htop
  · exact absurd hbot hc
  · intro v
    have : v ∈ Module.End.eigenspace φ c := htop ▸ Submodule.mem_top
    rwa [Module.End.mem_eigenspace_iff] at this

/-- For a finite-dimensional simple complex representation of a finite group, a nondegenerate invariant bilinear form satisfying `B w v = s • B v w` yields an equivariant map `j` and a real scalar `lam` such that `j (j v) = (lam : Complex) • v` and `0 < s * lam`. -/
theorem Representation.exists_equivariantMap_sq_of_invariant_bilinearForm_swap
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hinvB : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (s : ℝ) (hs : ∀ v w, B w v = s • B v w) :
    ∃ (j : V →ₗ⋆[ℂ] V) (lam : ℝ),
      (∀ g v, j (ρ g v) = ρ g (j v)) ∧
      (∀ v, j (j v) = (lam : ℂ) • v) ∧
      0 < s * lam := by
  classical
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  obtain ⟨H, hHinv, hHpos, hHsym⟩ := Representation.exists_invariant_positive_conjSymmForm ρ
  -- `H v v` is a nonnegative real (conjugate symmetry ⇒ real; positive-definiteness ⇒ positive).
  have hHreal : ∀ v, H v v = ((H v v).re : ℂ) := fun v => (Complex.conj_eq_iff_re.mp (hHsym v v)).symm
  -- `s ≠ 0` (else `B = 0`, contradicting nondegeneracy on the nontrivial space `V`).
  have hs0 : s ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hnd v fun w => by have := hs w v; rw [h, zero_smul] at this; exact this)
  -- `B.flip` is injective (second-slot nondegeneracy, obtained from `hs` + `hnd`).
  have hBdinj : Function.Injective (B.flip) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine hnd w fun w' => ?_
    have h1 : B w' w = 0 := DFunLike.congr_fun hw w'
    have := hs w' w
    rw [h1, smul_zero] at this
    exact this
  -- `LinearMap.flipToConjLinearDual H` is bijective: injective by positive-definiteness, surjective by an
  -- `ℝ`-dimension count (both `V` and `V*` have real dimension `2 · dim_ℂ V`).
  have hΦinj : Function.Injective (LinearMap.flipToConjLinearDual H) := LinearMap.flipToConjLinearDual_injective H hHpos
  have hΦsurj : Function.Surjective (LinearMap.flipToConjLinearDual H) := by
    let ΦR : V →ₗ[ℝ] Module.Dual ℂ V :=
      { toFun := LinearMap.flipToConjLinearDual H
        map_add' := (LinearMap.flipToConjLinearDual H).map_add
        map_smul' := fun r w => by
          simp only [RingHom.id_apply]
          rw [show (r : ℝ) • w = ((r : ℂ)) • w from (real_coe_smul r w).symm, map_smulₛₗ,
            Complex.conj_ofReal, ← IsScalarTower.algebraMap_smul ℂ r (LinearMap.flipToConjLinearDual H w),
            Complex.coe_algebraMap] }
    have hΦRinj : Function.Injective ΦR := hΦinj
    haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) ℂ V
    haveI : FiniteDimensional ℝ (Module.Dual ℂ V) := Module.Finite.trans (R := ℝ) ℂ _
    have hdimR : Module.finrank ℝ V = Module.finrank ℝ (Module.Dual ℂ V) := by
      rw [← Module.finrank_mul_finrank ℝ ℂ V,
        ← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ V), Subspace.dual_finrank_eq]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimR).mp hΦRinj
  -- Package `LinearMap.flipToConjLinearDual H` as a conjugate-linear equivalence and define `j := herm⁻¹ ∘ B.flip`.
  let hermEquiv : V ≃ₗ⋆[ℂ] Module.Dual ℂ V :=
    LinearEquiv.ofBijective (LinearMap.flipToConjLinearDual H) ⟨hΦinj, hΦsurj⟩
  let j0 : V →ₗ⋆[ℂ] V := (hermEquiv.symm.toLinearMap).comp B.flip
  -- Defining relation: `H v (j0 w) = B v w`.
  have hj0dual : ∀ w, LinearMap.flipToConjLinearDual H (j0 w) = B.flip w := fun w => by
    change LinearMap.flipToConjLinearDual H (hermEquiv.symm (B.flip w)) = B.flip w
    have : hermEquiv (hermEquiv.symm (B.flip w)) = B.flip w := hermEquiv.apply_symm_apply _
    simpa only [LinearEquiv.ofBijective_apply, hermEquiv] using this
  have hdefn : ∀ v w, H v (j0 w) = B v w := fun v w => by
    have := DFunLike.congr_fun (hj0dual w) v
    simpa only [LinearMap.flipToConjLinearDual_apply, LinearMap.flip_apply] using this
  have hj0inj : Function.Injective j0 := by
    have : Function.Injective (⇑j0) := by
      change Function.Injective (⇑hermEquiv.symm ∘ ⇑B.flip)
      exact hermEquiv.symm.injective.comp hBdinj
    exact this
  -- `j0` is `G`-equivariant (uniqueness via injectivity of `LinearMap.flipToConjLinearDual H`).
  have hj0equiv : ∀ g v, j0 (ρ g v) = ρ g (j0 v) := by
    intro g w
    apply hΦinj
    rw [hj0dual]
    ext v
    rw [LinearMap.flipToConjLinearDual_apply, LinearMap.flip_apply]
    -- `B v (ρ g w) = H v (ρ g (j0 w))`
    have hBv : B v (ρ g w) = B (ρ g⁻¹ v) w := by
      have hgg : (ρ g) ((ρ g⁻¹) v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have := hinvB g (ρ g⁻¹ v) w
      rwa [hgg] at this
    rw [hBv, ← hdefn, ← hHinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  -- `φ := j0 ∘ j0` is `ℂ`-linear equivariant, hence a scalar `c` by Schur.
  let φ : V →ₗ[ℂ] V :=
    { toFun := fun v => j0 (j0 v)
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [map_smulₛₗ, map_smulₛₗ, Complex.conj_conj] }
  have hφequiv : ∀ g v, φ (ρ g v) = ρ g (φ v) := fun g v => by
    change j0 (j0 (ρ g v)) = ρ g (j0 (j0 v))
    rw [hj0equiv, hj0equiv]
  obtain ⟨c, hc⟩ := schur_scalar hirr φ hφequiv
  have hcsq : ∀ v, j0 (j0 v) = c • v := hc
  -- Positivity: pin down `c` as a real number of sign `s`, using one nonzero vector.
  obtain ⟨w0, hw0⟩ := exists_ne (0 : V)
  have hjw0 : j0 w0 ≠ 0 := fun h => hw0 (hj0inj (h.trans (map_zero j0).symm))
  -- `conj c • H v w = B v (j0 w)` and `B v (j0 w) = s • H (j0 w) (j0 v)`.
  have hI : ∀ v w, (starRingEnd ℂ) c * H v w = B v (j0 w) := fun v w => by
    rw [← hdefn v (j0 w), hcsq w, map_smulₛₗ]; rfl
  have hII : ∀ v w, B v (j0 w) = (s : ℂ) * H (j0 w) (j0 v) := fun v w => by
    rw [hs (j0 w) v, hdefn (j0 w) v, Complex.real_smul]
  have hkey : (starRingEnd ℂ) c * ((H w0 w0).re : ℂ)
      = (s : ℂ) * ((H (j0 w0) (j0 w0)).re : ℂ) := by
    rw [← hHreal, ← hHreal, hI w0 w0, hII w0 w0]
  set p1 := (H w0 w0).re with hp1def
  set p2 := (H (j0 w0) (j0 w0)).re with hp2def
  have hp1 : 0 < p1 := hHpos w0 hw0
  have hp2 : 0 < p2 := hHpos (j0 w0) hjw0
  -- From `conj c * p1 = s * p2` deduce `conj c` is the real number `s * p2 / p1`.
  have hconj : (starRingEnd ℂ) c = ((s * p2 / p1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (by exact_mod_cast hp1.ne')]
    linear_combination hkey
  have hcre : c = ((s * p2 / p1 : ℝ) : ℂ) := by
    have := congrArg (starRingEnd ℂ) hconj
    rwa [Complex.conj_conj, Complex.conj_ofReal] at this
  refine ⟨j0, s * p2 / p1, hj0equiv, ?_, ?_⟩
  · intro v; rw [hcsq v, hcre]
  · have hs2 : 0 < s ^ 2 := (sq_nonneg s).lt_of_ne' (pow_ne_zero 2 hs0)
    have hrw : s * (s * p2 / p1) = s ^ 2 * (p2 / p1) := by ring
    rw [hrw]
    exact mul_pos hs2 (div_pos hp2 hp1)

/-- A finite-dimensional simple complex representation satisfying the stated auxiliary condition has a real-centralizer element whose square is one and which anticommutes with the centralizer complex structure. -/
theorem Representation.exists_realCentralizer_involution_anticommutes_complexStructure
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : auxiliaryRepresentationConditionTwo ρ) :
    ∃ j' : Representation.realEndomorphismCentralizer ρ, j' * j' = 1 ∧ Representation.realCentralizerComplexStructure ρ * j' = -(j' * Representation.realCentralizerComplexStructure ρ) := by
  obtain ⟨B, hsymm, hnd, hinvB⟩ := h
  obtain ⟨j0, lam, hjequiv, hjsq, hpos⟩ :=
    Representation.exists_equivariantMap_sq_of_invariant_bilinearForm_swap hirr B hnd hinvB 1
      (fun v w => by rw [hsymm, one_smul])
  rw [one_mul] at hpos
  -- `(r : ℂ) • v = r • v` for real `r`, via the scalar tower.
  have rcs : ∀ (r : ℝ) (v : V), (r : ℂ) • v = r • v := fun r v => by
    rw [← IsScalarTower.algebraMap_smul ℂ r v, Complex.coe_algebraMap]
  -- The underlying `ℝ`-linear map of the antilinear `j0`.
  let jm : Module.End ℝ V :=
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        rw [← rcs r v, map_smulₛₗ, Complex.conj_ofReal, rcs r (j0 v)] }
  have hmem : jm ∈ Representation.realEndomorphismCentralizer ρ := by
    rw [Representation.realEndomorphismCentralizer, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply]
    exact (hjequiv g v).symm
  set X : Representation.realEndomorphismCentralizer ρ := ⟨jm, hmem⟩ with hXdef
  -- `X² = lam • 1`.
  have hjm2 : X * X = lam • 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hXdef]
    ext v
    simp only [Module.End.mul_apply, SetLike.val_smul, Subalgebra.coe_one, LinearMap.smul_apply,
      Module.End.one_apply]
    change j0 (j0 v) = lam • v
    rw [hjsq v, rcs lam v]
  -- `X` anticommutes with `J = ·i`.
  have hanti0 : Representation.realCentralizerComplexStructure ρ * X = -(X * Representation.realCentralizerComplexStructure ρ) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul, hXdef]
    ext v
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply]
    change Complex.I • j0 v = -(j0 (Complex.I • v))
    rw [map_smulₛₗ, Complex.conj_I, neg_smul, neg_neg]
  have hsqrt : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hpos.le
  have hsne : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  refine ⟨(Real.sqrt lam)⁻¹ • X, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hjm2, smul_smul]
    have hscal : (Real.sqrt lam)⁻¹ * (Real.sqrt lam)⁻¹ * lam = 1 := by
      rw [← mul_inv, hsqrt, inv_mul_cancel₀ hpos.ne']
    rw [hscal, one_smul]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_neg, hanti0]

/-- Auxiliary theorem involving the displayed dependencies; its formal type is unavailable in the packet. -/
theorem Representation.auxiliaryCentralizerTheorem
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : auxiliaryRepresentationConditionOne ρ) :
    ∃ j' : Representation.realEndomorphismCentralizer ρ, j' * j' = -1 ∧ Representation.realCentralizerComplexStructure ρ * j' = -(j' * Representation.realCentralizerComplexStructure ρ) := by
  obtain ⟨B, hskew, hnd, hinvB⟩ := h
  obtain ⟨j0, lam, hjequiv, hjsq, hpos⟩ :=
    Representation.exists_equivariantMap_sq_of_invariant_bilinearForm_swap hirr B hnd hinvB (-1)
      (fun v w => by rw [hskew, neg_one_smul])
  -- `hpos : 0 < (-1) * lam`, i.e. `lam < 0`.
  have hnlam : 0 < -lam := by linarith
  have hlamne : lam ≠ 0 := by rintro rfl; simp at hnlam
  -- `(r : ℂ) • v = r • v` for real `r`, via the scalar tower.
  have rcs : ∀ (r : ℝ) (v : V), (r : ℂ) • v = r • v := fun r v => by
    rw [← IsScalarTower.algebraMap_smul ℂ r v, Complex.coe_algebraMap]
  -- The underlying `ℝ`-linear map of the antilinear `j0`.
  let jm : Module.End ℝ V :=
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        rw [← rcs r v, map_smulₛₗ, Complex.conj_ofReal, rcs r (j0 v)] }
  have hmem : jm ∈ Representation.realEndomorphismCentralizer ρ := by
    rw [Representation.realEndomorphismCentralizer, Subalgebra.mem_centralizer_iff]
    rintro _ ⟨g, rfl⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.restrictScalars_apply]
    exact (hjequiv g v).symm
  set X : Representation.realEndomorphismCentralizer ρ := ⟨jm, hmem⟩ with hXdef
  -- `X² = lam • 1`.
  have hjm2 : X * X = lam • 1 := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hXdef]
    ext v
    simp only [Module.End.mul_apply, SetLike.val_smul, Subalgebra.coe_one, LinearMap.smul_apply,
      Module.End.one_apply]
    change j0 (j0 v) = lam • v
    rw [hjsq v, rcs lam v]
  -- `X` anticommutes with `J = ·i`.
  have hanti0 : Representation.realCentralizerComplexStructure ρ * X = -(X * Representation.realCentralizerComplexStructure ρ) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul, hXdef]
    ext v
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply]
    change Complex.I • j0 v = -(j0 (Complex.I • v))
    rw [map_smulₛₗ, Complex.conj_I, neg_smul, neg_neg]
  have hsqrt : Real.sqrt (-lam) * Real.sqrt (-lam) = -lam := Real.mul_self_sqrt hnlam.le
  refine ⟨(Real.sqrt (-lam))⁻¹ • X, ?_, ?_⟩
  · rw [smul_mul_smul_comm, hjm2, smul_smul]
    have hscal : (Real.sqrt (-lam))⁻¹ * (Real.sqrt (-lam))⁻¹ * lam = -1 := by
      rw [← mul_inv, hsqrt, inv_mul_eq_div, div_eq_iff (neg_ne_zero.mpr hlamne)]; ring
    rw [hscal, neg_one_smul]
  · rw [mul_smul_comm, smul_mul_assoc, ← smul_neg, hanti0]

/-- Every member of the real endomorphism centralizer commutes pointwise with the action of each group element. -/
theorem Representation.realEndomorphismCentralizer_apply_comm (x : Representation.realEndomorphismCentralizer ρ) (g : G) (v : V) :
    (↑x : Module.End ℝ V) (ρ g v) = ρ g ((↑x : Module.End ℝ V) v) := by
  have hx2 : (↑x : Module.End ℝ V) ∈
      Subalgebra.centralizer ℝ (Set.range fun g => LinearMap.restrictScalars ℝ (ρ g)) := x.2
  rw [Subalgebra.mem_centralizer_iff] at hx2
  have hcomm := hx2 (LinearMap.restrictScalars ℝ (ρ g)) ⟨g, rfl⟩
  have hv := DFunLike.congr_fun hcomm v
  simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply] using hv.symm

/-- For a finite-dimensional simple complex representation of a finite group, the commuting component of every real-centralizer element is the image of some complex scalar. -/
theorem Representation.realCentralizerCommutingComponent_eq_complexScalar_of_isSimpleModule
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) (f : Representation.realEndomorphismCentralizer ρ) :
    ∃ z : ℂ, Representation.realCentralizerCommutingComponent f = Representation.complexScalarAlgHomRealCentralizer ρ z := by
  have hIp : ∀ v, (↑(Representation.realCentralizerCommutingComponent f) : Module.End ℝ V) (Complex.I • v)
      = Complex.I • (↑(Representation.realCentralizerCommutingComponent f) : Module.End ℝ V) v := by
    intro v
    have h0 : ((Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerCommutingComponent f : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
           = ((Representation.realCentralizerCommutingComponent f * Representation.realCentralizerComplexStructure ρ : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) :=
      congrArg _ (Representation.realCentralizerComplexStructure_mul_commutingComponent f)
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul] at h0
    have hv := DFunLike.congr_fun h0 v
    simpa only [Module.End.mul_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply] using hv.symm
  obtain ⟨c, hc⟩ := schur_scalar hirr (toCLinear _ hIp)
    (fun g v => Representation.realEndomorphismCentralizer_apply_comm (Representation.realCentralizerCommutingComponent f) g v)
  exact ⟨c, by apply Subtype.ext; ext v; rw [Representation.complexScalarAlgHomRealCentralizer_apply]; exact hc v⟩

/-- When the acting group is finite and the representation space has finite complex dimension, a complex number maps into the centralizer as its real part times the identity plus its imaginary part times the centralizer complex structure. -/
theorem Representation.complexScalarAlgHomRealCentralizer_eq_re_smul_one_add_im_smul_complexStructure (z : ℂ) :
    Representation.complexScalarAlgHomRealCentralizer ρ z = z.re • (1 : Representation.realEndomorphismCentralizer ρ) + z.im • Representation.realCentralizerComplexStructure ρ := by
  have hz : Representation.complexScalarAlgHomRealCentralizer ρ z
      = Representation.complexScalarAlgHomRealCentralizer ρ ((z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • Complex.I) := by
    congr 1
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im z).symm
  rw [hz, map_add, map_smul, map_smul, map_one, Representation.realCentralizerComplexStructure]

end ComplexTypeProof

section SplitQuaternionMatrix

variable {A : Type*} [Ring A] [Algebra ℝ A]

private lemma splitQuat_mul_expand (J j' : A) (hJ : J * J = -1) (hj : j' * j' = 1)
    (hanti : J * j' = -(j' * J))
    (a b c d a' b' c' d' : ℝ) :
    (a • (1 : A) + b • J + c • j' + d • (J * j')) *
      (a' • (1 : A) + b' • J + c' • j' + d' • (J * j')) =
      (a * a' - b * b' + c * c' + d * d') • (1 : A)
      + (a * b' + b * a' - c * d' + d * c') • J
      + (a * c' + c * a' - b * d' + d * b') • j'
      + (a * d' + d * a' + b * c' - c * b') • (J * j') := by
  have e1 : j' * J = -(J * j') := by rw [hanti, neg_neg]
  have e2 : J * (J * j') = -j' := by rw [← mul_assoc, hJ, neg_one_mul]
  have e3 : (J * j') * J = j' := by rw [mul_assoc, e1, mul_neg, e2, neg_neg]
  have e5 : (J * j') * j' = J := by rw [mul_assoc, hj, mul_one]
  have e4 : j' * (J * j') = -J := by rw [← mul_assoc, e1, neg_mul, e5]
  have e6 : (J * j') * (J * j') = 1 := by rw [mul_assoc, e4, mul_neg, hJ, neg_neg]
  simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, hJ, hj, e1, e2, e3, e4, e5,
    e6, smul_neg]
  module

/-- Auxiliary construction whose formal type is unavailable in the displayed evidence. -/
noncomputable def Representation.auxiliaryConstruction (J j' : A) (hJ : J * J = -1) (hj : j' * j' = 1)
    (hanti : J * j' = -(j' * J)) :
    Matrix (Fin 2) (Fin 2) ℝ →ₐ[ℝ] A :=
  AlgHom.ofLinearMap
    { toFun := fun M => ((M 0 0 + M 1 1) / 2) • (1 : A) + ((M 1 0 - M 0 1) / 2) • J
        + ((M 0 0 - M 1 1) / 2) • j' + ((M 0 1 + M 1 0) / 2) • (J * j')
      map_add' := fun M N => by simp only [Matrix.add_apply]; module
      map_smul' := fun r M => by
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; module }
    (by
      have h00 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
      have h11 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
      have h01 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
      have h10 : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, h00, h11, h01, h10]
      module)
    (fun M N => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [splitQuat_mul_expand J j' hJ hj hanti ((M 0 0 + M 1 1) / 2) ((M 1 0 - M 0 1) / 2)
        ((M 0 0 - M 1 1) / 2) ((M 0 1 + M 1 0) / 2) ((N 0 0 + N 1 1) / 2) ((N 1 0 - N 0 1) / 2)
        ((N 0 0 - N 1 1) / 2) ((N 0 1 + N 1 0) / 2)]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      module)

/-- Auxiliary theorem associated with an unavailable construction type. -/
@[simp] theorem Representation.auxiliaryConstruction_spec (J j' : A) (hJ : J * J = -1) (hj : j' * j' = 1)
    (hanti : J * j' = -(j' * J)) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    Representation.auxiliaryConstruction J j' hJ hj hanti M =
      ((M 0 0 + M 1 1) / 2) • (1 : A) + ((M 1 0 - M 0 1) / 2) • J
        + ((M 0 0 - M 1 1) / 2) • j' + ((M 0 1 + M 1 0) / 2) • (J * j') := rfl

end SplitQuaternionMatrix

/-- For a finite-dimensional simple complex representation satisfying the stated auxiliary condition, its real endomorphism centralizer admits a real-algebra equivalence with the complex numbers. -/
@[source_ref "Chapter5/Problem5.1.2" (role := primary)]
theorem Representation.nonempty_realEndomorphismCentralizer_algEquiv_complex
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : auxiliaryRepresentationProperty ρ) :
    Nonempty (Representation.realEndomorphismCentralizer ρ ≃ₐ[ℝ] ℂ) := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  -- Equivariance of any element of the centralizer.
  have equiv_of_mem : ∀ (x : Representation.realEndomorphismCentralizer ρ) (g : G) (v : V),
      (↑x : Module.End ℝ V) (ρ g v) = ρ g ((↑x : Module.End ℝ V) v) := by
    intro x g v
    have hx2 : (↑x : Module.End ℝ V) ∈
        Subalgebra.centralizer ℝ (Set.range fun g => LinearMap.restrictScalars ℝ (ρ g)) := x.2
    rw [Subalgebra.mem_centralizer_iff] at hx2
    have hcomm := hx2 (LinearMap.restrictScalars ℝ (ρ g)) ⟨g, rfl⟩
    have hv := DFunLike.congr_fun hcomm v
    simpa only [Module.End.mul_apply, LinearMap.restrictScalars_apply] using hv.symm
  -- The `ℂ`-embedding `Representation.complexScalarAlgHomRealCentralizer` is surjective.
  have hsurj : Function.Surjective (Representation.complexScalarAlgHomRealCentralizer ρ) := by
    intro f
    -- `Representation.realCentralizerCommutingComponent f` commutes with `i •`.
    have hIp : ∀ v, (↑(Representation.realCentralizerCommutingComponent f) : Module.End ℝ V) (Complex.I • v)
        = Complex.I • (↑(Representation.realCentralizerCommutingComponent f) : Module.End ℝ V) v := by
      intro v
      have h0 : ((Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerCommutingComponent f : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
             = ((Representation.realCentralizerCommutingComponent f * Representation.realCentralizerComplexStructure ρ : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) :=
        congrArg _ (Representation.realCentralizerComplexStructure_mul_commutingComponent f)
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 v
      simpa only [Module.End.mul_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply] using hv.symm
    -- `Representation.realCentralizerAnticommutingComponent f` anticommutes with `i •`.
    have hIm : ∀ v, (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) (Complex.I • v)
        = -(Complex.I • (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) v) := by
      intro v
      have h0 : ((Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerAnticommutingComponent f : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
             = ((-(Representation.realCentralizerAnticommutingComponent f * Representation.realCentralizerComplexStructure ρ) : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) :=
        congrArg _ (Representation.realCentralizerComplexStructure_mul_anticommutingComponent f)
      rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 v
      simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure,
        Representation.complexScalarAlgHomRealCentralizer_apply] at hv
      rw [hv, neg_neg]
    -- `Representation.realCentralizerCommutingComponent f` as a `ℂ`-linear equivariant endomorphism, hence a scalar by Schur.
    obtain ⟨c, hc⟩ := schur_scalar hirr (toCLinear _ hIp)
      (fun g v => equiv_of_mem (Representation.realCentralizerCommutingComponent f) g v)
    -- `Representation.realCentralizerAnticommutingComponent f = 0`.
    have hMeq : Representation.realCentralizerAnticommutingComponent f = 0 := by
      by_contra hne
      have hTmne : (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) ≠ 0 := fun h0 => hne (by
        apply Subtype.ext; simpa using h0)
      set ψ : V →ₗ⋆[ℂ] V := toAntilinear _ hIm with hψ
      have hψequiv : ∀ g v, ψ (ρ g v) = ρ g (ψ v) := fun g v => equiv_of_mem (Representation.realCentralizerAnticommutingComponent f) g v
      have hψne : ψ ≠ 0 := fun h0 => hTmne (by
        ext v; have := DFunLike.congr_fun h0 v; simpa [hψ, toAntilinear] using this)
      have hkerinv : ∀ (g : G) (v : V),
          v ∈ LinearMap.ker ψ → ρ g v ∈ LinearMap.ker ψ := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hψequiv, hv, map_zero]
      rcases invSubmodule_eq_bot_or_top hirr (LinearMap.ker ψ) hkerinv with hkbot | hktop
      · -- `ψ` injective: produce a `ℂ`-linear equivariant `V ≃ V*`, contradicting complex type.
        have hψinj : Function.Injective ψ := LinearMap.ker_eq_bot.mp hkbot
        obtain ⟨H, hHinv, hHpos, _⟩ := Representation.exists_invariant_positive_conjSymmForm ρ
        have hΦinj : Function.Injective (LinearMap.flipToConjLinearDual H) := LinearMap.flipToConjLinearDual_injective H hHpos
        let e : V →ₗ[ℂ] Module.Dual ℂ V :=
          { toFun := fun v => LinearMap.flipToConjLinearDual H (ψ v)
            map_add' := fun a b => by simp only [map_add]
            map_smul' := fun c v => by
              simp only [RingHom.id_apply]
              rw [map_smulₛₗ ψ, map_smulₛₗ (LinearMap.flipToConjLinearDual H), Complex.conj_conj] }
        have heinj : Function.Injective e :=
          fun a b hab => hψinj (hΦinj (show LinearMap.flipToConjLinearDual H (ψ a) = LinearMap.flipToConjLinearDual H (ψ b) from hab))
        have hdim : Module.finrank ℂ V = Module.finrank ℂ (Module.Dual ℂ V) :=
          (Subspace.dual_finrank_eq).symm
        apply h
        refine ⟨e.linearEquivOfInjective heinj hdim, ?_⟩
        intro g v
        rw [LinearMap.linearEquivOfInjective_apply, LinearMap.linearEquivOfInjective_apply]
        change LinearMap.flipToConjLinearDual H (ψ (ρ g v)) = ρ.dual g (LinearMap.flipToConjLinearDual H (ψ v))
        rw [hψequiv, LinearMap.flipToConjLinearDual_intertwines H hHinv]
      · exact hψne (by
          ext v
          have : v ∈ LinearMap.ker ψ := hktop ▸ Submodule.mem_top
          rwa [LinearMap.mem_ker] at this)
    -- Assemble: `f = Representation.realCentralizerCommutingComponent f = c • id = Representation.complexScalarAlgHomRealCentralizer ρ c`.
    have hPeq : Representation.realCentralizerCommutingComponent f = Representation.complexScalarAlgHomRealCentralizer ρ c := by
      apply Subtype.ext
      ext v
      rw [Representation.complexScalarAlgHomRealCentralizer_apply]
      exact hc v
    refine ⟨c, ?_⟩
    have hf : f = Representation.realCentralizerCommutingComponent f + Representation.realCentralizerAnticommutingComponent f := (Representation.realCentralizerCommutingComponent_add_anticommutingComponent f).symm
    rw [hMeq, add_zero] at hf
    rw [hf, hPeq]
  exact ⟨(AlgEquiv.ofBijective (Representation.complexScalarAlgHomRealCentralizer ρ)
    ⟨Representation.complexScalarAlgHomRealCentralizer_injective ρ, hsurj⟩).symm⟩

/-- For a finite-dimensional simple complex representation satisfying the stated auxiliary condition, its real endomorphism centralizer admits a real-algebra equivalence with matrices indexed by `Fin 2` over the reals. -/
@[source_ref "Chapter5/Problem5.1.2" (role := primary)]
theorem Representation.nonempty_realEndomorphismCentralizer_algEquiv_matrixFinTwo
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : auxiliaryRepresentationConditionTwo ρ) :
    Nonempty (Representation.realEndomorphismCentralizer ρ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  obtain ⟨j', hj'sq, hanti⟩ := Representation.exists_realCentralizer_involution_anticommutes_complexStructure hirr h
  have hJsq : Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerComplexStructure ρ = -1 := Representation.auxiliaryRealCentralizerComplexStructureTheorem ρ
  set Ψ := Representation.auxiliaryConstruction (Representation.realCentralizerComplexStructure ρ) j' hJsq hj'sq hanti with hΨ
  -- `↑j'` is `ℂ`-antilinear: `↑j' (i • v) = -(i • ↑j' v)`.
  have hjI : ∀ v, (↑j' : Module.End ℝ V) (Complex.I • v)
      = -(Complex.I • (↑j' : Module.End ℝ V) v) := by
    intro v
    have h0 : ((Representation.realCentralizerComplexStructure ρ * j' : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
           = ((-(j' * Representation.realCentralizerComplexStructure ρ) : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) := congrArg _ hanti
    rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
    have hv := DFunLike.congr_fun h0 v
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply] at hv
    rw [hv, neg_neg]
  -- `Ψ` is injective: `Mat₂(ℝ)` is a simple ring and `Representation.realEndomorphismCentralizer ρ` is nontrivial.
  haveI : Nontrivial (Representation.realEndomorphismCentralizer ρ) := by
    refine ⟨1, 0, fun hh => ?_⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h1 : ((1 : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) = ((0 : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) :=
      congrArg Subtype.val hh
    have h2 := DFunLike.congr_fun h1 v
    simpa using h2
  have hinj : Function.Injective Ψ := Ψ.toRingHom.injective
  -- `Ψ` is surjective: every `f ∈ End_{ℝ[G]} V` decomposes as `z + w·j'` (`z, w ∈ ℂ`), using that
  -- the `ℂ`-linear part `Representation.realCentralizerCommutingComponent f` and the antilinear `Representation.realCentralizerAnticommutingComponent f * j'` are complex scalars.
  have hsurj : Function.Surjective Ψ := by
    intro f
    have hIm : ∀ w, (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) (Complex.I • w)
        = -(Complex.I • (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) w) := by
      intro w
      have h0 : ((Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerAnticommutingComponent f : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
             = ((-(Representation.realCentralizerAnticommutingComponent f * Representation.realCentralizerComplexStructure ρ) : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) :=
        congrArg _ (Representation.realCentralizerComplexStructure_mul_anticommutingComponent f)
      rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 w
      simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply] at hv
      rw [hv, neg_neg]
    -- `Representation.realCentralizerAnticommutingComponent f * j'` is `ℂ`-linear (composite of two antilinear maps).
    have hTlin : ∀ v, (↑(Representation.realCentralizerAnticommutingComponent f * j') : Module.End ℝ V) (Complex.I • v)
        = Complex.I • (↑(Representation.realCentralizerAnticommutingComponent f * j') : Module.End ℝ V) v := by
      intro v
      rw [Subalgebra.coe_mul]
      simp only [Module.End.mul_apply]
      rw [hjI v, map_neg, hIm, neg_neg]
    obtain ⟨w, hw⟩ := schur_scalar hirr (toCLinear _ hTlin)
      (fun g v => Representation.realEndomorphismCentralizer_apply_comm (Representation.realCentralizerAnticommutingComponent f * j') g v)
    have hmj : Representation.realCentralizerAnticommutingComponent f * j' = Representation.complexScalarAlgHomRealCentralizer ρ w := by
      apply Subtype.ext; ext v; rw [Representation.complexScalarAlgHomRealCentralizer_apply]; exact hw v
    have hRM : Representation.realCentralizerAnticommutingComponent f = Representation.complexScalarAlgHomRealCentralizer ρ w * j' :=
      calc Representation.realCentralizerAnticommutingComponent f = Representation.realCentralizerAnticommutingComponent f * (j' * j') := by rw [hj'sq, mul_one]
        _ = Representation.realCentralizerAnticommutingComponent f * j' * j' := by rw [mul_assoc]
        _ = Representation.complexScalarAlgHomRealCentralizer ρ w * j' := by rw [hmj]
    obtain ⟨z, hz⟩ := Representation.realCentralizerCommutingComponent_eq_complexScalar_of_isSimpleModule hirr f
    have hfbasis : f = z.re • (1 : Representation.realEndomorphismCentralizer ρ) + z.im • Representation.realCentralizerComplexStructure ρ
        + w.re • j' + w.im • (Representation.realCentralizerComplexStructure ρ * j') := by
      have hfdec : f = Representation.complexScalarAlgHomRealCentralizer ρ z + Representation.complexScalarAlgHomRealCentralizer ρ w * j' := by
        conv_lhs => rw [← Representation.realCentralizerCommutingComponent_add_anticommutingComponent f]
        rw [hz, hRM]
      rw [hfdec, Representation.complexScalarAlgHomRealCentralizer_eq_re_smul_one_add_im_smul_complexStructure z, Representation.complexScalarAlgHomRealCentralizer_eq_re_smul_one_add_im_smul_complexStructure w, add_mul, smul_mul_assoc,
        smul_mul_assoc, one_mul]
      module
    refine ⟨!![z.re + w.re, w.im - z.im; z.im + w.im, z.re - w.re], ?_⟩
    simp only [hΨ, Representation.auxiliaryConstruction_spec, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val']
    rw [hfbasis]
    module
  exact ⟨(AlgEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩

/-- For a finite-dimensional simple complex representation satisfying the stated auxiliary condition, its real endomorphism centralizer admits a real-algebra equivalence with the real quaternions. -/
@[source_ref "Chapter5/Problem5.1.2" (role := primary)]
theorem Representation.nonempty_realEndomorphismCentralizer_algEquiv_quaternion
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : auxiliaryRepresentationConditionOne ρ) :
    Nonempty (Representation.realEndomorphismCentralizer ρ ≃ₐ[ℝ] Quaternion ℝ) := by
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  obtain ⟨j', hj'sq, hanti⟩ := Representation.auxiliaryCentralizerTheorem hirr h
  have hJsq : Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerComplexStructure ρ = -1 := Representation.auxiliaryRealCentralizerComplexStructureTheorem ρ
  -- The quaternion basis on `Representation.realEndomorphismCentralizer ρ`: `i = J`, `j = j'`, `k = J·j'`, with
  -- `J² = -1`, `j'² = -1`, `Jj' = -j'J` giving the Hamilton relations `ℍ[ℝ,-1,0,-1]`.
  let B : QuaternionAlgebra.Basis (Representation.realEndomorphismCentralizer ρ) (-1 : ℝ) 0 (-1) :=
    { i := Representation.realCentralizerComplexStructure ρ
      j := j'
      k := Representation.realCentralizerComplexStructure ρ * j'
      i_mul_i := by rw [hJsq]; module
      j_mul_j := by rw [hj'sq]; module
      i_mul_j := rfl
      j_mul_i := by rw [zero_smul, zero_sub, hanti, neg_neg] }
  let Ψ : Quaternion ℝ →ₐ[ℝ] Representation.realEndomorphismCentralizer ρ := QuaternionAlgebra.Basis.liftHom B
  -- `↑j'` is `ℂ`-antilinear: `↑j' (i • v) = -(i • ↑j' v)`.
  have hjI : ∀ v, (↑j' : Module.End ℝ V) (Complex.I • v)
      = -(Complex.I • (↑j' : Module.End ℝ V) v) := by
    intro v
    have h0 : ((Representation.realCentralizerComplexStructure ρ * j' : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
           = ((-(j' * Representation.realCentralizerComplexStructure ρ) : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) := congrArg _ hanti
    rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
    have hv := DFunLike.congr_fun h0 v
    simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply] at hv
    rw [hv, neg_neg]
  -- `Representation.realEndomorphismCentralizer ρ` is nontrivial (it acts faithfully on the nonzero space `V`).
  haveI : Nontrivial (Representation.realEndomorphismCentralizer ρ) := by
    refine ⟨1, 0, fun hh => ?_⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h1 : ((1 : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
        = ((0 : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) := congrArg Subtype.val hh
    have h2 := DFunLike.congr_fun h1 v
    simpa using h2
  -- `Ψ` is injective: `Quaternion ℝ` is a simple ring (division ring) and the target is nontrivial.
  have hinj : Function.Injective Ψ := Ψ.toRingHom.injective
  -- `Ψ` is surjective: every `f` decomposes as `z + w·j'` (`z, w ∈ ℂ`), using that the `ℂ`-linear
  -- part `Representation.realCentralizerCommutingComponent f` and the antilinear `Representation.realCentralizerAnticommutingComponent f * j'` are complex scalars (Schur).
  have hsurj : Function.Surjective Ψ := by
    intro f
    have hIm : ∀ w, (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) (Complex.I • w)
        = -(Complex.I • (↑(Representation.realCentralizerAnticommutingComponent f) : Module.End ℝ V) w) := by
      intro w
      have h0 : ((Representation.realCentralizerComplexStructure ρ * Representation.realCentralizerAnticommutingComponent f : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
             = ((-(Representation.realCentralizerAnticommutingComponent f * Representation.realCentralizerComplexStructure ρ) : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) :=
        congrArg _ (Representation.realCentralizerComplexStructure_mul_anticommutingComponent f)
      rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 w
      simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure, Representation.complexScalarAlgHomRealCentralizer_apply] at hv
      rw [hv, neg_neg]
    -- `Representation.realCentralizerAnticommutingComponent f * j'` is `ℂ`-linear (composite of two antilinear maps).
    have hTlin : ∀ v, (↑(Representation.realCentralizerAnticommutingComponent f * j') : Module.End ℝ V) (Complex.I • v)
        = Complex.I • (↑(Representation.realCentralizerAnticommutingComponent f * j') : Module.End ℝ V) v := by
      intro v
      rw [Subalgebra.coe_mul]
      simp only [Module.End.mul_apply]
      rw [hjI v, map_neg, hIm, neg_neg]
    obtain ⟨w, hw⟩ := schur_scalar hirr (toCLinear _ hTlin)
      (fun g v => Representation.realEndomorphismCentralizer_apply_comm (Representation.realCentralizerAnticommutingComponent f * j') g v)
    have hmj : Representation.realCentralizerAnticommutingComponent f * j' = Representation.complexScalarAlgHomRealCentralizer ρ w := by
      apply Subtype.ext; ext v; rw [Representation.complexScalarAlgHomRealCentralizer_apply]; exact hw v
    -- `j'² = -1`, so `Representation.realCentralizerAnticommutingComponent f = -(Representation.complexScalarAlgHomRealCentralizer w * j')`.
    -- `mul_neg_one` cannot be rewritten directly: its `-1` (via `HasDistribNeg`) is only
    -- defeq to `hj'sq`'s `-1` (via the ring's `Neg`), not syntactically equal, so we state
    -- the `* -1` step with an explicitly written `-1` that matches `hj'sq`.
    have hmulneg : Representation.realCentralizerAnticommutingComponent f * (-1 : Representation.realEndomorphismCentralizer ρ) = -Representation.realCentralizerAnticommutingComponent f :=
      mul_neg_one (Representation.realCentralizerAnticommutingComponent f)
    have hRM : Representation.realCentralizerAnticommutingComponent f = -(Representation.complexScalarAlgHomRealCentralizer ρ w * j') := by
      have hstep : Representation.realCentralizerAnticommutingComponent f * (j' * j') = Representation.complexScalarAlgHomRealCentralizer ρ w * j' := by
        rw [← mul_assoc, hmj]
      rw [hj'sq, hmulneg] at hstep
      exact neg_eq_iff_eq_neg.mp hstep
    obtain ⟨z, hz⟩ := Representation.realCentralizerCommutingComponent_eq_complexScalar_of_isSimpleModule hirr f
    have hfbasis : f = z.re • (1 : Representation.realEndomorphismCentralizer ρ) + z.im • Representation.realCentralizerComplexStructure ρ
        + (-w.re) • j' + (-w.im) • (Representation.realCentralizerComplexStructure ρ * j') := by
      have hfdec : f = Representation.complexScalarAlgHomRealCentralizer ρ z + -(Representation.complexScalarAlgHomRealCentralizer ρ w * j') := by
        conv_lhs => rw [← Representation.realCentralizerCommutingComponent_add_anticommutingComponent f]
        rw [hz, hRM]
      rw [hfdec, Representation.complexScalarAlgHomRealCentralizer_eq_re_smul_one_add_im_smul_complexStructure z, Representation.complexScalarAlgHomRealCentralizer_eq_re_smul_one_add_im_smul_complexStructure w, add_mul, smul_mul_assoc,
        smul_mul_assoc, one_mul]
      module
    refine ⟨(⟨z.re, z.im, -w.re, -w.im⟩ : Quaternion ℝ), ?_⟩
    change algebraMap ℝ (Representation.realEndomorphismCentralizer ρ) z.re + z.im • Representation.realCentralizerComplexStructure ρ
        + (-w.re) • j' + (-w.im) • (Representation.realCentralizerComplexStructure ρ * j') = f
    rw [Algebra.algebraMap_eq_smul_one, hfbasis]
  exact ⟨(AlgEquiv.ofBijective Ψ ⟨hinj, hsurj⟩).symm⟩

/-- Under the stated auxiliary condition, a finite-dimensional simple complex representation has an invariant real submodule whose complex span is all of the space and whose real finrank equals the complex finrank of the space. -/
@[source_ref "Chapter5/Problem5.1.2" (role := supporting)]
theorem Representation.exists_invariantRealSubmodule_of_auxiliaryCondition
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : auxiliaryRepresentationConditionTwo ρ) :
    ∃ W : Submodule ℝ V,
      (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) ∧
      Submodule.span ℂ (W : Set V) = ⊤ ∧
      Module.finrank ℝ W = Module.finrank ℂ V := by
  classical
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) ℂ V
  obtain ⟨j', hj'sq, hj'anti⟩ := Representation.exists_realCentralizer_involution_anticommutes_complexStructure hirr h
  -- Package the underlying `ℝ`-linear involution `T = j'` abstractly by its three properties.
  obtain ⟨T, hTsq, hTanti, hTequiv⟩ :
      ∃ T : Module.End ℝ V, (∀ v, T (T v) = v) ∧
        (∀ v, T (Complex.I • v) = -(Complex.I • T v)) ∧
        (∀ g v, T (ρ g v) = ρ g (T v)) := by
    refine ⟨(j' : Module.End ℝ V), ?_, ?_, fun g v => Representation.realEndomorphismCentralizer_apply_comm j' g v⟩
    · intro v
      have h1 : ((j' * j' : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
          = ((1 : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) := by rw [hj'sq]
      rw [Subalgebra.coe_mul, Subalgebra.coe_one] at h1
      have := DFunLike.congr_fun h1 v
      simpa only [Module.End.mul_apply, Module.End.one_apply] using this
    · intro v
      have h0 : ((Representation.realCentralizerComplexStructure ρ * j' : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V)
          = ((-(j' * Representation.realCentralizerComplexStructure ρ) : Representation.realEndomorphismCentralizer ρ) : Module.End ℝ V) := congrArg _ hj'anti
      rw [Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_mul] at h0
      have hv := DFunLike.congr_fun h0 v
      simp only [Module.End.mul_apply, LinearMap.neg_apply, Representation.realCentralizerComplexStructure,
        Representation.complexScalarAlgHomRealCentralizer_apply] at hv
      rw [hv, neg_neg]
  -- The `+1` and `-1` eigenspaces of `T`.
  set W : Submodule ℝ V := Module.End.eigenspace T (1 : ℝ) with hWdef
  set W' : Submodule ℝ V := Module.End.eigenspace T (-1 : ℝ) with hW'def
  have hWmem : ∀ v, v ∈ W ↔ T v = v := by
    intro v; rw [hWdef, Module.End.mem_eigenspace_iff, one_smul]
  have hW'mem : ∀ v, v ∈ W' ↔ T v = -v := by
    intro v; rw [hW'def, Module.End.mem_eigenspace_iff, neg_one_smul]
  -- `G`-stability of `W`.
  have hstab : ∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W := by
    intro g v hv
    rw [hWmem] at hv ⊢
    rw [hTequiv g v, hv]
  -- Eigenspace projections: `a = ½(v + Tv) ∈ W`, `b = ½(v − Tv) ∈ W'`, `v = a + b`.
  have haW : ∀ v, (2⁻¹ : ℝ) • (v + T v) ∈ W := by
    intro v; rw [hWmem, map_smul, map_add, hTsq]; rw [add_comm]
  have hbW' : ∀ v, (2⁻¹ : ℝ) • (v - T v) ∈ W' := by
    intro v
    rw [hW'mem, map_smul, map_sub, hTsq, ← smul_neg, neg_sub]
  have hsum : ∀ v, (2⁻¹ : ℝ) • (v + T v) + (2⁻¹ : ℝ) • (v - T v) = v := by
    intro v; rw [← smul_add]; module
  -- `i·W ⊆ W'` and `i·W' ⊆ W` (antilinearity of `T`).
  have hIWW' : ∀ v, v ∈ W → Complex.I • v ∈ W' := by
    intro v hv
    rw [hW'mem, hTanti, (hWmem v).mp hv]
  have hIW'W : ∀ v, v ∈ W' → Complex.I • v ∈ W := by
    intro v hv
    rw [hWmem, hTanti, (hW'mem v).mp hv, smul_neg, neg_neg]
  -- `span_ℂ W = ⊤`: every `v = a + b` with `a ∈ W` and `b = (-i)·(i·b) ∈ span_ℂ W`.
  have hspan : Submodule.span ℂ (W : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hb : (2⁻¹ : ℝ) • (v - T v) ∈ Submodule.span ℂ (W : Set V) := by
      have hIb : Complex.I • (2⁻¹ : ℝ) • (v - T v) ∈ W := hIW'W _ (hbW' v)
      have : (-Complex.I) • Complex.I • (2⁻¹ : ℝ) • (v - T v)
          ∈ Submodule.span ℂ (W : Set V) :=
        Submodule.smul_mem _ _ (Submodule.subset_span hIb)
      rwa [smul_smul, show (-Complex.I) * Complex.I = 1 by
        rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul] at this
    have ha : (2⁻¹ : ℝ) • (v + T v) ∈ Submodule.span ℂ (W : Set V) :=
      Submodule.subset_span (haW v)
    have := Submodule.add_mem _ ha hb
    rwa [hsum v] at this
  -- `IsCompl W W'` over `ℝ`.
  have hIC : IsCompl W W' := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro v hv
      have h1 := (hWmem v).mp hv.1
      have h2 := (hW'mem v).mp hv.2
      have hvv : v = -v := h1.symm.trans h2
      have h2v0 : (2 : ℝ) • v = 0 := by rw [two_smul, add_eq_zero_iff_eq_neg]; exact hvv
      rw [Submodule.mem_bot]
      rcases smul_eq_zero.mp h2v0 with h | h
      · norm_num at h
      · exact h
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      rw [Submodule.mem_sup]
      exact ⟨_, haW v, _, hbW' v, hsum v⟩
  -- `dim_ℝ W = dim_ℝ W'` via the `ℝ`-linear automorphism `·i` swapping the eigenspaces.
  have hdimWW' : Module.finrank ℝ W = Module.finrank ℝ W' := by
    let e : V ≃ₗ[ℝ] V :=
      { toFun := fun v => Complex.I • v
        map_add' := fun x y => smul_add _ _ _
        map_smul' := fun r v => by
          simp only [RingHom.id_apply]
          rw [← IsScalarTower.algebraMap_smul ℂ r v, smul_smul,
            ← IsScalarTower.algebraMap_smul ℂ r (Complex.I • v), smul_smul, mul_comm]
        invFun := fun v => (-Complex.I) • v
        left_inv := fun v => by
          change (-Complex.I) • Complex.I • v = v
          rw [smul_smul, show (-Complex.I) * Complex.I = 1 by
            rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
        right_inv := fun v => by
          change Complex.I • (-Complex.I) • v = v
          rw [smul_smul, show Complex.I * (-Complex.I) = 1 by
            rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul] }
    have hle1 : Submodule.map (e : V →ₗ[ℝ] V) W ≤ W' := by
      rintro _ ⟨w, hw, rfl⟩; exact hIWW' w hw
    have hle2 : Submodule.map (e : V →ₗ[ℝ] V) W' ≤ W := by
      rintro _ ⟨w, hw, rfl⟩; exact hIW'W w hw
    refine le_antisymm ?_ ?_
    · calc Module.finrank ℝ W = Module.finrank ℝ (Submodule.map (e : V →ₗ[ℝ] V) W) :=
            (LinearEquiv.finrank_map_eq e W).symm
        _ ≤ Module.finrank ℝ W' := Submodule.finrank_mono hle1
    · calc Module.finrank ℝ W' = Module.finrank ℝ (Submodule.map (e : V →ₗ[ℝ] V) W') :=
            (LinearEquiv.finrank_map_eq e W').symm
        _ ≤ Module.finrank ℝ W := Submodule.finrank_mono hle2
  -- Combine: `2·dim_ℝ W = dim_ℝ V = 2·dim_ℂ V`.
  have hsplit : Module.finrank ℝ W + Module.finrank ℝ W' = Module.finrank ℝ V :=
    Submodule.finrank_add_eq_of_isCompl hIC
  have hRV : Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
    rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]
  have hdim : Module.finrank ℝ W = Module.finrank ℂ V := by
    have h2W : 2 * Module.finrank ℝ W = 2 * Module.finrank ℂ V := by
      rw [two_mul]; nth_rewrite 2 [hdimWW']; rw [hsplit, hRV]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2W
  exact ⟨W, hstab, hspan, hdim⟩

/-- For a finite-dimensional simple complex representation of a finite group, an invariant real submodule with full complex span and real finrank equal to the ambient complex finrank implies the stated auxiliary condition. -/
@[source_ref "Chapter5/Problem5.1.2" (role := supporting)]
theorem Representation.auxiliaryCondition_of_exists_invariantRealSubmodule
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hW : ∃ W : Submodule ℝ V,
      (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) ∧
      Submodule.span ℂ (W : Set V) = ⊤ ∧
      Module.finrank ℝ W = Module.finrank ℂ V) :
    auxiliaryRepresentationConditionTwo ρ := by
  classical
  obtain ⟨W, hWstab, hspan, hdim⟩ := hW
  haveI : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  haveI hVnt : Nontrivial V := (Representation.asModuleEquiv ρ).symm.toEquiv.nontrivial
  haveI : FiniteDimensional ℝ V := Module.Finite.trans (R := ℝ) ℂ V
  obtain ⟨H, hHinv, hHpos, hHsym⟩ := Representation.exists_invariant_positive_conjSymmForm ρ
  -- `(r : ℂ) • z = r • z` for a real scalar `r` acting on `ℂ`.
  have rcC : ∀ (r : ℝ) (z : ℂ), (r : ℂ) • z = r • z := fun r z => by
    rw [smul_eq_mul, Complex.real_smul]
  -- Real basis `b` of `W`, viewed inside `V` as `bV`, upgraded to a `ℂ`-basis `bC` of `V`.
  let b := Module.finBasis ℝ W
  let bV : Fin (Module.finrank ℝ W) → V := fun i => (b i : V)
  have hcard : Fintype.card (Fin (Module.finrank ℝ W)) = Module.finrank ℂ V := by
    rw [Fintype.card_fin]; exact hdim
  have hle_span : ⊤ ≤ Submodule.span ℂ (Set.range bV) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    have hxe : x = ∑ i, (b.repr ⟨x, hx⟩ i) • bV i := by
      have hsr := b.sum_repr ⟨x, hx⟩
      have := congrArg (Submodule.subtype W) hsr
      simpa only [Submodule.subtype_apply, map_sum, map_smul] using this.symm
    rw [SetLike.mem_coe, hxe]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [← real_coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bC := basisOfTopLeSpanOfCardEqFinrank bV hle_span hcard
  have hbC : ∀ i, bC i = bV i := fun i =>
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank bV hle_span hcard) i
  -- The candidate `ℂ`-bilinear form: `ℂ`-bilinear extension of `(u,u') ↦ Re⟨u,u'⟩` on `W`.
  let Bform : V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
    bC.constr ℂ (fun i => bC.constr ℂ (fun j => ((H (bV i) (bV j)).re : ℂ)))
  have hBij : ∀ i j, Bform (bC i) (bC j) = ((H (bV i) (bV j)).re : ℂ) := fun i j => by
    change (bC.constr ℂ (fun i => bC.constr ℂ (fun j => ((H (bV i) (bV j)).re : ℂ)))) (bC i) (bC j)
        = ((H (bV i) (bV j)).re : ℂ)
    rw [Module.Basis.constr_basis, Module.Basis.constr_basis]
  -- `Bform` restricted to `W` is `Re H`: two `ℝ`-bilinear forms agreeing on the basis `b`.
  have hBW : ∀ u u' : ↥W, Bform (↑u) (↑u') = ((H (↑u) (↑u')).re : ℂ) := by
    let B1 : ↥W →ₗ[ℝ] ↥W →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun u u' : ↥W => Bform (↑u) (↑u'))
        (fun u1 u2 u' => by rw [Submodule.coe_add, map_add, LinearMap.add_apply])
        (fun c u u' => by
          rw [Submodule.coe_smul, ← real_coe_smul, map_smul, LinearMap.smul_apply, rcC])
        (fun u u1 u2 => by rw [Submodule.coe_add, map_add])
        (fun c u u' => by rw [Submodule.coe_smul, ← real_coe_smul, map_smul, rcC])
    let B2 : ↥W →ₗ[ℝ] ↥W →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun u u' : ↥W => ((H (↑u) (↑u')).re : ℂ))
        (fun u1 u2 u' => by
          rw [Submodule.coe_add, map_add, LinearMap.add_apply, Complex.add_re, Complex.ofReal_add])
        (fun c u u' => by
          rw [Submodule.coe_smul, ← real_coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
            Complex.re_ofReal_mul, Complex.real_smul]
          push_cast; ring)
        (fun u u1 u2 => by
          rw [Submodule.coe_add, map_add, Complex.add_re, Complex.ofReal_add])
        (fun c u u' => by
          rw [Submodule.coe_smul, ← real_coe_smul, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul,
            Complex.re_ofReal_mul, Complex.real_smul]
          push_cast; ring)
    have hB12 : B1 = B2 := by
      apply Module.Basis.ext b; intro i
      apply Module.Basis.ext b; intro j
      change Bform (↑(b i)) (↑(b j)) = ((H (↑(b i)) (↑(b j))).re : ℂ)
      have : (↑(b i) : V) = bV i := rfl
      have hj : (↑(b j) : V) = bV j := rfl
      rw [this, hj, ← hbC i, ← hbC j, hBij i j, hbC i, hbC j]
    intro u u'
    exact DFunLike.congr_fun (DFunLike.congr_fun hB12 u) u'
  -- `Bform` is symmetric.
  have hsymm : ∀ v w, Bform v w = Bform w v := by
    have hflip : Bform = Bform.flip := by
      apply LinearMap.ext_on hspan; intro x hx
      apply LinearMap.ext_on hspan; intro y hy
      rw [LinearMap.flip_apply, (hBW ⟨x, hx⟩ ⟨y, hy⟩ : Bform x y = ((H x y).re : ℂ)),
        (hBW ⟨y, hy⟩ ⟨x, hx⟩ : Bform y x = ((H y x).re : ℂ)), ← hHsym x y, Complex.conj_re]
    intro v w
    have h := DFunLike.congr_fun (DFunLike.congr_fun hflip v) w
    rwa [LinearMap.flip_apply] at h
  -- `Bform` is `G`-invariant.
  have hinv : ∀ (g : G) (v w : V), Bform (ρ g v) (ρ g w) = Bform v w := by
    intro g
    have hcompl : LinearMap.compl₁₂ Bform (ρ g) (ρ g) = Bform := by
      apply LinearMap.ext_on hspan; intro x hx
      apply LinearMap.ext_on hspan; intro y hy
      rw [LinearMap.compl₁₂_apply,
        (hBW ⟨ρ g x, hWstab g x hx⟩ ⟨ρ g y, hWstab g y hy⟩ :
          Bform (ρ g x) (ρ g y) = ((H (ρ g x) (ρ g y)).re : ℂ)),
        (hBW ⟨x, hx⟩ ⟨y, hy⟩ : Bform x y = ((H x y).re : ℂ)), hHinv]
    intro v w
    have hvw := DFunLike.congr_fun (DFunLike.congr_fun hcompl v) w
    rwa [LinearMap.compl₁₂_apply] at hvw
  -- `Bform` is nondegenerate: its kernel is a `G`-invariant subspace, `≠ ⊤` since `Bform ≠ 0`.
  have hnpos : 0 < Module.finrank ℝ W := by rw [hdim]; exact Module.finrank_pos
  have hne : Bform ≠ 0 := by
    intro hB0
    have hz : Bform (bC ⟨0, hnpos⟩) (bC ⟨0, hnpos⟩) = 0 := by rw [hB0]; rfl
    rw [hBij ⟨0, hnpos⟩ ⟨0, hnpos⟩] at hz
    have hbne : bV ⟨0, hnpos⟩ ≠ 0 := fun h =>
      (b.ne_zero ⟨0, hnpos⟩) (by rwa [Submodule.coe_eq_zero] at h)
    exact absurd (Complex.ofReal_eq_zero.mp hz) (hHpos _ hbne).ne'
  have hnd : ∀ v, (∀ w, Bform v w = 0) → v = 0 := by
    have hkerinv : ∀ (g : G) (x : V),
        x ∈ LinearMap.ker Bform → ρ g x ∈ LinearMap.ker Bform := by
      intro g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      ext w
      have hgg : (ρ g) ((ρ g⁻¹) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      have hstep := hinv g x (ρ g⁻¹ w)
      rw [hgg] at hstep
      rw [LinearMap.zero_apply, hstep, hx, LinearMap.zero_apply]
    intro v hv
    have hker : v ∈ LinearMap.ker Bform := by
      rw [LinearMap.mem_ker]; ext w; rw [LinearMap.zero_apply]; exact hv w
    rcases invSubmodule_eq_bot_or_top hirr (LinearMap.ker Bform) hkerinv with hbot | htop
    · rwa [hbot, Submodule.mem_bot] at hker
    · exfalso; apply hne
      ext v' w
      have hv'k : v' ∈ LinearMap.ker Bform := by rw [htop]; trivial
      rw [LinearMap.mem_ker] at hv'k
      rw [LinearMap.zero_apply, LinearMap.zero_apply]
      exact DFunLike.congr_fun hv'k w
  exact ⟨Bform, hsymm, hnd, hinv⟩

/-- For a finite-dimensional simple complex representation of a finite group, the stated auxiliary condition is equivalent to the existence of an invariant real submodule whose complex span is the whole space and whose real finrank is the complex finrank of the space. -/
@[source_ref "Chapter5/Problem5.1.2" (role := primary)]
theorem Representation.auxiliaryCondition_iff_exists_invariantRealSubmodule
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    auxiliaryRepresentationConditionTwo ρ ↔
      ∃ W : Submodule ℝ V,
        (∀ (g : G) (v : V), v ∈ W → ρ g v ∈ W) ∧
        Submodule.span ℂ (W : Set V) = ⊤ ∧
        Module.finrank ℝ W = Module.finrank ℂ V :=
  ⟨Representation.exists_invariantRealSubmodule_of_auxiliaryCondition ρ hirr, Representation.auxiliaryCondition_of_exists_invariantRealSubmodule ρ hirr⟩

end RealCentralizerAuxiliary

end RepresentationTheory.Complex.RealEndomorphismCentralizer
