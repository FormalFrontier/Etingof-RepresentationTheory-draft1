/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LinearAlgebra.ModuleDecompositions
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Analysis.ContinuousMap.StableModuleEquivalence

open scoped ContinuousMap

/-- An auxiliary real subalgebra of the algebra of real-valued continuous functions. -/
@[source_ref "Chapter3/Problem3.8.5" (role := supporting)]
noncomputable def auxiliaryFunctionAlgebra : Subalgebra ℝ C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = f x}
  mul_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.mul_apply, hf x, hg x]
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
  algebraMap_mem' := by
    intro r x
    simp

/-- An auxiliary submodule of real-valued continuous functions over the auxiliary function algebra. -/
@[source_ref "Chapter3/Problem3.8.5" (role := supporting)]
noncomputable def auxiliaryFunctionModule : Submodule (auxiliaryFunctionAlgebra) C(ℝ, ℝ) where
  carrier := {f | ∀ x : ℝ, f (x + 1) = - f x}
  add_mem' := by
    intro f g hf hg x
    simp only [ContinuousMap.add_apply, hf x, hg x]
    ring
  zero_mem' := by
    intro x
    simp
  smul_mem' := by
    intro c f hf x
    have key : ∀ y : ℝ, (c • f) y = (c : C(ℝ, ℝ)) y * f y := by
      intro y
      rw [Algebra.smul_def]
      rfl
    rw [key (x + 1), key x, hf x, c.2 x]
    ring

private lemma periodicSubalg_coe_mul (e : auxiliaryFunctionAlgebra) (x : ℝ) :
    ((e * e : auxiliaryFunctionAlgebra) : C(ℝ, ℝ)) x = ((e : C(ℝ, ℝ)) x) * ((e : C(ℝ, ℝ)) x) := by
  simp

/-- Every idempotent of the auxiliary function algebra is either zero or one. -/
lemma idempotent_eq_zero_or_eq_one (e : auxiliaryFunctionAlgebra) (he : e * e = e) :
    e = 0 ∨ e = 1 := by

  set f : C(ℝ, ℝ) := (e : C(ℝ, ℝ)) with hf

  have hpt : ∀ x, f x * f x = f x := by
    intro x
    have := congrArg (fun z : auxiliaryFunctionAlgebra => (z : C(ℝ, ℝ)) x) he
    simpa using this

  have hdich : ∀ x, f x = 0 ∨ f x = 1 := by
    intro x
    have h := hpt x
    have : f x * (f x - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith [sub_eq_zero.mp h1])

  set s : Set ℝ := {x | f x = 1} with hs
  have hclosed : IsClosed s := by
    have : s = f ⁻¹' {1} := rfl
    rw [this]
    exact IsClosed.preimage (map_continuous f) isClosed_singleton
  have hcompl_closed : IsClosed sᶜ := by
    have : sᶜ = f ⁻¹' {0} := by
      ext x
      simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro hx; rcases hdich x with h0 | h1
        · exact h0
        · exact absurd h1 hx
      · intro hx; rw [hx]; norm_num
    rw [this]
    exact IsClosed.preimage (map_continuous f) isClosed_singleton
  have hclopen : IsClopen s := ⟨hclosed, isClosed_compl_iff.mp hcompl_closed⟩

  rcases isClopen_iff.mp hclopen with hempty | huniv
  ·
    left
    have hzero : ∀ x, f x = 0 := by
      intro x
      rcases hdich x with h0 | h1
      · exact h0
      · have hmem : x ∈ s := h1
        rw [hempty] at hmem
        simp at hmem
    have : f = 0 := by ext x; simp [hzero x]
    have : (e : C(ℝ, ℝ)) = ((0 : auxiliaryFunctionAlgebra) : C(ℝ, ℝ)) := by simpa [hf] using this
    exact Subtype.ext this
  ·
    right
    have hone : ∀ x, f x = 1 := by
      intro x
      have : x ∈ s := by rw [huniv]; exact Set.mem_univ x
      exact this
    have : f = 1 := by ext x; simp [hone x]
    have : (e : C(ℝ, ℝ)) = ((1 : auxiliaryFunctionAlgebra) : C(ℝ, ℝ)) := by simpa [hf] using this
    exact Subtype.ext this

/-- The auxiliary function algebra, viewed as a module over itself, satisfies the displayed imported module predicate. -/
@[source_ref "Chapter3/Problem3.8.5" (role := primary),
  source_ref "Chapter3/Remark3.8.6" (role := supporting)]
theorem auxiliaryProperty_auxiliaryFunctionAlgebra :
    _root_.RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (auxiliaryFunctionAlgebra) (auxiliaryFunctionAlgebra) := by
  refine ⟨inferInstance, ?_⟩
  intro W₁ W₂ hC

  have h1 : (1 : auxiliaryFunctionAlgebra) ∈ W₁ ⊔ W₂ := by rw [hC.sup_eq_top]; trivial
  rw [Submodule.mem_sup] at h1
  obtain ⟨e₁, he₁, e₂, he₂, hsum⟩ := h1

  have hmem12 : e₁ * e₂ ∈ W₁ ⊓ W₂ := by
    refine ⟨?_, ?_⟩
    · rw [mul_comm]
      have := W₁.smul_mem e₂ he₁
      rwa [smul_eq_mul] at this
    · have := W₂.smul_mem e₁ he₂
      rwa [smul_eq_mul] at this
  rw [hC.inf_eq_bot, Submodule.mem_bot] at hmem12

  have hidem : e₁ * e₁ = e₁ := by
    have h : e₁ * (e₁ + e₂) = e₁ * 1 := by rw [hsum]
    rw [mul_add, hmem12, add_zero, mul_one] at h
    exact h
  rcases idempotent_eq_zero_or_eq_one e₁ hidem with rfl | rfl
  ·
    left
    have he2 : e₂ = 1 := by rw [zero_add] at hsum; exact hsum
    rw [he2] at he₂
    have hW2 : W₂ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have := W₂.smul_mem a he₂
      rwa [smul_eq_mul, mul_one] at this
    have := hC.inf_eq_bot
    rwa [hW2, inf_top_eq] at this
  ·
    right
    have hW1 : W₁ = ⊤ := by
      rw [eq_top_iff]
      intro a _
      have := W₁.smul_mem a he₁
      rwa [smul_eq_mul, mul_one] at this
    have := hC.inf_eq_bot
    rwa [hW1, top_inf_eq] at this

open Real in

/-- An auxiliary continuous real-valued map. -/
noncomputable def firstAuxiliaryMap : C(ℝ, ℝ) := ⟨fun x => Real.cos (π * x), by fun_prop⟩

open Real in

/-- A second auxiliary continuous real-valued map. -/
noncomputable def secondAuxiliaryMap : C(ℝ, ℝ) := ⟨fun x => Real.sin (π * x), by fun_prop⟩

/-- The first auxiliary continuous map evaluates at x as the cosine of pi times x. -/
@[simp] lemma firstAuxiliaryMap_apply (x : ℝ) : firstAuxiliaryMap x = Real.cos (Real.pi * x) := rfl
/-- The second auxiliary continuous map evaluates at x as the sine of pi times x. -/
@[simp] lemma secondAuxiliaryMap_apply (x : ℝ) : secondAuxiliaryMap x = Real.sin (Real.pi * x) := rfl

/-- The first auxiliary continuous map belongs to the auxiliary function module. -/
lemma firstAuxiliaryMap_mem_auxiliaryFunctionModule : firstAuxiliaryMap ∈ auxiliaryFunctionModule := by
  intro x
  simp only [firstAuxiliaryMap_apply, mul_add, mul_one]
  exact Real.cos_add_pi _

/-- The second auxiliary continuous map belongs to the auxiliary function module. -/
lemma secondAuxiliaryMap_mem_auxiliaryFunctionModule : secondAuxiliaryMap ∈ auxiliaryFunctionModule := by
  intro x
  simp only [secondAuxiliaryMap_apply, mul_add, mul_one]
  exact Real.sin_add_pi _

/-- The pointwise sum of the squares of the two auxiliary continuous maps equals one. -/
lemma firstAuxiliaryMap_sq_add_secondAuxiliaryMap_sq (x : ℝ) : firstAuxiliaryMap x * firstAuxiliaryMap x + secondAuxiliaryMap x * secondAuxiliaryMap x = 1 := by
  simp only [firstAuxiliaryMap_apply, secondAuxiliaryMap_apply]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

/-- A distinguished element of the auxiliary function module. -/
noncomputable def firstAuxiliaryElement : auxiliaryFunctionModule := ⟨firstAuxiliaryMap, firstAuxiliaryMap_mem_auxiliaryFunctionModule⟩
/-- A second distinguished element of the auxiliary function module. -/
noncomputable def secondAuxiliaryElement : auxiliaryFunctionModule := ⟨secondAuxiliaryMap, secondAuxiliaryMap_mem_auxiliaryFunctionModule⟩

/-- The underlying continuous map of the first distinguished module element is the first auxiliary continuous map. -/
@[simp] lemma coe_firstAuxiliaryElement : (firstAuxiliaryElement : C(ℝ, ℝ)) = firstAuxiliaryMap := rfl
/-- The underlying continuous map of the second distinguished module element is the second auxiliary continuous map. -/
@[simp] lemma coe_secondAuxiliaryElement : (secondAuxiliaryElement : C(ℝ, ℝ)) = secondAuxiliaryMap := rfl

/-- An auxiliary binary map from pairs of elements of the function module to the function algebra. -/
noncomputable def auxiliaryBinaryMap (f g : auxiliaryFunctionModule) : auxiliaryFunctionAlgebra :=
  ⟨(f : C(ℝ, ℝ)) * (g : C(ℝ, ℝ)), by
    intro x
    simp only [ContinuousMap.mul_apply, f.2 x, g.2 x]
    ring⟩

/-- The value of the auxiliary binary map is the pointwise product of the values of its two function arguments. -/
@[simp] lemma auxiliaryBinaryMap_apply (f g : auxiliaryFunctionModule) (x : ℝ) :
    ((auxiliaryBinaryMap f g : auxiliaryFunctionAlgebra) : C(ℝ, ℝ)) x = (f : C(ℝ, ℝ)) x * (g : C(ℝ, ℝ)) x := rfl

/-- Scalar multiplication of an auxiliary module function by an auxiliary algebra function is pointwise multiplication. -/
lemma smul_apply (a : auxiliaryFunctionAlgebra) (m : auxiliaryFunctionModule) (x : ℝ) :
    ((a • m : auxiliaryFunctionModule) : C(ℝ, ℝ)) x = (a : C(ℝ, ℝ)) x * (m : C(ℝ, ℝ)) x := by
  rw [Submodule.coe_smul, Algebra.smul_def]; rfl

/-- Every element of the auxiliary function module equals a sum formed from two distinguished elements and coefficients supplied by the auxiliary binary map. -/
lemma eq_sum_auxiliaryCoefficients (f : auxiliaryFunctionModule) :
    f = auxiliaryBinaryMap firstAuxiliaryElement f • firstAuxiliaryElement + auxiliaryBinaryMap secondAuxiliaryElement f • secondAuxiliaryElement := by
  apply Subtype.ext
  ext x
  simp only [Submodule.coe_add, ContinuousMap.add_apply, smul_apply, auxiliaryBinaryMap_apply,
    coe_firstAuxiliaryElement, coe_secondAuxiliaryElement]
  have h := firstAuxiliaryMap_sq_add_secondAuxiliaryMap_sq x
  linear_combination (-((f : C(ℝ, ℝ)) x)) * h

/-- The auxiliary function module satisfies the displayed imported module predicate. -/
@[source_ref "Chapter3/Problem3.8.5" (role := primary),
  source_ref "Chapter3/Remark3.8.6" (role := supporting)]
theorem auxiliaryProperty_auxiliaryFunctionModule :
    _root_.RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (auxiliaryFunctionAlgebra) (auxiliaryFunctionModule) := by
  refine ⟨⟨⟨0, firstAuxiliaryElement, ?_⟩⟩, ?_⟩
  ·
    intro h
    have := congrArg (fun z : auxiliaryFunctionModule => (z : C(ℝ, ℝ)) 0) h
    simp [coe_firstAuxiliaryElement, firstAuxiliaryMap_apply] at this
  · intro W₁ W₂ hC

    set π := @Submodule.projection (auxiliaryFunctionAlgebra) _ (auxiliaryFunctionModule) _ _ W₁ W₂ hC with hπ
    have hleft : ∀ w, w ∈ W₁ → π w = w := by
      intro w hw
      simpa [hπ] using
        (@Submodule.projection_apply_of_mem_left (auxiliaryFunctionAlgebra) _ (auxiliaryFunctionModule) _ _
          W₁ W₂ hC w hw)
    have hright : ∀ w, w ∈ W₂ → π w = 0 := by
      intro w hw
      simpa [hπ] using
        (@Submodule.projection_apply_of_mem_right (auxiliaryFunctionAlgebra) _ (auxiliaryFunctionModule) _ _
          W₁ W₂ hC w hw)
    have hmem : ∀ g, π g ∈ W₁ := by
      intro g
      have hg : g ∈ W₁ ⊔ W₂ := by rw [hC.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hg
      obtain ⟨a, ha, b, hb, hab⟩ := hg
      rw [← hab, map_add, hleft a ha, hright b hb, add_zero]
      exact ha
    have hidemπ : ∀ f, π (π f) = π f := fun f => hleft (π f) (hmem f)

    set e : auxiliaryFunctionAlgebra := auxiliaryBinaryMap firstAuxiliaryElement (π firstAuxiliaryElement) + auxiliaryBinaryMap secondAuxiliaryElement (π secondAuxiliaryElement) with he_def
    have key : ∀ f, π f = e • f := by
      intro f
      have hpieq : π f = auxiliaryBinaryMap firstAuxiliaryElement f • π firstAuxiliaryElement + auxiliaryBinaryMap secondAuxiliaryElement f • π secondAuxiliaryElement := by
        conv_lhs => rw [eq_sum_auxiliaryCoefficients f]
        rw [map_add, map_smul, map_smul]
      rw [hpieq]
      apply Subtype.ext
      ext x
      rw [he_def]
      simp only [Submodule.coe_add, Subalgebra.coe_add, ContinuousMap.add_apply, smul_apply,
        auxiliaryBinaryMap_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement]
      ring

    have hidem_smul : ∀ f : ↥auxiliaryFunctionModule, (e * e) • f = e • f := by
      intro f
      have h1 : π (π f) = π f := hidemπ f
      rw [key f] at h1
      rw [key (e • f)] at h1
      rw [smul_smul] at h1
      exact h1
    have hee : e * e = e := by
      apply Subtype.ext
      ext x
      have hcx := congrArg (fun z : auxiliaryFunctionModule => (z : C(ℝ, ℝ)) x) (hidem_smul firstAuxiliaryElement)
      have hsx := congrArg (fun z : auxiliaryFunctionModule => (z : C(ℝ, ℝ)) x) (hidem_smul secondAuxiliaryElement)
      simp only [smul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement] at hcx hsx
      have htrig := firstAuxiliaryMap_sq_add_secondAuxiliaryMap_sq x
      linear_combination firstAuxiliaryMap x * hcx + secondAuxiliaryMap x * hsx +
        ((e : C(ℝ, ℝ)) x - ((e * e : auxiliaryFunctionAlgebra) : C(ℝ, ℝ)) x) * htrig

    rcases idempotent_eq_zero_or_eq_one e hee with he0 | he1
    · left
      rw [Submodule.eq_bot_iff]
      intro w hw
      have h := hleft w hw
      rw [key w, he0, zero_smul] at h
      exact h.symm
    · right
      rw [Submodule.eq_bot_iff]
      intro w hw
      have h := hright w hw
      rw [key w, he1, one_smul] at h
      exact h

/-- There is no linear equivalence from the auxiliary function algebra to the auxiliary function module. -/
@[source_ref "Chapter3/Problem3.8.5" (role := primary),
  source_ref "Chapter3/Remark3.8.6" (role := supporting)]
theorem isEmpty_linearEquiv_auxiliaryFunctionModule :
    IsEmpty (auxiliaryFunctionAlgebra ≃ₗ[auxiliaryFunctionAlgebra] auxiliaryFunctionModule) := by
  refine ⟨fun φ => ?_⟩

  set u : auxiliaryFunctionModule := φ 1 with hu
  set U : C(ℝ, ℝ) := (u : C(ℝ, ℝ)) with hU_def
  have hUanti : ∀ x, U (x + 1) = - U x := u.2

  have hgen : ∀ m : auxiliaryFunctionModule,
      (m : C(ℝ, ℝ)) = ((φ.symm m • u : auxiliaryFunctionModule) : C(ℝ, ℝ)) := by
    intro m
    have : (φ.symm m • u : auxiliaryFunctionModule) = m := by
      rw [hu, ← φ.map_smul, smul_eq_mul, mul_one, φ.apply_symm_apply]
    rw [this]

  have hroot : ∃ x₀ ∈ Set.Icc (0 : ℝ) 1, U x₀ = 0 := by
    have hcont : ContinuousOn U (Set.Icc 0 1) := U.continuous.continuousOn
    have hU1 : U 1 = - U 0 := by have := hUanti 0; simpa using this
    rcases le_or_gt 0 (U 0) with h0 | h0
    · have hmem : (0 : ℝ) ∈ Set.Icc (U 1) (U 0) := ⟨by rw [hU1]; linarith, h0⟩
      obtain ⟨x₀, hx₀, hval⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
      exact ⟨x₀, hx₀, hval⟩
    · have hmem : (0 : ℝ) ∈ Set.Icc (U 0) (U 1) := ⟨by linarith, by rw [hU1]; linarith⟩
      obtain ⟨x₀, hx₀, hval⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
      exact ⟨x₀, hx₀, hval⟩
  obtain ⟨x₀, _, hx₀0⟩ := hroot

  set w : C(ℝ, ℝ) := ⟨fun x => Real.cos (Real.pi * (x - x₀)), by fun_prop⟩ with hw_def
  have hw_mem : w ∈ auxiliaryFunctionModule := by
    intro x
    change Real.cos (Real.pi * (x + 1 - x₀)) = - Real.cos (Real.pi * (x - x₀))
    rw [show Real.pi * (x + 1 - x₀) = Real.pi * (x - x₀) + Real.pi by ring, Real.cos_add_pi]
  set wM : auxiliaryFunctionModule := ⟨w, hw_mem⟩ with hwM
  have hwval : (wM : C(ℝ, ℝ)) x₀ = 1 := by
    change Real.cos (Real.pi * (x₀ - x₀)) = 1
    simp
  have hzero : (wM : C(ℝ, ℝ)) x₀ = 0 := by
    rw [hgen wM, smul_apply, ← hU_def, hx₀0, mul_zero]
  rw [hwval] at hzero
  exact one_ne_zero hzero

/-- A family of linear maps from the auxiliary function module to its auxiliary function algebra, indexed by module elements. -/
noncomputable def auxiliaryLinearMapFamily (h : auxiliaryFunctionModule) :
    auxiliaryFunctionModule →ₗ[auxiliaryFunctionAlgebra] auxiliaryFunctionAlgebra where
  toFun f := auxiliaryBinaryMap h f
  map_add' f g := by
    apply Subtype.ext; ext t
    simp only [Subalgebra.coe_add, ContinuousMap.add_apply, auxiliaryBinaryMap_apply, Submodule.coe_add]
    ring
  map_smul' a f := by
    apply Subtype.ext; ext t
    simp only [RingHom.id_apply, auxiliaryBinaryMap_apply, smul_apply, smul_eq_mul,
      Subalgebra.coe_mul, ContinuousMap.mul_apply]
    ring

/-- An auxiliary linear map from a pair of auxiliary module elements to a pair of auxiliary algebra elements. -/
noncomputable def reverseAuxiliaryLinearMap :
    (auxiliaryFunctionModule × auxiliaryFunctionModule) →ₗ[auxiliaryFunctionAlgebra]
      (auxiliaryFunctionAlgebra × auxiliaryFunctionAlgebra) where
  toFun fg := (auxiliaryBinaryMap firstAuxiliaryElement fg.1 - auxiliaryBinaryMap secondAuxiliaryElement fg.2, auxiliaryBinaryMap secondAuxiliaryElement fg.1 + auxiliaryBinaryMap firstAuxiliaryElement fg.2)
  map_add' x y := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, Subalgebra.coe_sub,
        ContinuousMap.add_apply, ContinuousMap.sub_apply, auxiliaryBinaryMap_apply, Submodule.coe_add]
      ring
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Subalgebra.coe_add, ContinuousMap.add_apply,
        auxiliaryBinaryMap_apply, Submodule.coe_add]
      ring
  map_smul' a x := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Subalgebra.coe_sub,
        ContinuousMap.sub_apply, auxiliaryBinaryMap_apply, smul_apply, smul_eq_mul,
        Subalgebra.coe_mul, ContinuousMap.mul_apply]
      ring
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Subalgebra.coe_add,
        ContinuousMap.add_apply, auxiliaryBinaryMap_apply, smul_apply, smul_eq_mul,
        Subalgebra.coe_mul, ContinuousMap.mul_apply]
      ring

/-- An auxiliary linear map from a pair of auxiliary algebra elements to a pair of auxiliary module elements. -/
noncomputable def forwardAuxiliaryLinearMap :
    (auxiliaryFunctionAlgebra × auxiliaryFunctionAlgebra) →ₗ[auxiliaryFunctionAlgebra]
      (auxiliaryFunctionModule × auxiliaryFunctionModule) where
  toFun pq := (pq.1 • firstAuxiliaryElement + pq.2 • secondAuxiliaryElement, -(pq.1 • secondAuxiliaryElement) + pq.2 • firstAuxiliaryElement)
  map_add' x y := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, ContinuousMap.add_apply,
        smul_apply, Subalgebra.coe_add, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement]
      ring
    · apply Subtype.ext; ext t
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Submodule.coe_neg,
        ContinuousMap.add_apply, ContinuousMap.neg_apply, smul_apply, Subalgebra.coe_add,
        coe_firstAuxiliaryElement, coe_secondAuxiliaryElement]
      ring
  map_smul' a x := by
    refine Prod.ext_iff.mpr ⟨?_, ?_⟩
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Submodule.coe_add,
        ContinuousMap.add_apply, smul_apply, smul_eq_mul, Subalgebra.coe_mul,
        ContinuousMap.mul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement]
      ring
    · apply Subtype.ext; ext t
      simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, Submodule.coe_add,
        Submodule.coe_neg, ContinuousMap.add_apply, ContinuousMap.neg_apply, smul_apply,
        smul_eq_mul, Subalgebra.coe_mul, ContinuousMap.mul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement]
      ring

/-- The reverse auxiliary linear map sends a pair to the displayed sum and difference formed by the auxiliary binary map and the two distinguished elements. -/
@[simp] lemma reverseAuxiliaryLinearMap_apply (fg : auxiliaryFunctionModule × auxiliaryFunctionModule) :
    reverseAuxiliaryLinearMap fg = (auxiliaryBinaryMap firstAuxiliaryElement fg.1 - auxiliaryBinaryMap secondAuxiliaryElement fg.2, auxiliaryBinaryMap secondAuxiliaryElement fg.1 + auxiliaryBinaryMap firstAuxiliaryElement fg.2) := rfl

/-- The forward auxiliary linear map sends a pair to the displayed linear combinations formed with the two distinguished module elements. -/
@[simp] lemma forwardAuxiliaryLinearMap_apply (pq : auxiliaryFunctionAlgebra × auxiliaryFunctionAlgebra) :
    forwardAuxiliaryLinearMap pq = (pq.1 • firstAuxiliaryElement + pq.2 • secondAuxiliaryElement, -(pq.1 • secondAuxiliaryElement) + pq.2 • firstAuxiliaryElement) := rfl

/-- Applying the reverse auxiliary linear map after the forward auxiliary linear map returns the original pair of algebra elements. -/
lemma reverseAuxiliaryLinearMap_forwardAuxiliaryLinearMap_apply (pq : auxiliaryFunctionAlgebra × auxiliaryFunctionAlgebra) : reverseAuxiliaryLinearMap (forwardAuxiliaryLinearMap pq) = pq := by
  obtain ⟨p, q⟩ := pq
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext; ext t
    simp only [forwardAuxiliaryLinearMap_apply, reverseAuxiliaryLinearMap_apply, Subalgebra.coe_sub, ContinuousMap.sub_apply,
      auxiliaryBinaryMap_apply, Submodule.coe_add, Submodule.coe_neg, ContinuousMap.add_apply,
      ContinuousMap.neg_apply, smul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement, firstAuxiliaryMap_apply, secondAuxiliaryMap_apply]
    linear_combination ((p : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)
  · apply Subtype.ext; ext t
    simp only [forwardAuxiliaryLinearMap_apply, reverseAuxiliaryLinearMap_apply, Subalgebra.coe_add, ContinuousMap.add_apply,
      auxiliaryBinaryMap_apply, Submodule.coe_add, Submodule.coe_neg, ContinuousMap.add_apply,
      ContinuousMap.neg_apply, smul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement, firstAuxiliaryMap_apply, secondAuxiliaryMap_apply]
    linear_combination ((q : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)

/-- Applying the forward auxiliary linear map after the reverse auxiliary linear map returns the original pair of module elements. -/
lemma forwardAuxiliaryLinearMap_reverseAuxiliaryLinearMap_apply (fg : auxiliaryFunctionModule × auxiliaryFunctionModule) : forwardAuxiliaryLinearMap (reverseAuxiliaryLinearMap fg) = fg := by
  obtain ⟨f, g⟩ := fg
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · apply Subtype.ext; ext t
    simp only [forwardAuxiliaryLinearMap_apply, reverseAuxiliaryLinearMap_apply, Subalgebra.coe_sub, Subalgebra.coe_add,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, auxiliaryBinaryMap_apply, Submodule.coe_add,
      ContinuousMap.add_apply, smul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement, firstAuxiliaryMap_apply, secondAuxiliaryMap_apply]
    linear_combination ((f : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)
  · apply Subtype.ext; ext t
    simp only [forwardAuxiliaryLinearMap_apply, reverseAuxiliaryLinearMap_apply, Subalgebra.coe_sub, Subalgebra.coe_add,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, auxiliaryBinaryMap_apply, Submodule.coe_add,
      Submodule.coe_neg, ContinuousMap.neg_apply, smul_apply, coe_firstAuxiliaryElement, coe_secondAuxiliaryElement,
      firstAuxiliaryMap_apply, secondAuxiliaryMap_apply]
    linear_combination ((g : C(ℝ, ℝ)) t) * Real.sin_sq_add_cos_sq (Real.pi * t)

/-- The product of two copies of the auxiliary function algebra is linearly equivalent to the product of two copies of the auxiliary function module. -/
@[source_ref "Chapter3/Problem3.8.5" (role := primary),
  source_ref "Chapter3/Remark3.8.6" (role := supporting)]
theorem nonempty_prod_linearEquiv :
    Nonempty ((auxiliaryFunctionAlgebra × auxiliaryFunctionAlgebra) ≃ₗ[auxiliaryFunctionAlgebra]
      (auxiliaryFunctionModule × auxiliaryFunctionModule)) :=
  ⟨(LinearEquiv.ofLinear reverseAuxiliaryLinearMap forwardAuxiliaryLinearMap
      (by apply LinearMap.ext; intro pq
          simp only [LinearMap.comp_apply, LinearMap.id_apply]; exact reverseAuxiliaryLinearMap_forwardAuxiliaryLinearMap_apply pq)
      (by apply LinearMap.ext; intro fg
          simp only [LinearMap.comp_apply, LinearMap.id_apply]; exact forwardAuxiliaryLinearMap_reverseAuxiliaryLinearMap_apply fg)).symm⟩

end RepresentationTheory.Analysis.ContinuousMap.StableModuleEquivalence
