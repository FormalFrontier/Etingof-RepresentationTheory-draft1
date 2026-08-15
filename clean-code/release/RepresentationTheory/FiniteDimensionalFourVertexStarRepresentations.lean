/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.OneDimensionalSubmoduleComplements

/-!
# Finite-dimensional four-vertex star representations

Finite-dimensional representations with three leaf spaces mapping to a central space.
-/

namespace RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations

/-- A finite-dimensional representation with one center vector space, three leaf vector spaces, and a linear map from each leaf to the center. -/
structure FourVertexStarRepresentation (k : Type*) [Field k] where
  /-- The center vector space of a four-vertex star representation. -/
  center : Type*
  /-- The first leaf vector space of a four-vertex star representation. -/
  leafOne : Type*
  /-- The second leaf vector space of a four-vertex star representation. -/
  leafTwo : Type*
  /-- The third leaf vector space of a four-vertex star representation. -/
  leafThree : Type*
  /-- The additive commutative group structure on the center space. -/
  [centerAddCommGroup : AddCommGroup center]
  /-- The scalar module structure on the center space. -/
  [centerModule : Module k center]
  /-- The center space of a star representation is finite-dimensional. -/
  [finiteDimensional_center : FiniteDimensional k center]
  /-- The additive commutative group structure on the first leaf space. -/
  [leafOneAddCommGroup : AddCommGroup leafOne]
  /-- The scalar module structure on the first leaf space. -/
  [leafOneModule : Module k leafOne]
  /-- The first leaf space of a star representation is finite-dimensional. -/
  [finiteDimensional_leafOne : FiniteDimensional k leafOne]
  /-- The additive commutative group structure on the second leaf space. -/
  [leafTwoAddCommGroup : AddCommGroup leafTwo]
  /-- The scalar module structure on the second leaf space. -/
  [leafTwoModule : Module k leafTwo]
  /-- The second leaf space of a star representation is finite-dimensional. -/
  [finiteDimensional_leafTwo : FiniteDimensional k leafTwo]
  /-- The additive commutative group structure on the third leaf space. -/
  [leafThreeAddCommGroup : AddCommGroup leafThree]
  /-- The scalar module structure on the third leaf space. -/
  [leafThreeModule : Module k leafThree]
  /-- The third leaf space of a star representation is finite-dimensional. -/
  [finiteDimensional_leafThree : FiniteDimensional k leafThree]
  /-- The structure map from the first leaf space to the center space. -/
  leafOneToCenter : leafOne →ₗ[k] center
  /-- The structure map from the second leaf space to the center space. -/
  leafTwoToCenter : leafTwo →ₗ[k] center
  /-- The structure map from the third leaf space to the center space. -/
  leafThreeToCenter : leafThree →ₗ[k] center
attribute [instance] FourVertexStarRepresentation.centerAddCommGroup FourVertexStarRepresentation.centerModule FourVertexStarRepresentation.finiteDimensional_center
  FourVertexStarRepresentation.leafOneAddCommGroup FourVertexStarRepresentation.leafOneModule FourVertexStarRepresentation.finiteDimensional_leafOne
  FourVertexStarRepresentation.leafTwoAddCommGroup FourVertexStarRepresentation.leafTwoModule FourVertexStarRepresentation.finiteDimensional_leafTwo
  FourVertexStarRepresentation.leafThreeAddCommGroup FourVertexStarRepresentation.leafThreeModule FourVertexStarRepresentation.finiteDimensional_leafThree

/-- The predicate that a four-vertex star representation is indecomposable. -/
def FourVertexStarRepresentation.IsIndecomposable {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k) : Prop :=
  (0 < Module.finrank k ρ.center ∨ 0 < Module.finrank k ρ.leafOne ∨
   0 < Module.finrank k ρ.leafTwo ∨ 0 < Module.finrank k ρ.leafThree) ∧
  ∀ (p q : Submodule k ρ.center)
    (p₁ q₁ : Submodule k ρ.leafOne)
    (p₂ q₂ : Submodule k ρ.leafTwo)
    (p₃ q₃ : Submodule k ρ.leafThree),
    IsCompl p q → IsCompl p₁ q₁ → IsCompl p₂ q₂ → IsCompl p₃ q₃ →
    (∀ x ∈ p₁, ρ.leafOneToCenter x ∈ p) → (∀ x ∈ q₁, ρ.leafOneToCenter x ∈ q) →
    (∀ x ∈ p₂, ρ.leafTwoToCenter x ∈ p) → (∀ x ∈ q₂, ρ.leafTwoToCenter x ∈ q) →
    (∀ x ∈ p₃, ρ.leafThreeToCenter x ∈ p) → (∀ x ∈ q₃, ρ.leafThreeToCenter x ∈ q) →
    (p = ⊥ ∧ p₁ = ⊥ ∧ p₂ = ⊥ ∧ p₃ = ⊥) ∨
    (q = ⊥ ∧ q₁ = ⊥ ∧ q₂ = ⊥ ∧ q₃ = ⊥)

/-- The nested four-tuple of center and leaf dimensions of a star representation. -/
noncomputable def FourVertexStarRepresentation.dimension {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k) : ℕ × ℕ × ℕ × ℕ :=
  (Module.finrank k ρ.center, Module.finrank k ρ.leafOne,
   Module.finrank k ρ.leafTwo, Module.finrank k ρ.leafThree)

/-- A finite collection of nested four-tuples of natural numbers associated with the four-vertex setting. -/
def fourVertexDimensionTuples : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {((0 : ℕ),1,0,0), ((0 : ℕ),0,1,0), ((0 : ℕ),0,0,1),
   ((1 : ℕ),0,0,0),
   ((1 : ℕ),1,0,0), ((1 : ℕ),0,1,0), ((1 : ℕ),0,0,1),
   ((1 : ℕ),1,1,0), ((1 : ℕ),1,0,1), ((1 : ℕ),0,1,1),
   ((1 : ℕ),1,1,1),
   ((2 : ℕ),1,1,1)}

/-- For an indecomposable star representation, the first leaf map is injective unless the center and the other two leaf spaces have dimension zero. -/
lemma leafOne_ker_eq_bot_or_other_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.leafOneToCenter = ⊥ ∨
    (Module.finrank k ρ.center = 0 ∧ Module.finrank k ρ.leafTwo = 0 ∧
     Module.finrank k ρ.leafThree = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₁, hq₁⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.leafOneToCenter)

  have := hind.2 ⊥ ⊤ (LinearMap.ker ρ.leafOneToCenter) q₁ ⊥ ⊤ ⊥ ⊤
    isCompl_bot_top hq₁ isCompl_bot_top isCompl_bot_top
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, hk, _, _⟩ | ⟨htop, _, htop₂, htop₃⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.center), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.leafTwo), htop₂, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.leafThree), htop₃, finrank_bot]⟩

/-- For an indecomposable star representation, the second leaf map is injective unless the center and the other two leaf spaces have dimension zero. -/
lemma leafTwo_ker_eq_bot_or_other_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.leafTwoToCenter = ⊥ ∨
    (Module.finrank k ρ.center = 0 ∧ Module.finrank k ρ.leafOne = 0 ∧
     Module.finrank k ρ.leafThree = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₂, hq₂⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.leafTwoToCenter)
  have := hind.2 ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.leafTwoToCenter) q₂ ⊥ ⊤
    isCompl_bot_top isCompl_bot_top hq₂ isCompl_bot_top
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, _, hk, _⟩ | ⟨htop, htop₁, _, htop₃⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.center), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.leafOne), htop₁, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.leafThree), htop₃, finrank_bot]⟩

/-- For an indecomposable star representation, the third leaf map is injective unless the center and the other two leaf spaces have dimension zero. -/
lemma leafThree_ker_eq_bot_or_other_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable) :
    LinearMap.ker ρ.leafThreeToCenter = ⊥ ∨
    (Module.finrank k ρ.center = 0 ∧ Module.finrank k ρ.leafOne = 0 ∧
     Module.finrank k ρ.leafTwo = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hker, hrest⟩ := h
  obtain ⟨q₃, hq₃⟩ := Submodule.exists_isCompl (LinearMap.ker ρ.leafThreeToCenter)
  have := hind.2 ⊥ ⊤ ⊥ ⊤ ⊥ ⊤ (LinearMap.ker ρ.leafThreeToCenter) q₃
    isCompl_bot_top isCompl_bot_top isCompl_bot_top hq₃
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun _ _ => Submodule.mem_top)
    (fun x hx => by simp [LinearMap.mem_ker.mp hx])
    (fun _ _ => Submodule.mem_top)
  rcases this with ⟨_, _, _, hk⟩ | ⟨htop, htop₁, htop₂, _⟩
  · exact hker hk
  · apply hrest
    exact ⟨by rw [← finrank_top (R := k) (M := ρ.center), htop, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.leafOne), htop₁, finrank_bot],
           by rw [← finrank_top (R := k) (M := ρ.leafTwo), htop₂, finrank_bot]⟩

/-- An indecomposable star representation with zero-dimensional center, second leaf, and third leaf has a one-dimensional first leaf. -/
lemma leafOne_finrank_eq_one_of_other_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hV : Module.finrank k ρ.center = 0) (hV₂ : Module.finrank k ρ.leafTwo = 0)
    (hV₃ : Module.finrank k ρ.leafThree = 0) :
    Module.finrank k ρ.leafOne = 1 := by
  rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₁ q₁ hpq₁ => ?_⟩
  · have : 0 < Module.finrank k ρ.leafOne := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.center) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have htopV₂ : (⊤ : Submodule k ρ.leafTwo) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV₂)
    have htopV₃ : (⊤ : Submodule k ρ.leafThree) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV₃)
    have hV_zero : ∀ (x : ρ.center), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.center) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ p₁ q₁ ⊥ ⊤ ⊥ ⊤
      isCompl_bot_top hpq₁ isCompl_bot_top isCompl_bot_top
      (fun x _ => by rw [hV_zero (ρ.leafOneToCenter x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, hp₁, _, _⟩ | ⟨_, hq₁, _, _⟩
    · left; exact hp₁
    · right; exact hq₁

/-- An indecomposable star representation with zero-dimensional center, first leaf, and third leaf has a one-dimensional second leaf. -/
lemma leafTwo_finrank_eq_one_of_other_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hV : Module.finrank k ρ.center = 0) (hV₁ : Module.finrank k ρ.leafOne = 0)
    (hV₃ : Module.finrank k ρ.leafThree = 0) :
    Module.finrank k ρ.leafTwo = 1 := by
  rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₂ q₂ hpq₂ => ?_⟩
  · have : 0 < Module.finrank k ρ.leafTwo := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.center) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have hV_zero : ∀ (x : ρ.center), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.center) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ ⊥ ⊤ p₂ q₂ ⊥ ⊤
      isCompl_bot_top isCompl_bot_top hpq₂ isCompl_bot_top
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV_zero (ρ.leafTwoToCenter x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, _, hp₂, _⟩ | ⟨_, _, hq₂, _⟩
    · left; exact hp₂
    · right; exact hq₂

/-- An indecomposable star representation with zero-dimensional center, first leaf, and second leaf has a one-dimensional third leaf. -/
lemma leafThree_finrank_eq_one_of_other_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hV : Module.finrank k ρ.center = 0) (hV₁ : Module.finrank k ρ.leafOne = 0)
    (hV₂ : Module.finrank k ρ.leafTwo = 0) :
    Module.finrank k ρ.leafThree = 1 := by
  rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p₃ q₃ hpq₃ => ?_⟩
  · have : 0 < Module.finrank k ρ.leafThree := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htopV : (⊤ : Submodule k ρ.center) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact hV)
    have hV_zero : ∀ (x : ρ.center), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.center) := Submodule.mem_top
      rwa [htopV, Submodule.mem_bot] at this
    specialize hind_cond ⊥ ⊤ ⊥ ⊤ ⊥ ⊤ p₃ q₃
      isCompl_bot_top isCompl_bot_top isCompl_bot_top hpq₃
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x hx => by
        rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
      (fun x _ => by rw [hV_zero (ρ.leafThreeToCenter x)]; exact Submodule.zero_mem _)
      (fun _ _ => Submodule.mem_top)
    rcases hind_cond with ⟨_, _, _, hp₃⟩ | ⟨_, _, _, hq₃⟩
    · left; exact hp₃
    · right; exact hq₃

/-- The domain of an injective linear map into a zero-dimensional finite-dimensional space also has dimension zero. -/
lemma finrank_eq_zero_of_injective_of_codomain_finrank_eq_zero {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V₁ →ₗ[k] V) (hf : LinearMap.ker f = ⊥) (hV : Module.finrank k V = 0) :
    Module.finrank k V₁ = 0 := by
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hf
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

/-- An indecomposable star representation whose three leaf spaces have dimension zero has a one-dimensional center. -/
lemma center_finrank_eq_one_of_leaf_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (h₁ : Module.finrank k ρ.leafOne = 0) (h₂ : Module.finrank k ρ.leafTwo = 0)
    (h₃ : Module.finrank k ρ.leafThree = 0) :
    Module.finrank k ρ.center = 1 := by
  rw [← RepresentationTheory.OneDimensionalSubmoduleComplements.nontrivial_and_isCompl_eq_bot_iff_finrank_eq_one]
  obtain ⟨hnt, hind_cond⟩ := hind
  refine ⟨?_, fun p q hpq => ?_⟩
  · have : 0 < Module.finrank k ρ.center := by
      rcases hnt with h | h | h | h <;> omega
    exact Module.nontrivial_of_finrank_pos this
  · have htop₁ : (⊤ : Submodule k ρ.leafOne) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₁)
    have htop₂ : (⊤ : Submodule k ρ.leafTwo) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₂)
    have htop₃ : (⊤ : Submodule k ρ.leafThree) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by rw [finrank_top]; exact h₃)
    have hV₁_zero : ∀ (x : ρ.leafOne), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.leafOne) := Submodule.mem_top
      rwa [htop₁, Submodule.mem_bot] at this
    have hV₂_zero : ∀ (x : ρ.leafTwo), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.leafTwo) := Submodule.mem_top
      rwa [htop₂, Submodule.mem_bot] at this
    have hV₃_zero : ∀ (x : ρ.leafThree), x = 0 := fun x => by
      have : x ∈ (⊤ : Submodule k ρ.leafThree) := Submodule.mem_top
      rwa [htop₃, Submodule.mem_bot] at this
    specialize hind_cond p q ⊥ ⊤ ⊥ ⊤ ⊥ ⊤
      hpq isCompl_bot_top isCompl_bot_top isCompl_bot_top
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₁_zero x, map_zero]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₂_zero x, map_zero]; exact Submodule.zero_mem _)
      (fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact Submodule.zero_mem _)
      (fun x _ => by rw [hV₃_zero x, map_zero]; exact Submodule.zero_mem _)
    rcases hind_cond with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
    · left; exact hp
    · right; exact hq

/-- If all three leaf maps of an indecomposable star representation are injective, then their ranges span the center or all leaf spaces have dimension zero. -/
lemma sup_ranges_eq_top_or_leaf_finrank_eq_zero {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (hA₁ : LinearMap.ker ρ.leafOneToCenter = ⊥) (hA₂ : LinearMap.ker ρ.leafTwoToCenter = ⊥)
    (hA₃ : LinearMap.ker ρ.leafThreeToCenter = ⊥) :
    LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter ⊔ LinearMap.range ρ.leafThreeToCenter = ⊤ ∨
    (Module.finrank k ρ.leafOne = 0 ∧ Module.finrank k ρ.leafTwo = 0 ∧
     Module.finrank k ρ.leafThree = 0) := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hR, harms⟩ := h
  set R := LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter ⊔ LinearMap.range ρ.leafThreeToCenter with hR_def
  obtain ⟨S, hRS⟩ := Submodule.exists_isCompl R

  have := hind.2 R S ⊤ ⊥ ⊤ ⊥ ⊤ ⊥
    hRS isCompl_top_bot isCompl_top_bot isCompl_top_bot
    (fun x _ => by
      have h : ρ.leafOneToCenter x ∈ LinearMap.range ρ.leafOneToCenter := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_left (Submodule.mem_sup_left h))
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun x _ => by
      have h : ρ.leafTwoToCenter x ∈ LinearMap.range ρ.leafTwoToCenter := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_left (Submodule.mem_sup_right h))
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
    (fun x _ => by
      have h : ρ.leafThreeToCenter x ∈ LinearMap.range ρ.leafThreeToCenter := LinearMap.mem_range.mpr ⟨x, rfl⟩
      exact Submodule.mem_sup_right h)
    (fun x hx => by simp [(Submodule.mem_bot (R := k)).mp hx])
  rcases this with ⟨hRbot, htop₁, htop₂, htop₃⟩ | ⟨hSbot, _, _, _⟩
  ·
    apply harms
    have hR₁ : LinearMap.range ρ.leafOneToCenter = ⊥ := by
      have h : LinearMap.range ρ.leafOneToCenter ≤ R :=
        le_sup_left.trans (le_sup_left (a := LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter))
      rw [hRbot] at h; exact bot_unique h
    have hR₂ : LinearMap.range ρ.leafTwoToCenter = ⊥ := by
      have h : LinearMap.range ρ.leafTwoToCenter ≤ R :=
        le_sup_right.trans (le_sup_left (a := LinearMap.range ρ.leafOneToCenter ⊔ LinearMap.range ρ.leafTwoToCenter))
      rw [hRbot] at h; exact bot_unique h
    have hR₃ : LinearMap.range ρ.leafThreeToCenter = ⊥ := by
      have h : LinearMap.range ρ.leafThreeToCenter ≤ R := le_sup_right
      rw [hRbot] at h; exact bot_unique h
    exact ⟨by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₁)]; simp [hR₁],
           by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₂)]; simp [hR₂],
           by rw [← LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hA₃)]; simp [hR₃]⟩
  · have : R = ⊤ := by
      have := hRS.sup_eq_top
      rw [hSbot, sup_bot_eq] at this
      exact this
    exact hR this

/-- For an indecomposable star representation, if every leaf-map range lies in one of two complementary center submodules, then one of those submodules is zero. -/
lemma eq_bot_or_eq_bot_of_ranges_le {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (p q : Submodule k ρ.center) (hpq : IsCompl p q)
    (h₁ : LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range ρ.leafOneToCenter ≤ q)
    (h₂ : LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range ρ.leafTwoToCenter ≤ q)
    (h₃ : LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range ρ.leafThreeToCenter ≤ q) :
    p = ⊥ ∨ q = ⊥ := by

  have arm₁ : ∃ (p₁ q₁ : Submodule k ρ.leafOne), IsCompl p₁ q₁ ∧
      (∀ x ∈ p₁, ρ.leafOneToCenter x ∈ p) ∧ (∀ x ∈ q₁, ρ.leafOneToCenter x ∈ q) := by
    rcases h₁ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.leafTwo), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.leafTwoToCenter x ∈ p) ∧ (∀ x ∈ q₂, ρ.leafTwoToCenter x ∈ q) := by
    rcases h₂ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.leafThree), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.leafThreeToCenter x ∈ p) ∧ (∀ x ∈ q₃, ρ.leafThreeToCenter x ∈ q) := by
    rcases h₃ with h | h
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
  obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := arm₁
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

/-- Complementary submodules pull back to complementary submodules along an injective linear map with full range. -/
lemma isCompl_comap_of_range_eq_top {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V] [Module k V]
    (A : V₁ →ₗ[k] V) (hA_inj : Function.Injective A) (hA_surj : LinearMap.range A = ⊤)
    (p q : Submodule k V) (hpq : IsCompl p q) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff]; ext x
    simp only [Submodule.mem_sup, Submodule.mem_comap, Submodule.mem_top, iff_true]
    have hA_surj' : Function.Surjective A := LinearMap.range_eq_top.mp hA_surj
    have hx_top : A x ∈ (⊤ : Submodule k V) := Submodule.mem_top
    rw [← hpq.sup_eq_top] at hx_top
    obtain ⟨yp, hyp, yq, hyq, heq⟩ := Submodule.mem_sup.mp hx_top
    obtain ⟨x₁, hx₁⟩ := hA_surj' yp
    obtain ⟨x₂, hx₂⟩ := hA_surj' yq
    have : x = x₁ + x₂ := hA_inj (by rw [map_add, hx₁, hx₂, heq])
    exact ⟨x₁, by rw [show A x₁ = yp from hx₁]; exact hyp,
           x₂, by rw [show A x₂ = yq from hx₂]; exact hyq, this.symm⟩

/-- Distinct one-dimensional submodules of a two-dimensional vector space are complementary. -/
lemma isCompl_of_finrank_eq_one_of_ne {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2)
    (p q : Submodule k V) (hp : Module.finrank k p = 1) (hq : Module.finrank k q = 1)
    (hne : p ≠ q) : IsCompl p q := by

  have hpq_le : Module.finrank k (p ⊓ q : Submodule k V) ≤ 1 :=
    (Submodule.finrank_mono (inf_le_left (a := p) (b := q))).trans hp.le

  have hpq_zero : Module.finrank k (p ⊓ q : Submodule k V) = 0 := by
    by_contra h; push Not at h
    have hpq_eq : Module.finrank k (p ⊓ q : Submodule k V) = 1 := by omega
    have h1 : (p ⊓ q : Submodule k V) = p :=
      Submodule.eq_of_le_of_finrank_le (inf_le_left (a := p) (b := q)) (by omega)
    have h2 : (p ⊓ q : Submodule k V) = q :=
      Submodule.eq_of_le_of_finrank_le (inf_le_right (a := p) (b := q)) (by omega)
    exact hne (h1.symm.trans h2)

  have hpq_sup : Module.finrank k (p ⊔ q : Submodule k V) = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq p q; omega
  constructor
  ·
    rw [disjoint_iff]
    exact Submodule.finrank_eq_zero.mp hpq_zero
  ·
    rw [codisjoint_iff]
    exact Submodule.eq_top_of_finrank_eq (by omega)

/-- For an indecomposable star representation, complementary center submodules have a zero member when each leaf map either has its range on one side or is injective with full range. -/
lemma eq_bot_or_eq_bot_of_range_side_or_bijective {k : Type*} [Field k] (ρ : FourVertexStarRepresentation k)
    (hind : ρ.IsIndecomposable)
    (p q : Submodule k ρ.center) (hpq : IsCompl p q)
    (h₁ : (LinearMap.range ρ.leafOneToCenter ≤ p ∨ LinearMap.range ρ.leafOneToCenter ≤ q) ∨
           (Function.Injective ρ.leafOneToCenter ∧ LinearMap.range ρ.leafOneToCenter = ⊤))
    (h₂ : (LinearMap.range ρ.leafTwoToCenter ≤ p ∨ LinearMap.range ρ.leafTwoToCenter ≤ q) ∨
           (Function.Injective ρ.leafTwoToCenter ∧ LinearMap.range ρ.leafTwoToCenter = ⊤))
    (h₃ : (LinearMap.range ρ.leafThreeToCenter ≤ p ∨ LinearMap.range ρ.leafThreeToCenter ≤ q) ∨
           (Function.Injective ρ.leafThreeToCenter ∧ LinearMap.range ρ.leafThreeToCenter = ⊤)) :
    p = ⊥ ∨ q = ⊥ := by

  have arm₁ : ∃ (p₁ q₁ : Submodule k ρ.leafOne), IsCompl p₁ q₁ ∧
      (∀ x ∈ p₁, ρ.leafOneToCenter x ∈ p) ∧ (∀ x ∈ q₁, ρ.leafOneToCenter x ∈ q) := by
    rcases h₁ with (h | h) | ⟨hinj, hsurj⟩
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
    · exact ⟨Submodule.comap ρ.leafOneToCenter p, Submodule.comap ρ.leafOneToCenter q,
        isCompl_comap_of_range_eq_top ρ.leafOneToCenter hinj hsurj p q hpq,
        fun x hx => hx, fun x hx => hx⟩
  have arm₂ : ∃ (p₂ q₂ : Submodule k ρ.leafTwo), IsCompl p₂ q₂ ∧
      (∀ x ∈ p₂, ρ.leafTwoToCenter x ∈ p) ∧ (∀ x ∈ q₂, ρ.leafTwoToCenter x ∈ q) := by
    rcases h₂ with (h | h) | ⟨hinj, hsurj⟩
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
    · exact ⟨Submodule.comap ρ.leafTwoToCenter p, Submodule.comap ρ.leafTwoToCenter q,
        isCompl_comap_of_range_eq_top ρ.leafTwoToCenter hinj hsurj p q hpq,
        fun x hx => hx, fun x hx => hx⟩
  have arm₃ : ∃ (p₃ q₃ : Submodule k ρ.leafThree), IsCompl p₃ q₃ ∧
      (∀ x ∈ p₃, ρ.leafThreeToCenter x ∈ p) ∧ (∀ x ∈ q₃, ρ.leafThreeToCenter x ∈ q) := by
    rcases h₃ with (h | h) | ⟨hinj, hsurj⟩
    · exact ⟨⊤, ⊥, isCompl_top_bot,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩),
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _⟩
    · exact ⟨⊥, ⊤, isCompl_bot_top,
        fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
        fun x _ => h (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩
    · exact ⟨Submodule.comap ρ.leafThreeToCenter p, Submodule.comap ρ.leafThreeToCenter q,
        isCompl_comap_of_range_eq_top ρ.leafThreeToCenter hinj hsurj p q hpq,
        fun x hx => hx, fun x hx => hx⟩
  obtain ⟨p₁, q₁, hc₁, hp₁, hq₁⟩ := arm₁
  obtain ⟨p₂, q₂, hc₂, hp₂, hq₂⟩ := arm₂
  obtain ⟨p₃, q₃, hc₃, hp₃, hq₃⟩ := arm₃
  have := hind.2 p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hc₁ hc₂ hc₃ hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  rcases this with ⟨hp, _, _, _⟩ | ⟨hq, _, _, _⟩
  · left; exact hp
  · right; exact hq

/-- Complementary submodules pull back to complementary submodules along an injective map when the first is contained in the range. -/
lemma isCompl_comap_of_le_range {k : Type*} [Field k]
    {V₁ V : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V₁] [FiniteDimensional k V]
    (A : V₁ →ₗ[k] V) (hA_inj : Function.Injective A)
    (p q : Submodule k V) (hpq : IsCompl p q) (hle : p ≤ LinearMap.range A) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff]; ext x
    simp only [Submodule.mem_sup, Submodule.mem_comap, Submodule.mem_top, iff_true]
    obtain ⟨yp, hyp, yq, hyq, heq⟩ := Submodule.mem_sup.mp
      (show A x ∈ p ⊔ q from hpq.sup_eq_top ▸ Submodule.mem_top)
    have hAx : A x ∈ LinearMap.range A := LinearMap.mem_range.mpr ⟨x, rfl⟩
    have hyp_range : yp ∈ LinearMap.range A := hle hyp
    have hyq_range : yq ∈ LinearMap.range A := by
      have hsub : A x - yp ∈ LinearMap.range A := (LinearMap.range A).sub_mem hAx hyp_range
      rwa [show A x - yp = yq from by rw [← heq]; abel] at hsub
    obtain ⟨x₁, hx₁⟩ := LinearMap.mem_range.mp hyp_range
    obtain ⟨x₂, hx₂⟩ := LinearMap.mem_range.mp hyq_range
    have : x = x₁ + x₂ := hA_inj (by rw [map_add, hx₁, hx₂, heq])
    exact ⟨x₁, show A x₁ ∈ p from hx₁ ▸ hyp,
           x₂, show A x₂ ∈ q from hx₂ ▸ hyq, this.symm⟩

/-- A submodule disjoint from a given submodule is contained in some complementary submodule of the latter. -/
lemma exists_isCompl_of_disjoint {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V]
    (p S : Submodule k V) (hdisj : Disjoint S p) :
    ∃ q : Submodule k V, IsCompl p q ∧ S ≤ q := by
  obtain ⟨q, hSq, hqp⟩ := hdisj.exists_isCompl
  exact ⟨q, hqp.symm, hSq⟩

/-- For an injective linear map and complementary submodules comparable with its range, there are complementary source submodules whose images lie in the given pair. -/
lemma exists_isCompl_mappedInto_of_range_comparable {k : Type*} [Field k]
    {V W : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (A : W →ₗ[k] V) (hA_inj : Function.Injective A)
    (p q : Submodule k V) (hpq : IsCompl p q)
    (hcond : p ≤ LinearMap.range A ∨ LinearMap.range A ≤ q) :
    ∃ (pW qW : Submodule k W), IsCompl pW qW ∧
      (∀ x ∈ pW, A x ∈ p) ∧ (∀ x ∈ qW, A x ∈ q) := by
  rcases hcond with hle | hle
  · exact ⟨Submodule.comap A p, Submodule.comap A q,
      isCompl_comap_of_le_range A hA_inj p q hpq hle,
      fun x hx => hx, fun x hx => hx⟩
  · exact ⟨⊥, ⊤, isCompl_bot_top,
      fun x hx => by rw [(Submodule.mem_bot (R := k)).mp hx, map_zero]; exact zero_mem _,
      fun x _ => hle (LinearMap.mem_range.mpr ⟨x, rfl⟩)⟩

/-- Complementary submodules pull back along an injective linear map when every vector in its range decomposes into range elements lying in the two submodules. -/
lemma isCompl_comap_of_range_decomposition {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    {V' : Type*} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (p q : Submodule k W) (hpq : IsCompl p q)
    (A : V' →ₗ[k] W) (hA_inj : Function.Injective A)
    (R : Submodule k W) (hR_eq : LinearMap.range A = R)
    (hR_split : ∀ x ∈ R, ∃ a ∈ R, ∃ b ∈ R, a ∈ p ∧ b ∈ q ∧ a + b = x) :
    IsCompl (Submodule.comap A p) (Submodule.comap A q) ∧
      (∀ x ∈ Submodule.comap A p, A x ∈ p) ∧
      (∀ x ∈ Submodule.comap A q, A x ∈ q) := by
  refine ⟨⟨?_, ?_⟩, fun x hx => hx, fun x hx => hx⟩
  · rw [Submodule.disjoint_def]
    intro x hxp hxq
    have : A x ∈ p ⊓ q := ⟨hxp, hxq⟩
    rw [hpq.inf_eq_bot, Submodule.mem_bot] at this
    exact hA_inj (this.trans (map_zero _).symm)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hAx_mem : A x ∈ R := hR_eq ▸ LinearMap.mem_range.mpr ⟨x, rfl⟩
    obtain ⟨a, ha_R, b, hb_R, ha_p, hb_q, hab⟩ := hR_split (A x) hAx_mem
    obtain ⟨a', rfl⟩ := LinearMap.mem_range.mp (hR_eq ▸ ha_R)
    obtain ⟨b', rfl⟩ := LinearMap.mem_range.mp (hR_eq ▸ hb_R)
    have : x = a' + b' := hA_inj (by rw [map_add, hab])
    rw [this]
    exact Submodule.add_mem_sup (Submodule.mem_comap.mpr ha_p) (Submodule.mem_comap.mpr hb_q)

end RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations
