/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.CategoryTheory.QuiverAuxiliary
import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import RepresentationTheory.Alignment.Attribute

/-!
# Vertex composition series

This module develops vertex-indexed composition series for quiver linear diagrams.
-/

open Module
open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
open RepresentationTheory.CategoryTheory.QuiverLinearMaps
open RepresentationTheory.CategoryTheory.QuiverAuxiliary

variable {k Q : Type*} [Field k] [Quiver Q] {ρ : AuxiliaryQuiverModuleData k Q}

namespace RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType

/-- Two subrepresentations with equal components at every vertex are equal. -/
@[ext]
theorem ext {W W' : AuxiliaryType k Q ρ}
    (h : ∀ v, W.carrier v = W'.carrier v) : W = W' := by
  obtain ⟨c, hc⟩ := W
  obtain ⟨c', hc'⟩ := W'
  have hcc : c = c' := funext h
  subst hcc
  rfl

/-- The partial-order structure on subrepresentations of a quiver representation. -/
instance partialOrder : PartialOrder (AuxiliaryType k Q ρ) where
  le W W' := ∀ v, W.carrier v ≤ W'.carrier v
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ v := (h₁ v).trans (h₂ v)
  le_antisymm _ _ h₁ h₂ := ext fun v => le_antisymm (h₁ v) (h₂ v)

/-- One subrepresentation is below another exactly when this holds for every vertex component. -/
theorem le_iff_componentwise {W W' : AuxiliaryType k Q ρ} :
    W ≤ W' ↔ ∀ v, W.carrier v ≤ W'.carrier v := Iff.rfl

/-- The order-bottom structure on subrepresentations of a quiver representation. -/
instance orderBot : OrderBot (AuxiliaryType k Q ρ) where
  bot :=
    { carrier := fun _ => ⊥
      map_mem := by
        intro v w e x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero] }
  bot_le _ _ := bot_le

/-- The order-top structure on subrepresentations of a quiver representation. -/
instance orderTop : OrderTop (AuxiliaryType k Q ρ) where
  top :=
    { carrier := fun _ => ⊤
      map_mem := fun _ _ _ => Submodule.mem_top }
  le_top _ _ := le_top

/-- Every component of the bottom subrepresentation is the bottom submodule. -/
@[simp] theorem bot_component (v : Q) :
    (⊥ : AuxiliaryType k Q ρ).carrier v = ⊥ := rfl

/-- Every component of the top subrepresentation is the top submodule. -/
@[simp] theorem top_component (v : Q) :
    (⊤ : AuxiliaryType k Q ρ).carrier v = ⊤ := rfl

/-- The quiver representation carried by a subrepresentation. -/
@[reducible] def toRepresentation (W : AuxiliaryType k Q ρ) : AuxiliaryQuiverModuleData k Q where
  obj v := W.carrier v
  map e := (ρ.map e).restrict (fun x hx => W.map_mem e x hx)

/-- The component of one subrepresentation viewed as a submodule inside the component of another. -/
def componentIntersection (W W' : AuxiliaryType k Q ρ) (v : Q) : Submodule k (W'.carrier v) :=
  (W.carrier v).comap (W'.carrier v).subtype

/-- An element of the upper component belongs to the component intersection exactly when its value lies in the lower component. -/
theorem mem_componentIntersection_iff {W W' : AuxiliaryType k Q ρ} {v : Q} {x : W'.carrier v} :
    x ∈ W.componentIntersection W' v ↔ (x : ρ.obj v) ∈ W.carrier v := Iff.rfl

/-- The component intersection is top exactly when the second component is contained in the first. -/
theorem componentIntersection_eq_top_iff {W W' : AuxiliaryType k Q ρ} {v : Q} :
    W.componentIntersection W' v = ⊤ ↔ W'.carrier v ≤ W.carrier v := by
  rw [eq_top_iff]
  constructor
  · intro h x hx
    exact (mem_componentIntersection_iff (W := W) (W' := W') (x := ⟨x, hx⟩)).1 (h Submodule.mem_top)
  · intro h x _
    exact h x.2

end RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType

namespace RepresentationTheory.QuiverRepresentation.VertexCompositionSeries

/-- A quiver representation associated with a selected vertex. -/
def representationAtVertex [DecidableEq Q] (i : Q) : AuxiliaryQuiverModuleData k Q where
  obj v := Fin (if v = i then 1 else 0) → k
  map _ := 0

/-- Every arrow map in the representation associated with a vertex is zero. -/
@[simp] theorem representationAtVertex_map_eq_zero [DecidableEq Q] (i : Q) {v w : Q} (e : v ⟶ w) :
    (representationAtVertex (k := k) i).map e = 0 := rfl

/-- The finite type whose size tests equality of a value with itself has a unique element. -/
@[reducible] def unique_fin_ite_self [DecidableEq Q] (i : Q) : Unique (Fin (if i = i then 1 else 0)) := by
  rw [if_pos rfl]; infer_instance

omit [Quiver Q] in

/-- For distinct values, the finite type whose size is one only when they are equal is empty. -/
theorem isEmpty_fin_ite_eq_of_ne [DecidableEq Q] {u i : Q} (h : u ≠ i) :
    IsEmpty (Fin (if u = i then 1 else 0)) := by
  rw [if_neg h]; infer_instance

/-- At a vertex different from the selected one, the associated representation space is a subsingleton. -/
theorem representationAtVertex_space_subsingleton_of_ne [DecidableEq Q] {u i : Q} (h : u ≠ i) :
    Subsingleton ((representationAtVertex (k := k) i).obj u) :=
  ⟨fun _ _ => funext fun x => (isEmpty_fin_ite_eq_of_ne h).elim x⟩

/-- A designated elementary-extension relation between two subrepresentations at a vertex. -/
@[source_ref "Chapter6/Problem6.9.3" (role := supporting)]
def IsElementaryExtensionAt [DecidableEq Q] (W W' : AuxiliaryType k Q ρ) (i : Q) : Prop :=
  W ≤ W' ∧ ∃ π : AuxiliaryQuiverLinearMapData k Q W'.toRepresentation (representationAtVertex i),
    (∀ v, Function.Surjective (π.app v)) ∧
    ∀ v, LinearMap.ker (π.app v) = W.componentIntersection W' v

/-- An auxiliary result whose formal type is unavailable. -/
theorem auxiliary_theorem {M : Type*} [AddCommMonoid M] [Module k M] (x y : M) :
    (x + (-1 : k) • y) + y = x := by
  rw [add_assoc]
  nth_rw 2 [show y = (1 : k) • y from (one_smul k y).symm]
  rw [← add_smul, neg_add_cancel, zero_smul, add_zero]

/-- Componentwise containment, a surjective functional with the specified kernel, and arrow compatibility imply an elementary extension at the selected vertex. -/
theorem isElementaryExtensionAt_of_linearMap [DecidableEq Q] {W W' : AuxiliaryType k Q ρ} {i : Q}
    (hle : W ≤ W')
    (heq : ∀ u, u ≠ i → W'.carrier u ≤ W.carrier u)
    (φ : W'.carrier i →ₗ[k] k)
    (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = W.componentIntersection W' i)
    (hnat : ∀ {u : Q} (e : u ⟶ i) (x : W'.toRepresentation.obj u), φ (W'.toRepresentation.map e x) = 0) :
    IsElementaryExtensionAt W W' i := by
  classical
  set app : ∀ u, W'.toRepresentation.obj u →ₗ[k] (representationAtVertex (k := k) i).obj u := fun u =>
    if h : u = i then by subst h; exact LinearMap.pi (fun _ => φ) else 0 with happ_def
  have happ_self : app i = LinearMap.pi (fun _ => φ) := by
    simp only [happ_def, dif_pos rfl]
  have happ_other : ∀ u, u ≠ i → app u = 0 := by
    intro u hu; simp only [happ_def, dif_neg hu]
  have hnaturality : ∀ {v w : Q} (e : v ⟶ w) (x : W'.toRepresentation.obj v),
      app w (W'.toRepresentation.map e x) = (representationAtVertex (k := k) i).map e (app v x) := by

    intro v w e x
    rw [representationAtVertex_map_eq_zero, LinearMap.zero_apply]
    rcases eq_or_ne w i with rfl | hw
    · rw [happ_self]
      funext l
      exact hnat e x
    · rw [happ_other w hw]
      rfl
  have hsurj' : ∀ u, Function.Surjective (app u) := by
    intro u
    rcases eq_or_ne u i with rfl | hu
    · rw [happ_self]
      haveI := unique_fin_ite_self u
      intro g
      obtain ⟨x, hx⟩ := hsurj (g default)
      refine ⟨x, funext fun l => ?_⟩
      rw [Subsingleton.elim l default]
      exact hx
    · haveI := representationAtVertex_space_subsingleton_of_ne (k := k) hu
      intro g
      exact ⟨0, Subsingleton.elim _ _⟩
  have hker' : ∀ u, LinearMap.ker (app u) = W.componentIntersection W' u := by
    intro u
    rcases eq_or_ne u i with rfl | hu
    · rw [happ_self, ← hker]
      haveI := unique_fin_ite_self u
      ext x
      simp only [LinearMap.mem_ker]
      constructor
      · intro h
        exact congrFun h default
      · intro h
        funext l
        exact h
    · rw [happ_other u hu, LinearMap.ker_zero]
      exact (AuxiliaryType.componentIntersection_eq_top_iff.2 (heq u hu)).symm
  exact ⟨hle, ⟨{ app := app, naturality := hnaturality }, hsurj', hker'⟩⟩

namespace IsElementaryExtensionAt

variable [DecidableEq Q] {W W' : AuxiliaryType k Q ρ} {i : Q}

/-- The lower endpoint of an elementary extension is below its upper endpoint. -/
theorem le (h : IsElementaryExtensionAt W W' i) : W ≤ W' := h.1

/-- An elementary extension admits a surjective linear functional whose kernel is the component intersection at the selected vertex. -/
theorem exists_surjective_linearMap_ker_componentIntersection (h : IsElementaryExtensionAt W W' i) :
    ∃ ψ : W'.toRepresentation.obj i →ₗ[k] k,
      Function.Surjective ψ ∧ LinearMap.ker ψ = W.componentIntersection W' i := by
  obtain ⟨hle, π, hsurj, hker⟩ := h
  haveI := unique_fin_ite_self i
  refine ⟨(LinearMap.proj default) ∘ₗ (π.app i), ?_, ?_⟩
  · intro c
    obtain ⟨x, hx⟩ := hsurj i (fun _ => c)
    exact ⟨x, by rw [LinearMap.comp_apply, hx]; rfl⟩
  · rw [← hker i]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hh
      funext l
      rw [Subsingleton.elim l default]
      exact hh
    · intro hh
      rw [hh]
      rfl

/-- Subrepresentations in an elementary extension at one vertex have equal components at every other vertex. -/
theorem component_eq_of_ne (h : IsElementaryExtensionAt W W' i) {u : Q} (hu : u ≠ i) :
    W.carrier u = W'.carrier u := by
  obtain ⟨hle, π, _, hker⟩ := h
  haveI := representationAtVertex_space_subsingleton_of_ne (k := k) (i := i) hu
  refine le_antisymm (hle u) ?_
  rw [← AuxiliaryType.componentIntersection_eq_top_iff, ← hker u]
  exact eq_top_iff.2 fun x _ => by
    simp only [LinearMap.mem_ker]
    exact Subsingleton.elim _ _

/-- The endpoints of an elementary extension are distinct. -/
theorem ne (h : IsElementaryExtensionAt W W' i) : W ≠ W' := by
  rintro rfl
  obtain ⟨ψ, hsurj, hker⟩ := h.exists_surjective_linearMap_ker_componentIntersection
  obtain ⟨x, hx⟩ := hsurj 1
  have hmem : x ∈ LinearMap.ker ψ := by
    rw [hker]
    exact (AuxiliaryType.mem_componentIntersection_iff (W := W) (W' := W)).2 x.2
  rw [LinearMap.mem_ker, hx] at hmem
  exact one_ne_zero hmem

/-- Every subrepresentation between the endpoints of an elementary extension equals one of the endpoints. -/
theorem eq_or_eq_of_le (h : IsElementaryExtensionAt W W' i) (U : AuxiliaryType k Q ρ)
    (h₁ : W ≤ U) (h₂ : U ≤ W') : U = W ∨ U = W' := by
  classical
  obtain ⟨ψ, hsurj, hker⟩ := h.exists_surjective_linearMap_ker_componentIntersection
  by_cases hU : ∃ y : W'.toRepresentation.obj i, (y : ρ.obj i) ∈ U.carrier i ∧ ψ y ≠ 0
  ·
    right
    obtain ⟨y, hyU, hy0⟩ := hU
    refine le_antisymm h₂ fun u x hx => ?_
    rcases eq_or_ne u i with rfl | hu
    ·
      set xx : W'.toRepresentation.obj u := ⟨x, hx⟩ with hxx
      set y' : W'.toRepresentation.obj u := (ψ xx / ψ y) • y with hy'
      set z : W'.toRepresentation.obj u := xx + (-1 : k) • y' with hz
      have hzker : z ∈ LinearMap.ker ψ := by
        rw [LinearMap.mem_ker, hz, map_add, map_smul, hy', map_smul]
        simp only [smul_eq_mul]
        field_simp
        ring
      rw [hker] at hzker
      have hzU : (z : ρ.obj u) ∈ U.carrier u := h₁ u hzker
      have hyU' : (y' : ρ.obj u) ∈ U.carrier u := (U.carrier u).smul_mem _ hyU
      have hsum : z + y' = xx := auxiliary_theorem (k := k) xx y'
      have hmem : ((z + y' : W'.toRepresentation.obj u) : ρ.obj u) ∈ U.carrier u :=
        (U.carrier u).add_mem hzU hyU'
      rw [hsum] at hmem
      exact hmem
    · rw [← h.component_eq_of_ne hu] at hx
      exact h₁ u hx
  ·
    left
    simp only [not_exists, not_and, not_not] at hU
    refine le_antisymm (fun u x hx => ?_) h₁
    rcases eq_or_ne u i with rfl | hu
    · have hxW' : x ∈ W'.carrier u := h₂ u hx
      have hzero : ψ ⟨x, hxW'⟩ = 0 := hU ⟨x, hxW'⟩ hx
      have hmem : (⟨x, hxW'⟩ : W'.toRepresentation.obj u) ∈ LinearMap.ker ψ := by
        rw [LinearMap.mem_ker]; exact hzero
      rw [hker] at hmem
      exact hmem
    · rw [h.component_eq_of_ne hu]
      exact h₂ u hx

end IsElementaryExtensionAt

/-- Data for a finite chain of subrepresentations whose successive steps are indexed by vertices. -/
@[source_ref "Chapter6/Problem6.9.3" (role := supporting)]
structure VertexCompositionSeries [DecidableEq Q] (ρ : AuxiliaryQuiverModuleData k Q) where
  /-- The number of steps in the vertex composition series. -/
  length : ℕ
  /-- The subrepresentation at a natural-number stage of the composition series. -/
  step : ℕ → AuxiliaryType k Q ρ
  /-- The vertex associated with a step of the composition series. -/
  vertex : Fin length → Q
  /-- The initial step of the series is the bottom subrepresentation. -/
  step_zero : step 0 = ⊥
  /-- The step at the length of the series is the top subrepresentation. -/
  step_length : step length = ⊤
  /-- Each consecutive pair of steps forms an elementary extension at its associated vertex. -/
  isElementaryExtensionAt_step : ∀ m : Fin length,
    IsElementaryExtensionAt (step (m : ℕ)) (step ((m : ℕ) + 1)) (vertex m)

namespace VertexCompositionSeries

variable [DecidableEq Q]

/-- The natural-number multiplicity assigned by the series to each vertex. -/
def multiplicity (s : VertexCompositionSeries ρ) (i : Q) : ℕ :=
  (Finset.univ.filter fun m => s.vertex m = i).card

/-- Each indexed step below the length differs from its successor. -/
theorem step_ne_step_succ (s : VertexCompositionSeries ρ) (m : Fin s.length) :
    s.step (m : ℕ) ≠ s.step ((m : ℕ) + 1) :=
  (s.isElementaryExtensionAt_step m).ne

end VertexCompositionSeries

/-- A number below a finite sum lies between one prefix sum and that prefix sum plus the next term. -/
theorem exists_prefixSum_le_lt {f : ℕ → ℕ} {n m : ℕ} (hm : m < ∑ l ∈ Finset.range n, f l) :
    ∃ j, j < n ∧ (∑ l ∈ Finset.range j, f l) ≤ m ∧
      m < (∑ l ∈ Finset.range j, f l) + f j := by
  induction n with
  | zero => simp at hm
  | succ n ih =>
    rw [Finset.sum_range_succ] at hm
    rcases lt_or_ge m (∑ l ∈ Finset.range n, f l) with h | h
    · obtain ⟨j, hj, h₁, h₂⟩ := ih h
      exact ⟨j, by omega, h₁, h₂⟩
    · exact ⟨n, by omega, h, by omega⟩

/-- For a finite vertex ordering that decreases along arrows and chosen vertex-space bases, there exists a series whose length is the sum of dimensions and whose vertex multiplicities are those dimensions. -/
@[source_ref "Chapter6/Problem6.9.3" (role := supporting)]
theorem exists_vertexCompositionSeries_with_multiplicity [DecidableEq Q] (ρ : AuxiliaryQuiverModuleData k Q)
    (n : ℕ) (e : Q ≃ Fin n) (hcompat : ∀ {v w : Q}, (v ⟶ w) → (e w : ℕ) < (e v : ℕ))
    (d : Q → ℕ) (b : ∀ v, Basis (Fin (d v)) k (ρ.obj v)) :
    ∃ s : VertexCompositionSeries ρ,
      s.length = ∑ l : Fin n, d (e.symm l) ∧ ∀ i, s.multiplicity i = d i := by
  classical

  set f : ℕ → ℕ := fun l => if h : l < n then d (e.symm ⟨l, h⟩) else 0 with hf_def
  set cum : Q → ℕ := fun v => ∑ l ∈ Finset.range (e v : ℕ), f l with hcum_def
  set N : ℕ := ∑ l ∈ Finset.range n, f l with hN_def
  have hf_eq : ∀ v : Q, f (e v : ℕ) = d v := by
    intro v
    simp only [hf_def, dif_pos (e v).isLt, Fin.eta, Equiv.symm_apply_apply]
  have hcum_step : ∀ v : Q, cum v + d v = ∑ l ∈ Finset.range ((e v : ℕ) + 1), f l := by
    intro v
    rw [Finset.sum_range_succ, hf_eq]

  have hcum_le : ∀ {v w : Q}, (e w : ℕ) < (e v : ℕ) → cum w + d w ≤ cum v := by
    intro v w h
    rw [hcum_step]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
  have hcum_top : ∀ v : Q, cum v + d v ≤ N := by
    intro v
    rw [hcum_step, hN_def]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (e v).isLt)

  set flag : ℕ → ∀ v : Q, Submodule k (ρ.obj v) := fun m v =>
    ⨅ l : {l : Fin (d v) // m ≤ cum v + (l : ℕ)},
      LinearMap.ker ((b v).coord (l : Fin (d v))) with hflag_def
  have hmem : ∀ (m : ℕ) (v : Q) (x : ρ.obj v),
      x ∈ flag m v ↔ ∀ l : Fin (d v), m ≤ cum v + (l : ℕ) → (b v).coord l x = 0 := by
    intro m v x
    simp [hflag_def, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  have hzero : ∀ (m : ℕ) (v : Q) (x : ρ.obj v), m ≤ cum v → x ∈ flag m v → x = 0 := by
    intro m v x hm hx
    refine (b v).ext_elem fun j => ?_
    rw [map_zero, Finsupp.zero_apply, ← Basis.coord_apply]
    exact (hmem m v x).1 hx j (by omega)
  have htop : ∀ (m : ℕ) (v : Q), cum v + d v ≤ m → flag m v = ⊤ := by
    intro m v hm
    refine eq_top_iff.2 fun x _ => (hmem m v x).2 fun l hl => ?_
    exact absurd hl (by have := l.isLt; omega)
  have hmono : ∀ {m m' : ℕ}, m ≤ m' → ∀ v, flag m v ≤ flag m' v := by
    intro m m' hmm v x hx
    exact (hmem m' v x).2 fun l hl => (hmem m v x).1 hx l (by omega)

  have hinv : ∀ (m : ℕ) {v w : Q} (arr : v ⟶ w) (x : ρ.obj v),
      x ∈ flag m v → ρ.map arr x ∈ flag m w := by
    intro m v w arr x hx
    rcases le_or_gt m (cum v) with hm | hm
    · rw [hzero m v x hm hx, map_zero]
      exact Submodule.zero_mem _
    · have hle := hcum_le (hcompat arr)
      rw [htop m w (by omega)]
      exact Submodule.mem_top
  set sub : ℕ → AuxiliaryType k Q ρ := fun m =>
    ⟨flag m, fun arr x hx => hinv m arr x hx⟩ with hsub_def
  have hsub_carrier : ∀ m v, (sub m).carrier v = flag m v := fun _ _ => rfl

  have hsub_zero : sub 0 = ⊥ := by
    refine AuxiliaryType.ext fun v => eq_bot_iff.2 fun x hx => ?_
    rw [Submodule.mem_bot]
    exact hzero 0 v x (Nat.zero_le _) hx
  have hsub_N : sub N = ⊤ := by
    exact AuxiliaryType.ext fun v => htop N v (hcum_top v)

  have hblock : ∀ m : Fin N, ∃ v : Q, cum v ≤ (m : ℕ) ∧ (m : ℕ) < cum v + d v := by
    intro m
    obtain ⟨j, hj, h₁, h₂⟩ := exists_prefixSum_le_lt (f := f) (n := n) (m := (m : ℕ)) m.isLt
    refine ⟨e.symm ⟨j, hj⟩, ?_, ?_⟩
    · simpa [hcum_def] using h₁
    · have hfe : f j = d (e.symm ⟨j, hj⟩) := by simp [hf_def, dif_pos hj]
      simpa [hcum_def, hfe] using h₂
  choose factor hfac₁ hfac₂ using hblock
  have huniq : ∀ (m : ℕ) (v w : Q), cum v ≤ m → m < cum v + d v → cum w ≤ m →
      m < cum w + d w → v = w := by
    intro m v w h₁ h₂ h₃ h₄
    rcases lt_trichotomy ((e v : ℕ)) ((e w : ℕ)) with h | h | h
    · exact absurd (hcum_le h) (by omega)
    · exact e.injective (Fin.ext h)
    · exact absurd (hcum_le h) (by omega)
  have hfactor_eq : ∀ (m : Fin N) (v : Q), cum v ≤ (m : ℕ) → (m : ℕ) < cum v + d v →
      factor m = v := fun m v h₁ h₂ => huniq (m : ℕ) (factor m) v (hfac₁ m) (hfac₂ m) h₁ h₂

  have hstep : ∀ m : Fin N, IsElementaryExtensionAt (sub (m : ℕ)) (sub ((m : ℕ) + 1)) (factor m) := by
    intro m
    set i : Q := factor m with hi_def
    have hcl : cum i ≤ (m : ℕ) := hfac₁ m
    have hcu : (m : ℕ) < cum i + d i := hfac₂ m

    set r : Fin (d i) := ⟨(m : ℕ) - cum i, by omega⟩ with hr_def
    have hr_val : cum i + (r : ℕ) = (m : ℕ) := by simp only [hr_def]; omega

    have heq : ∀ u, u ≠ i → (sub ((m : ℕ) + 1)).carrier u ≤ (sub (m : ℕ)).carrier u := by
      intro u hu x hx
      refine (hmem (m : ℕ) u x).2 fun l hl => ?_
      rcases le_or_gt ((m : ℕ) + 1) (cum u + (l : ℕ)) with h | h
      · exact (hmem ((m : ℕ) + 1) u x).1 hx l h
      · exact absurd (hfactor_eq m u (by omega) (by have := l.isLt; omega)).symm hu
    refine isElementaryExtensionAt_of_linearMap (hmono (Nat.le_succ _)) heq
      (((b i).coord r).comp ((sub ((m : ℕ) + 1)).carrier i).subtype) ?_ ?_ ?_
    ·
      intro c
      have hmemc : c • (b i) r ∈ (sub ((m : ℕ) + 1)).carrier i := by
        refine (hmem ((m : ℕ) + 1) i _).2 fun l hl => ?_
        have hlr : l ≠ r := by rintro rfl; omega
        simp [Basis.coord_apply, hlr]
      exact ⟨⟨_, hmemc⟩, by simp [Basis.coord_apply]⟩
    ·
      ext x
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        AuxiliaryType.mem_componentIntersection_iff, hsub_carrier]
      constructor
      · intro h
        refine (hmem (m : ℕ) i (x : ρ.obj i)).2 fun l hl => ?_
        rcases le_or_gt ((m : ℕ) + 1) (cum i + (l : ℕ)) with h' | h'
        · exact (hmem ((m : ℕ) + 1) i _).1 x.2 l h'
        · have : l = r := Fin.ext (by omega)
          rw [this]; exact h
      · intro h
        exact (hmem (m : ℕ) i _).1 h r (by omega)
    ·
      intro u arr x
      have hlt : (e i : ℕ) < (e u : ℕ) := hcompat arr
      have hle := hcum_le hlt
      have hx0 : (x : ρ.obj u) = 0 := hzero ((m : ℕ) + 1) u _ (by omega) x.2
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [show ((sub ((m : ℕ) + 1)).toRepresentation.map arr x : ρ.obj i) =
            ρ.map arr (x : ρ.obj u) from rfl, hx0, map_zero, map_zero]
  refine ⟨⟨N, sub, factor, hsub_zero, hsub_N, hstep⟩, ?_, ?_⟩
  · change N = ∑ l : Fin n, d (e.symm l)
    rw [hN_def, ← Fin.sum_univ_eq_sum_range (fun l => f l) n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hf_def, dif_pos l.isLt]
  ·
    intro i
    change (Finset.univ.filter fun m : Fin N => factor m = i).card = d i
    rw [← Finset.card_range (d i)]
    refine Finset.card_bij' (fun m _ => (m : ℕ) - cum i)
      (fun j hj => ⟨cum i + j, ?_⟩) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_range] at hj
      have := hcum_top i
      omega
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have h₁ := hfac₁ m
      have h₂ := hfac₂ m
      rw [hm.2] at h₁ h₂
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfactor_eq _ i (by simp) (by simp; omega)
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have h₁ := hfac₁ m
      rw [hm.2] at h₁
      exact Fin.ext (by simp; omega)
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp

end RepresentationTheory.QuiverRepresentation.VertexCompositionSeries
