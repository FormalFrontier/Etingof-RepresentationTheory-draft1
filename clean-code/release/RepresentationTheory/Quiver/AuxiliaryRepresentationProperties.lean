/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.FiniteTypeCriterion
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary Representation Properties -/

namespace RepresentationTheory.Quiver.AuxiliaryRepresentationProperties

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
open RepresentationTheory.CategoryTheory.QuiverLinearMaps
open RepresentationTheory.Quiver.FiniteTypeCriterion
open RepresentationTheory.AuxiliaryIntegerMatrixProperty
open RepresentationTheory.Quiver.MatrixOrientation

section EquivGroupoid

variable {k Q : Type*} [CommSemiring k] [Quiver Q] {ρ₁ ρ₂ ρ₃ : AuxiliaryQuiverModuleData k Q}

/-- The equivalence obtained by reversing the source and target representations. -/
def _root_.RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData.symm (e : AuxiliaryQuiverEquivData k Q ρ₁ ρ₂) :
    AuxiliaryQuiverEquivData k Q ρ₂ ρ₁ where
  app v := (e.app v).symm
  naturality {v w} f x := by
    rw [LinearEquiv.symm_apply_eq, e.naturality f, LinearEquiv.apply_symm_apply]

/-- The composite of equivalences between three quiver representations. -/
def _root_.RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData.trans (e₁ : AuxiliaryQuiverEquivData k Q ρ₁ ρ₂)
    (e₂ : AuxiliaryQuiverEquivData k Q ρ₂ ρ₃) :
    AuxiliaryQuiverEquivData k Q ρ₁ ρ₃ where
  app v := (e₁.app v).trans (e₂.app v)
  naturality {v w} f x := by
    simp only [LinearEquiv.trans_apply]
    rw [e₁.naturality f, e₂.naturality f]

end EquivGroupoid

section Helpers

variable (k : Type*) [CommSemiring k]

/-- An auxiliary linear map between two finite field-valued function spaces. -/
def auxiliaryFinFunctionLinearMap (p q : ℕ) : (Fin p → k) →ₗ[k] (Fin q → k) where
  toFun x i := if h : (i : ℕ) < p then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i; by_cases h : (i : ℕ) < p <;> simp [h]
  map_smul' a x := by
    funext i; by_cases h : (i : ℕ) < p <;> simp [h]

/-- The linear equivalence from field-valued functions on `Fin p` to the field when `p = 1`. -/
def finOneLinearEquiv {p : ℕ} (hp : p = 1) : (Fin p → k) ≃ₗ[k] k where
  toFun x := x ⟨0, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun t := fun _ => t
  left_inv x := by
    subst hp
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- The one-coordinate linear equivalence evaluates a function at the zeroth index. -/
@[simp] lemma finOneLinearEquiv_apply {p : ℕ} (hp : p = 1) (x : Fin p → k) :
    finOneLinearEquiv k hp x = x ⟨0, by omega⟩ := rfl

/-- The inverse one-coordinate equivalence sends a scalar to the constant function with that value. -/
@[simp] lemma finOneLinearEquiv_symm_apply {p : ℕ} (hp : p = 1) (t : k) (i : Fin p) :
    (finOneLinearEquiv k hp).symm t i = t := rfl

/-- Between one-coordinate function spaces, evaluation after the auxiliary finite-function linear map agrees with direct evaluation. -/
lemma finOneLinearEquiv_map_auxiliaryFinFunctionLinearMap {p q : ℕ} (hp : p = 1) (hq : q = 1) (x : Fin p → k) :
    finOneLinearEquiv k hq (auxiliaryFinFunctionLinearMap k p q x) = finOneLinearEquiv k hp x := by
  simp only [finOneLinearEquiv_apply, auxiliaryFinFunctionLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (show (0 : ℕ) < p by omega)]

variable {k}

/-- A module linearly equivalent to a nontrivial coefficient semiring is nontrivial. -/
lemma nontrivial_of_linearEquiv_field {M : Type*} [AddCommMonoid M] [Module k M] [Nontrivial k]
    (E : M ≃ₗ[k] k) : Nontrivial M :=
  ⟨⟨E.symm 0, E.symm 1, fun h => zero_ne_one (E.symm.injective h)⟩⟩

/-- Every submodule of a subsingleton module is bottom. -/
lemma submodule_eq_bot_of_subsingleton {M : Type*} [AddCommMonoid M] [Module k M]
    [Subsingleton M] (W : Submodule k M) : W = ⊥ :=
  eq_bot_iff.mpr fun x _ => (Submodule.mem_bot k).mpr (Subsingleton.elim x 0)

end Helpers

section RankOne

variable {k M : Type*} [Field k] [AddCommMonoid M] [Module k M]

/-- For a module linearly equivalent to its coefficient field, two complementary submodules cannot both be nonzero. -/
lemma eq_bot_or_eq_bot_of_isCompl_of_linearEquiv_field (E : M ≃ₗ[k] k) {W₁ W₂ : Submodule k M} (h : IsCompl W₁ W₂) :
    W₁ = ⊥ ∨ W₂ = ⊥ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W₁).mp h₁
  obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff W₂).mp h₂
  have hEx : E x ≠ 0 := fun hE => hx0 (by simpa using E.injective (hE.trans (map_zero E).symm))
  have hxy : (E y * (E x)⁻¹) • x = y := by
    apply E.injective
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hEx, mul_one]
  have hyW₁ : y ∈ W₁ := hxy ▸ W₁.smul_mem _ hxW
  exact hy0 ((Submodule.mem_bot k).mp (h.disjoint.le_bot ⟨hyW₁, hyW⟩))

end RankOne

section ThinRepresentation

variable (k : Type) [Field k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- The quiver representation supported on a decidable vertex predicate with arrow maps specified by field scalars. -/
abbrev thinRepresentation (S : Fin n → Prop) [DecidablePred S] (c : ∀ a b : Fin n, (a ⟶ b) → k) :
    FiniteQuiverRepresentation k n where
  obj j := Fin (if S j then 1 else 0) → k
  map {a b} e := c a b e • auxiliaryFinFunctionLinearMap k (if S a then 1 else 0) (if S b then 1 else 0)

variable (S : Fin n → Prop) [DecidablePred S]

/-- At a vertex satisfying the support predicate, its one-dimensional finite function space is linearly equivalent to the field. -/
def supportedVertexLinearEquiv {j : Fin n} (hj : S j) : (Fin (if S j then 1 else 0) → k) ≃ₗ[k] k :=
  finOneLinearEquiv k (if_pos hj)

/-- The vertex space of a thin representation is subsingleton outside its support. -/
lemma thinRepresentation_vertex_subsingleton_of_not_support (c : ∀ a b : Fin n, (a ⟶ b) → k) {j : Fin n} (hj : ¬ S j) :
    Subsingleton ((thinRepresentation k S c).obj j) := by
  have h : (if S j then 1 else 0) = 0 := if_neg hj
  refine ⟨fun x y => ?_⟩
  funext i
  exact absurd i.isLt (by omega)

/-- Every vertex space of a thin representation is finite as a module over the field. -/
instance thinRepresentation_vertex_moduleFinite (c : ∀ a b : Fin n, (a ⟶ b) → k) (j : Fin n) :
    Module.Finite k ((thinRepresentation k S c).obj j) :=
  Module.Finite.pi

variable {S}

/-- After identifying supported vertex spaces with the field, a thin-representation arrow map is multiplication by its assigned scalar. -/
lemma supportedVertexLinearEquiv_arrowMap (c : ∀ a b : Fin n, (a ⟶ b) → k) {a b : Fin n} (ha : S a) (hb : S b)
    (e : a ⟶ b) (x : Fin (if S a then 1 else 0) → k) :
    supportedVertexLinearEquiv k S hb ((thinRepresentation k S c).map e x) = c a b e * supportedVertexLinearEquiv k S ha x := by
  change supportedVertexLinearEquiv k S hb ((c a b e • auxiliaryFinFunctionLinearMap k _ _) x) = _
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, supportedVertexLinearEquiv, supportedVertexLinearEquiv,
    finOneLinearEquiv_map_auxiliaryFinFunctionLinearMap]

/-- An arrow map between supported vertices of a thin representation is surjective when its assigned scalar is nonzero. -/
lemma thinRepresentation_arrowMap_surjective (c : ∀ a b : Fin n, (a ⟶ b) → k) {a b : Fin n} (ha : S a)
    (hb : S b) (e : a ⟶ b) (hc : c a b e ≠ 0) :
    Function.Surjective ((thinRepresentation k S c).map e) := by
  intro y
  refine ⟨(supportedVertexLinearEquiv k S ha).symm ((c a b e)⁻¹ * supportedVertexLinearEquiv k S hb y), ?_⟩
  apply (supportedVertexLinearEquiv k S hb).injective
  rw [supportedVertexLinearEquiv_arrowMap k c ha hb, LinearEquiv.apply_symm_apply, ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul]

/-- A thin representation supported on one specified vertex satisfies the displayed unavailable representation property. -/
lemma auxiliaryRepresentationProperty_thinRepresentation_of_support_singleton (c : ∀ a b : Fin n, (a ⟶ b) → k) {v : Fin n}
    (hS : ∀ j, S j ↔ j = v) : (thinRepresentation k S c).AuxiliaryCondition := by
  have hSv : S v := (hS v).mpr rfl
  refine ⟨⟨v, nontrivial_of_linearEquiv_field (supportedVertexLinearEquiv k S hSv)⟩, ?_⟩
  intro W₁ W₂ _ _ hcompl
  have hother : ∀ (W : ∀ j, Submodule k ((thinRepresentation k S c).obj j)) (j : Fin n), j ≠ v →
      W j = ⊥ := by
    intro W j hj
    haveI := thinRepresentation_vertex_subsingleton_of_not_support k S c (fun h => hj ((hS j).mp h))
    exact submodule_eq_bot_of_subsingleton (W j)
  rcases eq_bot_or_eq_bot_of_isCompl_of_linearEquiv_field (supportedVertexLinearEquiv k S hSv) (hcompl v) with h | h
  · exact Or.inl fun j => by
      by_cases hj : j = v
      · exact hj ▸ h
      · exact hother W₁ j hj
  · exact Or.inr fun j => by
      by_cases hj : j = v
      · exact hj ▸ h
      · exact hother W₂ j hj

/-- If one summand of a decomposition vanishes at one supported vertex, it vanishes at every vertex. -/
private lemma thinRepresentation_pair_aux (c : ∀ a b : Fin n, (a ⟶ b) → k) {v w : Fin n}
    (hS : ∀ j, S j ↔ (j = v ∨ j = w)) (e₁ : v ⟶ w) (hc : c v w e₁ ≠ 0)
    (W₁ W₂ : ∀ j, Submodule k ((thinRepresentation k S c).obj j))
    (hW₂ : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W₂ a, (thinRepresentation k S c).map e x ∈ W₂ b)
    (hcompl : ∀ j, IsCompl (W₁ j) (W₂ j)) (hv : W₁ v = ⊥) : ∀ j, W₁ j = ⊥ := by
  have hSv : S v := (hS v).mpr (Or.inl rfl)
  have hSw : S w := (hS w).mpr (Or.inr rfl)
  have hW₂v : W₂ v = ⊤ := by
    have h := (hcompl v).sup_eq_top
    rwa [hv, bot_sup_eq] at h
  have hW₂w : W₂ w = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := thinRepresentation_arrowMap_surjective k c hSv hSw e₁ hc y
    have hxmem : x ∈ W₂ v := by rw [hW₂v]; trivial
    exact hx ▸ hW₂ e₁ x hxmem
  have hw : W₁ w = ⊥ :=
    (hcompl w).disjoint.eq_bot_of_le (by rw [hW₂w]; exact le_top)
  intro j
  by_cases hjv : j = v
  · exact hjv ▸ hv
  by_cases hjw : j = w
  · exact hjw ▸ hw
  haveI := thinRepresentation_vertex_subsingleton_of_not_support k S c (fun h => by rcases (hS j).mp h with h' | h' <;> simp_all)
  exact submodule_eq_bot_of_subsingleton (W₁ j)

/-- A thin representation supported on two specified vertices and having a nonzero distinguished arrow scalar satisfies the displayed unavailable representation property. -/
lemma auxiliaryRepresentationProperty_thinRepresentation_of_support_pair (c : ∀ a b : Fin n, (a ⟶ b) → k) {v w : Fin n}
    (hS : ∀ j, S j ↔ (j = v ∨ j = w)) (e₁ : v ⟶ w) (hc : c v w e₁ ≠ 0) :
    (thinRepresentation k S c).AuxiliaryCondition := by
  have hSv : S v := (hS v).mpr (Or.inl rfl)
  refine ⟨⟨v, nontrivial_of_linearEquiv_field (supportedVertexLinearEquiv k S hSv)⟩, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hcompl
  rcases eq_bot_or_eq_bot_of_isCompl_of_linearEquiv_field (supportedVertexLinearEquiv k S hSv) (hcompl v) with h | h
  · exact Or.inl (thinRepresentation_pair_aux k c hS e₁ hc W₁ W₂ hW₂ hcompl h)
  · exact Or.inr
      (thinRepresentation_pair_aux k c hS e₁ hc W₂ W₁ hW₁ (fun j => (hcompl j).symm) h)

variable {c c' : ∀ a b : Fin n, (a ⟶ b) → k}

/-- The field scalar induced at a supported vertex by an equivalence between two thin representations. -/
def componentScalar (φ : AuxiliaryQuiverEquivData k (Fin n) (thinRepresentation k S c) (thinRepresentation k S c'))
    {j : Fin n} (hj : S j) : k :=
  supportedVertexLinearEquiv k S hj (φ.app j ((supportedVertexLinearEquiv k S hj).symm 1))

/-- After identifying a supported vertex space with the field, the component of a representation equivalence is multiplication by its component scalar. -/
lemma componentMap_eq_componentScalar_mul (φ : AuxiliaryQuiverEquivData k (Fin n) (thinRepresentation k S c) (thinRepresentation k S c'))
    {j : Fin n} (hj : S j) (t : k) :
    supportedVertexLinearEquiv k S hj (φ.app j ((supportedVertexLinearEquiv k S hj).symm t))
      = componentScalar k φ hj * t := by
  have ht : (supportedVertexLinearEquiv k S hj).symm t = t • (supportedVertexLinearEquiv k S hj).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [ht, map_smul, map_smul, smul_eq_mul, componentScalar, mul_comm]

/-- The component scalar of an equivalence at a supported vertex is nonzero. -/
lemma componentScalar_ne_zero
    (φ : AuxiliaryQuiverEquivData k (Fin n) (thinRepresentation k S c) (thinRepresentation k S c'))
    {j : Fin n} (hj : S j) : componentScalar k φ hj ≠ 0 := by
  intro h
  rw [componentScalar] at h
  have h1 : ((supportedVertexLinearEquiv k S hj).symm 1 : Fin (if S j then 1 else 0) → k) = 0 := by
    apply (φ.app j).injective
    rw [map_zero]
    exact (supportedVertexLinearEquiv k S hj).injective (by rw [h, map_zero])
  have : (1 : k) = 0 := by
    have := congrArg (supportedVertexLinearEquiv k S hj) h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

/-- Component scalars of an equivalence intertwine the arrow scalars of the two thin representations. -/
lemma componentScalar_mul_arrowScalar
    (φ : AuxiliaryQuiverEquivData k (Fin n) (thinRepresentation k S c) (thinRepresentation k S c'))
    {a b : Fin n} (ha : S a) (hb : S b) (e : a ⟶ b) :
    componentScalar k φ hb * c a b e = c' a b e * componentScalar k φ ha := by
  have h1 : (thinRepresentation k S c).map e ((supportedVertexLinearEquiv k S ha).symm 1)
      = (supportedVertexLinearEquiv k S hb).symm (c a b e) := by
    apply (supportedVertexLinearEquiv k S hb).injective
    rw [supportedVertexLinearEquiv_arrowMap k c ha hb, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, mul_one]
  have hcomm := congrArg (supportedVertexLinearEquiv k S hb) (φ.naturality e ((supportedVertexLinearEquiv k S ha).symm 1))
  rw [h1, componentMap_eq_componentScalar_mul, supportedVertexLinearEquiv_arrowMap k c' ha hb, componentMap_eq_componentScalar_mul, mul_one] at hcomm
  exact hcomm

end ThinRepresentation

section Loop

variable (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- A field-indexed family with finite displayed vertex components, satisfying the auxiliary property and related only at equal parameters, contradicts the unavailable global quiver property. -/
lemma not_auxiliaryGlobalQuiverProperty_of_parameterizedFamily
    (R : k → FiniteQuiverRepresentation k n)
    (hfin : ∀ lam v, Module.Finite k ((R lam).obj v))
    (hindec : ∀ lam, (R lam).AuxiliaryCondition)
    (hsep : ∀ lam mu : k,
      Nonempty (AuxiliaryQuiverEquivData k (Fin n) (R lam) (R mu)) → lam = mu) :
    ¬ QuiverRepresentationFiniteness k n := by
  rintro ⟨m, reps, -, -, hcover⟩
  choose F hF using fun lam => hcover (R lam) (hfin lam) (hindec lam)
  have hinj : Function.Injective F := by
    intro lam mu hlm
    refine hsep lam mu ?_
    obtain ⟨e₁⟩ := hF lam
    obtain ⟨e₂⟩ := hF mu
    have e₂' : AuxiliaryQuiverEquivData k (Fin n) (R mu) (reps (F lam)) := by
      rw [hlm]; exact e₂
    exact ⟨e₁.trans e₂'.symm⟩
  haveI : Finite k := Finite.of_injective F hinj
  exact not_finite k

/-- The predicate selecting a single finite vertex. -/
private def auxiliaryVertexPredicate (v : Fin n) : Fin n → Prop := fun j => j = v

/-- A decision procedure for the displayed unavailable predicate associated with a finite vertex. -/
instance auxiliaryVertexPredicateDecidable (v : Fin n) : DecidablePred (auxiliaryVertexPredicate (n := n) v) :=
  fun j => inferInstanceAs (Decidable (j = v))

/-- For a quiver over an algebraically closed field, a loop contradicts the unavailable global quiver property. -/
theorem not_auxiliaryGlobalQuiverProperty_of_loop {v : Fin n} (e₀ : v ⟶ v) :
    ¬ QuiverRepresentationFiniteness k n := by
  have hS : ∀ j, auxiliaryVertexPredicate (n := n) v j ↔ j = v := fun _ => Iff.rfl
  have hSv : auxiliaryVertexPredicate (n := n) v v := rfl
  refine not_auxiliaryGlobalQuiverProperty_of_parameterizedFamily k
    (fun lam => thinRepresentation k (auxiliaryVertexPredicate v) (fun _ _ _ => lam))
    (fun lam j => thinRepresentation_vertex_moduleFinite k _ _ j)
    (fun lam => auxiliaryRepresentationProperty_thinRepresentation_of_support_singleton k _ hS) ?_
  rintro lam mu ⟨φ⟩
  have h := componentScalar_mul_arrowScalar k φ hSv hSv e₀
  have hg := componentScalar_ne_zero k φ hSv
  exact mul_left_cancel₀ hg (h.trans (mul_comm _ _))

end Loop

section TwoArrows

variable (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- The predicate selecting a pair of finite vertices. -/
private def auxiliaryVertexPairPredicate (v w : Fin n) : Fin n → Prop := fun j => j = v ∨ j = w

/-- A decision procedure for the displayed unavailable predicate associated with a pair of finite vertices. -/
instance auxiliaryVertexPairPredicateDecidable (v w : Fin n) : DecidablePred (auxiliaryVertexPairPredicate (n := n) v w) :=
  fun j => inferInstanceAs (Decidable (j = v ∨ j = w))

-- Arrow types carry no `DecidableEq`, so the arrow scalars below are defined classically.
attribute [local instance 0] Classical.propDecidable

/-- An auxiliary definition whose formal type is unavailable in this packet. -/
noncomputable def auxiliaryUnprintableDefinition (E₁ E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) (lam : k)
    (a b : Fin n) (e : a ⟶ b) : k :=
  if (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₁ then 1
  else if (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₂ then lam else 0

omit [IsAlgClosed k] in
/-- A first auxiliary property of the definition whose formal type is unavailable. -/
lemma auxiliaryUnprintableDefinition_propertyOne (E₁ E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) (lam : k)
    {a b : Fin n} (e : a ⟶ b) (h : (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₁) :
    auxiliaryUnprintableDefinition k E₁ E₂ lam a b e = 1 := by
  rw [auxiliaryUnprintableDefinition, if_pos h]

omit [IsAlgClosed k] in
/-- A second auxiliary property of the definition whose formal type is unavailable. -/
lemma auxiliaryUnprintableDefinition_propertyTwo (E₁ E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) (lam : k)
    {a b : Fin n} (e : a ⟶ b) (h : (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₂)
    (hne : E₂ ≠ E₁) : auxiliaryUnprintableDefinition k E₁ E₂ lam a b e = lam := by
  rw [auxiliaryUnprintableDefinition, if_neg (by rw [h]; exact hne), if_pos h]

/-- An auxiliary result about the displayed unavailable formal statement. -/
theorem auxiliaryUnprintableGlobalQuiverPropertyStatement {v w : Fin n} (e₁ : v ⟶ w)
    (E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b))
    (hE₂a : E₂.1 = v ∨ E₂.1 = w) (hE₂b : E₂.2.1 = v ∨ E₂.2.1 = w)
    (hne : E₂ ≠ (⟨v, w, e₁⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b))) :
    ¬ QuiverRepresentationFiniteness k n := by
  obtain ⟨a₂, b₂, e₂⟩ := E₂
  simp only at hE₂a hE₂b
  set S : Fin n → Prop := auxiliaryVertexPairPredicate v w with hSdef
  have hS : ∀ j, S j ↔ (j = v ∨ j = w) := fun _ => Iff.rfl
  have hSv : S v := Or.inl rfl
  have hSw : S w := Or.inr rfl
  have hSa : S a₂ := hE₂a
  have hSb : S b₂ := hE₂b
  set E₁ : (a : Fin n) × (b : Fin n) × (a ⟶ b) := ⟨v, w, e₁⟩ with hE₁def
  set E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b) := ⟨a₂, b₂, e₂⟩ with hE₂def
  have hone : ∀ lam : k, auxiliaryUnprintableDefinition k E₁ E₂ lam v w e₁ = 1 := fun lam =>
    auxiliaryUnprintableDefinition_propertyOne k E₁ E₂ lam e₁ rfl
  have hlam : ∀ lam : k, auxiliaryUnprintableDefinition k E₁ E₂ lam a₂ b₂ e₂ = lam := fun lam =>
    auxiliaryUnprintableDefinition_propertyTwo k E₁ E₂ lam e₂ rfl hne
  refine not_auxiliaryGlobalQuiverProperty_of_parameterizedFamily k
    (fun lam => thinRepresentation k S (auxiliaryUnprintableDefinition k E₁ E₂ lam))
    (fun lam j => thinRepresentation_vertex_moduleFinite k S _ j)
    (fun lam => auxiliaryRepresentationProperty_thinRepresentation_of_support_pair k _ hS e₁ (by rw [hone lam]; exact one_ne_zero)) ?_
  rintro lam mu ⟨φ⟩
  have hgv := componentScalar_ne_zero k φ hSv
  -- the distinguished arrow forces the two vertex scalars to agree
  have hvw : componentScalar k φ hSw = componentScalar k φ hSv := by
    have h := componentScalar_mul_arrowScalar k φ hSv hSw e₁
    rw [hone lam, hone mu, mul_one, one_mul] at h
    exact h
  -- the second arrow then identifies the parameters
  have h := componentScalar_mul_arrowScalar k φ hSa hSb e₂
  rw [hlam lam, hlam mu] at h
  have hga : componentScalar k φ hSa = componentScalar k φ hSv := by
    rcases hE₂a with h' | h'
    · subst h'; rfl
    · subst h'; exact hvw
  have hgb : componentScalar k φ hSb = componentScalar k φ hSv := by
    rcases hE₂b with h' | h'
    · subst h'; rfl
    · subst h'; exact hvw
  rw [hga, hgb] at h
  exact mul_left_cancel₀ hgv (h.trans (mul_comm _ _))

/-- For a quiver over an algebraically closed field, two distinct parallel arrows contradict the unavailable global quiver property. -/
theorem not_auxiliaryGlobalQuiverProperty_of_parallelArrows {v w : Fin n} (e₁ e₂ : v ⟶ w)
    (hne : e₁ ≠ e₂) : ¬ QuiverRepresentationFiniteness k n := by
  refine auxiliaryUnprintableGlobalQuiverPropertyStatement k e₁ ⟨v, w, e₂⟩ (Or.inl rfl)
    (Or.inr rfl) ?_
  intro h
  apply hne
  injection h with _ h₂
  injection h₂ with _ h₄
  exact h₄.symm

/-- For a quiver over an algebraically closed field, arrows in both directions between distinct vertices contradict the unavailable global quiver property. -/
theorem not_auxiliaryGlobalQuiverProperty_of_oppositeArrows {v w : Fin n} (hvw : v ≠ w) (e₁ : v ⟶ w)
    (e₂ : w ⟶ v) : ¬ QuiverRepresentationFiniteness k n := by
  refine auxiliaryUnprintableGlobalQuiverPropertyStatement k e₁ ⟨w, v, e₂⟩ (Or.inr rfl)
    (Or.inl rfl) ?_
  intro h
  exact hvw (congrArg Sigma.fst h).symm

end TwoArrows

section General

variable (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) [Quiver.{0} (Fin n)]
  [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]

/-- The displayed unavailable quiver property is equivalent to having no loops and no pair of arrows in opposite directions. -/
lemma auxiliaryQuiverProperty_iff_no_loops_no_twoCycles :
    IsMatrixOrientation ‹Quiver (Fin n)› (underlyingAdjacencyMatrix n) ↔
      ((∀ v : Fin n, IsEmpty (v ⟶ v)) ∧
        ∀ v w : Fin n, Nonempty (v ⟶ w) → Nonempty (w ⟶ v) → False) := by
  constructor
  · rintro ⟨h₁, -, h₃⟩
    refine ⟨fun v => h₁ v v ?_, h₃⟩
    rw [underlyingAdjacencyMatrix_diagonal]
    exact zero_ne_one
  · rintro ⟨hloop, hbi⟩
    refine ⟨?_, ?_, hbi⟩
    · intro i j hij
      by_cases h : i = j
      · exact h ▸ hloop i
      · rw [← not_nonempty_iff]
        intro hcon
        exact hij (by simp [underlyingAdjacencyMatrix, h, hcon])
    · intro i j hij
      by_contra hcon
      rw [not_or] at hcon
      have : underlyingAdjacencyMatrix n i j = 0 := by
        simp only [underlyingAdjacencyMatrix]
        rw [if_neg]
        rintro ⟨-, h | h⟩
        · exact hcon.1 h
        · exact hcon.2 h
      rw [this] at hij
      exact zero_ne_one hij

/-- Under the displayed natural-number hypothesis, the unavailable global quiver property is equivalent to having no loops, no arrows in both directions, subsingleton arrow types, and the displayed auxiliary graph property. -/
@[source_ref "Chapter2/Theorem2.1.2" (role := primary)]
theorem auxiliaryGlobalQuiverProperty_iff_explicitConditions (hconn : QuiverCombinatorialCondition n) :
    QuiverRepresentationFiniteness k n ↔
      ((∀ v : Fin n, IsEmpty (v ⟶ v)) ∧
        (∀ v w : Fin n, Nonempty (v ⟶ w) → Nonempty (w ⟶ v) → False) ∧
        (∀ a b : Fin n, Subsingleton (a ⟶ b)) ∧
        IsAuxiliaryMatrix n (underlyingAdjacencyMatrix n)) := by
  constructor
  · intro hfrt
    -- no loops
    have hloop : ∀ v : Fin n, IsEmpty (v ⟶ v) := by
      intro v
      rw [← not_nonempty_iff]
      intro hcon
      exact not_auxiliaryGlobalQuiverProperty_of_loop k hcon.some hfrt
    -- no edge oriented both ways
    have hbi : ∀ v w : Fin n, Nonempty (v ⟶ w) → Nonempty (w ⟶ v) → False := by
      rintro v w ⟨e₁⟩ ⟨e₂⟩
      by_cases hvw : v = w
      · subst hvw
        exact (hloop v).false e₁
      · exact not_auxiliaryGlobalQuiverProperty_of_oppositeArrows k hvw e₁ e₂ hfrt
    -- no parallel arrows
    have hsub : ∀ a b : Fin n, Subsingleton (a ⟶ b) := by
      intro a b
      refine ⟨fun e₁ e₂ => ?_⟩
      by_cases hab : a = b
      · subst hab
        exact ((hloop a).false e₁).elim
      by_contra hne
      exact not_auxiliaryGlobalQuiverProperty_of_parallelArrows k e₁ e₂ hne hfrt
    haveI := hsub
    have hOrient : IsMatrixOrientation ‹Quiver (Fin n)› (underlyingAdjacencyMatrix n) :=
      (auxiliaryQuiverProperty_iff_no_loops_no_twoCycles n).mpr ⟨hloop, hbi⟩
    exact ⟨hloop, hbi, hsub, (representationFiniteness_iff_matrixCondition k n hOrient hconn).mp hfrt⟩
  · rintro ⟨hloop, hbi, hsub, hDynkin⟩
    haveI := hsub
    have hOrient : IsMatrixOrientation ‹Quiver (Fin n)› (underlyingAdjacencyMatrix n) :=
      (auxiliaryQuiverProperty_iff_no_loops_no_twoCycles n).mpr ⟨hloop, hbi⟩
    exact (representationFiniteness_iff_matrixCondition k n hOrient hconn).mpr hDynkin

/-- Under the displayed natural-number hypothesis, the unavailable global quiver property is equivalent to the displayed orientation property, subsingleton arrow types, and the displayed graph property. -/
@[source_ref "Chapter2/Theorem2.1.2" (role := primary)]
theorem auxiliaryGlobalQuiverProperty_iff_auxiliaryConditions (hconn : QuiverCombinatorialCondition n) :
    QuiverRepresentationFiniteness k n ↔
      (IsMatrixOrientation ‹Quiver (Fin n)› (underlyingAdjacencyMatrix n) ∧
        (∀ a b : Fin n, Subsingleton (a ⟶ b)) ∧
        IsAuxiliaryMatrix n (underlyingAdjacencyMatrix n)) := by
  rw [auxiliaryGlobalQuiverProperty_iff_explicitConditions k n hconn, auxiliaryQuiverProperty_iff_no_loops_no_twoCycles n]
  tauto

end General

end RepresentationTheory.Quiver.AuxiliaryRepresentationProperties
