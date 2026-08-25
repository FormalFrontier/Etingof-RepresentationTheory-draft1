/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions
import RepresentationTheory.Alignment.Attribute

universe v u

open CategoryTheory

namespace RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions

variable (R : Type u) [Ring R]

/-- Elements satisfying the predicate are equal whenever their product is nonzero. -/
theorem eq_of_property_mul_ne_zero {f g : R}
    (hf : RepresentationTheory.RingTheory.ElementProperty.ElementProperty R f) (hg : RepresentationTheory.RingTheory.ElementProperty.ElementProperty R g)
    (hfg : f * g ≠ 0) : f = g := by
  obtain ⟨-, hfi, hfc, hfns⟩ := hf
  obtain ⟨-, hgi, hgc, hgns⟩ := hg
  have hcomm : f * g = g * f := hfc g
  have hprod_comm : ∀ y : R, f * g * y = y * (f * g) := by
    intro y
    rw [mul_assoc, hgc y, ← mul_assoc, hfc y, mul_assoc]
  have hprod_idem : IsIdempotentElem (f * g) := by
    change f * g * (f * g) = f * g
    rw [mul_assoc, ← mul_assoc g f g, ← hcomm, mul_assoc f g g, hgi.eq, ← mul_assoc, hfi.eq]
  have hffg : f * (f * g) = f * g := by rw [← mul_assoc, hfi.eq]
  have hfgf : f * g * f = f * g := by rw [mul_assoc, ← hcomm, ← mul_assoc, hfi.eq]
  have hrest_comm : ∀ y : R, (f - f * g) * y = y * (f - f * g) := by
    intro y
    rw [sub_mul, mul_sub, hfc y, hprod_comm y]
  have hrest_idem : IsIdempotentElem (f - f * g) := by
    change (f - f * g) * (f - f * g) = f - f * g
    rw [sub_mul, mul_sub, mul_sub, hfi.eq, hffg, hfgf, hprod_idem.eq]
    abel
  have hortho : (f * g) * (f - f * g) = 0 := by
    rw [mul_sub, hprod_idem.eq, hfgf, sub_self]
  have hsum : f = f * g + (f - f * g) := by abel
  have hf_eq : f = f * g := by
    by_contra hne
    exact hfns ⟨f * g, f - f * g, hfg, fun h0 => hne (by rw [← sub_eq_zero]; exact h0),
      hprod_idem, hrest_idem, hprod_comm, hrest_comm, hortho, hsum⟩
  have hgf : g * f ≠ 0 := by rw [← hcomm]; exact hfg
  have hprod_comm' : ∀ y : R, g * f * y = y * (g * f) := by
    intro y
    rw [mul_assoc, hfc y, ← mul_assoc, hgc y, mul_assoc]
  have hprod_idem' : IsIdempotentElem (g * f) := by
    change g * f * (g * f) = g * f
    rw [mul_assoc, ← mul_assoc f g f, hcomm, mul_assoc g f f, hfi.eq, ← mul_assoc, hgi.eq]
  have hggf : g * (g * f) = g * f := by rw [← mul_assoc, hgi.eq]
  have hgfg : g * f * g = g * f := by rw [mul_assoc, hcomm, ← mul_assoc, hgi.eq]
  have hrest_comm' : ∀ y : R, (g - g * f) * y = y * (g - g * f) := by
    intro y
    rw [sub_mul, mul_sub, hgc y, hprod_comm' y]
  have hrest_idem' : IsIdempotentElem (g - g * f) := by
    change (g - g * f) * (g - g * f) = g - g * f
    rw [sub_mul, mul_sub, mul_sub, hgi.eq, hggf, hgfg, hprod_idem'.eq]
    abel
  have hortho' : (g * f) * (g - g * f) = 0 := by
    rw [mul_sub, hprod_idem'.eq, hgfg, sub_self]
  have hg_eq : g = g * f := by
    by_contra hne
    exact hgns ⟨g * f, g - g * f, hgf, fun h0 => hne (by rw [← sub_eq_zero]; exact h0),
      hprod_idem', hrest_idem', hprod_comm', hrest_comm', hortho', by abel⟩
  rw [hf_eq, hcomm, ← hg_eq]

/-- Two elements satisfying the predicate coincide when both act as the identity on a simple module. -/
theorem eq_of_property_act_id_on_simple_module {f g : R}
    (hf : RepresentationTheory.RingTheory.ElementProperty.ElementProperty R f) (hg : RepresentationTheory.RingTheory.ElementProperty.ElementProperty R g)
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (hfS : ∀ m : (S : Type v), f • m = m) (hgS : ∀ m : (S : Type v), g • m = m) : f = g := by
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  obtain ⟨s, hs⟩ := exists_ne (0 : (S : Type v))
  refine eq_of_property_mul_ne_zero R hf hg (fun h0 => hs ?_)
  have h1 : (f * g) • s = s := by rw [mul_smul, hgS s, hfS s]
  rw [h0, zero_smul] at h1
  exact h1.symm

section FiniteDimensional

variable (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R]

include k

/-- The regular module has finite length under the stated finite-dimensional algebra assumptions. -/
theorem isFiniteLength_self : IsFiniteLength R R := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- A simple module determines a unique predicate-subtype element acting as the identity. -/
theorem existsUnique_property_subtype_smul_eq {S : ModuleCat.{v} R}
    (hS : IsSimpleModule R S) :
    ∃! e : {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e}, ∀ m : (S : Type v), e.1 • m = m := by
  obtain ⟨ι, hFin, e, hsum, hortho, hindec, _⟩ :=
    RepresentationTheory.RingTheory.ElementProperty.exists_orthogonalFamily_elementProperty_of_finiteDimensional (R := R) (k := k)
  letI : Fintype ι := hFin
  obtain ⟨i, hi, -⟩ := RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.existsUnique_index_actsAsIdentity R e hsum hortho
    (fun i => (hindec i).2.1) (fun i => (hindec i).2.2.1) hS
  refine ⟨⟨e i, hindec i⟩, hi, ?_⟩
  rintro ⟨f, hf⟩ hfS
  exact Subtype.ext (eq_of_property_act_id_on_simple_module R hf (hindec i) hS hfS hi)

/-- Chooses a predicate-subtype element associated with a simple module. -/
noncomputable def property_element_of_simple_module {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e} :=
  (existsUnique_property_subtype_smul_eq R k hS).choose

/-- The element associated with a simple module acts as the identity. -/
theorem property_element_of_simple_module_smul_eq {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    ∀ m : (S : Type v), (property_element_of_simple_module R k hS).1 • m = m :=
  (existsUnique_property_subtype_smul_eq R k hS).choose_spec.1

/-- An element satisfying the predicate and acting identically on a simple module is its associated element. -/
theorem eq_property_element_of_smul_eq {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) {f : R}
    (hf : RepresentationTheory.RingTheory.ElementProperty.ElementProperty R f) (hfS : ∀ m : (S : Type v), f • m = m) :
    f = (property_element_of_simple_module R k hS).1 :=
  eq_of_property_act_id_on_simple_module R hf (property_element_of_simple_module R k hS).2 hS hfS (property_element_of_simple_module_smul_eq R k hS)

/-- Related simple modules give the same associated predicate-subtype element. -/
theorem property_element_of_simple_module_eq_of_relation [Small.{v} R] {S T : ModuleCat.{v} R}
    (hS : IsSimpleModule R S) (hT : IsSimpleModule R T) (h : RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation R S T) :
    property_element_of_simple_module R k hS = property_element_of_simple_module R k hT :=
  Subtype.ext (eq_property_element_of_smul_eq R k hT (property_element_of_simple_module R k hS).2
    ((RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.auxiliaryElement_actsAsIdentity_iff_of_condition R
      ⟨(property_element_of_simple_module R k hS).1, (property_element_of_simple_module R k hS).2.2.1,
        (property_element_of_simple_module R k hS).2.2.2.1⟩ h).mp (property_element_of_simple_module_smul_eq R k hS)))

/-- Maps an element of the given class to the subtype of ring elements satisfying the predicate. -/
noncomputable def property_subtype_of_class [Small.{v} R] :
    RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryModuleType.{v} R → {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e} :=
  Quotient.lift (fun X : RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryType.{v} R => property_element_of_simple_module R k X.2)
    (fun a b hab => property_element_of_simple_module_eq_of_relation R k a.2 b.2 hab)

/-- The subtype value assigned to the quotient class of a simple module agrees with its associated element. -/
@[simp]
theorem property_subtype_of_quotient_eq [Small.{v} R] {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    property_subtype_of_class R k (Quotient.mk (RepresentationTheory.ModuleCat.Auxiliary.auxiliaryTypeSetoid R) ⟨S, hS⟩) = property_element_of_simple_module R k hS :=
  rfl

end FiniteDimensional

section Support

variable [Small.{v} R]

omit [Small.{v} R] in
/-- Shows that a ring element annihilates every vector of the target module from the supplied witness and an annihilation hypothesis. -/
theorem smul_eq_zero_of_witness {M S : ModuleCat.{v} R} {f : R}
    (hM : ∀ m : (M : Type v), f • m = 0) (h : RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelationOverRing R M S) :
    ∀ s : (S : Type v), f • s = 0 := by
  rw [RepresentationTheory.Algebra.Module.SimpleQuotient.simple_target_iff] at h
  obtain ⟨_, Q, g, hg⟩ := h
  intro s
  obtain ⟨q, rfl⟩ := hg s
  rw [← map_smul, show f • q = 0 from
    Subtype.ext (by rw [SetLike.val_smul, ZeroMemClass.coe_zero]; exact hM q.val), map_zero]

/-- Builds a module-category object from an element of the predicate subtype. -/
noncomputable def moduleCat_of_property_element (e : {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e}) :
    ModuleCat.{v} R :=
  (RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.exists_simpleModule_scalarActsAsIdentity R e.2.1 e.2.2.1 e.2.2.2.1).choose

/-- The module-category object attached to a predicate-subtype element is simple. -/
theorem isSimpleModule_moduleCat_of_property_element (e : {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e}) :
    IsSimpleModule R (moduleCat_of_property_element.{v} R e) :=
  (RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.exists_simpleModule_scalarActsAsIdentity R e.2.1 e.2.2.1 e.2.2.2.1).choose_spec.1

/-- The attached predicate-subtype element acts as the identity on its constructed module. -/
theorem property_element_smul_eq (e : {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e}) :
    ∀ m : (moduleCat_of_property_element.{v} R e : Type v), e.1 • m = m :=
  (RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.exists_simpleModule_scalarActsAsIdentity R e.2.1 e.2.2.1 e.2.2.2.1).choose_spec.2

variable (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R]

include k

/-- Relates the given binary relation on modules to identity action of the element attached to a simple module. -/
theorem relation_iff_property_element_smul_eq {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (M : ModuleCat.{v} R) :
    RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S M ↔ ∀ m : (M : Type v), (property_element_of_simple_module R k hS).1 • m = m := by
  set f : R := (property_element_of_simple_module R k hS).1 with hf
  have hfidem : IsIdempotentElem f := (property_element_of_simple_module R k hS).2.2.1
  have hfcentral : ∀ y : R, f * y = y * f := (property_element_of_simple_module R k hS).2.2.2.1
  constructor
  · intro hM
    let φ : (M : Type v) →ₗ[R] (M : Type v) :=
      { toFun := fun m => f • m
        map_add' := fun m₁ m₂ => smul_add f m₁ m₂
        map_smul' := fun r m => by simp only [RingHom.id_apply, smul_smul, hfcentral r] }
    let ψ : (M : Type v) →ₗ[R] (M : Type v) := LinearMap.id - φ
    have hψ_apply : ∀ m : (M : Type v), ψ m = m - f • m := fun m => rfl
    have hzero : ∀ q : (LinearMap.range ψ : Type v), f • q = 0 := by
      intro q
      obtain ⟨m, hm⟩ := q.2
      refine Subtype.ext ?_
      rw [SetLike.val_smul, ZeroMemClass.coe_zero, ← hm, hψ_apply, smul_sub, smul_smul,
        hfidem.eq, sub_self]
    have hbot : LinearMap.range ψ = ⊥ := by
      by_contra hne
      haveI : Nontrivial (LinearMap.range ψ : Type v) := Submodule.nontrivial_iff_ne_bot.mpr hne
      obtain ⟨U, hU⟩ :=
        RepresentationTheory.Algebra.Module.SimpleQuotient.exists_target (M := ModuleCat.of R (LinearMap.range ψ : Type v))
      have hUM : RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelationOverRing R M U :=
        RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelationOverRing.of_submodule (LinearMap.range ψ) hU
      have hU0 : ∀ u : (U : Type v), f • u = 0 :=
        smul_eq_zero_of_witness R
          (M := ModuleCat.of R (LinearMap.range ψ : Type v))
          hzero hU
      have hU1 : ∀ u : (U : Type v), f • u = u :=
        (RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.auxiliaryElement_actsAsIdentity_iff_of_condition R ⟨f, hfidem, hfcentral⟩
          ((RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation_equivalence R).symm (hM U hUM))).mp (property_element_of_simple_module_smul_eq R k hS)
      haveI := hU.1
      haveI : Nontrivial (U : Type v) := IsSimpleModule.nontrivial R (U : Type v)
      obtain ⟨u, hu⟩ := exists_ne (0 : (U : Type v))
      exact hu ((hU1 u).symm.trans (hU0 u))
    intro m
    have hm : ψ m = 0 := by
      have hmem : ψ m ∈ LinearMap.range ψ := ⟨m, rfl⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot R).mp hmem
    rw [hψ_apply] at hm
    exact (sub_eq_zero.mp hm).symm
  · intro hM T hT
    have hTf : ∀ t : (T : Type v), f • t = t :=
      RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.scalar_actsAsIdentity_of_condition R hM hT
    exact RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.simpleModules_satisfyCondition_of_scalarActsAsIdentity R (isFiniteLength_self R k) (property_element_of_simple_module R k hS).2
      hT.1 hS hTf (property_element_of_simple_module_smul_eq R k hS)

/-- For a module related to the simple module, a distinct predicate element annihilates every vector. -/
theorem smul_eq_zero_of_relation_ne_property_element {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    {M : ModuleCat.{v} R} (hM : RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation'''' R S M) {e : R}
    (he : RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e) (hne : e ≠ (property_element_of_simple_module R k hS).1) :
    ∀ m : (M : Type v), e • m = 0 := by
  intro m
  have hmul : e * (property_element_of_simple_module R k hS).1 = 0 := by
    by_contra h0
    exact hne (eq_of_property_mul_ne_zero R he (property_element_of_simple_module R k hS).2 h0)
  have h1 : (property_element_of_simple_module R k hS).1 • m = m :=
    (relation_iff_property_element_smul_eq R k hS M).mp hM m
  calc e • m = e • ((property_element_of_simple_module R k hS).1 • m) := by rw [h1]
    _ = (e * (property_element_of_simple_module R k hS).1) • m := (mul_smul _ _ m).symm
    _ = 0 := by rw [hmul, zero_smul]

/-- An equivalence from the given class to the subtype of ring elements satisfying the displayed predicate. -/
noncomputable def equiv_property_subtype :
    RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryModuleType.{v} R ≃ {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e} where
  toFun := property_subtype_of_class R k
  invFun e :=
    Quotient.mk (RepresentationTheory.ModuleCat.Auxiliary.auxiliaryTypeSetoid R)
      ⟨moduleCat_of_property_element R e, isSimpleModule_moduleCat_of_property_element R e⟩
  left_inv := by
    refine Quotient.ind (fun X => ?_)
    refine Quotient.sound ?_
    change RepresentationTheory.ModuleCat.Auxiliary.auxiliaryModuleRelation R (moduleCat_of_property_element R (property_element_of_simple_module R k X.2)) X.1
    exact RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.simpleModules_satisfyCondition_of_scalarActsAsIdentity R (isFiniteLength_self R k)
      (property_element_of_simple_module R k X.2).2
      (isSimpleModule_moduleCat_of_property_element R (property_element_of_simple_module R k X.2)) X.2
      (property_element_smul_eq R (property_element_of_simple_module R k X.2)) (property_element_of_simple_module_smul_eq R k X.2)
  right_inv e :=
    Subtype.ext
      (eq_property_element_of_smul_eq R k (isSimpleModule_moduleCat_of_property_element R e) e.2
        (property_element_smul_eq R e)).symm

/-- Evaluating the equivalence agrees with the associated map into the predicate subtype. -/
@[simp]
theorem equiv_property_subtype_apply (b : RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryModuleType.{v} R) :
    equiv_property_subtype R k b = property_subtype_of_class R k b :=
  rfl

/-- There exists an equivalence between the given class and the predicate subtype. -/
@[source_ref "Chapter9/Problem9.5.3" (role := primary)]
theorem nonempty_equiv_property_subtype :
    Nonempty (RepresentationTheory.ModuleCat.Auxiliary.AuxiliaryModuleType.{v} R ≃ {e : R // RepresentationTheory.RingTheory.ElementProperty.ElementProperty R e}) :=
  ⟨equiv_property_subtype R k⟩

end Support

end RepresentationTheory.ModuleTheory.SimpleModule.PropertyElementActions
