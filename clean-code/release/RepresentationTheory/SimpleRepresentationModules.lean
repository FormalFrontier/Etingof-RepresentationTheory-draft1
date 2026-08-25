/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.CategoryTheory.IsomorphismClasses
import RepresentationTheory.FDRep.SimpleCharacters

/-!
# Simple representations and modules over group algebras

This module relates simple finite-dimensional group representations to simple modules over the
corresponding group algebra. It also studies the sum of all group elements, detects failure of
semisimplicity in modular characteristic, and compares simple-module isomorphism classes before
and after quotienting by the Jacobson radical.
-/

open CategoryTheory

namespace RepresentationTheory.SimpleRepresentationModules

section GroupSum

variable (k G : Type*) [Field k] [Group G] [Fintype G]

/-- The group-algebra element whose coefficient at every group element is one. -/
noncomputable def groupElementSum : MonoidAlgebra k G := ∑ g : G, MonoidAlgebra.single g (1 : k)

variable {k G}

omit [Group G] in

/-- Every coefficient of the group-element sum is one. -/
@[simp] lemma groupElementSum_coeff (x : G) : (groupElementSum k G).coeff x = 1 := by
  classical
  rw [groupElementSum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Finset.sum_eq_single x
    (fun b _ hb => by simp [hb])
    (fun hx => absurd (Finset.mem_univ x) hx)]
  simp

/-- Left multiplication by a basis group element fixes the sum of all group elements. -/
lemma single_mul_groupElementSum (g : G) :
    MonoidAlgebra.single g (1 : k) * groupElementSum k G = groupElementSum k G := by
  simp only [groupElementSum, Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

/-- Right multiplication by a basis group element fixes the group-element sum. -/
lemma groupElementSum_mul_single (g : G) :
    groupElementSum k G * MonoidAlgebra.single g (1 : k) = groupElementSum k G := by
  simp only [groupElementSum, Finset.sum_mul, MonoidAlgebra.single_mul_single, mul_one]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

/-- The sum of all group elements belongs to the center of the group algebra. -/
lemma groupElementSum_mem_center :
    groupElementSum k G ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | hM g =>
    rw [show (MonoidAlgebra.of k G g : MonoidAlgebra k G) = MonoidAlgebra.single g 1 from rfl,
      single_mul_groupElementSum, groupElementSum_mul_single]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]
  | hsmul r x hx => rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, hx]

/-- The square of the group-element sum is zero when the group cardinality vanishes in the field. -/
lemma groupElementSum_sq (hcard : (Fintype.card G : k) = 0) :
    groupElementSum k G * groupElementSum k G = 0 := by
  have hdef : groupElementSum k G = ∑ g : G, MonoidAlgebra.single g (1 : k) := rfl
  calc groupElementSum k G * groupElementSum k G
      = ∑ g : G, MonoidAlgebra.single g (1 : k) * groupElementSum k G := by rw [← Finset.sum_mul, ← hdef]
    _ = ∑ _g : G, groupElementSum k G := by simp only [single_mul_groupElementSum]
    _ = 0 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, hcard, zero_smul]

/-- The group-element sum is nilpotent when the group cardinality vanishes in the field. -/
lemma groupElementSum_isNilpotent (hcard : (Fintype.card G : k) = 0) :
    IsNilpotent (groupElementSum k G) :=
  ⟨2, by rw [pow_two]; exact groupElementSum_sq hcard⟩

/-- The group-element sum is nonzero. -/
lemma groupElementSum_ne_zero : groupElementSum k G ≠ 0 := by
  intro h
  have h1 := groupElementSum_coeff (k := k) (G := G) (1 : G)
  rw [h, show (0 : MonoidAlgebra k G).coeff (1 : G) = 0 from rfl] at h1
  exact zero_ne_one h1

/-- A finite-group algebra is not semisimple when the group cardinality is zero in the field. -/
theorem not_isSemisimpleRing_monoidAlgebra_of_card_eq_zero (hcard : (Fintype.card G : k) = 0) :
    ¬ IsSemisimpleRing (MonoidAlgebra k G) := by
  intro hss
  haveI := hss
  refine groupElementSum_ne_zero (k := k) (G := G) ?_
  have hmem : groupElementSum k G ∈ Ideal.jacobson (⊥ : Ideal (MonoidAlgebra k G)) := by
    rw [Ideal.mem_jacobson_iff]
    intro y

    have hcomm : Commute y (groupElementSum k G) := Subalgebra.mem_center_iff.mp groupElementSum_mem_center y
    have hnil : IsNilpotent (y * groupElementSum k G) :=
      hcomm.isNilpotent_mul_left (groupElementSum_isNilpotent hcard)
    obtain ⟨u, hu⟩ := hnil.isUnit_one_add
    refine ⟨↑u⁻¹, ?_⟩
    have key : (↑u⁻¹ : MonoidAlgebra k G) * (y * groupElementSum k G) + ↑u⁻¹ = 1 := by
      have h := u.inv_mul
      rw [hu, mul_add, mul_one, add_comm] at h
      exact h
    rw [Ideal.mem_bot, mul_assoc, key, sub_self]
  have hjb : Ideal.jacobson (⊥ : Ideal (MonoidAlgebra k G))
      = Ring.jacobson (MonoidAlgebra k G) := Ideal.jacobson_bot
  have hmem' : groupElementSum k G ∈ Ring.jacobson (MonoidAlgebra k G) := hjb ▸ hmem
  rw [IsSemisimpleRing.jacobson_eq_bot, Ideal.mem_bot] at hmem'
  exact hmem'

end GroupSum

section Bridge

open CategoryTheory ObjectProperty

universe u v

private lemma simple_of_fullyFaithful_preservesMono {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro _
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- A finite-dimensional representation is simple when its associated group-algebra module is simple. -/
theorem simple_fdRep_of_isSimpleModule
    {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V)
    [hρ : @IsSimpleModule (MonoidAlgebra k G) _ ρ.asModule _
      (Representation.instModuleMonoidAlgebraAsModule ρ)] :
    Simple (FDRep.of ρ) := by
  letI : Module (MonoidAlgebra k G) ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule ρ
  haveI := hρ
  let E := Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ))) :=
    @simple_of_isSimpleModule (MonoidAlgebra k G) ρ.asModule _ _
      (Representation.instModuleMonoidAlgebraAsModule ρ) hρ
  haveI : Simple ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ)) :=
    simple_of_fullyFaithful_preservesMono E.functor _
  exact simple_of_fullyFaithful_preservesMono (forget₂ (FDRep k G) (Rep k G)) _

/-- A simple module over a finite-group algebra is finite-dimensional over the coefficient field. -/
theorem finite_of_simple_monoidAlgebra_module [Finite G] {M : Type u} [AddCommGroup M]
    [Module k M] [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]
    [IsSimpleModule (MonoidAlgebra k G) M] : Module.Finite k M := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (MonoidAlgebra k G) M
  obtain ⟨m, hm0⟩ := exists_ne (0 : M)
  have htop : Submodule.span (MonoidAlgebra k G) {m} = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left (by
      rw [Submodule.span_singleton_eq_bot]; exact hm0)
  haveI : Module.Finite (MonoidAlgebra k G) M := ⟨⟨{m}, by simpa using htop⟩⟩
  haveI : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G k)
  exact Module.Finite.trans (MonoidAlgebra k G) M

/-- An auxiliary object property on a category with zero morphisms. -/
def AuxiliaryObjectProperty (C : Type*) [Category C] [Limits.HasZeroMorphisms C] : ObjectProperty C :=
  fun X => Simple X

/-- The auxiliary categorical object property is invariant under isomorphism. -/
instance auxiliaryObjectProperty_isClosedUnderIsomorphisms (C : Type*) [Category C] [Limits.HasZeroMorphisms C] :
    (AuxiliaryObjectProperty C).IsClosedUnderIsomorphisms where
  of_iso e hX := (Simple.iff_of_iso e).mp hX

/-- An equivalence preserving monomorphisms in both directions preserves and reflects simple objects. -/
lemma simple_map_iff_of_equivalence {A B : Type*} [Category A] [Category B]
    [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B]
    (E : A ≌ B) [E.functor.PreservesMonomorphisms] [E.inverse.PreservesMonomorphisms]
    (X : A) : Simple (E.functor.obj X) ↔ Simple X := by
  constructor
  · intro _
    exact simple_of_fullyFaithful_preservesMono E.functor X
  · intro hX
    haveI := hX
    haveI : Simple (E.inverse.obj (E.functor.obj X)) :=
      Simple.of_iso (Y := X) (E.unitIso.symm.app X)
    exact simple_of_fullyFaithful_preservesMono E.inverse (E.functor.obj X)

variable (k G) in

/-- Representation isomorphism classes correspond to module isomorphism classes over the group algebra within the selected full subcategories. -/
noncomputable def repIsoClassesEquivModuleIsoClasses :
    Quotient (isIsomorphicSetoid (AuxiliaryObjectProperty (Rep k G)).FullSubcategory) ≃
      Quotient (isIsomorphicSetoid
        (AuxiliaryObjectProperty (ModuleCat (MonoidAlgebra k G))).FullSubcategory) := by
  refine _root_.RepresentationTheory.CategoryTheory.IsomorphismClasses.Equivalence.isomorphismClassesEquiv
    (Equivalence.congrFullSubcategory (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G))
      (P := AuxiliaryObjectProperty (Rep k G)) (Q := AuxiliaryObjectProperty (ModuleCat (MonoidAlgebra k G))) ?_)
  exact funext fun X => propext
    (simple_map_iff_of_equivalence (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)) X)

/-- The canonical intertwining map from a subrepresentation to its ambient finite-dimensional representation. -/
noncomputable def subrepresentationInclusion (V : FDRep k G) (S : Subrepresentation V.ρ) :
    S.toRepresentation.IntertwiningMap V.ρ :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _ S.toSubmodule.subtype (fun _ _ => rfl)

private lemma nontrivial_carrier_of_simple (V : FDRep k G) [Simple V] : Nontrivial V.V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply id_nonzero V
  apply (forget₂ (FDRep k G) (FGModuleCat k)).map_injective
  apply (forget₂ (FGModuleCat k) (ModuleCat k)).map_injective
  ext x
  exact @Subsingleton.elim V.V h _ _

/-- A simple finite-dimensional representation yields a simple module over the group algebra. -/
theorem isSimpleModule_of_simple_fdRep (V : FDRep k G) [Simple V] :
    IsSimpleModule (MonoidAlgebra k G) (Representation.asModule V.ρ) := by
  haveI : Nontrivial V.V := nontrivial_carrier_of_simple V
  haveI : Nontrivial (Representation.asModule V.ρ) :=
    (Representation.asModuleEquiv V.ρ).toEquiv.nontrivial
  refine { eq_bot_or_eq_top := fun N => ?_ }
  set S : Subrepresentation V.ρ := Subrepresentation.ofSubmodule' N with hS
  haveI : Module.Finite k S.toSubmodule := inferInstance
  let ι : S.toRepresentation.IntertwiningMap V.ρ := subrepresentationInclusion V S
  let j : (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of S.toRepresentation) ⟶
      (forget₂ (FDRep k G) (Rep k G)).obj V := Rep.ofHom ι
  have hjhom : ⇑j.hom = (Subtype.val : S.toSubmodule → V.V) := rfl
  have hjinj : Function.Injective ⇑j.hom := by rw [hjhom]; exact Subtype.coe_injective
  haveI hmonoj : Mono j := (Rep.mono_iff_injective j).mpr hjinj
  let j' : FDRep.of S.toRepresentation ⟶ V :=
    (forget₂ (FDRep k G) (Rep k G)).preimage j
  have hmap : (forget₂ (FDRep k G) (Rep k G)).map j' = j :=
    (forget₂ (FDRep k G) (Rep k G)).map_preimage j
  haveI hmonoj' : Mono j' :=
    (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map (by rw [hmap]; exact hmonoj)
  by_cases hz : j' = 0
  · left
    have hj0 : j = 0 := by rw [← hmap, hz]; exact Functor.map_zero _ _ _
    have hzero : ⇑j.hom = 0 := by rw [hj0]; rfl
    rw [eq_bot_iff]
    intro x hx
    have hxS : x ∈ S := (Subrepresentation.mem_ofSubmodule'_iff (ρ := V.ρ)).mpr hx
    have hval : (Subtype.val : S.toSubmodule → V.V) ⟨x, hxS⟩ = 0 := by
      rw [← hjhom]; exact congrFun hzero ⟨x, hxS⟩
    rw [Submodule.mem_bot]
    exact hval
  · right
    haveI : IsIso j' := (Simple.mono_isIso_iff_nonzero j').mpr hz
    haveI hisoj : IsIso ((forget₂ (FDRep k G) (Rep k G)).map j') := inferInstance
    rw [hmap] at hisoj
    have hsurj : Function.Surjective ⇑j.hom := (Rep.epi_iff_surjective j).mp inferInstance
    rw [hjhom] at hsurj
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy⟩ := hsurj x
    have hxS : x ∈ S := hy ▸ y.2
    exact (Subrepresentation.mem_ofSubmodule'_iff (ρ := V.ρ)).mp hxS

/-- A representation is simple exactly when its associated group-algebra module is simple. -/
theorem simple_rep_iff_isSimpleModule (W : Rep k G) :
    Simple W ↔ IsSimpleModule (MonoidAlgebra k G) (Representation.asModule W.ρ) := by
  rw [← simple_map_iff_of_equivalence (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)) W]
  exact simple_iff_isSimpleModule

/-- Forgetting finite-dimensional structure preserves simplicity of a representation. -/
theorem simple_forget_fdRep (V : FDRep k G) [Simple V] :
    Simple ((forget₂ (FDRep k G) (Rep k G)).obj V) := by
  rw [simple_rep_iff_isSimpleModule]
  exact isSimpleModule_of_simple_fdRep V

/-- A functor between the selected full subcategories of finite-dimensional and unrestricted representations. -/
noncomputable abbrev auxiliaryFullSubcategoryFunctor :
    (AuxiliaryObjectProperty (FDRep k G)).FullSubcategory ⥤ (AuxiliaryObjectProperty (Rep k G)).FullSubcategory :=
  (AuxiliaryObjectProperty (Rep k G)).lift
    ((AuxiliaryObjectProperty (FDRep k G)).ι ⋙ forget₂ (FDRep k G) (Rep k G))
    (fun X => by haveI : Simple X.obj := X.property; exact simple_forget_fdRep X.obj)

/-- The selected functor between full representation subcategories is essentially surjective for a finite group. -/
instance auxiliaryFullSubcategoryFunctor_essSurj [Finite G] : (auxiliaryFullSubcategoryFunctor (k := k) (G := G)).EssSurj where
  mem_essImage W := by
    haveI : Simple W.obj := W.property
    haveI hsm : IsSimpleModule (MonoidAlgebra k G) (Representation.asModule W.obj.ρ) :=
      (simple_rep_iff_isSimpleModule W.obj).mp W.property
    haveI : Module.Finite k (Representation.asModule W.obj.ρ) :=
      finite_of_simple_monoidAlgebra_module (k := k) (G := G) (M := Representation.asModule W.obj.ρ)
    haveI : Module.Finite k W.obj.V :=
      Module.Finite.equiv (Representation.asModuleEquiv W.obj.ρ)
    haveI : Simple (FDRep.of W.obj.ρ) :=
      simple_fdRep_of_isSimpleModule (hρ := hsm) W.obj.ρ
    exact ⟨⟨FDRep.of W.obj.ρ, ‹Simple (FDRep.of W.obj.ρ)›⟩, ⟨Iso.refl _⟩⟩

/-- The selected functor between full representation subcategories is an equivalence for a finite group. -/
noncomputable instance auxiliaryFullSubcategoryFunctor_isEquivalence [Finite G] :
    (auxiliaryFullSubcategoryFunctor (k := k) (G := G)).IsEquivalence where

variable (k G) in

/-- Equates the finite-group auxiliary type with isomorphism classes in the selected full representation subcategory. -/
noncomputable def auxiliaryTypeEquivRepIsoClasses [Finite G] :
    _root_.RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G ≃
      Quotient (isIsomorphicSetoid (AuxiliaryObjectProperty (Rep k G)).FullSubcategory) :=
  _root_.RepresentationTheory.CategoryTheory.IsomorphismClasses.Equivalence.isomorphismClassesEquiv (auxiliaryFullSubcategoryFunctor (k := k) (G := G)).asEquivalence

/-- An auxiliary type associated with a ring. -/
abbrev AuxiliaryRingType.{w, r} (R : Type r) [Ring R] :=
  Quotient (isIsomorphicSetoid (AuxiliaryObjectProperty (ModuleCat.{w} R)).FullSubcategory)

variable (k G) in

/-- Equates the finite-group auxiliary type with the auxiliary type of its group algebra. -/
noncomputable def auxiliaryTypeEquivGroupAlgebraAuxiliaryType [Finite G] :
    _root_.RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G ≃ AuxiliaryRingType.{u} (MonoidAlgebra k G) :=
  (auxiliaryTypeEquivRepIsoClasses k G).trans
    (_root_.RepresentationTheory.CategoryTheory.IsomorphismClasses.Equivalence.isomorphismClassesEquiv
      (Equivalence.congrFullSubcategory (Rep.equivalenceModuleMonoidAlgebra.{u} (k := k) (G := G))
        (P := AuxiliaryObjectProperty (Rep.{u} k G)) (Q := AuxiliaryObjectProperty (ModuleCat.{u} (MonoidAlgebra k G)))
        (funext fun X => propext (simple_map_iff_of_equivalence
          (Rep.equivalenceModuleMonoidAlgebra.{u} (k := k) (G := G)) X))))

variable (k G) in

/-- The two auxiliary types associated with a finite-group algebra have equal cardinalities. -/
theorem natCard_auxiliaryTypes_eq [Finite G] :
    Nat.card (_root_.RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G) = Nat.card (AuxiliaryRingType.{u} (MonoidAlgebra k G)) :=
  Nat.card_congr (auxiliaryTypeEquivGroupAlgebraAuxiliaryType k G)

end Bridge

section Finiteness

attribute [local instance] CategoryTheory.isIsomorphicSetoid

variable {R : Type*} [Ring R]

private theorem isTorsionBySet_jacobson {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module.IsTorsionBySet R M (Ring.jacobson R) := fun x a =>
  Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator R M a.2) x

@[implicit_reducible]
private noncomputable def jacobsonModule {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] : Module (R ⧸ Ring.jacobson R) M :=
  (isTorsionBySet_jacobson (R := R) (M := M)).module

private theorem isSimpleModule_jacobsonModule {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] :
    letI := jacobsonModule (R := R) (M := M); IsSimpleModule (R ⧸ Ring.jacobson R) M :=
  letI := jacobsonModule (R := R) (M := M)
  ((isTorsionBySet_jacobson (R := R) (M := M)).semilinearMap.isSimpleModule_iff_of_bijective
    Function.bijective_id).mp inferInstance

private noncomputable def demoteEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N]
    (e : letI := jacobsonModule (R := R) (M := M); letI := jacobsonModule (R := R) (M := N);
      M ≃ₗ[R ⧸ Ring.jacobson R] N) : M ≃ₗ[R] N :=
  letI := jacobsonModule (R := R) (M := M)
  letI := jacobsonModule (R := R) (M := N)
  { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
    map_add' := e.map_add
    map_smul' := fun r x => e.map_smul (Ideal.Quotient.mk _ r) x }

private noncomputable def promoteEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N] (e : M ≃ₗ[R] N) :
    letI := jacobsonModule (R := R) (M := M); letI := jacobsonModule (R := R) (M := N);
      M ≃ₗ[R ⧸ Ring.jacobson R] N :=
  letI := jacobsonModule (R := R) (M := M)
  letI := jacobsonModule (R := R) (M := N)
  { toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
    map_add' := e.map_add
    map_smul' := fun a x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact e.map_smul r x }

open scoped Classical in

/-- The auxiliary type of a ring finite over a field is finite. -/
theorem finite_auxiliaryRingType_of_module_finite (k : Type u) {R : Type*} [Field k] [Ring R] [Algebra k R]
    [Module.Finite k R] : Finite (AuxiliaryRingType.{u} R) := by
  classical
  haveI : IsArtinianRing R := isArtinian_of_tower k inferInstance
  haveI : IsSemiprimaryRing R := inferInstance
  set A := R ⧸ Ring.jacobson R with hA
  haveI : IsSemisimpleRing A := inferInstance
  haveI : Finite (isotypicComponents A A) := inferInstance

  have hsimp : ∀ P : (AuxiliaryObjectProperty (ModuleCat.{u} R)).FullSubcategory,
      IsSimpleModule R (P.obj : ModuleCat.{u} R) := fun P => by
    haveI : Simple P.obj := P.property
    exact isSimpleModule_of_simple _
  let f : (AuxiliaryObjectProperty (ModuleCat.{u} R)).FullSubcategory → isotypicComponents A A := fun P => by
    haveI := hsimp P
    letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
    haveI := isSimpleModule_jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
    refine ⟨isotypicComponent A A (P.obj : ModuleCat.{u} R), ?_⟩
    obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      A (P.obj : ModuleCat.{u} R)
    exact ⟨I, IsSimpleModule.congr e.symm, e.isotypicComponent_eq⟩

  have hresp : ∀ P Q : (AuxiliaryObjectProperty (ModuleCat.{u} R)).FullSubcategory, P ≈ Q → f P = f Q := by
    rintro P Q ⟨iso⟩
    haveI := hsimp P; haveI := hsimp Q
    letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
    letI := jacobsonModule (R := R) (M := (Q.obj : ModuleCat.{u} R))
    apply Subtype.ext
    have eR : (P.obj : ModuleCat.{u} R) ≃ₗ[R] (Q.obj : ModuleCat.{u} R) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    exact (promoteEquiv (R := R) (M := (P.obj : ModuleCat.{u} R))
      (N := (Q.obj : ModuleCat.{u} R)) eR).isotypicComponent_eq

  refine Finite.of_injective (Quotient.lift f hresp) ?_
  intro a b
  refine Quotient.inductionOn₂ a b (fun P Q hab => ?_)
  simp only [Quotient.lift_mk] at hab
  haveI := hsimp P; haveI := hsimp Q
  letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  letI := jacobsonModule (R := R) (M := (Q.obj : ModuleCat.{u} R))
  haveI := isSimpleModule_jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  haveI := isSimpleModule_jacobsonModule (R := R) (M := (Q.obj : ModuleCat.{u} R))
  have hcomp : isotypicComponent A A (P.obj : ModuleCat.{u} R)
      = isotypicComponent A A (Q.obj : ModuleCat.{u} R) := congrArg Subtype.val hab
  obtain ⟨I, ⟨eP⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    A (P.obj : ModuleCat.{u} R)
  haveI : IsSimpleModule A (I : Submodule A A) := IsSimpleModule.congr eP.symm
  have key : isotypicComponent A A (I : Submodule A A)
      = isotypicComponent A A (Q.obj : ModuleCat.{u} R) :=
    eP.isotypicComponent_eq.symm.trans hcomp
  have hIle : (I : Submodule A A) ≤ isotypicComponent A A (Q.obj : ModuleCat.{u} R) :=
    (Submodule.le_isotypicComponent I).trans key.le
  obtain ⟨eQ⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent A A (Q.obj : ModuleCat.{u} R)) I hIle
  have eR : (P.obj : ModuleCat.{u} R) ≃ₗ[R] (Q.obj : ModuleCat.{u} R) :=
    demoteEquiv (R := R) (M := (P.obj : ModuleCat.{u} R))
      (N := (Q.obj : ModuleCat.{u} R)) (eP.trans eQ)
  exact Quotient.sound
    ⟨(AuxiliaryObjectProperty (ModuleCat.{u} R)).fullyFaithfulι.preimageIso eR.toModuleIso⟩

private def idModuleIso {S : Type*} [Ring S] {M : Type u} [AddCommGroup M]
    (i₁ i₂ : Module S M) (h : ∀ (s : S) (x : M), (letI := i₁; s • x) = (letI := i₂; s • x)) :
    (letI := i₁; ModuleCat.of S M) ≅ (letI := i₂; ModuleCat.of S M) :=
  @LinearEquiv.toModuleIso S _ M M _ _ i₁ i₂
    (@AddEquiv.toLinearEquiv S M M _ _ _ i₁ i₂ (AddEquiv.refl M) h)

@[implicit_reducible]
private noncomputable def restrictedModule {M : Type*} [AddCommGroup M]
    [Module (R ⧸ Ring.jacobson R) M] : Module R M :=
  Module.compHom M (Ideal.Quotient.mk (Ring.jacobson R))

private theorem isSimpleModule_restrictedModule {M : Type*} [AddCommGroup M]
    [Module (R ⧸ Ring.jacobson R) M] [IsSimpleModule (R ⧸ Ring.jacobson R) M] :
    letI := restrictedModule (R := R) (M := M); IsSimpleModule R M :=
  letI := restrictedModule (R := R) (M := M)
  ((({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      M →ₛₗ[Ideal.Quotient.mk (Ring.jacobson R)] M)).isSimpleModule_iff_of_bijective
    Function.bijective_id).mpr inferInstance

@[reducible]
private noncomputable def demoteSimpleObj
    (P : (AuxiliaryObjectProperty (ModuleCat.{u} R)).FullSubcategory) :
    (AuxiliaryObjectProperty (ModuleCat.{u} (R ⧸ Ring.jacobson R))).FullSubcategory := by
  haveI : Simple P.obj := P.property
  haveI : IsSimpleModule R (P.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
  letI := jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  haveI := isSimpleModule_jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
  exact ⟨ModuleCat.of (R ⧸ Ring.jacobson R) (P.obj : ModuleCat.{u} R), simple_of_isSimpleModule⟩

@[reducible]
private noncomputable def inflateSimpleObj
    (Q : (AuxiliaryObjectProperty (ModuleCat.{u} (R ⧸ Ring.jacobson R))).FullSubcategory) :
    (AuxiliaryObjectProperty (ModuleCat.{u} R)).FullSubcategory := by
  haveI : Simple Q.obj := Q.property
  haveI : IsSimpleModule (R ⧸ Ring.jacobson R)
      (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) := isSimpleModule_of_simple _
  letI := restrictedModule (R := R) (M := (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
  haveI := isSimpleModule_restrictedModule (R := R)
    (M := (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
  exact ⟨ModuleCat.of R (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)), simple_of_isSimpleModule⟩

variable (R) in

/-- The auxiliary type of the Jacobson quotient is equivalent to the auxiliary type of the original ring. -/
noncomputable def auxiliaryRingTypeJacobsonQuotientEquiv :
    AuxiliaryRingType.{u} (R ⧸ Ring.jacobson R) ≃ AuxiliaryRingType.{u} R where
  toFun := Quotient.map inflateSimpleObj (by
    rintro Q Q' ⟨iso⟩
    haveI : Simple Q.obj := Q.property
    haveI : Simple Q'.obj := Q'.property
    haveI : IsSimpleModule (R ⧸ Ring.jacobson R)
        (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) := isSimpleModule_of_simple _
    haveI : IsSimpleModule (R ⧸ Ring.jacobson R)
        (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) := isSimpleModule_of_simple _
    letI := restrictedModule (R := R) (M := (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
    letI := restrictedModule (R := R) (M := (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)))
    have eA : (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) ≃ₗ[R ⧸ Ring.jacobson R]
        (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    let eR : (Q.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) ≃ₗ[R]
        (Q'.obj : ModuleCat.{u} (R ⧸ Ring.jacobson R)) :=
      { toFun := eA, invFun := eA.symm, left_inv := eA.left_inv, right_inv := eA.right_inv,
        map_add' := eA.map_add,
        map_smul' := fun r x => eA.map_smul (Ideal.Quotient.mk (Ring.jacobson R) r) x }
    exact ⟨(AuxiliaryObjectProperty (ModuleCat.{u} R)).fullyFaithfulι.preimageIso eR.toModuleIso⟩)
  invFun := Quotient.map demoteSimpleObj (by
    rintro P P' ⟨iso⟩
    haveI : Simple P.obj := P.property
    haveI : Simple P'.obj := P'.property
    haveI : IsSimpleModule R (P.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
    haveI : IsSimpleModule R (P'.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
    have eR : (P.obj : ModuleCat.{u} R) ≃ₗ[R] (P'.obj : ModuleCat.{u} R) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    exact ⟨(AuxiliaryObjectProperty (ModuleCat.{u} (R ⧸ Ring.jacobson R))).fullyFaithfulι.preimageIso
      (promoteEquiv (R := R) (M := (P.obj : ModuleCat.{u} R))
        (N := (P'.obj : ModuleCat.{u} R)) eR).toModuleIso⟩)
  left_inv := by
    rintro y
    induction y using Quotient.inductionOn with
    | _ Q =>
      haveI : Simple Q.obj := Q.property
      exact Quotient.sound
        ⟨(AuxiliaryObjectProperty (ModuleCat.{u} (R ⧸ Ring.jacobson R))).fullyFaithfulι.preimageIso
          (idModuleIso _ inferInstance (fun a x => by
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a; rfl))⟩
  right_inv := by
    rintro y
    induction y using Quotient.inductionOn with
    | _ P =>
      haveI : Simple P.obj := P.property
      haveI hsP : IsSimpleModule R (P.obj : ModuleCat.{u} R) := isSimpleModule_of_simple _
      let iAj : Module (R ⧸ Ring.jacobson R) (P.obj : ModuleCat.{u} R) :=
        jacobsonModule (R := R) (M := (P.obj : ModuleCat.{u} R))
      let iRc : Module R (P.obj : ModuleCat.{u} R) :=
        @restrictedModule R _ (P.obj : ModuleCat.{u} R) _ iAj
      exact Quotient.sound
        ⟨(AuxiliaryObjectProperty (ModuleCat.{u} R)).fullyFaithfulι.preimageIso
          (idModuleIso iRc inferInstance (fun r x => rfl))⟩

/-- Passing to the quotient by the Jacobson radical preserves the cardinality of the auxiliary ring type. -/
theorem natCard_auxiliaryRingType_jacobsonQuotient (k : Type u) [Field k] [Algebra k R]
    [Module.Finite k R] :
    Nat.card (AuxiliaryRingType.{u} (R ⧸ Ring.jacobson R))
      = Nat.card (AuxiliaryRingType.{u} R) :=
  Nat.card_congr (auxiliaryRingTypeJacobsonQuotientEquiv R)

/-- For a finite group, the owner's associated type is finite. -/
instance _root_.RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter.finite {k G : Type*} [Field k] [Group G] [Finite G] :
    Finite (_root_.RepresentationTheory.FDRep.SimpleCharacters.SimpleCharacter k G) := by
  haveI : Module.Finite k (MonoidAlgebra k G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G k)
  haveI := finite_auxiliaryRingType_of_module_finite k (R := MonoidAlgebra k G)
  exact Finite.of_equiv _ (auxiliaryTypeEquivGroupAlgebraAuxiliaryType k G).symm

end Finiteness

end RepresentationTheory.SimpleRepresentationModules
