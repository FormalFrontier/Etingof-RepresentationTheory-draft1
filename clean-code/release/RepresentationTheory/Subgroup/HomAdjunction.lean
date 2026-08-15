/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import Mathlib
import RepresentationTheory.Alignment.Attribute

/-! # Hom adjunction for subgroup representations -/

open CategoryTheory Opposite

universe w

namespace RepresentationTheory.Subgroup.HomAdjunction

variable (k G : Type) [Field k] [Group G] (H : Subgroup G)

/-- A functor from representations of an ambient group to representations of a subgroup. -/
abbrev ambientToSubgroupFunctor : Rep.{w} k G ⥤ Rep.{w} k ↥H := Rep.resFunctor H.subtype

/-- A functor from representations of a subgroup to representations of its ambient group. -/
noncomputable abbrev subgroupToAmbientFunctor : Rep.{w} k ↥H ⥤ Rep.{w} k G :=
  Rep.coindFunctor k H.subtype

/-- The ambient-to-subgroup functor is left adjoint to the subgroup-to-ambient functor. -/
@[source_ref "Chapter5/Introduction_5.10" (role := primary),
  source_ref "Chapter5/Theorem5.10.1" (role := primary)]
noncomputable def ambientSubgroupAdjunction :
    ambientToSubgroupFunctor.{w} k G H ⊣ subgroupToAmbientFunctor.{w} k G H :=
  Rep.resCoindAdjunction.{w} k H.subtype

/-- Forms modules of morphisms from an ambient representation into subgroup-to-ambient images of subgroup representations. -/
noncomputable def subgroupToAmbientHomFunctor : (Rep.{w} k G)ᵒᵖ ⥤ Rep.{w} k ↥H ⥤ ModuleCat k :=
  linearCoyoneda k (Rep.{w} k G) ⋙
    (Functor.whiskeringLeft (Rep.{w} k ↥H) (Rep.{w} k G) (ModuleCat k)).obj
      (subgroupToAmbientFunctor.{w} k G H)

/-- Forms modules of morphisms from ambient-to-subgroup images of ambient representations into subgroup representations. -/
noncomputable def ambientToSubgroupHomFunctor : (Rep.{w} k G)ᵒᵖ ⥤ Rep.{w} k ↥H ⥤ ModuleCat k :=
  (ambientToSubgroupFunctor.{w} k G H).op ⋙ linearCoyoneda k (Rep.{w} k ↥H)

/-- Its value at an ambient representation and a subgroup representation is the module of morphisms into the corresponding subgroup-to-ambient image. -/
@[simp]
lemma subgroupToAmbientHomFunctor_obj (V : Rep.{w} k G) (W : Rep.{w} k ↥H) :
    ((subgroupToAmbientHomFunctor.{w} k G H).obj (op V)).obj W =
      ModuleCat.of k (V ⟶ (subgroupToAmbientFunctor.{w} k G H).obj W) :=
  rfl

/-- Its value at an ambient representation and a subgroup representation is the module of morphisms from the corresponding ambient-to-subgroup image. -/
@[simp]
lemma ambientToSubgroupHomFunctor_obj (V : Rep.{w} k G) (W : Rep.{w} k ↥H) :
    ((ambientToSubgroupHomFunctor.{w} k G H).obj (op V)).obj W =
      ModuleCat.of k ((ambientToSubgroupFunctor.{w} k G H).obj V ⟶ W) :=
  rfl

variable {k G H}

/-- For a fixed ambient representation, an isomorphism between the two resulting module-valued functors on subgroup representations. -/
noncomputable def ambientSubgroupHomIso (V : Rep.{w} k G) :
    (subgroupToAmbientHomFunctor.{w} k G H).obj (op V) ≅ (ambientToSubgroupHomFunctor.{w} k G H).obj (op V) :=
  NatIso.ofComponents
    (fun W => (Rep.resCoindHomEquiv.{w} H.subtype V W).symm.toModuleIso)
    (fun {_ _} g => by
      ext α
      exact (Rep.resCoindAdjunction.{w} k H.subtype).homEquiv_naturality_right_symm α g)

/-- The fixed-representation isomorphism acts on a morphism by the inverse restriction-coinduction Hom equivalence. -/
@[simp]
lemma ambientSubgroupHomIso_app_apply (V : Rep.{w} k G) (W : Rep.{w} k ↥H)
    (α : V ⟶ (subgroupToAmbientFunctor.{w} k G H).obj W) :
    ((ambientSubgroupHomIso V).hom.app W).hom α =
      (Rep.resCoindHomEquiv.{w} H.subtype V W).symm α :=
  rfl

variable (k G H)

/-- An isomorphism between the two displayed module-valued Hom functors on ambient and subgroup representations. -/
@[source_ref "Chapter5/Introduction_5.10" (role := primary),
  source_ref "Chapter5/Theorem5.10.1" (role := primary),
  source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def ambientSubgroupHomFunctorIso :
    subgroupToAmbientHomFunctor.{w} k G H ≅ ambientToSubgroupHomFunctor.{w} k G H :=
  NatIso.ofComponents (fun V => ambientSubgroupHomIso V.unop)
    (fun {_ _} f => by
      ext W α
      exact (Rep.resCoindAdjunction.{w} k H.subtype).homEquiv_naturality_left_symm f.unop α)

/-- The component of the Hom-functor isomorphism at an ambient representation is the corresponding fixed-representation isomorphism. -/
@[simp]
lemma ambientSubgroupHomFunctorIso_app (V : Rep.{w} k G) :
    (ambientSubgroupHomFunctorIso.{w} k G H).hom.app (op V) = (ambientSubgroupHomIso V).hom :=
  rfl

/-- At an ambient representation and a subgroup representation, the functor-isomorphism component acts by the inverse restriction-coinduction Hom equivalence. -/
@[simp, source_ref "Chapter5/Theorem5.10.1" (role := supporting)]
lemma ambientSubgroupHomFunctorIso_app_apply (V : Rep.{w} k G) (W : Rep.{w} k ↥H)
    (α : V ⟶ (subgroupToAmbientFunctor.{w} k G H).obj W) :
    (((ambientSubgroupHomFunctorIso.{w} k G H).hom.app (op V)).app W).hom α =
      (Rep.resCoindHomEquiv.{w} H.subtype V W).symm α :=
  rfl

variable {k G H}

/-- A linear equivalence between morphisms into a subgroup-to-ambient image and morphisms from an ambient-to-subgroup image. -/
@[source_ref "Chapter5/Theorem5.10.1" (role := primary),
  source_ref "Chapter5/Discussion_Problem5.10.2_parts" (role := primary)]
noncomputable def ambientSubgroupHomEquiv (V : Rep.{w} k G) (W : Rep.{w} k ↥H) :
    (V ⟶ (subgroupToAmbientFunctor.{w} k G H).obj W) ≃ₗ[k]
      ((ambientToSubgroupFunctor.{w} k G H).obj V ⟶ W) :=
  (Rep.resCoindHomEquiv.{w} H.subtype V W).symm

/-- Under the displayed Hom-space equivalence, a morphism is evaluated at a vector by taking its value at the identity element. -/
@[simp, source_ref "Chapter5/Theorem5.10.1" (role := primary)]
lemma ambientSubgroupHomEquiv_apply (V : Rep.{w} k G) (W : Rep.{w} k ↥H)
    (α : V ⟶ (subgroupToAmbientFunctor.{w} k G H).obj W) (v : V.V) :
    (ambientSubgroupHomEquiv V W α).hom v = (α.hom v).1 (1 : G) :=
  rfl

/-- There exists a linear equivalence between morphisms into a coinduced representation and morphisms from the corresponding restricted representation. -/
theorem nonemptyResCoindHomEquiv
    (k G : Type) [Field k] [Group G]
    (H : Subgroup G)
    (V : Rep k G) (W : Rep k ↥H) :
    Nonempty ((V ⟶ Rep.coind H.subtype W) ≃ₗ[k]
      ((Rep.resFunctor H.subtype).obj V ⟶ W)) :=
  ⟨ambientSubgroupHomEquiv V W⟩

end RepresentationTheory.Subgroup.HomAdjunction
