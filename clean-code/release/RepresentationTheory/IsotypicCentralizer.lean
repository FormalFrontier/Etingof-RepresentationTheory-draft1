/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.CentralizerDecomposition
import RepresentationTheory.IsotypicComponents
import RepresentationTheory.Centralizer.LinearMaps

/-!
# Isotypic components for centralizers

This module relates simple modules and isotypic components for a semisimple subalgebra of an
endomorphism algebra to those for its centralizer.
-/

open scoped TensorProduct

universe u v w

namespace RepresentationTheory.IsotypicCentralizer

open RepresentationTheory.CentralizerDecomposition
open RepresentationTheory.IsotypicComponents
open RepresentationTheory.Centralizer.LinearMaps

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- The centralizer action on linear maps from an invariant submodule. -/
noncomputable local instance (priority := high) centralizerModuleLinearMap
    (A : Subalgebra k (Module.End k E)) (W : Submodule A E) :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥W →ₗ[A] E) :=
  centralizerModuleHom k E (A := A) (V := ↥W)

/-- An equivariant equivalence induces a centralizer-linear equivalence between the corresponding
linear-map spaces. -/
@[source_ref"Chapter5/Theorem5.18.1"(role:=supporting)]
noncomputable def linearEquivLinearMapPrecomp
    (A : Subalgebra k (Module.End k E))
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (e : M ≃ₗ[A] N) :
    (N →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (M →ₗ[A] E) where
  toFun f := f.comp e.toLinearMap
  invFun f := f.comp e.symm.toLinearMap
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; simp
  map_smul' b f := by
    ext v
    change (centralizerToModuleEnd k E A b) (f (e v)) =
      (centralizerToModuleEnd k E A b) (f (e v))
    rfl

omit [Module.Finite k E] in
/-- Linear maps from a simple module form a simple module for the centralizer. -/
theorem isSimpleModuleLinearMap
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A]
    (V : Type w) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] :
    IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) := by
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  obtain ⟨W, hWsimple, ⟨eVW⟩⟩ :=
    exists_simpleSubmodule_equiv_of_isSemisimple k E A V
  haveI := hWsimple
  letI : Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) := centralizerModuleHom k E (A := A) (V := V)
  have e : (V →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (↥W →ₗ[A] E) := linearEquivLinearMapPrecomp k E A
        (M := ↥W) (N := V) eVW.symm
  haveI : IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥W →ₗ[A] E) := isSimpleModule_linearMap k E A W
  exact IsSimpleModule.congr e

/-- Simple modules are equivalent when their associated centralizer-linear map spaces are
equivalent. -/
@[source_ref"Chapter5/Theorem5.18.1"(role:=supporting)]
theorem linearEquivOfCentralizerLinearEquivLinearMap
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E]
    [IsAlgClosed k]
    (V W : Type w)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [IsSimpleModule A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] [IsSimpleModule A W]
    (h : Nonempty ((V →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (W →ₗ[A] E))) :
    Nonempty (V ≃ₗ[A] W) := by
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  obtain ⟨h⟩ := h
  obtain ⟨S, hSsimple, ⟨eVS⟩⟩ :=
    exists_simpleSubmodule_equiv_of_isSemisimple k E A V
  obtain ⟨T, hTsimple, ⟨eWT⟩⟩ :=
    exists_simpleSubmodule_equiv_of_isSemisimple k E A W
  haveI := hSsimple
  haveI := hTsimple
  have eS : (↥S →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (V →ₗ[A] E) := linearEquivLinearMapPrecomp k E A (M := V) (N := ↥S) eVS
  have eT : (↥T →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (W →ₗ[A] E) := linearEquivLinearMapPrecomp k E A (M := W) (N := ↥T) eWT
  have hST : Nonempty ((↥S →ₗ[A] E)
      ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))] (↥T →ₗ[A] E)) :=
    ⟨eS.trans (h.trans eT.symm)⟩
  obtain ⟨eST⟩ := Subalgebra.centralizer.linearMapEquiv_implies_linearEquiv
    k E A S T hST
  exact ⟨eVS.trans (eST.trans eWT.symm)⟩

variable {k E} in
/-- The simple submodule of `E` chosen inside a nonzero isotypic component `c` over a semisimple
subalgebra `D`. -/
private noncomputable def compSimple
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) : Submodule D E :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule D E)).resolve_left
    (bot_lt_isotypicComponents c.2).ne').choose

variable {k E} in
omit [Module.Finite k E] in
private theorem compSimple_le
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) : compSimple D c ≤ c.1 :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule D E)).resolve_left
    (bot_lt_isotypicComponents c.2).ne').choose_spec.1

variable {k E} in
omit [Module.Finite k E] in
private instance compSimple_isSimple
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) : IsSimpleModule D (compSimple D c) :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule D E)).resolve_left
    (bot_lt_isotypicComponents c.2).ne').choose_spec.2

variable {k E} in
omit [Module.Finite k E] in
private theorem compSimple_component
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) :
    (c.1 : Submodule D E) = isotypicComponent D E (compSimple D c) :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  eq_isotypicComponent_of_le c.2 (compSimple_le D c)

/-- Maps an isotypic component for a subalgebra to one for its centralizer. -/
noncomputable def centralizerIsotypicComponent
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D] [IsAlgClosed k]
    (c : isotypicComponents D E) :
    isotypicComponents (Subalgebra.centralizer k (D : Set (Module.End k E))) E :=
  haveI : IsSemisimpleRing (Subalgebra.centralizer k (D : Set (Module.End k E))) :=
    isSemisimpleRing_centralizer k E D
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  haveI : IsSimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E) := isSimpleModule_linearMap k E D (compSimple D c)
  ⟨isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E
      (exists_simpleSubmodule_equiv_of_isSemisimple k E
        (Subalgebra.centralizer k (D : Set (Module.End k E)))
        (↥(compSimple D c) →ₗ[D] E)).choose,
    ⟨(exists_simpleSubmodule_equiv_of_isSemisimple k E
        (Subalgebra.centralizer k (D : Set (Module.End k E)))
        (↥(compSimple D c) →ₗ[D] E)).choose,
      (exists_simpleSubmodule_equiv_of_isSemisimple k E
        (Subalgebra.centralizer k (D : Set (Module.End k E)))
        (↥(compSimple D c) →ₗ[D] E)).choose_spec.1, rfl⟩⟩

/-- The map from isotypic components to centralizer isotypic components is injective. -/
theorem centralizerIsotypicComponent_injective
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D] [IsAlgClosed k] :
    Function.Injective (centralizerIsotypicComponent k E D) := by
  classical
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  haveI hCss : IsSemisimpleRing (Subalgebra.centralizer k (D : Set (Module.End k E))) :=
    isSemisimpleRing_centralizer k E D
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  intro c c' hcc
  haveI : IsSimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E) := isSimpleModule_linearMap k E D (compSimple D c)
  haveI : IsSimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c') →ₗ[D] E) := isSimpleModule_linearMap k E D (compSimple D c')
  set W := (exists_simpleSubmodule_equiv_of_isSemisimple k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E)).choose with hWdef
  set W' := (exists_simpleSubmodule_equiv_of_isSemisimple k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c') →ₗ[D] E)).choose with hW'def
  obtain ⟨hWsimple, ⟨eMW⟩⟩ := (exists_simpleSubmodule_equiv_of_isSemisimple k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E)).choose_spec
  obtain ⟨hW'simple, ⟨eMW'⟩⟩ := (exists_simpleSubmodule_equiv_of_isSemisimple k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c') →ₗ[D] E)).choose_spec
  haveI := hWsimple
  haveI := hW'simple
  have hcomp : isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W =
      isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W' :=
    congrArg (fun x => (x.1 : Submodule _ E)) hcc
  have hWle : W ≤ isotypicComponent
      (Subalgebra.centralizer k (D : Set (Module.End k E))) E W :=
    Submodule.le_isotypicComponent W
  have hW'le : W' ≤ isotypicComponent
      (Subalgebra.centralizer k (D : Set (Module.End k E))) E W :=
    hcomp ▸ Submodule.le_isotypicComponent W'
  obtain ⟨eWc⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent
      (Subalgebra.centralizer k (D : Set (Module.End k E))) E W) W hWle
  obtain ⟨eW'c⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent
      (Subalgebra.centralizer k (D : Set (Module.End k E))) E W) W' hW'le
  have hMM : Nonempty ((↥(compSimple D c) →ₗ[D] E)
      ≃ₗ[Subalgebra.centralizer k (D : Set (Module.End k E))]
        (↥(compSimple D c') →ₗ[D] E)) :=
    ⟨eMW.trans (eWc.trans (eW'c.symm.trans eMW'.symm))⟩
  obtain ⟨eVV⟩ := Subalgebra.centralizer.linearMapEquiv_implies_linearEquiv
    k E D (compSimple D c) (compSimple D c') hMM
  have hDcomp : isotypicComponent D E (compSimple D c) =
      isotypicComponent D E (compSimple D c') :=
    eVV.isotypicComponent_eq
  have hc1 : (c.1 : Submodule D E) = c'.1 := by
    rw [compSimple_component D c, compSimple_component D c', hDcomp]
  exact Subtype.ext hc1

/-- The map from isotypic components to centralizer isotypic components is bijective. -/
theorem centralizerIsotypicComponent_bijective
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [IsAlgClosed k] :
    Function.Bijective (centralizerIsotypicComponent k E A) := by
  classical
  set C := Subalgebra.centralizer k (A : Set (Module.End k E)) with hC
  haveI hCss : IsSemisimpleRing C := isSemisimpleRing_centralizer k E A
  haveI hCCss : IsSemisimpleRing (Subalgebra.centralizer k (C : Set (Module.End k E))) :=
    isSemisimpleRing_centralizer k E C
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : IsSemisimpleModule C E := IsSemisimpleRing.isSemisimpleModule
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (C : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  haveI : Module.Finite C E := Module.Finite.of_restrictScalars_finite k C E
  haveI : Module.Finite (Subalgebra.centralizer k (C : Set (Module.End k E))) E :=
    Module.Finite.of_restrictScalars_finite k _ E
  haveI : IsNoetherian A E := inferInstance
  haveI : IsNoetherian C E := inferInstance
  haveI : IsNoetherian (Subalgebra.centralizer k (C : Set (Module.End k E))) E := inferInstance
  haveI : Fintype (isotypicComponents A E) := Fintype.ofFinite _
  haveI : Fintype (isotypicComponents C E) := Fintype.ofFinite _
  haveI : Fintype
      (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E) :=
    Fintype.ofFinite _
  have hα : Function.Injective (centralizerIsotypicComponent k E A) :=
    centralizerIsotypicComponent_injective k E A
  have hβ : Function.Injective (centralizerIsotypicComponent k E C) :=
    centralizerIsotypicComponent_injective k E C
  have hcardα : Fintype.card (isotypicComponents A E) ≤
      Fintype.card (isotypicComponents C E) :=
    Fintype.card_le_of_injective _ hα
  have hcardβ : Fintype.card (isotypicComponents C E) ≤
      Fintype.card
        (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E) :=
    Fintype.card_le_of_injective _ hβ
  have hCC : Subalgebra.centralizer k (C : Set (Module.End k E)) = A :=
    centralizer_centralizer_eq k E A
  have hType :
      (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E : Type _) =
        (isotypicComponents A E : Type _) := by
    rw [hCC]
  have hcardCC : Fintype.card
      (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E) =
      Fintype.card (isotypicComponents A E) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hType]
  have hcard_eq : Fintype.card (isotypicComponents A E) =
      Fintype.card (isotypicComponents C E) :=
    le_antisymm hcardα (hcardβ.trans (le_of_eq hcardCC))
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hα, hcard_eq⟩

/-- Equivalence between the isotypic components of a subalgebra and of its centralizer. -/
@[source_ref"Chapter5/Theorem5.18.1"(role:=supporting)]
noncomputable def isotypicComponentsEquivCentralizer
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [IsAlgClosed k] :
    isotypicComponents A E ≃
      isotypicComponents (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
  Equiv.ofBijective _ (centralizerIsotypicComponent_bijective k E A)

/-- Every simple centralizer module is linearly equivalent to maps from a simple submodule. -/
@[source_ref"Chapter5/Theorem5.18.1"(role:=supporting)]
theorem existsIsSimpleModuleSubmoduleLinearMapEquiv
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [IsAlgClosed k]
    (W : Type w) [AddCommGroup W]
    [Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) W]
    [IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) W] :
    ∃ V : Submodule A E, IsSimpleModule A V ∧
      Nonempty (W ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
        (↥V →ₗ[A] E)) := by
  classical
  haveI hCss : IsSemisimpleRing (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    isSemisimpleRing_centralizer k E A
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  obtain ⟨W₀, hW₀simple, ⟨eWW₀⟩⟩ := exists_simpleSubmodule_equiv_of_isSemisimple k E
    (Subalgebra.centralizer k (A : Set (Module.End k E))) W
  haveI := hW₀simple
  set d : isotypicComponents (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    ⟨isotypicComponent _ E W₀, ⟨W₀, hW₀simple, rfl⟩⟩ with hd
  obtain ⟨c, hc⟩ := (centralizerIsotypicComponent_bijective k E A).2 d
  haveI : IsSimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥(compSimple A c) →ₗ[A] E) := isSimpleModule_linearMap k E A (compSimple A c)
  set R := (exists_simpleSubmodule_equiv_of_isSemisimple k E
      (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥(compSimple A c) →ₗ[A] E)).choose with hRdef
  obtain ⟨hRsimple, ⟨eMR⟩⟩ := (exists_simpleSubmodule_equiv_of_isSemisimple k E
      (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥(compSimple A c) →ₗ[A] E)).choose_spec
  haveI := hRsimple
  have hcomp : isotypicComponent (Subalgebra.centralizer k (A : Set (Module.End k E))) E R =
      isotypicComponent (Subalgebra.centralizer k (A : Set (Module.End k E))) E W₀ :=
    congrArg Subtype.val hc
  have hRle : R ≤ isotypicComponent
      (Subalgebra.centralizer k (A : Set (Module.End k E))) E R :=
    Submodule.le_isotypicComponent R
  have hW₀le : W₀ ≤ isotypicComponent
      (Subalgebra.centralizer k (A : Set (Module.End k E))) E R :=
    hcomp ▸ Submodule.le_isotypicComponent W₀
  obtain ⟨eRc⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent _ E R) R hRle
  obtain ⟨eW₀c⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent _ E R) W₀ hW₀le
  exact ⟨compSimple A c, compSimple_isSimple A c,
    ⟨eWW₀.trans (eW₀c.trans (eRc.symm.trans eMR.symm))⟩⟩

end RepresentationTheory.IsotypicCentralizer
