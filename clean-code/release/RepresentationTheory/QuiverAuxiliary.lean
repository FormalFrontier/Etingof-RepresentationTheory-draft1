/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.AuxiliaryPathStructures
import RepresentationTheory.Auxiliary.RingData
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Span.Basic

/-!
# An auxiliary module for path algebras

This module constructs a one-dimensional module associated with a vertex of a finite quiver and
uses an arrow ending at that vertex to show that a path algebra does not satisfy the displayed
ring property at zero. Related path-algebra constructions appear in
`RepresentationTheory.Quiver.PathAlgebra.LoopQuiver`, and the relevant ring and category
properties appear in `RepresentationTheory.Auxiliary.RingAndCategoryProperties`.
-/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-- The displayed optional operation returns the nil path at an element of the quiver exactly when
both inputs are that nil path. -/
theorem auxiliary_eq_some_nil_iff (x y : Quiver.AuxiliaryBundledPathType Q) (b : Q) :
    x.compose y = some ⟨b, b, Quiver.Path.nil⟩ ↔
      x = ⟨b, b, Quiver.Path.nil⟩ ∧ y = ⟨b, b, Quiver.Path.nil⟩ := by
  obtain ⟨xa, xb, xp⟩ := x
  obtain ⟨ya, yb, yq⟩ := y
  constructor
  · intro h
    rw [Quiver.AuxiliaryBundledPathType.compose] at h
    split at h
    · rename_i hbc
      subst hbc
      rw [Option.some.injEq] at h
      have hxa : xa = b := congrArg Sigma.fst h
      have hyb : yb = b := congrArg (fun z => z.2.1) h
      have hlen : (xp.comp yq).length = 0 := by
        have := congrArg (fun z => z.2.2.length) h
        simpa using this
      rw [Quiver.Path.length_comp] at hlen
      have hxl : xp.length = 0 := by omega
      have hyl : yq.length = 0 := by omega
      have hxbb : xb = b := (Quiver.Path.eq_of_length_zero xp hxl).symm.trans hxa
      subst xa; subst yb; subst xb
      rw [Quiver.Path.eq_nil_of_length_zero xp hxl, Quiver.Path.eq_nil_of_length_zero yq hyl]
      exact ⟨rfl, rfl⟩
    · exact absurd h (by simp)
  · rintro ⟨hx, hy⟩
    rw [hx, hy,
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType.compose_eq_some,
      Quiver.Path.nil_comp]

/-- The displayed optional operation on two indices returns the first index exactly when the second
is the nil path at the displayed endpoint of the first. -/
theorem auxiliary_eq_some_left_iff (p z : Quiver.AuxiliaryBundledPathType Q) :
    p.compose z = some p ↔ z = ⟨p.2.1, p.2.1, Quiver.Path.nil⟩ := by
  obtain ⟨pa, pb, pp⟩ := p
  obtain ⟨za, zb, zq⟩ := z
  constructor
  · intro h
    rw [Quiver.AuxiliaryBundledPathType.compose] at h
    split at h
    · rename_i hbc
      subst hbc
      rw [Option.some.injEq] at h
      have hzb : zb = pb := congrArg (fun w => w.2.1) h
      have hlen : (pp.comp zq).length = pp.length := by
        have := congrArg (fun w => w.2.2.length) h
        simpa using this
      rw [Quiver.Path.length_comp] at hlen
      have hzl : zq.length = 0 := by omega
      subst zb
      rw [Quiver.Path.eq_nil_of_length_zero zq hzl]
    · exact absurd h (by simp)
  · intro hz
    rw [hz,
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType.compose_eq_some,
      Quiver.Path.comp_nil]

/-- An auxiliary family of linear maps to the field. -/
noncomputable def auxiliaryLinearMap (x : Quiver.AuxiliaryBundledPathType Q) : AuxiliaryPathType k Q →ₗ[k] k :=
  Finsupp.lapply x

open Classical in
/-- The auxiliary linear map applied to a finitely supported singleton is its scalar at the
matching index and zero otherwise. -/
theorem auxiliaryLinearMap_single (x y : Quiver.AuxiliaryBundledPathType Q) (c : k) :
    auxiliaryLinearMap x (Finsupp.single y c) = if y = x then c else 0 :=
  Finsupp.single_apply

open Classical in
/-- The auxiliary linear map applied to the displayed binary construction is one when the displayed
optional value equals its index and zero otherwise. -/
theorem auxiliaryLinearMap_apply_auxiliary (x y z : Quiver.AuxiliaryBundledPathType Q) :
    auxiliaryLinearMap z (auxiliaryProduct x y : AuxiliaryPathType k Q) =
      if x.compose y = some z then (1 : k) else 0 := by
  rw [auxiliaryProduct]
  cases h : x.compose y with
  | none => simp
  | some w => rw [Option.elim_some, auxiliaryLinearMap_single]; simp

/-- An auxiliary ring homomorphism to the field indexed by an element of the quiver. -/
noncomputable def auxiliaryRingHom [Fintype Q] (b : Q) : AuxiliaryPathType k Q →+* k where
  toFun a := auxiliaryLinearMap ⟨b, b, Quiver.Path.nil⟩ a
  map_one' := by
    rw [one_eq_sum_single_vertexPath, map_sum, Finset.sum_eq_single b]
    · rw [auxiliaryLinearMap_single, if_pos rfl]
    · intro i _ hib
      rw [auxiliaryLinearMap_single, if_neg]
      intro hcon
      exact hib (congrArg Sigma.fst hcon)
    · intro hb; exact absurd (Finset.mem_univ b) hb
  map_mul' a a' := by
    induction a using induction_on with
    | zero => simp
    | add f g hf hg => rw [add_mul, map_add, map_add, hf, hg, add_mul]
    | single x c =>
      induction a' using induction_on with
      | zero => simp
      | add f g hf hg => rw [mul_add, map_add, map_add, hf, hg, mul_add]
      | single y d =>
        rw [single_mul_single, map_smul, auxiliaryLinearMap_apply_auxiliary,
          auxiliaryLinearMap_single, auxiliaryLinearMap_single, smul_eq_mul]
        by_cases hx : x = (⟨b, b, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) <;>
          by_cases hy : y = (⟨b, b, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) <;>
          simp [hx, hy, auxiliary_eq_some_nil_iff]
  map_zero' := by simp
  map_add' a a' := by simp

/-- The auxiliary ring homomorphism agrees with the displayed linear map indexed by the nil path. -/
@[simp] theorem auxiliaryRingHom_apply [Fintype Q] (b : Q) (a : AuxiliaryPathType k Q) :
    auxiliaryRingHom b a = auxiliaryLinearMap ⟨b, b, Quiver.Path.nil⟩ a := rfl

/-- The auxiliary ring homomorphism sends the displayed element associated with a quiver
homomorphism to zero. -/
theorem auxiliaryRingHom_apply_eq_zero [Fintype Q] {a b : Q} (e : a ⟶ b) :
    auxiliaryRingHom b (auxiliaryOfPath (⟨a, b, e.toPath⟩ : Quiver.AuxiliaryBundledPathType Q)) = (0 : k) := by
  rw [auxiliaryRingHom_apply, auxiliaryOfPath, auxiliaryLinearMap_single]
  apply if_neg
  intro hcon
  have : (e.toPath).length = (Quiver.Path.nil : Quiver.Path b b).length :=
    congrArg (fun w => w.2.2.length) hcon
  rw [Quiver.Path.length_nil, Quiver.Path.length_toPath] at this
  exact one_ne_zero this

/-- Applying the first displayed linear map to the displayed product agrees with applying the
second displayed linear map to the remaining factor. -/
theorem auxiliary_apply_mul {a b : Q} (e : a ⟶ b) (w : AuxiliaryPathType k Q) :
    auxiliaryLinearMap (⟨a, b, e.toPath⟩ : Quiver.AuxiliaryBundledPathType Q)
        (auxiliaryOfPath ⟨a, b, e.toPath⟩ * w) =
      auxiliaryLinearMap (⟨b, b, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) w := by
  induction w using induction_on with
  | zero => simp
  | add f g hf hg => rw [mul_add, map_add, map_add, hf, hg]
  | single z c =>
    rw [auxiliaryOfPath, single_mul_single, one_mul, map_smul, auxiliaryLinearMap_apply_auxiliary,
      auxiliaryLinearMap_single, smul_eq_mul]
    by_cases hz : z = (⟨b, b, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) <;>
      simp [hz, auxiliary_eq_some_left_iff]

/-- An auxiliary family of types indexed by a finite quiver. -/
def Auxiliary (k : Type u) (Q : Type u) [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]
    [Fintype Q] (_b : Q) : Type (u + 1) := ULift.{u + 1} k

/-- The additive commutative group structure on the auxiliary type. -/
noncomputable instance instAddCommGroupAuxiliary [Fintype Q] (b : Q) :
    AddCommGroup (Auxiliary k Q b) :=
  inferInstanceAs (AddCommGroup (ULift.{u + 1} k))

/-- The field module structure on the auxiliary type. -/
noncomputable instance instModuleAuxiliary [Fintype Q] (b : Q) : Module k (Auxiliary k Q b) :=
  inferInstanceAs (Module k (ULift.{u + 1} k))

/-- The module structure on the auxiliary type over the surrounding scalar type. -/
noncomputable instance instModuleAuxiliarySelf [Fintype Q] (b : Q) :
    Module (AuxiliaryPathType k Q) (Auxiliary k Q b) :=
  Module.compHom (Auxiliary k Q b) (auxiliaryRingHom b)

/-- The displayed action agrees with scalar multiplication through the auxiliary ring
homomorphism. -/
theorem auxiliary_smul_eq_smul [Fintype Q] (b : Q) (a : AuxiliaryPathType k Q)
    (v : Auxiliary k Q b) : a • v = auxiliaryRingHom b a • v := rfl

/-- The value underlying the displayed action is the auxiliary ring homomorphism applied to the
scalar times the value underlying the element. -/
theorem auxiliary_smul_down [Fintype Q] (b : Q) (a : AuxiliaryPathType k Q) (v : Auxiliary k Q b) :
    (a • v).down = auxiliaryRingHom b a * v.down := by
  rw [auxiliary_smul_eq_smul]; rfl

/-- An auxiliary element in the type indexed by an element of the quiver. -/
def auxiliary [Fintype Q] (b : Q) : Auxiliary k Q b := ULift.up (1 : k)

/-- The value underlying the auxiliary element is one. -/
@[simp] theorem auxiliary_down [Fintype Q] (b : Q) :
    (auxiliary (k := k) (Q := Q) b).down = 1 := rfl

/-- The displayed scalar associated with a quiver homomorphism acts as zero on the auxiliary
type. -/
theorem auxiliary_smul_eq_zero [Fintype Q] {a b : Q} (e : a ⟶ b) (v : Auxiliary k Q b) :
    (auxiliaryOfPath ⟨a, b, e.toPath⟩ : AuxiliaryPathType k Q) • v = 0 := by
  apply ULift.ext
  rw [auxiliary_smul_down, auxiliaryRingHom_apply_eq_zero e, zero_mul]
  rfl

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

namespace RepresentationTheory.QuiverAuxiliary

open _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]

/-- If some pair of vertices admits an arrow, the displayed predicate does not hold for zero in the
associated algebra. -/
theorem not_auxiliary_zero_of_exists_hom
    (hQ : ∃ a b : Q, Nonempty (a ⟶ b)) :
    ¬ _root_.RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) 0 := by
  intro hall
  obtain ⟨a, b, ⟨e⟩⟩ := hQ
  let MA := ModuleCat.of
    (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) (Auxiliary k Q b)
  have hpd : CategoryTheory.HasProjectiveDimensionLE MA 0 := hall MA
  haveI hproj : CategoryTheory.Projective MA :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hpd
  haveI hmod : Module.Projective
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q)
      (Auxiliary k Q b) :=
    (IsProjective.iff_projective (Auxiliary k Q b)).mpr hproj
  let surj := LinearMap.toSpanSingleton
    (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q)
    (Auxiliary k Q b) (auxiliary b)
  have hsurj : Function.Surjective surj := by
    intro v
    refine ⟨Finsupp.single ⟨b, b, Quiver.Path.nil⟩ v.down, ?_⟩
    apply ULift.ext
    simp only [surj, LinearMap.toSpanSingleton_apply, auxiliary_smul_down, auxiliaryRingHom_apply,
      auxiliaryLinearMap_single, if_pos, auxiliary_down, mul_one]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property surj LinearMap.id hsurj
  set w : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q :=
    s (auxiliary b) with hw_def
  have hsection : auxiliaryRingHom b w = 1 := by
    have hcf := LinearMap.congr_fun hs (auxiliary b)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcf
    have hdown := congrArg ULift.down hcf
    simp only [surj, LinearMap.toSpanSingleton_apply, auxiliary_smul_down, auxiliary_down,
      mul_one] at hdown
    exact hdown
  have hzero :
      (auxiliaryOfPath ⟨a, b, e.toPath⟩ :
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) * w = 0 := by
    have h1 := s.map_smul
      (auxiliaryOfPath (⟨a, b, e.toPath⟩ :
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q)) (auxiliary b)
    rw [auxiliary_smul_eq_zero e (auxiliary b), map_zero] at h1
    rw [← smul_eq_mul]
    exact h1.symm
  have hne : auxiliaryLinearMap
      (⟨a, b, e.toPath⟩ :
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q)
      (auxiliaryOfPath ⟨a, b, e.toPath⟩ * w) = 1 := by
    rw [auxiliary_apply_mul e w, ← auxiliaryRingHom_apply]; exact hsection
  rw [hzero, map_zero] at hne
  exact one_ne_zero hne.symm

end RepresentationTheory.QuiverAuxiliary
