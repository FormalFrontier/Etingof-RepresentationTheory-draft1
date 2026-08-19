/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import RepresentationTheory.FreeAlgebra.PolynomialOperators
import RepresentationTheory.Alignment.Attribute

/-! # Three-generator presentations -/

namespace RepresentationTheory.LieAlgebra.ThreeGeneratorPresentations

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type*} [CommRing k]

/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
def AuxiliaryType (k : Type*) [CommRing k] : Type _ := k × k × k

/-- Provides the indicated AddCommGroup structure on the specified type. -/
instance instAddCommGroup : AddCommGroup (AuxiliaryType k) := inferInstanceAs (AddCommGroup (k × k × k))

/-- Provides the indicated Module structure on the specified type. -/
instance instModule : Module k (AuxiliaryType k) := inferInstanceAs (Module k (k × k × k))

/-- Two coordinate triples are equal when their three coordinates agree. -/
@[ext] theorem AuxiliaryType.ext {a b : AuxiliaryType k}
    (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) (h3 : a.2.2 = b.2.2) : a = b :=
  Prod.ext h1 (Prod.ext h2 h3)

/-- The first coordinate of a sum is the sum of the corresponding coordinates. -/
@[simp] theorem fst_add (a b : AuxiliaryType k) : (a + b).1 = a.1 + b.1 := rfl
/-- The middle coordinate of a sum is the sum of the middle coordinates. -/
@[simp] theorem snd_fst_add (a b : AuxiliaryType k) : (a + b).2.1 = a.2.1 + b.2.1 := rfl
/-- The third coordinate of a sum is the sum of the corresponding coordinates. -/
@[simp] theorem snd_snd_add (a b : AuxiliaryType k) : (a + b).2.2 = a.2.2 + b.2.2 := rfl
/-- The first coordinate of zero is zero. -/
@[simp] theorem fst_zero : (0 : AuxiliaryType k).1 = 0 := rfl
/-- The indicated nested coordinate of zero is zero. -/
@[simp] theorem snd_fst_zero : (0 : AuxiliaryType k).2.1 = 0 := rfl
/-- The third coordinate of zero is zero. -/
@[simp] theorem snd_snd_zero : (0 : AuxiliaryType k).2.2 = 0 := rfl
/-- The first coordinate of a scalar multiple is the scalar multiple of that coordinate. -/
@[simp] theorem fst_smul (t : k) (a : AuxiliaryType k) : (t • a).1 = t • a.1 := rfl
/-- The middle coordinate of a scalar multiple is the scalar multiple of the middle coordinate. -/
@[simp] theorem snd_fst_smul (t : k) (a : AuxiliaryType k) : (t • a).2.1 = t • a.2.1 := rfl
/-- The third coordinate of a scalar multiple is the scalar multiple of that coordinate. -/
@[simp] theorem snd_snd_smul (t : k) (a : AuxiliaryType k) : (t • a).2.2 = t • a.2.2 := rfl

/-- Provides the indicated Bracket structure on the specified type. -/
instance instBracket : Bracket (AuxiliaryType k) (AuxiliaryType k) where
  bracket u v := ((0 : k), (0 : k), v.1 * u.2.1 - u.1 * v.2.1)

/-- The bracket of the displayed elements has the stated value. -/
@[simp]
theorem bracket_eq (u v : AuxiliaryType k) :
    ⁅u, v⁆ = ((0 : k), (0 : k), v.1 * u.2.1 - u.1 * v.2.1) := rfl

/-- Provides the indicated LieRing structure on the specified type. -/
instance instLieRing : LieRing (AuxiliaryType k) where
  add_lie u v w := by
    apply AuxiliaryType.ext <;>
      simp only [bracket_eq, fst_add, snd_fst_add, snd_snd_add] <;> ring
  lie_add u v w := by
    apply AuxiliaryType.ext <;>
      simp only [bracket_eq, fst_add, snd_fst_add, snd_snd_add] <;> ring
  lie_self u := by
    apply AuxiliaryType.ext <;> simp [bracket_eq]
  leibniz_lie u v w := by
    apply AuxiliaryType.ext <;>
      simp only [bracket_eq, fst_add, snd_fst_add, snd_snd_add] <;> ring

/-- Provides the indicated LieAlgebra structure on the specified type. -/
instance instLieAlgebra : LieAlgebra k (AuxiliaryType k) where
  lie_smul t u v := by
    apply AuxiliaryType.ext <;>
      simp only [bracket_eq, fst_smul, snd_fst_smul, snd_snd_smul, smul_eq_mul] <;> ring

/-- A distinguished value of the displayed type. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
def distinguishedElement_aux5 : AuxiliaryType k := ((1 : k), (0 : k), (0 : k))

/-- A distinguished value of the displayed type. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
def distinguishedElement_aux6 : AuxiliaryType k := ((0 : k), (1 : k), (0 : k))

/-- A distinguished value of the displayed type. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
def distinguishedElement_aux2 : AuxiliaryType k := ((0 : k), (0 : k), (1 : k))

/-- The bracket of the displayed elements has the stated value. -/
@[simp, source_ref "Chapter2/Example2.9.13" (role := supporting),
  source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived7" (role := supporting)]
theorem bracket_eq_aux3 : ⁅(distinguishedElement_aux6 : AuxiliaryType k), (distinguishedElement_aux5 : AuxiliaryType k)⁆ = (distinguishedElement_aux2 : AuxiliaryType k) := by
  simp [bracket_eq, distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux2]

/-- The bracket of the displayed elements has the stated value. -/
@[simp, source_ref "Chapter2/Example2.9.13" (role := supporting),
  source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived7" (role := supporting)]
theorem bracket_eq_aux1 : ⁅(distinguishedElement_aux5 : AuxiliaryType k), (distinguishedElement_aux2 : AuxiliaryType k)⁆ = 0 := by
  apply AuxiliaryType.ext <;> simp [bracket_eq, distinguishedElement_aux5, distinguishedElement_aux2]

/-- The bracket of the displayed elements has the stated value. -/
@[simp, source_ref "Chapter2/Example2.9.13" (role := supporting),
  source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived7" (role := supporting)]
theorem bracket_eq_aux2 : ⁅(distinguishedElement_aux6 : AuxiliaryType k), (distinguishedElement_aux2 : AuxiliaryType k)⁆ = 0 := by
  apply AuxiliaryType.ext <;> simp [bracket_eq, distinguishedElement_aux6, distinguishedElement_aux2]

/-- Both displayed properties hold. -/
@[source_ref "Chapter2/Example2.9.13" (role := primary)]
theorem property_and (k : Type*) [CommRing k] :
    (ι k (distinguishedElement_aux6 : AuxiliaryType k)) * (ι k distinguishedElement_aux5) - (ι k distinguishedElement_aux5) * (ι k distinguishedElement_aux6) = ι k distinguishedElement_aux2 ∧
    (ι k (distinguishedElement_aux6 : AuxiliaryType k)) * (ι k distinguishedElement_aux2) - (ι k distinguishedElement_aux2) * (ι k distinguishedElement_aux6) = 0 ∧
    (ι k (distinguishedElement_aux5 : AuxiliaryType k)) * (ι k distinguishedElement_aux2) - (ι k distinguishedElement_aux2) * (ι k distinguishedElement_aux5) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, bracket_eq_aux3]
  · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, bracket_eq_aux2, map_zero]
  · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, bracket_eq_aux1, map_zero]

/-- A binary relation on the free algebra over three generators. -/
inductive AuxiliaryRelation (k : Type*) [CommRing k] :
    FreeAlgebra k (Fin 3) → FreeAlgebra k (Fin 3) → Prop
  | relation1 : AuxiliaryRelation k
      (FreeAlgebra.ι k 1 * FreeAlgebra.ι k 0 - FreeAlgebra.ι k 0 * FreeAlgebra.ι k 1)
      (FreeAlgebra.ι k 2)
  | relation2 : AuxiliaryRelation k
      (FreeAlgebra.ι k 1 * FreeAlgebra.ι k 2 - FreeAlgebra.ι k 2 * FreeAlgebra.ι k 1)
      0
  | relation3 : AuxiliaryRelation k
      (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 2 - FreeAlgebra.ι k 2 * FreeAlgebra.ι k 0)
      0

/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
def AuxiliaryType_aux1 (k : Type*) [CommRing k] : Type _ := RingQuot (AuxiliaryRelation k)

/-- Provides the indicated Ring structure on the specified type. -/
instance instRing : Ring (AuxiliaryType_aux1 k) :=
  inferInstanceAs (Ring (RingQuot (AuxiliaryRelation k)))

/-- Provides the indicated Algebra structure on the specified type. -/
instance instAlgebra : Algebra k (AuxiliaryType_aux1 k) :=
  inferInstanceAs (Algebra k (RingQuot (AuxiliaryRelation k)))

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux1 (k : Type*) [CommRing k] :
    FreeAlgebra k (Fin 3) →ₐ[k] AuxiliaryType_aux1 k :=
  RingQuot.mkAlgHom k (AuxiliaryRelation k)

/-- A distinguished value of the displayed type. -/
def distinguishedElement_aux3 (k : Type*) [CommRing k] (i : Fin 3) : AuxiliaryType_aux1 k :=
  algHom_aux1 k (FreeAlgebra.ι k i)

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux4 (k : Type*) [CommRing k] :
    distinguishedElement_aux3 k 1 * distinguishedElement_aux3 k 0 -
        distinguishedElement_aux3 k 0 * distinguishedElement_aux3 k 1 = distinguishedElement_aux3 k 2 := by
  change (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 1) *
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 0) -
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 0) *
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 1) =
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 2)
  have hrel := RingQuot.mkAlgHom_rel (S := k) (AuxiliaryRelation.relation1 (k := k))
  simpa only [map_sub, map_mul] using hrel

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux3 (k : Type*) [CommRing k] :
    distinguishedElement_aux3 k 1 * distinguishedElement_aux3 k 2 -
        distinguishedElement_aux3 k 2 * distinguishedElement_aux3 k 1 = 0 := by
  change (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 1) *
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 2) -
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 2) *
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 1) = 0
  have hrel := RingQuot.mkAlgHom_rel (S := k) (AuxiliaryRelation.relation2 (k := k))
  simpa only [map_sub, map_mul, map_zero] using hrel

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux2 (k : Type*) [CommRing k] :
    distinguishedElement_aux3 k 0 * distinguishedElement_aux3 k 2 -
        distinguishedElement_aux3 k 2 * distinguishedElement_aux3 k 0 = 0 := by
  change (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 0) *
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 2) -
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 2) *
      (RingQuot.mkAlgHom k (AuxiliaryRelation k)) (FreeAlgebra.ι k 0) = 0
  have hrel := RingQuot.mkAlgHom_rel (S := k) (AuxiliaryRelation.relation3 (k := k))
  simpa only [map_sub, map_mul, map_zero] using hrel

section PresentationTriple

variable {A : Type*} [Ring A] [Algebra k A]

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
def lieHom (X Y C : A) (hYX : Y * X - X * Y = C)
    (hYC : Y * C - C * Y = 0) (hXC : X * C - C * X = 0) :
    AuxiliaryType k →ₗ⁅k⁆ A where
  toFun u := u.1 • X + u.2.1 • Y + u.2.2 • C
  map_add' u v := by
    simp only [fst_add, snd_fst_add, snd_snd_add, add_smul]
    abel
  map_smul' t u := by
    simp only [fst_smul, snd_fst_smul, snd_snd_smul, smul_eq_mul, RingHom.id_apply,
      smul_add, smul_smul]
  map_lie' {u v} := by
    obtain ⟨a₁, b₁, d₁⟩ := u
    obtain ⟨a₂, b₂, d₂⟩ := v
    have expand :
        (a₁ • X + b₁ • Y + d₁ • C) * (a₂ • X + b₂ • Y + d₂ • C) -
            (a₂ • X + b₂ • Y + d₂ • C) * (a₁ • X + b₁ • Y + d₁ • C) =
          (b₁ * a₂ - b₂ * a₁) • (Y * X - X * Y) +
            (b₁ * d₂ - b₂ * d₁) • (Y * C - C * Y) +
            (a₁ * d₂ - a₂ * d₁) • (X * C - C * X) := by
      simp only [add_mul, mul_add, smul_mul_smul_comm, smul_sub]
      module
    simp only [LieRing.of_associative_ring_bracket, bracket_eq]
    rw [expand, hYX, hYC, hXC]
    module

/-- The Lie homomorphism sends a coordinate triple to the corresponding linear combination of the displayed elements. -/
@[simp] theorem lieHom_apply (X Y C : A) (hYX : Y * X - X * Y = C)
    (hYC : Y * C - C * Y = 0) (hXC : X * C - C * X = 0) (u : AuxiliaryType k) :
    lieHom X Y C hYX hYC hXC u =
      u.1 • X + u.2.1 • Y + u.2.2 • C := rfl

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux2 (X Y C : A) (hYX : Y * X - X * Y = C)
    (hYC : Y * C - C * Y = 0) (hXC : X * C - C * X = 0) :
    lieHom X Y C hYX hYC hXC (distinguishedElement_aux5 : AuxiliaryType k) = X := by simp [distinguishedElement_aux5]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux3 (X Y C : A) (hYX : Y * X - X * Y = C)
    (hYC : Y * C - C * Y = 0) (hXC : X * C - C * X = 0) :
    lieHom X Y C hYX hYC hXC (distinguishedElement_aux6 : AuxiliaryType k) = Y := by simp [distinguishedElement_aux6]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux1 (X Y C : A) (hYX : Y * X - X * Y = C)
    (hYC : Y * C - C * Y = 0) (hXC : X * C - C * X = 0) :
    lieHom X Y C hYX hYC hXC (distinguishedElement_aux2 : AuxiliaryType k) = C := by simp [distinguishedElement_aux2]

end PresentationTriple

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
def lieHom_aux1 (k : Type*) [CommRing k] :
    AuxiliaryType k →ₗ⁅k⁆ AuxiliaryType_aux1 k :=
  lieHom (distinguishedElement_aux3 k 0) (distinguishedElement_aux3 k 1)
    (distinguishedElement_aux3 k 2) (displayed_eq_aux4 k) (displayed_eq_aux3 k)
    (displayed_eq_aux2 k)

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux4 (k : Type*) [CommRing k] :
    UniversalEnvelopingAlgebra k (AuxiliaryType k) →ₐ[k] AuxiliaryType_aux1 k :=
  UniversalEnvelopingAlgebra.lift k (lieHom_aux1 k)

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux3 (k : Type*) [CommRing k] :
    FreeAlgebra k (Fin 3) →ₐ[k] UniversalEnvelopingAlgebra k (AuxiliaryType k) :=
  FreeAlgebra.lift k ![ι k (distinguishedElement_aux5 : AuxiliaryType k), ι k (distinguishedElement_aux6 : AuxiliaryType k),
    ι k (distinguishedElement_aux2 : AuxiliaryType k)]

/-- The free-generator algebra homomorphism sends each generator to the canonical image of the corresponding distinguished coordinate. -/
@[simp] theorem freeGenerator_map (k : Type*) [CommRing k] (i : Fin 3) :
    algHom_aux3 k (FreeAlgebra.ι k i) =
      ι k (![(distinguishedElement_aux5 : AuxiliaryType k), distinguishedElement_aux6, distinguishedElement_aux2] i) := by
  simp only [algHom_aux3, FreeAlgebra.lift_ι_apply]
  fin_cases i <;> simp

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux4 (k : Type*) [CommRing k] :
    ∀ ⦃a b : FreeAlgebra k (Fin 3)⦄, AuxiliaryRelation k a b →
      algHom_aux3 k a = algHom_aux3 k b := by
  rintro a b hab
  obtain _ | _ | _ := hab
  · simpa using (property_and k).1
  · simpa using (property_and k).2.1
  · simpa using (property_and k).2.2

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux2 (k : Type*) [CommRing k] :
    AuxiliaryType_aux1 k →ₐ[k] UniversalEnvelopingAlgebra k (AuxiliaryType k) :=
  RingQuot.liftAlgHom k ⟨algHom_aux3 k, map_apply_aux4 k⟩

/-- The algebra homomorphism sends the canonical image of a coordinate triple to its corresponding linear combination of the three indexed distinguished elements. -/
@[simp] theorem algHom_iota_apply (k : Type*) [CommRing k] (u : AuxiliaryType k) :
    algHom_aux4 k (ι k u) =
      u.1 • distinguishedElement_aux3 k 0 + u.2.1 • distinguishedElement_aux3 k 1 +
        u.2.2 • distinguishedElement_aux3 k 2 :=
  UniversalEnvelopingAlgebra.lift_ι_apply k (lieHom_aux1 k) u

/-- The algebra homomorphism sends each indexed distinguished element to the canonical image of the corresponding coordinate basis element. -/
@[simp] theorem algHom_distinguishedElement_apply (k : Type*) [CommRing k] (i : Fin 3) :
    algHom_aux2 k (distinguishedElement_aux3 k i) =
      ι k (![(distinguishedElement_aux5 : AuxiliaryType k), distinguishedElement_aux6, distinguishedElement_aux2] i) := by
  change RingQuot.liftAlgHom k ⟨algHom_aux3 k, map_apply_aux4 k⟩
      (RingQuot.mkAlgHom k (AuxiliaryRelation k) (FreeAlgebra.ι k i)) = _
  rw [RingQuot.liftAlgHom_mkAlgHom_apply, freeGenerator_map]

/-- The composite of the displayed algebra homomorphisms is the stated map. -/
theorem algHom_comp_eq (k : Type*) [CommRing k] :
    (algHom_aux2 k).comp (algHom_aux4 k) =
      AlgHom.id k (UniversalEnvelopingAlgebra k (AuxiliaryType k)) := by
  ext u
  simp only [AlgHom.coe_comp, LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
    AlgHom.coe_id, id_eq, algHom_iota_apply, map_add, map_smul,
    algHom_distinguishedElement_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add]
  apply congrArg (ι k)
  apply AuxiliaryType.ext <;> simp [distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux2]

/-- The composite of the displayed algebra homomorphisms is the stated map. -/
theorem algHom_comp_eq_aux1 (k : Type*) [CommRing k] :
    (algHom_aux4 k).comp (algHom_aux2 k) =
      AlgHom.id k (AuxiliaryType_aux1 k) := by
  apply RingQuot.ringQuot_ext'
  ext i
  fin_cases i
  · change algHom_aux4 k (algHom_aux2 k (distinguishedElement_aux3 k 0)) =
      distinguishedElement_aux3 k 0
    simp [algHom_aux4, lieHom_aux1, distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux2]
  · change algHom_aux4 k (algHom_aux2 k (distinguishedElement_aux3 k 1)) =
      distinguishedElement_aux3 k 1
    simp [algHom_aux4, lieHom_aux1, distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux2]
  · change algHom_aux4 k (algHom_aux2 k (distinguishedElement_aux3 k 2)) =
      distinguishedElement_aux3 k 2
    simp [algHom_aux4, lieHom_aux1, distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux2]

/-- An algebra equivalence between the displayed algebras. -/
@[source_ref "Chapter2/Example2.9.13" (role := primary)]
def algEquiv (k : Type*) [CommRing k] :
    AuxiliaryType_aux1 k ≃ₐ[k] UniversalEnvelopingAlgebra k (AuxiliaryType k) :=
  AlgEquiv.ofAlgHom (algHom_aux2 k) (algHom_aux4 k)
    (algHom_comp_eq k) (algHom_comp_eq_aux1 k)

/-- There exists a value satisfying the displayed conditions. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
theorem exists_witness (k : Type*) [CommRing k] :
    ∃ e : AuxiliaryType_aux1 k ≃ₐ[k] UniversalEnvelopingAlgebra k (AuxiliaryType k),
      e (distinguishedElement_aux3 k 0) = ι k (distinguishedElement_aux5 : AuxiliaryType k) ∧
      e (distinguishedElement_aux3 k 1) = ι k (distinguishedElement_aux6 : AuxiliaryType k) ∧
      e (distinguishedElement_aux3 k 2) = ι k (distinguishedElement_aux2 : AuxiliaryType k) := by
  refine ⟨algEquiv k, ?_, ?_, ?_⟩ <;>
    simp [algEquiv]

/-- A ring congruence on the displayed free algebra. -/
abbrev ringCon (k : Type*) [CommRing k] :
    RingCon (UniversalEnvelopingAlgebra k (AuxiliaryType k)) :=
  (TwoSidedIdeal.span {ι k (distinguishedElement_aux2 : AuxiliaryType k) - 1}).ringCon

/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
abbrev AuxiliaryType_aux2 (k : Type*) [CommRing k] : Type _ := (ringCon k).Quotient

/-- The displayed map sends the specified input to the stated value. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
theorem map_apply_aux14 (k : Type*) [CommRing k] :
    (ringCon k).mk' (ι k (distinguishedElement_aux2 : AuxiliaryType k)) = (ringCon k).mk' 1 := by
  have h : ringCon k (ι k (distinguishedElement_aux2 : AuxiliaryType k)) 1 := by
    rw [ringCon, TwoSidedIdeal.rel_iff]
    exact TwoSidedIdeal.subset_span (Set.mem_singleton _)
  exact (RingCon.eq _).mpr h

/-- A linear map between the displayed modules. -/
noncomputable def linearMap (k : Type*) [CommRing k] :
    AuxiliaryType k →ₗ[k] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k where
  toFun u := u.1 • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k + u.2.1 • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + u.2.2 • 1
  map_add' u v := by
    simp only [fst_add, snd_fst_add, snd_snd_add, add_smul]; abel
  map_smul' t u := by
    simp only [fst_smul, snd_fst_smul, snd_snd_smul, RingHom.id_apply, smul_assoc, smul_add]

/-- The linear map sends a coordinate triple to the corresponding linear combination of the two displayed elements and one. -/
@[simp] theorem linearMap_apply (k : Type*) [CommRing k] (u : AuxiliaryType k) :
    linearMap k u =
      u.1 • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k + u.2.1 • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + u.2.2 • 1 := rfl

section OperatorBrackets

variable (k : Type*) [CommRing k]

private theorem second_first_bracket :
    ⁅RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k⁆ = (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  rw [LieRing.of_associative_ring_bracket, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator]; abel

private theorem first_second_bracket :
    ⁅RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k⁆ = (-1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  rw [LieRing.of_associative_ring_bracket, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator]; abel

private theorem first_one_bracket :
    ⁅RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k, (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_one, one_mul, sub_self]

private theorem one_first_bracket :
    ⁅(1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k), RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_one, one_mul, sub_self]

private theorem second_one_bracket :
    ⁅RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k, (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_one, one_mul, sub_self]

private theorem one_second_bracket :
    ⁅(1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k), RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_one, one_mul, sub_self]

private theorem one_one_bracket :
    ⁅(1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k), (1 : RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k)⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_one, sub_self]

end OperatorBrackets

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux2 (k : Type*) [CommRing k] :
    AuxiliaryType k →ₗ⁅k⁆ RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k :=
  { linearMap k with
    map_lie' := fun {u v} => by
      change linearMap k ⁅u, v⁆ =
        ⁅linearMap k u, linearMap k v⁆
      rw [LieRing.of_associative_ring_bracket]
      simp only [linearMap_apply, bracket_eq,
        mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_one, one_mul,
        RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator_mul_firstOperator, smul_add, zero_smul, add_zero, zero_add]
      module }

/-- The Lie homomorphism sends a coordinate triple to the corresponding linear combination of the two displayed elements and one. -/
@[simp] theorem lieHom_apply_aux1 (k : Type*) [CommRing k] (u : AuxiliaryType k) :
    lieHom_aux2 k u =
      u.1 • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k + u.2.1 • RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k + u.2.2 • 1 := rfl

/-- An algebra homomorphism between the displayed algebras. -/
noncomputable def algHom (k : Type*) [CommRing k] :
    UniversalEnvelopingAlgebra k (AuxiliaryType k) →ₐ[k] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k :=
  UniversalEnvelopingAlgebra.lift k (lieHom_aux2 k)

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply (k : Type*) [CommRing k] :
    algHom k (ι k (distinguishedElement_aux2 : AuxiliaryType k)) = 1 := by
  rw [algHom, UniversalEnvelopingAlgebra.lift_ι_apply, lieHom_apply_aux1, distinguishedElement_aux2]
  simp

/-- The displayed ring congruence is contained in the kernel of the algebra homomorphism. -/
theorem ringCon_le_ker (k : Type*) [CommRing k] :
    ringCon k ≤ RingCon.ker (algHom k).toRingHom := by
  have hsub : TwoSidedIdeal.span {ι k (distinguishedElement_aux2 : AuxiliaryType k) - 1} ≤
      TwoSidedIdeal.ker (algHom k).toRingHom := by
    rw [TwoSidedIdeal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
    change algHom k (ι k (distinguishedElement_aux2 : AuxiliaryType k) - 1) = 0
    rw [map_sub, map_one, map_apply, sub_self]
  intro a b hab
  rw [RingCon.ker_apply]
  change algHom k a = algHom k b
  rw [← sub_eq_zero, ← map_sub]
  exact (TwoSidedIdeal.mem_ker _).1 (hsub ((TwoSidedIdeal.rel_iff _ _ _).1 hab))

/-- An algebra homomorphism between the displayed algebras. -/
noncomputable def algHom_aux6 (k : Type*) [CommRing k] :
    AuxiliaryType_aux2 k →ₐ[k] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k :=
  (ringCon k).liftₐ (algHom k) (ringCon_le_ker k)

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux13 (k : Type*) [CommRing k]
    (a : UniversalEnvelopingAlgebra k (AuxiliaryType k)) :
    algHom_aux6 k ((ringCon k).mkₐ k a) = algHom k a := rfl

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement (k : Type*) [CommRing k] : AuxiliaryType_aux2 k :=
  (ringCon k).mkₐ k (ι k (distinguishedElement_aux5 : AuxiliaryType k))

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux1 (k : Type*) [CommRing k] : AuxiliaryType_aux2 k :=
  (ringCon k).mkₐ k (ι k (distinguishedElement_aux6 : AuxiliaryType k))

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux1 (k : Type*) [CommRing k] :
    distinguishedElement_aux1 k * distinguishedElement k = distinguishedElement k * distinguishedElement_aux1 k + 1 := by
  have hrel := (property_and k).1
  have hmk : (ringCon k).mkₐ k (ι k (distinguishedElement_aux6 : AuxiliaryType k) * ι k distinguishedElement_aux5 - ι k distinguishedElement_aux5 * ι k distinguishedElement_aux6) =
      (ringCon k).mkₐ k (ι k (distinguishedElement_aux2 : AuxiliaryType k)) := by rw [hrel]
  rw [map_sub, map_mul, map_mul] at hmk
  have hc : (ringCon k).mkₐ k (ι k (distinguishedElement_aux2 : AuxiliaryType k)) = 1 := by
    change (ringCon k).mk' (ι k (distinguishedElement_aux2 : AuxiliaryType k)) = 1
    rw [map_apply_aux14]; exact map_one _
  rw [hc] at hmk
  rw [distinguishedElement, distinguishedElement_aux1, ← sub_eq_iff_eq_add']
  exact hmk

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux4 (k : Type*) [CommRing k] : RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraGenerator → AuxiliaryType_aux2 k :=
  ![distinguishedElement k, distinguishedElement_aux1 k]

/-- An algebra homomorphism between the displayed algebras. -/
noncomputable def algHom_aux5 (k : Type*) [CommRing k] :
    RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k →ₐ[k] AuxiliaryType_aux2 k :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (distinguishedElement_aux4 k), by
      rintro a b ⟨rfl, rfl⟩
      simp only [RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraGeneratorLeft, RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraGeneratorRight, map_mul, map_add, map_one,
        FreeAlgebra.lift_ι_apply, distinguishedElement_aux4, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact displayed_eq_aux1 k⟩

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux9 (k : Type*) [CommRing k] :
    algHom_aux5 k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k) = distinguishedElement k := by
  rw [algHom_aux5, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.fromFreeAlgebra, RingQuot.liftAlgHom_mkAlgHom_apply,
    RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraGeneratorLeft, FreeAlgebra.lift_ι_apply]
  simp [distinguishedElement_aux4]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux10 (k : Type*) [CommRing k] :
    algHom_aux5 k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) = distinguishedElement_aux1 k := by
  rw [algHom_aux5, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator, RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.fromFreeAlgebra, RingQuot.liftAlgHom_mkAlgHom_apply,
    RepresentationTheory.FreeAlgebra.PolynomialOperators.freeAlgebraGeneratorRight, FreeAlgebra.lift_ι_apply]
  simp [distinguishedElement_aux4]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux11 (k : Type*) [CommRing k] :
    algHom_aux6 k (distinguishedElement k) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := by
  rw [distinguishedElement, map_apply_aux13, algHom, UniversalEnvelopingAlgebra.lift_ι_apply, lieHom_apply_aux1,
    distinguishedElement_aux5]
  simp

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux12 (k : Type*) [CommRing k] :
    algHom_aux6 k (distinguishedElement_aux1 k) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k := by
  rw [distinguishedElement_aux1, map_apply_aux13, algHom, UniversalEnvelopingAlgebra.lift_ι_apply, lieHom_apply_aux1,
    distinguishedElement_aux6]
  simp

/-- The composite of the displayed algebra homomorphisms is the stated map. -/
theorem algHom_comp_eq_aux3 (k : Type*) [CommRing k] :
    (algHom_aux6 k).comp (algHom_aux5 k) = AlgHom.id k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k) := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  fin_cases i
  · change algHom_aux6 k (algHom_aux5 k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k)) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k
    rw [map_apply_aux9, map_apply_aux11]
  · change algHom_aux6 k (algHom_aux5 k (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k)) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k
    rw [map_apply_aux10, map_apply_aux12]

/-- The composite of the displayed algebra homomorphisms is the stated map. -/
theorem algHom_comp_eq_aux2 (k : Type*) [CommRing k] :
    (algHom_aux5 k).comp (algHom_aux6 k) = AlgHom.id k (AuxiliaryType_aux2 k) := by

  have key : ((algHom_aux5 k).comp (algHom_aux6 k)).comp ((ringCon k).mkₐ k) = (ringCon k).mkₐ k := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro d
    change algHom_aux5 k (algHom_aux6 k ((ringCon k).mkₐ k (ι k d))) = (ringCon k).mkₐ k (ι k d)
    rw [map_apply_aux13, algHom, UniversalEnvelopingAlgebra.lift_ι_apply, lieHom_apply_aux1,
      map_add, map_add, map_smul, map_smul, map_smul, map_one, map_apply_aux9, map_apply_aux10]

    have hd : ι k d = d.1 • ι k (distinguishedElement_aux5 : AuxiliaryType k) + d.2.1 • ι k distinguishedElement_aux6 + d.2.2 • ι k distinguishedElement_aux2 := by
      rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add]
      congr 1
      apply AuxiliaryType.ext <;> simp [distinguishedElement_aux5, distinguishedElement_aux6, distinguishedElement_aux2]
    have hcbar : (ringCon k).mkₐ k (ι k (distinguishedElement_aux2 : AuxiliaryType k)) = 1 := by
      change (ringCon k).mk' (ι k (distinguishedElement_aux2 : AuxiliaryType k)) = 1
      rw [map_apply_aux14]; exact map_one _
    rw [hd, map_add, map_add, map_smul, map_smul, map_smul, hcbar, ← distinguishedElement, ← distinguishedElement_aux1]
  apply AlgHom.ext
  intro q
  obtain ⟨a, rfl⟩ := (ringCon k).mkₐ_surjective (α := k) q
  exact AlgHom.congr_fun key a

/-- An algebra equivalence between the displayed algebras. -/
@[source_ref "Chapter2/Example2.9.13" (role := supporting)]
noncomputable def algEquiv_aux1 (k : Type*) [CommRing k] :
    AuxiliaryType_aux2 k ≃ₐ[k] RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra k :=
  AlgEquiv.ofAlgHom (algHom_aux6 k) (algHom_aux5 k) (algHom_comp_eq_aux3 k) (algHom_comp_eq_aux2 k)

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux5 (k : Type*) [CommRing k] :
    algEquiv_aux1 k (distinguishedElement k) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k := map_apply_aux11 k

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux6 (k : Type*) [CommRing k] :
    algEquiv_aux1 k (distinguishedElement_aux1 k) = RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k := map_apply_aux12 k

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux7 (k : Type*) [CommRing k] :
    (algEquiv_aux1 k).symm (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.firstOperator k) = distinguishedElement k := map_apply_aux9 k

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux8 (k : Type*) [CommRing k] :
    (algEquiv_aux1 k).symm (RepresentationTheory.FreeAlgebra.PolynomialOperators.OperatorAlgebra.secondOperator k) = distinguishedElement_aux1 k := map_apply_aux10 k

end RepresentationTheory.LieAlgebra.ThreeGeneratorPresentations
