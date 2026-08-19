/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.FreeAlgebra
import RepresentationTheory.Alignment.Attribute

/-! # A presentation of the special linear Lie algebra -/

namespace RepresentationTheory.LieAlgebra.SpecialLinearPresentation

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type*} [CommRing k]

/-- A construction with the displayed domain and codomain. -/
def CoordinateTriple (k : Type*) [CommRing k] : Type _ := k × k × k

/-- Provides the indicated AddCommGroup structure on the specified type. -/
instance instAddCommGroup : AddCommGroup (CoordinateTriple k) := inferInstanceAs (AddCommGroup (k × k × k))

/-- Provides the indicated Module structure on the specified type. -/
instance instModule : Module k (CoordinateTriple k) := inferInstanceAs (Module k (k × k × k))

/-- Two coordinate triples are equal when their three coordinates agree. -/
@[ext] theorem CoordinateTriple.ext {a b : CoordinateTriple k}
    (h1 : a.1 = b.1) (h2 : a.2.1 = b.2.1) (h3 : a.2.2 = b.2.2) : a = b :=
  Prod.ext h1 (Prod.ext h2 h3)

/-- The first coordinate of a sum is the sum of the corresponding coordinates. -/
@[simp] theorem fst_add (a b : CoordinateTriple k) : (a + b).1 = a.1 + b.1 := rfl
/-- The indicated nested coordinate of a sum is the sum of the corresponding coordinates. -/
@[simp] theorem snd_fst_add (a b : CoordinateTriple k) : (a + b).2.1 = a.2.1 + b.2.1 := rfl
/-- The third coordinate of a sum is the sum of the corresponding coordinates. -/
@[simp] theorem snd_snd_add (a b : CoordinateTriple k) : (a + b).2.2 = a.2.2 + b.2.2 := rfl
/-- The first coordinate of zero is zero. -/
@[simp] theorem fst_zero : (0 : CoordinateTriple k).1 = 0 := rfl
/-- The indicated nested coordinate of zero is zero. -/
@[simp] theorem snd_fst_zero : (0 : CoordinateTriple k).2.1 = 0 := rfl
/-- The third coordinate of zero is zero. -/
@[simp] theorem snd_snd_zero : (0 : CoordinateTriple k).2.2 = 0 := rfl
/-- The first coordinate of a scalar multiple is the scalar multiple of that coordinate. -/
@[simp] theorem fst_smul (t : k) (a : CoordinateTriple k) : (t • a).1 = t • a.1 := rfl
/-- The middle coordinate of a scalar multiple is the scalar multiple of the middle coordinate. -/
@[simp] theorem snd_fst_smul (t : k) (a : CoordinateTriple k) : (t • a).2.1 = t • a.2.1 := rfl
/-- The third coordinate of a scalar multiple is the scalar multiple of that coordinate. -/
@[simp] theorem snd_snd_smul (t : k) (a : CoordinateTriple k) : (t • a).2.2 = t • a.2.2 := rfl
/-- The first coordinate of a negation is the negation of that coordinate. -/
@[simp] theorem fst_neg (a : CoordinateTriple k) : (-a).1 = -a.1 := rfl
/-- The middle coordinate of a negation is the negation of the middle coordinate. -/
@[simp] theorem snd_fst_neg (a : CoordinateTriple k) : (-a).2.1 = -a.2.1 := rfl
/-- The third coordinate of a negation is the negation of that coordinate. -/
@[simp] theorem snd_snd_neg (a : CoordinateTriple k) : (-a).2.2 = -a.2.2 := rfl

/-- Provides the indicated Bracket structure on the specified type. -/
instance instBracket : Bracket (CoordinateTriple k) (CoordinateTriple k) where
  bracket u v :=
    (2 * (u.2.2 * v.1 - u.1 * v.2.2),
     -(2 * (u.2.2 * v.2.1 - u.2.1 * v.2.2)),
     u.1 * v.2.1 - u.2.1 * v.1)

/-- The bracket of two coordinate triples is given by the displayed coordinate formula. -/
@[simp]
theorem bracket_apply (u v : CoordinateTriple k) :
    ⁅u, v⁆ =
      (2 * (u.2.2 * v.1 - u.1 * v.2.2),
       -(2 * (u.2.2 * v.2.1 - u.2.1 * v.2.2)),
       u.1 * v.2.1 - u.2.1 * v.1) := rfl

/-- Provides the indicated LieRing structure on the specified type. -/
instance instLieRing : LieRing (CoordinateTriple k) where
  add_lie x y z := by
    apply CoordinateTriple.ext <;>
      simp only [bracket_apply, fst_add, snd_fst_add, snd_snd_add] <;> ring
  lie_add x y z := by
    apply CoordinateTriple.ext <;>
      simp only [bracket_apply, fst_add, snd_fst_add, snd_snd_add] <;> ring
  lie_self x := by
    apply CoordinateTriple.ext <;> simp [bracket_apply] <;> ring
  leibniz_lie x y z := by
    apply CoordinateTriple.ext <;>
      simp only [bracket_apply, fst_add, snd_fst_add, snd_snd_add] <;> ring

/-- Provides the indicated LieAlgebra structure on the specified type. -/
instance instLieAlgebra : LieAlgebra k (CoordinateTriple k) where
  lie_smul t x y := by
    apply CoordinateTriple.ext <;>
      simp only [bracket_apply, fst_smul, snd_fst_smul, snd_snd_smul, smul_eq_mul] <;> ring

/-- A construction with the displayed domain and codomain. -/
def basis0 : CoordinateTriple k := ((1 : k), (0 : k), (0 : k))

/-- A construction with the displayed domain and codomain. -/
def basis1 : CoordinateTriple k := ((0 : k), (1 : k), (0 : k))

/-- A construction with the displayed domain and codomain. -/
def basis2 : CoordinateTriple k := ((0 : k), (0 : k), (1 : k))

/-- The bracket of the indicated distinguished basis elements has the displayed value. -/
@[simp, source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived4" (role := supporting)]
theorem bracket_basis2_basis0 : ⁅(basis2 : CoordinateTriple k), (basis0 : CoordinateTriple k)⁆ = (2 : k) • (basis0 : CoordinateTriple k) := by
  apply CoordinateTriple.ext <;> simp [bracket_apply, basis0, basis2]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[simp, source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived4" (role := supporting)]
theorem auxiliary_fact_aux7 : ⁅(basis2 : CoordinateTriple k), (basis1 : CoordinateTriple k)⁆ = (-2 : k) • (basis1 : CoordinateTriple k) := by
  apply CoordinateTriple.ext <;> simp [bracket_apply, basis1, basis2]

/-- The bracket of the indicated distinguished basis elements has the displayed value. -/
@[simp, source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived4" (role := supporting)]
theorem bracket_basis0_basis1 : ⁅(basis0 : CoordinateTriple k), (basis1 : CoordinateTriple k)⁆ = (basis2 : CoordinateTriple k) := by
  apply CoordinateTriple.ext <;> simp [bracket_apply, basis0, basis1, basis2]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[source_ref "Chapter2/Example2.9.12" (role := supporting)]
theorem auxiliary_fact_aux5 (k : Type*) [CommRing k] :
    (ι k (basis2 : CoordinateTriple k)) * (ι k basis0) - (ι k basis0) * (ι k basis2) = (2 : k) • ι k basis0 ∧
    (ι k (basis2 : CoordinateTriple k)) * (ι k basis1) - (ι k basis1) * (ι k basis2) = (-2 : k) • ι k basis1 ∧
    (ι k (basis0 : CoordinateTriple k)) * (ι k basis1) - (ι k basis1) * (ι k basis0) = ι k basis2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, bracket_basis2_basis0, map_smul]
  · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, auxiliary_fact_aux7, map_smul]
  · rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, bracket_basis0_basis1]

/-- Every coordinate triple is the corresponding linear combination of the three distinguished basis elements. -/
theorem basis_decomposition (x : CoordinateTriple k) :
    x = x.1 • (basis0 : CoordinateTriple k) + x.2.1 • (basis1 : CoordinateTriple k) + x.2.2 • (basis2 : CoordinateTriple k) := by
  apply CoordinateTriple.ext <;> simp [basis0, basis1, basis2]

/-- The range of the canonical Lie map generates the universal enveloping algebra. -/
theorem adjoin_lieRange_eq_top (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L] :
    Algebra.adjoin k (Set.range (ι k : L → UniversalEnvelopingAlgebra k L)) = ⊤ := by
  have hsurj : (mkAlgHom k L).range = ⊤ :=
    (AlgHom.range_eq_top _).mpr (RingCon.mkₐ_surjective _)
  calc Algebra.adjoin k (Set.range (ι k : L → UniversalEnvelopingAlgebra k L))
      = Algebra.adjoin k (mkAlgHom k L '' Set.range (TensorAlgebra.ι k)) := by
        rw [← Set.range_comp]; rfl
    _ = (Algebra.adjoin k (Set.range (TensorAlgebra.ι k (M := L)))).map (mkAlgHom k L) :=
        (AlgHom.map_adjoin _ _).symm
    _ = (⊤ : Subalgebra k (TensorAlgebra k L)).map (mkAlgHom k L) := by
        rw [TensorAlgebra.adjoin_range_ι]
    _ = ⊤ := by rw [Algebra.map_top, hsurj]

/-- The three distinguished images generate the universal enveloping algebra. -/
theorem adjoin_basis_eq_top (k : Type*) [CommRing k] :
    Algebra.adjoin k {ι k (basis0 : CoordinateTriple k), ι k (basis1 : CoordinateTriple k), ι k (basis2 : CoordinateTriple k)} = ⊤ := by
  rw [eq_top_iff, ← adjoin_lieRange_eq_top k (CoordinateTriple k), Algebra.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  rw [basis_decomposition x, map_add, map_add, map_smul, map_smul, map_smul]
  set S := Algebra.adjoin k {ι k (basis0 : CoordinateTriple k), ι k (basis1 : CoordinateTriple k), ι k (basis2 : CoordinateTriple k)} with hS
  have he : ι k (basis0 : CoordinateTriple k) ∈ S := Algebra.subset_adjoin (by simp)
  have hf : ι k (basis1 : CoordinateTriple k) ∈ S := Algebra.subset_adjoin (by simp)
  have hh : ι k (basis2 : CoordinateTriple k) ∈ S := Algebra.subset_adjoin (by simp)
  exact add_mem (add_mem (Subalgebra.smul_mem _ he _) (Subalgebra.smul_mem _ hf _))
    (Subalgebra.smul_mem _ hh _)

section AuxiliaryConstruction

variable {A : Type*} [Ring A] [Algebra k A]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
def auxiliaryConstruction (X Y Z : A) (hX : Z * X - X * Z = (2 : k) • X)
    (hY : Z * Y - Y * Z = (-2 : k) • Y) (hZ : X * Y - Y * X = Z) : CoordinateTriple k →ₗ⁅k⁆ A where
  toFun u := u.1 • X + u.2.1 • Y + u.2.2 • Z
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
        (a₁ • X + b₁ • Y + d₁ • Z) * (a₂ • X + b₂ • Y + d₂ • Z) -
            (a₂ • X + b₂ • Y + d₂ • Z) * (a₁ • X + b₁ • Y + d₁ • Z) =
          (a₁ * b₂ - b₁ * a₂) • (X * Y - Y * X) + (d₁ * a₂ - a₁ * d₂) • (Z * X - X * Z) +
            (d₁ * b₂ - b₁ * d₂) • (Z * Y - Y * Z) := by
      simp only [add_mul, mul_add, smul_mul_smul_comm, smul_sub]
      module
    simp only [LieRing.of_associative_ring_bracket, bracket_apply]
    rw [expand, hX, hY, hZ]
    module

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[simp] theorem auxiliary_fact (X Y Z : A) (hX : Z * X - X * Z = (2 : k) • X)
    (hY : Z * Y - Y * Z = (-2 : k) • Y) (hZ : X * Y - Y * X = Z) (u : CoordinateTriple k) :
    auxiliaryConstruction X Y Z hX hY hZ u = u.1 • X + u.2.1 • Y + u.2.2 • Z := rfl

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[simp] theorem auxiliary_fact_aux1 (X Y Z : A) (hX : Z * X - X * Z = (2 : k) • X)
    (hY : Z * Y - Y * Z = (-2 : k) • Y) (hZ : X * Y - Y * X = Z) :
    auxiliaryConstruction X Y Z hX hY hZ (basis0 : CoordinateTriple k) = X := by simp [basis0]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[simp] theorem auxiliary_fact_aux2 (X Y Z : A) (hX : Z * X - X * Z = (2 : k) • X)
    (hY : Z * Y - Y * Z = (-2 : k) • Y) (hZ : X * Y - Y * X = Z) :
    auxiliaryConstruction X Y Z hX hY hZ (basis1 : CoordinateTriple k) = Y := by simp [basis1]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[simp] theorem auxiliary_fact_aux3 (X Y Z : A) (hX : Z * X - X * Z = (2 : k) • X)
    (hY : Z * Y - Y * Z = (-2 : k) • Y) (hZ : X * Y - Y * X = Z) :
    auxiliaryConstruction X Y Z hX hY hZ (basis2 : CoordinateTriple k) = Z := by simp [basis2]

end AuxiliaryConstruction

section PresentedAlgebraConstruction

/-- A binary relation on the free algebra over three generators. -/
inductive FreeAlgebraRelation (k : Type*) [CommRing k] :
    FreeAlgebra k (Fin 3) → FreeAlgebra k (Fin 3) → Prop
  | he : FreeAlgebraRelation k
      (FreeAlgebra.ι k 2 * FreeAlgebra.ι k 0 - FreeAlgebra.ι k 0 * FreeAlgebra.ι k 2)
      ((2 : k) • FreeAlgebra.ι k 0)
  | hf : FreeAlgebraRelation k
      (FreeAlgebra.ι k 2 * FreeAlgebra.ι k 1 - FreeAlgebra.ι k 1 * FreeAlgebra.ι k 2)
      ((-2 : k) • FreeAlgebra.ι k 1)
  | ef : FreeAlgebraRelation k
      (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 1 - FreeAlgebra.ι k 1 * FreeAlgebra.ι k 0)
      (FreeAlgebra.ι k 2)

/-- A ring congruence on the displayed free algebra. -/
def ringCon (k : Type*) [CommRing k] : RingCon (FreeAlgebra k (Fin 3)) :=
  ringConGen (FreeAlgebraRelation k)

/-- A construction with the displayed domain and codomain. -/
def PresentedAlgebra (k : Type*) [CommRing k] : Type _ := (ringCon k).Quotient

/-- Provides the indicated Ring structure on the specified type. -/
instance instRing : Ring (PresentedAlgebra k) := inferInstanceAs (Ring (ringCon k).Quotient)

/-- Provides the indicated Algebra structure on the specified type. -/
instance instAlgebra : Algebra k (PresentedAlgebra k) := inferInstanceAs (Algebra k (ringCon k).Quotient)

/-- An algebra homomorphism between the displayed algebras. -/
def algHom (k : Type*) [CommRing k] : FreeAlgebra k (Fin 3) →ₐ[k] PresentedAlgebra k :=
  RingCon.mkₐ k (ringCon k)

/-- A distinguished value of the displayed type. -/
def distinguishedElement_aux1 (k : Type*) [CommRing k] (i : Fin 3) : PresentedAlgebra k :=
  algHom k (FreeAlgebra.ι k i)

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux1 (k : Type*) [CommRing k] :
    distinguishedElement_aux1 k 2 * distinguishedElement_aux1 k 0 - distinguishedElement_aux1 k 0 * distinguishedElement_aux1 k 2 = (2 : k) • distinguishedElement_aux1 k 0 := by
  have hrel := Quotient.sound <| RingCon.le_ringConGen _ _ (FreeAlgebraRelation.he (k := k))
  change algHom k
      (FreeAlgebra.ι k 2 * FreeAlgebra.ι k 0 - FreeAlgebra.ι k 0 * FreeAlgebra.ι k 2) =
    algHom k ((2 : k) • FreeAlgebra.ι k 0)
  exact hrel

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
theorem auxiliary_fact_aux4 (k : Type*) [CommRing k] :
    distinguishedElement_aux1 k 2 * distinguishedElement_aux1 k 1 - distinguishedElement_aux1 k 1 * distinguishedElement_aux1 k 2 = (-2 : k) • distinguishedElement_aux1 k 1 := by
  have hrel := Quotient.sound <| RingCon.le_ringConGen _ _ (FreeAlgebraRelation.hf (k := k))
  change algHom k
      (FreeAlgebra.ι k 2 * FreeAlgebra.ι k 1 - FreeAlgebra.ι k 1 * FreeAlgebra.ι k 2) =
    algHom k ((-2 : k) • FreeAlgebra.ι k 1)
  exact hrel

/-- The two displayed expressions are equal. -/
theorem displayed_eq (k : Type*) [CommRing k] :
    distinguishedElement_aux1 k 0 * distinguishedElement_aux1 k 1 - distinguishedElement_aux1 k 1 * distinguishedElement_aux1 k 0 = distinguishedElement_aux1 k 2 := by
  have hrel := Quotient.sound <| RingCon.le_ringConGen _ _ (FreeAlgebraRelation.ef (k := k))
  change algHom k
      (FreeAlgebra.ι k 0 * FreeAlgebra.ι k 1 - FreeAlgebra.ι k 1 * FreeAlgebra.ι k 0) =
    algHom k (FreeAlgebra.ι k 2)
  exact hrel

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
def lieHom_aux1 (k : Type*) [CommRing k] : CoordinateTriple k →ₗ⁅k⁆ PresentedAlgebra k :=
  auxiliaryConstruction (distinguishedElement_aux1 k 0) (distinguishedElement_aux1 k 1) (distinguishedElement_aux1 k 2) (displayed_eq_aux1 k) (auxiliary_fact_aux4 k) (displayed_eq k)

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux4 (k : Type*) [CommRing k] :
    UniversalEnvelopingAlgebra k (CoordinateTriple k) →ₐ[k] PresentedAlgebra k :=
  UniversalEnvelopingAlgebra.lift k (lieHom_aux1 k)

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux2 (k : Type*) [CommRing k] :
    FreeAlgebra k (Fin 3) →ₐ[k] UniversalEnvelopingAlgebra k (CoordinateTriple k) :=
  FreeAlgebra.lift k ![ι k (basis0 : CoordinateTriple k), ι k (basis1 : CoordinateTriple k), ι k (basis2 : CoordinateTriple k)]

/-- The free-generator algebra homomorphism sends each generator to the canonical image of the corresponding distinguished coordinate. -/
@[simp] theorem freeGenerator_map (k : Type*) [CommRing k] (i : Fin 3) :
    algHom_aux2 k (FreeAlgebra.ι k i) = ι k (![(basis0 : CoordinateTriple k), basis1, basis2] i) := by
  simp only [algHom_aux2, FreeAlgebra.lift_ι_apply]
  fin_cases i <;> simp

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply (k : Type*) [CommRing k] :
    ∀ ⦃a b : FreeAlgebra k (Fin 3)⦄, FreeAlgebraRelation k a b → algHom_aux2 k a = algHom_aux2 k b := by
  rintro a b hab
  obtain _ | _ | _ := hab
  · simpa using (auxiliary_fact_aux5 k).1
  · simpa using (auxiliary_fact_aux5 k).2.1
  · simpa using (auxiliary_fact_aux5 k).2.2

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux1 (k : Type*) [CommRing k] :
    PresentedAlgebra k →ₐ[k] UniversalEnvelopingAlgebra k (CoordinateTriple k) :=
  RingCon.liftₐ (ringCon k) (algHom_aux2 k) <| by
    grw [ringCon, RingCon.ringConGen_le]
    exact map_apply k

/-- The algebra homomorphism sends the canonical image of a coordinate triple to its corresponding linear combination of the three indexed distinguished elements. -/
@[simp] theorem algHom_iota_apply (k : Type*) [CommRing k] (x : CoordinateTriple k) :
    algHom_aux4 k (ι k x) = x.1 • distinguishedElement_aux1 k 0 + x.2.1 • distinguishedElement_aux1 k 1 + x.2.2 • distinguishedElement_aux1 k 2 :=
  UniversalEnvelopingAlgebra.lift_ι_apply k (lieHom_aux1 k) x

/-- The algebra homomorphism sends each indexed distinguished element to the canonical image of the corresponding coordinate basis element. -/
@[simp] theorem algHom_distinguishedElement_apply (k : Type*) [CommRing k] (i : Fin 3) :
    algHom_aux1 k (distinguishedElement_aux1 k i) = ι k (![(basis0 : CoordinateTriple k), basis1, basis2] i) := by
  change RingCon.liftₐ (ringCon k) (algHom_aux2 k) _
      (RingCon.mkₐ k (ringCon k) (FreeAlgebra.ι k i)) = _
  change algHom_aux2 k (FreeAlgebra.ι k i) = _
  exact freeGenerator_map k i

/-- The composite of the displayed algebra homomorphisms is the stated map. -/
theorem algHom_comp_eq (k : Type*) [CommRing k] :
    (algHom_aux1 k).comp (algHom_aux4 k) = AlgHom.id k (UniversalEnvelopingAlgebra k (CoordinateTriple k)) := by
  ext x
  simp only [AlgHom.coe_comp, LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom,
    AlgHom.coe_id, id_eq, algHom_iota_apply, map_add, map_smul, algHom_distinguishedElement_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add]
  exact congrArg _ (basis_decomposition x).symm

/-- The composite of the displayed algebra homomorphisms is the stated map. -/
theorem algHom_comp_eq_aux1 (k : Type*) [CommRing k] :
    (algHom_aux4 k).comp (algHom_aux1 k) = AlgHom.id k (PresentedAlgebra k) := by
  apply RingCon.Quotient.hom_extₐ
  ext i
  fin_cases i
  · change algHom_aux4 k (algHom_aux1 k (distinguishedElement_aux1 k 0)) = distinguishedElement_aux1 k 0
    simp [algHom_aux4, lieHom_aux1, basis0, basis1, basis2]
  · change algHom_aux4 k (algHom_aux1 k (distinguishedElement_aux1 k 1)) = distinguishedElement_aux1 k 1
    simp [algHom_aux4, lieHom_aux1, basis0, basis1, basis2]
  · change algHom_aux4 k (algHom_aux1 k (distinguishedElement_aux1 k 2)) = distinguishedElement_aux1 k 2
    simp [algHom_aux4, lieHom_aux1, basis0, basis1, basis2]

/-- An algebra equivalence between the displayed algebras. -/
@[source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived9" (role := supporting)]
def algEquiv (k : Type*) [CommRing k] :
    PresentedAlgebra k ≃ₐ[k] UniversalEnvelopingAlgebra k (CoordinateTriple k) :=
  AlgEquiv.ofAlgHom (algHom_aux1 k) (algHom_aux4 k) (algHom_comp_eq k) (algHom_comp_eq_aux1 k)

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux3 (k : Type*) [CommRing k] :
    algEquiv k (distinguishedElement_aux1 k 0) = ι k (basis0 : CoordinateTriple k) := by simp [algEquiv]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux1 (k : Type*) [CommRing k] :
    algEquiv k (distinguishedElement_aux1 k 1) = ι k (basis1 : CoordinateTriple k) := by simp [algEquiv]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux2 (k : Type*) [CommRing k] :
    algEquiv k (distinguishedElement_aux1 k 2) = ι k (basis2 : CoordinateTriple k) := by simp [algEquiv]

end PresentedAlgebraConstruction

section MatrixRealization

open LieAlgebra.SpecialLinear

/-- The matrix specified by the displayed parameters. -/
def matrix (u : CoordinateTriple k) : Matrix (Fin 2) (Fin 2) k := !![u.2.2, u.1; u.2.1, -u.2.2]

/-- The displayed matrix belongs to the special linear Lie algebra. -/
theorem mem_specialLinear (u : CoordinateTriple k) : matrix u ∈ sl (Fin 2) k := by
  change Matrix.trace (matrix u) = 0
  simp [matrix, Matrix.trace_fin_two]

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux2 (M : sl (Fin 2) k) : M.val 0 0 + M.val 1 1 = 0 := by
  have hM : Matrix.trace M.val = 0 := M.2
  simpa [Matrix.trace_fin_two] using hM

/-- A Lie algebra equivalence between the displayed Lie algebras. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived3" (role := supporting)]
def lieEquiv (k : Type*) [CommRing k] : CoordinateTriple k ≃ₗ⁅k⁆ sl (Fin 2) k where
  toFun u := ⟨matrix u, mem_specialLinear u⟩
  map_add' u v := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matrix]; ring
  map_smul' t u := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matrix]
  map_lie' {u v} := by
    apply Subtype.ext
    rw [sl_bracket]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix, bracket_apply] <;> ring
  invFun M := (M.val 0 1, M.val 1 0, M.val 0 0)
  left_inv u := by apply CoordinateTriple.ext <;> simp [matrix]
  right_inv M := by
    apply Subtype.ext
    have h11 : M.val 1 1 = -M.val 0 0 := by linear_combination displayed_eq_aux2 M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix, h11]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux4 (u : CoordinateTriple k) :
    (lieEquiv k u : Matrix (Fin 2) (Fin 2) k) = matrix u := rfl

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq (u v : CoordinateTriple k) : lieEquiv k ⁅u, v⁆ = ⁅lieEquiv k u, lieEquiv k v⁆ :=
  LieHom.map_lie (lieEquiv k).toLieHom u v

/-- The displayed matrices are equal. -/
@[simp, source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived3" (role := supporting)]
theorem matrix_eq_aux1 (k : Type*) [CommRing k] :
    (lieEquiv k (basis0 : CoordinateTriple k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, basis0]

/-- The displayed matrices are equal. -/
@[simp, source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived3" (role := supporting)]
theorem matrix_eq_aux2 (k : Type*) [CommRing k] :
    (lieEquiv k (basis1 : CoordinateTriple k) : Matrix (Fin 2) (Fin 2) k) = !![0, 0; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, basis1]

/-- An auxiliary declaration whose formal expression is unavailable in displayed form. -/
@[simp, source_ref "Chapter2/Discussion_concrete_Lie_examples/Derived3" (role := supporting)]
theorem auxiliary_fact_aux6 (k : Type*) [CommRing k] :
    (lieEquiv k (basis2 : CoordinateTriple k) : Matrix (Fin 2) (Fin 2) k) = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, basis2]

/-- The specified element is nonzero. -/
theorem distinguished_ne_zero (k : Type*) [CommRing k] [Nontrivial k] :
    lieEquiv k (basis2 : CoordinateTriple k) ≠ 0 := by
  intro hzero
  have hval : ((lieEquiv k (basis2 : CoordinateTriple k)) : Matrix (Fin 2) (Fin 2) k) = 0 := by rw [hzero]; rfl
  rw [auxiliary_fact_aux6] at hval
  have hent := congrFun (congrFun hval 0) 0
  simp at hent

/-- The three displayed elements form an sl2-triple. -/
theorem isSl2Triple (k : Type*) [CommRing k] [Nontrivial k] :
    IsSl2Triple (lieEquiv k (basis2 : CoordinateTriple k)) (lieEquiv k (basis0 : CoordinateTriple k)) (lieEquiv k (basis1 : CoordinateTriple k)) where
  h_ne_zero := distinguished_ne_zero k
  lie_e_f := by rw [← bracket_eq, bracket_basis0_basis1]
  lie_h_e_nsmul := by
    rw [← bracket_eq, bracket_basis2_basis0]
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, basis0]
  lie_h_f_nsmul := by
    rw [← bracket_eq, auxiliary_fact_aux7]
    apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [matrix, basis1]

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
def lieHom (k : Type*) [CommRing k] : CoordinateTriple k →ₗ⁅k⁆ Matrix (Fin 2) (Fin 2) k :=
  auxiliaryConstruction !![0, 1; 0, 0] !![0, 0; 1, 0] !![1, 0; 0, -1]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp; ring)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp; ring)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)

/-- An algebra homomorphism between the displayed algebras. -/
def algHom_aux3 (k : Type*) [CommRing k] :
    UniversalEnvelopingAlgebra k (CoordinateTriple k) →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  UniversalEnvelopingAlgebra.lift k (lieHom k)

/-- The specified element is nonzero. -/
theorem distinguished_ne_zero_aux1 (k : Type*) [CommRing k] [Nontrivial k] : ι k (basis0 : CoordinateTriple k) ≠ 0 := by
  intro hzero
  have himg := congrArg (algHom_aux3 k) hzero
  rw [map_zero, algHom_aux3, UniversalEnvelopingAlgebra.lift_ι_apply, lieHom, auxiliary_fact_aux1] at himg
  have : (1 : k) = 0 := by simpa using congrFun (congrFun himg 0) 1
  exact one_ne_zero this

/-- The displayed type is nontrivial. -/
instance nontrivial_aux1 (k : Type*) [CommRing k] [Nontrivial k] :
    Nontrivial (UniversalEnvelopingAlgebra k (CoordinateTriple k)) :=
  nontrivial_of_ne _ _ (distinguished_ne_zero_aux1 k)

/-- The displayed type is nontrivial. -/
instance nontrivial (k : Type*) [CommRing k] [Nontrivial k] :
    Nontrivial (PresentedAlgebra k) :=
  (algEquiv k).toRingEquiv.nontrivial

end MatrixRealization

end RepresentationTheory.LieAlgebra.SpecialLinearPresentation

attribute [source_ref "Chapter2/Example2.9.12" (role := primary)]
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.lieEquiv
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.matrix_eq_aux1
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.matrix_eq_aux2
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.nontrivial

attribute [source_ref "Chapter2/Example2.9.12" (role := supporting)]
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.auxiliary_fact_aux6
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.PresentedAlgebra
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.algEquiv
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux1
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux2
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux3
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.distinguished_ne_zero_aux1
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.nontrivial_aux1

attribute [source_ref "Chapter2/Discussion_2.1_irreducible_indecomposable/Derived8"
    (role := supporting)]
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.algEquiv
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux1
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux2
  RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux3
