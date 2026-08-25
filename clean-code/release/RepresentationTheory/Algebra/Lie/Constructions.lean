/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic.NoncommRing
import RepresentationTheory.Alignment.Attribute

/-! # Constructions for Lie algebras and derivations -/

namespace RepresentationTheory.Algebra.Lie.Constructions

/-- The type obtained from a module when equipped with the zero Lie bracket. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
def AbelianLieAlgebra (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V] : Type _ := V

namespace AbelianLieAlgebra

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- The inherited additive commutative group structure. -/
instance instAddCommGroup : AddCommGroup (AbelianLieAlgebra k V) :=
  inferInstanceAs (AddCommGroup V)

/-- The module structure inherited by the zero-bracket Lie algebra. -/
instance instModule : Module k (AbelianLieAlgebra k V) := inferInstanceAs (Module k V)

/-- The zero bracket on the underlying module. -/
instance instBracket : Bracket (AbelianLieAlgebra k V) (AbelianLieAlgebra k V) :=
  ⟨fun _ _ => 0⟩

/-- The bracket of any two elements of the zero-bracket Lie algebra is zero. -/
@[simp] theorem bracket_eq_zero (x y : AbelianLieAlgebra k V) : ⁅x, y⁆ = 0 := rfl

/-- The Lie ring structure on a module with zero bracket. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
instance instLieRing : LieRing (AbelianLieAlgebra k V) where
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := rfl
  leibniz_lie _ _ _ := by simp

/-- The Lie algebra structure on a module with zero bracket. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
instance instLieAlgebra : LieAlgebra k (AbelianLieAlgebra k V) where
  lie_smul _ _ _ := by simp

/-- The zero-bracket Lie algebra is Lie-abelian. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
instance isLieAbelian : IsLieAbelian (AbelianLieAlgebra k V) :=
  ⟨fun x y => bracket_eq_zero x y⟩

end AbelianLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A Lie ring structure on an algebra. -/
@[reducible, source_ref "Chapter2/Example2.9.2" (role := supporting)]
def commutatorLieRing (k : Type*) [CommRing k]
    (A : Type*) [Ring A] [Algebra k A] :
    LieRing A := inferInstance

/-- The Lie algebra structure on module endomorphisms. -/
@[reducible, source_ref "Chapter2/Example2.9.2" (role := supporting)]
def endomorphismLieAlgebra (k : Type*) [CommRing k] (V : Type*)
    [AddCommGroup V] [Module k V] :
    LieAlgebra k (Module.End k V) := inferInstance

/-- The induced Lie algebra structure on the carrier of a Lie subalgebra. -/
@[reducible, source_ref "Chapter2/Example2.9.2" (role := supporting)]
def subalgebraLieAlgebra (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
    (U : LieSubalgebra k A) :
    LieAlgebra k U := inferInstance

section Derivation

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

/-- A predicate on linear endomorphisms of an algebra. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
def IsDerivation (D : Module.End k A) : Prop :=
  ∀ a b : A, D (a * b) = D a * b + a * D b

/-- A Lie subalgebra of the linear endomorphisms of an algebra. -/
@[source_ref "Chapter2/Example2.9.2" (role := primary)]
def derivationLieSubalgebra : LieSubalgebra k (Module.End k A) where
  carrier := {D | IsDerivation k A D}
  add_mem' {D₁ D₂} h₁ h₂ a b := by
    simp only [LinearMap.add_apply, h₁ a b, h₂ a b, add_mul, mul_add]; abel
  zero_mem' a b := by simp
  smul_mem' c D h a b := by
    simp only [LinearMap.smul_apply, h a b, smul_add, smul_mul_assoc, mul_smul_comm]
  lie_mem' {D₁ D₂} h₁ h₂ a b := by
    change ⁅D₁, D₂⁆ (a * b) = ⁅D₁, D₂⁆ a * b + a * ⁅D₁, D₂⁆ b
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      h₁ a b, h₂ a b, map_add, h₁ (D₂ a) b, h₁ a (D₂ b), h₂ (D₁ a) b, h₂ a (D₁ b)]
    noncomm_ring

variable {k A}

/-- Characterization of membership in the derivation subalgebra by the product rule. -/
@[simp, source_ref "Chapter2/Example2.9.2" (role := primary)]
theorem mem_derivationLieSubalgebra_iff {D : Module.End k A} :
    D ∈ derivationLieSubalgebra k A ↔ ∀ a b : A, D (a * b) = D a * b + a * D b :=
  Iff.rfl

/-- Every element of the derivation subalgebra satisfies the product rule. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
theorem derivationLieSubalgebra.leibniz (D : derivationLieSubalgebra k A) (a b : A) :
    (D : Module.End k A) (a * b) =
      (D : Module.End k A) a * b + a * (D : Module.End k A) b :=
  D.2 a b

/-- The bracket of two derivation-subalgebra elements is the difference of their composites. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
theorem derivationLieSubalgebra.bracket_apply
    (D₁ D₂ : derivationLieSubalgebra k A) (a : A) :
    ((⁅D₁, D₂⁆ : derivationLieSubalgebra k A) : Module.End k A) a =
      (D₁ : Module.End k A) ((D₂ : Module.End k A) a) -
        (D₂ : Module.End k A) ((D₁ : Module.End k A) a) := by
  simp [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket]

/-- A map from an algebra to a subalgebra of its endomorphisms. -/
def derivationLieSubalgebra.innerDerivation (x : A) : derivationLieSubalgebra k A :=
  ⟨LinearMap.mulLeft k x - LinearMap.mulRight k x, fun a b => by
    simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      sub_mul, mul_sub, mul_assoc]
    noncomm_ring⟩

/-- An inner derivation evaluates to the difference of left and right products. -/
@[simp] theorem derivationLieSubalgebra.innerDerivation_apply (x a : A) :
    ((derivationLieSubalgebra.innerDerivation x : derivationLieSubalgebra k A) :
      Module.End k A) a = x * a - a * x :=
  rfl

example : LieAlgebra k (derivationLieSubalgebra k A) := inferInstance

example : LieRing (derivationLieSubalgebra k A) := inferInstance

end Derivation

section CommBridge

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

/-- The linear map underlying a derivation satisfies the designated predicate. -/
theorem derivation_isDerivation (D : Derivation k A A) :
    IsDerivation k A (D : A →ₗ[k] A) := fun a b => by
  rw [Derivation.coeFn_coe, D.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b (D a), add_comm]

/-- A Lie equivalence from derivations to a subalgebra of endomorphisms. -/
@[source_ref "Chapter2/Example2.9.2" (role := supporting)]
def derivationLieEquiv : Derivation k A A ≃ₗ⁅k⁆ derivationLieSubalgebra k A where
  toFun D := ⟨(D : A →ₗ[k] A), derivation_isDerivation k A D⟩
  invFun D := Derivation.mk' (D : Module.End k A) fun a b => by
    rw [derivationLieSubalgebra.leibniz D a b, smul_eq_mul, smul_eq_mul, mul_comm b, add_comm]
  left_inv D := by ext a; rfl
  right_inv D := by ext a; rfl
  map_add' D₁ D₂ := rfl
  map_smul' c D := rfl
  map_lie' {D₁ D₂} := by
    ext a
    rw [derivationLieSubalgebra.bracket_apply]
    exact Derivation.commutator_apply a

end CommBridge

end RepresentationTheory.Algebra.Lie.Constructions
