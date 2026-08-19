/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import RepresentationTheory.Alignment.Attribute

/-! # Modular representations of a two-dimensional matrix Lie algebra -/

namespace RepresentationTheory.LieAlgebra.ModularRepresentations

open scoped Matrix
open Module (finrank)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]

/-- A Lie subalgebra of two-by-two matrices over the displayed field. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
noncomputable def matrixLieSubalgebra : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieSubalgebra.lieSpan k _ {Matrix.single 0 0 1, Matrix.single 0 1 1}

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement : matrixLieSubalgebra k :=
  ⟨Matrix.single 0 0 1, LieSubalgebra.subset_lieSpan (by left; rfl)⟩

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux1 : matrixLieSubalgebra k :=
  ⟨Matrix.single 0 1 1, LieSubalgebra.subset_lieSpan (by right; rfl)⟩

private abbrev matrixUnit00 : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 0 1

private abbrev matrixUnit01 : Matrix (Fin 2) (Fin 2) k := Matrix.single 0 1 1

private theorem bracket_matrixUnit00_matrixUnit01 : ⁅matrixUnit00 k, matrixUnit01 k⁆ = matrixUnit01 k := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [matrixUnit00, matrixUnit01, LieRing.of_associative_ring_bracket, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h]

private theorem bracket_matrixUnit01_matrixUnit00 : ⁅matrixUnit01 k, matrixUnit00 k⁆ = - matrixUnit01 k := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [matrixUnit00, matrixUnit01, LieRing.of_associative_ring_bracket, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, h]

private theorem bracket_linearCombination (a b c d : k) :
    ⁅a • matrixUnit00 k + b • matrixUnit01 k, c • matrixUnit00 k + d • matrixUnit01 k⁆ = (a * d - b * c) • matrixUnit01 k := by
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, bracket_matrixUnit00_matrixUnit01 k,
    bracket_matrixUnit01_matrixUnit00 k, smul_zero, add_zero, zero_add, smul_neg]
  module

/-- The bracket of the displayed elements has the stated value. -/
@[source_ref "Chapter2/Discussion_concrete_Lie_examples_continued/Derived3" (role := supporting),
  source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem bracket_eq : ⁅distinguishedElement k, distinguishedElement_aux1 k⁆ = distinguishedElement_aux1 k := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  exact bracket_matrixUnit00_matrixUnit01 k

private noncomputable def matrixUnitSpan : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  { Submodule.span k {matrixUnit00 k, matrixUnit01 k} with
    lie_mem' := by
      intro x y hx hy
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [bracket_linearCombination]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)) }

private theorem matrixLieSubalgebra_le_matrixUnitSpan : matrixLieSubalgebra k ≤ matrixUnitSpan k :=
  LieSubalgebra.lieSpan_le.mpr (by
    intro z hz
    rcases hz with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp))

private theorem coe_mem_matrixUnitSpan (x : matrixLieSubalgebra k) :
    (x : Matrix (Fin 2) (Fin 2) k) ∈ Submodule.span k {matrixUnit00 k, matrixUnit01 k} :=
  matrixLieSubalgebra_le_matrixUnitSpan k x.2

private theorem bracket_mem_span_secondGenerator (x y : matrixLieSubalgebra k) : ⁅x, y⁆ ∈ Submodule.span k {distinguishedElement_aux1 k} := by
  obtain ⟨a, b, hx⟩ := Submodule.mem_span_pair.mp (coe_mem_matrixUnitSpan k x)
  obtain ⟨c, d, hy⟩ := Submodule.mem_span_pair.mp (coe_mem_matrixUnitSpan k y)
  rw [Submodule.mem_span_singleton]
  refine ⟨a * d - b * c, ?_⟩
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, ← hx, ← hy, bracket_linearCombination]
  rfl

/-- The two displayed expressions are equal. -/
theorem displayed_eq (Z : matrixLieSubalgebra k) :
    Z = (Z : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement k
      + (Z : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux1 k := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (coe_mem_matrixUnitSpan k Z)
  have h00 : (Z : Matrix (Fin 2) (Fin 2) k) 0 0 = a := by
    rw [← hab]; simp [matrixUnit00, matrixUnit01]
  have h01 : (Z : Matrix (Fin 2) (Fin 2) k) 0 1 = b := by
    rw [← hab]; simp [matrixUnit00, matrixUnit01]
  rw [h00, h01]
  apply Subtype.ext
  rw [AddMemClass.coe_add, SetLike.val_smul, SetLike.val_smul]
  exact hab.symm

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux6 (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] (Z : matrixLieSubalgebra k) (m : M) :
    ⁅Z, m⁆ = (Z : Matrix (Fin 2) (Fin 2) k) 0 0 • ⁅distinguishedElement k, m⁆
      + (Z : Matrix (Fin 2) (Fin 2) k) 0 1 • ⁅distinguishedElement_aux1 k, m⁆ := by
  conv_lhs => rw [displayed_eq k Z]
  rw [add_lie, smul_lie, smul_lie]

/-- The submodule specified by the displayed construction. -/
def submodule (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M]
    [LieModule k (matrixLieSubalgebra k) M] (N : Submodule k M)
    (hX : ∀ m ∈ N, ⁅distinguishedElement k, m⁆ ∈ N) (hY : ∀ m ∈ N, ⁅distinguishedElement_aux1 k, m⁆ ∈ N) : LieSubmodule k (matrixLieSubalgebra k) M where
  __ := N
  lie_mem {Z m} hm := by
    have hm' : m ∈ N := hm
    rw [bracket_eq_aux6 k M Z m]
    exact N.add_mem (N.smul_mem _ (hX m hm')) (N.smul_mem _ (hY m hm'))

/-- The displayed submodules are equal. -/
@[simp] theorem submodule_eq (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] (N : Submodule k M)
    (hX : ∀ m ∈ N, ⁅distinguishedElement k, m⁆ ∈ N) (hY : ∀ m ∈ N, ⁅distinguishedElement_aux1 k, m⁆ ∈ N) :
    (submodule k M N hX hY : Submodule k M) = N := rfl

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux1 (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] [LieModule.IsIrreducible k (matrixLieSubalgebra k) M]
    (N : Submodule k M) (hX : ∀ m ∈ N, ⁅distinguishedElement k, m⁆ ∈ N) (hY : ∀ m ∈ N, ⁅distinguishedElement_aux1 k, m⁆ ∈ N)
    {m₀ : M} (hm₀N : m₀ ∈ N) (hm₀ : m₀ ≠ 0) : N = ⊤ := by
  have hne : submodule k M N hX hY ≠ ⊥ := fun h => hm₀ (by
    have : m₀ ∈ submodule k M N hX hY := hm₀N
    rwa [h, LieSubmodule.mem_bot] at this)
  have := (IsSimpleOrder.eq_bot_or_eq_top (submodule k M N hX hY)).resolve_left hne
  rwa [← LieSubmodule.toSubmodule_eq_top, submodule_eq] at this

/-- An equivalence between the displayed Lie modules. -/
def lieModuleEquiv_aux1 {M N : Type*} [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M]
    [LieModule k (matrixLieSubalgebra k) M] [AddCommGroup N] [Module k N] [LieRingModule (matrixLieSubalgebra k) N]
    [LieModule k (matrixLieSubalgebra k) N] (e : M ≃ₗ[k] N) (hX : ∀ m : M, e ⁅distinguishedElement k, m⁆ = ⁅distinguishedElement k, e m⁆)
    (hY : ∀ m : M, e ⁅distinguishedElement_aux1 k, m⁆ = ⁅distinguishedElement_aux1 k, e m⁆) : M ≃ₗ⁅k, matrixLieSubalgebra k⁆ N where
  __ := e
  map_lie' {Z m} := by
    change e ⁅Z, m⁆ = ⁅Z, e m⁆
    rw [bracket_eq_aux6 k M Z m, map_add, map_smul, map_smul, hX, hY,
      bracket_eq_aux6 k N Z (e m)]

/-- A Lie-module equivalence intertwines every power of the action of the displayed Lie element. -/
theorem lieModuleEquiv_map_pow_action {M N : Type*} [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M]
    [LieModule k (matrixLieSubalgebra k) M] [AddCommGroup N] [Module k N] [LieRingModule (matrixLieSubalgebra k) N]
    [LieModule k (matrixLieSubalgebra k) N] (φ : M ≃ₗ⁅k,matrixLieSubalgebra k⁆ N) (Z : matrixLieSubalgebra k) (n : ℕ) (m : M) :
    φ (((LieModule.toEnd k (matrixLieSubalgebra k) M Z) ^ n) m)
      = ((LieModule.toEnd k (matrixLieSubalgebra k) N Z) ^ n) (φ m) := by
  induction n generalizing m with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih,
      LieModule.toEnd_apply_apply, LieModule.toEnd_apply_apply]
    exact congrArg _ (LieModuleHom.map_lie φ.toLieModuleHom Z m)

private theorem derivedSeries_one_le_span_secondGenerator (x : matrixLieSubalgebra k)
    (hx : x ∈ LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 1) : x ∈ Submodule.span k {distinguishedElement_aux1 k} := by
  have hx' : x ∈ (LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 1 : Submodule k (matrixLieSubalgebra k)) := hx
  rw [LieAlgebra.coe_derivedSeries_one_eq] at hx'
  refine Submodule.span_le.mpr ?_ hx'
  rintro z ⟨a, b, rfl⟩
  exact bracket_mem_span_secondGenerator k a b

/-- The displayed matrix Lie algebra is solvable. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
instance matrixLieSubalgebra_isSolvable : LieAlgebra.IsSolvable (matrixLieSubalgebra k) := by
  refine LieAlgebra.IsSolvable.mk (?_ : LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 2 = ⊥)
  have key : ⁅LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 1, LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 1⁆ = ⊥ := by
    rw [LieSubmodule.lie_eq_bot_iff]
    intro x hx m hm
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp (derivedSeries_one_le_span_secondGenerator k x hx)
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp (derivedSeries_one_le_span_secondGenerator k m hm)
    simp [smul_lie, lie_smul]
  have e2 : LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 2
      = ⁅LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 1, LieAlgebra.derivedSeries k (matrixLieSubalgebra k) 1⁆ := rfl
  rw [e2]; exact key

/-- The finite rank of the displayed module has the stated value. -/
theorem finrank_eq [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] :
    Module.finrank k M = 1 := by
  have : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (matrixLieSubalgebra k) M
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable k (matrixLieSubalgebra k) M
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace M χ)
  rw [LieModule.mem_weightSpace] at hv
  have hv0 : v ≠ 0 := fun h => hv0 (Subtype.ext h)
  let N : LieSubmodule k (matrixLieSubalgebra k) M :=
    { __ := Submodule.span k {v}
      lie_mem := fun {x m} hm => by
        have hm' : m ∈ Submodule.span k {v} := hm
        rw [Submodule.mem_span_singleton] at hm'
        obtain ⟨c, rfl⟩ := hm'
        exact Submodule.mem_span_singleton.mpr ⟨c * χ x, by rw [lie_smul, hv x, smul_smul]⟩ }
  have hN : N ≠ ⊥ := fun h => hv0 (by
    have : v ∈ N := Submodule.mem_span_singleton_self v
    rwa [h, LieSubmodule.mem_bot] at this)
  have hspan : Submodule.span k {v} = ⊤ := by
    have : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
    rwa [← LieSubmodule.toSubmodule_eq_top] at this
  rw [← finrank_top k M, ← hspan, finrank_span_singleton hv0]

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux2 [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] (m : M) :
    ⁅distinguishedElement_aux1 k, m⁆ = 0 := by
  have d1 : Module.finrank k M = 1 := finrank_eq k M
  obtain ⟨cX, hcX, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 (LieModule.toEnd k (matrixLieSubalgebra k) M (distinguishedElement k))
  obtain ⟨cY, hcY, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 (LieModule.toEnd k (matrixLieSubalgebra k) M (distinguishedElement_aux1 k))
  have eX : ∀ w : M, ⁅distinguishedElement k, w⁆ = cX • w := fun w => by
    have := LinearMap.congr_fun hcX w; simpa [LieModule.toEnd_apply_apply] using this
  have eY : ∀ w : M, ⁅distinguishedElement_aux1 k, w⁆ = cY • w := fun w => by
    have := LinearMap.congr_fun hcY w; simpa [LieModule.toEnd_apply_apply] using this
  rw [← bracket_eq k, lie_lie, eY, eX, eX, eY, smul_smul, smul_smul, mul_comm cX cY, sub_self]

private theorem bracket_coe_apply_zero_zero (A B : matrixLieSubalgebra k) :
    (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
  obtain ⟨a, b, hx⟩ := Submodule.mem_span_pair.mp (coe_mem_matrixUnitSpan k A)
  obtain ⟨c, d, hy⟩ := Submodule.mem_span_pair.mp (coe_mem_matrixUnitSpan k B)
  have hbr : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) = (a * d - b * c) • matrixUnit01 k := by
    rw [LieSubalgebra.coe_bracket, ← hx, ← hy, bracket_linearCombination]
  rw [hbr]
  simp [matrixUnit01, Matrix.smul_apply]

/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
def AuxiliaryType_aux1 (_μ : k) : Type _ := k

/-- Provides the indicated AddCommGroup structure on the specified type. -/
instance instAddCommGroup_aux1 (μ : k) : AddCommGroup (AuxiliaryType_aux1 k μ) := inferInstanceAs (AddCommGroup k)
/-- Provides the indicated Module structure on the specified type. -/
instance instModule_aux1 (μ : k) : Module k (AuxiliaryType_aux1 k μ) := inferInstanceAs (Module k k)

/-- The displayed module is finite-dimensional. -/
instance finiteDimensional_aux1 (μ : k) : FiniteDimensional k (AuxiliaryType_aux1 k μ) := inferInstanceAs (FiniteDimensional k k)

/-- The displayed type is nontrivial. -/
instance nontrivial_aux1 (μ : k) : Nontrivial (AuxiliaryType_aux1 k μ) := inferInstanceAs (Nontrivial k)

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux2 (μ : k) : matrixLieSubalgebra k →ₗ⁅k⁆ Module.End k (AuxiliaryType_aux1 k μ) where
  toFun A := ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
  map_add' A B := by
    change (((A + B : matrixLieSubalgebra k) : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
          + ((B : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
    rw [AddMemClass.coe_add, Matrix.add_apply, add_mul, add_smul]
  map_smul' c A := by
    change (((c • A : matrixLieSubalgebra k) : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = (RingHom.id k) c • ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
    rw [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul, mul_assoc]
  map_lie' := by
    intro A B
    have h00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := bracket_coe_apply_zero_zero k A B
    change ((↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id
        = ⁅((↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id,
            ((↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id⁆
    rw [h00, zero_mul, zero_smul]
    simp only [smul_lie, lie_smul, lie_self, smul_zero]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux10 (μ : k) (A : matrixLieSubalgebra k) :
    lieHom_aux2 k μ A = ((A : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • LinearMap.id := rfl

/-- Provides the indicated LieRingModule structure on the specified type. -/
noncomputable instance instLieRingModule_aux1 (μ : k) : LieRingModule (matrixLieSubalgebra k) (AuxiliaryType_aux1 k μ) :=
  LieRingModule.compLieHom (AuxiliaryType_aux1 k μ) (lieHom_aux2 k μ)

/-- The displayed one-dimensional family carries the indicated Lie-module structure. -/
noncomputable instance lieModule_oneDimensional (μ : k) : LieModule k (matrixLieSubalgebra k) (AuxiliaryType_aux1 k μ) :=
  LieModule.compLieHom (AuxiliaryType_aux1 k μ) (lieHom_aux2 k μ)

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux8 (μ : k) (x : AuxiliaryType_aux1 k μ) : (⁅distinguishedElement k, x⁆ : AuxiliaryType_aux1 k μ) = μ • x := by
  have h : (⁅distinguishedElement k, x⁆ : AuxiliaryType_aux1 k μ) = lieHom_aux2 k μ (distinguishedElement k) x := rfl
  have hX : (↑(distinguishedElement k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by simp [distinguishedElement]
  rw [h, map_apply_aux10, hX, one_mul, LinearMap.smul_apply, LinearMap.id_apply]

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux9 (μ : k) (x : AuxiliaryType_aux1 k μ) : (⁅distinguishedElement_aux1 k, x⁆ : AuxiliaryType_aux1 k μ) = 0 := by
  have h : (⁅distinguishedElement_aux1 k, x⁆ : AuxiliaryType_aux1 k μ) = lieHom_aux2 k μ (distinguishedElement_aux1 k) x := rfl
  have hY : (↑(distinguishedElement_aux1 k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by simp [distinguishedElement_aux1]
  rw [h, map_apply_aux10, hY, zero_mul, zero_smul, LinearMap.zero_apply]

/-- Each module in the displayed one-dimensional family is irreducible. -/
theorem oneDimensional_isIrreducible (μ : k) : LieModule.IsIrreducible k (matrixLieSubalgebra k) (AuxiliaryType_aux1 k μ) := by
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  rw [ne_eq, LieSubmodule.eq_bot_iff] at hN
  push Not at hN
  obtain ⟨v, hvN, hv0⟩ := hN
  rw [← LieSubmodule.toSubmodule_eq_top]
  have hle : Submodule.span k {v} ≤ (N : Submodule k (AuxiliaryType_aux1 k μ)) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr hvN
  have hspan : Submodule.span k {v} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hv0]
    exact (Module.finrank_self k).symm
  exact top_unique (hspan ▸ hle)

/-- Distinct scalar parameters give inequivalent modules in the one-dimensional family. -/
theorem not_nonempty_lieModuleEquiv_of_ne {μ₁ μ₂ : k} (h : μ₁ ≠ μ₂) :
    ¬ Nonempty (AuxiliaryType_aux1 k μ₁ ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType_aux1 k μ₂) := by
  rintro ⟨φ⟩
  apply h
  obtain ⟨m, hm⟩ := exists_ne (0 : AuxiliaryType_aux1 k μ₁)
  have hφm : φ m ≠ 0 := fun hh => hm (φ.injective (by rw [hh, map_zero]))
  have hint : φ ⁅distinguishedElement k, m⁆ = ⁅distinguishedElement k, φ m⁆ := LieModuleHom.map_lie φ.toLieModuleHom (distinguishedElement k) m
  rw [bracket_eq_aux8, bracket_eq_aux8, map_smul] at hint
  have hz : (μ₁ - μ₂) • φ m = 0 := by rw [sub_smul, hint, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 hφm

/-- There is a unique scalar by which the displayed Lie element acts on the irreducible finite-dimensional module. -/
theorem existsUnique_scalarAction [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] :
    ∃! μ : k, ∀ m : M, ⁅distinguishedElement k, m⁆ = μ • m := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (matrixLieSubalgebra k) M
  have d1 : Module.finrank k M = 1 := finrank_eq k M
  obtain ⟨cX, hcX, -⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one d1 (LieModule.toEnd k (matrixLieSubalgebra k) M (distinguishedElement k))
  have eX : ∀ w : M, ⁅distinguishedElement k, w⁆ = cX • w := fun w => by
    have := LinearMap.congr_fun hcX w; simpa [LieModule.toEnd_apply_apply] using this
  refine ⟨cX, eX, fun μ hμ => ?_⟩
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have hz : (cX - μ) • m = 0 := by rw [sub_smul, ← eX, hμ, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 hm

/-- A linear equivalence between the displayed modules. -/
def linearEquiv (μ : k) : k ≃ₗ[k] AuxiliaryType_aux1 k μ where
  toFun c := c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := c
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux7 (μ : k) (Z : matrixLieSubalgebra k) (x : AuxiliaryType_aux1 k μ) :
    (⁅Z, x⁆ : AuxiliaryType_aux1 k μ) = ((Z : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • x := by
  have h : (⁅Z, x⁆ : AuxiliaryType_aux1 k μ) = lieHom_aux2 k μ Z x := rfl
  rw [h, map_apply_aux10, LinearMap.smul_apply, LinearMap.id_apply]

/-- The stated scalar actions and finite-rank-one hypothesis yield an equivalence with the displayed one-dimensional module. -/
theorem nonempty_lieModuleEquiv_oneDimensional (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M]
    [LieModule k (matrixLieSubalgebra k) M] {μ : k} (hX : ∀ m : M, ⁅distinguishedElement k, m⁆ = μ • m)
    (hY : ∀ m : M, ⁅distinguishedElement_aux1 k, m⁆ = 0) (hdim : Module.finrank k M = 1) :
    Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType_aux1 k μ) := by
  have hlie : ∀ (Z : matrixLieSubalgebra k) (m : M),
      ⁅Z, m⁆ = ((Z : Matrix (Fin 2) (Fin 2) k) 0 0 * μ) • m := fun Z m => by
    rw [bracket_eq_aux6 k M Z m, hX, hY, smul_zero, add_zero, smul_smul]
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := k) (by rw [hdim]; norm_num)
  haveI : FiniteDimensional k M := Module.finite_of_finrank_pos (R := k) (by rw [hdim]; norm_num)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hinj : Function.Injective (LinearMap.toSpanSingleton k M m₀) := by
    intro c d hcd
    have h0 : (c - d) • m₀ = 0 := by
      rw [sub_smul, ← LinearMap.toSpanSingleton_apply, ← LinearMap.toSpanSingleton_apply, hcd,
        sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hm₀
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k M m₀) := by
    have hspan : Submodule.span k {m₀} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_singleton hm₀, hdim]
    intro m
    have hm : m ∈ Submodule.span k {m₀} := hspan ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
    exact ⟨c, LinearMap.toSpanSingleton_apply k M m₀ c⟩
  let e : M ≃ₗ[k] AuxiliaryType_aux1 k μ :=
    (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm.trans (linearEquiv k μ)
  refine ⟨{ e with map_lie' := ?_ }⟩
  intro Z m
  change e ⁅Z, m⁆ = ⁅Z, e m⁆
  rw [hlie, map_smul, bracket_eq_aux7]

/-- In characteristic zero, there is a unique scalar parameter for an equivalence with the displayed one-dimensional module. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem existsUnique_equiv_oneDimensional [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] :
    ∃! μ : k, Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType_aux1 k μ) := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_scalarAction k M
  obtain ⟨φ⟩ := nonempty_lieModuleEquiv_oneDimensional k M hμ (bracket_eq_aux2 k M)
    (finrank_eq k M)
  refine ⟨μ, ⟨φ⟩, ?_⟩
  rintro ν ⟨ψ⟩
  by_contra hne
  exact not_nonempty_lieModuleEquiv_of_ne k (Ne.symm hne) ⟨φ.symm.trans ψ⟩

section CharP

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A natural number known to be prime is nonzero. -/
instance prime_neZero : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux5 : ZMod p →+* k := ZMod.castHom (dvd_refl p) k

/-- The displayed map is injective. -/
theorem map_injective : Function.Injective (distinguishedElement_aux5 k p) := by
  change Function.Injective ⇑(ZMod.castHom (dvd_refl p) k)
  exact ZMod.castHom_injective k

variable {k p}

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux8 (n : ℕ) : distinguishedElement_aux5 k p (n : ZMod p) = (n : k) := map_natCast _ n

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux9 (i : ZMod p) : distinguishedElement_aux5 k p i = (i.val : k) := by
  have h : ((i.val : ℕ) : ZMod p) = i := ZMod.natCast_zmod_val i
  calc distinguishedElement_aux5 k p i = distinguishedElement_aux5 k p ((i.val : ℕ) : ZMod p) := by rw [h]
    _ = (i.val : k) := map_apply_aux8 i.val

variable (k p)

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux2 (a : k) : Module.End k (ZMod p → k) where
  toFun v i := (a + distinguishedElement_aux5 k p i) * v i
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux6 : Module.End k (ZMod p → k) :=
  LinearMap.funLeft k k (fun i => i - 1)

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux3 (γ : kˣ) : Module.End k (ZMod p → k) := (γ : k) • distinguishedElement_aux6 k p

variable {k p}

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply (a : k) (v : ZMod p → k) (i : ZMod p) :
    distinguishedElement_aux2 k p a v i = (a + distinguishedElement_aux5 k p i) * v i := rfl

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux14 (v : ZMod p → k) (i : ZMod p) : distinguishedElement_aux6 k p v i = v (i - 1) := rfl

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux6 (γ : kˣ) (v : ZMod p → k) (i : ZMod p) :
    distinguishedElement_aux3 k p γ v i = (γ : k) * v (i - 1) := rfl

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux16 (j : ZMod p) (c : k) :
    distinguishedElement_aux6 k p (Pi.single j c) = Pi.single (j + 1) c := by
  funext m
  rw [map_apply_aux14, Pi.single_apply, Pi.single_apply]
  congr 1
  simp [sub_eq_iff_eq_add]

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux7 (γ : kˣ) (j : ZMod p) (c : k) :
    distinguishedElement_aux3 k p γ (Pi.single j c) = Pi.single (j + 1) ((γ : k) * c) := by
  funext m
  rw [map_apply_aux6, Pi.single_apply, Pi.single_apply]
  by_cases hm : m = j + 1
  · have h1 : m - 1 = j := by rw [hm]; ring
    rw [if_pos h1, if_pos hm]
  · have h1 : ¬ (m - 1 = j) := fun h => hm (by rw [← h]; ring)
    rw [if_neg h1, if_neg hm, mul_zero]

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux1 (a : k) (γ : kˣ) :
    ⁅distinguishedElement_aux2 k p a, distinguishedElement_aux3 k p γ⁆ = distinguishedElement_aux3 k p γ := by
  refine LinearMap.ext fun v => funext fun i => ?_
  have h : distinguishedElement_aux5 k p i - distinguishedElement_aux5 k p (i - 1) = 1 := by rw [← map_sub, sub_sub_cancel, map_one]
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    map_apply, map_apply_aux6]
  linear_combination ((γ : k) * v (i - 1)) * h

variable (k p)

/-- A Lie subalgebra of two-by-two matrices over the displayed field. -/
def matrixLieSubalgebra_aux1 : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) where
  carrier := {A | A 1 0 = 0 ∧ A 1 1 = 0}
  add_mem' {a b} ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c a ha := ⟨by simp [ha.1], by simp [ha.2]⟩
  lie_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, ha.1, ha.2, hb.1, hb.2, zero_mul, mul_zero, add_zero, sub_zero, and_self]

/-- Both displayed properties hold. -/
theorem property_and (A : matrixLieSubalgebra k) :
    (↑A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧ (↑A : Matrix (Fin 2) (Fin 2) k) 1 1 = 0 := by
  have hg : matrixLieSubalgebra k = LieSubalgebra.lieSpan k (Matrix (Fin 2) (Fin 2) k)
      {Matrix.single 0 0 1, Matrix.single 0 1 1} := rfl
  have hle : matrixLieSubalgebra k ≤ matrixLieSubalgebra_aux1 k := by
    rw [hg, LieSubalgebra.lieSpan_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
  exact hle A.2

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom (γ : kˣ) (a : k) : matrixLieSubalgebra k →ₗ⁅k⁆ Module.End k (ZMod p → k) where
  toFun A := (A : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement_aux2 k p a
    + (A : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux3 k p γ
  map_add' A B := by
    simp only [AddMemClass.coe_add, Matrix.add_apply, add_smul]; abel
  map_smul' c A := by
    simp only [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
  map_lie' := by
    intro A B
    obtain ⟨hA0, hA1⟩ := property_and k A
    obtain ⟨hB0, hB1⟩ := property_and k B
    have hds : ⁅distinguishedElement_aux3 k p γ, distinguishedElement_aux2 k p a⁆ = -distinguishedElement_aux3 k p γ := by
      rw [← lie_skew, bracket_eq_aux1]

    have smul_lie' : ∀ (c : k) (u v : Module.End k (ZMod p → k)),
        ⁅c • u, v⁆ = c • ⁅u, v⁆ := fun c u v => smul_lie c u v
    have lie_smul' : ∀ (c : k) (u v : Module.End k (ZMod p → k)),
        ⁅u, c • v⁆ = c • ⁅u, v⁆ := fun c u v => lie_smul c u v
    have hbr : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k)
        = (↑A : Matrix (Fin 2) (Fin 2) k) * (↑B : Matrix (Fin 2) (Fin 2) k)
          - (↑B : Matrix (Fin 2) (Fin 2) k) * (↑A : Matrix (Fin 2) (Fin 2) k) := by
      rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    have e00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA0, hB0, mul_zero,
        add_zero]
      ring
    have e01 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 =
        (↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑B : Matrix (Fin 2) (Fin 2) k) 0 1
          - (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA1, hB1, mul_zero,
        add_zero]
    change (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement_aux2 k p a
        + (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux3 k p γ
      = ⁅(↑A : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement_aux2 k p a
          + (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux3 k p γ,
        (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement_aux2 k p a
          + (↑B : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux3 k p γ⁆
    rw [e00, e01]
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero, add_zero, zero_add,
      bracket_eq_aux1, hds, smul_neg, zero_smul]
    module

/-- The displayed single-entry matrix identity holds. -/
theorem matrixSingle_eq : (↑(distinguishedElement k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 0 1 := rfl

/-- The displayed single-entry matrix identity holds. -/
theorem matrixSingle_eq_aux1 : (↑(distinguishedElement_aux1 k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 1 1 := rfl

variable {k p}

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux4 (γ : kˣ) (a : k) : lieHom k p γ a (distinguishedElement k) = distinguishedElement_aux2 k p a := by
  have h0 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    simp
  have h1 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    simp
  change (↑(distinguishedElement k) : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement_aux2 k p a
      + (↑(distinguishedElement k) : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux3 k p γ = distinguishedElement_aux2 k p a
  rw [matrixSingle_eq, h0, h1, one_smul, zero_smul, add_zero]

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux5 (γ : kˣ) (a : k) : lieHom k p γ a (distinguishedElement_aux1 k) = distinguishedElement_aux3 k p γ := by
  have h0 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    simp
  have h1 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
    simp
  change (↑(distinguishedElement_aux1 k) : Matrix (Fin 2) (Fin 2) k) 0 0 • distinguishedElement_aux2 k p a
      + (↑(distinguishedElement_aux1 k) : Matrix (Fin 2) (Fin 2) k) 0 1 • distinguishedElement_aux3 k p γ = distinguishedElement_aux3 k p γ
  rw [matrixSingle_eq_aux1, h0, h1, zero_smul, one_smul, zero_add]

variable (k p)

/-- A type-valued construction determined by the displayed parameters. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
def AuxiliaryType (_γ : kˣ) (_a : k) : Type _ := ZMod p → k

/-- Provides the indicated AddCommGroup structure on the specified type. -/
instance instAddCommGroup (γ : kˣ) (a : k) : AddCommGroup (AuxiliaryType k p γ a) :=
  inferInstanceAs (AddCommGroup (ZMod p → k))

/-- Provides the indicated Module structure on the specified type. -/
instance instModule (γ : kˣ) (a : k) : Module k (AuxiliaryType k p γ a) := inferInstanceAs (Module k (ZMod p → k))

/-- The displayed module is finite-dimensional. -/
instance finiteDimensional (γ : kˣ) (a : k) : FiniteDimensional k (AuxiliaryType k p γ a) :=
  inferInstanceAs (FiniteDimensional k (ZMod p → k))

/-- The displayed type is nontrivial. -/
instance nontrivial (γ : kˣ) (a : k) : Nontrivial (AuxiliaryType k p γ a) := inferInstanceAs (Nontrivial (ZMod p → k))

/-- A Lie algebra homomorphism between the displayed Lie algebras. -/
noncomputable def lieHom_aux1 (γ : kˣ) (a : k) : matrixLieSubalgebra k →ₗ⁅k⁆ Module.End k (AuxiliaryType k p γ a) :=
  lieHom k p γ a

variable {k p}

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux2 (γ : kˣ) (a : k) : lieHom_aux1 k p γ a (distinguishedElement k) = distinguishedElement_aux2 k p a := map_apply_aux4 γ a

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux3 (γ : kˣ) (a : k) : lieHom_aux1 k p γ a (distinguishedElement_aux1 k) = distinguishedElement_aux3 k p γ := map_apply_aux5 γ a

variable (k p)

/-- Provides the indicated LieRingModule structure on the specified type. -/
noncomputable instance instLieRingModule (γ : kˣ) (a : k) : LieRingModule (matrixLieSubalgebra k) (AuxiliaryType k p γ a) :=
  LieRingModule.compLieHom (AuxiliaryType k p γ a) (lieHom_aux1 k p γ a)

/-- The displayed modular family carries the indicated Lie-module structure. -/
noncomputable instance lieModule_modularFamily (γ : kˣ) (a : k) : LieModule k (matrixLieSubalgebra k) (AuxiliaryType k p γ a) :=
  LieModule.compLieHom (AuxiliaryType k p γ a) (lieHom_aux1 k p γ a)

variable {k p}

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux3 (γ : kˣ) (a : k) (v : AuxiliaryType k p γ a) :
    (⁅distinguishedElement k, v⁆ : AuxiliaryType k p γ a) = distinguishedElement_aux2 k p a v := by
  have h : (⁅distinguishedElement k, v⁆ : AuxiliaryType k p γ a) = lieHom_aux1 k p γ a (distinguishedElement k) v := rfl
  rw [h, map_apply_aux2]
  exact rfl

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux4 (γ : kˣ) (a : k) (v : AuxiliaryType k p γ a) :
    (⁅distinguishedElement_aux1 k, v⁆ : AuxiliaryType k p γ a) = distinguishedElement_aux3 k p γ v := by
  have h : (⁅distinguishedElement_aux1 k, v⁆ : AuxiliaryType k p γ a) = lieHom_aux1 k p γ a (distinguishedElement_aux1 k) v := rfl
  rw [h, map_apply_aux3]
  exact rfl

omit [CharP k p] in

/-- The finite rank of the displayed module has the stated value. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem finrank_eq_aux1 (γ : kˣ) (a : k) : Module.finrank k (AuxiliaryType k p γ a) = p := by
  have h : Module.finrank k (AuxiliaryType k p γ a) = Module.finrank k (ZMod p → k) := rfl
  rw [h, Module.finrank_fintype_fun_eq_card, ZMod.card p]

open scoped Classical in

/-- A distinguished value of the displayed type. -/
noncomputable def distinguishedElement_aux7 (v : ZMod p → k) : Finset (ZMod p) :=
  Finset.univ.filter fun i => v i ≠ 0

omit [CharP k p] in

/-- An index belongs to the displayed support exactly when the function is nonzero there. -/
theorem mem_support {v : ZMod p → k} {i : ZMod p} : i ∈ distinguishedElement_aux7 v ↔ v i ≠ 0 := by
  simp [distinguishedElement_aux7]

omit [Fact (Nat.Prime p)] [CharP k p] in

private theorem smul_piSingle (m : ZMod p) (c d : k) :
    c • (Pi.single m d : ZMod p → k) = Pi.single m (c * d) := by
  funext x
  rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_zero]

/-- A submodule invariant under both displayed operators is either zero or the whole module. -/
theorem invariantSubmodule_eq_bot_or_top (γ : kˣ) (a : k) (N : Submodule k (ZMod p → k))
    (hdiag : ∀ v ∈ N, distinguishedElement_aux2 k p a v ∈ N) (hshift : ∀ v ∈ N, distinguishedElement_aux3 k p γ v ∈ N) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  rcases eq_or_ne N ⊥ with hbot | hbot
  · exact Or.inl hbot
  refine Or.inr ?_

  have hone : ∀ (m : ZMod p) (c : k), c ≠ 0 → (Pi.single m c : ZMod p → k) ∈ N →
      (Pi.single m (1 : k) : ZMod p → k) ∈ N := by
    intro m c hc hmem
    have h := N.smul_mem c⁻¹ hmem
    rwa [smul_piSingle, inv_mul_cancel₀ hc] at h

  have hstep : ∀ i : ZMod p, (Pi.single i (1 : k) : ZMod p → k) ∈ N →
      (Pi.single (i + 1) (1 : k) : ZMod p → k) ∈ N := by
    intro i hi
    have h2 := hshift _ hi
    rw [map_apply_aux7, mul_one] at h2
    exact hone _ _ (Units.ne_zero γ) h2

  have horbit : ∀ i₀ : ZMod p, (Pi.single i₀ (1 : k) : ZMod p → k) ∈ N →
      ∀ m : ZMod p, (Pi.single m (1 : k) : ZMod p → k) ∈ N := by
    intro i₀ hbase m
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, m = i₀ + t :=
      ⟨(m - i₀).val, by rw [ZMod.natCast_zmod_val]; abel⟩
    induction t with
    | zero => simpa using hbase
    | succ n ih =>
      have h := hstep _ ih
      rw [Nat.cast_succ, ← add_assoc]
      exact h

  have htop : (∀ m : ZMod p, (Pi.single m (1 : k) : ZMod p → k) ∈ N) → N = ⊤ := by
    intro hall
    rw [Submodule.eq_top_iff']
    intro x
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun m _ => ?_
    have hsingle : (Pi.single m (x m) : ZMod p → k) = x m • (Pi.single m (1 : k) : ZMod p → k) := by
      rw [smul_piSingle, mul_one]
    rw [hsingle]
    exact Submodule.smul_mem _ _ (hall m)
  obtain ⟨w, hwN, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

  suffices H : ∀ (n : ℕ) (v : ZMod p → k), v ∈ N → v ≠ 0 → (distinguishedElement_aux7 v).card = n → N = ⊤ from
    H _ w hwN hw0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro v hvN hv0 hcard
    have hne : (distinguishedElement_aux7 v).Nonempty := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
      exact ⟨i, mem_support.mpr hi⟩
    by_cases hsingleton : (distinguishedElement_aux7 v).card = 1
    · obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hsingleton
      have hvi₀ : v i₀ ≠ 0 := mem_support.mp (hi₀ ▸ Finset.mem_singleton_self i₀)
      have hzero : ∀ m, m ≠ i₀ → v m = 0 := by
        intro m hm
        by_contra hvm
        have hmem : m ∈ distinguishedElement_aux7 v := mem_support.mpr hvm
        rw [hi₀, Finset.mem_singleton] at hmem
        exact hm hmem
      have hbase : (Pi.single i₀ (1 : k) : ZMod p → k) ∈ N := by
        refine hone i₀ (v i₀) hvi₀ ?_
        have hval : (Pi.single i₀ (v i₀) : ZMod p → k) = v := by
          funext m
          rw [Pi.single_apply]
          by_cases hm : m = i₀
          · rw [if_pos hm, hm]
          · rw [if_neg hm, hzero m hm]
        rwa [hval]
      exact htop (horbit i₀ hbase)
    · have h2 : 1 < (distinguishedElement_aux7 v).card := by
        have h1 := Finset.card_pos.mpr hne; omega
      obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp h2
      set w' := distinguishedElement_aux2 k p a v - (a + distinguishedElement_aux5 k p j) • v with hw'def
      have hw'N : w' ∈ N := sub_mem (hdiag v hvN) (N.smul_mem _ hvN)
      have hw'coord : ∀ m, w' m = (distinguishedElement_aux5 k p m - distinguishedElement_aux5 k p j) * v m := fun m => by
        simp only [hw'def, Pi.sub_apply, map_apply, Pi.smul_apply, smul_eq_mul]; ring
      have hlamij : distinguishedElement_aux5 k p i ≠ distinguishedElement_aux5 k p j := fun heq => hij (map_injective k p heq)
      have hw'i : w' i ≠ 0 := by
        rw [hw'coord]
        exact mul_ne_zero (sub_ne_zero.mpr hlamij) (mem_support.mp hi)
      have hw'0 : w' ≠ 0 := fun heq => hw'i (congrFun heq i)
      have hsub : distinguishedElement_aux7 w' ⊆ distinguishedElement_aux7 v := by
        intro m hm
        rw [mem_support] at hm ⊢
        intro hvm
        exact hm (by rw [hw'coord, hvm, mul_zero])
      have hjnotin : j ∉ distinguishedElement_aux7 w' := by
        rw [mem_support, not_not, hw'coord, sub_self, zero_mul]
      have hss : distinguishedElement_aux7 w' ⊂ distinguishedElement_aux7 v :=
        (Finset.ssubset_iff_of_subset hsub).mpr ⟨j, hj, hjnotin⟩
      have hlt : (distinguishedElement_aux7 w').card < n := hcard ▸ Finset.card_lt_card hss
      exact IH _ hlt w' hw'N hw'0 rfl

/-- Each module in the displayed modular family is irreducible. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem modularFamily_isIrreducible (γ : kˣ) (a : k) : LieModule.IsIrreducible k (matrixLieSubalgebra k) (AuxiliaryType k p γ a) := by
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  have hdiag : ∀ v ∈ (N : Submodule k (AuxiliaryType k p γ a)), distinguishedElement_aux2 k p a v ∈ N := by
    intro v hv
    rw [← bracket_eq_aux3 γ a v]
    exact N.lie_mem hv
  have hshift : ∀ v ∈ (N : Submodule k (AuxiliaryType k p γ a)), distinguishedElement_aux3 k p γ v ∈ N := by
    intro v hv
    rw [← bracket_eq_aux4 γ a v]
    exact N.lie_mem hv
  rcases invariantSubmodule_eq_bot_or_top γ a (N : Submodule k (AuxiliaryType k p γ a)) hdiag hshift with h | h
  · exact absurd (by rwa [← LieSubmodule.toSubmodule_eq_bot]) hN
  · rwa [← LieSubmodule.toSubmodule_eq_top]

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux15 (n : ℕ) : ∀ (v : ZMod p → k) (i : ZMod p),
    ((distinguishedElement_aux6 k p ^ n) v) i = v (i - n) := by
  induction n with
  | zero => intro v i; simp
  | succ m ih =>
    intro v i
    rw [pow_succ, Module.End.mul_apply, ih, map_apply_aux14]
    congr 1
    push_cast
    ring

omit [CharP k p] in

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux3 : distinguishedElement_aux6 k p ^ p = 1 := by
  refine LinearMap.ext fun v => funext fun i => ?_
  rw [map_apply_aux15, ZMod.natCast_self, sub_zero, Module.End.one_apply]

omit [CharP k p] in

/-- The two displayed expressions are equal. -/
theorem displayed_eq_aux2 (γ : kˣ) :
    distinguishedElement_aux3 k p γ ^ p = ((γ : k) ^ p) • (1 : Module.End k (ZMod p → k)) := by
  rw [distinguishedElement_aux3, smul_pow, displayed_eq_aux3]

/-- The `n`-th power of the displayed Lie action agrees with the `n`-th power of its defining endomorphism. -/
theorem pow_action_apply (γ : kˣ) (a : k) (n : ℕ) : ∀ v : AuxiliaryType k p γ a,
    ((LieModule.toEnd k (matrixLieSubalgebra k) (AuxiliaryType k p γ a) (distinguishedElement_aux1 k)) ^ n) v = (distinguishedElement_aux3 k p γ ^ n) v := by
  induction n with
  | zero => intro v; simp
  | succ m ih =>
    intro v
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
      LieModule.toEnd_apply_apply, bracket_eq_aux4]
    exact ih _

/-- The prime-th power of the displayed Lie action is scalar multiplication by the prime-th power of the unit parameter. -/
theorem prime_pow_action_apply (γ : kˣ) (a : k) (v : AuxiliaryType k p γ a) :
    ((LieModule.toEnd k (matrixLieSubalgebra k) (AuxiliaryType k p γ a) (distinguishedElement_aux1 k)) ^ p) v = ((γ : k) ^ p) • v := by
  have hpow : (distinguishedElement_aux3 k p γ ^ p) v =
      (((γ : k) ^ p) • (1 : Module.End k (ZMod p → k))) v :=
    congrArg (fun f : Module.End k (ZMod p → k) => f v) (displayed_eq_aux2 γ)
  exact (pow_action_apply γ a p v).trans (hpow.trans (by rfl))

/-- A distinguished value of the displayed type. -/
def distinguishedElement_aux4 (γ : kˣ) (a : k) : AuxiliaryType k p γ a := (Pi.single (0 : ZMod p) (1 : k) : ZMod p → k)

omit [CharP k p] in

/-- The specified element is nonzero. -/
theorem distinguished_ne_zero (γ : kˣ) (a : k) : distinguishedElement_aux4 γ a ≠ (0 : AuxiliaryType k p γ a) := by
  intro h
  have h0 : (Pi.single (0 : ZMod p) (1 : k) : ZMod p → k) = 0 := h
  simpa using congrFun h0 (0 : ZMod p)

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux1 (a : k) :
    distinguishedElement_aux2 k p a (Pi.single (0 : ZMod p) (1 : k)) = a • (Pi.single (0 : ZMod p) (1 : k)) := by
  funext i
  rw [map_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = 0
  · rw [if_pos hi, mul_one, mul_one, hi, map_zero, add_zero]
  · rw [if_neg hi, mul_zero, mul_zero]

/-- There exists a value satisfying the displayed conditions. -/
theorem exists_witness (a c : k) (w : ZMod p → k) (hw : w ≠ 0)
    (h : distinguishedElement_aux2 k p a w = c • w) : ∃ i : ZMod p, c = a + distinguishedElement_aux5 k p i := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine ⟨i, ?_⟩
  have h1 := congrFun h i
  rw [map_apply, Pi.smul_apply, smul_eq_mul] at h1
  exact (mul_right_cancel₀ hi h1).symm

/-- A linear equivalence between the displayed modules. -/
def linearEquiv_aux1 (n : ZMod p) : (ZMod p → k) ≃ₗ[k] (ZMod p → k) where
  toFun v i := v (i + n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w i := w (i - n)
  left_inv v := by funext i; simp
  right_inv w := by funext i; simp

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
@[simp] theorem map_apply_aux11 (n : ZMod p) (v : ZMod p → k) (i : ZMod p) :
    linearEquiv_aux1 n v i = v (i + n) := rfl

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux12 (a : k) (n : ZMod p) (v : ZMod p → k) :
    linearEquiv_aux1 n (distinguishedElement_aux2 k p a v) = distinguishedElement_aux2 k p (a + distinguishedElement_aux5 k p n) (linearEquiv_aux1 n v) := by
  funext i
  simp only [map_apply_aux11, map_apply, map_add]
  ring

omit [CharP k p] in

/-- The displayed map sends the specified input to the stated value. -/
theorem map_apply_aux13 (γ : kˣ) (n : ZMod p) (v : ZMod p → k) :
    linearEquiv_aux1 n (distinguishedElement_aux3 k p γ v) = distinguishedElement_aux3 k p γ (linearEquiv_aux1 n v) := by
  funext i
  simp only [map_apply_aux11, map_apply_aux6]
  congr 2
  ring

/-- An equivalence between the displayed Lie modules. -/
noncomputable def lieModuleEquiv (γ : kˣ) (a : k) (n : ZMod p) :
    AuxiliaryType k p γ a ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ (a + distinguishedElement_aux5 k p n) := by
  refine lieModuleEquiv_aux1 k (linearEquiv_aux1 n) (fun m => ?_) (fun m => ?_)
  · rw [bracket_eq_aux3, bracket_eq_aux3]
    exact map_apply_aux12 a n m
  · rw [bracket_eq_aux4, bracket_eq_aux4]
    exact map_apply_aux13 γ n m

/-- Two modules in the modular family are equivalent exactly when their parameters satisfy the displayed conditions. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem nonempty_lieModuleEquiv_iff (γ γ' : kˣ) (a a' : k) :
    Nonempty (AuxiliaryType k p γ a ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ' a')
      ↔ γ = γ' ∧ ∃ n : ZMod p, a' = a + distinguishedElement_aux5 k p n := by
  constructor
  · rintro ⟨φ⟩
    have hu : φ (distinguishedElement_aux4 γ a) ≠ 0 := fun h =>
      distinguished_ne_zero γ a (by simpa using congrArg φ.symm h)
    refine ⟨?_, ?_⟩
    ·
      have h1 := lieModuleEquiv_map_pow_action k φ (distinguishedElement_aux1 k) p (distinguishedElement_aux4 γ a)
      rw [prime_pow_action_apply, prime_pow_action_apply, map_smul] at h1
      have h2 : ((γ : k) ^ p - (γ' : k) ^ p) • φ (distinguishedElement_aux4 γ a) = 0 := by
        rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · refine Units.ext ?_
        refine frobenius_inj k p ?_
        rw [frobenius_def, frobenius_def]
        exact sub_eq_zero.mp h
      · exact absurd h hu
    ·

      have hXu : (⁅distinguishedElement k, distinguishedElement_aux4 γ a⁆ : AuxiliaryType k p γ a) = a • distinguishedElement_aux4 γ a := by
        rw [bracket_eq_aux3]; exact map_apply_aux1 a
      have h1 : distinguishedElement_aux2 k p a' (φ (distinguishedElement_aux4 γ a)) = a • φ (distinguishedElement_aux4 γ a) := by
        have h := LieModuleHom.map_lie φ.toLieModuleHom (distinguishedElement k) (distinguishedElement_aux4 γ a)
        rw [hXu, map_smul, bracket_eq_aux3] at h
        exact h.symm
      obtain ⟨i, hi⟩ := exists_witness a' a (φ (distinguishedElement_aux4 γ a)) hu h1
      refine ⟨-i, ?_⟩
      rw [map_neg, hi]
      ring
  · rintro ⟨rfl, n, rfl⟩
    exact ⟨lieModuleEquiv γ a n⟩

/-- Failure of the displayed parameter conditions rules out an equivalence between the two modular-family modules. -/
theorem not_nonempty_lieModuleEquiv_of_parameters {γ γ' : kˣ} {a a' : k} (h : ¬ (γ = γ' ∧ ∃ n : ZMod p, a' = a + distinguishedElement_aux5 k p n)) :
    ¬ Nonempty (AuxiliaryType k p γ a ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ' a') :=
  fun hh => h ((nonempty_lieModuleEquiv_iff γ γ' a a').mp hh)

/-- A displayed one-dimensional module is not equivalent to a module in the modular family. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem not_nonempty_lieModuleEquiv_modular (μ : k) (γ : kˣ) (a : k) :
    ¬ Nonempty (AuxiliaryType_aux1 k μ ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ a) := by
  rintro ⟨φ⟩
  have h : Module.finrank k (AuxiliaryType_aux1 k μ) = Module.finrank k (AuxiliaryType k p γ a) :=
    φ.toLinearEquiv.finrank_eq
  rw [finrank_eq_aux1] at h
  have h1 : Module.finrank k (AuxiliaryType_aux1 k μ) = 1 :=
    (Module.finrank_self k).symm ▸ rfl
  rw [h1] at h
  exact ((Fact.out : p.Prime).one_lt).ne h

variable (k p)

/-- The bracket of the displayed elements has the stated value. -/
theorem bracket_eq_aux5 (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M]
    [LieModule k (matrixLieSubalgebra k) M] (m : M) :
    ⁅distinguishedElement k, ⁅distinguishedElement_aux1 k, m⁆⁆ = ⁅distinguishedElement_aux1 k, ⁅distinguishedElement k, m⁆⁆ + ⁅distinguishedElement_aux1 k, m⁆ := by
  have h := lie_lie (distinguishedElement k) (distinguishedElement_aux1 k) m
  rw [bracket_eq] at h
  exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)

/-- If the displayed Lie element acts trivially, the module is equivalent to a displayed one-dimensional module. -/
theorem exists_equiv_oneDimensional_of_trivial_action [IsAlgClosed k] (M : Type*) [AddCommGroup M]
    [Module k M] [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] (hY : ∀ m : M, ⁅distinguishedElement_aux1 k, m⁆ = 0) :
    ∃ μ : k, Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType_aux1 k μ) := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (matrixLieSubalgebra k) M
  obtain ⟨μ, hev⟩ := Module.End.exists_eigenvalue (LieModule.toEnd k (matrixLieSubalgebra k) M (distinguishedElement k))
  obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
  have hvX : ⁅distinguishedElement k, v⁆ = μ • v := Module.End.mem_eigenspace_iff.mp hvmem
  have hspan : Submodule.span k {v} = ⊤ := by
    refine displayed_eq_aux1 k M _ (fun m hm => ?_) (fun m _ => ?_)
      (Submodule.mem_span_singleton_self v) hv0
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
      rw [lie_smul, hvX, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [hY]; exact Submodule.zero_mem _
  have hdim : Module.finrank k M = 1 := by
    rw [← finrank_top k M, ← hspan, finrank_span_singleton hv0]
  refine ⟨μ, nonempty_lieModuleEquiv_oneDimensional k M (fun m => ?_) hY hdim⟩
  have hm : m ∈ Submodule.span k {v} := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
  rw [lie_smul, hvX, smul_smul, smul_smul, mul_comm]

/-- A nontrivial action of the displayed Lie element yields an equivalence with a module in the modular family. -/
theorem exists_equiv_modularFamily_of_nontrivial_action [IsAlgClosed k] (M : Type*) [AddCommGroup M]
    [Module k M] [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] (hYne : ∃ m : M, ⁅distinguishedElement_aux1 k, m⁆ ≠ 0) :
    ∃ (γ : kˣ) (a : k), Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ a) := by
  classical
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (matrixLieSubalgebra k) M
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩

  obtain ⟨A, hAapp⟩ : ∃ A : Module.End k M, ∀ m, A m = ⁅distinguishedElement k, m⁆ :=
    ⟨LieModule.toEnd k (matrixLieSubalgebra k) M (distinguishedElement k), fun _ => rfl⟩
  obtain ⟨B, hBapp⟩ : ∃ B : Module.End k M, ∀ m, B m = ⁅distinguishedElement_aux1 k, m⁆ :=
    ⟨LieModule.toEnd k (matrixLieSubalgebra k) M (distinguishedElement_aux1 k), fun _ => rfl⟩
  have hrel : ∀ m : M, A (B m) = B (A m) + B m := by
    intro m; simp only [hAapp, hBapp]; exact bracket_eq_aux5 k M m

  have hBinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hne
    obtain ⟨m₀, hm₀N, hm₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hX : ∀ m ∈ LinearMap.ker B, ⁅distinguishedElement k, m⁆ ∈ LinearMap.ker B := by
      intro m hm
      rw [LinearMap.mem_ker] at hm ⊢
      have h := hrel m
      rw [hm, map_zero, add_zero] at h
      rw [← hAapp]
      exact h.symm
    have hY : ∀ m ∈ LinearMap.ker B, ⁅distinguishedElement_aux1 k, m⁆ ∈ LinearMap.ker B := by
      intro m hm
      rw [LinearMap.mem_ker] at hm ⊢
      rw [← hBapp, hm, map_zero]
    have htop := displayed_eq_aux1 k M (LinearMap.ker B) hX hY hm₀N hm₀
    obtain ⟨m, hm⟩ := hYne
    have hmem : m ∈ LinearMap.ker B := by rw [htop]; exact Submodule.mem_top
    exact hm (by rw [← hBapp]; exact LinearMap.mem_ker.mp hmem)
  have hBpow : ∀ n : ℕ, Function.Injective ((B : Module.End k M) ^ n) := by
    intro n
    induction n with
    | zero => intro x y h; simpa using h
    | succ j ih =>
      intro x y h
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply] at h
      exact hBinj (ih h)

  have hApow : ∀ (n : ℕ) (m : M), A ((B ^ n) m) = (B ^ n) (A m) + (n : k) • (B ^ n) m := by
    intro n
    induction n with
    | zero => intro m; simp
    | succ j ih =>
      intro m
      simp only [pow_succ, Module.End.mul_apply]
      rw [ih (B m), hrel m, map_add, Nat.cast_succ]
      module

  obtain ⟨β, hβ⟩ : ∃ β : k, ∀ m : M, (B ^ p) m = β • m := by
    obtain ⟨β, hev⟩ := Module.End.exists_eigenvalue (B ^ p)
    obtain ⟨w, hwmem, hw0⟩ := hev.exists_hasEigenvector
    refine ⟨β, fun m => ?_⟩
    have hcomm : ∀ x : M, A ((B ^ p) x) = (B ^ p) (A x) := by
      intro x
      rw [hApow p x, CharP.cast_eq_zero k p, zero_smul, add_zero]
    have hBcomm : ∀ x : M, (B ^ p) (B x) = B ((B ^ p) x) := by
      intro x
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']
    have hX : ∀ x ∈ Module.End.eigenspace (B ^ p) β,
        ⁅distinguishedElement k, x⁆ ∈ Module.End.eigenspace (B ^ p) β := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [← hAapp, ← hcomm, hx, map_smul]
    have hY : ∀ x ∈ Module.End.eigenspace (B ^ p) β,
        ⁅distinguishedElement_aux1 k, x⁆ ∈ Module.End.eigenspace (B ^ p) β := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [← hBapp, hBcomm, hx, map_smul]
    have htop :=
      displayed_eq_aux1 k M (Module.End.eigenspace (B ^ p) β) hX hY hwmem hw0
    have hmem : m ∈ Module.End.eigenspace (B ^ p) β := by rw [htop]; exact Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.mp hmem
  have hβ0 : β ≠ 0 := by
    intro h
    obtain ⟨w, hw⟩ := exists_ne (0 : M)
    exact hw (hBpow p (by rw [hβ, h, zero_smul, map_zero]))

  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := k) β (Fact.out : p.Prime).pos
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hc
    exact hβ0 hc.symm

  obtain ⟨a, hev⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
  have hAv : A v = a • v := Module.End.mem_eigenspace_iff.mp hvmem

  obtain ⟨t, htdef⟩ : ∃ t : ℕ → M, ∀ n, t n = (c⁻¹ ^ n) • (B ^ n) v :=
    ⟨fun n => (c⁻¹ ^ n) • (B ^ n) v, fun _ => rfl⟩
  have htA : ∀ n : ℕ, A (t n) = (a + (n : k)) • t n := by
    intro n
    rw [htdef n, map_smul, hApow n v, hAv, map_smul]
    module
  have htB : ∀ n : ℕ, B (t n) = c • t (n + 1) := by
    intro n
    have hcc : c * c⁻¹ ^ (n + 1) = c⁻¹ ^ n := by
      rw [pow_succ', ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    rw [htdef n, htdef (n + 1), map_smul, smul_smul, hcc, ← Module.End.mul_apply, ← pow_succ']
  have ht0 : ∀ n : ℕ, t n ≠ 0 := by
    intro n h
    rw [htdef n] at h
    rcases smul_eq_zero.mp h with h2 | h2
    · exact pow_ne_zero _ (inv_ne_zero hc0) h2
    · exact hv0 (hBpow n (by rw [h2, map_zero]))
  have htper : ∀ n : ℕ, t (n + p) = t n := by
    intro n
    have h1 : (B ^ (n + p)) v = β • (B ^ n) v := by
      rw [pow_add, Module.End.mul_apply, hβ v, map_smul]
    have hpinv : c⁻¹ ^ p * c ^ p = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hc0, one_pow]
    have hscal : c⁻¹ ^ (n + p) * β = c⁻¹ ^ n := by
      rw [← hc, pow_add, mul_assoc, hpinv, mul_one]
    rw [htdef (n + p), htdef n, h1, smul_smul, hscal]
  have htmul : ∀ q n : ℕ, t (n + p * q) = t n := by
    intro q
    induction q with
    | zero => intro n; simp
    | succ j ih => intro n; rw [Nat.mul_succ, ← Nat.add_assoc, htper, ih]
  have htmod : ∀ n : ℕ, t (n % p) = t n := by
    intro n
    conv_rhs => rw [← Nat.mod_add_div n p]
    rw [htmul]

  obtain ⟨u, hudef⟩ : ∃ u : ZMod p → M, ∀ i, u i = t i.val := ⟨fun i => t i.val, fun _ => rfl⟩
  have huA : ∀ i : ZMod p, A (u i) = (a + distinguishedElement_aux5 k p i) • u i := by
    intro i
    rw [hudef i, htA, map_apply_aux9]
  have huB : ∀ i : ZMod p, B (u i) = c • u (i + 1) := by
    intro i
    rw [hudef i, hudef (i + 1), htB]
    congr 1
    rw [← htmod (i.val + 1)]
    congr 1
    rw [ZMod.val_add, ZMod.val_one]
  have hu0 : ∀ i : ZMod p, u i ≠ 0 := by
    intro i
    rw [hudef i]
    exact ht0 i.val

  have hindep : LinearIndependent k u := by
    refine Module.End.eigenvectors_linearIndependent' A (fun i => a + distinguishedElement_aux5 k p i) ?_ u ?_
    · intro i j hij
      exact map_injective k p (add_left_cancel hij)
    · intro i
      exact ⟨Module.End.mem_eigenspace_iff.mpr (huA i), hu0 i⟩

  have hspanX : ∀ m ∈ Submodule.span k (Set.range u),
      ⁅distinguishedElement k, m⁆ ∈ Submodule.span k (Set.range u) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← hAapp, huA]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [lie_smul]; exact Submodule.smul_mem _ _ hx
  have hspanY : ∀ m ∈ Submodule.span k (Set.range u),
      ⁅distinguishedElement_aux1 k, m⁆ ∈ Submodule.span k (Set.range u) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← hBapp, huB]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + 1, rfl⟩)
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [lie_smul]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span k (Set.range u) = ⊤ :=
    displayed_eq_aux1 k M _ hspanX hspanY
      (Submodule.subset_span ⟨0, rfl⟩) (hu0 0)

  let b : Module.Basis (ZMod p) k M := Module.Basis.mk hindep (le_of_eq hspan.symm)
  have hb : ∀ i, b i = u i := fun i => Module.Basis.mk_apply hindep _ i

  have hXint : ∀ f : ZMod p → k,
      b.equivFun.symm (distinguishedElement_aux2 k p a f) = A (b.equivFun.symm f) := by
    intro f
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hb i, huA i, map_apply, smul_smul, mul_comm]
  have hYint : ∀ f : ZMod p → k,
      b.equivFun.symm (distinguishedElement_aux3 k p (Units.mk0 c hc0) f) = B (b.equivFun.symm f) := by
    intro f
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
    have hR : ∀ i : ZMod p, B (f i • b i) = (f i * c) • u (i + 1) := fun i => by
      rw [hb, map_smul, huB, smul_smul]
    have hL : ∀ i : ZMod p,
        (distinguishedElement_aux3 k p (Units.mk0 c hc0) f) i • b i = (c * f (i - 1)) • u i := fun i => by
      rw [hb, map_apply_aux6, Units.val_mk0]
    simp only [hR, hL]
    exact (Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _
      (fun i => by simp [mul_comm])).symm
  have key : AuxiliaryType k p (Units.mk0 c hc0) a ≃ₗ⁅k, matrixLieSubalgebra k⁆ M := by
    refine lieModuleEquiv_aux1 k b.equivFun.symm (fun f => ?_) (fun f => ?_)
    · rw [bracket_eq_aux3, ← hAapp]
      exact hXint f
    · rw [bracket_eq_aux4, ← hBapp]
      exact hYint f
  exact ⟨Units.mk0 c hc0, a, ⟨key.symm⟩⟩

/-- Every finite-dimensional irreducible module is equivalent to either a one-parameter module or a module in the displayed modular family. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem irreducibleModule_equiv_classification [IsAlgClosed k] (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] :
    (∃ μ : k, Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType_aux1 k μ))
      ∨ ∃ (γ : kˣ) (a : k), Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ a) := by
  by_cases h : ∀ m : M, ⁅distinguishedElement_aux1 k, m⁆ = 0
  · exact Or.inl (exists_equiv_oneDimensional_of_trivial_action k M h)
  · exact Or.inr (exists_equiv_modularFamily_of_nontrivial_action k p M (not_forall.mp h))

/-- The displayed classification of finite-dimensional irreducible modules has the stated uniqueness of parameters. -/
@[source_ref "Chapter2/Problem2.16.2" (role := supporting)]
theorem irreducibleModule_equiv_classification_unique [IsAlgClosed k] (M : Type*) [AddCommGroup M] [Module k M]
    [LieRingModule (matrixLieSubalgebra k) M] [LieModule k (matrixLieSubalgebra k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (matrixLieSubalgebra k) M] :
    (∃! μ : k, Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType_aux1 k μ))
      ∨ ∃ (γ : kˣ) (a : k), Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ a)
          ∧ ∀ (γ' : kˣ) (a' : k), Nonempty (M ≃ₗ⁅k, matrixLieSubalgebra k⁆ AuxiliaryType k p γ' a') →
              γ' = γ ∧ ∃ n : ZMod p, a' = a + distinguishedElement_aux5 k p n := by
  rcases irreducibleModule_equiv_classification k p M with ⟨μ, hμ⟩ | ⟨γ, a, hγa⟩
  · refine Or.inl ⟨μ, hμ, ?_⟩
    rintro ν ⟨ψ⟩
    obtain ⟨φ⟩ := hμ
    by_contra hne
    exact not_nonempty_lieModuleEquiv_of_ne k (Ne.symm hne) ⟨φ.symm.trans ψ⟩
  · refine Or.inr ⟨γ, a, hγa, ?_⟩
    rintro γ' a' ⟨ψ⟩
    obtain ⟨φ⟩ := hγa
    obtain ⟨hg, n, hn⟩ := (nonempty_lieModuleEquiv_iff γ' γ a' a).mp ⟨ψ.symm.trans φ⟩
    refine ⟨hg, -n, ?_⟩
    rw [map_neg, hn]
    ring

/-- In the displayed positive-characteristic setting, not every finite-dimensional irreducible module has finite rank one. -/
@[source_ref "Chapter2/Problem2.16.2" (role := primary)]
theorem not_forall_irreducible_finrank_eq_one (k : Type) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (matrixLieSubalgebra k) M]
        [LieModule k (matrixLieSubalgebra k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (matrixLieSubalgebra k) M],
        Module.finrank k M = 1 := by
  haveI := modularFamily_isIrreducible (k := k) (p := p) 1 0
  intro h
  have hfr : Module.finrank k (AuxiliaryType k p 1 0) = 1 := h (AuxiliaryType k p 1 0)
  rw [finrank_eq_aux1] at hfr
  exact ((Fact.out : p.Prime).one_lt).ne' hfr

end CharP

end RepresentationTheory.LieAlgebra.ModularRepresentations

attribute [nolint defsWithUnderscore]
  RepresentationTheory.LieAlgebra.ModularRepresentations.matrixLieSubalgebra
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.submodule
  RepresentationTheory.LieAlgebra.ModularRepresentations.lieModuleEquiv_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.AuxiliaryType_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.instAddCommGroup_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.instModule_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.lieHom_aux2
  RepresentationTheory.LieAlgebra.ModularRepresentations.instLieRingModule_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.linearEquiv
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux5
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux2
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux6
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux3
  RepresentationTheory.LieAlgebra.ModularRepresentations.matrixLieSubalgebra_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.lieHom
  RepresentationTheory.LieAlgebra.ModularRepresentations.AuxiliaryType
  RepresentationTheory.LieAlgebra.ModularRepresentations.instAddCommGroup
  RepresentationTheory.LieAlgebra.ModularRepresentations.instModule
  RepresentationTheory.LieAlgebra.ModularRepresentations.lieHom_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.instLieRingModule
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux7
  RepresentationTheory.LieAlgebra.ModularRepresentations.distinguishedElement_aux4
  RepresentationTheory.LieAlgebra.ModularRepresentations.linearEquiv_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.lieModuleEquiv

attribute [nolint defsWithUnderscore unusedArguments]
  RepresentationTheory.LieAlgebra.ModularRepresentations.AuxiliaryType_aux1
  RepresentationTheory.LieAlgebra.ModularRepresentations.AuxiliaryType
