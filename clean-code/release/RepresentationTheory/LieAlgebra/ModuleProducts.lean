/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.LieModule.CentralAction
import RepresentationTheory.Alignment.Attribute

open LieModule Module

namespace RepresentationTheory.LieAlgebra.ModuleProducts

universe u



section PiLie

variable {L : Type*} [LieRing L] {ι : Type*} {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, LieRingModule L (M i)]


/-- Equips a dependent product with the componentwise Lie-ring-module action. -/
instance piLieRingModule : LieRingModule L (∀ i, M i) where
  bracket x v := fun i => ⁅x, v i⁆
  add_lie x y v := by funext i; exact add_lie x y (v i)
  lie_add x u v := by funext i; exact lie_add x (u i) (v i)
  leibniz_lie x y v := by funext i; exact leibniz_lie x y (v i)


/-- Evaluation of the bracket on a dependent product equals the bracket in the selected component. -/
@[simp] theorem bracket_pi_apply (x : L) (v : ∀ i, M i) (i : ι) :
    ⁅x, v⁆ i = ⁅x, v i⁆ := rfl

variable {R : Type*} [CommRing R] [LieAlgebra R L]
  [∀ i, Module R (M i)] [∀ i, LieModule R L (M i)]


/-- The dependent product of Lie modules carries the componentwise Lie-module structure. -/
instance piLieModule : LieModule R L (∀ i, M i) where
  smul_lie t x v := by funext i; exact smul_lie t x (v i)
  lie_smul t x v := by funext i; exact lie_smul t x (v i)

end PiLie

section ProdLie

variable {L : Type*} [LieRing L] {M N : Type*}
  [AddCommGroup M] [AddCommGroup N] [LieRingModule L M] [LieRingModule L N]


/-- Equips a product with the componentwise Lie-ring-module action. -/
instance prodLieRingModule : LieRingModule L (M × N) where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := by ext <;> exact add_lie x y _
  lie_add x p q := by ext <;> exact lie_add x _ _
  leibniz_lie x y p := by ext <;> exact leibniz_lie x y _


/-- The first projection of the bracket on a product is the bracket of the first projection. -/
@[simp] theorem bracket_prod_fst (x : L) (p : M × N) : (⁅x, p⁆ : M × N).1 = ⁅x, p.1⁆ := rfl

/-- The second projection of the bracket on a product is the bracket of the second projection. -/
@[simp] theorem bracket_prod_snd (x : L) (p : M × N) : (⁅x, p⁆ : M × N).2 = ⁅x, p.2⁆ := rfl

variable {R : Type*} [CommRing R] [LieAlgebra R L]
  [Module R M] [Module R N] [LieModule R L M] [LieModule R L N]


/-- The product of two Lie modules carries the componentwise Lie-module structure. -/
instance prodLieModule : LieModule R L (M × N) where
  smul_lie t x p := by ext <;> exact smul_lie t x _
  lie_smul t x p := by ext <;> exact lie_smul t x _

end ProdLie



section Assembly

variable {M M' N N' : Type*}
  [AddCommGroup M] [Module ℂ M] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M]
  [AddCommGroup M'] [Module ℂ M'] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M'] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra M']
  [AddCommGroup N] [Module ℂ N] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N]
  [AddCommGroup N'] [Module ℂ N'] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N'] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra N']


/-- A pair of Lie-module equivalences induces a Lie-module equivalence between the corresponding products. -/
def prodCongrLieModuleEquiv (eM : M ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ M') (eN : N ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ N') :
    (M × N) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ (M' × N') where
  toFun p := (eM p.1, eN p.2)
  map_add' p q := by ext <;> simp
  map_smul' t p := by ext <;> simp
  map_lie' := by
    intro x p
    ext
    · exact (eM : M →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ M').map_lie x p.1
    · exact (eN : N →ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ N').map_lie x p.2
  invFun p := (eM.symm p.1, eN.symm p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

end Assembly


/-- Reassociates a dependent family indexed by a cons into its head component and tail family as a Lie-module equivalence. -/
def consPiLieModuleEquiv {m : ℕ} (n₀ : ℕ) (n : Fin m → ℕ) :
    ((Fin (n₀ + 1) → ℂ) × ∀ i : Fin m, (Fin (n i + 1) → ℂ)) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆
      ∀ j : Fin (m + 1), (Fin ((Fin.cons n₀ n : Fin (m + 1) → ℕ) j + 1) → ℂ) where
  toFun p := Fin.cons (α := fun j => Fin ((Fin.cons n₀ n : Fin (m + 1) → ℕ) j + 1) → ℂ) p.1 p.2
  invFun w := (w 0, fun i => w i.succ)
  map_add' p q := by
    funext j; rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> rfl
  map_smul' t p := by
    funext j; rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> rfl
  map_lie' := by
    intro x p
    funext j; rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> rfl
  left_inv p := rfl
  right_inv w := Fin.cons_self_tail w



section Split

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]


/-- Complementary Lie submodules yield a Lie-module equivalence from their product to the ambient module. -/
noncomputable def prodOfComplementLieModuleEquiv (S C : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) (h : IsCompl S C) :
    (↥S × ↥C) ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ V :=
  { Submodule.prodEquivOfIsCompl (S : Submodule ℂ V) (C : Submodule ℂ V)
      (LieSubmodule.isCompl_toSubmodule.mpr h) with
    map_lie' := by
      intro x p
      change ((⁅x, p.1⁆ : ↥S) : V) + ((⁅x, p.2⁆ : ↥C) : V)
        = ⁅x, ((p.1 : ↥S) : V) + ((p.2 : ↥C) : V)⁆
      rw [LieSubmodule.coe_bracket, LieSubmodule.coe_bracket, ← lie_add] }

end Split



section Irreducible

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V]

omit [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] in

/-- Under the displayed nontrivial finite-dimensional module hypotheses, there exists an object satisfying `IsAtom`. -/
theorem auxiliary_exists_isAtom [FiniteDimensional ℂ V] [Nontrivial V] :
    ∃ W : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V, IsAtom W := by
  have : (⊤ : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) ≠ ⊥ := by
    intro h
    have hsub := (LieSubmodule.eq_bot_iff (N := (⊤ : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V))).mp h
    exact absurd (⟨fun a b => by simp [hsub a (LieSubmodule.mem_top a),
      hsub b (LieSubmodule.mem_top b)]⟩ : Subsingleton V) (not_subsingleton V)
  exact (eq_bot_or_exists_atom_le (⊤ : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V)).resolve_left this
    |>.imp fun W ⟨hW, _⟩ => hW

omit [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] in

/-- An atomic Lie submodule is irreducible with its induced module structure. -/
theorem isIrreducible_of_isAtom {W : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V} (hW : IsAtom W) :
    LieModule.IsIrreducible ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ↥W := by
  haveI : Nontrivial ↥W :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := V)).mpr hW.1
  exact LieModule.IsIrreducible.mk fun M hM => by
    set M' := LieSubmodule.map W.incl M
    have hM'_le : M' ≤ W := by
      intro v hv
      rw [LieSubmodule.mem_map] at hv
      obtain ⟨m, _, rfl⟩ := hv; exact m.property
    have hM'_ne : M' ≠ ⊥ := by
      intro h; apply hM; rw [eq_bot_iff]; intro m hm
      have : W.incl m ∈ (⊥ : LieSubmodule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V) := h ▸ LieSubmodule.mem_map_of_mem hm
      rw [LieSubmodule.mem_bot] at this
      rw [LieSubmodule.mem_bot]; exact Subtype.val_injective this
    have hM'_eq : M' = W := (hW.le_iff.mp hM'_le).resolve_left hM'_ne
    rw [eq_top_iff]; intro m _
    suffices hmem : (m : V) ∈ M' by
      rw [LieSubmodule.mem_map] at hmem
      obtain ⟨m', hm', hm'_eq⟩ := hmem
      exact (Subtype.val_injective hm'_eq) ▸ hm'
    rw [hM'_eq]; exact m.property

end Irreducible




private theorem nonempty_lieModuleEquiv_pi_of_finrank (d : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V],
      Module.finrank ℂ V = d →
      ∃ (m : ℕ) (n : Fin m → ℕ),
        Nonempty (V ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ ∀ i : Fin m, (Fin (n i + 1) → ℂ)) := by
  induction d using Nat.strongRecOn with | ind d ih => ?_
  intro V _ _ _ _ _ hdim
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  ·
    subst hd0
    haveI : Subsingleton V := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hnt
      haveI := hnt
      have : 0 < Module.finrank ℂ V := (finrank_pos_iff (R := ℂ)).mpr hnt
      omega
    refine ⟨0, Fin.elim0, ⟨?_⟩⟩
    exact
      { toFun := fun _ => (fun i => i.elim0)
        map_add' := fun _ _ => by funext i; exact i.elim0
        map_smul' := fun _ _ => by funext i; exact i.elim0
        map_lie' := by intro x v; funext i; exact i.elim0
        invFun := fun _ => 0
        left_inv := fun v => Subsingleton.elim _ _
        right_inv := fun w => by funext i; exact i.elim0 }
  ·
    haveI hnt : Nontrivial V := by
      rw [← finrank_pos_iff (R := ℂ)]; omega
    obtain ⟨S, hS⟩ := auxiliary_exists_isAtom (V := V)
    have hirr : LieModule.IsIrreducible ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra ↥S := isIrreducible_of_isAtom hS
    haveI : Nontrivial ↥S := (LieSubmodule.nontrivial_iff_ne_bot ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra (M := V)).mpr hS.1

    obtain ⟨n₀, hn₀⟩ : ∃ n₀, Module.finrank ℂ ↥S = n₀ + 1 := by
      have : 0 < Module.finrank ℂ ↥S := finrank_pos
      exact ⟨Module.finrank ℂ ↥S - 1, by omega⟩
    obtain ⟨eS⟩ := _root_.RepresentationTheory.LieAlgebra.FiniteDimensionalModules.nonempty_lieModuleEquiv_finFunction_of_irreducible n₀ hn₀ hirr

    obtain ⟨C, hC⟩ := _root_.RepresentationTheory.LieModule.CentralAction.exists_lieSubmodule_isCompl S

    have hsum : Module.finrank ℂ ↥S + Module.finrank ℂ ↥C = d := by
      have := Submodule.finrank_add_eq_of_isCompl (LieSubmodule.isCompl_toSubmodule.mpr hC)
      rw [← hdim]; exact this
    have hClt : Module.finrank ℂ ↥C < d := by omega
    obtain ⟨m, n, ⟨eC⟩⟩ := ih _ hClt ↥C rfl

    refine ⟨m + 1, Fin.cons n₀ n, ⟨?_⟩⟩
    exact (prodOfComplementLieModuleEquiv S C hC).symm.trans
      ((prodCongrLieModuleEquiv eS eC).trans (consPiLieModuleEquiv n₀ n))


/-- A finite-dimensional module over the displayed Lie algebra admits a Lie-module equivalence to a finite dependent product of complex coordinate-function spaces. -/
@[source_ref "Chapter2/Problem2.15.1/Derived10" (role := supporting),
  source_ref "Chapter2/Problem2.15.1/Derived11" (role := supporting),
  source_ref "Chapter2/Problem2.15.1/Derived12" (role := supporting)]
theorem nonempty_lieModuleEquiv_pi_of_finiteDimensional (V : Type u) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [LieRingModule _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] [LieModule ℂ _root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra V] :
    ∃ (m : ℕ) (n : Fin m → ℕ),
      Nonempty (V ≃ₗ⁅ℂ,_root_.RepresentationTheory.Algebra.Lie.ComplexTwoByTwoMatrices.complexTwoByTwoMatrixLieSubalgebra⁆ ∀ i : Fin m, (Fin (n i + 1) → ℂ)) :=
  nonempty_lieModuleEquiv_pi_of_finrank (Module.finrank ℂ V) V rfl

end RepresentationTheory.LieAlgebra.ModuleProducts
