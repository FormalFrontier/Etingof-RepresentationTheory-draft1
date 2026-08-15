/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Surjectivity of algebra actions on simple modules -/

namespace RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity

open _root_.Module in
/-- For a finite-dimensional simple module over an algebraically closed field, the algebra action
is surjective. -/
@[source_ref "Chapter3/Discussion_proof_of_Theorem3.10.2" (role := primary),
  source_ref "Chapter3/Introduction_to_3.2" (role := supporting),
  source_ref "Chapter3/Corollary3.2.1/Derived2" (role := supporting),
  source_ref "Chapter3/Theorem3.2.2" (role := primary),
  source_ref "Chapter3/Theorem3.2.2/Derived2" (role := supporting),
  source_ref "Chapter3/Theorem3.2.2/Derived4" (role := supporting)]
theorem algebra_smul_surjective (k : Type*) (A : Type*) (V : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] End k V) := by
  intro f
  have hbij := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) k
  have g_smul : ∀ (c : End A V) (v : V), f (c • v) = c • f v := by
    intro c v
    obtain ⟨t, ht⟩ := hbij.2 c
    have hc : ∀ w, c w = t • w := fun w => by simp [← ht]
    simp only [End.smul_def, hc, map_smul]
  let g : End (End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := g_smul }
  haveI : Module.Finite (End A V) V :=
    Module.Finite.of_restrictScalars_finite k (End A V) V
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := V) g
  exact ⟨a, LinearMap.ext fun v => show a • v = f v from congr($(ha) v)⟩

/-- For a finite family of pairwise inequivalent finite-dimensional simple modules, the displayed
family of algebra actions is surjective. -/
@[source_ref "Chapter3/Introduction_to_3.2" (role := supporting),
  source_ref "Chapter3/Theorem3.2.2" (role := primary),
  source_ref "Chapter3/Theorem3.2.2/Derived4" (role := supporting),
  source_ref "Chapter3/Theorem3.5.4/Derived3" (role := primary),
  source_ref "Chapter3/Theorem3.6.2/Derived2" (role := primary)]
theorem family_algebra_smul_surjective (k : Type*) (A : Type*) (ι : Type*)
    [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [Finite ι]
    (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, Module A (V i)] [∀ i, IsScalarTower k A (V i)]
    [∀ i, FiniteDimensional k (V i)] [∀ i, IsSimpleModule A (V i)]
    (h_noniso : ∀ i j, i ≠ j → IsEmpty (V i ≃ₗ[A] V j)) :
    Function.Surjective
      (fun a i => (Algebra.lsmul k k (V i) : A →ₐ[k] Module.End k (V i)) a :
        A → ∀ i, Module.End k (V i)) := by
  classical
  letI := Fintype.ofFinite ι
  intro f
  haveI : IsSemisimpleModule A (∀ i, V i) :=
    IsSemisimpleModule.congr (DFinsupp.linearEquivFunOnFintype (R := A) (M := V)).symm
  haveI : Module.Finite (Module.End A (∀ i, V i)) (∀ i, V i) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have off_diag : ∀ (c : Module.End A (∀ i, V i)) (i j : ι), i ≠ j →
      ∀ w : V j, (c (Pi.single j w)) i = 0 := by
    intro c i j hij w
    let φ : V j →ₗ[A] V i :=
      (LinearMap.proj i).comp (c.comp (LinearMap.single A _ j))
    rcases φ.bijective_or_eq_zero with hbij | hzero
    · exact ((h_noniso i j hij).false (LinearEquiv.ofBijective φ hbij).symm).elim
    · exact LinearMap.congr_fun hzero w
  have diag_scalar : ∀ (c : Module.End A (∀ i, V i)) (i : ι),
      ∃ t : k, ∀ w : V i, (c (Pi.single i w)) i = t • w := by
    intro c i
    let ψ : Module.End A (V i) :=
      (LinearMap.proj i).comp (c.comp (LinearMap.single A _ i))
    obtain ⟨t, ht⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A)
      (V := V i) k).2 ψ
    exact ⟨t, fun w => show ψ w = t • w by simp [ψ, ← ht]⟩
  have c_scalar : ∀ (c : Module.End A (∀ i, V i)) (v : ∀ i, V i) (i : ι),
      (c v) i = (diag_scalar c i).choose • (v i) := by
    intro c v i
    have hdecomp : v = ∑ j, Pi.single j (v j) := by ext j; simp
    conv_lhs => rw [hdecomp, map_sum]
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · exact (diag_scalar c i).choose_spec (v i)
    · intro j _ hji
      exact off_diag c i j (Ne.symm hji) (v j)
    · intro hi; exact absurd (Finset.mem_univ i) hi
  let g : Module.End (Module.End A (∀ i, V i)) (∀ i, V i) :=
    { toFun := fun v i => f i (v i),
      map_add' := fun v w => funext fun i => map_add (f i) (v i) (w i),
      map_smul' := fun c v => by
        ext i
        change f i ((c v) i) = (c (fun j => f j (v j))) i
        rw [c_scalar c v i, map_smul, c_scalar c (fun j => f j (v j)) i] }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := ∀ i, V i) g
  refine ⟨a, funext fun i => LinearMap.ext fun v => ?_⟩
  change a • v = f i v
  have h := congr_fun (LinearMap.congr_fun ha (Pi.single i v)) i
  have lhs : (Module.toModuleEnd (Module.End A (∀ i, V i)) (∀ i, V i) a
    (Pi.single i v)) i = a • v := by
    change a • (Pi.single i v : ∀ i, V i) i = a • v
    simp
  have rhs : g (Pi.single i v) i = f i v := by
    change f i ((Pi.single i v : ∀ i, V i) i) = f i v
    simp
  rw [lhs, rhs] at h
  exact h

end RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity
