/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.RingTheory.SimpleModule.Isotypic
import RepresentationTheory.Algebra.SimpleModule.Endomorphisms
import RepresentationTheory.Alignment.Attribute

/-!
# Isotypic decomposition

Evaluation identifies a finite-dimensional semisimple module with a direct sum of tensor
products formed from its simple constituents and their multiplicity spaces.
-/

open scoped TensorProduct

namespace RepresentationTheory.Module.IsotypicDecomposition

variable (k : Type*) (A : Type*) (X : Type*) (V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The linear map that regards an algebra-linear map between scalar-tower modules as a linear
map over the base ring. -/
def restrictScalarsHomLinearMap : (X →ₗ[A] V) →ₗ[k] (X →ₗ[k] V) where
  toFun g := g.restrictScalars k
  map_add' g g' := LinearMap.restrictScalars_add g g'
  map_smul' c g := LinearMap.restrictScalars_smul c g

/-- The linear evaluation map from the tensor product of algebra-linear maps with their source
module into the target module. -/
@[source_ref "Chapter3/Remark3.1.3" (role := supporting)]
noncomputable def homTensorEvaluation : (X →ₗ[A] V) ⊗[k] X →ₗ[k] V :=
  TensorProduct.lift (restrictScalarsHomLinearMap k A X V)

/-- The hom-tensor evaluation map sends a pure tensor to application of the homomorphism to the
vector. -/
@[source_ref "Chapter3/Remark3.1.3" (role := supporting), simp]
theorem homTensorEvaluation_tmul (g : X →ₗ[A] V) (x : X) :
    homTensorEvaluation k A X V (g ⊗ₜ[k] x) = g x := rfl

end RepresentationTheory.Module.IsotypicDecomposition

namespace RepresentationTheory.Module.IsotypicDecomposition

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k V]

/-- For a finite-dimensional simple module over an algebraically closed field, evaluation is a
linear equivalence from its algebra-endomorphism space tensored with the module to the module. -/
@[source_ref "Chapter3/Remark3.1.3" (role := primary)]
noncomputable def endomorphismTensorSelfEquiv :
    (V →ₗ[A] V) ⊗[k] V ≃ₗ[k] V :=
  LinearEquiv.ofLinear
    (homTensorEvaluation k A V V)
    (TensorProduct.mk k (V →ₗ[A] V) V LinearMap.id)
    (by
      ext v
      simp)
    (by
      refine TensorProduct.ext' fun g x => ?_
      obtain ⟨c, hc⟩ :=
        RepresentationTheory.Algebra.SimpleModule.Endomorphisms.endomorphism_eq_smul
          (k := k) g
      have hg : g = c • LinearMap.id := by
        ext v
        rw [LinearMap.smul_apply, LinearMap.id_apply]
        exact hc v
      simp only [LinearMap.coe_comp, Function.comp_apply, homTensorEvaluation_tmul,
        TensorProduct.mk_apply, LinearMap.id_coe, id_eq]
      rw [hc x, ← TensorProduct.smul_tmul, ← hg])

/-- The endomorphism-tensor equivalence sends a pure tensor to evaluation of the endomorphism on
the vector. -/
@[source_ref "Chapter3/Remark3.1.3" (role := supporting), simp]
theorem endomorphismTensorSelfEquiv_tmul (g : V →ₗ[A] V) (x : V) :
    endomorphismTensorSelfEquiv k A V (g ⊗ₜ[k] x) = g x := rfl

end RepresentationTheory.Module.IsotypicDecomposition

namespace RepresentationTheory.Module.IsotypicDecomposition

section PerX

variable (k : Type*) (A : Type*) (X : Type*) (V : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [IsSimpleModule A X] [FiniteDimensional k X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V]

/-- Evaluation from the hom-space tensor product of a finite-dimensional simple module into a
finite-dimensional target is injective over an algebraically closed field. -/
theorem homTensorEvaluation_injective : Function.Injective (homTensorEvaluation k A X V) := by
  haveI : Module.Finite k (X →ₗ[A] V) :=
    Module.Finite.of_injective (restrictScalarsHomLinearMap k A X V) (fun g g' h =>
      LinearMap.ext fun x => LinearMap.congr_fun h x)
  set n := Module.finrank k (X →ₗ[A] V) with hn
  set b : Module.Basis (Fin n) k (X →ₗ[A] V) := Module.finBasis k (X →ₗ[A] V) with hb
  set G : (Fin n →₀ X) →ₗ[A] V := ∑ j, (b j).comp (Finsupp.lapply j) with hG_def
  set F : (Fin n →₀ X) →ₗ[k] (X →ₗ[A] V) ⊗[k] X :=
    ∑ j, (TensorProduct.mk k (X →ₗ[A] V) X (b j)).comp (Finsupp.lapply j) with hF_def
  have hFsingle : ∀ (j : Fin n) (x : X), F (Finsupp.single j x) = b j ⊗ₜ[k] x := by
    intro j x
    simp only [hF_def, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      Finsupp.lapply_apply, TensorProduct.mk_apply]
    rw [Finset.sum_eq_single j
      (fun l _ hl => by rw [Finsupp.single_eq_of_ne hl, TensorProduct.tmul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]
  have hGF : ∀ y : Fin n →₀ X, homTensorEvaluation k A X V (F y) = G y := by
    intro y
    simp only [hF_def, hG_def, LinearMap.coe_sum, Finset.sum_apply, map_sum,
      LinearMap.comp_apply, Finsupp.lapply_apply, TensorProduct.mk_apply,
      homTensorEvaluation_tmul]
  have hFsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul g x =>
        rw [← b.sum_repr g, TensorProduct.sum_tmul]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [← TensorProduct.smul_tmul']
        exact Submodule.smul_mem _ _ ⟨Finsupp.single j x, hFsingle j x⟩
    | add p q hp hq => exact add_mem hp hq
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot]
    haveI : IsSemisimpleModule A (Fin n →₀ X) := inferInstance
    haveI : IsSemisimpleModule A (LinearMap.ker G) := inferInstance
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (LinearMap.ker G) with
      hbot | ⟨S, hSle, hSsimple⟩
    · exact hbot
    · exfalso
      haveI := hSsimple
      haveI : Nontrivial S := hSsimple.nontrivial
      have hincl_inj : Function.Injective S.subtype := S.subtype_injective
      have hex : ∃ j, ((Finsupp.lapply j).comp S.subtype : S →ₗ[A] X) ≠ 0 := by
        by_contra hall
        push Not at hall
        obtain ⟨s, hs⟩ := exists_ne (0 : S)
        apply hs
        apply hincl_inj
        rw [map_zero]
        ext j
        have h2 : ((Finsupp.lapply j).comp S.subtype) s = 0 := by
          rw [hall j]
          rfl
        simpa [Finsupp.lapply_apply] using h2
      obtain ⟨j₀, hj₀⟩ := hex
      have hbij : Function.Bijective ((Finsupp.lapply j₀).comp S.subtype) :=
        ((Finsupp.lapply j₀).comp S.subtype).bijective_of_ne_zero hj₀
      set e : S ≃ₗ[A] X := LinearEquiv.ofBijective _ hbij with he
      have hc : ∀ l : Fin n, ∃ c : k, ∀ x : X,
          (S.subtype (e.symm x)) l = c • x := by
        intro l
        obtain ⟨c, hcl⟩ :=
          RepresentationTheory.Algebra.SimpleModule.Endomorphisms.endomorphism_eq_smul
            (k := k) (((Finsupp.lapply l).comp S.subtype).comp e.symm.toLinearMap)
        refine ⟨c, fun x => ?_⟩
        have := hcl x
        simpa [Finsupp.lapply_apply] using this
      choose c hc using hc
      have hsum0 : (∑ l, c l • b l) = 0 := by
        ext x
        rw [LinearMap.sum_apply, LinearMap.zero_apply]
        have hGz : G (S.subtype (e.symm x)) = 0 :=
          LinearMap.mem_ker.mp (hSle (Submodule.coe_mem (e.symm x)))
        have hGexp : G (S.subtype (e.symm x)) = ∑ l, b l ((S.subtype (e.symm x)) l) := by
          simp only [hG_def, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
            Finsupp.lapply_apply]
        rw [hGz] at hGexp
        rw [Finset.sum_congr rfl (fun l _ => ?_), ← hGexp]
        rw [LinearMap.smul_apply, ← (b l).map_smul_of_tower (c l) x, hc l x]
      have hc0 : ∀ l, c l = 0 :=
        Fintype.linearIndependent_iff.mp b.linearIndependent c hsum0
      haveI : Nontrivial X := IsSimpleModule.nontrivial (R := A) (M := X)
      obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
      apply hx₀
      have h1 : (S.subtype (e.symm x₀)) j₀ = x₀ := e.apply_symm_apply x₀
      rw [hc j₀ x₀, hc0 j₀, zero_smul] at h1
      exact h1.symm
  refine (injective_iff_map_eq_zero (homTensorEvaluation k A X V)).mpr fun t ht => ?_
  obtain ⟨y, rfl⟩ := hFsurj t
  rw [hGF y] at ht
  rw [hG (ht.trans (map_zero G).symm), map_zero]

end PerX

end RepresentationTheory.Module.IsotypicDecomposition

namespace RepresentationTheory.Module.IsotypicDecomposition

open scoped DirectSum

variable (k : Type*) (A : Type*) {ι : Type*} (X : ι → Type*) (V : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
  [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, Module A (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V] [IsSemisimpleModule A V]

/-- The evaluation map from the direct sum of hom-space tensor products associated with a family
of modules into the target module. -/
@[source_ref "Chapter3/Remark3.1.3" (role := primary)]
noncomputable def isotypicEvaluation :
    (⨁ i, (X i →ₗ[A] V) ⊗[k] X i) →ₗ[k] V :=
  DirectSum.toModule k ι V (fun i => homTensorEvaluation k A (X i) V)

omit [IsAlgClosed k] [Fintype ι] [∀ i, IsSimpleModule A (X i)]
  [∀ i, FiniteDimensional k (X i)] [FiniteDimensional k V] [IsSemisimpleModule A V] in
/-- The isotypic evaluation map sends a pure tensor included from one direct-sum component to
evaluation of its homomorphism on its vector. -/
@[source_ref "Chapter3/Remark3.1.3" (role := primary), simp]
theorem isotypicEvaluation_lof_tmul (i : ι) (g : X i →ₗ[A] V) (x : X i) :
    isotypicEvaluation k A X V
        (DirectSum.lof k ι (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x)) =
      g x := by
  simp [isotypicEvaluation]

/-- Every linear map between two simple modules is zero when no module-linear equivalence between
them exists. -/
theorem linearMap_eq_zero_of_isEmpty_linearEquiv {Y Z : Type*}
    [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    [IsSimpleModule A Y] [IsSimpleModule A Z]
    (h : IsEmpty (Y ≃ₗ[A] Z)) (f : Y →ₗ[A] Z) : f = 0 := by
  by_contra hf
  exact h.elim (LinearEquiv.ofBijective f (f.bijective_of_ne_zero hf))

omit [IsAlgClosed k] [Fintype ι] [∀ i, IsSimpleModule A (X i)]
  [∀ i, FiniteDimensional k (X i)] [FiniteDimensional k V] [IsSemisimpleModule A V] in
/-- Every simple submodule represented by the indexing family is contained in the range of the
isotypic evaluation map. -/
theorem simpleSubmodule_le_range_isotypicEvaluation
    (hcomplete : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i))
    (W : Submodule A V) (hW : IsSimpleModule A W) :
    (W : Set V) ⊆ LinearMap.range (isotypicEvaluation k A X V) := by
  obtain ⟨i, ⟨e⟩⟩ := hcomplete W hW
  intro w hw
  refine ⟨DirectSum.lof k ι _ i
    ((W.subtype ∘ₗ e.symm.toLinearMap) ⊗ₜ[k] e ⟨w, hw⟩), ?_⟩
  rw [isotypicEvaluation_lof_tmul]
  simp

omit [IsAlgClosed k] [Fintype ι] [∀ i, IsSimpleModule A (X i)]
  [∀ i, FiniteDimensional k (X i)] [FiniteDimensional k V] in
/-- The isotypic evaluation map is surjective when every simple submodule of the semisimple target
is equivalent to a member of the indexing family. -/
@[source_ref "Chapter3/Remark3.1.3" (role := supporting)]
theorem isotypicEvaluation_surjective
    (hcomplete : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i)) :
    Function.Surjective (isotypicEvaluation k A X V) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff]
  intro v _
  have htop : v ∈ sSup { m : Submodule A V | IsSimpleModule A m } := by
    rw [IsSemisimpleModule.sSup_simples_eq_top A V]
    trivial
  rw [sSup_eq_iSup'] at htop
  refine Submodule.iSup_induction _
    (motive := fun y => y ∈ LinearMap.range (isotypicEvaluation k A X V))
    htop (fun m y hy => ?_) (LinearMap.range _).zero_mem
    (fun _ _ => (LinearMap.range _).add_mem)
  exact simpleSubmodule_le_range_isotypicEvaluation k A X V hcomplete m.1 m.2 hy

omit [IsAlgClosed k] [Fintype ι] [DecidableEq ι]
  [∀ i, FiniteDimensional k (X i)] [FiniteDimensional k V] [IsSemisimpleModule A V] in
/-- The value of the hom-tensor evaluation map belongs to the isotypic component determined by its
simple source module. -/
theorem homTensorEvaluation_mem_isotypicComponent
    (i : ι) (t : (X i →ₗ[A] V) ⊗[k] X i) :
    homTensorEvaluation k A (X i) V t ∈ isotypicComponent A V (X i) := by
  induction t using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact zero_mem _
  | tmul g x =>
      rw [homTensorEvaluation_tmul]
      by_cases hg : g = 0
      · subst hg
        simp
      · have hker : LinearMap.ker g = ⊥ :=
          (eq_bot_or_eq_top (LinearMap.ker g)).resolve_right
            (fun h => hg (LinearMap.ker_eq_top.mp h))
        have hginj : Function.Injective g := LinearMap.ker_eq_bot.mp hker
        have hmem : LinearMap.range g ∈ {m : Submodule A V | Nonempty (m ≃ₗ[A] X i)} :=
          ⟨(LinearEquiv.ofInjective g hginj).symm⟩
        exact (le_sSup hmem) (LinearMap.mem_range_self g x)
  | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq

omit [Field k] [IsAlgClosed k] [Algebra k A] [Fintype ι] [DecidableEq ι]
  [∀ i, Module k (X i)] [∀ i, IsScalarTower k A (X i)]
  [∀ i, FiniteDimensional k (X i)] [Module k V] [IsScalarTower k A V]
  [FiniteDimensional k V] [IsSemisimpleModule A V] in
/-- A nonzero isotypic component belongs to the set of isotypic components of the ambient module. -/
theorem isotypicComponent_mem_isotypicComponents (i : ι)
    (hi : isotypicComponent A V (X i) ≠ ⊥) :
    isotypicComponent A V (X i) ∈ isotypicComponents A V := by
  obtain ⟨W, hWmem, -⟩ : ∃ W ∈ {m : Submodule A V | Nonempty (m ≃ₗ[A] X i)}, W ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hi (sSup_eq_bot.mpr h)
  obtain ⟨e⟩ := hWmem
  haveI : IsSimpleModule A W := IsSimpleModule.congr e
  exact ⟨W, inferInstance, (e.isotypicComponent_eq).symm⟩

omit [Field k] [IsAlgClosed k] [Algebra k A] [Fintype ι] [DecidableEq ι]
  [∀ i, Module k (X i)] [∀ i, IsScalarTower k A (X i)]
  [∀ i, FiniteDimensional k (X i)] [Module k V] [IsScalarTower k A V]
  [FiniteDimensional k V] in
/-- Distinct members of a pairwise inequivalent family have distinct isotypic components whenever
the first component is nonzero. -/
theorem isotypicComponent_ne_of_ne
    (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j)) (i j : ι) (hij : i ≠ j)
    (hi : isotypicComponent A V (X i) ≠ ⊥) :
    isotypicComponent A V (X i) ≠ isotypicComponent A V (X j) := by
  intro heq
  obtain ⟨W, hWmem, -⟩ : ∃ W ∈ {m : Submodule A V | Nonempty (m ≃ₗ[A] X i)}, W ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hi (sSup_eq_bot.mpr h)
  have e : W ≃ₗ[A] X i := hWmem.some
  haveI : IsSimpleModule A W := IsSimpleModule.congr e
  haveI : IsSimpleModule A (⊤ : Submodule A W) := IsSimpleModule.congr Submodule.topEquiv
  have hWle : W ≤ isotypicComponent A V (X j) := heq ▸ le_sSup hWmem
  have hiso : IsIsotypicOfType A W (X j) := le_isotypicComponent_iff.mp hWle
  obtain ⟨f⟩ := hiso ⊤
  exact (hpair i j hij).false (e.symm.trans (Submodule.topEquiv.symm.trans f))

omit [Field k] [IsAlgClosed k] [Algebra k A] [Fintype ι] [DecidableEq ι]
  [∀ i, Module k (X i)] [∀ i, IsScalarTower k A (X i)]
  [∀ i, FiniteDimensional k (X i)]
  [Module k V] [IsScalarTower k A V] [FiniteDimensional k V] in
/-- The isotypic components associated with a pairwise inequivalent family of simple modules in a
semisimple module form an independent supremum. -/
theorem iSupIndep_isotypicComponent
    (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j)) :
    iSupIndep (fun i => isotypicComponent A V (X i)) := by
  rw [iSupIndep_def']
  intro i
  rcases eq_or_ne (isotypicComponent A V (X i)) ⊥ with hi | hi
  · rw [hi]
    exact disjoint_bot_left
  · rw [← sSup_sdiff_singleton_bot]
    refine (sSupIndep_isotypicComponents A V).disjoint_sSup
      (isotypicComponent_mem_isotypicComponents A X V i hi) ?_ ?_
    · rintro c ⟨⟨j, -, rfl⟩, hcne⟩
      exact isotypicComponent_mem_isotypicComponents A X V j
        (fun h => hcne (Set.mem_singleton_iff.mpr h))
    · rintro ⟨⟨j, hj, hji⟩, -⟩
      exact isotypicComponent_ne_of_ne A X V hpair i j (Ne.symm hj) hi hji.symm

/- Finiteness is used to expand a direct-sum element as a finite sum, although it does not occur
in the proposition returned by `Function.Injective`. -/
set_option linter.unusedFintypeInType false in
/-- The isotypic evaluation map is injective for a pairwise inequivalent finite family of
finite-dimensional simple modules over an algebraically closed field. -/
@[source_ref "Chapter3/Remark3.1.3" (role := supporting)]
theorem isotypicEvaluation_injective
    (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j)) :
    Function.Injective (isotypicEvaluation k A X V) := by
  suffices h : ∀ ξ, isotypicEvaluation k A X V ξ = 0 → ξ = 0 by
    intro ξ₁ ξ₂ he
    have hsub : isotypicEvaluation k A X V (ξ₁ - ξ₂) = 0 := by
      rw [map_sub, he, sub_self]
    exact sub_eq_zero.mp (h _ hsub)
  intro ξ hξ
  have hindep := iSupIndep_isotypicComponent A X V hpair
  have hexpand : isotypicEvaluation k A X V ξ =
      ∑ i, homTensorEvaluation k A (X i) V (ξ i) := by
    conv_lhs => rw [← DirectSum.sum_univ_of ξ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [isotypicEvaluation, ← DirectSum.lof_eq_of (R := k), DirectSum.toModule_lof]
  rw [hexpand] at hξ
  have hvi : ∀ i, homTensorEvaluation k A (X i) V (ξ i) = 0 := by
    intro i
    have hmemNi : homTensorEvaluation k A (X i) V (ξ i) ∈
        isotypicComponent A V (X i) :=
      homTensorEvaluation_mem_isotypicComponent k A X V i (ξ i)
    have hneg : homTensorEvaluation k A (X i) V (ξ i) =
        -∑ j ∈ Finset.univ.erase i, homTensorEvaluation k A (X j) V (ξ j) :=
      eq_neg_of_add_eq_zero_left
        ((Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).trans hξ)
    have hmemSup : homTensorEvaluation k A (X i) V (ξ i) ∈
        ⨆ (j) (_ : j ≠ i), isotypicComponent A V (X j) := by
      rw [hneg]
      refine neg_mem (Submodule.sum_mem _ fun j hj => ?_)
      exact Submodule.mem_iSup_of_mem j
        (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hj)
          (homTensorEvaluation_mem_isotypicComponent k A X V j (ξ j)))
    have h0 := (hindep i).le_bot (Submodule.mem_inf.mpr ⟨hmemNi, hmemSup⟩)
    simpa using h0
  ext i
  rw [DirectSum.zero_apply]
  exact homTensorEvaluation_injective k A (X i) V ((hvi i).trans (map_zero _).symm)

/-- The linear equivalence from the direct sum of multiplicity-space tensor products to a
finite-dimensional semisimple module whose simple constituents are exhausted by a pairwise
inequivalent family. -/
@[source_ref "Chapter3/Remark3.1.3" (role := supporting)]
noncomputable def isotypicDecompositionEquiv
    (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
    (hcomplete : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i)) :
    (⨁ i, (X i →ₗ[A] V) ⊗[k] X i) ≃ₗ[k] V :=
  LinearEquiv.ofBijective (isotypicEvaluation k A X V)
    ⟨isotypicEvaluation_injective k A X V hpair,
      isotypicEvaluation_surjective k A X V hcomplete⟩

end RepresentationTheory.Module.IsotypicDecomposition
