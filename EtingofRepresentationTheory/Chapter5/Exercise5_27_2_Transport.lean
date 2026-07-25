import Mathlib

/-!
# Exercise 5.27.2: transporting a classification along a group isomorphism

Exercise 5.27.2 asks to redo Problems 4.12.1(a), 4.12.2 and 4.12.6 using Theorem 5.27.1. The
orbit method of Theorem 5.27.1 produces the irreducibles of a semidirect product `A ⋊[φ] G`,
so each arm of the exercise first classifies the irreducibles of a semidirect-product model and
then has to move that classification onto the group the original problem studies (Mathlib's
`DihedralGroup N`, `Problem4_12_2.Heisenberg p`, `Problem4_12_6.Affine K`), which is a
*different type* isomorphic to the model.

This file holds the machinery shared by all three arms. Restriction of scalars along a group
isomorphism `e : G ≃* H` is an equivalence of representation categories
`FDRep ℂ H ≌ FDRep ℂ G` (`repEquiv`), and `transport_classification` pushes a complete,
irredundant family of irreducibles across it, keeping the dimensions on the nose. Any counting
statement about the family (how many members have each dimension) transports along the
dimension equality by `Finset.filter_congr`.
-/

noncomputable section

open CategoryTheory Module

namespace Etingof.Exercise5_27_2

section Simple

open CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A full, faithful, monomorphism-preserving functor reflects simple objects. -/
lemma simple_of_functor_obj (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms]
    (X : C) [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f _ := by
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
          (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- An equivalence of categories preserves simple objects. -/
lemma simple_equivalence_functor (E : C ≌ D) (X : C) [Simple X] :
    Simple (E.functor.obj X) := by
  haveI : Simple ((𝟭 C).obj X) := inferInstanceAs (Simple X)
  haveI : Simple (E.inverse.obj (E.functor.obj X)) := Simple.of_iso (E.unitIso.app X).symm
  exact simple_of_functor_obj E.inverse (E.functor.obj X)

end Simple

variable {G H : Type} [Group G] [Group H]

/-- Restriction of scalars along a group isomorphism `e : G ≃* H`: the equivalence of
representation categories `FDRep ℂ H ≌ FDRep ℂ G`. -/
def repEquiv (e : G ≃* H) : FDRep ℂ H ≌ FDRep ℂ G :=
  Action.resEquiv (FGModuleCat ℂ) e

/-- The transport functor keeps the underlying vector space, so it preserves dimension. -/
lemma finrank_repEquiv_functor (e : G ≃* H) (V : FDRep ℂ H) :
    finrank ℂ ((repEquiv e).functor.obj V : Type) = finrank ℂ (V : Type) := rfl

/-- **Transport of a classification along a group isomorphism.** A complete, pairwise
non-isomorphic family of irreducible `H`-representations gives one for `G` along `e : G ≃* H`,
with the same index type and the same dimensions. The dimension equality is what lets the
caller move dimension-filtered counts across the transport. -/
theorem transport_classification (e : G ≃* H) {n : ℕ} (W : Fin n → FDRep ℂ H)
    (hsimple : ∀ i, Simple (W i))
    (hinj : ∀ i j, Nonempty (W i ≅ W j) → i = j)
    (hcomplete : ∀ S : FDRep ℂ H, Simple S → ∃ i, Nonempty (S ≅ W i)) :
    ∃ W' : Fin n → FDRep ℂ G,
      (∀ i, Simple (W' i)) ∧
      (∀ i j, Nonempty (W' i ≅ W' j) → i = j) ∧
      (∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ W' i)) ∧
      (∀ i, finrank ℂ (W' i : Type) = finrank ℂ (W i : Type)) := by
  set E := repEquiv e with hE
  refine ⟨fun i => E.functor.obj (W i), ?_, ?_, ?_, ?_⟩
  · -- simplicity is preserved by the equivalence
    intro i
    haveI := hsimple i
    exact simple_equivalence_functor E (W i)
  · -- fully faithful reflects isomorphisms
    intro i j ⟨h⟩
    exact hinj i j ⟨E.fullyFaithfulFunctor.preimageIso h⟩
  · -- essential surjectivity: pull `S` back, classify, push forward
    intro S hS
    haveI := hS
    haveI : Simple (E.inverse.obj S) := simple_equivalence_functor E.symm S
    obtain ⟨i, ⟨h⟩⟩ := hcomplete (E.inverse.obj S) inferInstance
    exact ⟨i, ⟨(E.counitIso.app S).symm ≪≫ E.functor.mapIso h⟩⟩
  · -- dimensions are unchanged: the underlying vector space is the same
    intro i
    exact finrank_repEquiv_functor e (W i)

/-- The dimension filters of a transported family agree with those of the original family, so
every dimension-indexed count transports verbatim. -/
lemma filter_finrank_congr {n : ℕ} {W' : Fin n → FDRep ℂ G} {W : Fin n → FDRep ℂ H}
    (hdim : ∀ i, finrank ℂ (W' i : Type) = finrank ℂ (W i : Type)) (d : ℕ)
    [DecidablePred fun i => finrank ℂ (W' i : Type) = d]
    [DecidablePred fun i => finrank ℂ (W i : Type) = d] :
    (Finset.univ.filter fun i => finrank ℂ (W' i : Type) = d)
      = (Finset.univ.filter fun i => finrank ℂ (W i : Type) = d) := by
  apply Finset.filter_congr
  intro i _
  rw [hdim i]

end Etingof.Exercise5_27_2
