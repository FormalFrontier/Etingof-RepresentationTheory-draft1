import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_S3
import EtingofRepresentationTheory.Chapter5.CharEqIso

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

It also holds `exists_charRep_iso_of_finrank_eq_one`: every one-dimensional representation of a
finite group is the character representation `charRep ξ` of its own character. That is what lets
each arm name the one-dimensional members of its transported family.
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

/-! ## Identifying the one-dimensional members of a transported family

Each arm of the exercise wants to say not just *how many* irreducibles there are but *which*
representations they are, in the names the corresponding Chapter 4 problem gives them. The
one-dimensional members are always the character representations `charRep ξ`, and that holds for
any finite group, so it belongs here rather than in one of the arms. -/

section OneDim

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- On a one-dimensional representation, `S.ρ g` is multiplication by the scalar `S.character g`
(there is nothing else a linear endomorphism of a line can be). -/
private lemma rho_eq_character_smul (S : FDRep ℂ G) (hdim : finrank ℂ (S : Type) = 1) (g : G) :
    S.ρ g = (S.character g : ℂ) • LinearMap.id := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (S.ρ g)
  have hchar : S.character g = c := by
    change LinearMap.trace ℂ _ (S.ρ g) = c
    rw [hc, map_smul, LinearMap.trace_id, hdim]
    simp
  rw [hchar]; exact hc

omit [Finite G] in
/-- Scalars are determined by their action on a one-dimensional space. -/
private lemma smul_id_inj (S : FDRep ℂ G) (hdim : finrank ℂ (S : Type) = 1) {a b : ℂ}
    (h : (a : ℂ) • (LinearMap.id : (S : Type) →ₗ[ℂ] (S : Type)) = b • LinearMap.id) : a = b := by
  have := congrArg (LinearMap.trace ℂ (S : Type)) h
  rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at this

/-- **Every one-dimensional representation of a finite group is a character representation.**
Its character `g ↦ S.character g` is multiplicative and nowhere zero, hence a group homomorphism
`ξ : G →* ℂˣ`, and `S ≅ charRep ξ` because the two have the same character. Unlike
`AbelianFDRep.exists_charFDRep_iso`, this needs no commutativity: the hypothesis is the dimension,
not simplicity of every irreducible. -/
theorem exists_charRep_iso_of_finrank_eq_one (S : FDRep ℂ G) (hdim : finrank ℂ (S : Type) = 1) :
    ∃ ξ : G →* ℂˣ, Nonempty (S ≅ FDRep.of (Etingof.Example4_3_S3.charRep ξ)) := by
  have hone : S.character (1 : G) = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : G, S.character (g * h) = S.character g * S.character h := by
    intro g h
    apply smul_id_inj S hdim
    have h1 : S.ρ (g * h) = (S.character (g * h) : ℂ) • LinearMap.id :=
      rho_eq_character_smul S hdim (g * h)
    have h2 : S.ρ (g * h) = (S.character g * S.character h : ℂ) • LinearMap.id := by
      rw [map_mul, rho_eq_character_smul S hdim g, rho_eq_character_smul S hdim h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    rw [← h1, ← h2]
  have hne : ∀ g : G, S.character g ≠ 0 := by
    intro g h0
    have hgi := hmul g g⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at hgi
    exact one_ne_zero hgi
  refine ⟨{ toFun := fun g => Units.mk0 (S.character g) (hne g)
            map_one' := Units.ext (by simp [hone])
            map_mul' := fun g h => Units.ext (by simp [hmul g h, Units.val_mul]) }, ?_⟩
  refine Etingof.charEq_iso S _ (funext fun g => ?_)
  rw [Etingof.Example4_3_S3.charRep_character]
  rfl

end OneDim

end Etingof.Exercise5_27_2
