/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.RingTheory.Artinian.ModuleIdempotents
import Mathlib.Order.JordanHolder
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Composition-series invariants for modules

This module relates composition-series invariants to dimensions of linear-map modules.
-/

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A] [Module.Finite k A]

namespace RepresentationTheory.Algebra.Module.CompositionSeries

/-- A natural-number invariant associated with a composition series of submodules and a module. -/
noncomputable def CompositionSeries.moduleNatInvariant
    {N : Type*} [AddCommGroup N] [Module A N]
    (s : CompositionSeries (Submodule A N))
    (S : Type*) [AddCommGroup S] [Module A S] : ℕ :=
  @Finset.card _ (@Finset.filter _ (fun l : Fin s.length =>
      Nonempty ((↥(s l.succ) ⧸ (s (Fin.castSucc l)).comap (s l.succ).subtype) ≃ₗ[A] S))
    (fun _ => Classical.dec _) Finset.univ)

section Helpers

/-- Shows that the finite rank of the linear-map module is zero when the bottom and top submodules agree. -/
theorem Module.finrank_hom_eq_zero_of_bot_eq_top
    {R : Type*} [Ring R] {F : Type*} [Field F] [Algebra F R]
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module F P] [IsScalarTower F R P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N]
    (h : (⊥ : Submodule R N) = ⊤) :
    Module.finrank F (P →ₗ[R] N) = 0 := by
  haveI : Subsingleton N := by
    rw [subsingleton_iff]
    intro a b
    have ha : a ∈ (⊤ : Submodule R N) := Submodule.mem_top
    have hb : b ∈ (⊤ : Submodule R N) := Submodule.mem_top
    rw [← h] at ha hb
    simp only [Submodule.mem_bot] at ha hb
    rw [ha, hb]
  haveI : Subsingleton (P →ₗ[R] N) := ⟨fun f g => LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  exact Module.finrank_zero_of_subsingleton

/-- Decomposes the finite rank of maps into a module as the sum of the ranks for a submodule and its quotient. -/
theorem Module.finrank_hom_eq_finrank_hom_submodule_add_quotient
    {R : Type*} [Ring R] {F : Type*} [Field F] [Algebra F R]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
    [Module F P] [IsScalarTower F R P] [SMulCommClass R F P]
    [Module.Finite F P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N] [SMulCommClass R F N]
    [Module.Finite F N]
    (N' : Submodule R N) :
    Module.finrank F (P →ₗ[R] N) =
      Module.finrank F (P →ₗ[R] N') + Module.finrank F (P →ₗ[R] (N ⧸ N')) := by

  let ψ : (P →ₗ[R] N) →ₗ[F] (P →ₗ[R] (N ⧸ N')) :=
    { toFun := fun f => N'.mkQ.comp f
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }

  have hψ_surj : Function.Surjective ψ := by
    intro g
    obtain ⟨h, hh⟩ := Module.projective_lifting_property N'.mkQ g N'.mkQ_surjective
    exact ⟨h, LinearMap.ext fun p => by
      change N'.mkQ (h p) = g p
      exact congr_fun (congr_arg DFunLike.coe hh) p⟩

  let ι : (P →ₗ[R] N') →ₗ[F] (P →ₗ[R] N) :=
    { toFun := fun f => N'.subtype.comp f
      map_add' := fun f g => by ext; simp
      map_smul' := fun c f => by ext; simp }

  have hι_range : LinearMap.range ι = LinearMap.ker ψ := by
    ext f
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨g, rfl⟩
      ext p
      change N'.mkQ (N'.subtype (g p)) = 0
      simp [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, (g p).2]
    · intro hf
      refine ⟨{ toFun := fun p => ⟨f p, ?_⟩, map_add' := ?_, map_smul' := ?_ }, ?_⟩
      · have : (ψ f) p = 0 := LinearMap.ext_iff.mp hf p
        simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply] at this
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      · intro x y; ext; simp
      · intro r x; ext; simp
      · ext p; simp [ι]

  have hι_inj : Function.Injective ι := by
    intro f g hfg
    ext p
    have := LinearMap.ext_iff.mp hfg p
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.subtype_apply] at this
    exact this

  have hrn := LinearMap.finrank_range_add_finrank_ker ψ

  rw [LinearMap.range_eq_top.mpr hψ_surj, finrank_top] at hrn

  rw [← hι_range, LinearEquiv.finrank_eq (LinearEquiv.ofInjective ι hι_inj).symm] at hrn
  linarith

/-- Describes the invariant of a nonempty composition series using the series with its last term erased and the final quotient. -/
theorem CompositionSeries.moduleNatInvariant_eraseLast
    {N : Type*} [AddCommGroup N] [Module A N]
    (s : CompositionSeries (Submodule A N))
    (hs : 0 < s.length)
    (S : Type*) [AddCommGroup S] [Module A S] :
    CompositionSeries.moduleNatInvariant s S =
      CompositionSeries.moduleNatInvariant s.eraseLast S +
      @ite ℕ (Nonempty ((↥(s.last) ⧸
          (s.eraseLast.last).comap (s.last).subtype) ≃ₗ[A] S))
        (Classical.dec _) 1 0 := by

  unfold CompositionSeries.moduleNatInvariant;
  rw [ Finset.card_filter, Finset.card_filter ];
  rcases s with ⟨ ⟨ l, hl ⟩ ⟩
  · aesop
  · erw [Fin.sum_univ_castSucc]
    aesop

/-- Identifies maps into the top submodule with maps into the ambient module at the level of finite rank. -/
theorem Module.finrank_hom_top_eq
    {R : Type*} [Ring R] {F : Type*} [Field F] [Algebra F R]
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module F P] [IsScalarTower F R P]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower F R N] :
    Module.finrank F (P →ₗ[R] (⊤ : Submodule R N)) = Module.finrank F (P →ₗ[R] N) := by
  apply LinearEquiv.finrank_eq
  exact
  { toFun := fun f => Submodule.topEquiv.toLinearMap.comp f
    invFun := fun f => (Submodule.topEquiv.symm.toLinearMap.comp f : P →ₗ[R] (⊤ : Submodule R N))
    left_inv := fun f => by ext x; simp [Submodule.topEquiv]
    right_inv := fun f => by ext x; simp [Submodule.topEquiv]
    map_add' := fun f g => by ext; simp
    map_smul' := fun c f => by ext; simp }

end Helpers

/-- Identifies the series invariant with the finite rank of a linear-map module under the stated hypotheses. -/
theorem CompositionSeries.moduleNatInvariant_eq_finrank_hom
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
    [∀ i, Module k (M i)] [∀ i, IsScalarTower k A (M i)]
    [∀ i, SMulCommClass A k (M i)]
    [∀ i, IsSimpleModule A (M i)]
    (hM : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j)
    (P : ι → Type*) [∀ i, AddCommGroup (P i)] [∀ i, Module A (P i)]
    [∀ i, Module k (P i)] [∀ i, IsScalarTower k A (P i)]
    [∀ i, SMulCommClass A k (P i)]
    [∀ i, Module.Projective A (P i)] [∀ i, Module.Finite A (P i)]
    (hP_indec : ∀ i, RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate A (P i))
    (hP : ∀ i j, Module.finrank k (P i →ₗ[A] M j) = if i = j then 1 else 0)
    (N : Type*) [AddCommGroup N] [Module A N]
    [Module k N] [IsScalarTower k A N] [SMulCommClass A k N]
    [Module.Finite k N]
    (hM_complete : ∀ (S T : Submodule A N), S ⋖ T →
      ∃ j, Nonempty ((↥T ⧸ S.comap T.subtype) ≃ₗ[A] M j))
    (s : CompositionSeries (Submodule A N))
    (hs_head : s.head = ⊥) (hs_last : s.last = ⊤) :
    ∀ i, Module.finrank k (P i →ₗ[A] N) =
      CompositionSeries.moduleNatInvariant s (M i) := by




  suffices gen : ∀ (N' : Submodule A N)
      (s : CompositionSeries (Submodule A N))
      (_ : s.head = ⊥) (_ : s.last = N'),
      ∀ i, Module.finrank k (P i →ₗ[A] N') =
        CompositionSeries.moduleNatInvariant s (M i) by
    intro i
    rw [← Module.finrank_hom_top_eq (R := A) (F := k)]
    exact gen ⊤ s hs_head hs_last i

  intro N' s' hs'_head hs'_last
  induction hn : s'.length generalizing N' s' with
  | zero =>
    intro i
    have hN'_bot : N' = ⊥ := by
      rw [← hs'_last, ← hs'_head]
      simp only [RelSeries.head, RelSeries.last, Fin.last]
      congr 1; ext; omega
    subst hN'_bot
    have lhs_zero : Module.finrank k (P i →ₗ[A] (⊥ : Submodule A N)) = 0 := by
      apply Module.finrank_hom_eq_zero_of_bot_eq_top (R := A) (F := k)
      ext ⟨x, hx⟩
      simp only [Submodule.mem_bot, Submodule.mem_top, iff_true]
      have := hx
      simp only [Submodule.mem_bot] at this
      exact Subtype.ext this
    have rhs_zero : CompositionSeries.moduleNatInvariant s' (M i) = 0 := by
      unfold CompositionSeries.moduleNatInvariant
      have : Finset.univ (α := Fin s'.length) = ∅ := by
        rw [Finset.univ_eq_empty_iff]; exact hn ▸ Fin.isEmpty
      simp [this]
    rw [lhs_zero, rhs_zero]
  | succ n ih =>
    intro i

    rw [CompositionSeries.moduleNatInvariant_eraseLast s' (by omega) (M i)]

    set N'' := s'.eraseLast.last
    have h_el_head : s'.eraseLast.head = ⊥ := by
      rw [RelSeries.head_eraseLast]; exact hs'_head
    have h_el_len : s'.eraseLast.length = n := by simp [hn]
    rw [← ih N'' s'.eraseLast h_el_head rfl h_el_len i]



    subst hs'_last
    set Q := Submodule.comap (s'.last).subtype N'' with hQ_def

    haveI : Module.Finite k (P i) := Module.Finite.trans A (P i)

    haveI : Module.Finite k ↥(s'.last) :=
      FiniteDimensional.finiteDimensional_submodule ((s'.last).restrictScalars k)

    have hN''_le : N'' ≤ s'.last :=
      (s'.eraseLast_last_rel_last (by omega)).le

    have e := Submodule.comapSubtypeEquivOfLe hN''_le
    have hQ_eq : Module.finrank k (P i →ₗ[A] ↥Q) = Module.finrank k (P i →ₗ[A] ↥N'') := by
      apply LinearEquiv.finrank_eq
      exact LinearEquiv.mk
        { toFun := fun f => (e.toLinearMap).comp f
          map_add' := fun f g => by simp [LinearMap.comp_add]
          map_smul' := fun c f => by simp [LinearMap.comp_smul] }
        (fun f => (e.symm.toLinearMap).comp f)
        (fun f => by simp)
        (fun f => by simp)

    have haddit := Module.finrank_hom_eq_finrank_hom_submodule_add_quotient
      (R := A) (F := k) (P := P i) (N := ↥(s'.last)) Q
    rw [haddit, hQ_eq]


    congr 1
    set S := (↥(s'.last) ⧸ Q)
    split
    ·
      rename_i h
      obtain ⟨iso⟩ := h

      have hom_equiv : Module.finrank k (P i →ₗ[A] S) = Module.finrank k (P i →ₗ[A] M i) := by
        apply LinearEquiv.finrank_eq
        exact LinearEquiv.mk
          { toFun := fun f => iso.toLinearMap.comp f
            map_add' := fun f g => by simp [LinearMap.comp_add]
            map_smul' := fun c f => by simp [LinearMap.comp_smul] }
          (fun f => iso.symm.toLinearMap.comp f)
          (fun f => by simp)
          (fun f => by simp)
      rw [hom_equiv, hP i i, if_pos rfl]
    ·
      rename_i h

      have hcovby : N'' ⋖ s'.last := s'.eraseLast_last_rel_last (by omega)
      haveI : IsSimpleModule A (↥(s'.last) ⧸ Q) :=
        (covBy_iff_quot_is_simple hN''_le).mp hcovby

      obtain ⟨j, ⟨iso_j'⟩⟩ := hM_complete N'' s'.last hcovby

      have iso_j : S ≃ₗ[A] M j := by
        change (↥(s'.last) ⧸ Q) ≃ₗ[A] M j
        rw [hQ_def]; exact iso_j'

      have hji : j ≠ i := by
        intro hji; subst hji; exact h ⟨iso_j⟩

      have hom_equiv : Module.finrank k (P i →ₗ[A] S) = Module.finrank k (P i →ₗ[A] M j) := by
        apply LinearEquiv.finrank_eq
        exact LinearEquiv.mk
          { toFun := fun f => iso_j.toLinearMap.comp f
            map_add' := fun f g => by simp [LinearMap.comp_add]
            map_smul' := fun c f => by simp [LinearMap.comp_smul] }
          (fun f => iso_j.symm.toLinearMap.comp f)
          (fun f => by simp)
          (fun f => by simp)
      rw [hom_equiv, hP i j, if_neg (Ne.symm hji)]

end RepresentationTheory.Algebra.Module.CompositionSeries
