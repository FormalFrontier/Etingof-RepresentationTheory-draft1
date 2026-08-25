/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.CategoryTheory.EndomorphismDecomposition
import RepresentationTheory.CategoryTheory.Limits.BiproductDecomposition
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Indecomposable summands of finite biproducts

This module proves an exchange property for indecomposable retracts of finite biproducts and the
resulting uniqueness of finite indecomposable biproduct decompositions.
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.CategoryTheory.Limits.Biproducts.Indecomposable

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [RepresentationTheory.CategoryTheory.SubobjectFiniteDimensional.SubobjectFiniteDimensional C]

/-- In a possibly noncommutative local ring, `IsUnit (a + b)` forces `IsUnit a ∨ IsUnit b`. Mathlib
only states this for `CommSemiring`, but the proof uses no commutativity: left-multiply by the
inverse unit to reduce to the defining property `isUnit_or_isUnit_of_add_one`. -/
private theorem isUnit_or_isUnit_of_isUnit_add' {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  refine (IsLocalRing.isUnit_or_isUnit_of_add_one hu).imp (fun ha => ?_) (fun hb => ?_)
  · have : a = ↑u * (↑u⁻¹ * a) := by rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact u.isUnit.mul ha
  · have : b = ↑u * (↑u⁻¹ * b) := by rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact u.isUnit.mul hb

/-- An idempotent unit is `1`: left-multiply `a * a = a` by the inverse unit. (Mathlib's
`IsIdempotentElem.iff_eq_one_of_isUnit` needs `IsDedekindFiniteMonoid`, which `End X` is not known
to satisfy; the direct argument below works in any monoid.) -/
private theorem idem_isUnit_eq_one {R : Type*} [Monoid R] {a : R}
    (h : IsIdempotentElem a) (hu : IsUnit a) : a = 1 := by
  obtain ⟨u, rfl⟩ := hu
  calc (↑u : R) = 1 * ↑u := (one_mul _).symm
    _ = (↑u⁻¹ * ↑u) * ↑u := by rw [Units.inv_mul]
    _ = ↑u⁻¹ * (↑u * ↑u) := by rw [mul_assoc]
    _ = ↑u⁻¹ * ↑u := by rw [h]
    _ = 1 := Units.inv_mul u

/-- An idempotent in a (possibly noncommutative) local ring is `0` or `1`. If `a` is a unit then
`a * a = a` forces `a = 1`; otherwise `1 - a` is a unit and the same argument on the (also
idempotent) `1 - a` forces it to be `1`, i.e. `a = 0`. -/
private theorem isIdempotentElem_eq_zero_or_one {R : Type*} [Ring R] [IsLocalRing R] {a : R}
    (h : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hor : IsUnit a ∨ IsUnit (1 - a) :=
    IsLocalRing.isUnit_or_isUnit_of_add_one (by abel : a + (1 - a) = 1)
  rcases hor with hu | hu
  · exact Or.inr (idem_isUnit_eq_one h hu)
  · refine Or.inl ?_
    have h1 : (1 : R) - a = 1 := idem_isUnit_eq_one h.one_sub hu
    exact sub_eq_self.mp h1

/-- In a (possibly noncommutative) local ring a finite sum that is a unit has a unit summand: the
nonunits are closed under addition (`isUnit_or_isUnit_of_isUnit_add'`) and contain `0`, so if every
summand were a nonunit the whole sum would be a nonunit. -/
private theorem exists_isUnit_of_isUnit_sum {R : Type*} [Ring R] [IsLocalRing R]
    {ι : Type*} (s : Finset ι) (g : ι → R) (h : IsUnit (∑ i ∈ s, g i)) :
    ∃ i ∈ s, IsUnit (g i) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ i ∈ s, g i ∈ nonunits R := fun i hi => mem_nonunits_iff.mpr (hcon i hi)
  have hsum : (∑ i ∈ s, g i) ∈ nonunits R :=
    Finset.sum_induction g (· ∈ nonunits R)
      (fun x y hx hy => by
        rw [mem_nonunits_iff] at hx hy ⊢
        exact fun hH => (isUnit_or_isUnit_of_isUnit_add' hH).elim hx hy)
      (zero_mem_nonunits.mpr zero_ne_one) hmem
  exact (mem_nonunits_iff.mp hsum) h

/-- An idempotent endomorphism of an indecomposable object is the zero morphism or the identity:
`End Z` is local, and an idempotent in a local ring is `0` or `1`. -/
private theorem endo_eq_zero_or_id {Z : C} (hZ : CategoryTheory.Indecomposable Z) {g : Z ⟶ Z}
    (hg : g ≫ g = g) : g = 0 ∨ g = 𝟙 Z := by
  haveI : IsLocalRing (End Z) := RepresentationTheory.CategoryTheory.EndomorphismDecomposition.indecomposableEndIsLocalRing hZ
  have hidem : IsIdempotentElem (M := End Z) g := hg
  rcases isIdempotentElem_eq_zero_or_one hidem with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [← End.one_def]; exact h)

set_option linter.unusedFintypeInType false in
/-- For an indecomposable retract of a finite biproduct of indecomposables, one component of the retract inclusion is an isomorphism. -/
theorem isIso_comp_biproductProjection_of_indecomposable_retract {κ : Type} [Fintype κ] (Y : κ → C)
    (hY : ∀ k, CategoryTheory.Indecomposable (Y k))
    {X : C} (hX : CategoryTheory.Indecomposable X)
    (s : X ⟶ ⨁ Y) (r : ⨁ Y ⟶ X) (hsr : s ≫ r = 𝟙 X) :
    ∃ k, IsIso (s ≫ biproduct.π Y k) := by
  -- Expand `𝟙 X` as a finite sum of endomorphisms `a k = (s ≫ π k) ≫ (ι k ≫ r)`.
  have key : (∑ k : κ, (s ≫ biproduct.π Y k) ≫ (biproduct.ι Y k ≫ r)) = 𝟙 X := by
    have e1 : ∀ k : κ, (s ≫ biproduct.π Y k) ≫ (biproduct.ι Y k ≫ r)
        = s ≫ (biproduct.π Y k ≫ biproduct.ι Y k) ≫ r := fun k => by simp only [Category.assoc]
    simp_rw [e1]
    rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, biproduct.total, Category.id_comp, hsr]
  set a : κ → End X := fun k => (s ≫ biproduct.π Y k) ≫ (biproduct.ι Y k ≫ r) with ha
  have hsum : (∑ k, a k) = 𝟙 X := key
  -- The sum is the unit `𝟙 X = 1`, so some summand is a unit in the local ring `End X`.
  haveI : IsLocalRing (End X) := RepresentationTheory.CategoryTheory.EndomorphismDecomposition.indecomposableEndIsLocalRing hX
  have hunit : IsUnit (∑ k, a k) := by rw [hsum, ← End.one_def]; exact isUnit_one
  obtain ⟨k, -, hk⟩ := exists_isUnit_of_isUnit_sum Finset.univ a hunit
  refine ⟨k, ?_⟩
  -- `a k = α ≫ β` is an iso, where `α : X ⟶ Y k`, `β : Y k ⟶ X`.
  set α : X ⟶ Y k := s ≫ biproduct.π Y k with hα
  set β : Y k ⟶ X := biproduct.ι Y k ≫ r with hβ
  have hak : (a k : X ⟶ X) = α ≫ β := rfl
  have hiso : IsIso (α ≫ β) := by
    rw [← hak]; exact (isUnit_iff_isIso (a k)).mp hk
  haveI := hiso
  -- `rr := β ≫ (α ≫ β)⁻¹` is a section of `α`.
  set rr : Y k ⟶ X := β ≫ inv (α ≫ β) with hrr
  have hαrr : α ≫ rr = 𝟙 X := by rw [hrr, ← Category.assoc, IsIso.hom_inv_id]
  -- `rr ≫ α` is an idempotent endomorphism of the indecomposable `Y k`, hence `0` or `𝟙`.
  have hcomp : (rr ≫ α) ≫ (rr ≫ α) = rr ≫ α := by
    rw [Category.assoc, ← Category.assoc α rr α, hαrr, Category.id_comp]
  rcases endo_eq_zero_or_id (hY k) hcomp with he0 | he1
  · -- `rr ≫ α = 0` forces `𝟙 X = 0`, impossible.
    exfalso
    apply hX.1
    rw [IsZero.iff_id_eq_zero]
    calc 𝟙 X = (α ≫ rr) ≫ (α ≫ rr) := by rw [hαrr, Category.comp_id]
      _ = α ≫ (rr ≫ α) ≫ rr := by simp only [Category.assoc]
      _ = α ≫ (0 : Y k ⟶ Y k) ≫ rr := by rw [he0]
      _ = 0 := by simp
  · -- `rr ≫ α = 𝟙 (Y k)`: with `α ≫ rr = 𝟙 X` the component `α = s ≫ π k` is an isomorphism.
    exact ⟨⟨rr, hαrr, he1⟩⟩

set_option linter.unusedFintypeInType false in
/-- An indecomposable retract of a finite biproduct of indecomposable objects is isomorphic to one of its summands. -/
theorem indecomposable_iso_biproduct_summand_of_retract {κ : Type} [Fintype κ] (Y : κ → C)
    (hY : ∀ k, CategoryTheory.Indecomposable (Y k))
    {X : C} (hX : CategoryTheory.Indecomposable X)
    (s : X ⟶ ⨁ Y) (r : ⨁ Y ⟶ X) (hsr : s ≫ r = 𝟙 X) :
    ∃ k, Nonempty (X ≅ Y k) := by
  obtain ⟨k, hk⟩ := isIso_comp_biproductProjection_of_indecomposable_retract Y hY hX s r hsr
  exact ⟨k, ⟨asIso (s ≫ biproduct.π Y k)⟩⟩

set_option linter.unusedFintypeInType false in
/-- Separates a selected term of a finite biproduct from the complementary family as a binary
biproduct. -/
noncomputable def biproductIsoBiprodBiproductComplement {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → C) (i₀ : ι) :
    (⨁ g) ≅ g i₀ ⊞ (⨁ Subtype.restrict (· ≠ i₀) g) where
  hom := biprod.lift (biproduct.π g i₀) (biproduct.toSubtype g (· ≠ i₀))
  inv := biprod.desc (biproduct.ι g i₀) (biproduct.fromSubtype g (· ≠ i₀))
  hom_inv_id := by
    refine biproduct.hom_ext' _ _ (fun j => biproduct.hom_ext _ _ (fun j' => ?_))
    by_cases hj : j = i₀ <;> by_cases hj' : j' = i₀
    · subst hj; subst hj'
      simp [biprod.lift_desc]
    · subst hj
      simp [biprod.lift_desc, Ne.symm hj']
    · subst hj'
      simp [biprod.lift_desc, hj]
    · simp [biprod.lift_desc, biproduct.ι_π, hj]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- The first binary inclusion transported through the inverse splitting isomorphism is the selected
biproduct inclusion. -/
@[reassoc (attr := simp)]
theorem biproductIsoBiprodBiproductComplement_inl_comp_inv {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → C) (i₀ : ι) :
    biprod.inl ≫ (biproductIsoBiprodBiproductComplement g i₀).inv = biproduct.ι g i₀ := by
  simp [biproductIsoBiprodBiproductComplement]

/-- Precomposing with the transported first binary inclusion agrees with precomposing with the
selected biproduct inclusion. -/
add_decl_doc biproductIsoBiprodBiproductComplement_inl_comp_inv_assoc

/-- The first binary projection through the splitting isomorphism is the projection onto the
selected biproduct component. -/
@[reassoc (attr := simp)]
theorem biproductIsoBiprodBiproductComplement_hom_comp_fst {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → C) (i₀ : ι) :
    (biproductIsoBiprodBiproductComplement g i₀).hom ≫ biprod.fst = biproduct.π g i₀ := by
  simp [biproductIsoBiprodBiproductComplement]

/-- Postcomposing the transported first binary projection agrees with postcomposing the selected
biproduct projection. -/
add_decl_doc biproductIsoBiprodBiproductComplement_hom_comp_fst_assoc

set_option linter.unusedFintypeInType false in
/-- An isomorphism between finite biproducts of indecomposables matches every source summand with an isomorphic target summand. -/
theorem biproduct_iso_indecomposable_summand {κ μ : Type} [Fintype κ] [Fintype μ] (Y : κ → C) (Z : μ → C)
    (hY : ∀ k, CategoryTheory.Indecomposable (Y k))
    (hZ : ∀ m, CategoryTheory.Indecomposable (Z m))
    (e : (⨁ Y) ≅ ⨁ Z) :
    ∃ σ : κ ≃ μ, ∀ k, Nonempty (Y k ≅ Z (σ k)) := by
  classical
  -- Strong induction on `n = Fintype.card κ`, with `κ, μ` and all data generalized.
  have key : ∀ n : ℕ, ∀ {κ μ : Type} [Fintype κ] [Fintype μ] (Y : κ → C) (Z : μ → C),
      (∀ k, CategoryTheory.Indecomposable (Y k)) → (∀ m, CategoryTheory.Indecomposable (Z m)) →
      Fintype.card κ = n → ((⨁ Y) ≅ ⨁ Z) →
      ∃ σ : κ ≃ μ, ∀ k, Nonempty (Y k ≅ Z (σ k)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro κ μ _ _ Y Z hY hZ hcard e
      classical
      rcases isEmpty_or_nonempty κ with hκe | hκne
      · -- `κ` empty: `⨁ Y` is zero, hence so is `⨁ Z`, forcing `μ` empty.
        haveI := hκe
        have hYzero : IsZero (⨁ Y) := by
          refine ⟨fun W => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun W => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩
          · exact biproduct.hom_ext' _ _ fun j => isEmptyElim j
          · exact biproduct.hom_ext _ _ fun j => isEmptyElim j
        have hZzero : IsZero (⨁ Z) := hYzero.of_iso e.symm
        haveI hμe : IsEmpty μ := by
          refine ⟨fun m => (hZ m).1 ?_⟩
          rw [IsZero.iff_id_eq_zero]
          have hi : biproduct.ι Z m ≫ biproduct.π Z m = 𝟙 (Z m) := biproduct.ι_π_self Z m
          rw [hZzero.eq_of_tgt (biproduct.ι Z m) 0, Limits.zero_comp] at hi
          exact hi.symm
        exact ⟨Equiv.equivOfIsEmpty κ μ, fun k => isEmptyElim k⟩
      · -- `κ` nonempty: pick `k₀`, find a matching `m₀`, cancel, recurse.
        obtain ⟨k₀⟩ := hκne
        -- `Y k₀` is an indecomposable retract of `⨁ Z`.
        have hsr : (biproduct.ι Y k₀ ≫ e.hom) ≫ (e.inv ≫ biproduct.π Y k₀) = 𝟙 (Y k₀) := by
          rw [Category.assoc, ← Category.assoc e.hom e.inv, e.hom_inv_id, Category.id_comp,
            biproduct.ι_π_self]
        obtain ⟨m₀, hα⟩ := isIso_comp_biproductProjection_of_indecomposable_retract Z hZ (hY k₀)
          (biproduct.ι Y k₀ ≫ e.hom) (e.inv ≫ biproduct.π Y k₀) hsr
        -- The peeled binary-biproduct isomorphism, with invertible top-left entry.
        set f := (biproductIsoBiprodBiproductComplement Y k₀).symm ≪≫ e ≪≫ biproductIsoBiprodBiproductComplement Z m₀ with hf
        have htl : biprod.inl ≫ f.hom ≫ biprod.fst
            = (biproduct.ι Y k₀ ≫ e.hom) ≫ biproduct.π Z m₀ := by
          rw [hf]
          simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, biproductIsoBiprodBiproductComplement_hom_comp_fst,
            biproductIsoBiprodBiproductComplement_inl_comp_inv_assoc]
        haveI : IsIso (biprod.inl ≫ f.hom ≫ biprod.fst) := by rw [htl]; exact hα
        -- Gaussian elimination cancels the matched summand.
        let e' := Biprod.isoElim f
        -- The complement has strictly smaller cardinality, so the IH applies.
        have hlt : Fintype.card {k // k ≠ k₀} < n := by
          rw [← hcard]; exact Fintype.card_subtype_lt (x := k₀) (by simp)
        obtain ⟨σ', hσ'⟩ := ih (Fintype.card {k // k ≠ k₀}) hlt
          (fun k' : {k // k ≠ k₀} => Y k'.val) (fun m' : {m // m ≠ m₀} => Z m'.val)
          (fun k' => hY k'.val) (fun m' => hZ m'.val) rfl e'
        -- Extend `σ'` to `κ ≃ μ` by sending `k₀ ↦ m₀`.
        let e₁ : {k // k = k₀} ≃ {m // m = m₀} :=
          { toFun := fun _ => ⟨m₀, rfl⟩, invFun := fun _ => ⟨k₀, rfl⟩,
            left_inv := fun x => Subtype.ext x.2.symm, right_inv := fun y => Subtype.ext y.2.symm }
        refine ⟨(Equiv.sumCompl (· = k₀)).symm.trans
          ((Equiv.sumCongr e₁ σ').trans (Equiv.sumCompl (· = m₀))), fun k => ?_⟩
        by_cases hk : k = k₀
        · -- matched summand: `σ k₀ = m₀` and `Y k₀ ≅ Z m₀`.
          subst hk
          have hσk : (Equiv.sumCompl (· = k) |>.symm.trans
              ((Equiv.sumCongr e₁ σ').trans (Equiv.sumCompl (· = m₀)))) k = m₀ := by
            have h1 : (Equiv.sumCompl (· = k)).symm k = Sum.inl ⟨k, rfl⟩ :=
              Equiv.sumCompl_symm_apply_of_pos (p := (· = k)) rfl
            rw [Equiv.trans_apply, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inl,
              Equiv.sumCompl_apply_inl]
            exact (e₁ ⟨k, rfl⟩).2
          rw [hσk]
          exact ⟨asIso (biprod.inl ≫ f.hom ≫ biprod.fst)⟩
        · -- complement summand: transported from the inductive hypothesis.
          have hσk : (Equiv.sumCompl (· = k₀) |>.symm.trans
              ((Equiv.sumCongr e₁ σ').trans (Equiv.sumCompl (· = m₀)))) k
              = (σ' ⟨k, hk⟩).val := by
            have h1 : (Equiv.sumCompl (· = k₀)).symm k = Sum.inr ⟨k, hk⟩ :=
              Equiv.sumCompl_symm_apply_of_neg (p := (· = k₀)) hk
            rw [Equiv.trans_apply, Equiv.trans_apply, h1, Equiv.sumCongr_apply, Sum.map_inr,
              Equiv.sumCompl_apply_inr]
          rw [hσk]
          exact hσ' ⟨k, hk⟩
  exact key (Fintype.card κ) Y Z hY hZ rfl e

end RepresentationTheory.CategoryTheory.Limits.Biproducts.Indecomposable
