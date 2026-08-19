/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FiniteDimensionalLinearMapPair
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-- Data presenting the product of the two component spaces by iterates of one cyclic vector. -/
structure RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.CyclicBasisData (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) where
  /-- The number of iterates occurring in the cyclic basis. -/
  length : ℕ
  /-- The length of cyclic basis data is positive. -/
  length_pos : 0 < length
  /-- The vector whose successive iterates form the specified basis. -/
  cyclicVector : ρ.Left × ρ.Right
  /-- The cyclic vector lies entirely in one of the two component summands. -/
  cyclicVector_fst_eq_zero_or_snd_eq_zero : cyclicVector.1 = 0 ∨ cyclicVector.2 = 0
  /-- The iterate at the specified length annihilates the cyclic vector. -/
  iterate_cyclicVector_eq_zero : (ρ.combinedEndomorphism ^ length) cyclicVector = 0
  /-- The finite basis of the product space supplied by cyclic basis data. -/
  basis : Module.Basis (Fin length) ℂ (ρ.Left × ρ.Right)
  /-- The basis vector at an index is the corresponding iterate of the cyclic vector. -/
  basis_apply : ∀ i, basis i = (ρ.combinedEndomorphism ^ (i : ℕ)) cyclicVector

/-- Data decomposing a nilpotent two-space system into finitely indexed blocks. -/
structure RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.NilpotentBlockDecomposition (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) where
  /-- The type indexing the blocks of a nilpotent decomposition. -/
  Index : Type
  /-- The index type of a block decomposition is finite. -/
  [indexFintype : Fintype Index]
  /-- The positive natural-number length assigned to a block index. -/
  blockLength : Index → ℕ
  /-- Each block in the decomposition has positive length. -/
  blockLength_pos : ∀ i, 0 < blockLength i
  /-- The vector in the product of component spaces assigned to a block index. -/
  blockVector : Index → ρ.Left × ρ.Right
  /-- Every indexed block vector has at least one zero component. -/
  blockVector_fst_eq_zero_or_snd_eq_zero : ∀ i,
    (blockVector i).1 = 0 ∨ (blockVector i).2 = 0
  /-- Applying the coupled endomorphism to a block vector as many times as its block length gives zero. -/
  iterate_blockVector_eq_zero : ∀ i,
    (ρ.combinedEndomorphism ^ blockLength i) (blockVector i) = 0
  /-- Auxiliary data attached to a nilpotent block decomposition. -/
  auxiliary : Module.Basis (Σ i, Fin (blockLength i)) ℂ (ρ.Left × ρ.Right)
  /-- The auxiliary data of a nilpotent block decomposition satisfies its defining property. -/
  auxiliary_spec : ∀ i,
    auxiliary i = (ρ.combinedEndomorphism ^ (i.2 : ℕ)) (blockVector i.1)

/-- Turns a cyclic basis presentation into a nilpotent block decomposition. -/
noncomputable def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.CyclicBasisData.toNilpotentBlockDecomposition {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) : ρ.NilpotentBlockDecomposition where
  Index := PUnit
  blockLength := fun _ => c.length
  blockLength_pos := fun _ => c.length_pos
  blockVector := fun _ => c.cyclicVector
  blockVector_fst_eq_zero_or_snd_eq_zero := fun _ => c.cyclicVector_fst_eq_zero_or_snd_eq_zero
  iterate_blockVector_eq_zero := fun _ => c.iterate_cyclicVector_eq_zero
  auxiliary := c.basis.reindex
    (Equiv.uniqueSigma (fun _ : PUnit => Fin c.length)).symm
  auxiliary_spec := by
    rintro ⟨i, j⟩
    rw [Module.Basis.reindex_apply, c.basis_apply]
    rfl

attribute [instance] RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.NilpotentBlockDecomposition.indexFintype

/-- Constructs a block decomposition when both component spaces are subsingletons. -/
noncomputable def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.NilpotentBlockDecomposition.of_subsingleton (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    [Subsingleton ρ.Left] [Subsingleton ρ.Right] : ρ.NilpotentBlockDecomposition where
  Index := PEmpty
  blockLength := PEmpty.elim
  blockLength_pos := fun i => i.elim
  blockVector := PEmpty.elim
  blockVector_fst_eq_zero_or_snd_eq_zero := fun i => i.elim
  iterate_blockVector_eq_zero := fun i => i.elim
  auxiliary := Module.Basis.empty (ρ.Left × ρ.Right)
  auxiliary_spec := by rintro ⟨i, _⟩; exact i.elim

/-- Restricts a system to a pair of subspaces preserved by its two structure maps. -/
noncomputable abbrev RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.restrict (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (V' : Submodule ℂ ρ.Left)
    (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V') :
    RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ where
  Left := V'
  Right := W'
  leftToRight := (ρ.leftToRight.domRestrict V').codRestrict W' (fun v => hA v v.2)
  rightToLeft := (ρ.rightToLeft.domRestrict W').codRestrict V' (fun w => hB w w.2)

/-- The forward structure map of a restriction agrees with the ambient forward map after coercion. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.coe_forwardMap_restrict_apply (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (V' : Submodule ℂ ρ.Left) (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V')
    (v : V') :
    ((ρ.restrict V' W' hA hB).leftToRight v : ρ.Right) = ρ.leftToRight v := rfl

/-- The reverse structure map of a restriction agrees with the ambient reverse map after coercion. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.coe_reverseMap_restrict_apply (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (V' : Submodule ℂ ρ.Left) (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V')
    (w : W') :
    ((ρ.restrict V' W' hA hB).rightToLeft w : ρ.Left) = ρ.rightToLeft w := rfl

/-- The coupled endomorphism on an invariant restriction commutes with inclusion into the ambient product space. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.coe_coupledEndomorphism_restrict_apply (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (V' : Submodule ℂ ρ.Left) (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V')
    (x : V' × W') :
    ((ρ.restrict V' W' hA hB).combinedEndomorphism x).map V'.subtype W'.subtype =
      ρ.combinedEndomorphism (x.map V'.subtype W'.subtype) := by
  rcases x with ⟨v, w⟩
  rw [(ρ.restrict V' W' hA hB).combinedEndomorphism_apply, ρ.combinedEndomorphism_apply]
  rfl

/-- Every power of the restricted coupled endomorphism commutes with inclusion into the ambient product space. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.coe_iterate_coupledEndomorphism_restrict_apply (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (V' : Submodule ℂ ρ.Left) (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V')
    (j : ℕ) (x : V' × W') :
    (((ρ.restrict V' W' hA hB).combinedEndomorphism ^ j) x).map
        ((V'.subtype : V' →ₗ[ℂ] ρ.Left)) ((W'.subtype : W' →ₗ[ℂ] ρ.Right)) =
      (ρ.combinedEndomorphism ^ j) (x.map V'.subtype W'.subtype) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      rw [ρ.coe_coupledEndomorphism_restrict_apply V' W' hA hB]
      exact congrArg ρ.combinedEndomorphism ih

/-- After inclusion into the ambient right space, every iterate on a restriction agrees with the ambient iterate. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.coe_iterate_restrict_apply_right (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (V' : Submodule ℂ ρ.Left) (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V')
    (j : ℕ) (w : W') :
    ((((ρ.restrict V' W' hA hB).leftToRight.comp
        (ρ.restrict V' W' hA hB).rightToLeft) ^ j) w : W') =
      ((ρ.leftToRight.comp ρ.rightToLeft) ^ j) (w : ρ.Right) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.comp_apply, LinearMap.comp_apply]
      change ρ.leftToRight (ρ.rightToLeft (↑((((ρ.restrict V' W' hA hB).leftToRight.comp
        (ρ.restrict V' W' hA hB).rightToLeft) ^ j) w : W'))) = _
      rw [ih]

/-- Nilpotency of the ambient coupled endomorphism descends to every invariant restriction. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.isNilpotent_restrict (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (V' : Submodule ℂ ρ.Left) (W' : Submodule ℂ ρ.Right)
    (hA : ∀ v ∈ V', ρ.leftToRight v ∈ W') (hB : ∀ w ∈ W', ρ.rightToLeft w ∈ V')
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    IsNilpotent ((ρ.restrict V' W' hA hB).leftToRight.comp
      (ρ.restrict V' W' hA hB).rightToLeft) := by
  obtain ⟨n, hn⟩ := hAB
  refine ⟨n, LinearMap.ext fun w => Subtype.ext ?_⟩
  rw [ρ.coe_iterate_restrict_apply_right V' W' hA hB, LinearMap.congr_fun hn]
  rfl

/-- A structure-preserving linear isomorphism between two two-space systems. -/
structure RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.Iso (τ ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) where
  /-- The forward linear map between the left component spaces. -/
  homLeft : τ.Left →ₗ[ℂ] ρ.Left
  /-- The inverse linear map between the left component spaces. -/
  invLeft : ρ.Left →ₗ[ℂ] τ.Left
  /-- The forward linear map between the right component spaces. -/
  homRight : τ.Right →ₗ[ℂ] ρ.Right
  /-- The inverse linear map between the right component spaces. -/
  invRight : ρ.Right →ₗ[ℂ] τ.Right
  /-- The inverse left-component map is a left inverse of the forward left-component map. -/
  invLeft_homLeft : ∀ v, invLeft (homLeft v) = v
  /-- The inverse right-component map is a left inverse of the forward right-component map. -/
  invRight_homRight : ∀ w, invRight (homRight w) = w
  /-- The forward component maps intertwine the map from the left space to the right space. -/
  hom_commutes_forwardMap : ∀ v,
    homRight (τ.leftToRight v) = ρ.leftToRight (homLeft v)
  /-- The forward component maps intertwine the map from the right space to the left space. -/
  hom_commutes_reverseMap : ∀ w,
    homLeft (τ.rightToLeft w) = ρ.rightToLeft (homRight w)
  /-- The inverse component maps intertwine the map from the left space to the right space. -/
  inv_commutes_forwardMap : ∀ v,
    invRight (ρ.leftToRight v) = τ.leftToRight (invLeft v)
  /-- The inverse component maps intertwine the map from the right space to the left space. -/
  inv_commutes_reverseMap : ∀ w,
    invLeft (ρ.rightToLeft w) = τ.rightToLeft (invRight w)

/-- The identity structure-preserving isomorphism of a system. -/
def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.Iso.refl (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) : ρ.Iso ρ where
  homLeft := LinearMap.id
  invLeft := LinearMap.id
  homRight := LinearMap.id
  invRight := LinearMap.id
  invLeft_homLeft := fun _ => rfl
  invRight_homRight := fun _ => rfl
  hom_commutes_forwardMap := fun _ => rfl
  hom_commutes_reverseMap := fun _ => rfl
  inv_commutes_forwardMap := fun _ => rfl
  inv_commutes_reverseMap := fun _ => rfl

/-- Composes two structure-preserving isomorphisms. -/
def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.Iso.trans {τ σ ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (e : τ.Iso σ) (f : σ.Iso ρ) :
    τ.Iso ρ where
  homLeft := f.homLeft.comp e.homLeft
  invLeft := e.invLeft.comp f.invLeft
  homRight := f.homRight.comp e.homRight
  invRight := e.invRight.comp f.invRight
  invLeft_homLeft := fun v => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.invLeft_homLeft, e.invLeft_homLeft]
  invRight_homRight := fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.invRight_homRight, e.invRight_homRight]
  hom_commutes_forwardMap := fun v => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    e.hom_commutes_forwardMap, f.hom_commutes_forwardMap]
  hom_commutes_reverseMap := fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    e.hom_commutes_reverseMap, f.hom_commutes_reverseMap]
  inv_commutes_forwardMap := fun v => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.inv_commutes_forwardMap, e.inv_commutes_forwardMap]
  inv_commutes_reverseMap := fun w => by rw [LinearMap.comp_apply, LinearMap.comp_apply,
    f.inv_commutes_reverseMap, e.inv_commutes_reverseMap]

/-- Complementary invariant subspaces give a structure-preserving isomorphism from one restriction to the ambient system. -/
noncomputable def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.restrictIso (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (pV qV : Submodule ℂ ρ.Left) (pW qW : Submodule ℂ ρ.Right)
    (hcV : IsCompl pV qV) (hcW : IsCompl pW qW)
    (hApV : ∀ v ∈ pV, ρ.leftToRight v ∈ pW) (hAqV : ∀ v ∈ qV, ρ.leftToRight v ∈ qW)
    (hBpW : ∀ w ∈ pW, ρ.rightToLeft w ∈ pV) (hBqW : ∀ w ∈ qW, ρ.rightToLeft w ∈ qV) :
    (ρ.restrict pV pW hApV hBpW).Iso ρ where
  homLeft := pV.subtype
  invLeft := pV.projectionOnto qV hcV
  homRight := pW.subtype
  invRight := pW.projectionOnto qW hcW
  invLeft_homLeft := Submodule.projectionOnto_apply_left hcV
  invRight_homRight := Submodule.projectionOnto_apply_left hcW
  hom_commutes_forwardMap := fun _ => rfl
  hom_commutes_reverseMap := fun _ => rfl
  inv_commutes_forwardMap := by
    intro v
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show v ∈ pV ⊔ qV by rw [hcV.sup_eq_top]; exact Submodule.mem_top)
    rw [← hab, map_add, map_add, map_add, map_add,
      Submodule.projectionOnto_apply_of_mem_left hcV ha,
      Submodule.projectionOnto_apply_of_mem_right hcV hb,
      Submodule.projectionOnto_apply_of_mem_left hcW (hApV a ha),
      Submodule.projectionOnto_apply_of_mem_right hcW (hAqV b hb),
      add_zero, map_zero]
    rw [add_zero]
    apply Subtype.ext
    rfl
  inv_commutes_reverseMap := by
    intro w
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show w ∈ pW ⊔ qW by rw [hcW.sup_eq_top]; exact Submodule.mem_top)
    rw [← hab, map_add, map_add, map_add, map_add,
      Submodule.projectionOnto_apply_of_mem_left hcW ha,
      Submodule.projectionOnto_apply_of_mem_right hcW hb,
      Submodule.projectionOnto_apply_of_mem_left hcV (hBpW a ha),
      Submodule.projectionOnto_apply_of_mem_right hcV (hBqW b hb),
      add_zero, map_zero]
    rw [add_zero]
    apply Subtype.ext
    rfl

/-- Nilpotency on two invariant restrictions with complementary right subspaces implies nilpotency of the full coupled endomorphism. -/
lemma RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.isNilpotent_of_isCompl_restrict (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (pV qV : Submodule ℂ ρ.Left) (pW qW : Submodule ℂ ρ.Right)
    (hcW : IsCompl pW qW)
    (hApV : ∀ v ∈ pV, ρ.leftToRight v ∈ pW) (hAqV : ∀ v ∈ qV, ρ.leftToRight v ∈ qW)
    (hBpW : ∀ w ∈ pW, ρ.rightToLeft w ∈ pV) (hBqW : ∀ w ∈ qW, ρ.rightToLeft w ∈ qV)
    (hp : IsNilpotent ((ρ.restrict pV pW hApV hBpW).leftToRight.comp
      (ρ.restrict pV pW hApV hBpW).rightToLeft))
    (hq : IsNilpotent ((ρ.restrict qV qW hAqV hBqW).leftToRight.comp
      (ρ.restrict qV qW hAqV hBqW).rightToLeft)) :
    IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft) := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, hn⟩ := hq
  refine ⟨m + n, LinearMap.ext fun w => ?_⟩
  let z := (Submodule.prodEquivOfIsCompl pW qW hcW).symm w
  have hw : (z.1 : ρ.Right) + (z.2 : ρ.Right) = w := by
    simpa [z] using (Submodule.prodEquivOfIsCompl pW qW hcW).apply_symm_apply w
  rw [← hw, map_add]
  have hp0 : ((ρ.leftToRight.comp ρ.rightToLeft) ^ (m + n)) (z.1 : ρ.Right) = 0 := by
    rw [← ρ.coe_iterate_restrict_apply_right pV pW hApV hBpW]
    rw [pow_add, hm]
    rfl
  have hq0 : ((ρ.leftToRight.comp ρ.rightToLeft) ^ (m + n)) (z.2 : ρ.Right) = 0 := by
    rw [Nat.add_comm, ← ρ.coe_iterate_restrict_apply_right qV qW hAqV hBqW]
    rw [pow_add, hn]
    rfl
  rw [hp0, hq0]
  simp

/-- Combines block decompositions on two complementary invariant restrictions into one for the ambient system. -/
noncomputable def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.NilpotentBlockDecomposition.combine
    {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ} {pV qV : Submodule ℂ ρ.Left} {pW qW : Submodule ℂ ρ.Right}
    (hcV : IsCompl pV qV) (hcW : IsCompl pW qW)
    (hApV : ∀ v ∈ pV, ρ.leftToRight v ∈ pW) (hAqV : ∀ v ∈ qV, ρ.leftToRight v ∈ qW)
    (hBpW : ∀ w ∈ pW, ρ.rightToLeft w ∈ pV) (hBqW : ∀ w ∈ qW, ρ.rightToLeft w ∈ qV)
    (cp : (ρ.restrict pV pW hApV hBpW).NilpotentBlockDecomposition)
    (cq : (ρ.restrict qV qW hAqV hBqW).NilpotentBlockDecomposition) :
    ρ.NilpotentBlockDecomposition := by
  classical
  letI : Fintype cp.Index := cp.indexFintype
  letI : Fintype cq.Index := cq.indexFintype
  let length : cp.Index ⊕ cq.Index → ℕ := Sum.elim cp.blockLength cq.blockLength
  let head : cp.Index ⊕ cq.Index → ρ.Left × ρ.Right := fun i => match i with
    | Sum.inl i => (cp.blockVector i).map pV.subtype pW.subtype
    | Sum.inr i => (cq.blockVector i).map qV.subtype qW.subtype
  let shuffle : ((pV × pW) × (qV × qW)) ≃ₗ[ℂ]
      ((pV × qV) × (pW × qW)) :=
    { toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
      invFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let total : ((pV × pW) × (qV × qW)) ≃ₗ[ℂ] (ρ.Left × ρ.Right) :=
    shuffle.trans ((Submodule.prodEquivOfIsCompl pV qV hcV).prodCongr
      (Submodule.prodEquivOfIsCompl pW qW hcW))
  let indexEquiv :
      ((Σ i, Fin (cp.blockLength i)) ⊕ (Σ i, Fin (cq.blockLength i))) ≃
        (Σ i, Fin (length i)) :=
    { toFun := Sum.elim (fun x => ⟨Sum.inl x.1, x.2⟩)
        (fun x => ⟨Sum.inr x.1, x.2⟩)
      invFun := fun x => match x with
        | ⟨Sum.inl i, j⟩ => Sum.inl ⟨i, j⟩
        | ⟨Sum.inr i, j⟩ => Sum.inr ⟨i, j⟩
      left_inv := by rintro (⟨i, j⟩ | ⟨i, j⟩) <;> rfl
      right_inv := by rintro ⟨i | i, j⟩ <;> rfl }
  let b : Module.Basis (Σ i, Fin (length i)) ℂ (ρ.Left × ρ.Right) :=
    ((cp.auxiliary.prod cq.auxiliary).map total).reindex indexEquiv
  refine {
    Index := cp.Index ⊕ cq.Index
    blockLength := length
    blockLength_pos := ?_
    blockVector := head
    blockVector_fst_eq_zero_or_snd_eq_zero := ?_
    iterate_blockVector_eq_zero := ?_
    auxiliary := b
    auxiliary_spec := ?_ }
  · rintro (i | i)
    · exact cp.blockLength_pos i
    · exact cq.blockLength_pos i
  · rintro (i | i)
    · simpa [head] using cp.blockVector_fst_eq_zero_or_snd_eq_zero i
    · simpa [head] using cq.blockVector_fst_eq_zero_or_snd_eq_zero i
  · rintro (i | i)
    · change (ρ.combinedEndomorphism ^ cp.blockLength i)
        ((cp.blockVector i).map pV.subtype pW.subtype) = 0
      calc
        _ = (((ρ.restrict pV pW hApV hBpW).combinedEndomorphism ^ cp.blockLength i)
              (cp.blockVector i)).map pV.subtype pW.subtype :=
          (ρ.coe_iterate_coupledEndomorphism_restrict_apply pV pW hApV hBpW _ _).symm
        _ = 0 := by rw [cp.iterate_blockVector_eq_zero]; rfl
    · change (ρ.combinedEndomorphism ^ cq.blockLength i)
        ((cq.blockVector i).map qV.subtype qW.subtype) = 0
      calc
        _ = (((ρ.restrict qV qW hAqV hBqW).combinedEndomorphism ^ cq.blockLength i)
              (cq.blockVector i)).map qV.subtype qW.subtype :=
          (ρ.coe_iterate_coupledEndomorphism_restrict_apply qV qW hAqV hBqW _ _).symm
        _ = 0 := by rw [cq.iterate_blockVector_eq_zero]; rfl
  · rintro ⟨i | i, j⟩
    · rw [show b ⟨Sum.inl i, j⟩ = total (cp.auxiliary ⟨i, j⟩, 0) by
        simp [b, indexEquiv, Module.Basis.prod_apply]]
      rw [cp.auxiliary_spec]
      rw [show total
          (((ρ.restrict pV pW hApV hBpW).combinedEndomorphism ^ (j : ℕ)) (cp.blockVector i), 0) =
          (((ρ.restrict pV pW hApV hBpW).combinedEndomorphism ^ (j : ℕ))
            (cp.blockVector i)).map pV.subtype pW.subtype by
        change
          (Submodule.prodEquivOfIsCompl pV qV hcV
              ((((ρ.restrict pV pW hApV hBpW).combinedEndomorphism ^ (j : ℕ))
                (cp.blockVector i)).1, (0 : qV)),
            Submodule.prodEquivOfIsCompl pW qW hcW
              ((((ρ.restrict pV pW hApV hBpW).combinedEndomorphism ^ (j : ℕ))
                (cp.blockVector i)).2, (0 : qW))) = _
        simp only [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero, Prod.map]
        rfl]
      change _ = (ρ.combinedEndomorphism ^ (j : ℕ))
        ((cp.blockVector i).map pV.subtype pW.subtype)
      exact ρ.coe_iterate_coupledEndomorphism_restrict_apply pV pW hApV hBpW (j : ℕ) (cp.blockVector i)
    · rw [show b ⟨Sum.inr i, j⟩ = total (0, cq.auxiliary ⟨i, j⟩) by
        simp [b, indexEquiv, Module.Basis.prod_apply]]
      rw [cq.auxiliary_spec]
      rw [show total
          (0, ((ρ.restrict qV qW hAqV hBqW).combinedEndomorphism ^ (j : ℕ)) (cq.blockVector i)) =
          (((ρ.restrict qV qW hAqV hBqW).combinedEndomorphism ^ (j : ℕ))
            (cq.blockVector i)).map qV.subtype qW.subtype by
        change
          (Submodule.prodEquivOfIsCompl pV qV hcV
              ((0 : pV), (((ρ.restrict qV qW hAqV hBqW).combinedEndomorphism ^ (j : ℕ))
                (cq.blockVector i)).1),
            Submodule.prodEquivOfIsCompl pW qW hcW
              ((0 : pW), (((ρ.restrict qV qW hAqV hBqW).combinedEndomorphism ^ (j : ℕ))
                (cq.blockVector i)).2)) = _
        simp only [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, zero_add, Prod.map]
        rfl]
      change _ = (ρ.combinedEndomorphism ^ (j : ℕ))
        ((cq.blockVector i).map qV.subtype qW.subtype)
      exact ρ.coe_iterate_coupledEndomorphism_restrict_apply qV qW hAqV hBqW (j : ℕ) (cq.blockVector i)

private lemma aeval_equiv_pow_intertwines
    {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N]
    (S : Module.End ℂ M) (T : Module.End ℂ N)
    (e : Module.AEval' S ≃ₗ[Polynomial ℂ] Module.AEval' T)
    (j : ℕ) (x : M) :
    (Module.AEval'.of T).symm
        (e (Module.AEval'.of S ((S ^ j) x))) =
      (T ^ j) ((Module.AEval'.of T).symm (e (Module.AEval'.of S x))) := by
  have hST (y : M) :
      (Module.AEval'.of T).symm (e (Module.AEval'.of S (S y))) =
        T ((Module.AEval'.of T).symm (e (Module.AEval'.of S y))) := by
    apply (Module.AEval'.of T).injective
    rw [(Module.AEval'.of T).apply_symm_apply]
    rw [← Module.AEval'.X_smul_of, ← Module.AEval'.X_smul_of, e.map_smul]
    simp
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      rw [ih (x := S x), hST]

/-- A nilpotent system whose coupled endomorphism has one-dimensional kernel admits cyclic basis data. -/
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.nonempty_cyclicBasisData_of_ker_finrank_eq_one
    (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hker : Module.finrank ℂ (LinearMap.ker ρ.combinedEndomorphism) = 1) :
    Nonempty ρ.CyclicBasisData := by
  classical
  let T := ρ.combinedEndomorphism
  have hT : IsNilpotent T := RepresentationTheory.FiniteDimensionalLinearMapPair.combinedEndomorphism_isNilpotent_of_comp_isNilpotent ρ hAB
  have hindecomp : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial ℂ) (Module.AEval' T) :=
    RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryPolynomialProperty_of_isNilpotent_finrank_ker_eq_one T hT hker
  obtain ⟨lam, n, hn, ⟨e⟩⟩ :=
    RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_jordanBlock_of_isIndecomposableModule
      (k := ℂ) (M := Module.AEval' T) hindecomp
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let ofT := Module.AEval'.of (R := ℂ) T
  let J := RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator lam n
  let ofJ := Module.AEval'.of (R := ℂ) J
  have hlam : lam = 0 := by
    obtain ⟨m, hm⟩ := hT
    let y := e.symm (ofJ (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector n))
    have hy : (Polynomial.X ^ m : Polynomial ℂ) • y = 0 := by
      let z := ofT.symm y
      rw [show y = ofT z by simp [z]]
      change ofT (Polynomial.aeval T (Polynomial.X ^ m) z) = 0
      rw [map_pow, Polynomial.aeval_X, hm]
      simp
    have hy' := congrArg e hy
    rw [map_smul, e.apply_symm_apply, map_zero] at hy'
    change ofJ (Polynomial.aeval J (Polynomial.X ^ m)
      (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector n)) = 0 at hy'
    rw [map_pow, Polynomial.aeval_X] at hy'
    have hJpow : (J ^ m) (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector n) = 0 :=
      ofJ.injective (by simpa using hy')
    have heigen : ∀ r : ℕ, (J ^ r) (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector n) =
        lam ^ r • (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector n : Fin n → ℂ) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          rw [pow_succ', Module.End.mul_apply, ih, map_smul]
          rw [RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator_jordanEigenvector, smul_smul, pow_succ']
          simp [mul_comm]
    rw [heigen] at hJpow
    by_contra hne
    exact (pow_ne_zero m hne)
      ((smul_eq_zero.mp hJpow).resolve_right
        (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector_ne_zero n))
  subst lam
  change Module.AEval' T ≃ₗ[Polynomial ℂ]
    RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.JordanBlockModule 0 n at e
  let F : (ρ.Left × ρ.Right) ≃ₗ[ℂ] (Fin n → ℂ) :=
    ofT.trans ((e.restrictScalars ℂ).trans ofJ.symm)
  have hJ : J = RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n := by
    simp [J, RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator]
  have hFpow (j : ℕ) (x : ρ.Left × ρ.Right) :
      F ((T ^ j) x) = (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n ^ j) (F x) := by
    change ofJ.symm (e (ofT ((T ^ j) x))) =
      (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n ^ j) (ofJ.symm (e (ofT x)))
    have hh := aeval_equiv_pow_intertwines T J
      (show Module.AEval' T ≃ₗ[Polynomial ℂ] Module.AEval' J from e) j x
    calc
      ofJ.symm (e (ofT ((T ^ j) x))) = (J ^ j) (ofJ.symm (e (ofT x))) := hh
      _ = (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n ^ j) (ofJ.symm (e (ofT x))) := by rw [hJ]
  have hdim : Module.finrank ℂ (ρ.Left × ρ.Right) = n := by
    calc
      Module.finrank ℂ (ρ.Left × ρ.Right) = Module.finrank ℂ (Fin n → ℂ) := F.finrank_eq
      _ = n := by simp
  let g := F.symm (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanCyclicVector n)
  have hgmax : (T ^ (n - 1)) g ≠ 0 := by
    intro h
    have h' := congrArg F h
    rw [hFpow, map_zero, F.apply_symm_apply,
      RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent_pow_jordanCyclicVector n (by omega)] at h'
    apply RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanEigenvector_ne_zero (k := ℂ) n
    have hindex : (⟨n - 1 - (n - 1), by omega⟩ : Fin n) = 0 := by
      apply Fin.ext
      simp
    rw [hindex] at h'
    exact h'
  rcases g with ⟨v, w⟩
  have hpure : (T ^ (n - 1)) (v, (0 : ρ.Right)) ≠ 0 ∨
      (T ^ (n - 1)) ((0 : ρ.Left), w) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨hv0, hw0⟩ := h
    apply hgmax
    rw [show (v, w) = (v, (0 : ρ.Right)) + ((0 : ρ.Left), w) by simp,
      map_add, hv0, hw0, add_zero]
  obtain ⟨p, hpmax, hppure⟩ : ∃ p : ρ.Left × ρ.Right,
      (T ^ (n - 1)) p ≠ 0 ∧ (p.1 = 0 ∨ p.2 = 0) := by
    rcases hpure with hv | hw
    · exact ⟨(v, 0), hv, Or.inr rfl⟩
    · exact ⟨(0, w), hw, Or.inl rfl⟩
  let q := F p
  have hqmax : (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n ^ (n - 1)) q ≠ 0 := by
    simpa [q, hFpow] using F.injective.ne hpmax
  have hqlast : q ⟨n - 1, by omega⟩ ≠ 0 := by
    intro hlast
    apply hqmax
    funext i
    rw [RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.auxiliaryFact_aux2]
    split_ifs with hi
    · have hval : (i : ℕ) + (n - 1) = n - 1 := by omega
      have hidx : (⟨(i : ℕ) + (n - 1), hi⟩ : Fin n) =
          ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        exact hval
      rw [hidx, hlast]
      rfl
    · rfl
  have hliQ : LinearIndependent ℂ (fun i : Fin n =>
      (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n ^ (i : ℕ)) q) :=
    RepresentationTheory.FiniteDimensionalLinearMapPair.linearIndependent_iterates_of_last_ne_zero n hn q hqlast
  have hli : LinearIndependent ℂ (fun i : Fin n => (T ^ (i : ℕ)) p) := by
    apply LinearIndependent.of_comp F.toLinearMap
    convert hliQ using 1
    funext i
    exact hFpow (i : ℕ) p
  let b : Module.Basis (Fin n) ℂ (ρ.Left × ρ.Right) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])
  have hb (i : Fin n) : b i = (T ^ (i : ℕ)) p := by
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])) i
  have hkill : (T ^ n) p = 0 := by
    apply F.injective
    rw [hFpow, map_zero, RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent_pow_eq_zero]
    rfl
  exact ⟨{
    length := n
    length_pos := hn
    cyclicVector := p
    cyclicVector_fst_eq_zero_or_snd_eq_zero := hppure
    iterate_cyclicVector_eq_zero := hkill
    basis := b
    basis_apply := hb }⟩

/-- A compatible nilpotent system with both component spaces nontrivial admits cyclic basis data. -/
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.nonempty_cyclicBasisData_of_isNilpotent (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (hρ : ρ.AuxiliaryCondition) (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft))
    (hV : 0 < Module.finrank ℂ ρ.Left) (hW : 0 < Module.finrank ℂ ρ.Right) :
    Nonempty ρ.CyclicBasisData :=
  RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.nonempty_cyclicBasisData_of_ker_finrank_eq_one ρ hAB
    (RepresentationTheory.FiniteDimensionalLinearMapPair.finrank_ker_combinedEndomorphism_eq_one ρ hρ hAB hV hW)

/-- A system whose alternating composite is nilpotent admits a block decomposition. -/
@[source_ref "Chapter6/Problem6.9.1" (role := primary)]
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.nonempty_nilpotentBlockDecomposition (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    Nonempty ρ.NilpotentBlockDecomposition := by
  classical
  suffices h : ∀ d : ℕ, ∀ σ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ,
      Module.finrank ℂ σ.Left + Module.finrank ℂ σ.Right = d →
      IsNilpotent (σ.leftToRight.comp σ.rightToLeft) → Nonempty σ.NilpotentBlockDecomposition by
    exact h _ ρ rfl hAB
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro σ hdim hABσ
      by_cases hd0 : d = 0
      · have hV0 : Module.finrank ℂ σ.Left = 0 := by omega
        have hW0 : Module.finrank ℂ σ.Right = 0 := by omega
        letI : Subsingleton σ.Left := Module.finrank_zero_iff.mp hV0
        letI : Subsingleton σ.Right := Module.finrank_zero_iff.mp hW0
        exact ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.NilpotentBlockDecomposition.of_subsingleton σ⟩
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        have hprodpos : 0 < Module.finrank ℂ (σ.Left × σ.Right) := by
          rw [Module.finrank_prod, hdim]
          exact hdpos
        letI : Nontrivial (σ.Left × σ.Right) := Module.finrank_pos_iff.mp hprodpos
        have hX : IsNilpotent σ.combinedEndomorphism := RepresentationTheory.FiniteDimensionalLinearMapPair.combinedEndomorphism_isNilpotent_of_comp_isNilpotent σ hABσ
        obtain ⟨x, hxne, hx0⟩ :=
          RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.exists_ne_zero_mem_ker_of_isNilpotent σ.combinedEndomorphism hX
        have hxmem : x ∈ LinearMap.ker σ.combinedEndomorphism := LinearMap.mem_ker.mpr hx0
        have hkerne : Module.finrank ℂ (LinearMap.ker σ.combinedEndomorphism) ≠ 0 := by
          intro hzero
          have hbot : LinearMap.ker σ.combinedEndomorphism = ⊥ :=
            Submodule.finrank_eq_zero.mp hzero
          apply hxne
          exact (Submodule.mem_bot ℂ).mp (hbot ▸ hxmem)
        have hkerpos : 0 < Module.finrank ℂ (LinearMap.ker σ.combinedEndomorphism) :=
          Nat.pos_of_ne_zero hkerne
        by_cases hker1 : Module.finrank ℂ (LinearMap.ker σ.combinedEndomorphism) = 1
        · obtain ⟨c⟩ :=
            RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.nonempty_cyclicBasisData_of_ker_finrank_eq_one
              σ hABσ hker1
          exact ⟨c.toNilpotentBlockDecomposition⟩
        · have hker2 : 2 ≤ Module.finrank ℂ (LinearMap.ker σ.combinedEndomorphism) := by
            omega
          have hkerSum : 2 ≤ Module.finrank ℂ (LinearMap.ker σ.leftToRight) +
              Module.finrank ℂ (LinearMap.ker σ.rightToLeft) := by
            rw [← σ.finrank_ker_combinedEndomorphism]
            exact hker2
          obtain ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW,
              hpne, hqne⟩ :=
            RepresentationTheory.FiniteDimensionalLinearMapPair.exists_nontrivial_compatible_complements σ.leftToRight σ.rightToLeft hABσ hkerSum
          have hdimV : Module.finrank ℂ pV + Module.finrank ℂ qV =
              Module.finrank ℂ σ.Left := by
            simpa [Module.finrank_prod] using
              (Submodule.prodEquivOfIsCompl pV qV hcV).finrank_eq
          have hdimW : Module.finrank ℂ pW + Module.finrank ℂ qW =
              Module.finrank ℂ σ.Right := by
            simpa [Module.finrank_prod] using
              (Submodule.prodEquivOfIsCompl pW qW hcW).finrank_eq
          have hpdim : 0 < Module.finrank ℂ pV + Module.finrank ℂ pW := by
            by_contra hzero
            apply hpne
            constructor
            · apply Submodule.finrank_eq_zero.mp
              omega
            · apply Submodule.finrank_eq_zero.mp
              omega
          have hqdim : 0 < Module.finrank ℂ qV + Module.finrank ℂ qW := by
            by_contra hzero
            apply hqne
            constructor
            · apply Submodule.finrank_eq_zero.mp
              omega
            · apply Submodule.finrank_eq_zero.mp
              omega
          have hp_lt : Module.finrank ℂ pV + Module.finrank ℂ pW < d := by
            omega
          have hq_lt : Module.finrank ℂ qV + Module.finrank ℂ qW < d := by
            omega
          let σp := σ.restrict pV pW hApV hBpW
          let σq := σ.restrict qV qW hAqV hBqW
          have hABp : IsNilpotent (σp.leftToRight.comp σp.rightToLeft) :=
            σ.isNilpotent_restrict pV pW hApV hBpW hABσ
          have hABq : IsNilpotent (σq.leftToRight.comp σq.rightToLeft) :=
            σ.isNilpotent_restrict qV qW hAqV hBqW hABσ
          obtain ⟨cp⟩ := ih _ hp_lt σp rfl hABp
          obtain ⟨cq⟩ := ih _ hq_lt σq rfl hABq
          exact ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.NilpotentBlockDecomposition.combine hcV hcW hApV hAqV
            hBpW hBqW cp cq⟩

private lemma chain_pow_parity_of_snd_zero {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ} (p : ρ.Left × ρ.Right)
    (hp : p.2 = 0) (i : ℕ) :
    ((ρ.combinedEndomorphism ^ (2 * i)) p).2 = 0 ∧
      ((ρ.combinedEndomorphism ^ (2 * i + 1)) p).1 = 0 := by
  induction i with
  | zero =>
      constructor
      · simpa using hp
      · simp [pow_succ', ρ.combinedEndomorphism_apply, hp]
  | succ i ih =>
      constructor
      · rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.combinedEndomorphism_apply]
        exact map_zero ρ.leftToRight ▸ congrArg ρ.leftToRight ih.2
      · rw [show 2 * (i + 1) + 1 = (2 * i + 2) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.combinedEndomorphism_apply]
        exact map_zero ρ.rightToLeft ▸ congrArg ρ.rightToLeft (by
          rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega, pow_succ',
            Module.End.mul_apply, ρ.combinedEndomorphism_apply]
          exact map_zero ρ.leftToRight ▸ congrArg ρ.leftToRight ih.2)

private lemma chain_pow_parity_of_fst_zero {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ} (p : ρ.Left × ρ.Right)
    (hp : p.1 = 0) (i : ℕ) :
    ((ρ.combinedEndomorphism ^ (2 * i)) p).1 = 0 ∧
      ((ρ.combinedEndomorphism ^ (2 * i + 1)) p).2 = 0 := by
  induction i with
  | zero =>
      constructor
      · simpa using hp
      · simp [pow_succ', ρ.combinedEndomorphism_apply, hp]
  | succ i ih =>
      constructor
      · rw [show 2 * (i + 1) = (2 * i + 1) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.combinedEndomorphism_apply]
        exact map_zero ρ.rightToLeft ▸ congrArg ρ.rightToLeft ih.2
      · rw [show 2 * (i + 1) + 1 = (2 * i + 2) + 1 by omega, pow_succ',
          Module.End.mul_apply, ρ.combinedEndomorphism_apply]
        exact map_zero ρ.leftToRight ▸ congrArg ρ.leftToRight (by
          rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega, pow_succ',
            Module.End.mul_apply, ρ.combinedEndomorphism_apply]
          exact map_zero ρ.rightToLeft ▸ congrArg ρ.rightToLeft ih.2)

private lemma Q₂Rep_E_zero_A_basis (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn 0).leftToRight ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j) =
      if h : j.val + 1 < n then
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis ⟨j.val + 1, h⟩ else 0 := by
  split_ifs with hj
  all_goals
    apply WithLp.ofLp_injective
    funext i
    simp only [RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    simp [Fin.ext_iff]
    all_goals omega

private lemma Q₂Rep_H_A_basis (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB n hn).leftToRight ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j) =
      if h : j.val < n - 1 then
        (EuclideanSpace.basisFun (Fin (n - 1)) ℂ).toBasis ⟨j.val, h⟩ else 0 := by
  split_ifs with hj
  all_goals
    apply WithLp.ofLp_injective
    funext i
    simp only [RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
    simp [Fin.ext_iff]
    all_goals omega

private lemma Q₂Rep_H_B_basis (n : ℕ) (hn : 0 < n) (j : Fin (n - 1)) :
    (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB n hn).rightToLeft
        ((EuclideanSpace.basisFun (Fin (n - 1)) ℂ).toBasis j) =
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis ⟨j.val + 1, by omega⟩ := by
  apply WithLp.ofLp_injective
  funext i
  simp only [RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Fin.ext_iff]

private theorem pureChain_even_snd_zero_iso {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) (m : ℕ) (hm : 0 < m) (hlen : c.length = 2 * m)
    (hp : c.cyclicVector.2 = 0) :
    Nonempty (ρ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelA m hm)) := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let vchain : Fin m → ρ.Left := fun i =>
    ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector).1
  let wchain : Fin m → ρ.Right := fun i =>
    ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector).2
  let evenIndex : Fin m → Fin c.length := fun i => ⟨2 * (i : ℕ), by rw [hlen]; omega⟩
  let oddIndex : Fin m → Fin c.length := fun i => ⟨2 * (i : ℕ) + 1, by rw [hlen]; omega⟩
  have heven_inj : Function.Injective evenIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [evenIndex] at this
    omega
  have hodd_inj : Function.Injective oddIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [oddIndex] at this
    omega
  have hliV : LinearIndependent ℂ vchain := by
    apply LinearIndependent.of_comp (LinearMap.inl ℂ ρ.Left ρ.Right)
    have hsub := c.basis.linearIndependent.comp evenIndex heven_inj
    convert hsub using 1
    funext i
    change (vchain i, (0 : ρ.Right)) = c.basis (evenIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · rfl
    · simpa [evenIndex] using (chain_pow_parity_of_snd_zero c.cyclicVector hp (i : ℕ)).1.symm
  have hliW : LinearIndependent ℂ wchain := by
    apply LinearIndependent.of_comp (LinearMap.inr ℂ ρ.Left ρ.Right)
    have hsub := c.basis.linearIndependent.comp oddIndex hodd_inj
    convert hsub using 1
    funext i
    change ((0 : ρ.Left), wchain i) = c.basis (oddIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · simpa [oddIndex] using (chain_pow_parity_of_snd_zero c.cyclicVector hp (i : ℕ)).2.symm
    · rfl
  have hsum : Module.finrank ℂ ρ.Left + Module.finrank ℂ ρ.Right = 2 * m := by
    rw [← Module.finrank_prod]
    simpa [hlen] using Module.finrank_eq_card_basis c.basis
  have hdimV : Module.finrank ℂ ρ.Left = m := by
    have hleV := hliV.fintype_card_le_finrank
    have hleW := hliW.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hleV hleW
    omega
  have hdimW : Module.finrank ℂ ρ.Right = m := by omega
  let bV : Module.Basis (Fin m) ℂ ρ.Left :=
    basisOfLinearIndependentOfCardEqFinrank hliV (by rw [Fintype.card_fin, hdimV])
  let bW : Module.Basis (Fin m) ℂ ρ.Right :=
    basisOfLinearIndependentOfCardEqFinrank hliW (by rw [Fintype.card_fin, hdimW])
  have hbV (i : Fin m) : bV i = vchain i :=
    congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hliV (by rw [Fintype.card_fin, hdimV])) i
  have hbW (i : Fin m) : bW i = wchain i :=
    congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hliW (by rw [Fintype.card_fin, hdimW])) i
  let std := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
  let eV : ρ.Left ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) := bV.equiv std (Equiv.refl _)
  let eW : ρ.Right ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) := bW.equiv std (Equiv.refl _)
  have hAchain (i : Fin m) : ρ.leftToRight (vchain i) = wchain i := by
    change ρ.leftToRight ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector).1 =
      ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector).2
    have hstep : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector =
        ρ.combinedEndomorphism ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector) := by
      rw [pow_succ', Module.End.mul_apply]
    have hs := congrArg Prod.snd hstep
    rw [ρ.combinedEndomorphism_apply] at hs
    exact hs.symm
  have hBchain (i : Fin m) : ρ.rightToLeft (wchain i) =
      if h : i.val + 1 < m then vchain ⟨i.val + 1, h⟩ else 0 := by
    split_ifs with hi
    · have hstep : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 2)) c.cyclicVector =
          ρ.combinedEndomorphism ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector) := by
        rw [show 2 * (i : ℕ) + 2 = (2 * (i : ℕ) + 1) + 1 by omega,
          pow_succ', Module.End.mul_apply]
      change ρ.rightToLeft ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector).2 =
        ((ρ.combinedEndomorphism ^ (2 * ((⟨i.val + 1, hi⟩ : Fin m) : ℕ))) c.cyclicVector).1
      have hs := congrArg Prod.fst hstep
      rw [ρ.combinedEndomorphism_apply] at hs
      rw [show 2 * ((⟨i.val + 1, hi⟩ : Fin m) : ℕ) =
        2 * (i : ℕ) + 2 by simp; omega]
      exact hs.symm
    · have hilast : (i : ℕ) = m - 1 := by omega
      have hkill : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 2)) c.cyclicVector = 0 := by
        rw [show 2 * (i : ℕ) + 2 = c.length by omega]
        exact c.iterate_cyclicVector_eq_zero
      have hstep : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 2)) c.cyclicVector =
          ρ.combinedEndomorphism ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector) := by
        rw [show 2 * (i : ℕ) + 2 = (2 * (i : ℕ) + 1) + 1 by omega,
          pow_succ', Module.End.mul_apply]
      have := congrArg Prod.fst (hstep.symm.trans hkill)
      simpa [ρ.combinedEndomorphism_apply] using this
  have hmapA : eW.toLinearMap.comp ρ.leftToRight = eV.toLinearMap := by
    apply bV.ext
    intro i
    simp only [LinearMap.comp_apply]
    rw [hbV, hAchain, ← hbW, ← hbV]
    simp [eV, eW, std]
  have hmapB_basis (i : Fin m) : eV (ρ.rightToLeft (bW i)) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel m hm 0).leftToRight (eW (bW i)) := by
    rw [hbW, hBchain]
    split_ifs with hi
    · rw [← hbV, ← hbW]
      simp only [eV, eW, std, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_E_zero_A_basis m hm i).symm
    · rw [map_zero]
      rw [← hbW]
      simp only [eW, std, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_E_zero_A_basis m hm i).symm
  have hmapB (x : ρ.Right) : eV (ρ.rightToLeft x) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel m hm 0).leftToRight (eW x) := by
    rw [← bW.sum_repr x]
    simp only [map_sum, map_smul]
    simp_rw [hmapB_basis]
  exact ⟨{
    leftMap := eV
    rightMap := eW
    rightMap_leftToRight := fun x => by
      simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelA, RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.dual, RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel] using
        LinearMap.congr_fun hmapA x
    leftMap_rightToLeft := fun x => by
      change eV (ρ.rightToLeft x) = (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel m hm 0).leftToRight (eW x)
      exact hmapB x }⟩

private theorem pureChain_odd_snd_zero_iso {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) (m : ℕ) (hlen : c.length = 2 * m + 1)
    (hp : c.cyclicVector.2 = 0) :
    Nonempty (ρ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB (m + 1) (by omega))) := by
  classical
  have hn : 0 < m + 1 := by omega
  let vchain : Fin (m + 1) → ρ.Left := fun i =>
    ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector).1
  let wchain : Fin m → ρ.Right := fun i =>
    ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector).2
  let evenIndex : Fin (m + 1) → Fin c.length := fun i =>
    ⟨2 * (i : ℕ), by rw [hlen]; omega⟩
  let oddIndex : Fin m → Fin c.length := fun i =>
    ⟨2 * (i : ℕ) + 1, by rw [hlen]; omega⟩
  have heven_inj : Function.Injective evenIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [evenIndex] at this
    omega
  have hodd_inj : Function.Injective oddIndex := by
    intro i j hij
    apply Fin.ext
    have := congrArg Fin.val hij
    dsimp [oddIndex] at this
    omega
  have hliV : LinearIndependent ℂ vchain := by
    apply LinearIndependent.of_comp (LinearMap.inl ℂ ρ.Left ρ.Right)
    have hsub := c.basis.linearIndependent.comp evenIndex heven_inj
    convert hsub using 1
    funext i
    change (vchain i, (0 : ρ.Right)) = c.basis (evenIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · rfl
    · simpa [evenIndex] using (chain_pow_parity_of_snd_zero c.cyclicVector hp (i : ℕ)).1.symm
  have hliW : LinearIndependent ℂ wchain := by
    apply LinearIndependent.of_comp (LinearMap.inr ℂ ρ.Left ρ.Right)
    have hsub := c.basis.linearIndependent.comp oddIndex hodd_inj
    convert hsub using 1
    funext i
    change ((0 : ρ.Left), wchain i) = c.basis (oddIndex i)
    rw [c.basis_apply]
    apply Prod.ext
    · simpa [oddIndex] using (chain_pow_parity_of_snd_zero c.cyclicVector hp (i : ℕ)).2.symm
    · rfl
  have hsum : Module.finrank ℂ ρ.Left + Module.finrank ℂ ρ.Right = 2 * m + 1 := by
    rw [← Module.finrank_prod]
    simpa [hlen] using Module.finrank_eq_card_basis c.basis
  have hdimV : Module.finrank ℂ ρ.Left = m + 1 := by
    have hleV := hliV.fintype_card_le_finrank
    have hleW := hliW.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hleV hleW
    omega
  have hdimW : Module.finrank ℂ ρ.Right = m := by omega
  let bV : Module.Basis (Fin (m + 1)) ℂ ρ.Left :=
    basisOfLinearIndependentOfCardEqFinrank' vchain hliV
      (by rw [Fintype.card_fin, hdimV])
  let bW : Module.Basis (Fin m) ℂ ρ.Right :=
    basisOfLinearIndependentOfCardEqFinrank' wchain hliW
      (by rw [Fintype.card_fin, hdimW])
  have hbV (i : Fin (m + 1)) : bV i = vchain i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' vchain hliV
      (by rw [Fintype.card_fin, hdimV])) i
  have hbW (i : Fin m) : bW i = wchain i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' wchain hliW
      (by rw [Fintype.card_fin, hdimW])) i
  let stdV := (EuclideanSpace.basisFun (Fin (m + 1)) ℂ).toBasis
  let stdW := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
  let eV : ρ.Left ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (m + 1)) := bV.equiv stdV (Equiv.refl _)
  let eW : ρ.Right ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m) := bW.equiv stdW (Equiv.refl _)
  have hAchain (i : Fin (m + 1)) : ρ.leftToRight (vchain i) =
      if h : i.val < m then wchain ⟨i.val, h⟩ else 0 := by
    split_ifs with hi
    · change ρ.leftToRight ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector).1 =
        ((ρ.combinedEndomorphism ^ (2 * ((⟨i.val, hi⟩ : Fin m) : ℕ) + 1)) c.cyclicVector).2
      have hstep : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector =
          ρ.combinedEndomorphism ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector) := by
        rw [pow_succ', Module.End.mul_apply]
      have hs := congrArg Prod.snd hstep
      rw [ρ.combinedEndomorphism_apply] at hs
      simpa using hs.symm
    · have hilast : (i : ℕ) = m := by omega
      have hkill : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector = 0 := by
        rw [show 2 * (i : ℕ) + 1 = c.length by omega]
        exact c.iterate_cyclicVector_eq_zero
      have hstep : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector =
          ρ.combinedEndomorphism ((ρ.combinedEndomorphism ^ (2 * (i : ℕ))) c.cyclicVector) := by
        rw [pow_succ', Module.End.mul_apply]
      have hs := congrArg Prod.snd (hstep.symm.trans hkill)
      simpa [ρ.combinedEndomorphism_apply] using hs
  have hBchain (i : Fin m) : ρ.rightToLeft (wchain i) =
      vchain ⟨i.val + 1, by omega⟩ := by
    change ρ.rightToLeft ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector).2 =
      ((ρ.combinedEndomorphism ^ (2 * ((⟨i.val + 1, by omega⟩ : Fin (m + 1)) : ℕ))) c.cyclicVector).1
    have hstep : (ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 2)) c.cyclicVector =
        ρ.combinedEndomorphism ((ρ.combinedEndomorphism ^ (2 * (i : ℕ) + 1)) c.cyclicVector) := by
      rw [show 2 * (i : ℕ) + 2 = (2 * (i : ℕ) + 1) + 1 by omega,
        pow_succ', Module.End.mul_apply]
    have hs := congrArg Prod.fst hstep
    rw [ρ.combinedEndomorphism_apply] at hs
    rw [show 2 * ((⟨i.val + 1, by omega⟩ : Fin (m + 1)) : ℕ) =
      2 * (i : ℕ) + 2 by simp; omega]
    exact hs.symm
  have hmapA_basis (i : Fin (m + 1)) : eW (ρ.leftToRight (bV i)) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB (m + 1) hn).leftToRight (eV (bV i)) := by
    rw [hbV, hAchain]
    split_ifs with hi
    · rw [← hbW, ← hbV]
      simp only [eV, eW, stdV, stdW, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_H_A_basis (m + 1) hn i).symm
    · rw [map_zero, ← hbV]
      simp only [eV, stdV, Module.Basis.equiv_apply]
      simpa [hi] using (Q₂Rep_H_A_basis (m + 1) hn i).symm
  have hmapB_basis (i : Fin m) : eV (ρ.rightToLeft (bW i)) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB (m + 1) hn).rightToLeft (eW (bW i)) := by
    rw [hbW, hBchain, ← hbV, ← hbW]
    simp only [eV, eW, stdV, stdW, Module.Basis.equiv_apply]
    simpa using (Q₂Rep_H_B_basis (m + 1) hn i).symm
  have hmapA (x : ρ.Left) : eW (ρ.leftToRight x) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB (m + 1) hn).leftToRight (eV x) := by
    rw [← bV.sum_repr x]
    simp only [map_sum, map_smul]
    simp_rw [hmapA_basis]
  have hmapB (x : ρ.Right) : eV (ρ.rightToLeft x) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB (m + 1) hn).rightToLeft (eW x) := by
    rw [← bW.sum_repr x]
    simp only [map_sum, map_smul]
    simp_rw [hmapB_basis]
  exact ⟨{
    leftMap := eV
    rightMap := eW
    rightMap_leftToRight := hmapA
    leftMap_rightToLeft := hmapB }⟩

/-- Transports a relation between systems through the operation that exchanges their component spaces. -/
def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.Equiv.transform {k : Type*} [Field k] {ρ σ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair k}
    (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual where
  leftMap := e.rightMap
  rightMap := e.leftMap
  rightMap_leftToRight := e.leftMap_rightToLeft
  leftMap_rightToLeft := e.rightMap_leftToRight

private lemma chainOperator_swap_intertwines (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (j : ℕ)
    (x : ρ.Left × ρ.Right) :
    ((ρ.dual.combinedEndomorphism ^ j) ((LinearEquiv.prodComm ℂ ρ.Left ρ.Right) x)) =
      (LinearEquiv.prodComm ℂ ρ.Left ρ.Right) ((ρ.combinedEndomorphism ^ j) x) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      rcases (ρ.combinedEndomorphism ^ j) x with ⟨v, w⟩
      simp only [LinearEquiv.prodComm_apply, Prod.swap_prod_mk]
      rw [ρ.combinedEndomorphism_apply, ρ.dual.combinedEndomorphism_apply]
      rfl

/-- Exchanges the component spaces in cyclic basis data along the corresponding system transformation. -/
noncomputable def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.CyclicBasisData.transform {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) : ρ.dual.CyclicBasisData where
  length := c.length
  length_pos := c.length_pos
  cyclicVector := (LinearEquiv.prodComm ℂ ρ.Left ρ.Right) c.cyclicVector
  cyclicVector_fst_eq_zero_or_snd_eq_zero := by simpa using c.cyclicVector_fst_eq_zero_or_snd_eq_zero.symm
  iterate_cyclicVector_eq_zero := by
    rw [chainOperator_swap_intertwines]
    rw [c.iterate_cyclicVector_eq_zero, map_zero]
  basis := c.basis.map (LinearEquiv.prodComm ℂ ρ.Left ρ.Right)
  basis_apply := by
    intro i
    rw [Module.Basis.map_apply, c.basis_apply]
    exact (chainOperator_swap_intertwines ρ (i : ℕ) c.cyclicVector).symm

/-- Applying the component-exchanging transformation twice produces a system related to the original one. -/
def RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.doubleTransformRelation {k : Type*} [Field k] (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair k) :
    ρ.dual.dual.Equiv ρ where
  leftMap := LinearEquiv.refl k ρ.Left
  rightMap := LinearEquiv.refl k ρ.Right
  rightMap_leftToRight := fun _ => rfl
  leftMap_rightToLeft := fun _ => rfl

private theorem pureChain_even_fst_zero_iso {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) (m : ℕ) (hm : 0 < m) (hlen : c.length = 2 * m)
    (hp : c.cyclicVector.1 = 0) :
    Nonempty (ρ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel m hm 0)) := by
  obtain ⟨e⟩ := pureChain_even_snd_zero_iso c.transform m hm hlen hp
  let f := (RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.doubleTransformRelation ρ).symm.trans e.transform
  exact ⟨by simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelA, RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.dual] using f⟩

private theorem pureChain_odd_fst_zero_iso {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) (m : ℕ) (hlen : c.length = 2 * m + 1)
    (hp : c.cyclicVector.1 = 0) :
    Nonempty (ρ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelC (m + 1) (by omega))) := by
  obtain ⟨e⟩ := pureChain_odd_snd_zero_iso c.transform m hlen hp
  let f := (RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.doubleTransformRelation ρ).symm.trans e.transform
  exact ⟨by simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelC] using f⟩

/-- Cyclic basis data supplies the associated auxiliary property. -/
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.Auxiliary.property_of_cyclicBasisData {ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ}
    (c : ρ.CyclicBasisData) : RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryPredicate ρ := by
  obtain ⟨m, hlen | hlen⟩ := c.length.even_or_odd'
  · have hm : 0 < m := by
      have hpos := c.length_pos
      rw [hlen] at hpos
      omega
    rcases c.cyclicVector_fst_eq_zero_or_snd_eq_zero with hp | hp
    · refine ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.finite ⟨m, hm⟩ 0, ?_⟩
      simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep] using pureChain_even_fst_zero_iso c m hm hlen hp
    · refine ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.infinity ⟨m, hm⟩, ?_⟩
      simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep] using pureChain_even_snd_zero_iso c m hm hlen hp
  · rcases c.cyclicVector_fst_eq_zero_or_snd_eq_zero with hp | hp
    · refine ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.preinjective ⟨m + 1, by omega⟩, ?_⟩
      simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep] using pureChain_odd_fst_zero_iso c m hlen hp
    · refine ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.preprojective ⟨m + 1, by omega⟩, ?_⟩
      simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep] using pureChain_odd_snd_zero_iso c m hlen hp

private lemma nonnilpotent_arrows_bijective (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : ¬IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    Function.Bijective ρ.leftToRight ∧ Function.Bijective ρ.rightToLeft := by
  set AB := ρ.leftToRight.comp ρ.rightToLeft
  set BA := ρ.rightToLeft.comp ρ.leftToRight
  set pW := ⨆ n, LinearMap.ker (AB ^ n)
  set qW := ⨅ n, LinearMap.range (AB ^ n)
  set pV := ⨆ n, LinearMap.ker (BA ^ n)
  set qV := ⨅ n, LinearMap.range (BA ^ n)
  have hcV := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow BA
  have hcW := LinearMap.isCompl_iSup_ker_pow_iInf_range_pow AB
  have hApV : ∀ x ∈ pV, ρ.leftToRight x ∈ pW := fun x hx =>
    ρ.leftToRight_mem_iSup_ker_powers x hx
  have hAqV : ∀ x ∈ qV, ρ.leftToRight x ∈ qW := fun x hx =>
    ρ.leftToRight_mem_iInf_range_powers x hx
  have hBpW : ∀ x ∈ pW, ρ.rightToLeft x ∈ pV := fun x hx =>
    ρ.rightToLeft_mem_iSup_ker_powers x hx
  have hBqW : ∀ x ∈ qW, ρ.rightToLeft x ∈ qV := fun x hx =>
    ρ.rightToLeft_mem_iInf_range_powers x hx
  have hqW_ne : qW ≠ ⊥ := by
    intro hq
    apply hAB
    have hpW : pW = ⊤ := eq_top_of_isCompl_bot (hq ▸ hcW)
    have hsup : ⨆ n, LinearMap.ker (AB ^ n) = ⊤ := hpW
    obtain ⟨N, hN⟩ := Filter.Eventually.exists (LinearMap.eventually_iSup_ker_pow_eq AB)
    rw [hsup] at hN
    exact ⟨N, LinearMap.ker_eq_top.mp hN.symm⟩
  rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with hp | hq
  · have hqV : qV = ⊤ := eq_top_of_bot_isCompl (hp.1 ▸ hcV)
    have hqW : qW = ⊤ := eq_top_of_bot_isCompl (hp.2 ▸ hcW)
    have hAinj : Function.Injective ρ.leftToRight := by
      intro x y hxy
      apply ρ.leftToRight_injectiveOn_iInf_range_powers
        (show x ∈ qV by rw [hqV]; exact Submodule.mem_top)
        (show y ∈ qV by rw [hqV]; exact Submodule.mem_top) hxy
    have hBinj : Function.Injective ρ.rightToLeft := by
      intro x y hxy
      apply ρ.rightToLeft_injectiveOn_iInf_range_powers
        (show x ∈ qW by rw [hqW]; exact Submodule.mem_top)
        (show y ∈ qW by rw [hqW]; exact Submodule.mem_top) hxy
    have hdim : Module.finrank ℂ ρ.Left = Module.finrank ℂ ρ.Right := le_antisymm
      (LinearMap.finrank_le_finrank_of_injective hAinj)
      (LinearMap.finrank_le_finrank_of_injective hBinj)
    exact ⟨⟨hAinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hAinj⟩,
      ⟨hBinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hBinj⟩⟩
  · exact (hqW_ne hq.2).elim

private lemma aeval_AB_indecomposable_of_B_bijective (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    (hρ : ρ.AuxiliaryCondition) (hB : Function.Bijective ρ.rightToLeft) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial ℂ) (Module.AEval' (ρ.leftToRight.comp ρ.rightToLeft)) := by
  classical
  let AB := ρ.leftToRight.comp ρ.rightToLeft
  let ofAB := Module.AEval'.of (R := ℂ) AB
  have hWpos : 0 < Module.finrank ℂ ρ.Right := by
    rcases hρ.1 with hV | hW
    · have := LinearMap.finrank_le_finrank_of_surjective hB.2
      omega
    · exact hW
  letI : Nontrivial ρ.Right := Module.finrank_pos_iff.mp hWpos
  letI : Nontrivial (Module.AEval' AB) := ofAB.symm.toEquiv.nontrivial
  refine ⟨inferInstance, ?_⟩
  intro P Q hPQ
  let eB : ρ.Right ≃ₗ[ℂ] ρ.Left := LinearEquiv.ofBijective ρ.rightToLeft hB
  let oW := Submodule.orderIsoMapComap ofAB
  let oB := Submodule.orderIsoMapComap eB
  let pW : Submodule ℂ ρ.Right := oW.symm (P.restrictScalars ℂ)
  let qW : Submodule ℂ ρ.Right := oW.symm (Q.restrictScalars ℂ)
  let pV : Submodule ℂ ρ.Left := oB pW
  let qV : Submodule ℂ ρ.Left := oB qW
  have hcW0 : IsCompl (P.restrictScalars ℂ) (Q.restrictScalars ℂ) :=
    ⟨by simpa using hPQ.disjoint, by simpa using hPQ.codisjoint⟩
  have hcW : IsCompl pW qW := oW.symm.isCompl hcW0
  have hcV : IsCompl pV qV := oB.isCompl hcW
  have invariant (N : Submodule (Polynomial ℂ) (Module.AEval' AB))
      (w : ρ.Right) (hw : ofAB w ∈ N) : AB w ∈ oW.symm (N.restrictScalars ℂ) := by
    change ofAB (AB w) ∈ N
    rw [← Module.AEval'.X_smul_of]
    exact N.smul_mem Polynomial.X hw
  have hApV : ∀ x ∈ pV, ρ.leftToRight x ∈ pW := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    change ρ.leftToRight (ρ.rightToLeft w) ∈ pW
    exact invariant P w hw
  have hAqV : ∀ x ∈ qV, ρ.leftToRight x ∈ qW := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    change ρ.leftToRight (ρ.rightToLeft w) ∈ qW
    exact invariant Q w hw
  have hBpW : ∀ x ∈ pW, ρ.rightToLeft x ∈ pV := by
    intro x hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hBqW : ∀ x ∈ qW, ρ.rightToLeft x ∈ qV := by
    intro x hx
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rcases hρ.2 pV qV pW qW hcV hcW hApV hAqV hBpW hBqW with hp | hq
  · left
    apply Submodule.restrictScalars_injective ℂ (Polynomial ℂ) (Module.AEval' AB)
    apply oW.symm.injective
    simpa [pW] using hp.2
  · right
    apply Submodule.restrictScalars_injective ℂ (Polynomial ℂ) (Module.AEval' AB)
    apply oW.symm.injective
    simpa [qW] using hq.2

private noncomputable def reverseEuclidean (n : ℕ) :
    (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin n => ℂ) Fin.revPerm).trans
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm

@[simp] private lemma reverseEuclidean_apply (n : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    WithLp.ofLp (reverseEuclidean n x) i = x i.rev := by
  rfl

private lemma reverseEuclidean_intertwines (lam : ℂ) (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℂ) :
    reverseEuclidean n (RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator lam n x) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam).leftToRight (reverseEuclidean n x) := by
  apply WithLp.ofLp_injective
  funext i
  simp only [reverseEuclidean_apply, RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.auxiliaryFact,
    RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Matrix.of_apply]
  have hentry (j : Fin n) :
      (if i = j then lam else if i.val = j.val + 1 then 1 else 0) * x j.rev =
        (if i = j then lam * x j.rev else 0) +
          (if i.val = j.val + 1 then x j.rev else 0) := by
    split_ifs <;> simp_all
  simp_rw [hentry, Finset.sum_add_distrib]
  have hfirst : (∑ j : Fin n, if i = j then lam * x j.rev else 0) =
      lam * x i.rev := by simp
  rw [hfirst]
  by_cases hi : (i : ℕ) = 0
  · have hrev : (i.rev : ℕ) = n - 1 := by simp [Fin.rev, hi]
    rw [dif_neg (by omega)]
    apply congrArg (lam * x i.rev + ·)
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega)]
  · have hi_pos : 0 < (i : ℕ) := by omega
    let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
    have hj (a : Fin n) : ((i : ℕ) = (a : ℕ) + 1) ↔ a = j := by
      constructor
      · intro h
        apply Fin.ext
        dsimp [j]
        omega
      · rintro rfl
        dsimp [j]
        omega
    simp_rw [hj]
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, ↓reduceIte]
    have hrevlt : (i.rev : ℕ) + 1 < n := by simp [Fin.rev]; omega
    rw [dif_pos hrevlt]
    congr 2
    apply Fin.ext
    simp [j, Fin.rev]
    omega

/-- Under the auxiliary compatibility hypothesis, a nonnilpotent composite has a nonzero scalar witness at some dependent index. -/
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.exists_nonzero_scalar_witness_of_not_isNilpotent (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hAB : ¬IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    ∃ (n : ℕ) (hn : 0 < n) (lam : ℂ), lam ≠ 0 ∧
      Nonempty (ρ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam)) := by
  classical
  obtain ⟨hA, hB⟩ := nonnilpotent_arrows_bijective ρ hρ hAB
  let AB := ρ.leftToRight.comp ρ.rightToLeft
  have hindecomp : RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate (Polynomial ℂ) (Module.AEval' AB) :=
    aeval_AB_indecomposable_of_B_bijective ρ hρ hB
  obtain ⟨lam, n, hn, ⟨e⟩⟩ :=
    RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_jordanBlock_of_isIndecomposableModule
      (k := ℂ) (M := Module.AEval' AB) hindecomp
  let ofAB := Module.AEval'.of (R := ℂ) AB
  let J := RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator lam n
  let ofJ := Module.AEval'.of (R := ℂ) J
  let e0 : ρ.Right ≃ₗ[ℂ] (Fin n → ℂ) :=
    ofAB.trans ((e.restrictScalars ℂ).trans ofJ.symm)
  have he0 (w : ρ.Right) : e0 (AB w) = J (e0 w) := by
    change ofJ.symm (e (ofAB (AB w))) = J (ofJ.symm (e (ofAB w)))
    simpa [pow_one] using aeval_equiv_pow_intertwines AB J
      (show Module.AEval' AB ≃ₗ[Polynomial ℂ] Module.AEval' J from e) 1 w
  have hlam : lam ≠ 0 := by
    intro hlam
    subst lam
    apply hAB
    refine ⟨n, ?_⟩
    apply LinearMap.ext
    intro w
    apply e0.injective
    have he0pow : e0 ((AB ^ n) w) = (J ^ n) (e0 w) := by
      simpa [e0, ofAB, ofJ] using aeval_equiv_pow_intertwines AB J
        (show Module.AEval' AB ≃ₗ[Polynomial ℂ] Module.AEval' J from e) n w
    rw [he0pow]
    have hJ : J = RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent n := by
      simp [J, RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator]
    rw [hJ, RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanNilpotent_pow_eq_zero]
    simp
  let eW : ρ.Right ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := e0.trans (reverseEuclidean n)
  let eB : ρ.Right ≃ₗ[ℂ] ρ.Left := LinearEquiv.ofBijective ρ.rightToLeft hB
  let eV : ρ.Left ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := eB.symm.trans eW
  have hABmap (w : ρ.Right) : eW (AB w) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam).leftToRight (eW w) := by
    change reverseEuclidean n (e0 (AB w)) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam).leftToRight (reverseEuclidean n (e0 w))
    rw [he0]
    exact reverseEuclidean_intertwines lam n hn (e0 w)
  have hmapA (v : ρ.Left) : eW (ρ.leftToRight v) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam).leftToRight (eV v) := by
    let w := eB.symm v
    have hw : eB w = v := eB.apply_symm_apply v
    rw [← hw]
    change eW (ρ.leftToRight (ρ.rightToLeft w)) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam).leftToRight (eW (eB.symm (eB w)))
    rw [eB.symm_apply_apply]
    exact hABmap w
  have hmapB (w : ρ.Right) : eV (ρ.rightToLeft w) =
      (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam).rightToLeft (eW w) := by
    change eW (eB.symm (ρ.rightToLeft w)) = eW w
    rw [show ρ.rightToLeft w = eB w from rfl, eB.symm_apply_apply]
  exact ⟨n, hn, lam, hlam, ⟨{
    leftMap := eV
    rightMap := eW
    rightMap_leftToRight := hmapA
    leftMap_rightToLeft := hmapB }⟩⟩

universe uV uW

/-- Failure of nilpotency yields a dependent index, a nonzero scalar, and a related system carrying the corresponding witness. -/
@[source_ref "Chapter6/Problem6.9.1" (role := primary)]
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.exists_related_nonzero_scalar_of_not_isNilpotent (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.{0, uV, uW} ℂ)
    (hAB : ¬IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)) :
    ∃ (n : ℕ) (hn : 0 < n) (lam : ℂ), lam ≠ 0 ∧
      ∃ τ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.{0, uV, uW} ℂ, Nonempty (τ.Iso ρ) ∧
        Nonempty (τ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam)) := by
  classical
  suffices h : ∀ d : ℕ, ∀ σ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.{0, uV, uW} ℂ,
      Module.finrank ℂ σ.Left + Module.finrank ℂ σ.Right = d →
      ¬IsNilpotent (σ.leftToRight.comp σ.rightToLeft) →
      ∃ (n : ℕ) (hn : 0 < n) (lam : ℂ), lam ≠ 0 ∧
        ∃ τ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.{0, uV, uW} ℂ, Nonempty (τ.Iso σ) ∧
          Nonempty (τ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam)) by
    exact h _ ρ rfl hAB
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro σ hdim hABσ
      have hdpos : 0 < d := by
        by_contra hnot
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
        have hW0 : Module.finrank ℂ σ.Right = 0 := by omega
        letI : Subsingleton σ.Right := Module.finrank_zero_iff.mp hW0
        apply hABσ
        exact ⟨1, Subsingleton.elim _ _⟩
      have hnon : 0 < Module.finrank ℂ σ.Left ∨ 0 < Module.finrank ℂ σ.Right := by
        rcases Nat.eq_zero_or_pos (Module.finrank ℂ σ.Left) with hV0 | hVpos
        · right; omega
        · exact Or.inl hVpos
      by_cases hσ : σ.AuxiliaryCondition
      · obtain ⟨n, hn, lam, hlam, he⟩ := RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.exists_nonzero_scalar_witness_of_not_isNilpotent σ hσ hABσ
        exact ⟨n, hn, lam, hlam, σ, ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.Iso.refl σ⟩, he⟩
      · rw [RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair.AuxiliaryCondition] at hσ
        have hnotdecomp : ¬ ∀ (pV qV : Submodule ℂ σ.Left)
            (pW qW : Submodule ℂ σ.Right),
            IsCompl pV qV → IsCompl pW qW →
            (∀ x ∈ pV, σ.leftToRight x ∈ pW) → (∀ x ∈ qV, σ.leftToRight x ∈ qW) →
            (∀ x ∈ pW, σ.rightToLeft x ∈ pV) → (∀ x ∈ qW, σ.rightToLeft x ∈ qV) →
            (pV = ⊥ ∧ pW = ⊥) ∨ (qV = ⊥ ∧ qW = ⊥) := by
          intro hdecomp
          exact hσ ⟨hnon, hdecomp⟩
        push Not at hnotdecomp
        obtain ⟨pV, qV, pW, qW, hcV, hcW, hApV, hAqV, hBpW, hBqW,
            hpV, hqV⟩ := hnotdecomp
        have hpne : ¬(pV = ⊥ ∧ pW = ⊥) := fun hzero => hpV hzero.1 hzero.2
        have hqne : ¬(qV = ⊥ ∧ qW = ⊥) := fun hzero => hqV hzero.1 hzero.2
        have hdimV : Module.finrank ℂ pV + Module.finrank ℂ qV =
            Module.finrank ℂ σ.Left := by
          simpa [Module.finrank_prod] using
            (Submodule.prodEquivOfIsCompl pV qV hcV).finrank_eq
        have hdimW : Module.finrank ℂ pW + Module.finrank ℂ qW =
            Module.finrank ℂ σ.Right := by
          simpa [Module.finrank_prod] using
            (Submodule.prodEquivOfIsCompl pW qW hcW).finrank_eq
        have hpdim : 0 < Module.finrank ℂ pV + Module.finrank ℂ pW := by
          by_contra hzero
          apply hpne
          exact ⟨Submodule.finrank_eq_zero.mp (by omega),
            Submodule.finrank_eq_zero.mp (by omega)⟩
        have hqdim : 0 < Module.finrank ℂ qV + Module.finrank ℂ qW := by
          by_contra hzero
          apply hqne
          exact ⟨Submodule.finrank_eq_zero.mp (by omega),
            Submodule.finrank_eq_zero.mp (by omega)⟩
        have hp_lt : Module.finrank ℂ pV + Module.finrank ℂ pW < d := by omega
        have hq_lt : Module.finrank ℂ qV + Module.finrank ℂ qW < d := by omega
        let σp := σ.restrict pV pW hApV hBpW
        let σq := σ.restrict qV qW hAqV hBqW
        by_cases hp : IsNilpotent (σp.leftToRight.comp σp.rightToLeft)
        · have hq : ¬IsNilpotent (σq.leftToRight.comp σq.rightToLeft) := by
            intro hqnil
            exact hABσ (σ.isNilpotent_of_isCompl_restrict pV qV pW qW hcW
              hApV hAqV hBpW hBqW hp hqnil)
          obtain ⟨n, hn, lam, hlam, τ, ⟨e⟩, heiso⟩ := ih _ hq_lt σq rfl hq
          refine ⟨n, hn, lam, hlam, τ, ⟨e.trans ?_⟩, heiso⟩
          exact σ.restrictIso qV pV qW pW hcV.symm hcW.symm
            hAqV hApV hBqW hBpW
        · obtain ⟨n, hn, lam, hlam, τ, ⟨e⟩, heiso⟩ := ih _ hp_lt σp rfl hp
          refine ⟨n, hn, lam, hlam, τ, ⟨e.trans ?_⟩, heiso⟩
          exact σ.restrictIso pV qV pW qW hcV hcW
            hApV hAqV hBpW hBqW

private theorem classified_of_finrank_V_zero (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hV0 : Module.finrank ℂ ρ.Left = 0) : RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryPredicate ρ := by
  have hWpos : 0 < Module.finrank ℂ ρ.Right := by
    rcases hρ.1 with hV | hW
    · omega
    · exact hW
  have hdim := RepresentationTheory.FiniteDimensionalLinearMapPair.finrank_eq_or_eq_add_one ρ hρ
  have hW1 : Module.finrank ℂ ρ.Right = 1 := by
    rcases hdim with h | h | h <;> omega
  obtain ⟨eV⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.Left = Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) by
      simp [hV0])
  obtain ⟨eW⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.Right = Module.finrank ℂ (EuclideanSpace ℂ (Fin 1)) by
      simp [hW1])
  letI : Subsingleton ρ.Left := Module.finrank_zero_iff.mp hV0
  let target := RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelC 1 (by omega)
  have hmapA (v : ρ.Left) : eW (ρ.leftToRight v) = target.leftToRight (eV v) := by
    rw [Subsingleton.elim v 0, map_zero, map_zero, map_zero]
    exact target.leftToRight.map_zero.symm
  have hmapB (w : ρ.Right) : eV (ρ.rightToLeft w) = target.rightToLeft (eW w) := by
    apply Subsingleton.elim
  refine ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.preinjective ⟨1, by omega⟩, ⟨?_⟩⟩
  simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep, target] using (show ρ.Equiv target from {
    leftMap := eV
    rightMap := eW
    rightMap_leftToRight := hmapA
    leftMap_rightToLeft := hmapB })

private theorem classified_of_finrank_W_zero (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition)
    (hW0 : Module.finrank ℂ ρ.Right = 0) : RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryPredicate ρ := by
  have hVpos : 0 < Module.finrank ℂ ρ.Left := by
    rcases hρ.1 with hV | hW
    · exact hV
    · omega
  have hdim := RepresentationTheory.FiniteDimensionalLinearMapPair.finrank_eq_or_eq_add_one ρ hρ
  have hV1 : Module.finrank ℂ ρ.Left = 1 := by
    rcases hdim with h | h | h <;> omega
  obtain ⟨eV⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.Left = Module.finrank ℂ (EuclideanSpace ℂ (Fin 1)) by
      simp [hV1])
  obtain ⟨eW⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (show Module.finrank ℂ ρ.Right = Module.finrank ℂ (EuclideanSpace ℂ (Fin 0)) by
      simp [hW0])
  letI : Subsingleton ρ.Right := Module.finrank_zero_iff.mp hW0
  let target := RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryModelB 1 (by omega)
  have hmapA (v : ρ.Left) : eW (ρ.leftToRight v) = target.leftToRight (eV v) := by
    apply Subsingleton.elim
  have hmapB (w : ρ.Right) : eV (ρ.rightToLeft w) = target.rightToLeft (eW w) := by
    rw [Subsingleton.elim w 0, map_zero, map_zero, map_zero]
    exact target.rightToLeft.map_zero.symm
  refine ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.preprojective ⟨1, by omega⟩, ⟨?_⟩⟩
  simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep, target] using (show ρ.Equiv target from {
    leftMap := eV
    rightMap := eW
    rightMap_leftToRight := hmapA
    leftMap_rightToLeft := hmapB })

/-- An auxiliary compatibility condition implies the associated property. -/
@[source_ref "Chapter6/Section6.9_heading" (role := supporting),
  source_ref "Chapter6/Problem6.9.1" (role := supporting)]
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.Auxiliary.property_of_compatibility (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ) (hρ : ρ.AuxiliaryCondition) :
    RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryPredicate ρ := by
  by_cases hAB : IsNilpotent (ρ.leftToRight.comp ρ.rightToLeft)
  · by_cases hV0 : Module.finrank ℂ ρ.Left = 0
    · exact classified_of_finrank_V_zero ρ hρ hV0
    by_cases hW0 : Module.finrank ℂ ρ.Right = 0
    · exact classified_of_finrank_W_zero ρ hρ hW0
    obtain ⟨c⟩ := RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.nonempty_cyclicBasisData_of_isNilpotent ρ hρ hAB
      (Nat.pos_of_ne_zero hV0) (Nat.pos_of_ne_zero hW0)
    exact RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.Auxiliary.property_of_cyclicBasisData c
  · obtain ⟨n, hn, lam, hlam, ⟨e⟩⟩ := RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.exists_nonzero_scalar_witness_of_not_isNilpotent ρ hρ hAB
    exact ⟨RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.finite ⟨n, hn⟩ lam, by
      simpa [RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.rep] using (show Nonempty
        (ρ.Equiv (RepresentationTheory.FiniteDimensionalLinearMapPair.auxiliaryEigenvalueModel n hn lam)) from ⟨e⟩)⟩

/-- Two parameters are equal when their representatives both admit the prescribed relation to the same system. -/
@[source_ref "Chapter6/Problem6.9.1" (role := supporting)]
theorem RepresentationTheory.LinearAlgebra.TwoSpaceSystem.Nilpotent.TwoSpaceSystem.Auxiliary.eq_of_nonempty_rep_relations (ρ : RepresentationTheory.FiniteDimensionalLinearMapPair.FiniteDimensionalLinearMapPair ℂ)
    {c d : RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass} (ec : Nonempty (ρ.Equiv c.rep))
    (ed : Nonempty (ρ.Equiv d.rep)) : c = d := by
  obtain ⟨ec⟩ := ec
  obtain ⟨ed⟩ := ed
  exact RepresentationTheory.FiniteDimensionalLinearMapPair.AuxiliaryClass.eq_of_rep_equiv (ec.symm.trans ed)
