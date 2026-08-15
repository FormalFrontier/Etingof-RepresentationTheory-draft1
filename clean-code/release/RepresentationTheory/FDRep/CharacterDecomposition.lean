/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Group.CharacterAuxiliary
import RepresentationTheory.FiniteGroup.CharacterPairing

/-!
# Character decomposition for finite-dimensional representations

This module decomposes finite-dimensional representations against a complete family of pairwise
nonisomorphic simple representations using character and morphism-space dimensions.
-/

open CategoryTheory CategoryTheory.Limits Module
  RepresentationTheory.Group.CharacterAuxiliary
  RepresentationTheory.FiniteGroup.CharacterPairing

namespace RepresentationTheory.FDRep.CharacterDecomposition

variable {k : Type} [Field k] {G : Type} [Group G] [Fintype G]

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! ## Underlying linear algebra of biproducts -/

omit [Fintype G] in
/-- A morphism of representations commutes with the action of each group element. -/
lemma hom_action_comm {A B : FDRep k G} (f : A ⟶ B) (g : G) (a : (A : Type)) :
    f.hom.hom.hom (A.ρ g a) = B.ρ g (f.hom.hom.hom a) := by
  have h := f.comm g
  apply_fun (fun m : A.V ⟶ B.V => m.hom.hom) at h
  have h2 := congrFun (congrArg (fun (m : (A.V.obj) →ₗ[k] (B.V.obj)) => (m : _ → _)) h) a
  simpa using h2

/-- The underlying vector space of a binary biproduct is linearly equivalent to the product of its
components. -/
noncomputable def biprodCarrierLinearEquiv (X Y : FDRep k G) :
    (X ⊞ Y : FDRep k G) ≃ₗ[k] Prod (X : Type) (Y : Type) where
  toFun v := ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v,
              (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
  map_add' a b := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' r a := Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  invFun p := (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
              (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2
  left_inv v := by
    change ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
      (X ⊞ Y : FDRep k G) ⟶ (X ⊞ Y))).hom.hom.hom v = v
    rw [biprod.total]
    rfl
  right_inv p := by
    have hzero : ∀ (A B : FDRep k G) (x : (A : Type)),
        (0 : A ⟶ B).hom.hom.hom x = 0 := by
      intro A B x
      change (0 : A.V.obj ⟶ B.V.obj).hom x = 0
      simp [ModuleCat.Hom.hom]
    have hid : ∀ (A : FDRep k G) (x : (A : Type)),
        (𝟙 A : A ⟶ A).hom.hom.hom x = x := fun _ _ => rfl
    ext <;> dsimp only
    · change ((biprod.fst : X ⊞ Y ⟶ X)).hom.hom.hom
          ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
           (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.1
      rw [map_add]
      change ((biprod.inl ≫ biprod.fst : X ⟶ X)).hom.hom.hom p.1 +
           ((biprod.inr ≫ biprod.fst : Y ⟶ X)).hom.hom.hom p.2 = p.1
      rw [biprod.inl_fst, biprod.inr_fst, hid, hzero, add_zero]
    · change ((biprod.snd : X ⊞ Y ⟶ Y)).hom.hom.hom
          ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
           (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.2
      rw [map_add]
      change ((biprod.inl ≫ biprod.snd : X ⟶ Y)).hom.hom.hom p.1 +
           ((biprod.inr ≫ biprod.snd : Y ⟶ Y)).hom.hom.hom p.2 = p.2
      rw [biprod.inl_snd, biprod.inr_snd, hzero, hid, zero_add]

/-- The character of a binary biproduct is the sum of the two component characters. -/
lemma character_biprod (X Y : FDRep k G) (g : G) :
    (X ⊞ Y : FDRep k G).character g = X.character g + Y.character g := by
  have hequiv : ∀ v, (biprodCarrierLinearEquiv X Y) ((X ⊞ Y : FDRep k G).ρ g v) =
      LinearMap.prodMap (X.ρ g) (Y.ρ g) ((biprodCarrierLinearEquiv X Y) v) := by
    intro v
    apply Prod.ext
    · exact hom_action_comm (biprod.fst : X ⊞ Y ⟶ X) g v
    · exact hom_action_comm (biprod.snd : X ⊞ Y ⟶ Y) g v
  have hconj : (biprodCarrierLinearEquiv X Y).conj ((X ⊞ Y : FDRep k G).ρ g) =
      LinearMap.prodMap (X.ρ g) (Y.ρ g) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have hv := hequiv ((biprodCarrierLinearEquiv X Y).symm w)
    rw [LinearEquiv.apply_symm_apply] at hv
    simpa using hv
  calc
    (X ⊞ Y : FDRep k G).character g =
        LinearMap.trace k _ ((X ⊞ Y : FDRep k G).ρ g) := rfl
    _ = LinearMap.trace k _
        ((biprodCarrierLinearEquiv X Y).conj ((X ⊞ Y : FDRep k G).ρ g)) :=
      (LinearMap.trace_conj' _ _).symm
    _ = LinearMap.trace k _ (LinearMap.prodMap (X.ρ g) (Y.ρ g)) := by rw [hconj]
    _ = X.character g + Y.character g := LinearMap.trace_prodMap' _ _

omit [Fintype G] in
/-- A zero representation has the zero character at every group element. -/
lemma character_eq_zero_of_isZero {V : FDRep k G} (hV : IsZero V) (g : G) :
    V.character g = 0 := by
  have hsub : Subsingleton (V : Type) := by
    have hid : (𝟙 V : V ⟶ V) = 0 := (IsZero.iff_id_eq_zero V).mp hV
    refine ⟨fun a b => ?_⟩
    have ha : (𝟙 V : V ⟶ V).hom.hom.hom a = (0 : V ⟶ V).hom.hom.hom a := by rw [hid]
    have hb : (𝟙 V : V ⟶ V).hom.hom.hom b = (0 : V ⟶ V).hom.hom.hom b := by rw [hid]
    simp only [show ∀ x : (V : Type), (0 : V ⟶ V).hom.hom.hom x = 0 from fun x => by
      change (0 : V.V.obj ⟶ V.V.obj).hom x = 0
      simp [ModuleCat.Hom.hom]] at ha hb
    exact ha.trans hb.symm
  have hρ : V.ρ g = 0 := by
    ext v
    exact Subsingleton.elim _ _
  change LinearMap.trace k _ (V.ρ g) = 0
  rw [hρ, map_zero]

/-! ## Hom spaces into a finite biproduct -/

/-- Maps from a fixed representation to a finite biproduct are linearly equivalent to families of
component maps. -/
noncomputable def homBiproductLinearEquiv
    (S : FDRep k G) {J : Type} [Fintype J] [DecidableEq J] (U : J → FDRep k G) :
    (S ⟶ ⨁ U) ≃ₗ[k] (∀ j, (S ⟶ U j)) where
  toFun f j := f ≫ biproduct.π U j
  map_add' f g := by funext j; simp [Preadditive.add_comp]
  map_smul' r f := by funext j; simp
  invFun φ := biproduct.lift φ
  left_inv f := by
    apply biproduct.hom_ext
    intro j
    simp
  right_inv φ := by funext j; simp

omit [Fintype G] in
/-- The dimension of maps from a fixed representation into a finite biproduct is the sum of the
component dimensions. -/
lemma finrank_hom_biproduct
    (S : FDRep k G) {J : Type} [Fintype J] [DecidableEq J] (U : J → FDRep k G) :
    finrank k (S ⟶ ⨁ U) = ∑ j, finrank k (S ⟶ U j) := by
  rw [(homBiproductLinearEquiv S U).finrank_eq, finrank_pi_fintype]

/-! ## Decomposition against a complete family -/

section Complete

variable [IsAlgClosed k] [CharZero k] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A complete family of simple representations expresses every character with natural
coefficients. -/
theorem exists_character_eq_sum_smul (T : ι → FDRep k G)
    (hcomplete : ∀ S : FDRep k G, Simple S → ∃ i, Nonempty (S ≅ T i))
    (V : FDRep k G) :
    ∃ n : ι → ℕ, ∀ g : G, V.character g = ∑ i, (n i : k) * (T i).character g := by
  suffices key : ∀ (m : ℕ) (V : FDRep k G), finrank k V ≤ m →
      ∃ n : ι → ℕ, ∀ g : G, V.character g = ∑ i, (n i : k) * (T i).character g from
    key _ V le_rfl
  intro m
  induction m with
  | zero =>
    intro V hV
    refine ⟨fun _ => 0, fun g => ?_⟩
    rw [character_eq_zero_of_isZero
      (isZero_of_finrank_eq_zero V (Nat.eq_zero_of_le_zero hV)) g]
    simp
  | succ m ih =>
    intro V hV
    by_cases hz : IsZero V
    · exact ⟨fun _ => 0, fun g => by rw [character_eq_zero_of_isZero hz g]; simp⟩
    obtain ⟨S, V', hS, ⟨φ⟩⟩ := exists_simple_biprod V hz
    haveI := hS
    obtain ⟨i₀, ⟨ψ⟩⟩ := hcomplete S hS
    have hdim : finrank k V = finrank k S + finrank k V' := by
      rw [finrank_eq_of_iso V (S ⊞ V') φ, finrank_biproduct]
    have hSpos : 0 < finrank k S := finrank_pos_of_simple S
    obtain ⟨n', hn'⟩ := ih V' (by omega)
    refine ⟨fun i => n' i + if i = i₀ then 1 else 0, fun g => ?_⟩
    have hV_char : V.character g = S.character g + V'.character g := by
      rw [FDRep.char_iso φ, character_biprod]
    rw [hV_char, FDRep.char_iso ψ, hn' g]
    have hsplit : ∑ i, ((n' i + if i = i₀ then 1 else 0 : ℕ) : k) * (T i).character g =
        (∑ i, (n' i : k) * (T i).character g) + (T i₀).character g := by
      push_cast
      simp only [add_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i₀ (fun i => (T i).character g)]
      simp
    rw [hsplit]
    ring

variable (T : ι → FDRep k G)

/-- An indexed natural-number-valued operation on a family of representations and a
representation. -/
noncomputable def indexedNatForRepresentation (V : FDRep k G) (i : ι) : ℕ :=
  finrank k (T i ⟶ V)

/-- A representation-valued operation on a finite family of representations and an indexed family
of natural numbers. -/
noncomputable def representationFromIndexedNats (n : ι → ℕ) : FDRep k G :=
  ⨁ (fun p : Σ i : ι, Fin (n i) => T p.1)

/-- Maps into the representation returned from a finite family and indexed natural numbers have
dimension given by the weighted component sum. -/
lemma finrank_hom_representationFromIndexedNats (n : ι → ℕ) (S : FDRep k G) :
    finrank k (S ⟶ representationFromIndexedNats T n) =
      ∑ i, n i * finrank k (S ⟶ T i) := by
  rw [representationFromIndexedNats, finrank_hom_biproduct,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const_nat (m := finrank k (S ⟶ T i)) (fun _ _ => rfl),
    Finset.card_univ, Fintype.card_fin]

variable (hT : ∀ i, Simple (T i)) (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
  (hcomplete : ∀ S : FDRep k G, Simple S → ∃ i, Nonempty (S ≅ T i))

omit [Fintype G] [CharZero k] [Fintype ι] in
include hT hinj in
/-- Maps between members of a pairwise nonisomorphic simple family have dimension one on the
diagonal and zero otherwise. -/
lemma finrank_hom_simple_eq_ite (i j : ι) :
    finrank k (T i ⟶ T j) = if i = j then 1 else 0 := by
  haveI := hT i
  haveI := hT j
  rw [FDRep.finrank_hom_simple_simple]
  by_cases h : i = j
  · subst h
    simp
  · simp only [h, if_false, ite_eq_right_iff]
    intro hiso
    exact absurd (hinj i j hiso) h

include hcomplete in
/-- The coefficients arising from a complete simple family give the corresponding Hom-space
dimension formula. -/
theorem exists_finrank_hom_eq_sum_mul (V : FDRep k G) :
    ∃ n : ι → ℕ, ∀ S : FDRep k G,
      finrank k (S ⟶ V) = ∑ i, n i * finrank k (S ⟶ T i) := by
  obtain ⟨n, hn⟩ := exists_character_eq_sum_smul T hcomplete V
  haveI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨n, fun S => ?_⟩
  have hkey : ((finrank k (S ⟶ V) : ℕ) : k) =
      ((∑ i, n i * finrank k (S ⟶ T i) : ℕ) : k) := by
    rw [← FiniteGroup.normalized_characterPairing_eq_finrank_hom V S]
    push_cast
    have hrhs : ∀ i : ι, ((n i : k) * (finrank k (S ⟶ T i) : k)) =
        (n i : k) * (⅟(Fintype.card G : k) •
          ∑ g : G, (T i).character g * S.character g⁻¹) := by
      intro i
      rw [FiniteGroup.normalized_characterPairing_eq_finrank_hom (T i) S]
    rw [Finset.sum_congr rfl (fun i _ => hrhs i)]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hn g, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact_mod_cast hkey

include hT hinj hcomplete in
/-- For a complete pairwise distinct simple family, Hom-space dimensions are given by a weighted
sum using the indexed natural numbers assigned to the representation. -/
theorem finrank_hom_eq_sum_indexedNatForRepresentation_mul
    (V : FDRep k G) (S : FDRep k G) :
    finrank k (S ⟶ V) =
      ∑ i, indexedNatForRepresentation T V i * finrank k (S ⟶ T i) := by
  obtain ⟨n, hn⟩ := exists_finrank_hom_eq_sum_mul T hcomplete V
  have hmul : ∀ i, indexedNatForRepresentation T V i = n i := by
    intro i
    rw [indexedNatForRepresentation, hn (T i)]
    rw [Finset.sum_congr rfl (fun j _ => by rw [finrank_hom_simple_eq_ite T hT hinj i j])]
    simp
  rw [Finset.sum_congr rfl (fun i _ => by rw [hmul i])]
  exact hn S

include hT hinj hcomplete in
/-- For a complete pairwise distinct simple family, every representation is isomorphic to the
result obtained from its associated indexed natural numbers. -/
theorem iso_representationFromIndexedNats_indexedNatForRepresentation (V : FDRep k G) :
    Nonempty
      (V ≅ representationFromIndexedNats T (indexedNatForRepresentation T V)) := by
  refine iso_of_hom_finrank_eq V _ fun S => ?_
  rw [finrank_hom_representationFromIndexedNats]
  exact finrank_hom_eq_sum_indexedNatForRepresentation_mul T hT hinj hcomplete V S

end Complete

end RepresentationTheory.FDRep.CharacterDecomposition
