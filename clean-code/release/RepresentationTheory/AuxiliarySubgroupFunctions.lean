import Mathlib
import RepresentationTheory.FiniteGroup.ClassFunctions
import RepresentationTheory.Alignment.Attribute




















noncomputable section

open Classical in




/-- An auxiliary complex-valued function on a finite group constructed from a subgroup function. -/
def RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : ↥H → ℂ) : G → ℂ :=
  fun g => (Fintype.card ↥H : ℂ)⁻¹ *
    ∑ x : G, if h : x⁻¹ * g * x ∈ H then χ ⟨x⁻¹ * g * x, h⟩ else 0

open Classical in









private lemma frobenius_char_reciprocity {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (f : G → ℂ) (χ : ↥H → ℂ)
    (hf : ∀ g x : G, f (x * g * x⁻¹) = f g) :
    ∑ g : G, f g * RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H χ g⁻¹ =
    (Fintype.card G : ℂ) * (Fintype.card ↥H : ℂ)⁻¹ *
      ∑ h : ↥H, f ↑h * χ (h⁻¹) := by


  suffices inner_sum_eq : ∀ x : G,
      ∑ g : G, f g * (if h : x⁻¹ * g⁻¹ * x ∈ H then χ ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0) =
      ∑ h : ↥H, f ↑h * χ (h⁻¹) by

    simp_rw [RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction]


    have lhs_eq : (∑ g : G, f g *
        ((↑(Fintype.card ↥H))⁻¹ * ∑ x : G,
          if h : x⁻¹ * g⁻¹ * x ∈ H then χ ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0)) =
      (↑(Fintype.card ↥H))⁻¹ * ∑ x : G, ∑ g : G,
        f g * (if h : x⁻¹ * g⁻¹ * x ∈ H then χ ⟨x⁻¹ * g⁻¹ * x, h⟩ else 0) := by

      conv_lhs => arg 2; ext g
                  rw [mul_left_comm]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [lhs_eq]

    simp_rw [inner_sum_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring

  intro x


  let φ : G ≃ G :=
    { toFun := fun k => x * k⁻¹ * x⁻¹
      invFun := fun g => x⁻¹ * g⁻¹ * x
      left_inv := fun k => by group
      right_inv := fun g => by group }
  rw [← Equiv.sum_comp φ]


  have hsimp : ∀ k : G, x⁻¹ * (x * k⁻¹ * x⁻¹)⁻¹ * x = k := fun k => by group
  simp_rw [show ∀ k : G, φ k = x * k⁻¹ * x⁻¹ from fun _ => rfl, hsimp]

  simp_rw [show ∀ k : G, f (x * k⁻¹ * x⁻¹) = f k⁻¹ from fun k => hf k⁻¹ x]


  conv_lhs => arg 2; ext k; rw [show f k⁻¹ * (if h : k ∈ H then χ ⟨k, h⟩ else 0) =
    if h : k ∈ H then f k⁻¹ * χ ⟨k, h⟩ else 0 by split_ifs <;> simp]







  have h_restrict : (∑ k : G, if h_1 : k ∈ H then f k⁻¹ * χ ⟨k, h_1⟩ else 0) =
      ∑ k : ↥H, f (↑k)⁻¹ * χ k := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ H)
      (fun k : G => if h_1 : k ∈ H then f k⁻¹ * χ ⟨k, h_1⟩ else 0)]
    have h_compl : (∑ k : {k : G // k ∉ H},
        if h_1 : (↑k : G) ∈ H then f (↑k)⁻¹ * χ ⟨↑k, h_1⟩ else 0) = 0 :=
      Finset.sum_eq_zero (fun ⟨k, hk⟩ _ => dif_neg hk)
    rw [h_compl, add_zero]
    congr 1; ext ⟨k, hk⟩; exact dif_pos hk
  rw [h_restrict]

  conv_lhs => rw [← Equiv.sum_comp (Equiv.inv ↥H)]
  congr 1; ext h
  simp only [Equiv.inv_apply, Subgroup.coe_inv, inv_inv]

open Classical in





/-- The auxiliary subgroup function is expressed as a finite sum of displayed characters with multiplicity coefficients. -/
theorem RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction_eq_sum_character
    {G : Type} [Group G] [Fintype G] [NeZero (Nat.card G : ℂ)]
    (D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData ℂ G) (H : Subgroup G) (W : FDRep ℂ ↥H) :
    RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character =
      ∑ i : Fin D.count,
        (Module.finrank ℂ
          (W ⟶ FDRep.of ((D.representation i).ρ.comp H.subtype)) : ℤ) •
          (D.representation i).character := by
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
  haveI : Invertible (Fintype.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  haveI : NeZero (Nat.card ↥H : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩
  let resH : Fin D.count → FDRep ℂ ↥H := fun i =>
    FDRep.of ((D.representation i).ρ.comp H.subtype)
  let m : Fin D.count → ℕ := fun i => Module.finrank ℂ (W ⟶ resH i)
  have hdiff : RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character -
      ∑ i : Fin D.count, (m i : ℤ) • (D.representation i).character = 0 := by
    apply RepresentationTheory.FiniteGroup.ClassFunctions.FiniteGroup.ClassFunction.eq_zero_of_characterPairing_eq_zero
    · intro g x
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
      congr 1
      · show RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character (x * g * x⁻¹) =
             RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g
        simp only [RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction]
        congr 1
        let φ : G ≃ G :=
          { toFun := fun y => x * y
            invFun := fun z => x⁻¹ * z
            left_inv := fun y => by group
            right_inv := fun z => by group }
        rw [← Equiv.sum_comp φ]
        apply Finset.sum_congr rfl
        intro y _
        have dite_eq : ∀ (a b : G) (hab : a = b),
            (if h : a ∈ H then W.character ⟨a, h⟩ else 0) =
            (if h : b ∈ H then W.character ⟨b, h⟩ else 0) := by
          rintro a b rfl
          rfl
        exact dite_eq _ _ (by
          change (x * y)⁻¹ * (x * g * x⁻¹) * (x * y) = y⁻¹ * g * y
          group)
      · congr 1
        ext i
        congr 1
        exact FDRep.char_conj (D.representation i) g x
    · intro V' hV'
      obtain ⟨j, ⟨iso_j⟩⟩ := D.exists_iso_representation_of_simple V' hV'
      rw [FDRep.char_iso iso_j]
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, sub_mul,
        Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      haveI (i : Fin D.count) : CategoryTheory.Simple (D.representation i) :=
        D.simple_representation i
      have horth_G : ∀ i : Fin D.count,
          ∑ g : G, (D.representation i).character g * (D.representation j).character g⁻¹ =
          if i = j then (Fintype.card G : ℂ) else 0 := by
        intro i
        have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (D.representation i) (D.representation j)
        rw [smul_eq_mul] at h
        have hinv : ∀ (x y : ℂ), ⅟(Fintype.card G : ℂ) * x = y →
            x = (Fintype.card G : ℂ) * y := fun x y hxy => by
          rw [← hxy, ← mul_assoc, mul_invOf_self, one_mul]
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl]
          exact (hinv _ _ (by
            rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h
            exact h)).trans (mul_one _)
        · rw [if_neg hij]
          exact (hinv _ _ (by
            rw [if_neg (fun ⟨iso⟩ => hij
              (D.representation_index_eq_of_iso i j ⟨iso⟩))] at h
            exact h)).trans (mul_zero _)
      trans (↑(m j) * (Fintype.card G : ℂ))
      · have lhs_sub : ∑ g : G,
            RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g *
              (D.representation j).character g⁻¹ =
            ∑ g : G, (D.representation j).character g *
              RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g⁻¹ := by
          rw [← Equiv.sum_comp (Equiv.inv G)]
          congr 1
          ext g
          simp [mul_comm]
        have hfrob := frobenius_char_reciprocity H
          (D.representation j).character W.character
          (fun g x => FDRep.char_conj (D.representation j) g x)
        rw [lhs_sub, hfrob]
        have hlhs_rw :
            ∑ h : ↥H, (D.representation j).character (↑h : G) * W.character h⁻¹ =
              ∑ h : ↥H, (resH j).character h * W.character h⁻¹ :=
          Finset.sum_congr rfl (fun h _ => rfl)
        rw [hlhs_rw]
        have hmult : ⅟(Fintype.card ↥H : ℂ) •
            ∑ h : ↥H, (resH j).character h * W.character h⁻¹ = ↑(m j) := by
          have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom (resH j) W
          rw [smul_eq_mul] at h ⊢
          convert h using 1
        have hsum_H : ∑ h : ↥H, (resH j).character h * W.character h⁻¹ =
            (Fintype.card ↥H : ℂ) * ↑(m j) := by
          rw [smul_eq_mul] at hmult
          calc
            _ = (Fintype.card ↥H : ℂ) * (⅟(Fintype.card ↥H : ℂ) *
                ∑ h : ↥H, (resH j).character h * W.character h⁻¹) := by
              rw [← mul_assoc, mul_invOf_self, one_mul]
            _ = _ := by rw [hmult]
        rw [hsum_H]
        have hH_ne : (Fintype.card ↥H : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        field_simp
      · symm
        simp only [zsmul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, horth_G, mul_ite, mul_zero]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
  exact sub_eq_zero.mp hdiff

open Classical in










private lemma class_fun_vanishes_on_subgroup_of_orthogonal
    {G : Type} [Group G] [Fintype G]
    (H : Subgroup G)
    (f : G → ℂ) (hf_class : ∀ g x : G, f (x * g * x⁻¹) = f g)
    (horth : ∀ (W : FDRep ℂ ↥H), CategoryTheory.Simple W →
      ∑ h : ↥H, f ↑h * W.character (h⁻¹) = 0) :
    ∀ h : ↥H, f ↑h = 0 := by

  suffices hzero : (fun h : ↥H => f ↑h) = 0 by
    intro h; exact congr_fun hzero h

  haveI : Invertible (Fintype.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

  apply RepresentationTheory.FiniteGroup.ClassFunctions.FiniteGroup.ClassFunction.eq_zero_of_characterPairing_eq_zero
  ·
    intro a b
    change f ↑(b * a * b⁻¹) = f ↑a
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hf_class ↑a ↑b
  ·
    intro W
    exact horth W ‹_›



private lemma covering_implies_vanishing {G : Type} [Group G]
    (X : Set (Subgroup G))
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H)
    (f : G → ℂ)
    (hvan : ∀ H ∈ X, ∀ h : ↥H, f ↑h = 0) :
    f = 0 := by
  ext g
  obtain ⟨H, hH, hg⟩ := hcov g
  exact hvan H hH ⟨g, hg⟩





private lemma inner_zero_of_span_mem {G : Type} [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (f : G → ℂ) (hf_class : ∀ g x : G, f (x * g * x⁻¹) = f g)
    (hf_orth : ∀ H ∈ X, ∀ (W : FDRep ℂ ↥H),
      ∑ g : G, f g * RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g⁻¹ = 0)
    (s : G → ℂ)
    (hs : s ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character}) :
    ∑ g : G, f g * s g⁻¹ = 0 := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨H, hH, W, rfl⟩ := hx
    exact hf_orth H hH W
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hx, hy, add_zero]
  | smul r x _ hx =>
    change ∑ g : G, f g * (r • x) g⁻¹ = 0
    have key : ∀ g : G, f g * (r • x) g⁻¹ = (r : ℂ) * (f g * x g⁻¹) := by
      intro g; change f g * r • x g⁻¹ = _; rw [show r • x g⁻¹ = (r : ℂ) * x g⁻¹ from
        Algebra.smul_def r (x g⁻¹)]; ring
    simp_rw [key, ← Finset.mul_sum, hx, mul_zero]













private lemma artin_Q_span_of_induced_chars {G : Type} [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X)
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H)

    (horth_trivial : ∀ (f : G → ℂ),
      (∀ g x : G, f (x * g * x⁻¹) = f g) →
      (∀ H ∈ X, ∀ (W : FDRep ℂ ↥H),
        ∑ g : G, f g * RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g⁻¹ = 0) →
      f = 0)
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    V.character ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character} := by

  set S := {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
    f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character} with hS_def

  by_contra hV_not_mem




















  classical
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩

  let D := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default (k := ℂ) (G := G)

  obtain ⟨j₀, ⟨hj₀⟩⟩ := D.exists_iso_representation_of_simple V ‹_›

  have hV_char : V.character = (D.representation j₀).character :=
    FDRep.char_iso hj₀




  have hS_in_ℤspan : ∀ s ∈ S, s ∈ Submodule.span ℤ
      (Set.range (fun i : Fin D.count => (D.representation i).character)) := by
    intro s hs
    obtain ⟨H, hHX, W, rfl⟩ := hs

    haveI : Invertible (Fintype.card ↥H : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    haveI : NeZero (Nat.card ↥H : ℂ) :=
      ⟨by rw [Nat.card_eq_fintype_card]; exact Invertible.ne_zero _⟩

    let resH : Fin D.count → FDRep ℂ ↥H := fun i =>
      FDRep.of ((D.representation i).ρ.comp H.subtype)

    let m : Fin D.count → ℕ := fun i => Module.finrank ℂ (W ⟶ resH i)

    suffices hsuff : RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character =
        ∑ i : Fin D.count, (m i : ℤ) • (D.representation i).character by
      rw [hsuff]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


    have hdiff : RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character -
        ∑ i : Fin D.count, (m i : ℤ) • (D.representation i).character = 0 := by
      apply RepresentationTheory.FiniteGroup.ClassFunctions.FiniteGroup.ClassFunction.eq_zero_of_characterPairing_eq_zero
      ·
        intro g x
        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
        congr 1
        ·
          show RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character (x * g * x⁻¹) =
               RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g
          simp only [RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction]
          congr 1
          let φ : G ≃ G :=
            { toFun := fun y => x * y
              invFun := fun z => x⁻¹ * z
              left_inv := fun y => by group
              right_inv := fun z => by group }
          rw [← Equiv.sum_comp φ]
          apply Finset.sum_congr rfl
          intro y _

          have dite_eq : ∀ (a b : G) (hab : a = b),
              (if h : a ∈ H then W.character ⟨a, h⟩ else 0) =
              (if h : b ∈ H then W.character ⟨b, h⟩ else 0) := by
            rintro a b rfl; rfl
          exact dite_eq _ _ (by change (x * y)⁻¹ * (x * g * x⁻¹) * (x * y) = y⁻¹ * g * y; group)
        ·
          congr 1; ext i; congr 1
          exact FDRep.char_conj (D.representation i) g x
      ·
        intro V' hV'
        obtain ⟨j, ⟨iso_j⟩⟩ := D.exists_iso_representation_of_simple V' hV'
        rw [FDRep.char_iso iso_j]

        simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, sub_mul,
          Finset.sum_sub_distrib]
        rw [sub_eq_zero]

        haveI (i : Fin D.count) : CategoryTheory.Simple (D.representation i) :=
          D.simple_representation i
        have horth_G : ∀ i : Fin D.count,
            ∑ g : G, (D.representation i).character g * (D.representation j).character g⁻¹ =
            if i = j then (Fintype.card G : ℂ) else 0 := by
          intro i
          have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (D.representation i) (D.representation j)
          rw [smul_eq_mul] at h
          have hinv : ∀ (x y : ℂ), ⅟(Fintype.card G : ℂ) * x = y →
              x = (Fintype.card G : ℂ) * y := fun x y h => by
            rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
          by_cases hij : i = j
          · subst hij
            rw [if_pos rfl]
            exact (hinv _ _ (by rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h; exact h)).trans
              (mul_one _)
          · rw [if_neg hij]
            exact (hinv _ _ (by rw [if_neg (fun ⟨iso⟩ => hij
              (D.representation_index_eq_of_iso i j ⟨iso⟩))] at h; exact h)).trans (mul_zero _)



        trans (↑(m j) * (Fintype.card G : ℂ))
        ·

          have lhs_sub : ∑ g : G,
              RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g *
                (D.representation j).character g⁻¹ =
              ∑ g : G, (D.representation j).character g *
                RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g⁻¹ := by
            rw [← Equiv.sum_comp (Equiv.inv G)]
            congr 1; ext g; simp [mul_comm]
          have hfrob := frobenius_char_reciprocity H (D.representation j).character W.character
            (fun g x => FDRep.char_conj (D.representation j) g x)
          rw [lhs_sub, hfrob]

          have hlhs_rw : ∑ h : ↥H, (D.representation j).character (↑h : G) * W.character h⁻¹ =
              ∑ h : ↥H, (resH j).character h * W.character h⁻¹ :=
            Finset.sum_congr rfl (fun h _ => rfl)
          rw [hlhs_rw]

          have hmult : ⅟(Fintype.card ↥H : ℂ) •
              ∑ h : ↥H, (resH j).character h * W.character h⁻¹ = ↑(m j) := by
            have := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_finrank_hom (resH j) W
            rw [smul_eq_mul] at this ⊢
            convert this using 1

          have hsum_H : ∑ h : ↥H, (resH j).character h * W.character h⁻¹ =
              (Fintype.card ↥H : ℂ) * ↑(m j) := by
            rw [smul_eq_mul] at hmult
            calc _ = (Fintype.card ↥H : ℂ) * (⅟(Fintype.card ↥H : ℂ) *
                ∑ h : ↥H, (resH j).character h * W.character h⁻¹) := by
                  rw [← mul_assoc, mul_invOf_self, one_mul]
              _ = _ := by rw [hmult]
          rw [hsum_H]
          have hH_ne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          field_simp
        ·
          symm
          simp only [zsmul_eq_mul, Finset.sum_mul]
          rw [Finset.sum_comm]
          simp_rw [mul_assoc, ← Finset.mul_sum, horth_G, mul_ite, mul_zero]
          simp [Finset.sum_ite_eq', Finset.mem_univ]
    exact sub_eq_zero.mp hdiff

  have h_li_C : LinearIndependent ℂ (fun i : Fin D.count => (D.representation i).character) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j




    haveI (i : Fin D.count) : CategoryTheory.Simple (D.representation i) := D.simple_representation i

    have h_iso_iff : ∀ i k : Fin D.count,
        Nonempty ((D.representation i) ≅ (D.representation k)) ↔ i = k := by
      intro i k
      constructor
      · exact D.representation_index_eq_of_iso i k
      · rintro rfl; exact ⟨CategoryTheory.Iso.refl _⟩


    have h_orth : ∀ i : Fin D.count,
        ⅟(Fintype.card G : ℂ) • ∑ g : G,
          (D.representation i).character g * (D.representation j).character g⁻¹ =
        if i = j then 1 else 0 := by
      intro i
      rw [RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple]
      simp [h_iso_iff]

    have lhs_zero : ∀ g, (∑ i : Fin D.count, c i * (D.representation i).character g) = 0 := by
      intro g
      have := congr_fun hc g
      simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this



    have stepA : ⅟(Fintype.card G : ℂ) • ∑ g : G,
        (∑ i : Fin D.count, c i * (D.representation i).character g) *
        (D.representation j).character g⁻¹ = 0 := by
      simp_rw [lhs_zero, zero_mul, Finset.sum_const_zero, smul_zero]

    have stepB : ⅟(Fintype.card G : ℂ) • ∑ g : G,
        (∑ i : Fin D.count, c i * (D.representation i).character g) *
        (D.representation j).character g⁻¹ =
        ∑ i : Fin D.count, c i * (⅟(Fintype.card G : ℂ) • ∑ g : G,
          (D.representation i).character g * (D.representation j).character g⁻¹) := by
      calc ⅟(Fintype.card G : ℂ) • ∑ g : G,
              (∑ i, c i * (D.representation i).character g) * (D.representation j).character g⁻¹
          _ = ⅟(Fintype.card G : ℂ) • ∑ g : G, ∑ i,
              c i * (D.representation i).character g * (D.representation j).character g⁻¹ := by
            congr 1; apply Finset.sum_congr rfl; intro g _; rw [Finset.sum_mul]
          _ = ⅟(Fintype.card G : ℂ) • ∑ i, ∑ g : G,
              c i * (D.representation i).character g * (D.representation j).character g⁻¹ := by
            congr 1; rw [Finset.sum_comm]
          _ = ⅟(Fintype.card G : ℂ) • ∑ i,
              c i * ∑ g : G, (D.representation i).character g * (D.representation j).character g⁻¹ := by
            congr 1; apply Finset.sum_congr rfl; intro i _
            conv_lhs => arg 2; ext g; rw [mul_assoc]
            rw [← Finset.mul_sum]
          _ = ∑ i, c i * (⅟(Fintype.card G : ℂ) •
              ∑ g : G, (D.representation i).character g * (D.representation j).character g⁻¹) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl; intro i _
            rw [Algebra.mul_smul_comm]

    simp_rw [stepB, h_orth] at stepA
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at stepA
    exact stepA

  have h_li_Q : LinearIndependent ℚ (fun i : Fin D.count => (D.representation i).character) :=
    h_li_C.restrict_scalars (smul_left_injective ℚ one_ne_zero)

  have hS_sub_Q : Submodule.span ℚ S ≤ Submodule.span ℚ
      (Set.range (fun i : Fin D.count => (D.representation i).character)) := by
    apply Submodule.span_le.mpr
    intro s hs
    exact Submodule.span_mono (by intro x ⟨i, hi⟩; exact ⟨i, hi⟩)
      (Submodule.span_le_restrictScalars (R := ℤ) (S := ℚ) _ (hS_in_ℤspan s hs))

  have hV_in_Q : V.character ∈ Submodule.span ℚ
      (Set.range (fun i : Fin D.count => (D.representation i).character)) := by
    rw [hV_char]
    exact Submodule.subset_span ⟨j₀, rfl⟩





  obtain ⟨ℓ, hℓ_ne, hℓ_ker⟩ := Submodule.exists_le_ker_of_notMem hV_not_mem

  have hℓS : ∀ s ∈ S, ℓ s = 0 := fun s hs =>
    LinearMap.mem_ker.mp (hℓ_ker (Submodule.subset_span hs))

  let c : Fin D.count → ℂ := fun i =>
    algebraMap ℚ ℂ (ℓ ((D.representation i).character))

  haveI (i : Fin D.count) : CategoryTheory.Simple (D.representation i) := D.simple_representation i
  have horth_G2 : ∀ i j : Fin D.count,
      ∑ g : G, (D.representation i).character g * (D.representation j).character g⁻¹ =
      if i = j then (Fintype.card G : ℂ) else 0 := by
    intro i j
    have h := RepresentationTheory.FDRep.Character.normalizedCharacterSum_eq_ite_iso_of_simple (D.representation i) (D.representation j)
    rw [smul_eq_mul] at h
    have hinv : ∀ (x y : ℂ), ⅟(Fintype.card G : ℂ) * x = y →
        x = (Fintype.card G : ℂ) * y := fun x y h => by
      rw [← h, ← mul_assoc, mul_invOf_self, one_mul]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]
      exact (hinv _ _ (by rw [if_pos ⟨CategoryTheory.Iso.refl _⟩] at h; exact h)).trans
        (mul_one _)
    · rw [if_neg hij]
      exact (hinv _ _ (by rw [if_neg (fun ⟨iso⟩ => hij
        (D.representation_index_eq_of_iso i j ⟨iso⟩))] at h; exact h)).trans (mul_zero _)

  have hf_inner_span : ∀ s : G → ℂ,
      s ∈ Submodule.span ℤ (Set.range (fun i : Fin D.count => (D.representation i).character)) →
      ∑ g : G, (∑ i : Fin D.count, c i * (D.representation i).character g) * s g⁻¹ =
      (Fintype.card G : ℂ) * algebraMap ℚ ℂ (ℓ s) := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      conv_lhs => arg 2; ext g; rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, horth_G2, mul_ite, mul_zero]
      simp [Finset.sum_ite_eq', Finset.mem_univ, c, mul_comm]
    | zero => simp [map_zero]
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add, _root_.map_add]
      rw [hx, hy]
    | smul n x _ hx =>

      have lhs_eq : ∑ g : G, (∑ i, c i * (D.representation i).character g) * (n • x) g⁻¹ =
          (n : ℂ) * ∑ g, (∑ i, c i * (D.representation i).character g) * x g⁻¹ := by
        simp only [Pi.smul_apply, zsmul_eq_mul, mul_left_comm _ (n : ℂ)]
        rw [← Finset.mul_sum]

      have rhs_eq : (Fintype.card G : ℂ) * algebraMap ℚ ℂ (ℓ (n • x)) =
          (n : ℂ) * ((Fintype.card G : ℂ) * algebraMap ℚ ℂ (ℓ x)) := by
        rw [map_zsmul ℓ, zsmul_eq_mul, _root_.map_mul, map_intCast]; ring
      rw [lhs_eq, hx, rhs_eq]

  have hf_orth : ∀ H ∈ X, ∀ (W : FDRep ℂ ↥H),
      ∑ g : G, (∑ i : Fin D.count, c i * (D.representation i).character g) *
        RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character g⁻¹ = 0 := by
    intro H hH W
    rw [hf_inner_span _ (hS_in_ℤspan _ ⟨H, hH, W, rfl⟩),
      hℓS _ ⟨H, hH, W, rfl⟩, map_zero, mul_zero]

  have hf_class : ∀ g x : G,
      (∑ i : Fin D.count, c i * (D.representation i).character (x * g * x⁻¹)) =
      (∑ i : Fin D.count, c i * (D.representation i).character g) := by
    intro g x; congr 1; ext i; congr 1; exact FDRep.char_conj _ _ _

  have hf_zero := horth_trivial
    (fun g => ∑ i : Fin D.count, c i * (D.representation i).character g) hf_class hf_orth

  have hc_ne : c j₀ ≠ 0 := by
    simp only [c, ← hV_char]
    intro h; exact hℓ_ne ((algebraMap ℚ ℂ).injective (by rwa [map_zero]))

  rw [Fintype.linearIndependent_iff] at h_li_C
  exact absurd (h_li_C c (by ext g; simpa [smul_eq_mul] using congr_fun hf_zero g) j₀) hc_ne
















private lemma artin_forward {G : Type} [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X)
    (hcov : ∀ g : G, ∃ H ∈ X, g ∈ H)
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    V.character ∈ Submodule.span ℚ
      {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character} := by
  apply artin_Q_span_of_induced_chars X hX hcov

  intro f hf_class hf_orth



  have hvan : ∀ H ∈ X, ∀ h : ↥H, f ↑h = 0 := by
    intro H hHX
    apply class_fun_vanishes_on_subgroup_of_orthogonal H f hf_class
    intro W hW




    classical
    have hfrob := frobenius_char_reciprocity H f W.character hf_class
    have hzero := hf_orth H hHX W
    rw [hzero] at hfrob

    have hG_ne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hH_ne : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hcoeff_ne : (Fintype.card G : ℂ) * (Fintype.card ↥H : ℂ)⁻¹ ≠ 0 :=
      mul_ne_zero hG_ne (inv_ne_zero hH_ne)


    exact mul_left_cancel₀ hcoeff_ne (by rw [mul_zero]; exact hfrob.symm)

  exact covering_implies_vanishing X hcov f hvan


private def trivialRep (G : Type) [Group G] : Representation ℂ G ℂ := 1


private def trivialFDRep (G : Type) [Group G] [Fintype G] : FDRep ℂ G :=
  FDRep.of (trivialRep G)


private theorem trivialFDRep_character (G : Type) [Group G] [Fintype G] (g : G) :
    (trivialFDRep G).character g = 1 := by
  change LinearMap.trace ℂ _ ((trivialRep G) g) = 1
  simp [trivialRep, MonoidHom.one_apply, LinearMap.trace_one, Module.finrank_self]

open CategoryTheory in

private lemma simple_of_full_faithful_preservesMono
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) :=
        (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
          (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

open CategoryTheory in

private theorem trivialFDRep_simple (G : Type) [Group G] [Fintype G] :
    Simple (trivialFDRep G) := by


  let ρ := trivialRep G
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule := by
    rw [isSimpleModule_iff]




    exact is_simple_module_of_finrank_eq_one
      (ρ.asModuleEquiv.finrank_eq.trans (Module.finrank_self ℂ))

  haveI : Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule) :=
    simple_of_isSimpleModule

  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)
  haveI : Simple
      (E.functor.obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (trivialFDRep G))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule)
    infer_instance
  haveI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (trivialFDRep G)) :=
    simple_of_full_faithful_preservesMono E.functor _
  exact simple_of_full_faithful_preservesMono (forget₂ (FDRep ℂ G) (Rep ℂ G)) _













/-- For a conjugation-stable family of subgroups, the auxiliary covering condition is equivalent to character membership in the displayed span. -/
@[source_ref "Chapter5/Theorem5.26.1" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.26.1" (role := primary)]
theorem RepresentationTheory.AuxiliarySubgroupFunctions.auxiliary_cover_iff_character_mem_span
    (G : Type) [Group G] [Fintype G]
    (X : Set (Subgroup G))
    (hX : ∀ H ∈ X, ∀ g : G, H.map (MulAut.conj g).toMonoidHom ∈ X) :
    (∀ g : G, ∃ H ∈ X, g ∈ H) ↔
    (∀ (V : FDRep ℂ G), CategoryTheory.Simple V →
      V.character ∈ Submodule.span ℚ
        {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
          f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character}) := by
  constructor
  ·


    intro hcov V hV
    exact artin_forward X hX hcov V
  ·



    intro hspan
    by_contra hncov
    push Not at hncov
    obtain ⟨g₀, hg₀⟩ := hncov

    have hconj_out : ∀ H ∈ X, ∀ x : G, x⁻¹ * g₀ * x ∉ H := by
      intro H hHX x hmem
      have : g₀ ∈ H.map (MulAut.conj x).toMonoidHom := by
        apply Subgroup.mem_map.mpr
        refine ⟨x⁻¹ * g₀ * x, hmem, ?_⟩
        change x * (x⁻¹ * g₀ * x) * x⁻¹ = g₀
        group
      exact hg₀ _ (hX H hHX x) this

    have hgen_vanish : ∀ f ∈ ({f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
        f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character} : Set (G → ℂ)),
        f g₀ = 0 := by
      rintro f ⟨H, hHX, W, rfl⟩
      classical
      simp only [RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction]
      suffices h : ∑ x : G, (if h : x⁻¹ * g₀ * x ∈ H
          then W.character ⟨x⁻¹ * g₀ * x, h⟩ else 0) = 0 by
        rw [h, mul_zero]
      apply Finset.sum_eq_zero
      intro x _
      exact dif_neg (hconj_out H hHX x)

    have hspan_vanish : ∀ f ∈ Submodule.span ℚ
        {f : G → ℂ | ∃ H ∈ X, ∃ (W : FDRep ℂ ↥H),
          f = RepresentationTheory.AuxiliarySubgroupFunctions.auxiliaryFunction H W.character},
        f g₀ = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx => exact hgen_vanish x hx
      | zero => rfl
      | add x y _ _ hx hy => simp [Pi.add_apply, hx, hy]
      | smul r x _ hx => simp [Pi.smul_apply, hx]

    have hmem := hspan (trivialFDRep G) (trivialFDRep_simple G)
    have hval := hspan_vanish _ hmem
    rw [trivialFDRep_character] at hval
    exact one_ne_zero hval
