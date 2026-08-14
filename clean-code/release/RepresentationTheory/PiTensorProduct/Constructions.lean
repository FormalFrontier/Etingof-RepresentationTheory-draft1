import Mathlib
import RepresentationTheory.Alignment.Attribute

/-!
# Constructions for finite pi tensor products

This module defines selected subsets, maps, and subalgebras associated with finite pi tensor
products. It also proves spanning and equality results for these constructions over fields of
characteristic zero.
-/

open scoped TensorProduct

namespace RepresentationTheory.PiTensorProduct.Constructions

section Span

variable (k : Type) [Field k]
  (U : Type*) [AddCommGroup U] [Module k U] [Module.Finite k U]
  (n : ℕ)

/-- A designated subset of the symmetric power indexed by a finite type. -/
def symmetricPowerSubset : Set (Sym[k]^n U) :=
  Set.range (fun u : U => SymmetricPower.tprod k (fun (_ : Fin n) => u))

private lemma sum_powerset_neg_one_pow_card_eq_zero
    {α : Type*} {x : Finset α} (hx : x.Nonempty) :
    (∑ m ∈ x.powerset, (-1 : k) ^ m.card) = 0 := by
  have hZ := Finset.sum_powerset_neg_one_pow_card_of_nonempty hx

  have : (∑ m ∈ x.powerset, (-1 : k) ^ m.card) =
      ((∑ m ∈ x.powerset, (-1 : ℤ) ^ m.card : ℤ) : k) := by
    rw [Int.cast_sum]
    congr 1; ext m
    simp [Int.cast_pow]
  rw [this, hZ, Int.cast_zero]

private lemma alternating_superset_sum
    (T : Finset (Fin n)) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
      (-1 : k) ^ (n - S.card)) =
    if T = Finset.univ then 1 else 0 := by
  classical





  split_ifs with hT
  ·
    subst hT
    have : Finset.univ.powerset.filter (fun S => Finset.univ ⊆ S) =
        {(Finset.univ : Finset (Fin n))} := by
      ext S; simp [Finset.univ_subset_iff]
    rw [this, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero]
  ·
    have hC : (Finset.univ \ T).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun h => hT (Finset.univ_subset_iff.mp h)

    rw [show ∑ S ∈ Finset.univ.powerset.filter (fun S => T ⊆ S),
          (-1 : k) ^ (n - S.card) =
        ∑ T' ∈ (Finset.univ \ T).powerset,
          (-1 : k) ^ ((Finset.univ \ T).card - T'.card) from by
      apply Finset.sum_nbij' (· \ T) (· ∪ T)
      ·
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
        exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl T)
      ·
        intro T' hT'
        simp only [Finset.mem_powerset] at hT'
        simp only [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.union_subset (hT'.trans Finset.sdiff_subset) (Finset.subset_univ T),
               Finset.subset_union_right⟩
      ·
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        exact Finset.sdiff_union_of_subset hS.2
      ·
        intro T' hT'
        simp only [Finset.mem_powerset] at hT'
        rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint]
        exact Finset.disjoint_of_subset_left hT' disjoint_sdiff_self_left
      ·
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        congr 1

        have h1 : (S \ T).card + T.card = S.card :=
          Finset.card_sdiff_add_card_eq_card hS.2
        have h2 : ((Finset.univ : Finset (Fin n)) \ T).card + T.card =
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
        have h3 : S.card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card hS.1
        have h4 : (S \ T).card ≤ ((Finset.univ : Finset (Fin n)) \ T).card :=
          Finset.card_le_card (Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl T))
        simp only [Finset.card_univ, Fintype.card_fin] at h2 h3
        omega]


    set C := Finset.univ \ T with hCdef
    have factor : ∀ T' ∈ C.powerset, (-1 : k) ^ (C.card - T'.card) =
        (-1 : k) ^ C.card * (-1 : k) ^ T'.card := by
      intro T' hT'
      simp only [Finset.mem_powerset] at hT'
      have hle := Finset.card_le_card hT'
      have hmul : (-1 : k) ^ (C.card - T'.card) * (-1 : k) ^ T'.card =
          (-1 : k) ^ C.card := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hsq : (-1 : k) ^ T'.card * (-1 : k) ^ T'.card = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      calc (-1 : k) ^ (C.card - T'.card)
          = (-1 : k) ^ (C.card - T'.card) * 1 := (mul_one _).symm
        _ = (-1 : k) ^ (C.card - T'.card) *
            ((-1 : k) ^ T'.card * (-1 : k) ^ T'.card) := by rw [hsq]
        _ = (-1 : k) ^ (C.card - T'.card) * (-1 : k) ^ T'.card *
            (-1 : k) ^ T'.card := by rw [mul_assoc]
        _ = (-1 : k) ^ C.card * (-1 : k) ^ T'.card := by rw [hmul]
    rw [Finset.sum_congr rfl factor, ← Finset.mul_sum]
    rw [sum_powerset_neg_one_pow_card_eq_zero (k := k) hC, mul_zero]

omit [Module.Finite k U] in
private lemma polarization_eq [CharZero k] (f : Fin n → U) :
    (n.factorial : k) • SymmetricPower.tprod k f =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((-1 : k) ^ (n - S.card)) • SymmetricPower.tprod k (fun _ => ∑ i ∈ S, f i) := by
  classical

  conv_rhs =>
    arg 2; ext S
    rw [show (-1 : k) ^ (n - S.card) • SymmetricPower.tprod k (fun _ => ∑ i ∈ S, f i) =
        ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S),
          (-1 : k) ^ (n - S.card) • (SymmetricPower.tprod k) (fun i => f (r i)) by
      rw [MultilinearMap.map_sum_finset (SymmetricPower.tprod k) (fun _ => f) (fun _ => S)]
      rw [Finset.smul_sum]]

  rw [Finset.sum_comm'
    (s' := fun r => Finset.univ.powerset.filter (fun S => ∀ i, r i ∈ S))
    (t' := Fintype.piFinset (fun _ : Fin n => Finset.univ))
    (h := by
      intro S r
      simp only [Finset.mem_powerset, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ]
      tauto)]

  simp_rw [← Finset.sum_smul]

  have coeff_eq : ∀ r : Fin n → Fin n,
      (∑ S ∈ Finset.univ.powerset.filter (fun S => ∀ j, r j ∈ S),
        (-1 : k) ^ (n - S.card)) =
      if Finset.image r Finset.univ = Finset.univ then 1 else 0 := by
    intro r
    convert alternating_superset_sum k n (Finset.image r Finset.univ) using 2
    ext S; simp [Finset.subset_iff]
  simp_rw [coeff_eq]

  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]




  have tprod_perm : ∀ (σ : Equiv.Perm (Fin n)),
      (⨂ₛ[k] (i : Fin n), f (σ i)) = SymmetricPower.tprod k f := by
    intro σ; exact SymmetricPower.tprod_equiv σ f

  have all_eq : ∀ x ∈ (Fintype.piFinset fun _ : Fin n => Finset.univ).filter
        (fun x => Finset.image x Finset.univ = Finset.univ),
      (⨂ₛ[k] (i : Fin n), f (x i)) = SymmetricPower.tprod k f := by
    intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx
    have hxsurj : Function.Surjective x := by
      intro b
      have hb : b ∈ Finset.image x Finset.univ := by rw [hx.2]; exact Finset.mem_univ b
      exact let ⟨a, _, ha⟩ := Finset.mem_image.mp hb; ⟨a, ha⟩
    exact tprod_perm (Equiv.ofBijective x
      ((Finite.surjective_iff_bijective (α := Fin n)).mp hxsurj))
  rw [Finset.sum_congr rfl all_eq, Finset.sum_const, ← Nat.cast_smul_eq_nsmul k]
  congr 1

  norm_cast

  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) :=
    ⟨fun σ => σ, fun σ₁ σ₂ h => Equiv.ext (congr_fun h)⟩
  have hmap : (Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset (Fin n))).filter
        (fun x => Finset.image x Finset.univ = Finset.univ) =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).map e := by
    ext r
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_univ,
      Finset.mem_map]
    constructor
    · intro ⟨_, hr⟩
      have hsurj : Function.Surjective r := by
        intro b
        have : b ∈ Finset.image r Finset.univ := by rw [hr]; exact Finset.mem_univ b
        exact let ⟨a, _, ha⟩ := Finset.mem_image.mp this; ⟨a, ha⟩
      exact ⟨Equiv.ofBijective r
        ((Finite.surjective_iff_bijective (α := Fin n)).mp hsurj), trivial, rfl⟩
    · rintro ⟨σ, _, rfl⟩
      exact ⟨fun _ => trivial, Finset.image_univ_of_surjective σ.surjective⟩
  rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

omit [Module.Finite k U] in
/-- In characteristic zero, the span of the designated symmetric-power subset is the whole space. -/
@[source_ref "Chapter5/Lemma5.18.3" (role := primary)]
theorem span_symmetricPowerSubset_eq_top [CharZero k] :
    Submodule.span k (symmetricPowerSubset k U n) = ⊤ := by
  rw [eq_top_iff, ← SymmetricPower.span_tprod_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨f, rfl⟩

  have hfact : (n.factorial : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [show SymmetricPower.tprod k f =
      (n.factorial : k)⁻¹ • ((n.factorial : k) • SymmetricPower.tprod k f) from
    (inv_smul_smul₀ hfact _).symm]
  rw [polarization_eq]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨∑ i ∈ S, f i, rfl⟩

end Span

section Generated

variable (k : Type*) [Field k]
  (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V]
  (n : ℕ)

/-- The specified subalgebra of endomorphisms of a finite pi tensor product. -/
noncomputable def piTensorEndSubalgebra :
    Subalgebra k (Module.End k (⨂[k] (_ : Fin n), V)) :=
  Algebra.adjoin k (Set.range fun (b : Module.End k V) =>
    ∑ i : Fin n,
      PiTensorProduct.map (fun j => if j = i then b else LinearMap.id))

/-- An alternative specified subalgebra of pi tensor product endomorphisms. -/
noncomputable def piTensorEndSubalgebraAlternate :
    Subalgebra k (Module.End k (⨂[k] (_ : Fin n), V)) :=
  Algebra.adjoin k (Set.range fun (f : Module.End k V) =>
    PiTensorProduct.map (fun _ => f))



private lemma polynomial_coeffs_in_submodule [CharZero k]
    {A : Type*} [AddCommGroup A] [Module k A]
    (M : Submodule k A)
    (d : ℕ) (a : Fin (d + 1) → A)
    (h_eval : ∀ j : Fin (d + 1),
      ∑ m : Fin (d + 1), ((j : ℕ) : k) ^ (m : ℕ) • a m ∈ M) :
    ∀ m : Fin (d + 1), a m ∈ M := by
  set v : Fin (d+1) → k := fun j => ((j : ℕ) : k)
  set V : Matrix (Fin (d+1)) (Fin (d+1)) k := Matrix.vandermonde v
  have hv_inj : Function.Injective v := by
    intro i j h; simp only [v] at h; exact Fin.ext (Nat.cast_injective h)
  have hV_unit : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]; exact hv_inj
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hV_unit
  intro m
  suffices h : a m = ∑ j : Fin (d+1), V⁻¹ m j •
      (∑ i : Fin (d+1), v j ^ (i : ℕ) • a i) by
    rw [h]; exact M.sum_mem fun j _ => M.smul_mem _ (h_eval j)
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have coeff_eq : ∀ i : Fin (d+1),
      (∑ j : Fin (d+1), V⁻¹ m j * v j ^ (i : ℕ)) = if m = i then 1 else 0 := by
    intro i
    change (∑ j, V⁻¹ m j * V j i) = _
    rw [show ∑ j, V⁻¹ m j * V j i = (V⁻¹ * V) m i from rfl, hWV, Matrix.one_apply]
  simp_rw [coeff_eq]; simp [ite_smul]


private lemma card_finset_fin_lt (S : Finset (Fin n)) : S.card < n + 1 := by
  have := S.card_le_univ; simp at this; omega


open Finset in
set_option maxHeartbeats 800000 in
private lemma sum_regroup_by_card
    {M : Type*} [AddCommMonoid M] [Module k M]
    (f : Finset (Fin n) → M) (c : k) :
    ∑ S : Finset (Fin n), c ^ S.card • f S =
    ∑ m : Fin (n + 1), c ^ (m : ℕ) •
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card = m.val), f S := by
  let g : Finset (Fin n) → Fin (n + 1) := fun S =>
    ⟨S.card, card_finset_fin_lt n S⟩
  have hg : ∀ S ∈ (univ : Finset (Finset (Fin n))), g S ∈ (univ : Finset (Fin (n+1))) :=
    fun _ _ => mem_univ _
  rw [← sum_fiberwise_of_maps_to hg (fun S => c ^ S.card • f S)]
  congr 1; ext m
  simp_rw [smul_sum]
  apply sum_congr
  · ext S; simp only [mem_filter, mem_univ, true_and, g]
    constructor
    · intro h; have := congr_arg Fin.val h; simpa using this
    · intro h; exact Fin.ext h
  · intro S hS; simp only [mem_filter, mem_univ, true_and] at hS; simp [hS]


set_option maxHeartbeats 800000 in
private lemma sum_card_pred_eq_sum_erase (hn : 0 < n)
    {M : Type*} [AddCommMonoid M]
    (f : Finset (Fin n) → M) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S.card = n - 1), f S =
    ∑ i : Fin n, f (Finset.univ.erase i) := by
  symm
  apply Finset.sum_bij (fun i _ => Finset.univ.erase i)
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ h
    by_contra hij
    have : i ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
    rw [← h] at this
    exact absurd rfl (Finset.mem_erase.mp this).1
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have hcard : (Finset.univ \ S).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
        Fintype.card_fin]; omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, Finset.mem_univ _, ?_⟩
    ext x; constructor
    · intro hxE
      have hne := (Finset.mem_erase.mp hxE).1
      by_contra hxS
      have : x ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxS⟩
      rw [hi] at this
      exact hne (Finset.mem_singleton.mp this)
    · intro hxS
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hxi
      have : x ∈ Finset.univ \ S := hi ▸ Finset.mem_singleton.mpr hxi
      exact (Finset.mem_sdiff.mp this).2 hxS
  · intro i _; rfl


omit [Module.Finite k V] in
private lemma piecewise_erase_eq {α : Type*} [DecidableEq α] [Fintype α]
    {β : Type*} (i : α) (f g : β) :
    (Finset.univ.erase i).piecewise (fun _ => f) (fun _ => g) =
    fun j => if j = i then g else f := by
  ext x
  simp only [Finset.piecewise, Finset.mem_erase, Finset.mem_univ, and_true]

  by_cases hx : x = i <;> simp [hx]


set_option maxHeartbeats 3200000 in
omit [Module.Finite k V] in
private lemma diag_le_fullDiag [CharZero k] :
    piTensorEndSubalgebra k V n ≤ piTensorEndSubalgebraAlternate k V n := by
  apply Algebra.adjoin_le
  rintro _ ⟨b, rfl⟩


  by_cases hn : n = 0
  · subst hn; simp [Finset.sum_empty]
  · push Not at hn; have hn' : 0 < n := Nat.pos_of_ne_zero hn

    let mm := PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ => V)

    set a : Fin (n + 1) → Module.End k (⨂[k] (_ : Fin n), V) :=
      fun m => ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => S.card = m.val),
        mm (S.piecewise (fun _ => LinearMap.id) (fun _ => b))

    have h_eval : ∀ j : Fin (n + 1),
        ∑ m : Fin (n + 1), ((j : ℕ) : k) ^ (m : ℕ) • a m =
          mm (fun _ => ((j : ℕ) : k) • LinearMap.id + b) := by
      intro j
      simp only [a]
      rw [← sum_regroup_by_card]
      symm
      have key : (fun (_ : Fin n) => ((j : ℕ) : k) • LinearMap.id + b) =
          (fun _ => ((j : ℕ) : k) • LinearMap.id) + (fun _ => b) := by
        ext; simp [Pi.add_apply]
      rw [key, mm.map_add_univ]
      apply Finset.sum_congr rfl; intro S _
      set base := S.piecewise (fun _ : Fin n => LinearMap.id) (fun _ => b)
      have h2 := mm.map_piecewise_smul (fun _ => ((j : ℕ) : k)) base S
      simp only [Finset.prod_const] at h2
      rw [← h2]
      congr 1; funext i
      simp only [Finset.piecewise, base]
      split_ifs with h <;> simp

    have h_mem : ∀ j : Fin (n + 1),
        ∑ m : Fin (n + 1), ((j : ℕ) : k) ^ (m : ℕ) • a m ∈
          (piTensorEndSubalgebraAlternate k V n).toSubmodule := by
      intro j; rw [h_eval]
      exact Algebra.subset_adjoin ⟨_, rfl⟩

    have h_all := polynomial_coeffs_in_submodule k
      (piTensorEndSubalgebraAlternate k V n).toSubmodule n a h_mem

    have h_target := h_all ⟨n - 1, by omega⟩
    simp only [a] at h_target
    rw [sum_card_pred_eq_sum_erase n hn'] at h_target


    simp_rw [show ∀ i : Fin n, mm ((Finset.univ.erase i).piecewise
        (fun _ => LinearMap.id) (fun _ => b)) =
        PiTensorProduct.map (fun j => if j = i then b else LinearMap.id) from
      fun i => by
        change mm _ = mm _; congr 1
        rw [piecewise_erase_eq]] at h_target
    exact h_target






set_option maxHeartbeats 800000 in
omit [Module.Finite k V] in
private lemma fullDiag_le_diag [CharZero k] :
    piTensorEndSubalgebraAlternate k V n ≤ piTensorEndSubalgebra k V n := by
  apply Algebra.adjoin_le
  rintro _ ⟨f, rfl⟩


  set B : Fin n → Module.End k (⨂[k] (_ : Fin n), V) :=
    fun i => PiTensorProduct.map (fun j => if j = i then f else LinearMap.id)

  have hcomm : ∀ i j, Commute (B i) (B j) := by
    intro i j
    change B i * B j = B j * B i
    simp only [B, ← PiTensorProduct.map_mul]
    congr 1; ext x

    by_cases hi : x = i <;> by_cases hj : x = j <;> simp_all

  have hpow : ∀ i m, B i ^ m = PiTensorProduct.map
      (fun j => if j = i then f ^ m else LinearMap.id) := by
    intro i m; simp only [B, ← PiTensorProduct.map_pow]
    congr 1; ext x; by_cases h : x = i <;> simp [h]

  have hpsum : ∀ m, 0 < m → ∑ i, B i ^ m ∈ (piTensorEndSubalgebra k V n : Set _) := by
    intro m _; simp_rw [hpow]; exact Algebra.subset_adjoin ⟨f ^ m, rfl⟩

  set e : ℕ → Module.End k (⨂[k] (_ : Fin n), V) := fun m =>
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      S.noncommProd B (fun i _ j _ _ => hcomm i j)

  suffices heq : e n = PiTensorProduct.map (fun _ => f) by
    change PiTensorProduct.map (fun _ => f) ∈ _
    rw [← heq]

    suffices ∀ m, e m ∈ piTensorEndSubalgebra k V n from this n
    intro m
    induction m using Nat.strongRecOn with | ind m ih => ?_
    by_cases hm : m = 0
    · subst hm; simp [e, Finset.powersetCard_zero]
    ·

        have hm' : 0 < m := Nat.pos_of_ne_zero hm
        have hcast : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm

        have newton : (m : k) • e m =
            (-1 : k) ^ (m + 1) • ∑ j ∈ Finset.range m,
              ((-1 : k) ^ j) • (e j * ∑ i : Fin n, B i ^ (m - j)) := by

          set A := Algebra.adjoin k (Set.range B)
          have hBA : ∀ i, B i ∈ A := fun i => Algebra.subset_adjoin ⟨i, rfl⟩

          have hcommA : ∀ (a b : A), a * b = b * a := by
            intro a b; apply Subtype.ext; change a.val * b.val = b.val * a.val
            exact Algebra.adjoin_induction₂
              (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ => hi ▸ hj ▸ hcomm i j)
              (fun r₁ r₂ => by rw [← map_mul, mul_comm, map_mul])
              (fun r _ _ => Algebra.commutes r _)
              (fun r _ _ => (Algebra.commutes r _).symm)
              (fun _ _ _ _ _ _ h₁ h₂ => by rw [add_mul, mul_add, h₁, h₂])
              (fun _ _ _ _ _ _ h₁ h₂ => by rw [mul_add, add_mul, h₁, h₂])
              (fun _ _ _ _ _ _ h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc])
              (fun _ _ _ _ _ _ h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc])
              a.property b.property

          letI : CommRing A := { show Ring A from inferInstance with mul_comm := hcommA }

          set B' : Fin n → A := fun i => ⟨B i, hBA i⟩

          set ψ : MvPolynomial (Fin n) k →ₐ[k] A := MvPolynomial.aeval B' with hψ_def

          have prod_val : ∀ S : Finset (Fin n),
              (∏ i ∈ S, B' i : A).val =
                S.noncommProd B (fun i _ j _ _ => hcomm i j) := by
            intro S
            induction S using Finset.cons_induction_on with
            | empty => simp [Finset.noncommProd_empty]
            | cons a s ha ih =>
              rw [Finset.prod_cons, Finset.noncommProd_cons]
              change (B' a * ∏ i ∈ s, B' i).val = B a * s.noncommProd B _
              simp only [Subalgebra.coe_mul]; rw [ih]

          have esymm_val : ∀ j,
              (ψ (MvPolynomial.esymm (Fin n) k j) : Module.End k _) = e j := by
            intro j
            simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X, hψ_def, e]
            rw [AddSubmonoidClass.coe_finsetSum]
            exact Finset.sum_congr rfl (fun T _ => prod_val T)

          have psum_val : ∀ d,
              (ψ (MvPolynomial.psum (Fin n) k d) : Module.End k _) =
                ∑ i : Fin n, B i ^ d := by
            intro d
            simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, hψ_def]
            simp only [AddSubmonoidClass.coe_finsetSum, SubmonoidClass.coe_pow, B']

          set Φ : MvPolynomial (Fin n) k →ₐ[k] Module.End k (⨂[k] (_ : Fin n), V) :=
            A.val.comp ψ
          have Φ_esymm : ∀ j, Φ (MvPolynomial.esymm (Fin n) k j) = e j := esymm_val
          have Φ_psum : ∀ d, Φ (MvPolynomial.psum (Fin n) k d) = ∑ i : Fin n, B i ^ d :=
            psum_val

          have h := congr_arg Φ (MvPolynomial.mul_esymm_eq_sum (Fin n) k m)
          simp only [map_mul, map_pow, map_neg, map_one, map_sum,
            Φ_esymm, Φ_psum] at h
          rw [map_natCast Φ m] at h


          rw [show (Finset.HasAntidiagonal.antidiagonal m).filter (fun x => x.1 < m) =
              (Finset.range m).map ⟨fun j => (j, m - j), fun a b h => by
                simp [Prod.ext_iff] at h; exact h.1⟩ from by
            ext ⟨a, b⟩
            simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
              Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
            constructor
            · rintro ⟨hab, ha⟩
              exact ⟨a, ha, by ext <;> omega⟩
            · rintro ⟨j, hj, hpair⟩
              rcases Prod.ext_iff.mp hpair with ⟨rfl, hb⟩
              exact ⟨by omega, by omega⟩,
            Finset.sum_map] at h
          simp only [Function.Embedding.coeFn_mk] at h


          rw [Nat.cast_smul_eq_nsmul k m (e m), nsmul_eq_mul, h]


          have neg_pow_smul : ∀ (p : ℕ)
              (x : Module.End k (⨂[k] (_ : Fin n), V)),
              (-1 : Module.End k (⨂[k] (_ : Fin n), V)) ^ p * x = (-1 : k) ^ p • x := by
            intro p x
            have : (-1 : Module.End k (⨂[k] (_ : Fin n), V)) =
                algebraMap k _ (-1 : k) := by
              simp [map_neg, map_one]
            rw [this, ← map_pow, Algebra.smul_def]
          rw [neg_pow_smul]; congr 1
          apply Finset.sum_congr rfl; intro j _
          rw [mul_assoc, neg_pow_smul]
        rw [show e m = (m : k)⁻¹ • ((m : k) • e m) from (inv_smul_smul₀ hcast _).symm,
          newton]
        apply Subalgebra.smul_mem
        apply Subalgebra.smul_mem
        apply Subalgebra.sum_mem
        intro j hj
        have hjm : j < m := Finset.mem_range.mp hj
        apply Subalgebra.smul_mem
        apply Subalgebra.mul_mem
        · exact ih j hjm
        · exact hpsum (m - j) (Nat.sub_pos_of_lt hjm)


  simp only [e]
  have hcard : (Finset.univ : Finset (Fin n)).card = n :=
    Finset.card_univ.trans (Fintype.card_fin n)
  have huniv : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [hcard] at this
  rw [huniv, Finset.sum_singleton]



  set piF : Fin n → (Fin n → Module.End k V) :=
    fun i j => if j = i then f else LinearMap.id with hpiF_def
  have hpiFcomm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ∀ j ∈ (Finset.univ : Finset (Fin n)), i ≠ j →
      Commute (piF i) (piF j) := by
    intro i _ j _ _
    ext x; simp only [Pi.mul_apply, piF]
    by_cases hi : x = i <;> by_cases hj : x = j <;> simp_all

  have piF_prod : Finset.univ.noncommProd piF hpiFcomm = fun _ => f := by
    funext j
    change (Pi.evalMonoidHom (fun _ : Fin n => Module.End k V) j)
      (Finset.univ.noncommProd piF hpiFcomm) = f
    rw [Finset.map_noncommProd _ _ _ (Pi.evalMonoidHom (fun _ : Fin n => Module.End k V) j)]
    change Finset.univ.noncommProd (fun i => piF i j) _ = f
    simp only [piF]
    conv_lhs => rw [← Finset.mul_noncommProd_erase _ (Finset.mem_univ j)]
    simp only [ite_true]
    suffices h : (Finset.univ.erase j).noncommProd
        (fun i => if j = i then f else LinearMap.id) _ = 1 by
      rw [h, mul_one]
    rw [Finset.noncommProd_eq_pow_card _ _ _ (1 : Module.End k V)
      (fun i hi => by simp only [Ne.symm (Finset.mem_erase.mp hi).1, ite_false]; rfl), one_pow]

  have key := Finset.map_noncommProd Finset.univ piF hpiFcomm PiTensorProduct.mapMonoidHom

  rw [piF_prod] at key



  have hBeq : ∀ i ∈ Finset.univ, B i = PiTensorProduct.mapMonoidHom (piF i) := by
    intro i _; simp [B, piF]
  rw [Finset.noncommProd_congr rfl hBeq, ← key]; rfl

omit [Module.Finite k V] in
/-- The two displayed subalgebras of pi tensor product endomorphisms agree in characteristic zero. -/
theorem piTensorEndSubalgebra_eq_alternate [CharZero k] :
    piTensorEndSubalgebra k V n = piTensorEndSubalgebraAlternate k V n :=
  le_antisymm (diag_le_fullDiag k V n) (fullDiag_le_diag k V n)

end Generated

section GeneralAlgebra

/-!
## Algebra-valued constructions

This section develops analogous maps and subalgebras for a general algebra and compares the
resulting generated subalgebras in characteristic zero.
-/

open _root_.PiTensorProduct

variable (k : Type*) [Field k]
  (A : Type*) [Ring A] [Algebra k A]
  (n : ℕ)

/-- A map from an algebra to its finite pi tensor product. -/
noncomputable def toPiTensorProduct (a : A) : ⨂[k] (_ : Fin n), A :=
  ∑ i : Fin n, singleAlgHom (R := k) (A := fun _ : Fin n => A) i a

/-- An alternative map from an algebra to its finite pi tensor product. -/
noncomputable def toPiTensorProductAlternate (a : A) : ⨂[k] (_ : Fin n), A :=
  tprod k (fun _ : Fin n => a)

/-- The specified subalgebra of a finite pi tensor product of an algebra. -/
noncomputable def piTensorSubalgebra : Subalgebra k (⨂[k] (_ : Fin n), A) :=
  Algebra.adjoin k (Set.range (toPiTensorProduct k A n))

/-- An alternative specified subalgebra of a finite pi tensor product of an algebra. -/
noncomputable def piTensorSubalgebraAlternate : Subalgebra k (⨂[k] (_ : Fin n), A) :=
  Algebra.adjoin k (Set.range (toPiTensorProductAlternate k A n))



set_option maxHeartbeats 3200000 in
private lemma tensor_diag_le_fullDiag [CharZero k] :
    piTensorSubalgebra k A n ≤ piTensorSubalgebraAlternate k A n := by
  apply Algebra.adjoin_le
  rintro _ ⟨b, rfl⟩

  by_cases hn : n = 0
  · subst hn; simp only [toPiTensorProduct, Finset.univ_eq_empty, Finset.sum_empty]
    exact Subalgebra.zero_mem _
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn

    set mm := (tprod k : MultilinearMap k (fun _ : Fin n => A) (⨂[k] (_ : Fin n), A))
      with hmm

    set a : Fin (n + 1) → ⨂[k] (_ : Fin n), A :=
      fun m => ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
        (fun S => S.card = m.val),
        mm (S.piecewise (fun _ => (1 : A)) (fun _ => b))

    have h_eval : ∀ j : Fin (n + 1),
        ∑ m : Fin (n + 1), ((j : ℕ) : k) ^ (m : ℕ) • a m =
          mm (fun _ => ((j : ℕ) : k) • (1 : A) + b) := by
      intro j
      simp only [a]
      rw [← sum_regroup_by_card]
      symm
      have key : (fun (_ : Fin n) => ((j : ℕ) : k) • (1 : A) + b) =
          (fun _ => ((j : ℕ) : k) • (1 : A)) + (fun _ => b) := by
        ext; simp [Pi.add_apply]
      rw [key, mm.map_add_univ]
      apply Finset.sum_congr rfl; intro S _
      set base := S.piecewise (fun _ : Fin n => (1 : A)) (fun _ => b)
      have h2 := mm.map_piecewise_smul (fun _ => ((j : ℕ) : k)) base S
      simp only [Finset.prod_const] at h2
      rw [← h2]
      congr 1; funext i
      simp only [Finset.piecewise, base]
      split_ifs with h <;> simp

    have h_mem : ∀ j : Fin (n + 1),
        ∑ m : Fin (n + 1), ((j : ℕ) : k) ^ (m : ℕ) • a m ∈
          (piTensorSubalgebraAlternate k A n).toSubmodule := by
      intro j; rw [h_eval]
      exact Algebra.subset_adjoin ⟨((j : ℕ) : k) • (1 : A) + b, rfl⟩

    have h_all := polynomial_coeffs_in_submodule k
      (piTensorSubalgebraAlternate k A n).toSubmodule n a h_mem

    have h_target := h_all ⟨n - 1, by omega⟩
    simp only [a] at h_target
    rw [sum_card_pred_eq_sum_erase n hn'] at h_target

    rw [show (∑ i : Fin n, mm ((Finset.univ.erase i).piecewise
        (fun _ => (1 : A)) (fun _ => b))) =
        ∑ i : Fin n, singleAlgHom (R := k) (A := fun _ : Fin n => A) i b from by
      apply Finset.sum_congr rfl; intro i _
      rw [piecewise_erase_eq, singleAlgHom_apply]
      congr 1; funext j
      simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]] at h_target
    exact h_target





set_option maxHeartbeats 800000 in
private lemma tensor_fullDiag_le_diag [CharZero k] :
    piTensorSubalgebraAlternate k A n ≤ piTensorSubalgebra k A n := by
  apply Algebra.adjoin_le
  rintro _ ⟨f, rfl⟩


  set B : Fin n → ⨂[k] (_ : Fin n), A :=
    fun i => singleAlgHom (R := k) (A := fun _ : Fin n => A) i f with hB

  have hcomm : ∀ i j, Commute (B i) (B j) := by
    intro i j
    simp only [B, singleAlgHom_apply]
    apply Commute.tprod
    change (MonoidHom.mulSingle (fun _ : Fin n => A) i f) *
        (MonoidHom.mulSingle (fun _ : Fin n => A) j f) =
      (MonoidHom.mulSingle (fun _ : Fin n => A) j f) *
        (MonoidHom.mulSingle (fun _ : Fin n => A) i f)
    funext x
    simp only [Pi.mul_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
    by_cases hi : x = i <;> by_cases hj : x = j <;> simp_all

  have hpow : ∀ i m, B i ^ m =
      singleAlgHom (R := k) (A := fun _ : Fin n => A) i (f ^ m) := by
    intro i m; simp only [B, ← map_pow]

  have hpsum : ∀ m, 0 < m → ∑ i, B i ^ m ∈ (piTensorSubalgebra k A n : Set _) := by
    intro m _; simp_rw [hpow]
    exact Algebra.subset_adjoin ⟨f ^ m, rfl⟩

  set e : ℕ → ⨂[k] (_ : Fin n), A := fun m =>
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      S.noncommProd B (fun i _ j _ _ => hcomm i j)

  suffices heq : e n = toPiTensorProductAlternate k A n f by
    change toPiTensorProductAlternate k A n f ∈ _
    rw [← heq]
    suffices ∀ m, e m ∈ piTensorSubalgebra k A n from this n
    intro m
    induction m using Nat.strongRecOn with | ind m ih => ?_
    by_cases hm : m = 0
    · subst hm; simp [e, Finset.powersetCard_zero]
    · have hm' : 0 < m := Nat.pos_of_ne_zero hm
      have hcast : (m : k) ≠ 0 := Nat.cast_ne_zero.mpr hm

      have newton : (m : k) • e m =
          (-1 : k) ^ (m + 1) • ∑ j ∈ Finset.range m,
            ((-1 : k) ^ j) • (e j * ∑ i : Fin n, B i ^ (m - j)) := by
        set Asub := Algebra.adjoin k (Set.range B)
        have hBA : ∀ i, B i ∈ Asub := fun i => Algebra.subset_adjoin ⟨i, rfl⟩
        have hcommA : ∀ (x y : Asub), x * y = y * x := by
          intro x y; apply Subtype.ext; change x.val * y.val = y.val * x.val
          exact Algebra.adjoin_induction₂
            (fun _ _ ⟨i, hi⟩ ⟨j, hj⟩ => hi ▸ hj ▸ hcomm i j)
            (fun r₁ r₂ => by rw [← map_mul, mul_comm, map_mul])
            (fun r _ _ => Algebra.commutes r _)
            (fun r _ _ => (Algebra.commutes r _).symm)
            (fun _ _ _ _ _ _ h₁ h₂ => by rw [add_mul, mul_add, h₁, h₂])
            (fun _ _ _ _ _ _ h₁ h₂ => by rw [mul_add, add_mul, h₁, h₂])
            (fun _ _ _ _ _ _ h₁ h₂ => by rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc])
            (fun _ _ _ _ _ _ h₁ h₂ => by rw [← mul_assoc, h₁, mul_assoc, h₂, ← mul_assoc])
            x.property y.property
        letI : CommRing Asub := { show Ring Asub from inferInstance with mul_comm := hcommA }
        set B' : Fin n → Asub := fun i => ⟨B i, hBA i⟩
        set ψ : MvPolynomial (Fin n) k →ₐ[k] Asub := MvPolynomial.aeval B' with hψ_def
        have prod_val : ∀ S : Finset (Fin n),
            (∏ i ∈ S, B' i : Asub).val =
              S.noncommProd B (fun i _ j _ _ => hcomm i j) := by
          intro S
          induction S using Finset.cons_induction_on with
          | empty => simp [Finset.noncommProd_empty]
          | cons a s ha ih =>
            rw [Finset.prod_cons, Finset.noncommProd_cons]
            change (B' a * ∏ i ∈ s, B' i).val = B a * s.noncommProd B _
            simp only [Subalgebra.coe_mul]; rw [ih]
        have esymm_val : ∀ j,
            (ψ (MvPolynomial.esymm (Fin n) k j) : ⨂[k] (_ : Fin n), A) = e j := by
          intro j
          simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X, hψ_def, e]
          rw [AddSubmonoidClass.coe_finsetSum]
          exact Finset.sum_congr rfl (fun T _ => prod_val T)
        have psum_val : ∀ d,
            (ψ (MvPolynomial.psum (Fin n) k d) : ⨂[k] (_ : Fin n), A) =
              ∑ i : Fin n, B i ^ d := by
          intro d
          simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, hψ_def]
          simp only [AddSubmonoidClass.coe_finsetSum, SubmonoidClass.coe_pow, B']
        set Φ : MvPolynomial (Fin n) k →ₐ[k] ⨂[k] (_ : Fin n), A := Asub.val.comp ψ
        have Φ_esymm : ∀ j, Φ (MvPolynomial.esymm (Fin n) k j) = e j := esymm_val
        have Φ_psum : ∀ d, Φ (MvPolynomial.psum (Fin n) k d) = ∑ i : Fin n, B i ^ d :=
          psum_val
        have h := congr_arg Φ (MvPolynomial.mul_esymm_eq_sum (Fin n) k m)
        simp only [map_mul, map_pow, map_neg, map_one, map_sum,
          Φ_esymm, Φ_psum] at h
        rw [map_natCast Φ m] at h
        rw [show (Finset.HasAntidiagonal.antidiagonal m).filter (fun x => x.1 < m) =
            (Finset.range m).map ⟨fun j => (j, m - j), fun a b h => by
              simp [Prod.ext_iff] at h; exact h.1⟩ from by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
            Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
          constructor
          · rintro ⟨hab, ha⟩
            exact ⟨a, ha, by ext <;> omega⟩
          · rintro ⟨j, hj, hpair⟩
            rcases Prod.ext_iff.mp hpair with ⟨rfl, hb⟩
            exact ⟨by omega, by omega⟩,
          Finset.sum_map] at h
        simp only [Function.Embedding.coeFn_mk] at h
        rw [Nat.cast_smul_eq_nsmul k m (e m), nsmul_eq_mul, h]
        have neg_pow_smul : ∀ (p : ℕ) (x : ⨂[k] (_ : Fin n), A),
            (-1 : ⨂[k] (_ : Fin n), A) ^ p * x = (-1 : k) ^ p • x := by
          intro p x
          have : (-1 : ⨂[k] (_ : Fin n), A) = algebraMap k _ (-1 : k) := by
            simp [map_neg, map_one]
          rw [this, ← map_pow, Algebra.smul_def]
        rw [neg_pow_smul]; congr 1
        apply Finset.sum_congr rfl; intro j _
        rw [mul_assoc, neg_pow_smul]
      rw [show e m = (m : k)⁻¹ • ((m : k) • e m) from (inv_smul_smul₀ hcast _).symm,
        newton]
      apply Subalgebra.smul_mem
      apply Subalgebra.smul_mem
      apply Subalgebra.sum_mem
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      apply Subalgebra.smul_mem
      apply Subalgebra.mul_mem
      · exact ih j hjm
      · exact hpsum (m - j) (Nat.sub_pos_of_lt hjm)

  simp only [e]
  have hcard : (Finset.univ : Finset (Fin n)).card = n :=
    Finset.card_univ.trans (Fintype.card_fin n)
  have huniv : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    rwa [hcard] at this
  rw [huniv, Finset.sum_singleton]


  set piF : Fin n → (Fin n → A) := fun i j => if j = i then f else 1 with hpiF_def
  have hpiFcomm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ∀ j ∈ (Finset.univ : Finset (Fin n)), i ≠ j →
      Commute (piF i) (piF j) := by
    intro i _ j _ _
    ext x; simp only [Pi.mul_apply, piF]
    by_cases hi : x = i <;> by_cases hj : x = j <;> simp_all

  have piF_prod : Finset.univ.noncommProd piF hpiFcomm = fun _ => f := by
    funext j
    change (Pi.evalMonoidHom (fun _ : Fin n => A) j)
      (Finset.univ.noncommProd piF hpiFcomm) = f
    rw [Finset.map_noncommProd _ _ _ (Pi.evalMonoidHom (fun _ : Fin n => A) j)]
    change Finset.univ.noncommProd (fun i => piF i j) _ = f
    simp only [piF]
    conv_lhs => rw [← Finset.mul_noncommProd_erase _ (Finset.mem_univ j)]
    simp only [ite_true]
    suffices h : (Finset.univ.erase j).noncommProd
        (fun i => if j = i then f else (1 : A)) _ = 1 by rw [h, mul_one]
    rw [Finset.noncommProd_eq_pow_card _ _ _ (1 : A)
      (fun i hi => by simp only [Ne.symm (Finset.mem_erase.mp hi).1, ite_false]), one_pow]

  have key := Finset.map_noncommProd Finset.univ piF hpiFcomm (tprodMonoidHom k)
  rw [piF_prod] at key

  have hBeq : ∀ i ∈ (Finset.univ : Finset (Fin n)), B i = tprodMonoidHom k (piF i) := by
    intro i _
    simp only [B, singleAlgHom_apply, tprodMonoidHom_apply, piF]
    congr 1; funext j
    simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
  rw [Finset.noncommProd_congr rfl hBeq, ← key]
  rfl

open _root_.PiTensorProduct in
/-- The two displayed subalgebras of a pi tensor product agree in characteristic zero. -/
@[source_ref "Chapter5/Lemma5.18.3" (role := primary)]
theorem piTensorSubalgebra_eq_alternate [CharZero k] :
    piTensorSubalgebra k A n = piTensorSubalgebraAlternate k A n :=
  le_antisymm (tensor_diag_le_fullDiag k A n) (tensor_fullDiag_le_diag k A n)

end GeneralAlgebra

end RepresentationTheory.PiTensorProduct.Constructions
