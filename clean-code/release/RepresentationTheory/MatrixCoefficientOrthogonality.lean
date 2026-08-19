/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

open FDRep CategoryTheory Representation

universe u

section SchurAverage

variable {k G : Type u} [Field k] [Group G] [Fintype G]
  [Invertible (Fintype.card G : k)]

/-- An auxiliary endomorphism of the space of linear maps between the underlying spaces of two finite-dimensional representations. -/
@[source_ref "Chapter4/Proposition4.7.1" (role := supporting)]
noncomputable def _root_.RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap (V W : FDRep k G) (f : (↑W : Type u) →ₗ[k] ↑V) :
    (↑W : Type u) →ₗ[k] ↑V :=
  ⅟(Fintype.card G : k) • ∑ g : G, (V.ρ g).comp (f.comp (W.ρ g⁻¹))

/-- The auxiliary linear-map construction equals the representation-theoretic averaging map on the corresponding linear-hom representation. -/
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_eq_averageMap (V W : FDRep k G) (f : (↑W : Type u) →ₗ[k] ↑V) :
    RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V W f = Representation.averageMap (Representation.linHom W.ρ V.ρ) f := by
  simp only [RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap, Representation.averageMap, GroupAlgebra.average,
    map_smul, map_sum]
  congr 1; ext g : 1
  simp [Representation.linHom_apply]

/-- The result of the auxiliary linear-map construction belongs to the invariant subspace of the corresponding linear-hom representation. -/
@[source_ref "Chapter4/Proposition4.7.1" (role := supporting)]
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_mem_invariants (V W : FDRep k G)
    (f : (↑W : Type u) →ₗ[k] ↑V) :
    RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V W f ∈ (Representation.linHom W.ρ V.ρ).invariants := by
  rw [RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_eq_averageMap]
  exact Representation.averageMap_invariant _ _

/-- The auxiliary linear-map construction sends every map between two nonisomorphic simple representations to zero. -/
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_eq_zero_of_not_iso [IsAlgClosed k]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    (f : (↑W : Type u) →ₗ[k] ↑V) :
    RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V W f = 0 := by
  have hmem := RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_mem_invariants V W f
  have hbot : (Representation.linHom W.ρ V.ρ).invariants = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    rw [LinearEquiv.finrank_eq
      (Representation.linHom.invariantsEquivFDRepHom W V)]
    exact CategoryTheory.finrank_hom_simple_simple_eq_zero_of_not_iso k
      fun i => hVW.false i.symm
  rw [hbot] at hmem
  exact hmem

private theorem sum_eq_averagedLinHom_entry
    (V W : FDRep k G)
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k ↑V) (bW : Module.Basis (Fin nW) k ↑W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q =
    (bV.repr (RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V W ((bW.coord p).smulRight (bV j)) (bW q))) i := by
  set f : (↑W : Type u) →ₗ[k] (↑V : Type u) := (bW.coord p).smulRight (bV j)
  simp_rw [LinearMap.toMatrix_apply]
  have step : ∀ g : G,
      (bV.repr (V.ρ g (bV j))) i * (bW.repr (W.ρ g⁻¹ (bW q))) p =
      (bV.repr ((V.ρ g).comp (f.comp (W.ρ g⁻¹)) (bW q))) i := by
    intro g
    simp [f, LinearMap.smulRight_apply, Module.Basis.coord_apply,
      LinearMap.comp_apply, map_smul, mul_comm]
  simp_rw [step]
  symm
  simp only [RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, map_smul, map_sum, Finsupp.smul_apply,
    Finsupp.finsetSum_apply]

end SchurAverage

/-- For nonisomorphic simple representations, the normalized sum of a matrix coefficient of one representation times an inverse-argument matrix coefficient of the other is zero. -/
@[source_ref "Chapter4/Introduction_4.7" (role := supporting),
  source_ref "Chapter4/Proposition4.7.1" (role := primary)]
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.orthogonalitySum_eq_zero_of_not_iso
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V W : FDRep k G) [Simple V] [Simple W]
    (hVW : IsEmpty (V ≅ W))
    {nV nW : ℕ}
    (bV : Module.Basis (Fin nV) k V) (bW : Module.Basis (Fin nW) k W)
    (i j : Fin nV) (p q : Fin nW) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix bV bV (V.ρ g)) i j *
      (LinearMap.toMatrix bW bW (W.ρ g⁻¹)) p q = 0 := by
  rw [sum_eq_averagedLinHom_entry V W bV bW i j p q]
  rw [RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_eq_zero_of_not_iso V W hVW]
  simp

/-- For a simple representation, the normalized sum of two matrix coefficients at inverse arguments is the inverse dimension when the indicated indices match, and zero otherwise. -/
@[source_ref "Chapter4/Introduction_4.7" (role := supporting),
  source_ref "Chapter4/Proposition4.7.1" (role := primary)]
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.orthogonalitySum_eq_ite
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) [Simple V]
    [Invertible (Module.finrank k (↑V : Type u) : k)]
    {n : ℕ}
    (b : Module.Basis (Fin n) k V)
    (i j p q : Fin n) :
    ⅟(Fintype.card G : k) • ∑ g : G,
      (LinearMap.toMatrix b b (V.ρ g)) i j *
      (LinearMap.toMatrix b b (V.ρ g⁻¹)) p q =
    if i = q ∧ j = p then (⅟(Module.finrank k (↑V : Type u) : k) : k) else 0 := by
  set f : (↑V : Type u) →ₗ[k] (↑V : Type u) := (b.coord p).smulRight (b j)

  rw [sum_eq_averagedLinHom_entry V V b b i j p q]

  have hmem := RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap_mem_invariants V V f
  have h1dim : Module.finrank k (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one k V

  have hid_mem : LinearMap.id ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl

  have hdim_ne : (Module.finrank k (↑V : Type u) : k) ≠ 0 :=
    isUnit_of_invertible _ |>.ne_zero
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro h
    have : (Module.finrank k (↑V : Type u) : k) = 0 := by
      rw [← LinearMap.trace_id (R := k) (M := (↑V : Type u)), h, map_zero]
    exact hdim_ne this

  obtain ⟨c, hc⟩ := ((finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim)
    ⟨RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V V f, hmem⟩

  have hT_eq : RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V V f = c • LinearMap.id := by
    have := congr_arg Subtype.val hc
    simpa using this.symm

  have htrace_T : LinearMap.trace k ↑V (RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap V V f) =
      LinearMap.trace k ↑V f := by
    simp only [RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryLinearMap, map_smul, map_sum]
    have trace_conj : ∀ g : G,
        LinearMap.trace k ↑V ((V.ρ g).comp (f.comp (V.ρ g⁻¹))) =
        LinearMap.trace k ↑V f := by
      intro g
      have : (V.ρ g).comp (f.comp (V.ρ g⁻¹)) = V.ρ g * f * V.ρ g⁻¹ := rfl
      rw [this, LinearMap.trace_mul_cycle]
      rw [show V.ρ g⁻¹ * V.ρ g * f = f from by
        rw [← map_mul, inv_mul_cancel, map_one, one_mul]]
    simp_rw [trace_conj, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, smul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

  have htrace_f : LinearMap.trace k ↑V f = if j = p then 1 else 0 := by
    simp only [f, LinearMap.trace_smulRight, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply]

  have hc_val : c = if j = p then ⅟(Module.finrank k (↑V : Type u) : k) else 0 := by
    have htr : (Module.finrank k (↑V : Type u) : k) * c =
        if j = p then 1 else 0 := by
      have : LinearMap.trace k ↑V (c • LinearMap.id) =
          if j = p then 1 else 0 := by
        rw [← hT_eq, htrace_T, htrace_f]
      rw [map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm] at this
      exact this
    split_ifs with hjp
    · rw [if_pos hjp] at htr
      rw [eq_comm]
      exact invOf_eq_right_inv htr
    · rw [if_neg hjp] at htr
      exact (mul_eq_zero.mp htr).resolve_left hdim_ne

  rw [hT_eq]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, hc_val]
  split_ifs <;> simp_all

namespace RepresentationTheory.MatrixCoefficientOrthogonality

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]

section Pairing

variable [Invertible (Fintype.card G : k)]

/-- An auxiliary scalar-valued pairing on two functions from a finite group to a field when the group cardinality is invertible. -/
noncomputable def auxiliaryPairing (f h : G → k) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, f g * h g⁻¹

omit [IsAlgClosed k] in

/-- The auxiliary pairing on functions from a finite group is symmetric. -/
theorem auxiliaryPairing_comm (f h : G → k) : auxiliaryPairing f h = auxiliaryPairing h f := by
  unfold auxiliaryPairing
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp [mul_comm]

/-- The linear functional obtained by fixing the second argument of the auxiliary pairing on group-valued functions. -/
noncomputable def auxiliaryPairingLinearMap (h : G → k) : (G → k) →ₗ[k] k where
  toFun f := auxiliaryPairing f h
  map_add' f₁ f₂ := by
    simp only [auxiliaryPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, smul_add]
  map_smul' c f := by
    simp only [auxiliaryPairing, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      ← Finset.mul_sum]
    ring

omit [IsAlgClosed k] in
/-- Applying the auxiliary pairing linear map to a function agrees with the auxiliary pairing of the two functions. -/
@[simp]
theorem auxiliaryPairingLinearMap_apply (f h : G → k) : auxiliaryPairingLinearMap h f = auxiliaryPairing f h := rfl

end Pairing

variable {n : ℕ} {d : Fin n → ℕ}

/-- An auxiliary index type determined by a finite family of natural numbers. -/
abbrev AuxiliaryIndex (n : ℕ) (d : Fin n → ℕ) : Type := Σ i : Fin n, Fin (d i) × Fin (d i)

/-- An auxiliary family of field-valued functions on a group, indexed by the associated auxiliary type. -/
noncomputable def auxiliaryFunction (V : Fin n → FDRep k G) (b : ∀ i, Module.Basis (Fin (d i)) k (V i))
    (e : AuxiliaryIndex n d) : G → k :=
  fun g => LinearMap.toMatrix (b e.1) (b e.1) ((V e.1).ρ g) e.2.1 e.2.2

variable {V : Fin n → FDRep k G} {b : ∀ i, Module.Basis (Fin (d i)) k (V i)}

omit [IsAlgClosed k] [Fintype G] in

/-- The dimension of each representation space equals the cardinality of the finite type indexing a chosen basis. -/
theorem finrank_eq_dimension (b : ∀ i, Module.Basis (Fin (d i)) k (V i)) (i : Fin n) :
    Module.finrank k (V i) = d i := by
  rw [Module.finrank_eq_card_basis (b i), Fintype.card_fin]

section Orthogonality

variable [Invertible (Fintype.card G : k)]

/-- The auxiliary pairing of auxiliary functions associated to distinct members of a pairwise nonisomorphic family of simple representations is zero. -/
theorem auxiliaryPairing_auxiliaryFunction_eq_zero_of_ne (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    {i i' : Fin n} (hii : i ≠ i') (p' q' : Fin (d i')) (p q : Fin (d i)) :
    auxiliaryPairing (auxiliaryFunction V b ⟨i', p', q'⟩) (auxiliaryFunction V b ⟨i, q, p⟩) = 0 := by
  haveI := hV i; haveI := hV i'
  have hVW : IsEmpty ((V i') ≅ (V i)) :=
    not_nonempty_iff.mp fun h => hii (hinj i i' ⟨h.some.symm⟩)
  exact orthogonalitySum_eq_zero_of_not_iso (V i') (V i) hVW (b i') (b i) p' q' q p

/-- Within one simple representation, the auxiliary pairing of two auxiliary functions is the inverse dimension when their displayed index pairs match, and zero otherwise. -/
theorem auxiliaryPairing_auxiliaryFunction_eq_ite (hV : ∀ i, Simple (V i)) {i : Fin n} (hd : ((d i : k)) ≠ 0)
    (p' q' p q : Fin (d i)) :
    auxiliaryPairing (auxiliaryFunction V b ⟨i, p', q'⟩) (auxiliaryFunction V b ⟨i, q, p⟩) =
      if p' = p ∧ q' = q then ((d i : k))⁻¹ else 0 := by
  haveI := hV i
  have hfr : ((Module.finrank k (V i) : k)) = (d i : k) := by rw [finrank_eq_dimension b i]
  haveI : Invertible ((Module.finrank k (V i) : k)) :=
    invertibleOfNonzero (by rw [hfr]; exact hd)
  have hinv : (⅟(Module.finrank k (V i) : k) : k) = ((d i : k))⁻¹ :=
    invOf_eq_right_inv (by rw [hfr]; exact mul_inv_cancel₀ hd)
  have hunfold : auxiliaryPairing (auxiliaryFunction V b ⟨i, p', q'⟩) (auxiliaryFunction V b ⟨i, q, p⟩) =
      ⅟(Fintype.card G : k) • ∑ g : G,
        (LinearMap.toMatrix (b i) (b i) ((V i).ρ g)) p' q' *
        (LinearMap.toMatrix (b i) (b i) ((V i).ρ g⁻¹)) q p := rfl
  rw [hunfold, orthogonalitySum_eq_ite (V i) (b i) p' q' q p, hinv]

end Orthogonality

section Basis

variable [Invertible (Fintype.card G : k)]

/-- The auxiliary function family associated to pairwise nonisomorphic simple representations is linearly independent when the specified dimensions are nonzero. -/
theorem linearIndependent_auxiliaryFunction (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    LinearIndependent k (auxiliaryFunction V b) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i₀, p₀, q₀⟩

  have h0 := congrArg (auxiliaryPairingLinearMap (k := k) (auxiliaryFunction V b ⟨i₀, q₀, p₀⟩)) hc
  rw [map_sum, map_zero] at h0
  simp only [map_smul, smul_eq_mul, auxiliaryPairingLinearMap_apply] at h0

  rw [← Finset.univ_sigma_univ, Finset.sum_sigma] at h0

  rw [Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ i₀) h)] at h0
  ·
    rw [← Finset.univ_product_univ, Finset.sum_product] at h0
    rw [Finset.sum_eq_single p₀ (fun p _ hp => ?_) (fun h => absurd (Finset.mem_univ p₀) h)] at h0
    · rw [Finset.sum_eq_single q₀ (fun q _ hq => ?_) (fun h => absurd (Finset.mem_univ q₀) h)] at h0
      · rw [auxiliaryPairing_auxiliaryFunction_eq_ite hV (hd i₀) p₀ q₀ p₀ q₀, if_pos ⟨rfl, rfl⟩] at h0
        exact (mul_eq_zero.mp h0).resolve_right (inv_ne_zero (hd i₀))
      · rw [auxiliaryPairing_auxiliaryFunction_eq_ite hV (hd i₀) p₀ q p₀ q₀, if_neg (by simp [hq]), mul_zero]
    · refine Finset.sum_eq_zero fun q _ => ?_
      rw [auxiliaryPairing_auxiliaryFunction_eq_ite hV (hd i₀) p q p₀ q₀, if_neg (by simp [hp]), mul_zero]
  · refine Finset.sum_eq_zero fun pq _ => ?_
    obtain ⟨p, q⟩ := pq
    rw [auxiliaryPairing_auxiliaryFunction_eq_zero_of_ne hV hinj (Ne.symm hi) p q p₀ q₀, mul_zero]

/-- The cardinality of the auxiliary index type equals the dimension of the function space on the finite group. -/
theorem card_auxiliaryIndex_eq_finrank (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (b : ∀ i, Module.Basis (Fin (d i)) k (V i)) :
    Fintype.card (AuxiliaryIndex n d) = Module.finrank k (G → k) := by
  haveI : NeZero (Nat.card G : k) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact (isUnit_of_invertible _).ne_zero⟩
  rw [Module.finrank_fintype_fun_eq_card, ← RepresentationTheory.FDRep.GroupAlgebraDecomposition.sum_finrank_sq_eq_card_of_completeSimpleFamily V hV hinj hsurj]
  simp only [AuxiliaryIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_congr rfl fun i _ => by rw [finrank_eq_dimension b i, sq]

/-- A basis of the function space on a finite group indexed by the auxiliary index type, constructed from a complete pairwise nonisomorphic family of simple representations with chosen bases. -/
@[source_ref "Chapter4/Proposition4.7.1" (role := supporting)]
noncomputable def functionSpaceBasis (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    Module.Basis (AuxiliaryIndex n d) k (G → k) :=
  basisOfLinearIndependentOfCardEqFinrank' (auxiliaryFunction V b)
    (linearIndependent_auxiliaryFunction hV hinj hd) (card_auxiliaryIndex_eq_finrank hV hinj hsurj b)

/-- The function-space basis evaluated at an auxiliary index equals the corresponding auxiliary function. -/
@[simp]
theorem functionSpaceBasis_apply_eq_auxiliaryFunction (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    ⇑(functionSpaceBasis (b := b) hV hinj hsurj hd) = auxiliaryFunction V b :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

end Basis

end RepresentationTheory.MatrixCoefficientOrthogonality

/-- An additional auxiliary theorem involving the scalar-valued pairing on functions from a finite group. -/
@[source_ref "Chapter4/Proposition4.7.1" (role := supporting)]
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing_auxiliaryTheorem'
    {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [Invertible (Fintype.card G : k)]
    {n : ℕ} {d : Fin n → ℕ} (V : Fin n → FDRep k G)
    (b : ∀ i, Module.Basis (Fin (d i)) k (V i))
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (hsurj : ∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i))
    (hd : ∀ i, ((d i : k)) ≠ 0) :
    ∃ B : Module.Basis (Σ i : Fin n, Fin (d i) × Fin (d i)) k (G → k),
      (∀ (e : Σ i : Fin n, Fin (d i) × Fin (d i)) (g : G),
        B e g = LinearMap.toMatrix (b e.1) (b e.1) ((V e.1).ρ g) e.2.1 e.2.2) ∧
      (∀ (i i' : Fin n) (p' q' : Fin (d i')) (p q : Fin (d i)),
        RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing (B ⟨i', p', q'⟩) (B ⟨i, q, p⟩) =
          if h : i = i' then
            (if p' = h ▸ p ∧ q' = h ▸ q then ((d i' : k))⁻¹ else 0)
          else 0) := by
  classical
  refine ⟨RepresentationTheory.MatrixCoefficientOrthogonality.functionSpaceBasis (b := b) hV hinj hsurj hd, fun e g => ?_, ?_⟩
  · rw [RepresentationTheory.MatrixCoefficientOrthogonality.functionSpaceBasis_apply_eq_auxiliaryFunction]; rfl
  · intro i i' p' q' p q
    rw [RepresentationTheory.MatrixCoefficientOrthogonality.functionSpaceBasis_apply_eq_auxiliaryFunction]
    by_cases hii : i = i'
    · subst hii
      rw [dif_pos rfl, RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing_auxiliaryFunction_eq_ite hV (hd i) p' q' p q]
    · rw [dif_neg hii,
        RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing_auxiliaryFunction_eq_zero_of_ne hV hinj hii p' q' p q]

/-- An auxiliary theorem involving the scalar-valued pairing on functions from a finite group. -/
@[source_ref "Chapter4/Proposition4.7.1" (role := supporting)]
theorem _root_.RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing_auxiliaryTheorem
    (k G : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Fintype G] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G) (d : Fin n → ℕ)
      (b : ∀ i, Module.Basis (Fin (d i)) k (V i))
      (B : Module.Basis (Σ i : Fin n, Fin (d i) × Fin (d i)) k (G → k)),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) ∧
      (∀ (W : FDRep k G), Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      (∀ (e : Σ i : Fin n, Fin (d i) × Fin (d i)) (g : G),
        B e g = LinearMap.toMatrix (b e.1) (b e.1) ((V e.1).ρ g) e.2.1 e.2.2) ∧
      (∀ (i i' : Fin n) (p' q' : Fin (d i')) (p q : Fin (d i)),
        RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing (B ⟨i', p', q'⟩) (B ⟨i, q, p⟩) =
          if h : i = i' then
            (if p' = h ▸ p ∧ q' = h ▸ q then ((d i' : k))⁻¹ else 0)
          else 0) := by
  classical
  haveI : NeZero (Nat.card G : k) := ⟨by
    rw [Nat.card_eq_fintype_card]
    exact (Nat.cast_ne_zero (R := k)).mpr Fintype.card_ne_zero⟩

  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G := RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  let b : ∀ i, Module.Basis (Fin (D.dimension i)) k (D.representation i) := fun i =>
    Module.finBasisOfFinrankEq k _ (D.finrank_representation i)
  have hd : ∀ i, ((D.dimension i : k)) ≠ 0 := fun i =>
    (Nat.cast_ne_zero (R := k)).mpr (D.dimension_neZero i).ne
  obtain ⟨B, hB, horth⟩ :=
    RepresentationTheory.MatrixCoefficientOrthogonality.auxiliaryPairing_auxiliaryTheorem' D.representation b
      D.simple_representation D.representation_index_eq_of_iso D.exists_iso_representation_of_simple hd
  exact ⟨D.count, D.representation, D.dimension, b, B, D.simple_representation, D.representation_index_eq_of_iso,
    D.exists_iso_representation_of_simple, hB, horth⟩
