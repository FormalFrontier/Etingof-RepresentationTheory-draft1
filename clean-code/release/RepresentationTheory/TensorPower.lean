import Mathlib
import RepresentationTheory.Auxiliary.MutualCentralizers

set_option linter.style.cdot false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.flexible false

namespace RepresentationTheory.TensorPower

open scoped TensorProduct

universe u v

variable (k : Type u) [Field k]

/-- Shows that each vector in the family lies in the submodule when the displayed power-weighted sums lie there at pairwise distinct scalars. -/

theorem submodule_mem_of_polynomial_evaluations
    {M : Type*} [AddCommGroup M] [Module k M]
    (W : Submodule k M)
    {n : ℕ} (m : Fin (n + 1) → M)
    (c : Fin (n + 1) → k) (hc : Function.Injective c)
    (h : ∀ j : Fin (n + 1), ∑ i : Fin (n + 1), c j ^ (i : ℕ) • m i ∈ W) :
    ∀ i : Fin (n + 1), m i ∈ W := by
  classical
  set V : Matrix (Fin (n + 1)) (Fin (n + 1)) k := Matrix.vandermonde c with hV
  have hVdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_vandermonde_ne_zero_iff]; exact hc
  have key : ∀ j, ∑ i, V j i • m i ∈ W := by
    intro j
    have := h j
    simpa [V, hV, Matrix.vandermonde_apply] using this
  have h_adj : V.adjugate * V = V.det • (1 : Matrix _ _ k) := Matrix.adjugate_mul V
  intro i
  set v : Fin (n + 1) → M := fun j => ∑ i, V j i • m i
  have hsum : ∑ l, V.adjugate i l • v l = V.det • m i := by
    have step1 : ∀ l, V.adjugate i l • v l =
        ∑ i', (V.adjugate i l * V l i') • m i' := by
      intro l
      simp only [v, Finset.smul_sum, smul_smul]
    calc ∑ l, V.adjugate i l • v l
        = ∑ l, ∑ i', (V.adjugate i l * V l i') • m i' := by simp_rw [step1]
      _ = ∑ i', ∑ l, (V.adjugate i l * V l i') • m i' := Finset.sum_comm
      _ = ∑ i', (∑ l, V.adjugate i l * V l i') • m i' := by
          simp_rw [← Finset.sum_smul]
      _ = ∑ i', (V.adjugate * V) i i' • m i' := by
          simp_rw [Matrix.mul_apply]
      _ = ∑ i', (V.det • (1 : Matrix _ _ k)) i i' • m i' := by rw [h_adj]
      _ = ∑ i', (if i = i' then V.det else 0) • m i' := by
          apply Finset.sum_congr rfl
          intro i' _
          rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
            mul_one, mul_zero]
      _ = V.det • m i := by
          simp [ite_smul, zero_smul]
  have : V.det • m i ∈ W := by
    rw [← hsum]
    exact W.sum_smul_mem _ (fun l _ => key l)
  have := W.smul_mem (V.det)⁻¹ this
  rwa [smul_smul, inv_mul_cancel₀ hVdet, one_smul] at this

variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Defines an auxiliary endomorphism from a linear endomorphism and a finite set of indices. -/

noncomputable def auxiliaryEndomorphismOfFinset (n : ℕ) (f : Module.End k V)
    (s : Finset (Fin n)) : Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
  PiTensorProduct.map (R := k)
    (fun j : Fin n => if j ∈ s then f else (1 : Module.End k V))

/-- Identifies the auxiliary endomorphism at the universal finite set with the displayed tensor-product map. -/
@[simp]
theorem auxiliaryEndomorphismOfFinset_univ (n : ℕ) (f : Module.End k V) :
    auxiliaryEndomorphismOfFinset k n f Finset.univ =
      PiTensorProduct.map (R := k) (fun _ : Fin n => f) := by
  unfold auxiliaryEndomorphismOfFinset
  congr 1
  funext j
  simp

/-- Defines an auxiliary indexed family of endomorphisms from a linear endomorphism. -/

noncomputable def auxiliaryEndomorphismByIndex (n : ℕ) (f : Module.End k V) (i : ℕ) :
    Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
  ((-1 : k)) ^ i • ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard (n - i),
    auxiliaryEndomorphismOfFinset k n f s

/-- Identifies the zeroth auxiliary endomorphism with the displayed tensor-product map. -/

theorem auxiliaryEndomorphismByIndex_zero (n : ℕ) (f : Module.End k V) :
    auxiliaryEndomorphismByIndex k n f 0 =
      PiTensorProduct.map (R := k) (fun _ : Fin n => f) := by
  unfold auxiliaryEndomorphismByIndex
  simp only [pow_zero, one_smul, Nat.sub_zero]
  have h1 : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.mem_singleton, Finset.subset_univ,
      true_and]
    refine ⟨fun hcard => Finset.eq_univ_of_card s ?_, fun hs => hs ▸ ?_⟩
    · simpa [Fintype.card_fin] using hcard
    · simp [Fintype.card_fin]
  rw [h1, Finset.sum_singleton, auxiliaryEndomorphismOfFinset_univ]

private theorem map_piecewise_neg_smul_eq (n : ℕ) (f : Module.End k V) (c : k)
    (s : Finset (Fin n)) :
    PiTensorProduct.map (R := k)
      (s.piecewise (fun _ : Fin n => f)
        (fun _ : Fin n => (-c) • (1 : Module.End k V))) =
      (-c) ^ (n - s.card) • RepresentationTheory.TensorPower.auxiliaryEndomorphismOfFinset k n f s := by
  classical

  have hpw : s.piecewise (fun _ : Fin n => f)
      (fun _ : Fin n => (-c) • (1 : Module.End k V)) =
      fun j : Fin n =>
        (if j ∈ s then (1 : k) else (-c)) •
          (if j ∈ s then f else (1 : Module.End k V)) := by
    funext j
    by_cases hj : j ∈ s
    · simp [hj]
    · simp [hj]

  set ml := PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ : Fin n => V)
  have h_lhs : PiTensorProduct.map (R := k)
      (s.piecewise (fun _ : Fin n => f)
        (fun _ : Fin n => (-c) • (1 : Module.End k V))) =
      ml (s.piecewise (fun _ : Fin n => f)
        (fun _ : Fin n => (-c) • (1 : Module.End k V))) := rfl
  rw [h_lhs, hpw]
  rw [ml.map_smul_univ
    (c := fun j : Fin n => if j ∈ s then (1 : k) else (-c))
    (m := fun j : Fin n => if j ∈ s then f else (1 : Module.End k V))]

  have hprod : (∏ j : Fin n, (if j ∈ s then (1 : k) else (-c))) =
      (-c) ^ (n - s.card) := by
    rw [show (∏ j : Fin n, (if j ∈ s then (1 : k) else (-c))) =
        ∏ j ∈ Finset.univ, (if j ∈ s then (1 : k) else (-c)) from rfl]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1

    have hfilt : (Finset.univ.filter (fun j : Fin n => j ∉ s)) =
        (Finset.univ : Finset (Fin n)) \ s := by
      ext j; simp [Finset.mem_sdiff]
    rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [Fintype.card_fin]
  change (∏ j : Fin n, (if j ∈ s then (1 : k) else (-c))) •
      PiTensorProduct.map (R := k)
        (fun j : Fin n => if j ∈ s then f else (1 : Module.End k V)) =
      (-c) ^ (n - s.card) • RepresentationTheory.TensorPower.auxiliaryEndomorphismOfFinset k n f s
  rw [hprod]
  rfl

/-- Expresses the displayed tensor-product map as a finite sum involving the auxiliary indexed endomorphisms. -/

theorem piTensorProductMap_sub_smul_one_eq_auxiliary_sum (n : ℕ)
    (f : Module.End k V) (c : k) :
    PiTensorProduct.map (R := k) (fun _ : Fin n => f - c • (1 : Module.End k V)) =
      ∑ i ∈ Finset.range (n + 1), c ^ i • auxiliaryEndomorphismByIndex k n f i := by
  classical

  set ml := PiTensorProduct.mapMultilinear k (fun _ : Fin n => V) (fun _ : Fin n => V)
  have h_eq : (fun _ : Fin n => f - c • (1 : Module.End k V))
      = (fun _ : Fin n => f) + (fun _ : Fin n => (-c) • (1 : Module.End k V)) := by
    funext i; simp [neg_smul, sub_eq_add_neg]
  have lhs_eq :
      PiTensorProduct.map (R := k) (fun _ : Fin n => f - c • (1 : Module.End k V)) =
        ∑ s : Finset (Fin n),
          PiTensorProduct.map (R := k)
            (s.piecewise (fun _ : Fin n => f)
              (fun _ : Fin n => (-c) • (1 : Module.End k V))) := by
    change ml _ = _
    rw [h_eq]
    have : ml ((fun _ : Fin n => f) + (fun _ : Fin n => (-c) • (1 : Module.End k V))) =
        ∑ s : Finset (Fin n),
          ml (s.piecewise (fun _ : Fin n => f)
            (fun _ : Fin n => (-c) • (1 : Module.End k V))) :=
      ml.map_add_univ _ _

    convert this using 1
    rfl
  rw [lhs_eq]

  rw [Finset.sum_congr rfl (fun s _ => map_piecewise_neg_smul_eq k n f c s)]

  rw [show ((Finset.univ : Finset (Finset (Fin n))) : Finset _) =
      (Finset.range (n + 1)).biUnion
        (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) from by
    ext s
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, true_iff]
    refine ⟨s.card, ?_, Finset.subset_univ _, rfl⟩
    have h1 : s.card ≤ Fintype.card (Fin n) :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Fintype.card_fin] at h1
    omega]
  rw [Finset.sum_biUnion (by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro s ha hb
    rw [Finset.mem_powersetCard] at ha hb
    exact hab (ha.2.symm.trans hb.2))]

  refine Finset.sum_nbij' (fun j => n - j) (fun i => n - i) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    show n - (n - j) = j
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    show n - (n - i) = i
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj

    change ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (-c) ^ (n - s.card) • auxiliaryEndomorphismOfFinset k n f s =
      c ^ (n - j) • auxiliaryEndomorphismByIndex k n f (n - j)
    have hj' : n - (n - j) = j := by omega
    unfold auxiliaryEndomorphismByIndex
    rw [hj']

    rw [show ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (-c) ^ (n - s.card) • auxiliaryEndomorphismOfFinset k n f s =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (-c) ^ (n - j) • auxiliaryEndomorphismOfFinset k n f s from by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [Finset.mem_powersetCard] at hs
      rw [hs.2]]

    rw [← Finset.smul_sum]
    rw [show ((-c) ^ (n - j) : k) = c ^ (n - j) * (-1) ^ (n - j) from by
      rw [neg_pow]; ring]
    rw [mul_smul]

/-- Produces a set outside which subtracting a scalar multiple of the identity from an endomorphism is a unit. -/

theorem exists_set_outside_sub_scalar_isUnit [Module.Finite k V] (f : Module.End k V) :
    ∃ S : Finset k, ∀ c, c ∉ S → IsUnit (f - c • (1 : Module.End k V)) := by
  haveI : Module.Free k V := Module.Free.of_divisionRing k V
  classical

  refine ⟨f.charpoly.roots.toFinset, fun c hc => ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots f.charpoly_monic.ne_zero] at hc

  have h_aux : IsUnit (algebraMap k (Module.End k V) c - f) := by
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.eval_charpoly]
    rw [Polynomial.IsRoot.def] at hc
    exact Ne.isUnit hc
  have h_eq : f - c • (1 : Module.End k V) = -(algebraMap k (Module.End k V) c - f) := by
    rw [Algebra.algebraMap_eq_smul_one]
    abel
  rw [h_eq]
  exact h_aux.neg

/-- Places the tensor-product map of every endomorphism in the span of maps induced by units. -/

theorem piTensorProductMap_mem_span_of_unitMaps [Module.Finite k V] [Infinite k]
    (n : ℕ) (f : Module.End k V) :
    PiTensorProduct.map (R := k) (fun _ : Fin n => f) ∈
      Submodule.span k
        (Set.range fun (g : (Module.End k V)ˣ) =>
          PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) := by
  classical
  set W := Submodule.span k
        (Set.range fun (g : (Module.End k V)ˣ) =>
          PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) with hW

  obtain ⟨S, hS⟩ := exists_set_outside_sub_scalar_isUnit k f

  have hSc_infinite : (↑S : Set k)ᶜ.Infinite := S.finite_toSet.infinite_compl

  let e : ℕ ↪ ((↑S : Set k)ᶜ : Set k) := hSc_infinite.natEmbedding
  let c : Fin (n + 1) → k := fun j => ((e j.val) : k)
  have hc_inj : Function.Injective c := by
    intro j₁ j₂ hjj
    have h1 : e j₁.val = e j₂.val := Subtype.ext hjj
    have h2 : j₁.val = j₂.val := e.injective h1
    exact Fin.val_injective h2
  have hc_notin_S : ∀ j, c j ∉ S := fun j => by
    have h1 : (c j : k) ∈ ((↑S : Set k)ᶜ : Set k) := (e j.val).property
    rw [Set.mem_compl_iff, Finset.mem_coe] at h1
    exact h1

  have h_in_W : ∀ j : Fin (n + 1), PiTensorProduct.map (R := k)
      (fun _ : Fin n => f - c j • (1 : Module.End k V)) ∈ W := by
    intro j
    have h_unit : IsUnit (f - c j • (1 : Module.End k V)) := hS (c j) (hc_notin_S j)
    refine Submodule.subset_span ⟨h_unit.unit, ?_⟩
    rfl

  have h_in_W' : ∀ j : Fin (n + 1),
      ∑ i : Fin (n + 1), c j ^ (i : ℕ) • auxiliaryEndomorphismByIndex k n f i ∈ W := by
    intro j
    have h_eq := piTensorProductMap_sub_smul_one_eq_auxiliary_sum k n f (c j)
    rw [show (∑ i ∈ Finset.range (n + 1), c j ^ i • auxiliaryEndomorphismByIndex k n f i) =
        ∑ i : Fin (n + 1), c j ^ (i : ℕ) • auxiliaryEndomorphismByIndex k n f i from by
      rw [Finset.sum_range (fun i => c j ^ i • auxiliaryEndomorphismByIndex k n f i)]] at h_eq
    rw [← h_eq]
    exact h_in_W j
  have h_coeff_in_W : ∀ i : Fin (n + 1), auxiliaryEndomorphismByIndex k n f (i : ℕ) ∈ W := by
    apply submodule_mem_of_polynomial_evaluations k W _ c hc_inj
    exact h_in_W'

  have := h_coeff_in_W ⟨0, Nat.zero_lt_succ n⟩
  rw [show ((⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) : ℕ) = 0 from rfl,
    auxiliaryEndomorphismByIndex_zero] at this
  exact this

/-- Identifies the algebra generated by tensor-product maps with the displayed auxiliary algebra. -/

theorem adjoin_piTensorProductMaps_eq_auxiliary
    [Module.Finite k V] [Infinite k] (n : ℕ) :
    Algebra.adjoin k (Set.range fun (g : (Module.End k V)ˣ) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V))) =
    RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := by
  apply le_antisymm
  ·
    apply Algebra.adjoin_le
    rintro x ⟨g, rfl⟩
    exact Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩
  ·
    apply Algebra.adjoin_le
    rintro x ⟨f, rfl⟩

    have h_span := piTensorProductMap_mem_span_of_unitMaps k n f
    exact Algebra.span_le_adjoin k _ h_span

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Auxiliary result showing closure under the displayed subtype action from invariance under the given units. -/

theorem auxiliary_smul_mem_of_unit_invariant
    [Module.Finite k V] [Infinite k]
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    [Module (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) M]
    [IsScalarTower k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) M]
    (W : Submodule k M)
    (hW : ∀ (g : (Module.End k V)ˣ),
        ∀ x ∈ W, (⟨PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)),
            Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩⟩ :
              RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) • x ∈ W)
    (b : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) (x : M) (hx : x ∈ W) :
    b • x ∈ W := by
  classical

  obtain ⟨b_val, b_mem⟩ := b

  suffices h : ∀ y ∈ W, (⟨b_val, b_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) • y ∈ W by
    exact h x hx

  refine Algebra.adjoin_induction
    (s := Set.range fun (f : Module.End k V) =>
      PiTensorProduct.map (R := k) (fun _ : Fin n => f))
    (p := fun b_val' _ =>
      ∀ (h_mem : b_val' ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n),
      ∀ y ∈ W, (⟨b_val', h_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) • y ∈ W)
    ?_ ?_ ?_ ?_ b_mem b_mem
  ·
    rintro b_val' ⟨f, rfl⟩ h_mem y hy

    have h_span := piTensorProductMap_mem_span_of_unitMaps k n f

    refine Submodule.span_induction
      (M := Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))
      (R := k)
      (s := Set.range fun (g : (Module.End k V)ˣ) =>
        PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)))
      (p := fun b'' _ =>
        ∀ (h_b_mem : b'' ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n),
        (⟨b'', h_b_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) • y ∈ W)
      ?_ ?_ ?_ ?_ h_span h_mem
    · rintro b'' ⟨g, rfl⟩ h_b_mem
      have := hW g y hy
      convert this
    · intro h_zero_mem
      rw [show (⟨0, h_zero_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) = 0 from rfl, zero_smul]
      exact W.zero_mem
    · intro b₁ b₂ h₁_in h₂_in ih₁ ih₂ h_b_mem
      have h₁_mem : b₁ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := by
        rw [← adjoin_piTensorProductMaps_eq_auxiliary]
        exact Algebra.span_le_adjoin k _ h₁_in
      have h₂_mem : b₂ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := by
        rw [← adjoin_piTensorProductMaps_eq_auxiliary]
        exact Algebra.span_le_adjoin k _ h₂_in
      rw [show (⟨b₁ + b₂, h_b_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) =
          (⟨b₁, h₁_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) +
          (⟨b₂, h₂_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) from rfl, add_smul]
      exact W.add_mem (ih₁ h₁_mem) (ih₂ h₂_mem)
    · intro a b₁ h₁_in ih h_smul_mem
      have h₁_mem : b₁ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := by
        rw [← adjoin_piTensorProductMaps_eq_auxiliary]
        exact Algebra.span_le_adjoin k _ h₁_in
      rw [show (⟨a • b₁, h_smul_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) =
          a • (⟨b₁, h₁_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) from rfl, smul_assoc]
      exact W.smul_mem a (ih h₁_mem)
  ·
    intros r h_mem y hy
    rw [show (⟨algebraMap k _ r, h_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) =
        algebraMap k _ r from rfl,
      Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]
    exact W.smul_mem r hy
  ·
    rintro b₁ b₂ h₁_adj h₂_adj ih₁ ih₂ h_mem y hy
    have h₁_mem : b₁ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := h₁_adj
    have h₂_mem : b₂ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := h₂_adj
    rw [show (⟨b₁ + b₂, h_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) =
        (⟨b₁, h₁_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) +
        (⟨b₂, h₂_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) from rfl, add_smul]
    exact W.add_mem (ih₁ h₁_mem y hy) (ih₂ h₂_mem y hy)
  ·
    rintro b₁ b₂ h₁_adj h₂_adj ih₁ ih₂ h_mem y hy
    have h₁_mem : b₁ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := h₁_adj
    have h₂_mem : b₂ ∈ RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n := h₂_adj
    have hy₂ := ih₂ h₂_mem y hy
    have hy₁ := ih₁ h₁_mem _ hy₂
    rw [show (⟨b₁ * b₂, h_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) =
        (⟨b₁, h₁_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) *
        (⟨b₂, h₂_mem⟩ : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) from rfl, mul_smul]
    exact hy₁

/-- Provides a ring structure on the subtype defined by the displayed auxiliary set. -/
noncomputable local instance (priority := high) auxiliaryRingOfSubtype'
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (n : ℕ) :
    Ring (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) := (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n).toRing

/-- Provides a ring structure on the subtype defined by the displayed auxiliary set. -/
noncomputable local instance (priority := high) auxiliaryRingOfSubtype
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V] (n : ℕ) :
    Ring (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) := (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n).toRing

set_option synthInstance.maxHeartbeats 40000 in
/-- Auxiliary result showing that the displayed unit-invariant submodule is either bottom or top. -/

theorem eq_bot_or_eq_top_of_auxiliary_unit_invariant
    [Module.Finite k V] [Infinite k]
    {n : ℕ} {M : Type*} [AddCommGroup M] [Module k M]
    [Module (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) M]
    [IsScalarTower k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) M]
    [IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) M]
    (W : Submodule k M)
    (hW : ∀ (g : (Module.End k V)ˣ),
        ∀ x ∈ W, (⟨PiTensorProduct.map (R := k) (fun _ : Fin n => (g : Module.End k V)),
            Algebra.subset_adjoin ⟨(g : Module.End k V), rfl⟩⟩ :
              RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) • x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by

  let W' : Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) M :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun b x hx =>
        auxiliary_smul_mem_of_unit_invariant k W hW b x hx }

  rcases (IsSimpleOrder.eq_bot_or_eq_top W' : W' = ⊥ ∨ W' = ⊤) with h | h
  · left
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have : x ∈ W' := hx
      rw [h] at this
      exact this
    · simp at hx
      exact hx ▸ W.zero_mem
  · right
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    have : x ∈ W' := by rw [h]; trivial
    exact this

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary result deriving simplicity of the displayed representation module from agreement with the displayed tensor-product action. -/

theorem isSimpleModule_of_auxiliary_piTensorProduct_action
    {N n : ℕ}
    {M : Type*} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) M]
    [IsScalarTower k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) M]
    [IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) M]
    [IsAlgClosed k]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) M)
    (h_act : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M),
        ρ g x =
          (⟨PiTensorProduct.map (R := k)
              (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val),
            Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩⟩ :
              RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) • x) :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      ρ.asModule := by
  haveI : Module.Finite k (Fin N → k) := inferInstance
  haveI : Nontrivial M :=
    IsSimpleModule.nontrivial (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) M
  haveI : Nontrivial ρ.asModule := (show Nontrivial M from inferInstance)
  haveI : Nontrivial (Submodule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) ρ.asModule) :=
    (Submodule.nontrivial_iff
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))).mpr inferInstance
  rw [isSimpleModule_iff]

  refine ⟨fun W => ?_⟩

  set W_k : Submodule k M := W.restrictScalars k with hW_k_def

  have hW_k_closed : ∀ (f : (Module.End k (Fin N → k))ˣ),
      ∀ x ∈ W_k,
      (⟨PiTensorProduct.map (R := k)
          (fun _ : Fin n => (f : Module.End k (Fin N → k))),
        Algebra.subset_adjoin ⟨(f : Module.End k (Fin N → k)), rfl⟩⟩ :
          RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) • x ∈ W_k := by
    intro f x hx

    set g : Matrix.GeneralLinearGroup (Fin N) k :=
      (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := k)).symm f with hg_def
    have hg_eq : Matrix.mulVecLin (R := k) g.val =
        (f : Module.End k (Fin N → k)) := by
      have h := MulEquiv.apply_symm_apply
        (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := k)) f
      exact congrArg Units.val h

    have hfg : (fun _ : Fin n => (f : Module.End k (Fin N → k))) =
        (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val) :=
      funext fun _ => hg_eq.symm
    have h_subst : (⟨PiTensorProduct.map (R := k)
        (fun _ : Fin n => (f : Module.End k (Fin N → k))),
        Algebra.subset_adjoin ⟨(f : Module.End k (Fin N → k)), rfl⟩⟩ :
          RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k (Fin N → k) n) =
        ⟨PiTensorProduct.map (R := k)
            (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val),
          Algebra.subset_adjoin ⟨Matrix.mulVecLin g.val, rfl⟩⟩ :=
      Subtype.ext (congrArg (PiTensorProduct.map (R := k)) hfg)
    rw [h_subst, ← h_act g x]

    change ρ g x ∈ W_k
    have hxW : (show ρ.asModule from x) ∈ W := hx
    have h_single : (MonoidAlgebra.single g (1 : k) :
        MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)) •
        (show ρ.asModule from x) = ρ g x := by
      rw [Representation.single_smul, one_smul]
      rfl
    rw [hW_k_def, Submodule.restrictScalars_mem]
    exact h_single ▸ W.smul_mem _ hxW
  have h_W_k := eq_bot_or_eq_top_of_auxiliary_unit_invariant k W_k hW_k_closed
  rcases h_W_k with h | h
  · left
    rwa [hW_k_def, Submodule.restrictScalars_eq_bot_iff] at h
  · right
    rwa [hW_k_def, Submodule.restrictScalars_eq_top_iff] at h

set_option maxHeartbeats 12000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- Auxiliary existence statement for a linear equivalence from the displayed type to a direct sum of tensor products. -/

theorem exists_auxiliary_linearEquiv_directSum
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) (_hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n) (S i))
      (_ : ∀ i, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n) (S i))
      (_ : ∀ i j,
        Nonempty (S i ≃ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n] S j) → i = j)
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ)),
      Nonempty (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n ≃ₗ[k]
        DirectSum ι (fun i => S i ⊗[k] (L i : Type u))) := by
  set V : Type u := Fin N → k with hV
  haveI : Module.Finite k V := inferInstance
  haveI := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra_semisimple k V n
  haveI := RepresentationTheory.Auxiliary.MutualCentralizers.faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n

  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, homA_simp, e, _he⟩ :=
    RepresentationTheory.Auxiliary.MutualCentralizers.exists_auxiliarySpace_decomposition_evaluation k V n
  let coherentSAddCommGroup : ∀ i, AddCommGroup (S' i) := fun i =>
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (S' i).addCommMonoid }
  letI : ∀ i, AddCommGroup (S' i) := coherentSAddCommGroup

  let glHom : Matrix.GeneralLinearGroup (Fin N) k →*
      ↥(Subalgebra.centralizer k
        (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))) :=
    RepresentationTheory.Auxiliary.MutualCentralizers.generalLinearGroupHomToPermutationCentralizer k N n
  haveI hLi_fin : ∀ i, Module.Finite k
      ((↥(S' i) : Type u) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
    fun i => by
      letI : AddCommGroup (↥(S' i) : Type u) :=
        { Module.addCommMonoidToAddCommGroup k with
          toAddCommMonoid := (S' i).addCommMonoid }
      haveI : Module.Finite k (↥(S' i) : Type u) := hS'_fin i
      haveI : Module.Free k (↥(S' i) : Type u) :=
        Module.Free.of_divisionRing k (↥(S' i))
      haveI : Module.Finite k
          ((↥(S' i) : Type u) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        Module.Finite.linearMap k k (↥(S' i)) (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
      letI : AddCommGroup
          ((↥(S' i) : Type u) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        LinearMap.addCommGroup
      letI : AddCommGroup ((↥(S' i) : Type u) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        LinearMap.addCommGroup
      let f : ((↥(S' i) : Type u) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) →ₗ[k]
          ((↥(S' i) : Type u) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        LinearMap.restrictScalarsₗ k (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (↥(S' i))
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) k
      refine @FiniteDimensional.of_injective k _ inferInstance inferInstance inferInstance _
        inferInstance inferInstance f ?_ inferInstance
      intro x y h
      exact LinearMap.ext fun v ↦ LinearMap.congr_fun h v
  let ρ_i : ∀ i, Matrix.GeneralLinearGroup (Fin N) k →*
      Module.End k (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := fun i =>
    (RepresentationTheory.CentralizerDecomposition.centralizerActionMonoidHom k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n)
      (↥(S' i))).comp glHom
  let L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) := fun i =>
    FDRep.of (ρ_i i)

  have h_eq : Subalgebra.centralizer k
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))) =
      RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n :=
    ((RepresentationTheory.Auxiliary.MutualCentralizers.mutual_centralizer_algebras k V n).2).symm

  have hL_simple : ∀ i, IsSimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (L i).ρ) := by
    intro i

    letI hC_ring : Ring (↥(Subalgebra.centralizer k
        (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))) :=
      @Subalgebra.toRing k (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) inferInstance
        inferInstance inferInstance (Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))
    letI hC_mod :
        Module (↥(Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      RepresentationTheory.CentralizerDecomposition.centralizerModuleHom (A := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n)
        (V := (↥(S' i) : Type u))
    haveI hC_st :
        IsScalarTower k
          (↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := by
      refine ⟨fun a c f => ?_⟩
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)
    haveI hC_simp :
        IsSimpleModule
          (↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      homA_simp i

    let φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) ≃ₐ[k]
        ↥(Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))) :=
      Subalgebra.equivOfEq _ _ h_eq.symm

    letI hD_mod :
        Module (↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      Module.compHom (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
        (φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) →+*
          ↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
    haveI hD_st :
        IsScalarTower k (↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := by
      refine ⟨fun a d m => ?_⟩
      change φ (a • d) • m = a • φ d • m
      rw [map_smul]
      exact smul_assoc a (φ d) m
    haveI hφ_surj :
        RingHomSurjective
          (φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) →+*
            ↥(Subalgebra.centralizer k
              (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))) :=
      ⟨φ.surjective⟩
    haveI hD_simp :
        IsSimpleModule (↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := by
      let l : (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
          →ₛₗ[(φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) →+*
              ↥(Subalgebra.centralizer k
                (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))]
            (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hl : Function.Bijective l :=
        ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩
      exact (LinearMap.isSimpleModule_iff_of_bijective l hl).mpr hC_simp
    haveI : Module.Finite k
        (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      hLi_fin i
    refine @isSimpleModule_of_auxiliary_piTensorProduct_action k inferInstance N n
      (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) inferInstance
      inferInstance (hLi_fin i) hD_mod hD_st hD_simp inferInstance
      (L i).ρ ?_
    intro g x

    exact LinearMap.ext fun _ => rfl
  refine ⟨ι, hι, hι_dec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    hS'_simp, hS'_dist, hS'_fin,
    L, hL_simple, ⟨e⟩⟩

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 3200000 in
/-- Constructs a direct-sum tensor-product description whose component maps intertwine the indicated group actions. -/

theorem exists_tensorProduct_decomposition_with_action
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (N n : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Submodule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n)
        (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n))
      (_ : ∀ i, IsSimpleModule (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n) (S i))
      (_ : ∀ i j,
        Nonempty (↥(S i) ≃ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n] ↥(S j)) → i = j)
      (_ : ∀ i, Module.Finite k ↥(S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule
        (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
        (Representation.asModule (L i).ρ))
      (L_carrier : ∀ i, (L i : Type u) ≃ₗ[k]
        (↥(S i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k (Fin N → k) n]
          RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n)),
      ∃ (e : RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k (Fin N → k) n ≃ₗ[k]
          DirectSum ι (fun i => ↥(S i) ⊗[k] (L i : Type u))),
        (∀ (i : ι) (v : ↥(S i)) (l : (L i : Type u)),
          e.symm (DirectSum.of (fun i => ↥(S i) ⊗[k] (L i : Type u)) i
              (v ⊗ₜ[k] l)) = (L_carrier i l) v) ∧
        (∀ (i : ι) (g : Matrix.GeneralLinearGroup (Fin N) k)
            (l : (L i : Type u)) (v : ↥(S i)),
          (L_carrier i ((L i).ρ g l)) v =
            PiTensorProduct.map
              (fun _ : Fin n => Matrix.mulVecLin (R := k) g.val)
              ((L_carrier i l) v)) := by
  set V : Type u := Fin N → k with hV
  haveI : Module.Finite k V := inferInstance
  haveI := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra_semisimple k V n
  haveI := RepresentationTheory.Auxiliary.MutualCentralizers.faithfulSMul_permutationActionAlgebra_auxiliarySpace k V n

  obtain ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, homA_simp, e, he⟩ :=
    RepresentationTheory.Auxiliary.MutualCentralizers.exists_auxiliarySpace_decomposition_evaluation k V n
  let coherentSAddCommGroup : ∀ i, AddCommGroup (S' i) := fun i =>
    { Module.addCommMonoidToAddCommGroup k with
      toAddCommMonoid := (S' i).addCommMonoid }
  letI : ∀ i, AddCommGroup (S' i) := coherentSAddCommGroup
  let glHom : Matrix.GeneralLinearGroup (Fin N) k →*
      ↥(Subalgebra.centralizer k
        (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))) :=
    RepresentationTheory.Auxiliary.MutualCentralizers.generalLinearGroupHomToPermutationCentralizer k N n
  haveI hLi_fin : ∀ i, Module.Finite k
      ((↥(S' i) : Type u) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
    fun i => by
      letI : AddCommGroup (↥(S' i) : Type u) :=
        { Module.addCommMonoidToAddCommGroup k with
          toAddCommMonoid := (S' i).addCommMonoid }
      haveI : Module.Finite k (↥(S' i) : Type u) := hS'_fin i
      haveI : Module.Free k (↥(S' i) : Type u) :=
        Module.Free.of_divisionRing k (↥(S' i))
      haveI : Module.Finite k
          ((↥(S' i) : Type u) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        Module.Finite.linearMap k k (↥(S' i)) (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
      letI : AddCommGroup
          ((↥(S' i) : Type u) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        LinearMap.addCommGroup
      letI : AddCommGroup ((↥(S' i) : Type u) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        LinearMap.addCommGroup
      let f : ((↥(S' i) : Type u) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) →ₗ[k]
          ((↥(S' i) : Type u) →ₗ[k] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        LinearMap.restrictScalarsₗ k (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n) (↥(S' i))
          (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) k
      refine @FiniteDimensional.of_injective k _ inferInstance inferInstance inferInstance _
        inferInstance inferInstance f ?_ inferInstance
      intro x y h
      exact LinearMap.ext fun v ↦ LinearMap.congr_fun h v
  let ρ : ∀ i, Matrix.GeneralLinearGroup (Fin N) k →*
      Module.End k (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := fun i =>
    (RepresentationTheory.CentralizerDecomposition.centralizerActionMonoidHom k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n)
      (↥(S' i))).comp glHom
  let L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k) := fun i =>
    FDRep.of (ρ i)
  let L_carrier : ∀ i, (L i : Type u) ≃ₗ[k]
      (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
    fun i => LinearEquiv.refl k _

  have h_eq : Subalgebra.centralizer k
      (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))) =
      RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n :=
    ((RepresentationTheory.Auxiliary.MutualCentralizers.mutual_centralizer_algebras k V n).2).symm

  have hL_simple : ∀ i, IsSimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule (L i).ρ) := by
    intro i
    letI hC_ring : Ring (↥(Subalgebra.centralizer k
        (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))) :=
      @Subalgebra.toRing k (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)) inferInstance
        inferInstance inferInstance (Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))
    letI hC_mod :
        Module (↥(Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      RepresentationTheory.CentralizerDecomposition.centralizerModuleHom (A := RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n)
        (V := (↥(S' i) : Type u))
    haveI hC_st :
        IsScalarTower k
          (↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := by
      refine ⟨fun a c f => ?_⟩
      refine LinearMap.ext fun v => ?_
      change (a • c).val (f v) = a • c.val (f v)
      rw [SetLike.val_smul]
      exact LinearMap.smul_apply a c.val (f v)
    haveI hC_simp :
        IsSimpleModule
          (↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      homA_simp i
    let φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) ≃ₐ[k]
        ↥(Subalgebra.centralizer k
          (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))) :=
      Subalgebra.equivOfEq _ _ h_eq.symm
    letI hD_mod :
        Module (↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      Module.compHom (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
        (φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) →+*
          ↥(Subalgebra.centralizer k
            (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))
    haveI hD_st :
        IsScalarTower k (↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := by
      refine ⟨fun a d m => ?_⟩
      change φ (a • d) • m = a • φ d • m
      rw [map_smul]
      exact smul_assoc a (φ d) m
    haveI hφ_surj :
        RingHomSurjective
          (φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) →+*
            ↥(Subalgebra.centralizer k
              (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n))))) :=
      ⟨φ.surjective⟩
    haveI hD_simp :
        IsSimpleModule (↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n))
          (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) := by
      let l : (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)
          →ₛₗ[(φ : ↥(RepresentationTheory.Auxiliary.MutualCentralizers.auxiliaryEndomorphismAlgebra k V n) →+*
              ↥(Subalgebra.centralizer k
                (RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n : Set (Module.End k (RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n)))))]
            (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
        { toFun := id
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hl : Function.Bijective l :=
        ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩
      exact (LinearMap.isSimpleModule_iff_of_bijective l hl).mpr hC_simp
    haveI : Module.Finite k
        (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) :=
      hLi_fin i
    refine @isSimpleModule_of_auxiliary_piTensorProduct_action k inferInstance N n
      (↥(S' i) →ₗ[RepresentationTheory.Auxiliary.MutualCentralizers.permutationActionAlgebra k V n] RepresentationTheory.Auxiliary.MutualCentralizers.auxiliarySpace k V n) inferInstance
      inferInstance (hLi_fin i) hD_mod hD_st hD_simp inferInstance
      (L i).ρ ?_
    intro g x
    exact LinearMap.ext fun _ => rfl
  refine ⟨ι, hι, hι_dec, S', hS'_simp, hS'_dist, hS'_fin, L, hL_simple,
    L_carrier, e, he, ?_⟩
  intro i g l v
  rfl

end RepresentationTheory.TensorPower
