import Mathlib
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.SymmetricGroup.PartitionDominance
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Group.SimpleRepresentations
import RepresentationTheory.Alignment.Attribute
namespace RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
noncomputable section
open scoped Classical
open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.SymmetricGroup.PartitionDominance
open RepresentationTheory.FDRep.GroupAlgebraDecomposition
open RepresentationTheory.Group.SimpleRepresentations
private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A' (n : ℕ) := MonoidAlgebra ℂ (G' n)
/-- The function coercion from a monoid algebra to functions `G → R`. -/
local instance MonoidAlgebra.coeFun {R G : Type*} [Semiring R] :
    CoeFun (MonoidAlgebra R G) (fun _ => G → R) :=
  ⟨fun a => a.coeff⟩
private lemma young_symmetrizer_annihilates_specht (n : ℕ) (la mu : Nat.Partition n)
    (h : ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates mu la)
    (v : partitionSubmodule n mu) :
    auxiliaryPartitionGroupAlgebraElementC n la * (v : A' n) = 0 := by
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp v.2
  rw [← hx]
  change auxiliaryPartitionGroupAlgebraElementC n la * (x * auxiliaryPartitionGroupAlgebraElementC n mu) = 0
  simp only [auxiliaryPartitionGroupAlgebraElementC]
  rw [show auxiliaryPartitionGroupAlgebraElementA n la * auxiliaryPartitionGroupAlgebraElementB n la *
    (x * (auxiliaryPartitionGroupAlgebraElementA n mu * auxiliaryPartitionGroupAlgebraElementB n mu)) =
    auxiliaryPartitionGroupAlgebraElementA n la * (auxiliaryPartitionGroupAlgebraElementB n la * x * auxiliaryPartitionGroupAlgebraElementA n mu) *
    auxiliaryPartitionGroupAlgebraElementB n mu from by simp only [mul_assoc],
    sandwich_eq_zero_of_not_dominates n la mu h, mul_zero, zero_mul]
/-- Distinct partitions of `n` determine subtypes whose type of linear equivalences is empty. -/
@[source_ref "Chapter5/Introduction_5.12" (role := supporting),
  source_ref "Chapter5/Theorem5.12.2" (role := primary),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.12.2" (role := primary)]
theorem isEmpty_linearEquiv_of_ne_partition
    (n : ℕ) (la mu : Nat.Partition n) (h : la ≠ mu) :
    IsEmpty ((partitionSubmodule n la) ≃ₗ[natIndexedType n] (partitionSubmodule n mu)) := by
  have hdom_or :
      ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates mu la ∨
      ¬ RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates la mu := by
    by_contra hall
    push Not at hall
    exact h (hall.1.antisymm hall.2).symm
  constructor
  intro φ
  set c_la := auxiliaryPartitionGroupAlgebraElementC n la
  set c_mu := auxiliaryPartitionGroupAlgebraElementC n mu
  have hc_la_mem : c_la ∈ partitionSubmodule n la := Submodule.subset_span rfl
  have hc_mu_mem : c_mu ∈ partitionSubmodule n mu := Submodule.subset_span rfl
  suffices ∀ (V V' : Submodule (A' n) (A' n))
      (c : A' n) (hc_mem : c ∈ V') (hc_sq : c * c ≠ 0)
      (hvanish : ∀ v : V, c * (v : A' n) = 0)
      (ψ : V' ≃ₗ[A' n] V), False by
    rcases hdom_or with h1 | h2
    · exact this (partitionSubmodule n mu) (partitionSubmodule n la) c_la hc_la_mem
        (self_mul_ne_zero n la)
        (fun v => young_symmetrizer_annihilates_specht n la mu h1 v) φ
    · exact this (partitionSubmodule n la) (partitionSubmodule n mu) c_mu hc_mu_mem
        (self_mul_ne_zero n mu)
        (fun v => young_symmetrizer_annihilates_specht n mu la h2 v) φ.symm
  intro V V' c hc_mem hc_sq hvanish ψ
  have hc_sq_mem : c * c ∈ V' := V'.smul_mem c hc_mem
  have h1 : c * (ψ ⟨c, hc_mem⟩ : A' n) = 0 := hvanish (ψ ⟨c, hc_mem⟩)
  have h2 : c * (ψ ⟨c, hc_mem⟩ : A' n) = (ψ ⟨c * c, hc_sq_mem⟩ : A' n) := by
    change (c • ψ ⟨c, hc_mem⟩ : V).val = (ψ ⟨c * c, hc_sq_mem⟩ : V).val
    congr 1
    rw [← ψ.map_smul]; rfl
  have h3 : (ψ ⟨c * c, hc_sq_mem⟩ : A' n) = 0 := h2 ▸ h1
  have h4 : (⟨c * c, hc_sq_mem⟩ : V') = 0 :=
    ψ.injective (Subtype.ext (by simp [h3, map_zero]))
  exact hc_sq (congr_arg Subtype.val h4)
private def conjClassToPartition (n : ℕ) :
    ConjClasses (Equiv.Perm (Fin n)) → Nat.Partition n :=
  Quotient.lift
    (fun σ => (Fintype.card_fin n) ▸ σ.partition)
    (fun _ _ h => congrArg (Fintype.card_fin n ▸ ·) (Equiv.Perm.partition_eq_of_isConj.mp h))
private lemma conjClassToPartition_injective (n : ℕ) :
    Function.Injective (conjClassToPartition n) := by
  intro a b h
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change (Fintype.card_fin n ▸ a.partition) = (Fintype.card_fin n ▸ b.partition) at h
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have : ∀ (m : ℕ) (hm : m = n) (p q : m.Partition),
      (hm ▸ p : Nat.Partition n) = (hm ▸ q : Nat.Partition n) → p = q := by
    intro m hm; subst hm; intro p q hpq; exact hpq
  exact this _ (Fintype.card_fin n) _ _ h
private lemma card_conjClasses_le_card_partition (n : ℕ) :
    Fintype.card (ConjClasses (Equiv.Perm (Fin n))) ≤ Fintype.card (Nat.Partition n) :=
  Fintype.card_le_of_injective _ (conjClassToPartition_injective n)
private lemma center_coeff_conj_invariant'
    {G : Type*} [Group G]
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (g h : G) : a (g * h * g⁻¹) = a h := by
  rw [Subalgebra.mem_center_iff] at ha
  have key := congr_fun (congr_arg (⇑) (ha (MonoidAlgebra.of ℂ G g))) (g * h)
  change (MonoidAlgebra.single g 1 * a).coeff (g * h) =
    (a * MonoidAlgebra.single g 1).coeff (g * h) at key
  rw [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply] at key
  simp only [one_mul, mul_one, inv_mul_cancel_left] at key
  exact key.symm
private lemma finrank_center_monoidAlgebra_le_card_conjClasses
    {G : Type*} [Group G] [Fintype G] [DecidableEq G] :
    Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G)) ≤
      Fintype.card (ConjClasses G) := by
  let f : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₗ[ℂ] (ConjClasses G → ℂ) :=
    { toFun := fun a C => (a : MonoidAlgebra ℂ G) (Quotient.out C)
      map_add' := fun _ _ => funext fun _ => Finsupp.add_apply _ _ _
      map_smul' := fun _ _ => funext fun _ => Finsupp.smul_apply _ _ _ }
  have hf : Function.Injective f := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    ext g
    have h : (a : MonoidAlgebra ℂ G) (Quotient.out (ConjClasses.mk g)) =
        (b : MonoidAlgebra ℂ G) (Quotient.out (ConjClasses.mk g)) := by
      exact congr_fun hab (ConjClasses.mk g)
    have hconj_a : a (Quotient.out (ConjClasses.mk g)) = a g := by
      have hc := Quotient.out_eq (ConjClasses.mk g)
      rw [ConjClasses.quotient_mk_eq_mk] at hc
      obtain ⟨c, hc'⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hc)
      rw [show a (Quotient.out (ConjClasses.mk g)) =
          a (c * Quotient.out (ConjClasses.mk g) * c⁻¹) from
        (center_coeff_conj_invariant' ha c _).symm, hc']
    have hconj_b : b (Quotient.out (ConjClasses.mk g)) = b g := by
      have hc := Quotient.out_eq (ConjClasses.mk g)
      rw [ConjClasses.quotient_mk_eq_mk] at hc
      obtain ⟨c, hc'⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hc)
      rw [show b (Quotient.out (ConjClasses.mk g)) =
          b (c * Quotient.out (ConjClasses.mk g) * c⁻¹) from
        (center_coeff_conj_invariant' hb c _).symm, hc']
    rw [← hconj_a, h, hconj_b]
  calc Module.finrank ℂ (Subalgebra.center ℂ (MonoidAlgebra ℂ G))
      ≤ Module.finrank ℂ (ConjClasses G → ℂ) := LinearMap.finrank_le_finrank_of_injective hf
    _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card ℂ
private lemma finrank_center_pi_matrix
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, NeZero (d i)) :
    Module.finrank ℂ
      (Subalgebra.center ℂ (Π i : Fin k, Matrix (Fin (d i)) (Fin (d i)) ℂ)) = k := by
  let PiMat := (∀ i : Fin k, Matrix (Fin (d i)) (Fin (d i)) ℂ)
  let fwd : ↥(Subalgebra.center ℂ PiMat) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun a i =>
        haveI := hd i
        (a : PiMat) i ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
          ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  let bwd_fun : (Fin k → ℂ) → PiMat :=
    fun c i => c i • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)
  have bwd_mem : ∀ c, bwd_fun c ∈ Subalgebra.center ℂ PiMat := fun c => by
    rw [Subalgebra.mem_center_iff]; intro N; ext i : 1
    change N i * (c i • 1) = (c i • 1) * N i
    rw [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  let bwd : (Fin k → ℂ) →ₗ[ℂ] ↥(Subalgebra.center ℂ PiMat) :=
    { toFun := fun c => ⟨bwd_fun c, bwd_mem c⟩
      map_add' := fun c₁ c₂ => by
        apply Subtype.ext; funext i
        change (c₁ i + c₂ i) • (1 : Matrix _ _ ℂ) = _
        rw [add_smul]; rfl
      map_smul' := fun r c => by
        apply Subtype.ext; funext i
        change (r * c i) • (1 : Matrix _ _ ℂ) = _
        rw [mul_smul]; rfl }
  have hfb : ∀ c, fwd (bwd c) = c := fun c => funext fun i => by
    simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
    simp [Matrix.smul_apply]
  have hbf : ∀ x : ↥(Subalgebra.center ℂ PiMat), bwd (fwd x) = x := fun ⟨f, hf⟩ => by
    apply Subtype.ext; ext i a b
    simp only [fwd, bwd, bwd_fun, LinearMap.coe_mk, AddHom.coe_mk]
    have hfc : f i ∈ Subalgebra.center ℂ (Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
      rw [Subalgebra.mem_center_iff]; intro M
      have hf' : ∀ b : PiMat, b * f = f * b := Subalgebra.mem_center_iff.mp hf
      have h := hf' (Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i M)
      have lhs : (Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i M * f) i =
          M * f i := by rw [Pi.mul_apply, Pi.single_eq_same]
      have rhs : (f * Pi.single (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i M) i =
          f i * M := by rw [Pi.mul_apply, Pi.single_eq_same]
      rw [show M * f i = (Pi.single
        (M := fun j => Matrix (Fin (d j)) (Fin (d j)) ℂ) i M * f) i from lhs.symm, h, rhs]
    rw [Algebra.IsCentral.center_eq_bot] at hfc
    rw [Algebra.mem_bot] at hfc
    obtain ⟨c, hc⟩ := Set.mem_range.mp hfc
    have hfi : f i = c • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
      rw [← hc, Algebra.algebraMap_eq_smul_one]
    rw [hfi]; simp [Matrix.smul_apply, Matrix.one_apply]
  have e : ↥(Subalgebra.center ℂ PiMat) ≃ₗ[ℂ] (Fin k → ℂ) :=
    { fwd with invFun := bwd, left_inv := hbf, right_inv := hfb }
  have : Module.finrank ℂ (Fin k → ℂ) = k := by
    rw [Module.finrank_fintype_fun_eq_card ℂ, Fintype.card_fin]
  linarith [e.finrank_eq]
private lemma wedderburn_blocks_le_card_partition (n : ℕ)
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ i, NeZero (d i))
    (e : A' n ≃ₐ[ℂ] Π i : Fin k, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    k ≤ Fintype.card (Nat.Partition n) := by
  have h_center_dim : Module.finrank ℂ (Subalgebra.center ℂ (A' n)) = k := by
    have : Module.finrank ℂ (Subalgebra.center ℂ (A' n)) =
        Module.finrank ℂ (Subalgebra.center ℂ
          (Π i : Fin k, Matrix (Fin (d i)) (Fin (d i)) ℂ)) := by
      have hmap : (Subalgebra.center ℂ (A' n)).map e.toAlgHom =
          Subalgebra.center ℂ (Π i : Fin k, Matrix (Fin (d i)) (Fin (d i)) ℂ) := by
        ext x; constructor
        · rintro ⟨a, ha, rfl⟩
          exact Subalgebra.mem_center_iff.mpr fun b => by
            have := Subalgebra.mem_center_iff.mp ha (e.symm b)
            simpa using congr_arg e this
        · intro hx
          exact ⟨e.symm x, Subalgebra.mem_center_iff.mpr fun b => by
            have := Subalgebra.mem_center_iff.mp hx (e b)
            simpa using congr_arg e.symm this, e.apply_symm_apply x⟩
      exact LinearEquiv.finrank_eq
        ((Subalgebra.center ℂ (A' n)).equivMapOfInjective
          e.toAlgHom e.injective |>.toLinearEquiv |>.trans
          (Subalgebra.equivOfEq _ _ hmap).toLinearEquiv)
    rw [this, finrank_center_pi_matrix hd]
  have h_center_le : Module.finrank ℂ (Subalgebra.center ℂ (A' n)) ≤
      Fintype.card (ConjClasses (G' n)) :=
    finrank_center_monoidAlgebra_le_card_conjClasses
  calc k = Module.finrank ℂ (Subalgebra.center ℂ (A' n)) := h_center_dim.symm
    _ ≤ Fintype.card (ConjClasses (G' n)) := h_center_le
    _ ≤ Fintype.card (Nat.Partition n) := card_conjClasses_le_card_partition n
/-- For every `D` of the indicated type, its associated value is at most the number of partitions of `n`. -/
lemma value_le_partition_card (n : ℕ)
    (D : DecompositionData ℂ (G' n)) :
    D.count ≤ Fintype.card (Nat.Partition n) := by
  haveI : Invertible (Fintype.card (G' n) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  obtain ⟨n_cc, V_cc, hV_simp, hV_inj, hV_surj, hn_cc⟩ := exists_simpleReps_card_eq_conjClasses
    (G := G' n) (k := ℂ)
  suffices h_eq : D.count = n_cc by
    calc D.count = n_cc := h_eq
      _ = Fintype.card (ConjClasses (G' n)) := hn_cc
      _ ≤ Fintype.card (Nat.Partition n) := card_conjClasses_le_card_partition n
  have f : ∀ j : Fin D.count, ∃ i : Fin n_cc, Nonempty (D.representation j ≅ V_cc i) :=
    fun j => hV_surj (D.representation j) (D.simple_representation j)
  choose f hf using f
  have f_inj : Function.Injective f := by
    intro j₁ j₂ h
    exact D.representation_index_eq_of_iso j₁ j₂
      ⟨(hf j₁).some ≪≫ (h ▸ (hf j₂).some.symm)⟩
  obtain ⟨V_D, _, hD_inj, hD_surj⟩ := D.exists_completeSimpleFamily
  have g : ∀ i : Fin n_cc, ∃ j : Fin D.count, Nonempty (V_cc i ≅ V_D j) :=
    fun i => hD_surj (V_cc i) (hV_simp i)
  choose g hg using g
  have g_inj : Function.Injective g := by
    intro i₁ i₂ h
    exact hV_inj i₁ i₂ ⟨(hg i₁).some ≪≫ (h ▸ (hg i₂).some.symm)⟩
  have h1 : D.count ≤ n_cc := by
    have := Fintype.card_le_of_injective f f_inj
    simp only [Fintype.card_fin] at this; exact this
  have h2 : n_cc ≤ D.count := by
    have := Fintype.card_le_of_injective g g_inj
    simp only [Fintype.card_fin] at this; exact this
  omega
end
end RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
