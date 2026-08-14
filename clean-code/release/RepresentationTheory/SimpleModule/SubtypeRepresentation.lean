import Mathlib
import RepresentationTheory.PartitionAuxiliary
import RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.SimpleModule.SubtypeRepresentation

noncomputable section
open scoped Classical

open RepresentationTheory.PartitionAuxiliary
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.FDRep.GroupAlgebraDecomposition
open RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra

private abbrev G' (n : ℕ) := Equiv.Perm (Fin n)
private abbrev A' (n : ℕ) := MonoidAlgebra ℂ (G' n)

private noncomputable def centralIdem' (n : ℕ) (D : DecompositionData ℂ (G' n)) (j : Fin D.count) :
    A' n :=
  D.groupAlgebraEquivMatrix.symm (Pi.single j 1)

private lemma centralIdem'_sq (n : ℕ) (D : DecompositionData ℂ (G' n)) (j : Fin D.count) :
    centralIdem' n D j * centralIdem' n D j = centralIdem' n D j := by
  simp only [centralIdem']
  rw [← map_mul D.groupAlgebraEquivMatrix.symm]
  congr 1; ext i
  simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

private lemma centralIdem'_sum (n : ℕ) (D : DecompositionData ℂ (G' n)) :
    ∑ j, centralIdem' n D j = 1 := by
  simp only [centralIdem']
  rw [← map_sum D.groupAlgebraEquivMatrix.symm]
  conv_rhs => rw [← AlgEquiv.symm_apply_apply D.groupAlgebraEquivMatrix 1]
  congr 1
  ext i
  simp only [Finset.sum_apply, map_one, Pi.one_apply]
  rw [Finset.sum_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hji; simp [Pi.single_eq_of_ne (Ne.symm hji)]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma centralIdem'_orthog (n : ℕ) (D : DecompositionData ℂ (G' n))
    (i j : Fin D.count) (hij : i ≠ j) :
    centralIdem' n D i * centralIdem' n D j = 0 := by
  simp only [centralIdem']
  rw [← map_mul D.groupAlgebraEquivMatrix.symm, ← map_zero D.groupAlgebraEquivMatrix.symm]
  congr 1; ext k
  simp only [Pi.mul_apply, Pi.zero_apply]
  by_cases hki : k = i
  · subst hki
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij]
    simp
  · simp [Pi.single_eq_of_ne hki]

private lemma centralIdem'_comm (n : ℕ) (D : DecompositionData ℂ (G' n))
    (j : Fin D.count) (a : A' n) :
    centralIdem' n D j * a = a * centralIdem' n D j := by
  simp only [centralIdem']
  apply D.groupAlgebraEquivMatrix.injective
  simp only [map_mul, AlgEquiv.apply_symm_apply]
  ext i
  simp only [Pi.mul_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

private lemma exists_unique_block (n : ℕ) (D : DecompositionData ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L] :
    ∃! j : Fin D.count, ∀ l : L, centralIdem' n D j • l = l := by

  have hsum : ∀ l : L, l = ∑ j, centralIdem' n D j • l := by
    intro l; conv_lhs => rw [← one_smul (A' n) l, ← centralIdem'_sum n D]; rw [Finset.sum_smul]

  have hact : ∀ j, (∀ l : L, centralIdem' n D j • l = 0) ∨
                    (∀ l : L, centralIdem' n D j • l = l) := by
    intro j

    let ker_j : Submodule (A' n) L :=
      { carrier := {l | centralIdem' n D j • l = l}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          change centralIdem' n D j • (a + b) = a + b
          rw [smul_add, ha, hb]
        smul_mem' := fun a {l} hl => by
          change centralIdem' n D j • (a • l) = a • l
          rw [← mul_smul, centralIdem'_comm, mul_smul, hl] }
    rcases IsSimpleOrder.eq_bot_or_eq_top ker_j with h | h
    ·

      left; intro l
      have : centralIdem' n D j • l ∈ ker_j := by
        change centralIdem' n D j • (centralIdem' n D j • l) = centralIdem' n D j • l
        rw [← mul_smul, centralIdem'_sq]
      rw [h] at this; exact (Submodule.mem_bot (A' n)).mp this
    · right; intro l
      have : l ∈ ker_j := h ▸ Submodule.mem_top
      exact this

  haveI := IsSimpleModule.nontrivial (R := A' n) (M := L)
  obtain ⟨l₀, hl₀⟩ := exists_ne (0 : L)
  have hexists : ∃ j, ∀ l : L, centralIdem' n D j • l = l := by
    by_contra hall
    push Not at hall
    have : ∀ j, ∀ l : L, centralIdem' n D j • l = 0 := by
      intro j; exact (hact j).resolve_right (fun h => (hall j).elim (fun l hl => hl (h l)))
    exact hl₀ (by rw [hsum l₀, Finset.sum_eq_zero (fun j _ => this j l₀)])
  obtain ⟨j₀, hj₀⟩ := hexists

  refine ⟨j₀, hj₀, ?_⟩
  intro j hj
  by_contra hij

  have h1 : centralIdem' n D j * centralIdem' n D j₀ = 0 := centralIdem'_orthog n D j j₀ hij
  have h2 : (centralIdem' n D j * centralIdem' n D j₀) • l₀ = l₀ := by
    rw [mul_smul, hj₀ l₀, hj l₀]
  rw [h1, zero_smul] at h2
  exact hl₀ h2.symm

private noncomputable def blockOf (n : ℕ) (D : DecompositionData ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L] :
    Fin D.count :=
  (exists_unique_block n D L).choose

private lemma blockOf_spec (n : ℕ) (D : DecompositionData ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L] :
    ∀ l : L, centralIdem' n D (blockOf n D L) • l = l :=
  (exists_unique_block n D L).choose_spec.1

private lemma blockOf_unique (n : ℕ) (D : DecompositionData ℂ (G' n))
    (L : Type) [AddCommGroup L] [Module (A' n) L] [IsSimpleModule (A' n) L]
    (j : Fin D.count) (hj : ∀ l : L, centralIdem' n D j • l = l) :
    j = blockOf n D L :=
  (exists_unique_block n D L).choose_spec.2 j hj

private lemma action_factors_block (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x) (a : A' n) :
    a * x = D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a)) * x := by
  have key : a * centralIdem' n D j₀ = D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a)) := by
    apply D.groupAlgebraEquivMatrix.injective; rw [map_mul, AlgEquiv.apply_symm_apply]
    ext k; simp only [Pi.mul_apply, centralIdem', AlgEquiv.apply_symm_apply]
    by_cases hk : k = j₀
    · subst hk; simp [Pi.single_eq_same, DecompositionData.matrixBlockHom, Pi.evalRingHom]
    · simp [Pi.single_eq_of_ne hk]
  calc a * x = a * (centralIdem' n D j₀ * x) := by rw [hx]
    _ = (a * centralIdem' n D j₀) * x := by rw [mul_assoc]
    _ = D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a)) * x := by rw [key]

private lemma iso_eq_single_of_block (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x) :
    D.groupAlgebraEquivMatrix x = Pi.single j₀ (D.matrixBlockHom j₀ x) := by
  have h1 : D.groupAlgebraEquivMatrix (centralIdem' n D j₀ * x) = D.groupAlgebraEquivMatrix x := by rw [hx]
  rw [map_mul] at h1; simp only [centralIdem', AlgEquiv.apply_symm_apply] at h1
  ext k; rw [← h1]; simp only [Pi.mul_apply]
  by_cases hk : k = j₀
  · subst hk; simp [Pi.single_eq_same, DecompositionData.matrixBlockHom, Pi.evalRingHom]
  · simp [Pi.single_eq_of_ne hk]

private lemma recover_block (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x) :
    D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ x)) = x := by
  rw [← iso_eq_single_of_block n D j₀ hx, D.groupAlgebraEquivMatrix.symm_apply_apply]

private lemma proj_inj_on_block (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    {x : A' n} (hx : centralIdem' n D j₀ * x = x)
    (h0 : D.matrixBlockHom j₀ x = 0) : x = 0 := by
  rw [← recover_block n D j₀ hx, h0, Pi.single_zero, map_zero]

private def projImage (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    (L : Submodule (A' n) (A' n)) : Submodule
      (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ)
      (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ) where
  carrier := {m | ∃ l ∈ L, D.matrixBlockHom j₀ l = m}
  zero_mem' := ⟨0, L.zero_mem, map_zero _⟩
  add_mem' := fun ⟨l₁, hl₁, he₁⟩ ⟨l₂, hl₂, he₂⟩ =>
    ⟨l₁ + l₂, L.add_mem hl₁ hl₂, by rw [map_add, he₁, he₂]⟩
  smul_mem' := fun m {x} hx => by
    obtain ⟨l, hl, he⟩ := hx
    obtain ⟨a, ha⟩ := D.matrixBlockHom_surjective j₀ m
    exact ⟨a * l, L.smul_mem a hl, by
      rw [map_mul, ha, he, smul_eq_mul]⟩

set_option maxHeartbeats 12800000 in

private lemma projImage_isSimple (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    (L : Submodule (A' n) (A' n)) [IsSimpleModule (A' n) L]
    (hL : ∀ l : L, centralIdem' n D j₀ * (l : A' n) = ↑l) :
    IsSimpleModule
      (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ)
      (projImage n D j₀ L) := by
  rw [isSimpleModule_iff_isAtom]
  constructor
  ·
    intro h
    haveI := IsSimpleModule.nontrivial (R := A' n) (M := L)
    obtain ⟨l, hl⟩ := exists_ne (0 : L)
    have : D.matrixBlockHom j₀ ↑l = 0 := by
      have hm : D.matrixBlockHom j₀ ↑l ∈ projImage n D j₀ L := ⟨↑l, l.prop, rfl⟩
      rw [h] at hm; exact (Submodule.mem_bot _).mp hm
    exact hl (Subtype.ext (proj_inj_on_block n D j₀ (hL l) this))
  ·
    intro N hN
    by_contra hN_ne_bot
    have hN_le := le_of_lt hN

    set N' : Submodule (A' n) L :=
      { carrier := {l : L | D.matrixBlockHom j₀ ↑l ∈ N}
        zero_mem' := by simp [N.zero_mem]
        add_mem' := fun {a b} ha hb => by
          change D.matrixBlockHom j₀ (↑a + ↑b) ∈ N
          rw [map_add]; exact N.add_mem ha hb
        smul_mem' := fun c {l} hl => by
          change D.matrixBlockHom j₀ (c * ↑l) ∈ N
          rw [map_mul]; exact N.smul_mem _ hl } with N'_def

    have hN'_ne_top : N' ≠ ⊤ := by
      intro h_eq
      apply ne_of_lt hN
      apply le_antisymm hN_le
      intro m hm
      obtain ⟨l, hl, he⟩ := hm
      have : (⟨l, hl⟩ : L) ∈ N' := h_eq ▸ Submodule.mem_top
      rw [N'_def] at this
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at this
      rw [← he]; exact this
    have hN'_bot :=
      (IsSimpleOrder.eq_bot_or_eq_top N').resolve_right hN'_ne_top

    apply hN_ne_bot; rw [eq_bot_iff]
    intro m hmN
    have hm_pi := hN_le hmN
    obtain ⟨l, hl, he⟩ := hm_pi
    have : (⟨l, hl⟩ : L) ∈ N' := by
      rw [N'_def]
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      rw [he]; exact hmN
    rw [hN'_bot] at this
    rw [Submodule.mem_bot] at this
    have hl0 : l = 0 := congr_arg Subtype.val this
    rw [Submodule.mem_bot, ← he, hl0, map_zero]

private lemma recover_mem_of_projImage (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    (L : Submodule (A' n) (A' n))
    (hL : ∀ l : L, centralIdem' n D j₀ * (l : A' n) = ↑l)
    {m : Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ}
    (hm : m ∈ projImage n D j₀ L) :
    D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m) ∈ L := by
  obtain ⟨l, hl, he⟩ := hm
  rw [← he, recover_block n D j₀ (hL ⟨l, hl⟩)]
  exact hl

private lemma recover_injective_on_projImage (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    {m₁ m₂ : Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ}
    (h : D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m₁) = D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m₂)) :
    m₁ = m₂ := by
  have h1 := D.groupAlgebraEquivMatrix.symm.injective h
  have h2 := congr_fun h1 j₀
  simp only [Pi.single_eq_same] at h2
  exact h2

private lemma proj_recover (n : ℕ) (D : DecompositionData ℂ (G' n)) (j₀ : Fin D.count)
    (m : Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ) :
    D.matrixBlockHom j₀ (D.groupAlgebraEquivMatrix.symm (Pi.single j₀ m)) = m := by
  simp [DecompositionData.matrixBlockHom, Pi.evalRingHom, Pi.single_eq_same]

private lemma same_block_iso (n : ℕ) (D : DecompositionData ℂ (G' n))
    (L₁ L₂ : Submodule (A' n) (A' n))
    [IsSimpleModule (A' n) L₁] [IsSimpleModule (A' n) L₂]
    (hblock : blockOf n D L₁ = blockOf n D L₂) :
    Nonempty (L₁ ≃ₗ[A' n] L₂) := by
  set j₀ := blockOf n D L₁ with hj₀_def

  have hL₁ : ∀ l : L₁, centralIdem' n D j₀ * (l : A' n) = ↑l :=
    fun l => congr_arg Subtype.val (blockOf_spec n D L₁ l)
  have hL₂ : ∀ l : L₂, centralIdem' n D j₀ * (l : A' n) = ↑l :=
    fun l => congr_arg Subtype.val (hblock ▸ blockOf_spec n D L₂ l)

  haveI := projImage_isSimple n D j₀ L₁ hL₁
  haveI := projImage_isSimple n D j₀ L₂ hL₂
  haveI := D.dimension_neZero j₀
  haveI : IsSimpleRing (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ) := IsSimpleRing.matrix ..
  haveI : IsArtinianRing (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ) := inferInstance

  obtain ⟨φ_mat⟩ := (IsSimpleRing.isIsotypic
    (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ)
    (Matrix (Fin (D.dimension j₀)) (Fin (D.dimension j₀)) ℂ))
    (projImage n D j₀ L₂) (projImage n D j₀ L₁)

  let projElem (L : Submodule (A' n) (A' n)) (l : L) : projImage n D j₀ L :=
    ⟨D.matrixBlockHom j₀ ↑l, ↑l, l.prop, rfl⟩

  set f : L₁ →ₗ[A' n] L₂ :=
    { toFun := fun l₁ =>
        ⟨D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val),
         recover_mem_of_projImage n D j₀ L₂ hL₂ (φ_mat (projElem L₁ l₁)).prop⟩
      map_add' := fun l₁ l₂ => by
        apply Subtype.ext; apply D.groupAlgebraEquivMatrix.injective
        simp only [Submodule.coe_add, map_add, AlgEquiv.apply_symm_apply]

        have he : projElem L₁ (l₁ + l₂) = projElem L₁ l₁ + projElem L₁ l₂ := by
          ext; simp [projElem, map_add]
        rw [he, φ_mat.map_add, Submodule.coe_add, Pi.single_add]
      map_smul' := fun a l₁ => by
        apply Subtype.ext
        simp only [SetLike.val_smul, smul_eq_mul]

        set v := (φ_mat (projElem L₁ l₁)).val

        have e_smul : projElem L₁ (a • l₁) = D.matrixBlockHom j₀ a • projElem L₁ l₁ := by
          ext; simp [projElem, map_mul]
        have φ_smul : (φ_mat (projElem L₁ (a • l₁))).val = D.matrixBlockHom j₀ a * v := by
          rw [e_smul, φ_mat.map_smul]; rfl
        rw [show D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ (a • l₁))).val) =
          D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (D.matrixBlockHom j₀ a * v)) from by rw [φ_smul]]

        have hv_mem : D.groupAlgebraEquivMatrix.symm (Pi.single j₀ v) ∈ L₂ :=
          recover_mem_of_projImage n D j₀ L₂ hL₂ (φ_mat (projElem L₁ l₁)).prop
        have hv_block : centralIdem' n D j₀ * D.groupAlgebraEquivMatrix.symm (Pi.single j₀ v) =
            D.groupAlgebraEquivMatrix.symm (Pi.single j₀ v) := hL₂ ⟨_, hv_mem⟩
        simp only [RingHom.id_apply]
        rw [action_factors_block n D j₀ hv_block a, ← map_mul D.groupAlgebraEquivMatrix.symm]
        congr 1; ext k; simp only [Pi.mul_apply]
        by_cases hk : k = j₀
        · subst hk; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne hk] }

  have hf_ne : f ≠ 0 := by
    intro h
    haveI := IsSimpleModule.nontrivial (R := A' n) (M := L₁)
    obtain ⟨l₁, hl₁⟩ := exists_ne (0 : L₁)
    have h1 : f l₁ = 0 := congr_fun (congr_arg DFunLike.coe h) l₁

    have h2 : D.groupAlgebraEquivMatrix.symm (Pi.single j₀ (φ_mat (projElem L₁ l₁)).val) = 0 :=
      congr_arg Subtype.val h1

    have h3 : (φ_mat (projElem L₁ l₁)).val = 0 := by
      have h3a := D.groupAlgebraEquivMatrix.symm.injective (by rw [h2, map_zero] : D.groupAlgebraEquivMatrix.symm (Pi.single j₀
        (φ_mat (projElem L₁ l₁)).val) = D.groupAlgebraEquivMatrix.symm 0)
      have h3b := congr_fun h3a j₀
      simp only [Pi.single_eq_same, Pi.zero_apply] at h3b
      exact h3b

    have h4 : projElem L₁ l₁ = 0 := by
      have : φ_mat (projElem L₁ l₁) = 0 := Subtype.ext h3
      exact φ_mat.injective (by rw [this, map_zero])
    have h5 : (projElem L₁ l₁).val = 0 := congr_arg Subtype.val h4
    exact hl₁ (Subtype.ext (proj_inj_on_block n D j₀ (hL₁ l₁) h5))

  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf_ne)⟩

private lemma blockOf_specht_injective (n : ℕ) (D : DecompositionData ℂ (G' n))
    (la mu : Nat.Partition n)
    (hla : IsSimpleModule (A' n) (partitionSubmodule n la))
    (hmu : IsSimpleModule (A' n) (partitionSubmodule n mu))
    (hblock : blockOf n D (partitionSubmodule n la) = blockOf n D (partitionSubmodule n mu)) :
    la = mu := by
  by_contra h
  have ⟨φ⟩ := @same_block_iso n D (partitionSubmodule n la) (partitionSubmodule n mu) hla hmu hblock
  exact (isEmpty_linearEquiv_of_ne_partition n la mu h).false φ

private lemma exists_young_symmetrizer_nontrivial (n : ℕ)
    (M : Type) [AddCommGroup M] [Module (A' n) M]
    [IsSimpleModule (A' n) M] :
    ∃ la : Nat.Partition n, ∃ m : M, auxiliaryPartitionGroupAlgebraElementC n la • m ≠ 0 := by
  by_contra h
  push Not at h

  let D := DecompositionData.default (k := ℂ) (G := G' n)

  set j₀ := blockOf n D M

  have hspecht_simple : ∀ la : Nat.Partition n,
      IsSimpleModule (A' n) (partitionSubmodule n la) := partitionSubmodule_isSimpleModule n

  let β : Nat.Partition n → Fin D.count :=
    fun la => @blockOf n D (partitionSubmodule n la) _ _ (hspecht_simple la)
  have β_inj : Function.Injective β := by
    intro la mu h
    exact blockOf_specht_injective n D la mu (hspecht_simple la) (hspecht_simple mu) h

  have hn_le := value_le_partition_card n D

  have hcard_eq : Fintype.card (Nat.Partition n) = Fintype.card (Fin D.count) := by
    apply le_antisymm
    · have := Fintype.card_le_of_injective β β_inj; exact this
    · rwa [Fintype.card_fin]

  have β_surj : Function.Surjective β :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard_eq)).mp β_inj

  obtain ⟨la₀, hla₀⟩ := β_surj j₀

  have hM_block := blockOf_spec n D M
  haveI := hspecht_simple la₀

  have hiso : Nonempty (M ≃ₗ[A' n] partitionSubmodule n la₀) := by

    obtain ⟨I, ⟨φ_M⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (A' n) M

    haveI : IsSimpleModule (A' n) I := IsSimpleModule.congr φ_M.symm
    have hI_block : blockOf n D I = j₀ := by
      apply (blockOf_unique n D I j₀ _).symm
      intro l
      have := hM_block (φ_M.symm l)
      rw [← φ_M.symm.map_smul] at this
      exact φ_M.symm.injective this

    have hblock : blockOf n D I = blockOf n D (partitionSubmodule n la₀) := by
      rw [hI_block]; exact hla₀.symm
    obtain ⟨ψ⟩ := same_block_iso n D I (partitionSubmodule n la₀) hblock
    exact ⟨φ_M.trans ψ⟩
  obtain ⟨φ⟩ := hiso

  set c := auxiliaryPartitionGroupAlgebraElementC n la₀
  have hc_mem : c ∈ partitionSubmodule n la₀ := Submodule.subset_span rfl
  have hc_sq_mem : c * c ∈ partitionSubmodule n la₀ :=
    (partitionSubmodule n la₀).smul_mem c hc_mem
  have hc_sq_ne : (⟨c * c, hc_sq_mem⟩ : partitionSubmodule n la₀) ≠ 0 := by
    intro h_eq; exact self_mul_ne_zero n la₀ (Subtype.ext_iff.mp h_eq)

  have hpre_ne : φ.symm ⟨c * c, hc_sq_mem⟩ ≠ 0 := by
    intro h_eq; exact hc_sq_ne (φ.symm.injective (by simp [h_eq]))

  have h1 : c • (φ.symm ⟨c, hc_mem⟩) = 0 := h la₀ (φ.symm ⟨c, hc_mem⟩)
  have h2 : φ.symm ⟨c * c, hc_sq_mem⟩ = 0 := by
    rw [show (⟨c * c, hc_sq_mem⟩ : partitionSubmodule n la₀) = c • ⟨c, hc_mem⟩ from rfl]
    rw [LinearEquiv.map_smul]
    exact h1
  exact hpre_ne h2

private noncomputable def spechtEvalMap (n : ℕ) (la : Nat.Partition n)
    (M : Type) [AddCommGroup M] [Module (A' n) M] (m₀ : M) :
    (partitionSubmodule n la) →ₗ[A' n] M where
  toFun v := (v : A' n) • m₀
  map_add' v w := by
    change ((v : A' n) + (w : A' n)) • m₀ = (v : A' n) • m₀ + (w : A' n) • m₀
    exact add_smul (v : A' n) (w : A' n) m₀
  map_smul' a v := by
    change (a * (v : A' n)) • m₀ = a • ((v : A' n) • m₀)
    exact mul_smul a (v : A' n) m₀

/-- Every simple module in this family admits a linear identification with a suitably chosen membership-defined subtype. -/
@[source_ref "Chapter5/Introduction_5.12" (role := primary),
  source_ref "Chapter5/Theorem5.12.2" (role := supporting),
  source_ref "Chapter5/Discussion_proof_of_Theorem5.12.2" (role := primary)]
theorem exists_linearEquiv_to_subtype
    (n : ℕ) (M : Type) [AddCommGroup M] [Module (natIndexedType n) M]
    [IsSimpleModule (natIndexedType n) M] :
    ∃ la : Nat.Partition n,
      Nonempty (M ≃ₗ[natIndexedType n] (partitionSubmodule n la)) := by

  obtain ⟨la, m₀, hm₀⟩ := exists_young_symmetrizer_nontrivial n M

  set f := spechtEvalMap n la M m₀
  have hf_ne : f ≠ 0 := by
    intro h
    apply hm₀
    have : f ⟨auxiliaryPartitionGroupAlgebraElementC n la, Submodule.subset_span rfl⟩ = 0 :=
      congr_fun (congr_arg DFunLike.coe h) ⟨auxiliaryPartitionGroupAlgebraElementC n la, Submodule.subset_span rfl⟩
    exact this

  haveI : IsSimpleModule (A' n) (partitionSubmodule n la) := partitionSubmodule_isSimpleModule n la
  have hf_bij := LinearMap.bijective_of_ne_zero hf_ne

  exact ⟨la, ⟨(LinearEquiv.ofBijective f hf_bij).symm⟩⟩

end

end RepresentationTheory.SimpleModule.SubtypeRepresentation
