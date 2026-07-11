import Mathlib

/-!
# Problem 4.12.11: elasticity theory and representations of `SO(3)`

**Problem 4.12.11.** (Elasticity theory.) Let `V = ℝ³` with its standard inner product, on
which `SO(3)` acts. The deformation tensor lives in `S²V` and the stress tensor in
`End(V)`, and Hooke's law is a linear `SO(3)`-equivariant map `f : S²V → End(V)`.

(a) Show that `End(V)` admits a decomposition `ℝ ⊕ V ⊕ W`, where `ℝ` is the trivial
representation, `V` is the standard `3`-dimensional representation, and `W` is a
`5`-dimensional representation of `SO(3)`. Show that `S²V = ℝ ⊕ W`.

(b) Show that `V` and `W` are irreducible, even after complexification. Deduce using Schur's
lemma that `S_P` is always symmetric, and for `x ∈ ℝ`, `y ∈ W` one has `f(x + y) = Kx + μy`
for some real numbers `K, μ` (the compression modulus `K` and shearing modulus `μ`).

## Formalization

We take `V = Fin 3 → ℝ` and `End(V) = Matrix (Fin 3) (Fin 3) ℝ`, with `SO(3)` modelled by
`Matrix.specialOrthogonalGroup (Fin 3) ℝ` acting on `End(V)` by conjugation
`M ↦ A · M · Aᵀ` (`conjRep`; for orthogonal `A`, `Aᵀ = A⁻¹`). Inside `End(V)`:

* `scalarSub` = scalar matrices `ℝ·1` (the trivial summand `ℝ`);
* `skewSub` = skew-symmetric matrices `Mᵀ = -M` (`3`-dimensional, isomorphic to the standard
  representation `V`);
* `symSub` = symmetric matrices `Mᵀ = M` (this is `S²V`, `6`-dimensional);
* `tracelessSymSub` = traceless symmetric matrices (the `5`-dimensional representation `W`).

Statements (faithful signatures, `sorry` proofs — a statement pass):

* **(a)** each subspace is `SO(3)`-invariant; `End(V) = scalarSub ⊕ skewSub ⊕ tracelessSymSub`
  and `symSub = scalarSub ⊕ tracelessSymSub`; the dimensions are `1, 3, 5`.
* **(b)** `skewSub` (`≅ V`) and `tracelessSymSub` (`= W`) are irreducible (stated over `ℝ`;
  the irreducibility survives complexification, recorded in this docstring). Hooke's law:
  any `SO(3)`-equivariant `f : End(V) → End(V)` acts as a scalar `K` on `scalarSub` and a
  scalar `μ` on `tracelessSymSub`, and maps symmetric matrices to symmetric matrices (so the
  stress tensor `S_P` is symmetric).
-/

open Matrix

noncomputable section

namespace Etingof.Problem4_12_11

/-- `SO(3)`, modelled as the special orthogonal group of `3 × 3` real matrices. -/
abbrev SO3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := specialOrthogonalGroup (Fin 3) ℝ

/-- `End(V) = Matrix (Fin 3) (Fin 3) ℝ`, on which `SO(3)` acts by conjugation. -/
abbrev EndV : Type := Matrix (Fin 3) (Fin 3) ℝ

/-- The conjugation action of `SO(3)` on `End(V)`: `conjRep A M = A · M · Aᵀ`. Since `A` is
orthogonal, `Aᵀ = A⁻¹`, so this is genuine conjugation. -/
def conjRep : Representation ℝ SO3 EndV where
  toFun A := (LinearMap.mulLeft ℝ (A : EndV)).comp
    (LinearMap.mulRight ℝ (star (A : EndV)))
  map_one' := by
    ext M
    simp
  map_mul' A B := by
    ext M
    simp only [Submonoid.coe_mul, star_mul, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, Module.End.mul_apply]
    simp [mul_assoc]

@[simp]
theorem conjRep_apply (A : SO3) (M : EndV) :
    conjRep A M = (A : EndV) * M * star (A : EndV) := by
  simp [conjRep, mul_assoc]

/-- The trivial summand `ℝ ⊆ End(V)`: the scalar matrices `ℝ·1`. -/
def scalarSub : Submodule ℝ EndV := Submodule.span ℝ {(1 : EndV)}

/-- The skew-symmetric matrices `{M | Mᵀ = -M}` — a `3`-dimensional subrepresentation
isomorphic to the standard representation `V`. -/
def skewSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]; abel
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha, smul_neg]

/-- The symmetric matrices `{M | Mᵀ = M}` — this is `S²V ⊆ End(V)`. -/
def symSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha]

/-- The traceless symmetric matrices `{M | Mᵀ = M ∧ trace M = 0}` — the `5`-dimensional
representation `W`. -/
def tracelessSymSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = M ∧ M.trace = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ⟨by rw [transpose_add, ha.1, hb.1], by rw [trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact ⟨by simp, by simp⟩
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ⟨by rw [transpose_smul, ha.1], by rw [trace_smul, ha.2, smul_zero]⟩

theorem scalar_le_sym : scalarSub ≤ symSub := by
  intro M hM
  rw [scalarSub, Submodule.mem_span_singleton] at hM
  obtain ⟨c, rfl⟩ := hM
  change (c • (1 : EndV))ᵀ = c • 1
  rw [transpose_smul, transpose_one]

theorem tracelessSym_le_sym : tracelessSymSub ≤ symSub := fun _ hM => hM.1

/-! ### Orthogonality helpers -/

/-- Over `ℝ`, the `star` of a matrix is its transpose. -/
theorem star_coe_eq_transpose (A : SO3) : star (A : EndV) = (A : EndV)ᵀ := by
  ext i j
  simp

/-- `A · Aᵀ = 1` for `A ∈ SO(3)`. -/
theorem coe_mul_star (A : SO3) : (A : EndV) * star (A : EndV) = 1 :=
  mem_unitaryGroup_iff.mp (mem_specialOrthogonalGroup_iff.mp A.2).1

/-- `Aᵀ · A = 1` for `A ∈ SO(3)`. -/
theorem star_mul_coe (A : SO3) : star (A : EndV) * (A : EndV) = 1 :=
  mem_unitaryGroup_iff'.mp (mem_specialOrthogonalGroup_iff.mp A.2).1

/-! ### Part (a): the decomposition -/

/-- **(a)** Each of the three subspaces is `SO(3)`-invariant. -/
theorem conjRep_invariant (S : Submodule ℝ EndV)
    (hS : S = scalarSub ∨ S = skewSub ∨ S = tracelessSymSub)
    (A : SO3) (M : EndV) (hM : M ∈ S) : conjRep A M ∈ S := by
  have hAstar : (A : EndV) * star (A : EndV) = 1 := coe_mul_star A
  have hstarA : star (A : EndV) * (A : EndV) = 1 := star_mul_coe A
  have hstarT : star (A : EndV) = (A : EndV)ᵀ := star_coe_eq_transpose A
  rw [conjRep_apply]
  rcases hS with h | h | h
  · -- scalarSub: `A · (c•1) · Aᵀ = c • (A · Aᵀ) = c•1`
    subst h
    rw [scalarSub, Submodule.mem_span_singleton] at hM ⊢
    obtain ⟨c, rfl⟩ := hM
    exact ⟨c, by rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hAstar]⟩
  · -- skewSub: `(A · M · Aᵀ)ᵀ = A · Mᵀ · Aᵀ = -(A · M · Aᵀ)`
    subst h
    simp only [skewSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] at hM ⊢
    rw [hstarT]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_neg,
      Matrix.neg_mul, mul_assoc]
  · -- tracelessSymSub: symmetric as above; trace preserved by cyclicity
    subst h
    simp only [tracelessSymSub, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] at hM ⊢
    obtain ⟨hsym, htr⟩ := hM
    refine ⟨?_, ?_⟩
    · rw [hstarT]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym, mul_assoc]
    · rw [Matrix.trace_mul_comm, ← mul_assoc, hstarA, Matrix.one_mul, htr]

theorem mem_skewSub_iff {M : EndV} : M ∈ skewSub ↔ Mᵀ = -M := Iff.rfl
theorem mem_symSub_iff {M : EndV} : M ∈ symSub ↔ Mᵀ = M := Iff.rfl
theorem mem_tracelessSymSub_iff {M : EndV} :
    M ∈ tracelessSymSub ↔ Mᵀ = M ∧ M.trace = 0 := Iff.rfl

/-- Skew-symmetric matrices are traceless. -/
theorem skew_trace_zero {M : EndV} (hM : M ∈ skewSub) : M.trace = 0 := by
  have h : Mᵀ = -M := hM
  have h2 := congr_arg Matrix.trace h
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h2
  linarith

/-- A scalar matrix `c•1` with vanishing trace has `c = 0` (`3 ≠ 0` in `ℝ`). -/
theorem eq_zero_of_smul_one_trace_zero {c : ℝ} (h : (c • (1 : EndV)).trace = 0) : c = 0 := by
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · norm_num at h'

/-- **(a)** `End(V) = ℝ ⊕ V ⊕ W`: the three subspaces form an internal direct sum of
`End(V)`. -/
theorem endV_isInternal :
    DirectSum.IsInternal ![scalarSub, skewSub, tracelessSymSub] := by
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_fin_three]
    refine ⟨?_, ?_, ?_⟩
    · -- `Disjoint scalarSub (skewSub ⊔ tracelessSymSub)`: trace kills the scalar.
      change Disjoint scalarSub (skewSub ⊔ tracelessSymSub)
      rw [Submodule.disjoint_def]
      intro M hMs hMst
      rw [scalarSub, Submodule.mem_span_singleton] at hMs
      obtain ⟨c, rfl⟩ := hMs
      rw [Submodule.mem_sup] at hMst
      obtain ⟨y, hy, z, hz, hyz⟩ := hMst
      have htr : (c • (1 : EndV)).trace = 0 := by
        rw [← hyz, Matrix.trace_add, skew_trace_zero hy,
          (mem_tracelessSymSub_iff.mp hz).2, add_zero]
      rw [eq_zero_of_smul_one_trace_zero htr, zero_smul]
    · -- `Disjoint skewSub (tracelessSymSub ⊔ scalarSub)`: a symmetric skew matrix is `0`.
      change Disjoint skewSub (tracelessSymSub ⊔ scalarSub)
      rw [Submodule.disjoint_def]
      intro M hM hMts
      have hMskew : Mᵀ = -M := hM
      rw [Submodule.mem_sup] at hMts
      obtain ⟨z, hz, a, ha, hza⟩ := hMts
      have hsym : Mᵀ = M := by
        rw [← hza, Matrix.transpose_add, (mem_tracelessSymSub_iff.mp hz).1,
          mem_symSub_iff.mp (scalar_le_sym ha)]
      have hMM : M = -M := hsym.symm.trans hMskew
      have h2 : (2 : ℝ) • M = 0 := by rw [two_smul ℝ]; nth_rewrite 2 [hMM]; rw [add_neg_cancel]
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
    · -- `Disjoint tracelessSymSub (scalarSub ⊔ skewSub)`: symmetry kills the skew part,
      -- then trace kills the scalar.
      change Disjoint tracelessSymSub (scalarSub ⊔ skewSub)
      rw [Submodule.disjoint_def]
      intro M hM hMsk
      obtain ⟨hMsym, hMtr⟩ := mem_tracelessSymSub_iff.mp hM
      rw [Submodule.mem_sup] at hMsk
      obtain ⟨a, ha, y, hy, hay⟩ := hMsk
      have haa : aᵀ = a := mem_symSub_iff.mp (scalar_le_sym ha)
      have hya : yᵀ = -y := hy
      have hMt : Mᵀ = a - y := by
        rw [← hay, Matrix.transpose_add, haa, hya, sub_eq_add_neg]
      have key : a - y = a + y := by rw [← hMt, hMsym, hay]
      have hyy : -y = y := by
        rw [sub_eq_add_neg] at key; exact add_right_injective a key
      have hy0 : y = 0 := by
        have h2 : (2 : ℝ) • y = 0 := by rw [two_smul ℝ]; nth_rewrite 2 [← hyy]; rw [add_neg_cancel]
        exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
      have hMa : M = a := by rw [← hay, hy0, add_zero]
      rw [scalarSub, Submodule.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [hMa] at hMtr ⊢
      rw [eq_zero_of_smul_one_trace_zero hMtr, zero_smul]
  · -- `iSup = ⊤`: every matrix decomposes as scalar + skew + traceless-symmetric.
    rw [eq_top_iff]
    rintro M -
    have hdecomp : M ∈ scalarSub ⊔ skewSub ⊔ tracelessSymSub := by
      rw [Submodule.mem_sup]
      refine ⟨(M.trace / 3) • (1 : EndV) + (1 / 2 : ℝ) • (M - Mᵀ), ?_,
          (1 / 2 : ℝ) • (M + Mᵀ) - (M.trace / 3) • (1 : EndV), ?_, by module⟩
      · rw [Submodule.mem_sup]
        refine ⟨(M.trace / 3) • (1 : EndV), ?_, (1 / 2 : ℝ) • (M - Mᵀ), ?_, rfl⟩
        · rw [scalarSub]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        · rw [mem_skewSub_iff, Matrix.transpose_smul, Matrix.transpose_sub,
            Matrix.transpose_transpose]
          module
      · rw [mem_tracelessSymSub_iff]
        refine ⟨?_, ?_⟩
        · simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
            Matrix.transpose_transpose, Matrix.transpose_one]
          module
        · simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
            Matrix.trace_transpose, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat,
            smul_eq_mul]
          ring
    refine SetLike.le_def.mp ?_ hdecomp
    exact sup_le
      (sup_le (le_iSup ![scalarSub, skewSub, tracelessSymSub] 0)
        (le_iSup ![scalarSub, skewSub, tracelessSymSub] 1))
      (le_iSup ![scalarSub, skewSub, tracelessSymSub] 2)

/-- **(a)** `S²V = ℝ ⊕ W`: the symmetric matrices are the internal direct sum of the scalars
and the traceless symmetric matrices. -/
theorem symSub_eq_scalar_sup_tracelessSym :
    scalarSub ⊔ tracelessSymSub = symSub ∧ scalarSub ⊓ tracelessSymSub = ⊥ := by
  refine ⟨le_antisymm (sup_le scalar_le_sym tracelessSym_le_sym) ?_, ?_⟩
  · -- `symSub ≤ scalarSub ⊔ tracelessSymSub`: `M = (trace M/3)•1 + (M − (trace M/3)•1)`.
    intro M hM
    have hMsym : Mᵀ = M := hM
    rw [Submodule.mem_sup]
    refine ⟨(M.trace / 3) • (1 : EndV), ?_, M - (M.trace / 3) • (1 : EndV), ?_, by module⟩
    · rw [scalarSub]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [mem_tracelessSymSub_iff]
      refine ⟨?_, ?_⟩
      · rw [Matrix.transpose_sub, hMsym, Matrix.transpose_smul, Matrix.transpose_one]
      · simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
          Nat.cast_ofNat, smul_eq_mul]
        ring
  · -- `scalarSub ⊓ tracelessSymSub = ⊥`: a traceless scalar matrix is `0`.
    rw [Submodule.eq_bot_iff]
    intro M hM
    rw [Submodule.mem_inf] at hM
    obtain ⟨hs, htsym⟩ := hM
    rw [scalarSub, Submodule.mem_span_singleton] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [eq_zero_of_smul_one_trace_zero (mem_tracelessSymSub_iff.mp htsym).2, zero_smul]

theorem scalarSub_finrank : Module.finrank ℝ scalarSub = 1 := by
  rw [scalarSub, finrank_span_singleton (one_ne_zero)]

theorem skewSub_finrank : Module.finrank ℝ skewSub = 3 := by
  classical
  set v : Fin 3 → EndV :=
    ![!![0, 1, 0; -1, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; -1, 0, 0],
      !![0, 0, 0; 0, 0, 1; 0, -1, 0]] with hv
  have hindep : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e01 := congr_fun (congr_fun hg 0) 1
    have e02 := congr_fun (congr_fun hg 0) 2
    have e12 := congr_fun (congr_fun hg 1) 2
    simp [hv, Fin.sum_univ_three, Matrix.add_apply] at e01 e02 e12
    intro i; fin_cases i <;> simp_all
  have hspan : skewSub = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · intro M hM
      have hM' : Mᵀ = -M := hM
      have hd : ∀ i, M i i = 0 := fun i => by
        have h := congr_fun (congr_fun hM' i) i
        simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
      have ho : ∀ i j, M j i = -M i j := fun i j => by
        have h := congr_fun (congr_fun hM' i) j
        simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
      have key : M = M 0 1 • v 0 + M 0 2 • v 1 + M 1 2 • v 2 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hv, Matrix.add_apply] <;>
          linarith [hd 0, hd 1, hd 2, ho 0 1, ho 0 2, ho 1 2]
      rw [key]
      exact Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change (v i)ᵀ = -(v i)
      fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [hv]
  rw [hspan, finrank_span_eq_card hindep, Fintype.card_fin]

theorem tracelessSymSub_finrank : Module.finrank ℝ tracelessSymSub = 5 := by
  classical
  set v : Fin 5 → EndV :=
    ![!![0, 1, 0; 1, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 1, 0, 0],
      !![0, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, -1, 0; 0, 0, 0],
      !![0, 0, 0; 0, 1, 0; 0, 0, -1]] with hv
  have hindep : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e01 := congr_fun (congr_fun hg 0) 1
    have e02 := congr_fun (congr_fun hg 0) 2
    have e12 := congr_fun (congr_fun hg 1) 2
    have e00 := congr_fun (congr_fun hg 0) 0
    have e11 := congr_fun (congr_fun hg 1) 1
    simp [hv, Fin.sum_univ_five, Matrix.add_apply] at e01 e02 e12 e00 e11
    intro i; fin_cases i <;> simp_all
  have hspan : tracelessSymSub = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · intro M hM
      obtain ⟨hsym, htr⟩ := hM
      have hs : ∀ i j, M j i = M i j := fun i j => by
        have h := congr_fun (congr_fun hsym i) j
        simpa only [Matrix.transpose_apply] using h
      have htrace : M 2 2 = -M 0 0 - M 1 1 := by
        rw [Matrix.trace_fin_three] at htr; linarith
      have key : M = M 0 1 • v 0 + M 0 2 • v 1 + M 1 2 • v 2 + M 0 0 • v 3
          + (M 0 0 + M 1 1) • v 4 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hv, Matrix.add_apply] <;>
          linarith [hs 0 1, hs 0 2, hs 1 2, htrace]
      rw [key]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩)))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨?_, ?_⟩
      · show (v i)ᵀ = v i
        fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [hv]
      · show (v i).trace = 0
        fin_cases i <;> simp [hv, Matrix.trace_fin_three]
  rw [hspan, finrank_span_eq_card hindep, Fintype.card_fin]

/-! ### Part (b): irreducibility and Hooke's law -/

/-- **(b)** The standard representation `V ≅ skewSub` is irreducible: every `SO(3)`-invariant
subspace contained in `skewSub` is `⊥` or all of `skewSub`. (Irreducibility survives
complexification.) -/
theorem skewSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ skewSub)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) :
    U = ⊥ ∨ U = skewSub := by
  sorry

/-- **(b)** The representation `W = tracelessSymSub` is irreducible: every `SO(3)`-invariant
subspace contained in `tracelessSymSub` is `⊥` or all of `tracelessSymSub`. (Irreducibility
survives complexification.) -/
theorem tracelessSymSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ tracelessSymSub)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) :
    U = ⊥ ∨ U = tracelessSymSub := by
  sorry

/-- **(b), Hooke's law.** Any `SO(3)`-equivariant linear map `f : End(V) → End(V)` acts as a
scalar `K` (the compression modulus) on the trivial component `scalarSub` and a scalar `μ`
(the shearing modulus) on the `W`-component `tracelessSymSub`, and it maps symmetric matrices
to symmetric matrices (so the stress tensor `S_P = f(d_P)` is always symmetric). Thus for
`x ∈ ℝ`, `y ∈ W`, `f(x + y) = Kx + μy`. -/
theorem hooke_law (f : EndV →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (conjRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ,
      (∀ x ∈ scalarSub, f x = K • x) ∧
      (∀ y ∈ tracelessSymSub, f y = μ • y) ∧
      (∀ x ∈ symSub, f x ∈ symSub) := by
  sorry

end Etingof.Problem4_12_11
