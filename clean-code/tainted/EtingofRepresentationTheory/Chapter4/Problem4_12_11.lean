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
* `skewSub` = skew-symmetric matrices `Mᵀ = -M` (`3`-dimensional; the hat map `hatEquiv`
  identifies it with the standard representation `stdRep` on `ℝ³`, see
  `hatEquiv_equivariant`);
* `symSub` = symmetric matrices `Mᵀ = M` (this is `S²V`, `6`-dimensional);
* `tracelessSymSub` = traceless symmetric matrices (the `5`-dimensional representation `W`).

Results:

* **(a)** each subspace is `SO(3)`-invariant; `End(V) = scalarSub ⊕ skewSub ⊕ tracelessSymSub`
  and `symSub = scalarSub ⊕ tracelessSymSub`; the dimensions are `1, 3, 5`. The middle summand
  is the standard representation: the hat map gives an isomorphism
  `hatEquiv : ℝ³ ≃ₗ[ℝ] skewSub` intertwining `stdRep` with `skewRep` (`hatEquiv_equivariant`).
  The book identifies `S²V` with the symmetric matrices, so `symSub` needs no such
  identification, and `W` is only described as `5`-dimensional.
* **(b)** `skewSub` (`≅ V`) and `tracelessSymSub` (`= W`) are irreducible over `ℝ`
  (`skewSub_irreducible`, `tracelessSymSub_irreducible`), and "even after complexification":
  the complexified representations `skewSubc` (`= V ⊗ ℂ`) and `tracelessSymSubc` (`= W ⊗ ℂ`) on
  `EndVc = Matrix (Fin 3) (Fin 3) ℂ` are irreducible as well
  (`skewSub_irreducible_complexified`, `tracelessSymSub_irreducible_complexified`). Hooke's law:
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
orthogonal, `Aᵀ = A⁻¹`, so this is conjugation. -/
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

/-- The skew-symmetric matrices `{M | Mᵀ = -M}`, a `3`-dimensional subrepresentation. It is
isomorphic to the standard representation `V` via the hat map: see `hatEquiv_equivariant`. -/
def skewSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]; abel
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha, smul_neg]

/-- The symmetric matrices `{M | Mᵀ = M}`: this is `S²V ⊆ End(V)`. -/
def symSub : Submodule ℝ EndV where
  carrier := {M | Mᵀ = M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha]

/-- The traceless symmetric matrices `{M | Mᵀ = M ∧ trace M = 0}`, the `5`-dimensional
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

/-! ### The standard representation `V` and its identification with `skewSub` -/

/-- The standard `3`-dimensional representation of `SO(3)` on `V = ℝ³`, acting by
matrix-vector multiplication `A · v`. -/
def stdRep : Representation ℝ SO3 (Fin 3 → ℝ) where
  toFun A := Matrix.mulVecLin (A : EndV)
  map_one' := by rw [Submonoid.coe_one, Matrix.mulVecLin_one]; rfl
  map_mul' A B := by rw [Submonoid.coe_mul, Matrix.mulVecLin_mul]; rfl

@[simp]
theorem stdRep_apply (A : SO3) (v : Fin 3 → ℝ) : stdRep A v = (A : EndV) *ᵥ v := rfl

/-- The hat map `V → End(V)` sending `v` to the skew-symmetric matrix of the cross product
`w ↦ v × w`. -/
def hatMap : (Fin 3 → ℝ) →ₗ[ℝ] EndV where
  toFun v := !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0]
  map_add' u v := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c v := by ext i j; fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem hatMap_apply (v : Fin 3 → ℝ) :
    hatMap v = !![0, -v 2, v 1; v 2, 0, -v 0; -v 1, v 0, 0] := rfl

theorem hatMap_mem (v : Fin 3 → ℝ) : hatMap v ∈ skewSub := by
  change (hatMap v)ᵀ = -hatMap v
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The hat map transforms under an arbitrary `3 × 3` matrix by
`Aᵀ · hat(A · v) · A = det A • hat(v)`. This is a polynomial identity in the entries of `A`
and `v`; the determinant factor is what makes the equivariance below specific to `SO(3)`. -/
theorem transpose_mul_hatMap_mulVec (A : EndV) (v : Fin 3 → ℝ) :
    Aᵀ * hatMap (A *ᵥ v) * A = A.det • hatMap v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Matrix.det_fin_three] <;> ring

/-- Equivariance of the hat map: `hat(A · v) = A · hat(v) · Aᵀ` for `A ∈ SO(3)`. Both
`A · Aᵀ = 1` and `det A = 1` are used, the latter through
`transpose_mul_hatMap_mulVec`; over `O(3)` the identity acquires a factor of `det A`, which
is why the summand is the standard representation and not its twist by the determinant. -/
theorem hatMap_mulVec (A : SO3) (v : Fin 3 → ℝ) :
    hatMap ((A : EndV) *ᵥ v) = conjRep A (hatMap v) := by
  have hdet : (A : EndV).det = 1 := (mem_specialOrthogonalGroup_iff.mp A.2).2
  have hAAt : (A : EndV) * (A : EndV)ᵀ = 1 := by
    simpa [star_coe_eq_transpose] using coe_mul_star A
  have key := transpose_mul_hatMap_mulVec (A : EndV) v
  rw [hdet, one_smul] at key
  calc hatMap ((A : EndV) *ᵥ v)
      = (A : EndV) * (A : EndV)ᵀ * hatMap ((A : EndV) *ᵥ v) * ((A : EndV) * (A : EndV)ᵀ) := by
        rw [hAAt, one_mul, mul_one]
    _ = (A : EndV) * ((A : EndV)ᵀ * hatMap ((A : EndV) *ᵥ v) * (A : EndV)) * (A : EndV)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (A : EndV) * hatMap v * (A : EndV)ᵀ := by rw [key]
    _ = conjRep A (hatMap v) := by rw [conjRep_apply, star_coe_eq_transpose]

/-- The inverse of the hat map, reading off the three independent entries of a
skew-symmetric matrix. -/
def unhat : EndV →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun M := ![M 2 1, M 0 2, M 1 0]
  map_add' M N := by ext i; fin_cases i <;> simp
  map_smul' c M := by ext i; fin_cases i <;> simp

@[simp]
theorem unhat_apply (M : EndV) : unhat M = ![M 2 1, M 0 2, M 1 0] := rfl

@[simp]
theorem unhat_hatMap (v : Fin 3 → ℝ) : unhat (hatMap v) = v := by
  ext i; fin_cases i <;> simp

theorem hatMap_unhat {M : EndV} (hM : M ∈ skewSub) : hatMap (unhat M) = M := by
  have hM' : Mᵀ = -M := hM
  have hd : ∀ i, M i i = 0 := fun i => by
    have h := congr_fun (congr_fun hM' i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  have ho : ∀ i j, M j i = -M i j := fun i j => by
    have h := congr_fun (congr_fun hM' i) j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    linarith [hd 0, hd 1, hd 2, ho 0 1, ho 0 2, ho 1 2]

/-- The subrepresentation of `conjRep` carried by the skew-symmetric matrices. -/
def skewRep : Representation ℝ SO3 skewSub where
  toFun A := (conjRep A).restrict
    (fun M hM => conjRep_invariant skewSub (Or.inr (Or.inl rfl)) A M hM)
  map_one' := by ext M; simp
  map_mul' A B := by ext M; simp

@[simp]
theorem skewRep_coe_apply (A : SO3) (M : skewSub) :
    (skewRep A M : EndV) = conjRep A (M : EndV) := rfl

/-- The hat map as a linear isomorphism `V ≃ skewSub`. -/
def hatEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] skewSub where
  toFun v := ⟨hatMap v, hatMap_mem v⟩
  map_add' u v := by ext : 1; exact hatMap.map_add u v
  map_smul' c v := by ext : 1; exact hatMap.map_smul c v
  invFun M := unhat (M : EndV)
  left_inv v := unhat_hatMap v
  right_inv M := by ext : 1; exact hatMap_unhat M.2

@[simp]
theorem hatEquiv_coe_apply (v : Fin 3 → ℝ) : (hatEquiv v : EndV) = hatMap v := rfl

/-- **(a)** The `3`-dimensional summand of `End(V)` is the standard representation: `hatEquiv`
is an isomorphism `V ≃ skewSub` intertwining `stdRep` with `skewRep`. -/
theorem hatEquiv_equivariant (A : SO3) (v : Fin 3 → ℝ) :
    hatEquiv (stdRep A v) = skewRep A (hatEquiv v) := by
  ext : 1
  rw [hatEquiv_coe_apply, skewRep_coe_apply, hatEquiv_coe_apply, stdRep_apply, hatMap_mulVec]

/-! ### Rotation matrices used for the irreducibility arguments -/

/-- The explicit basis of `skewSub` (as in `skewSub_finrank`). -/
def sbasis : Fin 3 → EndV :=
  ![!![0, 1, 0; -1, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, -1, 0]]

theorem sbasis_mem (i : Fin 3) : sbasis i ∈ skewSub := by
  fin_cases i <;> · change (_ : EndV)ᵀ = -_; ext a b; fin_cases a <;> fin_cases b <;> simp [sbasis]

/-- Every skew-symmetric matrix is a combination of the three basis matrices. -/
theorem skew_decomp (M : EndV) (hM : Mᵀ = -M) :
    M = (M 0 1) • sbasis 0 + (M 0 2) • sbasis 1 + (M 1 2) • sbasis 2 := by
  have hd : ∀ i, M i i = 0 := fun i => by
    have h := congr_fun (congr_fun hM i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linarith
  have ho : ∀ i j, M j i = -M i j := fun i j => by
    have h := congr_fun (congr_fun hM i) j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbasis, Matrix.add_apply] <;>
    linarith [hd 0, hd 1, hd 2, ho 0 1, ho 0 2, ho 1 2]

/-- Sign rotation `diag(-1,-1,1) ∈ SO(3)`. -/
def Dz : SO3 := ⟨!![(-1:ℝ), 0, 0; 0, -1, 0; 0, 0, 1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩

/-- Sign rotation `diag(-1,1,-1) ∈ SO(3)`. -/
def Dy : SO3 := ⟨!![(-1:ℝ), 0, 0; 0, 1, 0; 0, 0, -1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩

/-- Sign rotation `diag(1,-1,-1) ∈ SO(3)`. -/
def Dx : SO3 := ⟨!![(1:ℝ), 0, 0; 0, -1, 0; 0, 0, -1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩

/-- Cyclic-permutation rotation `e₀ ↦ e₁ ↦ e₂ ↦ e₀ ∈ SO(3)`. -/
def Pc : SO3 := ⟨!![(0:ℝ), 0, 1; 1, 0, 0; 0, 1, 0], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · simp [Matrix.det_fin_three]⟩

/-- Uniform tactic for `conjRep R (sbasis i) = ±sbasis j` computations. -/
private theorem conjRep_Dz0 : conjRep Dz (sbasis 0) = sbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz1 : conjRep Dz (sbasis 1) = -sbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz2 : conjRep Dz (sbasis 2) = -sbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy0 : conjRep Dy (sbasis 0) = -sbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy1 : conjRep Dy (sbasis 1) = sbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy2 : conjRep Dy (sbasis 2) = -sbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx0 : conjRep Dx (sbasis 0) = -sbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx1 : conjRep Dx (sbasis 1) = -sbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx2 : conjRep Dx (sbasis 2) = sbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc0 : conjRep Pc (sbasis 0) = sbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc1 : conjRep Pc (sbasis 1) = -sbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, sbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc2 : conjRep Pc (sbasis 2) = -sbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, sbasis, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Basis and rotations for the `5`-dimensional representation `W` -/

/-- The explicit basis of `tracelessSymSub` (as in `tracelessSymSub_finrank`):
`w0 = E01+E10`, `w1 = E02+E20`, `w2 = E12+E21`, `w3 = diag(1,-1,0)`, `w4 = diag(0,1,-1)`. -/
def wbasis : Fin 5 → EndV :=
  ![!![0, 1, 0; 1, 0, 0; 0, 0, 0], !![0, 0, 1; 0, 0, 0; 1, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, -1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, 0; 0, 0, -1]]

theorem wbasis_mem (i : Fin 5) : wbasis i ∈ tracelessSymSub := by
  rw [mem_tracelessSymSub_iff]
  refine ⟨?_, ?_⟩
  · fin_cases i <;> · ext a b; fin_cases a <;> fin_cases b <;> simp [wbasis]
  · fin_cases i <;> simp [wbasis, Matrix.trace_fin_three]

/-- Every traceless symmetric matrix is the combination of the five basis matrices given by
its independent entries. -/
theorem traceless_sym_decomp (M : EndV) (hsym : Mᵀ = M) (htr : M.trace = 0) :
    M = M 0 1 • wbasis 0 + M 0 2 • wbasis 1 + M 1 2 • wbasis 2 + M 0 0 • wbasis 3
      + (M 0 0 + M 1 1) • wbasis 4 := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have h := congr_fun (congr_fun hsym i) j
    simpa only [Matrix.transpose_apply] using h
  have htrace : M 2 2 = -M 0 0 - M 1 1 := by
    rw [Matrix.trace_fin_three] at htr; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wbasis, Matrix.add_apply] <;>
    linarith [hs 0 1, hs 0 2, hs 1 2, htrace]

/-- `√2 / 2 = cos 45° = sin 45°`. -/
noncomputable def c45 : ℝ := Real.sqrt 2 / 2

theorem c45_sq : c45 * c45 = 1 / 2 := by
  rw [c45, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- Rotation by `45°` about the `z`-axis, in `SO(3)`. -/
def Rz45 : SO3 := ⟨!![c45, -c45, 0; c45, c45, 0; 0, 0, 1], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [c45_sq]
  · simp [Matrix.det_fin_three]
    nlinarith [c45_sq]⟩

/-- Rotation by `45°` about the `y`-axis, in `SO(3)`. -/
def Ry45 : SO3 := ⟨!![c45, 0, c45; 0, 1, 0; -c45, 0, c45], by
  rw [mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith [c45_sq]
  · simp [Matrix.det_fin_three]
    nlinarith [c45_sq]⟩

/-- The `45°`-about-`z` rotation converts the off-diagonal basis vector `w0` into `-w3`. -/
theorem conjRep_Rz45_w0 : conjRep Rz45 (wbasis 0) = -wbasis 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Rz45, wbasis, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.neg_apply] <;> nlinarith [c45_sq]

/-- `Rz45` rotates the first diagonal vector `w3` onto the off-diagonal vector `w0`. -/
private theorem conjRep_Rz45_w3 : conjRep Rz45 (wbasis 3) = wbasis 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Rz45, wbasis, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [c45_sq]

/-- `Rz45` acting on the second diagonal vector `w4`. -/
private theorem conjRep_Rz45_w4 :
    conjRep Rz45 (wbasis 4)
      = (-2⁻¹ : ℝ) • wbasis 0 + (2⁻¹ : ℝ) • wbasis 3 + wbasis 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Rz45, wbasis, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply] <;>
    nlinarith [c45_sq]

/-- `Ry45` acting on the first diagonal vector `w3`. -/
private theorem conjRep_Ry45_w3 :
    conjRep Ry45 (wbasis 3)
      = (-2⁻¹ : ℝ) • wbasis 1 + (2⁻¹ : ℝ) • wbasis 3 + (-2⁻¹ : ℝ) • wbasis 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Ry45, wbasis, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply] <;>
    nlinarith [c45_sq]

/-- `Ry45` acting on the second diagonal vector `w4`. -/
private theorem conjRep_Ry45_w4 :
    conjRep Ry45 (wbasis 4)
      = (-2⁻¹ : ℝ) • wbasis 1 + (-2⁻¹ : ℝ) • wbasis 3 + (2⁻¹ : ℝ) • wbasis 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Ry45, wbasis, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.add_apply] <;>
    nlinarith [c45_sq]

/-- The cyclic rotation permutes the off-diagonal basis vectors `w0 ↦ w2 ↦ w1 ↦ w0`. -/
private theorem conjRep_Pc_w0 : conjRep Pc (wbasis 0) = wbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc_w1 : conjRep Pc (wbasis 1) = wbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc_w2 : conjRep Pc (wbasis 2) = wbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Pc_w3 : conjRep Pc (wbasis 3) = wbasis 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Pc, wbasis, Matrix.mul_apply, Fin.sum_univ_three]

/-- The action of the three sign rotations on the five basis vectors of `W`. The characters
of `w0, w1, w2` under `(Dx, Dy, Dz)` are `(-1,-1,1)`, `(-1,1,-1)`, `(1,-1,-1)`; the diagonal
vectors `w3, w4` are fixed. -/
private theorem conjRep_Dx_w0 : conjRep Dx (wbasis 0) = -wbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w1 : conjRep Dx (wbasis 1) = -wbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w2 : conjRep Dx (wbasis 2) = wbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w3 : conjRep Dx (wbasis 3) = wbasis 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dx_w4 : conjRep Dx (wbasis 4) = wbasis 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dx, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w0 : conjRep Dy (wbasis 0) = -wbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w1 : conjRep Dy (wbasis 1) = wbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w2 : conjRep Dy (wbasis 2) = -wbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w3 : conjRep Dy (wbasis 3) = wbasis 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dy_w4 : conjRep Dy (wbasis 4) = wbasis 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dy, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w0 : conjRep Dz (wbasis 0) = wbasis 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w1 : conjRep Dz (wbasis 1) = -wbasis 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w2 : conjRep Dz (wbasis 2) = -wbasis 2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w3 : conjRep Dz (wbasis 3) = wbasis 3 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, wbasis, Matrix.mul_apply, Fin.sum_univ_three]
private theorem conjRep_Dz_w4 : conjRep Dz (wbasis 4) = wbasis 4 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conjRep_apply, Dz, wbasis, Matrix.mul_apply, Fin.sum_univ_three]

/-! ### Part (b): irreducibility and Hooke's law -/

/-- **(b)** The standard representation, realized as `skewSub` by `hatEquiv_equivariant`, is
irreducible: every `SO(3)`-invariant subspace contained in `skewSub` is `⊥` or all of
`skewSub`. Irreducibility survives complexification: see
`skewSub_irreducible_complexified`. -/
theorem skewSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ skewSub)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) :
    U = ⊥ ∨ U = skewSub := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)
  -- Pick a nonzero `M ∈ U`; it is skew, so `M = a·v₀ + b·v₁ + c·v₂`.
  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  have hMsk : Mᵀ = -M := mem_skewSub_iff.mp (hUle hMU)
  have hMdec : M = (M 0 1) • sbasis 0 + (M 0 2) • sbasis 1 + (M 1 2) • sbasis 2 :=
    skew_decomp M hMsk
  have hDzM : conjRep Dz M ∈ U := hUinv Dz M hMU
  have hDyM : conjRep Dy M ∈ U := hUinv Dy M hMU
  have hDxM : conjRep Dx M ∈ U := hUinv Dx M hMU
  -- Each sign rotation isolates one coordinate axis.
  have hav0 : (M 0 1) • sbasis 0 ∈ U := by
    have key : (M 0 1) • sbasis 0 = (2⁻¹ : ℝ) • (M + conjRep Dz M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRep_Dz0, conjRep_Dz1, conjRep_Dz2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDzM)
  have hbv1 : (M 0 2) • sbasis 1 ∈ U := by
    have key : (M 0 2) • sbasis 1 = (2⁻¹ : ℝ) • (M + conjRep Dy M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRep_Dy0, conjRep_Dy1, conjRep_Dy2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDyM)
  have hcv2 : (M 1 2) • sbasis 2 ∈ U := by
    have key : (M 1 2) • sbasis 2 = (2⁻¹ : ℝ) • (M + conjRep Dx M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRep_Dx0, conjRep_Dx1, conjRep_Dx2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDxM)
  -- Spread each coordinate across all three axes with the cyclic rotation.
  have hav2 : (M 0 1) • sbasis 2 ∈ U := by
    have t := hUinv Pc _ hav0; rwa [map_smul, conjRep_Pc0] at t
  have hav1 : (M 0 1) • sbasis 1 ∈ U := by
    have t := hUinv Pc _ hav2; rw [map_smul, conjRep_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv0 : (M 0 2) • sbasis 0 ∈ U := by
    have t := hUinv Pc _ hbv1; rw [map_smul, conjRep_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv2 : (M 0 2) • sbasis 2 ∈ U := by
    have t := hUinv Pc _ hbv0; rwa [map_smul, conjRep_Pc0] at t
  have hcv1 : (M 1 2) • sbasis 1 ∈ U := by
    have t := hUinv Pc _ hcv2; rw [map_smul, conjRep_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hcv0 : (M 1 2) • sbasis 0 ∈ U := by
    have t := hUinv Pc _ hcv1; rw [map_smul, conjRep_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  -- `M ≠ 0` gives a nonzero coordinate, so each basis vector lies in `U`.
  have hne3 : M 0 1 ≠ 0 ∨ M 0 2 ≠ 0 ∨ M 1 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMne (by rw [hMdec, hcon.1, hcon.2.1, hcon.2.2]; simp)
  have extract : ∀ w : EndV,
      (M 0 1) • w ∈ U → (M 0 2) • w ∈ U → (M 1 2) • w ∈ U → w ∈ U := by
    intro w h1 h2 h3
    rcases hne3 with hh | hh | hh
    · rw [← one_smul ℝ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h1
    · rw [← one_smul ℝ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h2
    · rw [← one_smul ℝ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h3
  have hs0 : sbasis 0 ∈ U := extract _ hav0 hbv0 hcv0
  have hs1 : sbasis 1 ∈ U := extract _ hav1 hbv1 hcv1
  have hs2 : sbasis 2 ∈ U := extract _ hav2 hbv2 hcv2
  -- Hence `skewSub ≤ U`.
  intro N hN
  rw [skew_decomp N (mem_skewSub_iff.mp hN)]
  exact U.add_mem (U.add_mem (U.smul_mem _ hs0) (U.smul_mem _ hs1)) (U.smul_mem _ hs2)

/-- **(b)** The representation `W = tracelessSymSub` is irreducible: every `SO(3)`-invariant
subspace contained in `tracelessSymSub` is `⊥` or all of `tracelessSymSub`. Irreducibility
survives complexification: see `tracelessSymSub_irreducible_complexified`. -/
theorem tracelessSymSub_irreducible (U : Submodule ℝ EndV) (hUle : U ≤ tracelessSymSub)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) :
    U = ⊥ ∨ U = tracelessSymSub := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)
  -- Every element of `U` is symmetric (being in `tracelessSymSub`).
  have hUsym : ∀ N ∈ U, Nᵀ = N := fun N hN => (mem_tracelessSymSub_iff.mp (hUle hN)).1
  -- V4 sign-averaging projections onto the three off-diagonal basis vectors.
  have projA : ∀ N ∈ U, (N 0 1) • wbasis 0 ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := mem_tracelessSymSub_iff.mp (hUle hN)
    have key : (N 0 1) • wbasis 0
        = (4⁻¹ : ℝ) • (N - conjRep Dx N - conjRep Dy N + conjRep Dz N) := by
      conv_rhs => rw [traceless_sym_decomp N hsym htr]
      simp only [map_add, map_smul, conjRep_Dx_w0, conjRep_Dx_w1, conjRep_Dx_w2, conjRep_Dx_w3,
        conjRep_Dx_w4, conjRep_Dy_w0, conjRep_Dy_w1, conjRep_Dy_w2, conjRep_Dy_w3, conjRep_Dy_w4,
        conjRep_Dz_w0, conjRep_Dz_w1, conjRep_Dz_w2, conjRep_Dz_w3, conjRep_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.add_mem (U.sub_mem (U.sub_mem hN (hUinv Dx N hN))
      (hUinv Dy N hN)) (hUinv Dz N hN))
  have projB : ∀ N ∈ U, (N 0 2) • wbasis 1 ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := mem_tracelessSymSub_iff.mp (hUle hN)
    have key : (N 0 2) • wbasis 1
        = (4⁻¹ : ℝ) • (N - conjRep Dx N + conjRep Dy N - conjRep Dz N) := by
      conv_rhs => rw [traceless_sym_decomp N hsym htr]
      simp only [map_add, map_smul, conjRep_Dx_w0, conjRep_Dx_w1, conjRep_Dx_w2, conjRep_Dx_w3,
        conjRep_Dx_w4, conjRep_Dy_w0, conjRep_Dy_w1, conjRep_Dy_w2, conjRep_Dy_w3, conjRep_Dy_w4,
        conjRep_Dz_w0, conjRep_Dz_w1, conjRep_Dz_w2, conjRep_Dz_w3, conjRep_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.add_mem (U.sub_mem hN (hUinv Dx N hN))
      (hUinv Dy N hN)) (hUinv Dz N hN))
  have projC : ∀ N ∈ U, (N 1 2) • wbasis 2 ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := mem_tracelessSymSub_iff.mp (hUle hN)
    have key : (N 1 2) • wbasis 2
        = (4⁻¹ : ℝ) • (N + conjRep Dx N - conjRep Dy N - conjRep Dz N) := by
      conv_rhs => rw [traceless_sym_decomp N hsym htr]
      simp only [map_add, map_smul, conjRep_Dx_w0, conjRep_Dx_w1, conjRep_Dx_w2, conjRep_Dx_w3,
        conjRep_Dx_w4, conjRep_Dy_w0, conjRep_Dy_w1, conjRep_Dy_w2, conjRep_Dy_w3, conjRep_Dy_w4,
        conjRep_Dz_w0, conjRep_Dz_w1, conjRep_Dz_w2, conjRep_Dz_w3, conjRep_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.sub_mem (U.add_mem hN (hUinv Dx N hN))
      (hUinv Dy N hN)) (hUinv Dz N hN))
  -- Once `wbasis 0 ∈ U`, the cyclic and `45°` rotations spread it over all five basis vectors.
  have hbootstrap : wbasis 0 ∈ U → tracelessSymSub ≤ U := by
    intro hw0
    have hw2 : wbasis 2 ∈ U := by
      have t := hUinv Pc _ hw0; rwa [conjRep_Pc_w0] at t
    have hw1 : wbasis 1 ∈ U := by
      have t := hUinv Pc _ hw2; rwa [conjRep_Pc_w2] at t
    have hw3 : wbasis 3 ∈ U := by
      have t := hUinv Rz45 _ hw0; rw [conjRep_Rz45_w0] at t
      exact (Submodule.neg_mem_iff U).mp t
    have hw4 : wbasis 4 ∈ U := by
      have t := hUinv Pc _ hw3; rwa [conjRep_Pc_w3] at t
    intro N hN
    obtain ⟨hNsym, hNtr⟩ := mem_tracelessSymSub_iff.mp hN
    rw [traceless_sym_decomp N hNsym hNtr]
    exact U.add_mem (U.add_mem (U.add_mem (U.add_mem
      (U.smul_mem _ hw0) (U.smul_mem _ hw1)) (U.smul_mem _ hw2))
      (U.smul_mem _ hw3)) (U.smul_mem _ hw4)
  -- A nonzero coefficient lets us cancel a scalar.
  have smul_extract : ∀ {c : ℝ} {w : EndV}, c ≠ 0 → c • w ∈ U → w ∈ U := by
    intro c w hc hcw
    rw [← one_smul ℝ w, ← inv_mul_cancel₀ hc, mul_smul]; exact U.smul_mem _ hcw
  -- Rotate any off-diagonal basis vector to `w0`.
  have w1_to_w0 : wbasis 1 ∈ U → wbasis 0 ∈ U := fun hw1 => by
    have t := hUinv Pc _ hw1; rwa [conjRep_Pc_w1] at t
  have w2_to_w0 : wbasis 2 ∈ U → wbasis 0 ∈ U := fun hw2 => by
    have t := hUinv Pc _ hw2; rw [conjRep_Pc_w2] at t; exact w1_to_w0 t
  -- Pick a nonzero `M ∈ U`.
  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  obtain ⟨hMsym, hMtr⟩ := mem_tracelessSymSub_iff.mp (hUle hMU)
  rcases eq_or_ne (M 0 1) 0 with h01 | h01
  · rcases eq_or_ne (M 0 2) 0 with h02 | h02
    · rcases eq_or_ne (M 1 2) 0 with h12 | h12
      · -- Purely diagonal case: `M` is diagonal traceless nonzero.
        -- `M` reduces to its two diagonal basis components; name them `a, b`.
        have hMdec : M = M 0 0 • wbasis 3 + (M 0 0 + M 1 1) • wbasis 4 := by
          have hd := traceless_sym_decomp M hMsym hMtr
          rw [h01, h02, h12] at hd
          simpa only [zero_smul, zero_add] using hd
        set a := M 0 0 with ha
        set b := M 1 1 with hb
        rcases eq_or_ne a b with hab | hab
        · -- `a = b`, so `a ≠ 0` (else `M = 0`); `Ry45` produces a nonzero off-diagonal.
          have hM00 : a ≠ 0 := by
            intro hz
            have hb0 : b = 0 := by rw [← hab]; exact hz
            apply hMne
            conv_lhs => rw [hMdec]
            rw [hz, hb0]; simp
          have hform : conjRep Ry45 M
              = (-(2 * a + b) / 2) • wbasis 1 + (-b / 2) • wbasis 3 + (b / 2) • wbasis 4 := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRep_Ry45_w3, conjRep_Ry45_w4]
            module
          have hentry : (conjRep Ry45 M) 0 2 = -(2 * a + b) / 2 := by
            rw [hform]; simp [wbasis, Matrix.add_apply]
          have hne : 2 * a + b ≠ 0 := by rw [← hab]; intro hc; exact hM00 (by linarith)
          have hcoef : (conjRep Ry45 M) 0 2 ≠ 0 := by
            rw [hentry, neg_div]; exact neg_ne_zero.mpr (div_ne_zero hne (by norm_num))
          exact hbootstrap (w1_to_w0 (smul_extract hcoef (projB _ (hUinv Ry45 M hMU))))
        · -- `a ≠ b`: `Rz45` produces a nonzero off-diagonal `w0`-component.
          have hform : conjRep Rz45 M
              = ((a - b) / 2) • wbasis 0 + ((a + b) / 2) • wbasis 3 + (a + b) • wbasis 4 := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRep_Rz45_w3, conjRep_Rz45_w4]
            module
          have hentry : (conjRep Rz45 M) 0 1 = (a - b) / 2 := by
            rw [hform]; simp [wbasis, Matrix.add_apply]
          have hcoef : (conjRep Rz45 M) 0 1 ≠ 0 :=
            hentry ▸ div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
          exact hbootstrap (smul_extract hcoef (projA _ (hUinv Rz45 M hMU)))
      · -- `M 1 2 ≠ 0`: extract `w2`, rotate to `w0`.
        exact hbootstrap (w2_to_w0 (smul_extract h12 (projC M hMU)))
    · -- `M 0 2 ≠ 0`: extract `w1`, rotate to `w0`.
      exact hbootstrap (w1_to_w0 (smul_extract h02 (projB M hMU)))
  · -- `M 0 1 ≠ 0`: extract `w0` directly.
    exact hbootstrap (smul_extract h01 (projA M hMU))

/-! ### Part (b), complexification: `V ⊗ ℂ` and `W ⊗ ℂ` remain irreducible

The book asks for irreducibility of `V` and `W` **"even after complexification"**. We model the
complexified representations concretely on `EndVc = Matrix (Fin 3) (Fin 3) ℂ`, with `SO(3)`
(real matrices) acting by the same conjugation `M ↦ cx A · M · (cx A)ᵀ`, where `cx` is the
entrywise inclusion `ℝ → ℂ`. The complexified standard representation `V ⊗ ℂ` is `skewSubc`
(complex skew matrices) and the complexified `W ⊗ ℂ` is `tracelessSymSubc` (complex traceless
symmetric matrices).

Real irreducibility does **not** formally imply complex irreducibility in general (that upgrade
is exactly the statement that `V`, `W` are of *real type*). But the combinatorial
sign-averaging/rotation argument of `skewSub_irreducible` / `tracelessSymSub_irreducible` uses
only group elements with real (in fact rational or `√2`-valued) entries together with linear
combinations, so it runs verbatim over `ℂ`. The pointwise action facts are transported from
their real counterparts through the ring homomorphism `cx`. -/

/-- `End(V) ⊗ ℂ = Matrix (Fin 3) (Fin 3) ℂ`. -/
abbrev EndVc : Type := Matrix (Fin 3) (Fin 3) ℂ

/-- Entrywise inclusion `ℝ → ℂ` of `3 × 3` matrices, as a ring homomorphism. -/
def cx : EndV →+* EndVc := (algebraMap ℝ ℂ).mapMatrix

@[simp] theorem cx_apply (M : EndV) (i j : Fin 3) : cx M i j = ((M i j : ℝ) : ℂ) := rfl

/-- `cx` commutes with transpose. -/
theorem cx_transpose (M : EndV) : cx Mᵀ = (cx M)ᵀ := by
  ext i j; simp [Matrix.transpose_apply]

/-- `cx` intertwines the real and complex conjugation actions:
`cx (conjRep A M) = conjRepc A (cx M)`. -/
def conjRepc : Representation ℂ SO3 EndVc where
  toFun A := (LinearMap.mulLeft ℂ (cx (A : EndV))).comp
    (LinearMap.mulRight ℂ ((cx (A : EndV))ᵀ))
  map_one' := by
    ext M
    simp
  map_mul' A B := by
    ext M
    simp only [Submonoid.coe_mul, map_mul, Matrix.transpose_mul, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Module.End.mul_apply]
    simp [mul_assoc]

@[simp]
theorem conjRepc_apply (A : SO3) (M : EndVc) :
    conjRepc A M = cx (A : EndV) * M * (cx (A : EndV))ᵀ := by
  simp [conjRepc, mul_assoc]

/-- The transport identity: `cx` intertwines the real and complexified actions. -/
theorem cx_conjRep (A : SO3) (M : EndV) : cx (conjRep A M) = conjRepc A (cx M) := by
  rw [conjRep_apply, conjRepc_apply, star_coe_eq_transpose, map_mul, map_mul, cx_transpose]

/-- The complexified standard representation `V ⊗ ℂ`: complex skew-symmetric matrices. -/
def skewSubc : Submodule ℂ EndVc where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢; rw [transpose_add, ha, hb]; abel
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢; rw [transpose_smul, ha, smul_neg]

/-- The complexified representation `W ⊗ ℂ`: complex traceless symmetric matrices. -/
def tracelessSymSubc : Submodule ℂ EndVc where
  carrier := {M | Mᵀ = M ∧ M.trace = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    exact ⟨by rw [transpose_add, ha.1, hb.1], by rw [trace_add, ha.2, hb.2, add_zero]⟩
  zero_mem' := by simp only [Set.mem_setOf_eq]; exact ⟨by simp, by simp⟩
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    exact ⟨by rw [transpose_smul, ha.1], by rw [trace_smul, ha.2, smul_zero]⟩

theorem mem_skewSubc_iff {M : EndVc} : M ∈ skewSubc ↔ Mᵀ = -M := Iff.rfl
theorem mem_tracelessSymSubc_iff {M : EndVc} :
    M ∈ tracelessSymSubc ↔ Mᵀ = M ∧ M.trace = 0 := Iff.rfl

/-- `cx` sends a real scalar multiple to the corresponding complex scalar multiple. -/
theorem cx_smul (r : ℝ) (N : EndV) : cx (r • N) = (r : ℂ) • cx N := by
  ext i j; simp [Matrix.smul_apply, Complex.ofReal_mul]

/-! #### Complex decomposition lemmas -/

/-- Every complex skew-symmetric matrix is a combination of the (complexified) basis matrices. -/
theorem skew_decompc (M : EndVc) (hM : Mᵀ = -M) :
    M = M 0 1 • cx (sbasis 0) + M 0 2 • cx (sbasis 1) + M 1 2 • cx (sbasis 2) := by
  have hd : ∀ i, M i i = 0 := fun i => by
    have h := congr_fun (congr_fun hM i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h; linear_combination (2⁻¹ : ℂ) * h
  have ho : ∀ i j, M j i = -M i j := fun i j => by
    have h := congr_fun (congr_fun hM i) j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbasis, Matrix.add_apply] <;>
    (first | rfl | exact hd 0 | exact hd 1 | exact hd 2 |
      exact ho 0 1 | exact ho 0 2 | exact ho 1 2)

/-- Every complex traceless symmetric matrix is the combination of the five basis matrices. -/
theorem traceless_sym_decompc (M : EndVc) (hsym : Mᵀ = M) (htr : M.trace = 0) :
    M = M 0 1 • cx (wbasis 0) + M 0 2 • cx (wbasis 1) + M 1 2 • cx (wbasis 2) + M 0 0 • cx (wbasis 3)
      + (M 0 0 + M 1 1) • cx (wbasis 4) := by
  have hs : ∀ i j, M j i = M i j := fun i j => by
    have h := congr_fun (congr_fun hsym i) j
    simpa only [Matrix.transpose_apply] using h
  have htrace : M 2 2 = -M 1 1 - M 0 0 := by
    rw [Matrix.trace_fin_three] at htr; linear_combination htr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wbasis, Matrix.add_apply] <;>
    (first | rfl | exact hs 0 1 | exact hs 0 2 | exact hs 1 2 | exact htrace)

/-! #### Transported pointwise action facts

Each `conjRepc R (cx w) = ± cx w'` follows from its real counterpart `conjRep R w = ± w'` by
applying the ring homomorphism `cx` and the transport identity `cx_conjRep`. -/

private theorem conjRepc_Dz0 : conjRepc Dz (cx (sbasis 0)) = cx (sbasis 0) := by
  rw [← cx_conjRep, conjRep_Dz0]
private theorem conjRepc_Dz1 : conjRepc Dz (cx (sbasis 1)) = -cx (sbasis 1) := by
  rw [← cx_conjRep, conjRep_Dz1, map_neg]
private theorem conjRepc_Dz2 : conjRepc Dz (cx (sbasis 2)) = -cx (sbasis 2) := by
  rw [← cx_conjRep, conjRep_Dz2, map_neg]
private theorem conjRepc_Dy0 : conjRepc Dy (cx (sbasis 0)) = -cx (sbasis 0) := by
  rw [← cx_conjRep, conjRep_Dy0, map_neg]
private theorem conjRepc_Dy1 : conjRepc Dy (cx (sbasis 1)) = cx (sbasis 1) := by
  rw [← cx_conjRep, conjRep_Dy1]
private theorem conjRepc_Dy2 : conjRepc Dy (cx (sbasis 2)) = -cx (sbasis 2) := by
  rw [← cx_conjRep, conjRep_Dy2, map_neg]
private theorem conjRepc_Dx0 : conjRepc Dx (cx (sbasis 0)) = -cx (sbasis 0) := by
  rw [← cx_conjRep, conjRep_Dx0, map_neg]
private theorem conjRepc_Dx1 : conjRepc Dx (cx (sbasis 1)) = -cx (sbasis 1) := by
  rw [← cx_conjRep, conjRep_Dx1, map_neg]
private theorem conjRepc_Dx2 : conjRepc Dx (cx (sbasis 2)) = cx (sbasis 2) := by
  rw [← cx_conjRep, conjRep_Dx2]
private theorem conjRepc_Pc0 : conjRepc Pc (cx (sbasis 0)) = cx (sbasis 2) := by
  rw [← cx_conjRep, conjRep_Pc0]
private theorem conjRepc_Pc1 : conjRepc Pc (cx (sbasis 1)) = -cx (sbasis 0) := by
  rw [← cx_conjRep, conjRep_Pc1, map_neg]
private theorem conjRepc_Pc2 : conjRepc Pc (cx (sbasis 2)) = -cx (sbasis 1) := by
  rw [← cx_conjRep, conjRep_Pc2, map_neg]

private theorem conjRepc_Pc_w0 : conjRepc Pc (cx (wbasis 0)) = cx (wbasis 2) := by
  rw [← cx_conjRep, conjRep_Pc_w0]
private theorem conjRepc_Pc_w1 : conjRepc Pc (cx (wbasis 1)) = cx (wbasis 0) := by
  rw [← cx_conjRep, conjRep_Pc_w1]
private theorem conjRepc_Pc_w2 : conjRepc Pc (cx (wbasis 2)) = cx (wbasis 1) := by
  rw [← cx_conjRep, conjRep_Pc_w2]
private theorem conjRepc_Pc_w3 : conjRepc Pc (cx (wbasis 3)) = cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Pc_w3]
private theorem conjRepc_Rz45_w0 : conjRepc Rz45 (cx (wbasis 0)) = -cx (wbasis 3) := by
  rw [← cx_conjRep, conjRep_Rz45_w0, map_neg]
private theorem conjRepc_Rz45_w3 : conjRepc Rz45 (cx (wbasis 3)) = cx (wbasis 0) := by
  rw [← cx_conjRep, conjRep_Rz45_w3]
private theorem conjRepc_Rz45_w4 : conjRepc Rz45 (cx (wbasis 4))
    = (-2⁻¹ : ℂ) • cx (wbasis 0) + (2⁻¹ : ℂ) • cx (wbasis 3) + cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Rz45_w4]; simp only [map_add, cx_smul]; push_cast; module
private theorem conjRepc_Ry45_w3 : conjRepc Ry45 (cx (wbasis 3))
    = (-2⁻¹ : ℂ) • cx (wbasis 1) + (2⁻¹ : ℂ) • cx (wbasis 3) + (-2⁻¹ : ℂ) • cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Ry45_w3]; simp only [map_add, cx_smul]; push_cast; module
private theorem conjRepc_Ry45_w4 : conjRepc Ry45 (cx (wbasis 4))
    = (-2⁻¹ : ℂ) • cx (wbasis 1) + (-2⁻¹ : ℂ) • cx (wbasis 3) + (2⁻¹ : ℂ) • cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Ry45_w4]; simp only [map_add, cx_smul]; push_cast; module
private theorem conjRepc_Dx_w0 : conjRepc Dx (cx (wbasis 0)) = -cx (wbasis 0) := by
  rw [← cx_conjRep, conjRep_Dx_w0, map_neg]
private theorem conjRepc_Dx_w1 : conjRepc Dx (cx (wbasis 1)) = -cx (wbasis 1) := by
  rw [← cx_conjRep, conjRep_Dx_w1, map_neg]
private theorem conjRepc_Dx_w2 : conjRepc Dx (cx (wbasis 2)) = cx (wbasis 2) := by
  rw [← cx_conjRep, conjRep_Dx_w2]
private theorem conjRepc_Dx_w3 : conjRepc Dx (cx (wbasis 3)) = cx (wbasis 3) := by
  rw [← cx_conjRep, conjRep_Dx_w3]
private theorem conjRepc_Dx_w4 : conjRepc Dx (cx (wbasis 4)) = cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Dx_w4]
private theorem conjRepc_Dy_w0 : conjRepc Dy (cx (wbasis 0)) = -cx (wbasis 0) := by
  rw [← cx_conjRep, conjRep_Dy_w0, map_neg]
private theorem conjRepc_Dy_w1 : conjRepc Dy (cx (wbasis 1)) = cx (wbasis 1) := by
  rw [← cx_conjRep, conjRep_Dy_w1]
private theorem conjRepc_Dy_w2 : conjRepc Dy (cx (wbasis 2)) = -cx (wbasis 2) := by
  rw [← cx_conjRep, conjRep_Dy_w2, map_neg]
private theorem conjRepc_Dy_w3 : conjRepc Dy (cx (wbasis 3)) = cx (wbasis 3) := by
  rw [← cx_conjRep, conjRep_Dy_w3]
private theorem conjRepc_Dy_w4 : conjRepc Dy (cx (wbasis 4)) = cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Dy_w4]
private theorem conjRepc_Dz_w0 : conjRepc Dz (cx (wbasis 0)) = cx (wbasis 0) := by
  rw [← cx_conjRep, conjRep_Dz_w0]
private theorem conjRepc_Dz_w1 : conjRepc Dz (cx (wbasis 1)) = -cx (wbasis 1) := by
  rw [← cx_conjRep, conjRep_Dz_w1, map_neg]
private theorem conjRepc_Dz_w2 : conjRepc Dz (cx (wbasis 2)) = -cx (wbasis 2) := by
  rw [← cx_conjRep, conjRep_Dz_w2, map_neg]
private theorem conjRepc_Dz_w3 : conjRepc Dz (cx (wbasis 3)) = cx (wbasis 3) := by
  rw [← cx_conjRep, conjRep_Dz_w3]
private theorem conjRepc_Dz_w4 : conjRepc Dz (cx (wbasis 4)) = cx (wbasis 4) := by
  rw [← cx_conjRep, conjRep_Dz_w4]

/-- **(b), complexified.** The complexified standard representation `V ⊗ ℂ ≅ skewSubc` is
irreducible: every `SO(3)`-invariant `ℂ`-subspace contained in `skewSubc` is `⊥` or all of
`skewSubc`. -/
theorem skewSub_irreducible_complexified (U : Submodule ℂ EndVc) (hUle : U ≤ skewSubc)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRepc A M ∈ U) :
    U = ⊥ ∨ U = skewSubc := by
  -- The combinatorial argument of `skewSub_irreducible` transported to `ℂ`.
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)
  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  have hMsk : Mᵀ = -M := mem_skewSubc_iff.mp (hUle hMU)
  have hMdec : M = M 0 1 • cx (sbasis 0) + M 0 2 • cx (sbasis 1) + M 1 2 • cx (sbasis 2) :=
    skew_decompc M hMsk
  have hDzM : conjRepc Dz M ∈ U := hUinv Dz M hMU
  have hDyM : conjRepc Dy M ∈ U := hUinv Dy M hMU
  have hDxM : conjRepc Dx M ∈ U := hUinv Dx M hMU
  have hav0 : M 0 1 • cx (sbasis 0) ∈ U := by
    have key : M 0 1 • cx (sbasis 0) = (2⁻¹ : ℂ) • (M + conjRepc Dz M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRepc_Dz0, conjRepc_Dz1, conjRepc_Dz2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDzM)
  have hbv1 : M 0 2 • cx (sbasis 1) ∈ U := by
    have key : M 0 2 • cx (sbasis 1) = (2⁻¹ : ℂ) • (M + conjRepc Dy M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRepc_Dy0, conjRepc_Dy1, conjRepc_Dy2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDyM)
  have hcv2 : M 1 2 • cx (sbasis 2) ∈ U := by
    have key : M 1 2 • cx (sbasis 2) = (2⁻¹ : ℂ) • (M + conjRepc Dx M) := by
      conv_rhs => rw [hMdec]
      simp only [map_add, map_smul, conjRepc_Dx0, conjRepc_Dx1, conjRepc_Dx2]
      module
    rw [key]; exact U.smul_mem _ (U.add_mem hMU hDxM)
  have hav2 : M 0 1 • cx (sbasis 2) ∈ U := by
    have t := hUinv Pc _ hav0; rwa [map_smul, conjRepc_Pc0] at t
  have hav1 : M 0 1 • cx (sbasis 1) ∈ U := by
    have t := hUinv Pc _ hav2; rw [map_smul, conjRepc_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv0 : M 0 2 • cx (sbasis 0) ∈ U := by
    have t := hUinv Pc _ hbv1; rw [map_smul, conjRepc_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  have hbv2 : M 0 2 • cx (sbasis 2) ∈ U := by
    have t := hUinv Pc _ hbv0; rwa [map_smul, conjRepc_Pc0] at t
  have hcv1 : M 1 2 • cx (sbasis 1) ∈ U := by
    have t := hUinv Pc _ hcv2; rw [map_smul, conjRepc_Pc2, smul_neg] at t
    exact neg_mem_iff.mp t
  have hcv0 : M 1 2 • cx (sbasis 0) ∈ U := by
    have t := hUinv Pc _ hcv1; rw [map_smul, conjRepc_Pc1, smul_neg] at t
    exact neg_mem_iff.mp t
  have hne3 : M 0 1 ≠ 0 ∨ M 0 2 ≠ 0 ∨ M 1 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hMne (by rw [hMdec, hcon.1, hcon.2.1, hcon.2.2]; simp)
  have extract : ∀ w : EndVc,
      M 0 1 • w ∈ U → M 0 2 • w ∈ U → M 1 2 • w ∈ U → w ∈ U := by
    intro w h1 h2 h3
    rcases hne3 with hh | hh | hh
    · rw [← one_smul ℂ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h1
    · rw [← one_smul ℂ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h2
    · rw [← one_smul ℂ w, ← inv_mul_cancel₀ hh, mul_smul]; exact U.smul_mem _ h3
  have hs0 : cx (sbasis 0) ∈ U := extract _ hav0 hbv0 hcv0
  have hs1 : cx (sbasis 1) ∈ U := extract _ hav1 hbv1 hcv1
  have hs2 : cx (sbasis 2) ∈ U := extract _ hav2 hbv2 hcv2
  intro N hN
  rw [skew_decompc N (mem_skewSubc_iff.mp hN)]
  exact U.add_mem (U.add_mem (U.smul_mem _ hs0) (U.smul_mem _ hs1)) (U.smul_mem _ hs2)

/-- **(b), complexified.** The complexified representation `W ⊗ ℂ = tracelessSymSubc` is
irreducible: every `SO(3)`-invariant `ℂ`-subspace contained in `tracelessSymSubc` is `⊥` or all
of `tracelessSymSubc`. -/
theorem tracelessSymSub_irreducible_complexified (U : Submodule ℂ EndVc)
    (hUle : U ≤ tracelessSymSubc)
    (hUinv : ∀ (A : SO3), ∀ M ∈ U, conjRepc A M ∈ U) :
    U = ⊥ ∨ U = tracelessSymSubc := by
  -- The combinatorial argument of `tracelessSymSub_irreducible` transported to `ℂ`.
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (le_antisymm hUle ?_)
  have projA : ∀ N ∈ U, N 0 1 • cx (wbasis 0) ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := mem_tracelessSymSubc_iff.mp (hUle hN)
    have key : N 0 1 • cx (wbasis 0)
        = (4⁻¹ : ℂ) • (N - conjRepc Dx N - conjRepc Dy N + conjRepc Dz N) := by
      conv_rhs => rw [traceless_sym_decompc N hsym htr]
      simp only [map_add, map_smul, conjRepc_Dx_w0, conjRepc_Dx_w1, conjRepc_Dx_w2, conjRepc_Dx_w3,
        conjRepc_Dx_w4, conjRepc_Dy_w0, conjRepc_Dy_w1, conjRepc_Dy_w2, conjRepc_Dy_w3,
        conjRepc_Dy_w4, conjRepc_Dz_w0, conjRepc_Dz_w1, conjRepc_Dz_w2, conjRepc_Dz_w3,
        conjRepc_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.add_mem (U.sub_mem (U.sub_mem hN (hUinv Dx N hN))
      (hUinv Dy N hN)) (hUinv Dz N hN))
  have projB : ∀ N ∈ U, N 0 2 • cx (wbasis 1) ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := mem_tracelessSymSubc_iff.mp (hUle hN)
    have key : N 0 2 • cx (wbasis 1)
        = (4⁻¹ : ℂ) • (N - conjRepc Dx N + conjRepc Dy N - conjRepc Dz N) := by
      conv_rhs => rw [traceless_sym_decompc N hsym htr]
      simp only [map_add, map_smul, conjRepc_Dx_w0, conjRepc_Dx_w1, conjRepc_Dx_w2, conjRepc_Dx_w3,
        conjRepc_Dx_w4, conjRepc_Dy_w0, conjRepc_Dy_w1, conjRepc_Dy_w2, conjRepc_Dy_w3,
        conjRepc_Dy_w4, conjRepc_Dz_w0, conjRepc_Dz_w1, conjRepc_Dz_w2, conjRepc_Dz_w3,
        conjRepc_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.add_mem (U.sub_mem hN (hUinv Dx N hN))
      (hUinv Dy N hN)) (hUinv Dz N hN))
  have projC : ∀ N ∈ U, N 1 2 • cx (wbasis 2) ∈ U := by
    intro N hN
    obtain ⟨hsym, htr⟩ := mem_tracelessSymSubc_iff.mp (hUle hN)
    have key : N 1 2 • cx (wbasis 2)
        = (4⁻¹ : ℂ) • (N + conjRepc Dx N - conjRepc Dy N - conjRepc Dz N) := by
      conv_rhs => rw [traceless_sym_decompc N hsym htr]
      simp only [map_add, map_smul, conjRepc_Dx_w0, conjRepc_Dx_w1, conjRepc_Dx_w2, conjRepc_Dx_w3,
        conjRepc_Dx_w4, conjRepc_Dy_w0, conjRepc_Dy_w1, conjRepc_Dy_w2, conjRepc_Dy_w3,
        conjRepc_Dy_w4, conjRepc_Dz_w0, conjRepc_Dz_w1, conjRepc_Dz_w2, conjRepc_Dz_w3,
        conjRepc_Dz_w4]
      module
    rw [key]
    exact U.smul_mem _ (U.sub_mem (U.sub_mem (U.add_mem hN (hUinv Dx N hN))
      (hUinv Dy N hN)) (hUinv Dz N hN))
  have hbootstrap : cx (wbasis 0) ∈ U → tracelessSymSubc ≤ U := by
    intro hw0
    have hw2 : cx (wbasis 2) ∈ U := by
      have t := hUinv Pc _ hw0; rwa [conjRepc_Pc_w0] at t
    have hw1 : cx (wbasis 1) ∈ U := by
      have t := hUinv Pc _ hw2; rwa [conjRepc_Pc_w2] at t
    have hw3 : cx (wbasis 3) ∈ U := by
      have t := hUinv Rz45 _ hw0; rw [conjRepc_Rz45_w0] at t
      exact (Submodule.neg_mem_iff U).mp t
    have hw4 : cx (wbasis 4) ∈ U := by
      have t := hUinv Pc _ hw3; rwa [conjRepc_Pc_w3] at t
    intro N hN
    obtain ⟨hNsym, hNtr⟩ := mem_tracelessSymSubc_iff.mp hN
    rw [traceless_sym_decompc N hNsym hNtr]
    exact U.add_mem (U.add_mem (U.add_mem (U.add_mem
      (U.smul_mem _ hw0) (U.smul_mem _ hw1)) (U.smul_mem _ hw2))
      (U.smul_mem _ hw3)) (U.smul_mem _ hw4)
  have smul_extract : ∀ {c : ℂ} {w : EndVc}, c ≠ 0 → c • w ∈ U → w ∈ U := by
    intro c w hc hcw
    rw [← one_smul ℂ w, ← inv_mul_cancel₀ hc, mul_smul]; exact U.smul_mem _ hcw
  have w1_to_w0 : cx (wbasis 1) ∈ U → cx (wbasis 0) ∈ U := fun hw1 => by
    have t := hUinv Pc _ hw1; rwa [conjRepc_Pc_w1] at t
  have w2_to_w0 : cx (wbasis 2) ∈ U → cx (wbasis 0) ∈ U := fun hw2 => by
    have t := hUinv Pc _ hw2; rw [conjRepc_Pc_w2] at t; exact w1_to_w0 t
  obtain ⟨M, hMU, hMne⟩ := U.ne_bot_iff.mp h
  obtain ⟨hMsym, hMtr⟩ := mem_tracelessSymSubc_iff.mp (hUle hMU)
  rcases eq_or_ne (M 0 1) 0 with h01 | h01
  · rcases eq_or_ne (M 0 2) 0 with h02 | h02
    · rcases eq_or_ne (M 1 2) 0 with h12 | h12
      · have hMdec : M = M 0 0 • cx (wbasis 3) + (M 0 0 + M 1 1) • cx (wbasis 4) := by
          have hd := traceless_sym_decompc M hMsym hMtr
          rw [h01, h02, h12] at hd
          simpa only [zero_smul, zero_add] using hd
        set a := M 0 0 with ha
        set b := M 1 1 with hb
        rcases eq_or_ne a b with hab | hab
        · have hM00 : a ≠ 0 := by
            intro hz
            have hb0 : b = 0 := by rw [← hab]; exact hz
            apply hMne
            conv_lhs => rw [hMdec]
            rw [hz, hb0]; simp
          have hform : conjRepc Ry45 M
              = (-(2 * a + b) / 2) • cx (wbasis 1) + (-b / 2) • cx (wbasis 3)
                + (b / 2) • cx (wbasis 4) := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRepc_Ry45_w3, conjRepc_Ry45_w4]
            module
          have hentry : (conjRepc Ry45 M) 0 2 = -(2 * a + b) / 2 := by
            rw [hform]; simp [wbasis, Matrix.add_apply]
          have hne : 2 * a + b ≠ 0 := by
            rw [← hab]; intro hc; exact hM00 (by linear_combination (3⁻¹ : ℂ) * hc)
          have hcoef : (conjRepc Ry45 M) 0 2 ≠ 0 := by
            rw [hentry, neg_div]; exact neg_ne_zero.mpr (div_ne_zero hne (by norm_num))
          exact hbootstrap (w1_to_w0 (smul_extract hcoef (projB _ (hUinv Ry45 M hMU))))
        · have hform : conjRepc Rz45 M
              = ((a - b) / 2) • cx (wbasis 0) + ((a + b) / 2) • cx (wbasis 3)
                + (a + b) • cx (wbasis 4) := by
            conv_lhs => rw [hMdec]
            rw [map_add, map_smul, map_smul, conjRepc_Rz45_w3, conjRepc_Rz45_w4]
            module
          have hentry : (conjRepc Rz45 M) 0 1 = (a - b) / 2 := by
            rw [hform]; simp [wbasis, Matrix.add_apply]
          have hcoef : (conjRepc Rz45 M) 0 1 ≠ 0 :=
            hentry ▸ div_ne_zero (sub_ne_zero.mpr hab) (by norm_num)
          exact hbootstrap (smul_extract hcoef (projA _ (hUinv Rz45 M hMU)))
      · exact hbootstrap (w2_to_w0 (smul_extract h12 (projC M hMU)))
    · exact hbootstrap (w1_to_w0 (smul_extract h02 (projB M hMU)))
  · exact hbootstrap (smul_extract h01 (projA M hMU))

/-! ### Schur-lemma infrastructure for Hooke's law -/

/-- The conjugation action fixes the identity matrix: `conjRep A 1 = 1`. -/
theorem conjRep_one (A : SO3) : conjRep A (1 : EndV) = 1 := by
  rw [conjRep_apply, Matrix.mul_one, coe_mul_star]

/-- The conjugation action commutes with transpose: `conjRep A (Mᵀ) = (conjRep A M)ᵀ`. -/
theorem conjRep_transpose (A : SO3) (M : EndV) :
    conjRep A Mᵀ = (conjRep A M)ᵀ := by
  simp only [conjRep_apply, star_coe_eq_transpose, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc]

/-- The conjugation action preserves the trace: `trace (conjRep A M) = trace M`. -/
theorem conjRep_trace (A : SO3) (M : EndV) : (conjRep A M).trace = M.trace := by
  rw [conjRep_apply, Matrix.trace_mul_comm ((A : EndV) * M) (star (A : EndV)),
    ← Matrix.mul_assoc, star_mul_coe, Matrix.one_mul]

/-- Projection of `End(V)` onto the scalar (trivial) summand: `M ↦ (trace M / 3) • 1`. -/
def scalarProj : EndV →ₗ[ℝ] EndV where
  toFun M := (M.trace / 3) • (1 : EndV)
  map_add' M N := by rw [Matrix.trace_add]; module
  map_smul' c M := by rw [Matrix.trace_smul]; simp only [RingHom.id_apply, smul_eq_mul]; module

@[simp] theorem scalarProj_apply (M : EndV) : scalarProj M = (M.trace / 3) • (1 : EndV) := rfl

/-- `scalarProj` is `SO(3)`-equivariant. -/
theorem scalarProj_equivariant (A : SO3) (M : EndV) :
    scalarProj (conjRep A M) = conjRep A (scalarProj M) := by
  rw [scalarProj_apply, scalarProj_apply, conjRep_trace, map_smul, conjRep_one]

/-- Projection of `End(V)` onto the skew-symmetric summand: `M ↦ (1/2) • (M - Mᵀ)`. -/
def skewProj : EndV →ₗ[ℝ] EndV where
  toFun M := (1 / 2 : ℝ) • (M - Mᵀ)
  map_add' M N := by rw [Matrix.transpose_add]; module
  map_smul' c M := by rw [Matrix.transpose_smul]; simp only [RingHom.id_apply]; module

@[simp] theorem skewProj_apply (M : EndV) : skewProj M = (1 / 2 : ℝ) • (M - Mᵀ) := rfl

/-- `skewProj` is `SO(3)`-equivariant. -/
theorem skewProj_equivariant (A : SO3) (M : EndV) :
    skewProj (conjRep A M) = conjRep A (skewProj M) := by
  rw [skewProj_apply, skewProj_apply, map_smul, map_sub, conjRep_transpose]

/-- `scalarProj M` lies in `scalarSub`. -/
theorem scalarProj_mem (M : EndV) : scalarProj M ∈ scalarSub := by
  rw [scalarProj_apply, scalarSub]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `skewProj M` lies in `skewSub`. -/
theorem skewProj_mem (M : EndV) : skewProj M ∈ skewSub := by
  rw [skewProj_apply, mem_skewSub_iff, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_transpose]
  module

/-- **Schur, dimension form.** An `SO(3)`-equivariant map `φ` sending an irreducible invariant
subspace `W` into a *strictly smaller* invariant subspace `Wsmall` vanishes on `W`: otherwise the
restriction `W → Wsmall` would be injective, forcing `finrank W ≤ finrank Wsmall`. -/
theorem equivMap_eq_zero_of_finrank_lt (φ : EndV →ₗ[ℝ] EndV)
    (hφ : ∀ (A : SO3) (M : EndV), φ (conjRep A M) = conjRep A (φ M))
    (W Wsmall : Submodule ℝ EndV)
    (hWirr : ∀ (U : Submodule ℝ EndV), U ≤ W →
      (∀ (A : SO3), ∀ M ∈ U, conjRep A M ∈ U) → U = ⊥ ∨ U = W)
    (hWinv : ∀ (A : SO3), ∀ M ∈ W, conjRep A M ∈ W)
    (hmaps : ∀ w ∈ W, φ w ∈ Wsmall)
    (hlt : Module.finrank ℝ Wsmall < Module.finrank ℝ W) :
    ∀ w ∈ W, φ w = 0 := by
  have hkerinv : ∀ (A : SO3), ∀ M ∈ LinearMap.ker φ, conjRep A M ∈ LinearMap.ker φ := by
    intro A M hM
    rw [LinearMap.mem_ker] at hM ⊢
    rw [hφ A M, hM, map_zero]
  set K := W ⊓ LinearMap.ker φ with hK
  have hKinv : ∀ (A : SO3), ∀ M ∈ K, conjRep A M ∈ K := by
    intro A M hM
    rw [hK, Submodule.mem_inf] at hM ⊢
    exact ⟨hWinv A M hM.1, hkerinv A M hM.2⟩
  rcases hWirr K inf_le_left hKinv with hbot | htop
  · exfalso
    have hψinj : Function.Injective (φ.restrict hmaps) := by
      rw [injective_iff_map_eq_zero]
      rintro ⟨x, hx⟩ hψ0
      have hfx : φ x = 0 := by
        have := congrArg (Subtype.val) hψ0
        rwa [LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at this
      have hxK : x ∈ K := by rw [hK]; exact ⟨hx, LinearMap.mem_ker.mpr hfx⟩
      rw [hbot, Submodule.mem_bot] at hxK
      exact Subtype.ext hxK
    have := LinearMap.finrank_le_finrank_of_injective hψinj
    omega
  · intro w hw
    have : w ∈ K := by rw [htop]; exact hw
    rw [hK, Submodule.mem_inf] at this
    exact LinearMap.mem_ker.mp this.2

/-- An `SO(3)`-invariant matrix (fixed by `Dz`, `Dy` and the cyclic rotation `Pc`) is a scalar. -/
theorem invariant_matrix_scalar (N : EndV)
    (hz : conjRep Dz N = N) (hy : conjRep Dy N = N) (hp : conjRep Pc N = N) :
    N = N 0 0 • (1 : EndV) := by
  rw [conjRep_apply] at hz hy hp
  -- off-diagonal entries killed by the sign rotations `Dz`, `Dy`
  have z02 := congr_fun (congr_fun hz 0) 2
  have z20 := congr_fun (congr_fun hz 2) 0
  have z12 := congr_fun (congr_fun hz 1) 2
  have z21 := congr_fun (congr_fun hz 2) 1
  have y01 := congr_fun (congr_fun hy 0) 1
  have y10 := congr_fun (congr_fun hy 1) 0
  -- diagonal entries equalised by the cyclic rotation `Pc`
  have p00 := congr_fun (congr_fun hp 0) 0
  have p11 := congr_fun (congr_fun hp 1) 1
  have p22 := congr_fun (congr_fun hp 2) 2
  simp only [Dz, Dy, Pc, Matrix.mul_apply, Fin.sum_univ_three, star, Matrix.conjTranspose,
    Matrix.transpose, Matrix.of_apply, Matrix.map_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    id_eq] at z02 z20 z12 z21 y01 y10 p00 p11 p22
  have h01 : N 0 1 = 0 := by linarith
  have h10 : N 1 0 = 0 := by linarith
  have h02 : N 0 2 = 0 := by linarith
  have h20 : N 2 0 = 0 := by linarith
  have h12 : N 1 2 = 0 := by linarith
  have h21 : N 2 1 = 0 := by linarith
  have h11 : N 1 1 = N 0 0 := by linarith
  have h22 : N 2 2 = N 0 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, smul_eq_mul, h01, h10, h02, h20, h12, h21, h11, h22]

open Polynomial Filter Topology in
/-- A real polynomial of odd degree has a root (via the intermediate value theorem). -/
theorem exists_isRoot_of_odd_natDegree {p : ℝ[X]} (hodd : Odd p.natDegree) :
    ∃ x : ℝ, p.IsRoot x := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hodd
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hpne
  set c := p.leadingCoeff⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hlc
  set q := C c * p with hq
  have hqdeg : q.natDegree = p.natDegree := by rw [hq, natDegree_C_mul hcne]
  have hqodd : Odd q.natDegree := hqdeg ▸ hodd
  have hqlc : q.leadingCoeff = 1 := by
    rw [hq, leadingCoeff_mul, leadingCoeff_C, hc, inv_mul_cancel₀ hlc]
  have hqnd : q.natDegree ≠ 0 := by
    rintro h; rw [h] at hqodd; simp at hqodd
  have hdeg : 0 < q.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hqnd)
  -- reduce the root of `p` to a root of `q` (same roots, positive leading coefficient)
  suffices h : ∃ x, q.IsRoot x by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    have : eval x q = 0 := hx
    rw [hq, eval_mul, eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left hcne
  -- a point where `q` is positive
  have hpos : Tendsto (fun x => eval x q) atTop atTop :=
    q.tendsto_atTop_of_leadingCoeff_nonneg hdeg (by rw [hqlc]; norm_num)
  obtain ⟨b, hb⟩ := (hpos.eventually_gt_atTop 0).exists
  -- a point where `q` is negative, via `q ∘ (-X)`
  set r := q.comp (-X) with hr
  have hrnd : r.natDegree = q.natDegree := by rw [hr, natDegree_comp]; simp
  have hrdeg : 0 < r.degree :=
    natDegree_pos_iff_degree_pos.mp (by rw [hrnd]; exact Nat.pos_of_ne_zero hqnd)
  have hrlc : r.leadingCoeff ≤ 0 := by
    rw [hr, leadingCoeff_comp (by simp), hqlc, one_mul, leadingCoeff_neg, leadingCoeff_X,
      Odd.neg_one_pow hqodd]
    norm_num
  have hneg : Tendsto (fun x => eval x r) atTop atBot :=
    r.tendsto_atBot_of_leadingCoeff_nonpos hrdeg hrlc
  obtain ⟨a, ha⟩ := (hneg.eventually_lt_atBot 0).exists
  have ha' : eval (-a) q < 0 := by rw [hr, eval_comp, eval_neg, eval_X] at ha; exact ha
  have hmem : (0 : ℝ) ∈ Set.Icc (eval (-a) q) (eval b q) := ⟨ha'.le, hb.le⟩
  rcases le_total (-a) b with hab | hab
  · obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab q.continuous.continuousOn hmem
    exact ⟨x, hx⟩
  · obtain ⟨x, _, hx⟩ := intermediate_value_Icc' hab q.continuous.continuousOn hmem
    exact ⟨x, hx⟩

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
  have hf_pt : ∀ (A : SO3) (M : EndV), f (conjRep A M) = conjRep A (f M) :=
    fun A M => LinearMap.congr_fun (hf A) M
  -- Scalar `K` on `scalarSub`: `f 1` is `conjRep`-invariant, hence scalar.
  have hinv1 : ∀ A : SO3, conjRep A (f 1) = f 1 := fun A => by rw [← hf_pt A 1, conjRep_one]
  set K := (f 1) 0 0 with hKdef
  have hf1 : f 1 = K • (1 : EndV) :=
    invariant_matrix_scalar (f 1) (hinv1 Dz) (hinv1 Dy) (hinv1 Pc)
  have hscalar : ∀ x ∈ scalarSub, f x = K • x := by
    intro x hx
    rw [scalarSub, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_smul, hf1, smul_comm]
  -- `f` preserves `tracelessSymSub`: its scalar/skew components vanish by Schur.
  have hWinv : ∀ (A : SO3), ∀ M ∈ tracelessSymSub, conjRep A M ∈ tracelessSymSub :=
    fun A M hM => conjRep_invariant tracelessSymSub (Or.inr (Or.inr rfl)) A M hM
  have hsc0 : ∀ w ∈ tracelessSymSub, scalarProj (f w) = 0 := by
    refine equivMap_eq_zero_of_finrank_lt (scalarProj.comp f) ?_ tracelessSymSub scalarSub
      tracelessSymSub_irreducible hWinv ?_ ?_
    · intro A M; simp only [LinearMap.comp_apply]; rw [hf_pt, scalarProj_equivariant]
    · intro w _; simp only [LinearMap.comp_apply]; exact scalarProj_mem _
    · rw [scalarSub_finrank, tracelessSymSub_finrank]; norm_num
  have hsk0 : ∀ w ∈ tracelessSymSub, skewProj (f w) = 0 := by
    refine equivMap_eq_zero_of_finrank_lt (skewProj.comp f) ?_ tracelessSymSub skewSub
      tracelessSymSub_irreducible hWinv ?_ ?_
    · intro A M; simp only [LinearMap.comp_apply]; rw [hf_pt, skewProj_equivariant]
    · intro w _; simp only [LinearMap.comp_apply]; exact skewProj_mem _
    · rw [skewSub_finrank, tracelessSymSub_finrank]; norm_num
  have hmapsW : ∀ w ∈ tracelessSymSub, f w ∈ tracelessSymSub := by
    intro w hw
    have hs := hsc0 w hw
    have hk := hsk0 w hw
    rw [scalarProj_apply, smul_eq_zero] at hs
    rw [skewProj_apply, smul_eq_zero] at hk
    rw [mem_tracelessSymSub_iff]
    refine ⟨?_, ?_⟩
    · rcases hk with h | h
      · norm_num at h
      · rw [sub_eq_zero] at h; exact h.symm
    · rcases hs with h | h
      · exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)
      · exact absurd h one_ne_zero
  -- Scalar `μ` on `tracelessSymSub`: `f|_W` on odd-dim `W` has a real eigenvalue `μ`;
  -- its `μ`-eigenspace is a nonzero invariant subspace, hence all of `W` by irreducibility.
  set g : Module.End ℝ tracelessSymSub := f.restrict hmapsW with hg
  have hgnd : g.charpoly.natDegree = 5 := by
    rw [LinearMap.charpoly_natDegree, tracelessSymSub_finrank]
  obtain ⟨μ, hμ⟩ := exists_isRoot_of_odd_natDegree (p := g.charpoly) (by rw [hgnd]; decide)
  have hev : g.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly g μ).mpr hμ
  obtain ⟨v, hvec⟩ := hev.exists_hasEigenvector
  have hvsmul : g v = μ • v := hvec.apply_eq_smul
  have hvne : (v : EndV) ≠ 0 :=
    fun h => (Module.End.hasEigenvector_iff.mp hvec).2 (Subtype.ext (by simpa using h))
  have hfv : f (v : EndV) = μ • (v : EndV) := by
    have := congrArg (Subtype.val) hvsmul
    rwa [LinearMap.coe_restrict_apply, Submodule.coe_smul] at this
  set E := tracelessSymSub ⊓ LinearMap.ker (f - μ • LinearMap.id) with hE
  have hEinv : ∀ (A : SO3), ∀ M ∈ E, conjRep A M ∈ E := by
    intro A M hM
    rw [hE, Submodule.mem_inf] at hM
    obtain ⟨hM1, hM2⟩ := hM
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hM2
    rw [hE, Submodule.mem_inf]
    refine ⟨hWinv A M hM1, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, hf_pt, hM2, map_smul]
  have hEne : E ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, ?_, hvne⟩
    rw [hE, Submodule.mem_inf]
    refine ⟨v.2, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, hfv]
  have hEtop : E = tracelessSymSub :=
    (tracelessSymSub_irreducible E inf_le_left hEinv).resolve_left hEne
  have hmu : ∀ y ∈ tracelessSymSub, f y = μ • y := by
    intro y hy
    have hyE : y ∈ E := by rw [hEtop]; exact hy
    rw [hE, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hyE
    exact hyE.2
  -- `f` preserves `symSub`: split `x = s + w` and reuse the two scalars.
  refine ⟨K, μ, hscalar, hmu, ?_⟩
  intro x hx
  rw [← symSub_eq_scalar_sup_tracelessSym.1] at hx
  rw [Submodule.mem_sup] at hx
  obtain ⟨s, hs, w, hw, rfl⟩ := hx
  rw [map_add, hscalar s hs, hmu w hw]
  exact Submodule.add_mem _ (Submodule.smul_mem symSub K (scalar_le_sym hs))
    (Submodule.smul_mem symSub μ (tracelessSym_le_sym hw))

/-- **(b), the book's displayed conclusion.** For `x` in the trivial summand `ℝ·1` and `y` in
the `5`-dimensional summand `W`, an equivariant `f` satisfies `f (x + y) = K x + μ y`. -/
theorem hooke_law_add (f : EndV →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (conjRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ, ∀ x ∈ scalarSub, ∀ y ∈ tracelessSymSub, f (x + y) = K • x + μ • y := by
  obtain ⟨K, μ, hK, hμ, -⟩ := hooke_law f hf
  exact ⟨K, μ, fun x hx y hy => by rw [map_add, hK x hx, hμ y hy]⟩

/-! ### Part (b) on the book's exact domain `f : S²V → End(V)`

The book's elasticity law is a linear map `f : S²V → End(V)`, defined only on the symmetric
matrices, so `hooke_law` above — which assumes an equivariant self-map of `End(V)` — cannot be
instantiated at the book's data. This section restates the conclusion on the exact domain.

The route is supplied by part (a): `End(V) = S²V ⊕ Λ²V` as representations, with the
`SO(3)`-equivariant projection `symProj : M ↦ (M + Mᵀ)/2` onto the symmetric summand. So an
equivariant `f : S²V → End(V)` extends to `symExtend f = f ∘ symProj` on all of `End(V)`
(equivalently: extend by `0` on the skew summand), the extension is again equivariant, and
`hooke_law` applies to it. Restricting back gives the exact-domain statement. -/

/-- The symmetric matrices `S²V` form an `SO(3)`-invariant subspace of `End(V)`. -/
theorem conjRep_symSub_mem (A : SO3) {M : EndV} (hM : M ∈ symSub) : conjRep A M ∈ symSub := by
  have h : Mᵀ = M := hM
  change (conjRep A M)ᵀ = conjRep A M
  rw [← conjRep_transpose, h]

/-- `S²V` as a representation of `SO(3)`: the restriction of `conjRep` to `symSub`. -/
def symRep : Representation ℝ SO3 symSub where
  toFun A := (conjRep A).restrict (fun _ hM => conjRep_symSub_mem A hM)
  map_one' := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp
  map_mul' A B := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp [mul_assoc]

@[simp] theorem symRep_coe_apply (A : SO3) (x : symSub) :
    (symRep A x : EndV) = conjRep A (x : EndV) := rfl

/-- The equivariance hypothesis below is satisfiable by a nonzero map: the inclusion
`S²V ↪ End(V)` is `SO(3)`-equivariant. (It is the elasticity law with `K = μ = 1`.) -/
theorem symSub_subtype_equivariant (A : SO3) :
    symSub.subtype.comp (symRep A) = (conjRep A).comp symSub.subtype :=
  LinearMap.ext fun _ => rfl

/-- Projection of `End(V)` onto the symmetric summand `S²V`: `M ↦ (1/2) • (M + Mᵀ)`. -/
def symProj : EndV →ₗ[ℝ] EndV where
  toFun M := (1 / 2 : ℝ) • (M + Mᵀ)
  map_add' M N := by rw [Matrix.transpose_add]; module
  map_smul' c M := by rw [Matrix.transpose_smul]; simp only [RingHom.id_apply]; module

@[simp] theorem symProj_apply (M : EndV) : symProj M = (1 / 2 : ℝ) • (M + Mᵀ) := rfl

/-- `symProj M` lies in `symSub`. -/
theorem symProj_mem (M : EndV) : symProj M ∈ symSub := by
  rw [symProj_apply, mem_symSub_iff, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_transpose]
  module

/-- `symProj` is `SO(3)`-equivariant. -/
theorem symProj_equivariant (A : SO3) (M : EndV) :
    symProj (conjRep A M) = conjRep A (symProj M) := by
  rw [symProj_apply, symProj_apply, map_smul, map_add, conjRep_transpose]

/-- `symProj` is the identity on `S²V`. -/
theorem symProj_eq_self {M : EndV} (hM : M ∈ symSub) : symProj M = M := by
  have h : Mᵀ = M := hM
  rw [symProj_apply, h]
  module

/-- `symProj` viewed as a map into `S²V`. -/
def symProjTo : EndV →ₗ[ℝ] symSub := LinearMap.codRestrict symSub symProj symProj_mem

@[simp] theorem symProjTo_coe (M : EndV) : (symProjTo M : EndV) = symProj M := rfl

theorem symProjTo_apply_coe (x : symSub) : symProjTo (x : EndV) = x :=
  Subtype.ext (by rw [symProjTo_coe, symProj_eq_self x.2])

theorem symProjTo_equivariant (A : SO3) (M : EndV) :
    symProjTo (conjRep A M) = symRep A (symProjTo M) :=
  Subtype.ext (by rw [symProjTo_coe, symRep_coe_apply, symProjTo_coe, symProj_equivariant])

/-- Extension of an elasticity law `f : S²V → End(V)` to all of `End(V)`, by composing with the
equivariant projection onto `S²V`; equivalently, extension by `0` on the skew summand `Λ²V`. -/
def symExtend (f : symSub →ₗ[ℝ] EndV) : EndV →ₗ[ℝ] EndV := f.comp symProjTo

theorem symExtend_apply_coe (f : symSub →ₗ[ℝ] EndV) (x : symSub) :
    symExtend f (x : EndV) = f x := by
  rw [symExtend, LinearMap.comp_apply, symProjTo_apply_coe]

/-- The extension of an equivariant `f : S²V → End(V)` is equivariant on all of `End(V)`. -/
theorem symExtend_equivariant (f : symSub →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (symRep A) = (conjRep A).comp f) (A : SO3) :
    (symExtend f).comp (conjRep A) = (conjRep A).comp (symExtend f) := by
  refine LinearMap.ext fun M => ?_
  have hpt := LinearMap.congr_fun (hf A) (symProjTo M)
  simp only [LinearMap.comp_apply] at hpt
  simp only [symExtend, LinearMap.comp_apply]
  rw [symProjTo_equivariant, hpt]

/-- **(b), Hooke's law on the book's exact domain.** An `SO(3)`-equivariant linear map
`f : S²V → End(V)` — the book's elasticity law, defined only on the deformation tensors — acts
as the compression modulus `K` on the trivial summand `ℝ·1` and as the shearing modulus `μ` on
the `5`-dimensional summand `W`, and takes values in the symmetric matrices, so the stress
tensor `S_P = f (d_P)` is always symmetric. -/
theorem hooke_law_symSub (f : symSub →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (symRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ,
      (∀ x : symSub, (x : EndV) ∈ scalarSub → f x = K • (x : EndV)) ∧
      (∀ y : symSub, (y : EndV) ∈ tracelessSymSub → f y = μ • (y : EndV)) ∧
      (∀ x : symSub, f x ∈ symSub) := by
  obtain ⟨K, μ, hK, hμ, hsym⟩ := hooke_law (symExtend f) (symExtend_equivariant f hf)
  refine ⟨K, μ, fun x hx => ?_, fun y hy => ?_, fun x => ?_⟩
  · rw [← symExtend_apply_coe f x]; exact hK _ hx
  · rw [← symExtend_apply_coe f y]; exact hμ _ hy
  · rw [← symExtend_apply_coe f x]; exact hsym _ x.2

/-- **(b), the book's displayed conclusion on the exact domain.** For `x ∈ ℝ·1` and `y ∈ W`,
`f (x + y) = K x + μ y`. -/
theorem hooke_law_symSub_add (f : symSub →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (symRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ, ∀ x y : symSub, (x : EndV) ∈ scalarSub → (y : EndV) ∈ tracelessSymSub →
      f (x + y) = K • (x : EndV) + μ • (y : EndV) := by
  obtain ⟨K, μ, hK, hμ, -⟩ := hooke_law_symSub f hf
  exact ⟨K, μ, fun x y hx hy => by rw [map_add, hK x hx, hμ y hy]⟩

/-- **(b), the `54 = 2` statement.** Two real parameters determine the elasticity law
completely: every deformation tensor `d ∈ S²V` splits as `d = x + y` with `x ∈ ℝ·1` and
`y ∈ W`, and then `f d = K x + μ y`. -/
theorem hooke_law_symSub_two_moduli (f : symSub →ₗ[ℝ] EndV)
    (hf : ∀ A : SO3, f.comp (symRep A) = (conjRep A).comp f) :
    ∃ K μ : ℝ, ∀ d : symSub, ∃ x ∈ scalarSub, ∃ y ∈ tracelessSymSub,
      (d : EndV) = x + y ∧ f d = K • x + μ • y := by
  obtain ⟨K, μ, hK, hμ, -⟩ := hooke_law_symSub f hf
  refine ⟨K, μ, fun d => ?_⟩
  have hd : (d : EndV) ∈ scalarSub ⊔ tracelessSymSub := by
    rw [symSub_eq_scalar_sup_tracelessSym.1]; exact d.2
  rw [Submodule.mem_sup] at hd
  obtain ⟨x, hx, y, hy, hxy⟩ := hd
  refine ⟨x, hx, y, hy, hxy.symm, ?_⟩
  have hdxy : d = (⟨x, scalar_le_sym hx⟩ : symSub) + ⟨y, tracelessSym_le_sym hy⟩ :=
    Subtype.ext (by simpa using hxy.symm)
  rw [hdxy, map_add, hK _ hx, hμ _ hy]

end Etingof.Problem4_12_11
