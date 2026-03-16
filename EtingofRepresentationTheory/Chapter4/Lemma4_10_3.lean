import Mathlib

/-!
# Lemma 4.10.3: Irreducibility of the Generic Determinant

For an n × n matrix Y with entries y_{ij} treated as independent variables,
det(Y) is an irreducible polynomial in the n² variables {y_{ij}}.

## Proof strategy

By induction on n using cofactor expansion along row 0 and
`MvPolynomial.irreducible_mul_X_add`.

## Mathlib correspondence

Mathlib has `Matrix.det` and `MvPolynomial.Irreducible`. The irreducibility of
the generic determinant is not proved in Mathlib.
-/

open MvPolynomial Matrix Finset

-- Abbreviation for the generic matrix
private noncomputable def genMatrix (m : ℕ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) ℂ) :=
  of fun i j => X (i, j)

@[simp] private lemma genMatrix_apply (m : ℕ) (i j : Fin m) :
    genMatrix m i j = X (i, j) := rfl

private lemma genMatrix_eq_mvPolynomialX (m : ℕ) :
    genMatrix m = mvPolynomialX (Fin m) (Fin m) ℂ := rfl

/-- A submatrix determinant equals the rename of the smaller determinant. -/
private lemma submatrix_eq_rename (n : ℕ) (c : Fin (n + 2)) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c)) =
    rename (Prod.map Fin.succ (Fin.succAbove c)) (det (genMatrix (n + 1))) := by
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [genMatrix_apply, submatrix_apply, AlgHom.mapMatrix_apply, rename_X]

/-- Variables in any submatrix determinant have first component ≥ 1. -/
private lemma submatrix_vars_fst_ne_zero (n : ℕ) (c : Fin (n + 2))
    {v : Fin (n + 2) × Fin (n + 2)}
    (hv : v ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))).vars) :
    v.1 ≠ 0 := by
  rw [submatrix_eq_rename] at hv
  obtain ⟨⟨a, b⟩, _, hab⟩ := mem_vars_rename _ _ hv
  exact hab ▸ Fin.succ_ne_zero a

/-- The (0,0) minor equals the rename of the smaller determinant (column 0 case). -/
private lemma minor00_eq_rename (n : ℕ) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) =
    rename (Prod.map Fin.succ Fin.succ) (det (genMatrix (n + 1))) := by
  have := submatrix_eq_rename n 0
  simp only [Fin.succAbove_zero] at this ⊢
  exact this

/-- The (0,0) minor is nonzero. -/
private lemma minor00_ne_zero (n : ℕ) :
    det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) ≠ 0 := by
  rw [minor00_eq_rename]
  exact (rename_injective _
    (Prod.map_injective.mpr ⟨Fin.succ_injective _, Fin.succ_injective _⟩)).ne
    (det_mvPolynomialX_ne_zero (Fin (n + 1)) ℂ)

/-- The (0,0) minor doesn't involve variable (0,0). -/
private lemma minor00_vars (n : ℕ) :
    ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
    (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))).vars := by
  intro h
  exact absurd rfl (submatrix_vars_fst_ne_zero n 0 h)

/-- The remaining cofactor terms don't involve X(0,0). -/
private lemma rest_vars (n : ℕ) :
    ((0 : Fin (n + 2)), (0 : Fin (n + 2))) ∉
    (∑ j : Fin (n + 1),
      (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
      X ((0 : Fin (n + 2)), j.succ) *
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))).vars := by
  intro h
  have h' := vars_sum_subset (Finset.univ) _ h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h'
  obtain ⟨j, hj⟩ := h'
  -- vars of each term ⊆ vars of the two factors
  have hj' := vars_mul _ _ hj
  simp only [Finset.mem_union] at hj'
  rcases hj' with hj' | hj'
  · -- (0,0) in vars of (-1)^(j+1) * X(0, j.succ)
    have hj'' := vars_mul _ _ hj'
    simp only [Finset.mem_union] at hj''
    rcases hj'' with hj'' | hj''
    · -- (0,0) in vars of (-1)^(j+1) — impossible, it's a constant
      exact absurd (vars_pow _ _ hj'') (by simp)
    · -- (0,0) in vars(X(0, j.succ)) = {(0, j.succ)}
      rw [vars_X] at hj''
      simp only [Finset.mem_singleton] at hj''
      exact absurd (congr_arg Prod.snd hj'').symm (Fin.succ_ne_zero j)
  · -- (0,0) in vars of det(submatrix ... j.succ)
    exact absurd rfl (submatrix_vars_fst_ne_zero n j.succ hj')

/-- Irreducibility is preserved by `MvPolynomial.rename` with an injective function.
This is a general fact: in MvPolynomial over a domain, if `f` is injective then
`rename f` preserves irreducibility. The proof uses: (1) pick left inverse `g` of `f`,
(2) if `rename f p = a * b`, apply `rename g` to get `p = (rename g a) * (rename g b)`,
(3) WLOG `rename g a` is a unit, (4) show `a` is a unit using `degreeOf_mul_eq` to
establish `vars(a) ⊆ range f`, then `rename (f ∘ g) a = a`, hence `a = rename f (C c)`.
Missing from Mathlib; see https://github.com/leanprover-community/mathlib4/issues/XXXXX -/
private lemma vars_subset_vars_mul_left {σ : Type*} {R : Type*} [CommSemiring R]
    [NoZeroDivisors R] {a b : MvPolynomial σ R} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.vars ⊆ (a * b).vars := by
  classical
  intro x hx
  simp only [vars_def] at hx ⊢
  rw [Multiset.mem_toFinset] at hx ⊢
  rw [← Multiset.count_pos] at hx ⊢
  rw [← degreeOf_def] at hx ⊢
  have := degreeOf_mul_eq ha hb (n := x)
  omega

private lemma rename_irreducible {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]
    {f : σ → τ} (hf : Function.Injective f)
    {p : MvPolynomial σ ℂ} (hp : Irreducible p) :
    Irreducible (rename f p) := by
  constructor
  · -- rename f p is not a unit
    intro h
    exact hp.1 ((killCompl_rename_app hf p) ▸ h.map (killCompl hf).toRingHom)
  · -- If rename f p = a * b, then one of a, b is a unit
    intro a b hab
    have hne : rename f p ≠ 0 := (rename_injective f hf).ne hp.ne_zero
    have ha : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hne)
    have hb : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hne)
    -- vars of rename f p are contained in Set.range f
    have hvars_rfp : ∀ x ∈ (rename f p).vars, x ∈ Set.range f := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := mem_vars_rename f p hx
      exact Set.mem_range_self y
    -- vars(a) ⊆ vars(a*b) = vars(rename f p) ⊆ range f
    have hvars_a : ↑a.vars ⊆ Set.range f := by
      intro x hx
      exact hvars_rfp x (hab ▸ vars_subset_vars_mul_left ha hb hx)
    have hvars_b : ↑b.vars ⊆ Set.range f := by
      intro x hx
      exact hvars_rfp x (hab ▸ mul_comm a b ▸ vars_subset_vars_mul_left hb ha hx)
    -- Express a and b as renames
    obtain ⟨a', rfl⟩ := exists_rename_eq_of_vars_subset_range a f hf hvars_a
    obtain ⟨b', rfl⟩ := exists_rename_eq_of_vars_subset_range b f hf hvars_b
    -- rename f p = rename f a' * rename f b' = rename f (a' * b')
    rw [← map_mul] at hab
    have hab' : p = a' * b' := (rename_injective f hf) hab
    -- Since p is irreducible, one factor is a unit
    exact (hp.isUnit_or_isUnit hab').imp (·.map (rename f).toRingHom) (·.map (rename f).toRingHom)

set_option maxHeartbeats 800000 in
/-- The (0,0) minor is coprime to the rest of the cofactor expansion. -/
private lemma minor00_isRelPrime (n : ℕ) (ih' : Irreducible (det (genMatrix (n + 1)))) :
    IsRelPrime
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)))
      (∑ j : Fin (n + 1),
        (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
        X ((0 : Fin (n + 2)), j.succ) *
        det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) := by
  -- The minor M₀₀ is irreducible (hence prime in UFD) by IH + rename
  have hf_irr : Irreducible (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) := by
    rw [minor00_eq_rename]
    exact rename_irreducible (Prod.map_injective.mpr
      ⟨Fin.succ_injective _, Fin.succ_injective _⟩) ih'
  -- Irreducible ↔ not-dvd for IsRelPrime
  rw [hf_irr.isRelPrime_iff_not_dvd]
  -- M₀₁ is also irreducible
  have hf1_irr : Irreducible (det ((genMatrix (n + 2)).submatrix Fin.succ
      (Fin.succAbove (1 : Fin (n + 2))))) := by
    rw [submatrix_eq_rename]
    exact rename_irreducible (Prod.map_injective.mpr
      ⟨Fin.succ_injective _, Fin.succAbove_right_injective⟩) ih'
  -- Define evaluation: X(0,1)→1, X(0,j)→0 for j≠1, X(i,j)→X(i,j) for i≥1
  let φ : (Fin (n + 2) × Fin (n + 2)) → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ :=
    fun v => if v.1 = 0 then (if v.2 = 1 then 1 else 0) else X v
  -- aeval X is the identity
  have aeval_X_id : ∀ (p : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ),
      aeval (X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) p = p := by
    have : aeval (X : _ → MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) = AlgHom.id ℂ _ := by
      ext i; simp
    intro p; rw [this]; simp
  -- φ fixes any submatrix minor (no row-0 variables)
  have hφ_fix_minor : ∀ (c : Fin (n + 2)),
      aeval φ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))) =
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c)) := by
    intro c
    have hφ_eq : ∀ v ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove c))).vars, φ v = X v := by
      intro v hv
      simp only [φ, if_neg (submatrix_vars_fst_ne_zero n c hv)]
    rw [show aeval φ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))) =
      aeval X (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove c))) from
      MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hφ_eq i hi) rfl]
    exact aeval_X_id _
  -- φ(X(0, j.succ)) = 1 if j = 0, else 0
  have hφ_X : ∀ j : Fin (n + 1),
      φ ((0 : Fin (n + 2)), j.succ) = if j = 0 then 1 else 0 := by
    intro j
    simp only [φ, ite_true]
    rcases Decidable.eq_or_ne j 0 with rfl | hj
    · simp [show Fin.succ (0 : Fin (n + 1)) = (1 : Fin (n + 2)) from rfl]
    · simp [show Fin.succ j ≠ (1 : Fin (n + 2)) from by
        rwa [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Ne, Fin.succ_inj], hj]
  -- Suppose M₀₀ | rest
  intro ⟨q, hq⟩
  -- Apply aeval φ: φ(rest) = -M₀₁
  have hφ_rest : aeval φ (∑ j : Fin (n + 1),
      (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
      X ((0 : Fin (n + 2)), j.succ) *
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) =
      -det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2)))) := by
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, aeval_X, hφ_fix_minor, hφ_X]
    rw [Fin.sum_univ_succ]
    simp
  -- So M₀₀ | M₀₁
  have hdvd : det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) ∣
      det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 1)) := by
    have h1 : aeval φ (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) ∣
        aeval φ (∑ j : Fin (n + 1),
          (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
          X ((0 : Fin (n + 2)), j.succ) *
          det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) :=
      (aeval φ).toRingHom.map_dvd ⟨q, hq⟩
    rw [hφ_fix_minor 0, hφ_rest] at h1
    exact dvd_neg.mp h1
  -- Both are irreducible, so they must be associated
  have hassoc := hf_irr.associated_of_dvd hf1_irr hdvd
  -- Associated means M₀₁ = u * M₀₀ for unit u, so they have same vars
  obtain ⟨u, hu⟩ := hassoc
  -- Variable (1,1) is in vars(M₀₀) but not vars(M₀₁)
  have hmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∈
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))).vars := by
    -- Evaluation argument: if (1,1) ∉ vars, two evaluations agree but give 1 ≠ 0
    by_contra habs
    let g₁ : Fin (n + 2) × Fin (n + 2) → ℂ := fun ⟨i, j⟩ => if i = j then 1 else 0
    let g₂ : Fin (n + 2) × Fin (n + 2) → ℂ := Function.update g₁ (1, 1) 0
    have hag : ∀ i ∈ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove 0))).vars, g₁ i = g₂ i := by
      intro i hi
      exact (Function.update_of_ne (ne_of_mem_of_not_mem hi habs) _ _).symm
    -- g₁ and g₂ agree on vars of the submatrix det
    have heq : MvPolynomial.eval g₁
          (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) =
        MvPolynomial.eval g₂
          (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) :=
      MvPolynomial.eval₂Hom_congr' rfl (fun i hi _ => hag i hi) rfl
    -- eval g₁ gives det(I) = 1
    have hev1 : MvPolynomial.eval g₁
        (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) = 1 := by
      rw [show MvPolynomial.eval g₁ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove 0))) = det ((MvPolynomial.eval g₁).mapMatrix
        ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) from
        RingHom.map_det _ _]
      have : (MvPolynomial.eval g₁).mapMatrix
          ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) =
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
        ext i j
        simp [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply, genMatrix_apply,
          MvPolynomial.eval_X, g₁, Fin.succAbove_zero, Fin.succ_inj, one_apply]
      rw [this, det_one]
    -- eval g₂ gives 0 (first row is all zeros)
    have hev0 : MvPolynomial.eval g₂
        (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) = 0 := by
      rw [show MvPolynomial.eval g₂ (det ((genMatrix (n + 2)).submatrix Fin.succ
        (Fin.succAbove 0))) = det ((MvPolynomial.eval g₂).mapMatrix
        ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0))) from
        RingHom.map_det _ _]
      apply det_eq_zero_of_row_eq_zero (0 : Fin (n + 1))
      intro j
      -- Entry (0, j) of the evaluated matrix is g₂(Fin.succ 0, Fin.succ j)
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply,
        genMatrix_apply, MvPolynomial.eval_X, Fin.succAbove_zero]
      -- g₂(1, succ j) = 0: either j=0 so g₂(1,1)=0, or j≠0 so 1≠succ j
      simp only [g₂, g₁, Function.update_apply]
      simp only [Prod.mk.injEq, show (1 : Fin (n + 2)) = Fin.succ 0 from rfl, Fin.succ_inj]
      split
      · simp
      · next h =>
        simp only [not_and] at h
        simp [Ne.symm (h trivial)]
    exact absurd (hev1.symm.trans (heq.trans hev0)) one_ne_zero
  have hnotmem : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∉
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove (1 : Fin (n + 2))))).vars := by
    rw [submatrix_eq_rename]
    intro h
    obtain ⟨⟨a, b⟩, _, hab⟩ := mem_vars_rename _ _ h
    simp only [Prod.map, Prod.mk.injEq] at hab
    exact absurd hab.2 (Fin.succAbove_ne 1 b)
  -- M₀₀ * u = M₀₁, so vars(M₀₀) ⊆ vars(M₀₀ * u) = vars(M₀₁)
  have hmem' : ((1 : Fin (n + 2)), (1 : Fin (n + 2))) ∈
      (det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 1))).vars :=
    hu ▸ vars_subset_vars_mul_left hf_irr.ne_zero (Units.ne_zero u) hmem
  exact hnotmem hmem'

/-- The determinant of a generic n × n matrix is an irreducible polynomial.
(Etingof Lemma 4.10.3) -/
theorem Etingof.Lemma4_10_3 (n : ℕ) (hn : 0 < n) :
    Irreducible (det (genMatrix n)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- 1×1 case: det = X(0,0), which has totalDegree 1
      have hdet : det (genMatrix 1) = X ((0 : Fin 1), (0 : Fin 1)) := by
        unfold genMatrix; rw [det_fin_one]; rfl
      rw [hdet]
      exact irreducible_of_totalDegree_eq_one
        (totalDegree_X _)
        (fun x hx => isUnit_of_dvd_one (by
          have := hx (Finsupp.single ((0 : Fin 1), (0 : Fin 1)) 1)
          rwa [coeff_X] at this))
    | succ n =>
      -- (n+2)×(n+2) case. IH gives irreducibility for (n+1)×(n+1).
      have ih' := ih (by omega)
      -- Cofactor expansion: det = f * X(0,0) + g
      suffices heq : det (genMatrix (n + 2)) =
          det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove 0)) *
          X ((0 : Fin (n + 2)), (0 : Fin (n + 2))) +
          (∑ j : Fin (n + 1),
            (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ ((j : ℕ) + 1) *
            X ((0 : Fin (n + 2)), j.succ) *
            det ((genMatrix (n + 2)).submatrix Fin.succ (Fin.succAbove j.succ))) by
        rw [heq]
        exact irreducible_mul_X_add _ _ _
          (minor00_ne_zero n)
          (minor00_vars n)
          (rest_vars n)
          (minor00_isRelPrime n ih')
      -- Prove via det_succ_row_zero
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [genMatrix_apply, Fin.val_zero, pow_zero, one_mul]
      congr 1
      · ring
