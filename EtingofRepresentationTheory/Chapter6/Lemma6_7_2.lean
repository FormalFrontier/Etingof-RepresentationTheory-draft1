import EtingofRepresentationTheory.Chapter6.Definition6_1_4
import EtingofRepresentationTheory.Chapter6.Definition6_4_1
import EtingofRepresentationTheory.Chapter6.Definition6_4_10
import EtingofRepresentationTheory.Chapter6.Definition6_7_1
import EtingofRepresentationTheory.Chapter6.Corollary6_8_2

/-!
# Lemma 6.7.2: Coxeter Element Produces Negative Coefficients

For β = Σᵢ kᵢ αᵢ with kᵢ ≥ 0 (not all zero), some power cᴺβ has a negative
coefficient. The proof uses: (1) 1 is not an eigenvalue of the Coxeter element
(telescoping argument), (2) B-preservation gives finite orbits under nonneg
assumption, (3) sum of periodic orbit is a fixed point hence zero, contradicting
β ≠ 0.
-/

/-- The action of the Coxeter element on a vector in ℤⁿ. -/
def Etingof.coxeterAction (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : Fin n → ℤ :=
  let A := Etingof.cartanMatrix n adj
  (List.ofFn (fun i : Fin n => Etingof.simpleReflection n A i)).foldr
    (· ∘ ·) id v

/-- Iterated action of the Coxeter element: c^N applied to a vector. -/
def Etingof.coxeterActionIter (n : ℕ) (adj : Matrix (Fin n) (Fin n) ℤ)
    (N : ℕ) (v : Fin n → ℤ) : Fin n → ℤ :=
  (Etingof.coxeterAction n adj)^[N] v

namespace Etingof

variable {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}

/-! ## B-preservation -/

private lemma cartanMatrix_isSymm (hadj : adj.IsSymm) :
    (cartanMatrix n adj).IsSymm := by
  rw [Matrix.IsSymm]; unfold cartanMatrix
  simp only [Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one]; rw [hadj.eq]

private lemma cartanMatrix_diag_eq_two
    (hDynkin : IsDynkinDiagram n adj) (i : Fin n) :
    cartanMatrix n adj i i = 2 := by
  simp only [cartanMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one,
    hDynkin.2.1 i, sub_zero]; norm_num

private lemma simpleRoot_B_eq_two
    (hDynkin : IsDynkinDiagram n adj) (i : Fin n) :
    dotProduct (Pi.single i 1)
      ((cartanMatrix n adj).mulVec (Pi.single i 1)) = 2 := by
  simp [dotProduct, Pi.single_apply, Matrix.mulVec,
    Finset.sum_ite_eq', Finset.mem_univ,
    cartanMatrix_diag_eq_two hDynkin i]

private lemma foldr_preserves_B
    (fs : List ((Fin n → ℤ) → (Fin n → ℤ)))
    (hfs : ∀ f ∈ fs, ∀ u : Fin n → ℤ,
      dotProduct (f u) ((cartanMatrix n adj).mulVec (f u)) =
      dotProduct u ((cartanMatrix n adj).mulVec u))
    (v : Fin n → ℤ) :
    dotProduct (fs.foldr (· ∘ ·) id v)
      ((cartanMatrix n adj).mulVec (fs.foldr (· ∘ ·) id v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.foldr_cons, Function.comp_apply]
    rw [hfs f (List.mem_cons_self ..)]
    exact ih fun g hg => hfs g (List.mem_cons.mpr (Or.inr hg))

private lemma coxeterAction_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ) :
    dotProduct (coxeterAction n adj v)
      ((cartanMatrix n adj).mulVec (coxeterAction n adj v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  unfold coxeterAction; apply foldr_preserves_B
  intro f hf u; simp only [List.mem_ofFn] at hf
  obtain ⟨i, rfl⟩ := hf
  exact simpleReflection_preserves_bilinearForm _
    (cartanMatrix_isSymm hDynkin.1) i
    (simpleRoot_B_eq_two hDynkin i) u

private lemma coxeterActionIter_preserves_B
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ)
    (N : ℕ) :
    dotProduct (coxeterActionIter n adj N v)
      ((cartanMatrix n adj).mulVec
        (coxeterActionIter n adj N v)) =
    dotProduct v ((cartanMatrix n adj).mulVec v) := by
  unfold coxeterActionIter; induction N with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [coxeterAction_preserves_B hDynkin, ih]

/-! ## Fixed point implies zero -/

private lemma simpleReflection_apply_ne
    (v : Fin n → ℤ) (i j : Fin n) (hij : j ≠ i) :
    simpleReflection n (cartanMatrix n adj) i v j = v j := by
  simp [simpleReflection, rootReflection, Pi.sub_apply,
    Pi.smul_apply, Pi.single_apply, hij]

private lemma simpleReflection_apply_self
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ)
    (i : Fin n) :
    simpleReflection n (cartanMatrix n adj) i v i =
    v i - (cartanMatrix n adj).mulVec v i := by
  set A := cartanMatrix n adj
  have hAsymm := cartanMatrix_isSymm hDynkin.1
  have symm : ∀ j, A j i = A i j :=
    fun j => congr_fun (congr_fun hAsymm i) j
  have key : dotProduct v (A.mulVec (Pi.single i 1)) =
      (A.mulVec v) i := by
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun j _ => by rw [symm j]; ring
  simp only [simpleReflection, rootReflection, Pi.sub_apply,
    Pi.smul_apply, Pi.single_apply, if_pos rfl, mul_one, key,
    ite_true, smul_eq_mul]

/-- Intermediate state after applying reflections n-1, n-2, ..., n-m
to v. w(0) = v, w(m+1) = s_{n-1-m}(w(m)), w(n) = c(v). -/
private def intermediateState
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) : ℕ → Fin n → ℤ
  | 0 => v
  | m + 1 =>
    if h : m < n then
      simpleReflection n A ⟨n - 1 - m, by omega⟩
        (intermediateState A v m)
    else intermediateState A v m

private lemma intermediateState_zero (A : Matrix (Fin n) (Fin n) ℤ)
    (v : Fin n → ℤ) : intermediateState A v 0 = v := rfl

private lemma intermediateState_succ
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) (m : ℕ)
    (hm : m < n) :
    intermediateState A v (m + 1) =
    simpleReflection n A ⟨n - 1 - m, by omega⟩
      (intermediateState A v m) :=
  dif_pos hm

/-- Reflections at index > j don't affect coordinate j. -/
private lemma intermediateState_coord_low
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) (m : ℕ)
    (j : Fin n) (hj : j.val < n - m) :
    intermediateState A v m j = v j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [intermediateState_succ A v m (by omega)]
    have hne : j ≠ ⟨n - 1 - m, by omega⟩ := by
      intro heq; simp [Fin.ext_iff] at heq; omega
    simp only [simpleReflection, rootReflection, Pi.sub_apply,
      Pi.smul_apply, Pi.single_apply, hne, ite_false, smul_zero, sub_zero]
    exact ih (by omega)

set_option maxHeartbeats 800000 in
-- intermediateState recursion needs many heartbeats to unfold
/-- For m ≤ n, intermediateState m equals the foldr of the last m reflections. -/
private lemma intermediateState_eq_drop_foldr
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) (m : ℕ) (hm : m ≤ n) :
    intermediateState A v m =
    ((List.ofFn (fun i : Fin n => simpleReflection n A i)).drop (n - m)).foldr
      (· ∘ ·) id v := by
  induction m with
  | zero =>
    simp only [intermediateState]
    have : n - 0 = n := by omega
    rw [this]
    have hdrop : (List.ofFn (fun i : Fin n => simpleReflection n A i)).drop n = [] :=
      List.drop_eq_nil_of_le (by simp [List.length_ofFn])
    simp [hdrop]
  | succ k ih =>
    rw [intermediateState_succ A v k (by omega), ih (by omega)]
    have hidx : n - (k + 1) < (List.ofFn (fun i : Fin n => simpleReflection n A i)).length :=
      by simp [List.length_ofFn]; omega
    have hdrop := List.drop_eq_getElem_cons hidx
    conv_rhs => rw [hdrop, List.foldr_cons, Function.comp_apply]
    have hstep : n - (k + 1) + 1 = n - k := by omega
    rw [hstep]
    have heq : (⟨n - 1 - k, by omega⟩ : Fin n) = ⟨n - (k + 1), by omega⟩ :=
      Fin.ext (show n - 1 - k = n - (k + 1) by omega)
    rw [heq]; congr 1
    simp [List.getElem_ofFn]

/-- intermediateState n = coxeterAction. -/
private lemma intermediateState_full
    (v : Fin n → ℤ) :
    intermediateState (cartanMatrix n adj) v n =
    coxeterAction n adj v := by
  unfold coxeterAction
  rw [intermediateState_eq_drop_foldr _ v n le_rfl]
  simp

/-- Coordinate j is stable from step m₁ to m₂ when j is not the index
of any reflection applied between those steps. -/
private lemma intermediateState_coord_stable
    (A : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ)
    (m₁ m₂ : ℕ) (hle : m₁ ≤ m₂) (hm₂ : m₂ ≤ n)
    (j : Fin n) (hj : j.val ≥ n - m₁) :
    intermediateState A v m₂ j = intermediateState A v m₁ j := by
  induction m₂ with
  | zero => simp [Nat.le_zero.mp hle]
  | succ p ih =>
    by_cases hp : m₁ = p + 1
    · rw [hp]
    · have hple : m₁ ≤ p := by omega
      rw [intermediateState_succ A v p (by omega)]
      have hne : j ≠ ⟨n - 1 - p, by omega⟩ := by
        intro heq; simp [Fin.ext_iff] at heq; omega
      simp only [simpleReflection, rootReflection, Pi.sub_apply,
        Pi.smul_apply, Pi.single_apply, hne, ite_false, smul_zero, sub_zero]
      exact ih hple (by omega)

set_option maxHeartbeats 800000 in
-- telescoping argument requires many heartbeats for unfolding
/-- If c(v) = v then v = 0.

The telescoping argument: all intermediateState m = v by induction,
extracting (A·v)ₖ = 0 at each step from the fixed-point condition. -/
private lemma coxeterAction_fixed_zero
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ)
    (hfixed : coxeterAction n adj v = v) : v = 0 := by
  set A := cartanMatrix n adj with hA_def
  have hA_symm := cartanMatrix_isSymm hDynkin.1
  -- Show Av = 0, then positive definiteness gives v = 0
  suffices hAv : A.mulVec v = 0 by
    by_contra hv
    have hpos := hDynkin.2.2.2.2 v hv
    rw [show A = (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) from rfl] at hAv
    rw [hAv, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  have hfull : intermediateState A v n = v := by
    rw [intermediateState_full]; exact hfixed
  -- Helper: dotProduct v (A.mulVec eᵢ) = (A.mulVec v) i (by A-symmetry)
  have hcoeff : ∀ i : Fin n,
      dotProduct v (A.mulVec (Pi.single i 1)) = (A.mulVec v) i := by
    intro i
    simp only [dotProduct, Matrix.mulVec, Pi.single_apply,
      mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl; intro p _
    have h := congr_fun (congr_fun hA_symm i) p
    simp only [Matrix.transpose_apply] at h
    change A p i = A i p at h
    rw [h, mul_comm]
  -- Helper: if (Av)_i = 0 then s_i(v) = v
  have hrefl_id : ∀ i : Fin n, (A.mulVec v) i = 0 →
      simpleReflection n A i v = v := by
    intro i hi
    change v - dotProduct v (A.mulVec (Pi.single i 1)) • Pi.single i 1 = v
    rw [hcoeff i, hi, zero_smul, sub_zero]
  -- Prove all intermediateState A v m = v by induction on m
  suffices hall : ∀ m, m ≤ n → intermediateState A v m = v by
    ext k; simp only [Pi.zero_apply]
    have hstep := intermediateState_succ A v (n - 1 - k.val) (by omega)
    rw [hall (n - 1 - k.val) (by omega),
      hall (n - 1 - k.val + 1) (by omega)] at hstep
    have hfin_eq : (⟨n - 1 - (n - 1 - k.val), by omega⟩ : Fin n) = k :=
      Fin.ext (show n - 1 - (n - 1 - k.val) = k.val by omega)
    rw [hfin_eq] at hstep
    have hself := simpleReflection_apply_self hDynkin v k
    have : v k = simpleReflection n A k v k := congr_fun hstep k
    rw [hself] at this; linarith
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [intermediateState_succ A v m (by omega), ih (by omega)]
    set j : Fin n := ⟨n - 1 - m, by omega⟩
    -- intermediateState n at coord j = v j (from hfull)
    -- intermediateState(m+1) at coord j = (s_j v) j (after ih rewrite)
    -- These are equal by coord stability (reflections < j don't affect coord j)
    have hstable : intermediateState A v n j =
        intermediateState A v (m + 1) j :=
      intermediateState_coord_stable A v (m + 1) n (by omega) le_rfl j
        (by simp [j]; omega)
    rw [hfull] at hstable
    -- v j = (s_j v) j = v j - (Av)_j, so (Av)_j = 0
    have hAv_j : (A.mulVec v) j = 0 := by
      have heval : intermediateState A v (m + 1) j =
          simpleReflection n A j (intermediateState A v m) j := by
        rw [intermediateState_succ A v m (by omega)]
      rw [ih (by omega)] at heval
      rw [simpleReflection_apply_self hDynkin v j] at heval
      linarith [hstable]
    exact hrefl_id j hAv_j

/-! ## Orbit finiteness -/

/-- For nonneg v with B(v,v) = K, each vᵢ² ≤ 2K.
Uses: B(v,v) = 2Σvᵢ² - Σ_{i~j} vᵢvⱼ ≥ ½Σvᵢ² (Dynkin degree ≤ 3). -/
private lemma nonneg_coord_sq_le_two_B
    (hDynkin : IsDynkinDiagram n adj) (v : Fin n → ℤ)
    (hv_nonneg : ∀ i, 0 ≤ v i) (K : ℤ)
    (hK : dotProduct v ((cartanMatrix n adj).mulVec v) = K)
    (i : Fin n) : v i * v i ≤ 2 * K := by
  -- B(v,v) = 2Σvᵢ² - Σ_{adj(i,j)=1} vᵢvⱼ ≥ 2vᵢ² - Σ_{j~i} vᵢvⱼ
  -- For vᵢ ≥ 0: vᵢvⱼ ≤ (vᵢ² + vⱼ²)/2
  -- Σ_{j~i} vᵢvⱼ ≤ Σ_{j~i} (vᵢ² + vⱼ²)/2 ≤ (deg(i)/2)Σvⱼ²
  -- But we just need: B(v,v) ≥ 2vᵢ² - vᵢ · Σⱼ adj(i,j) vⱼ
  -- ≥ 2vᵢ² - vᵢ · (Σⱼ vⱼ) is too weak.
  -- Simpler: vᵢ² ≤ Σvⱼ² ≤ ... relate to B.
  -- B(v,v) = 2Σvⱼ² - Σ_{(a,b)∈E} vₐvᵦ.
  -- For nonneg v, Σ vₐvᵦ ≥ 0, so B ≤ 2Σvⱼ².
  -- Thus Σvⱼ² ≥ B/2 = K/2. This gives LOWER bound.
  -- For UPPER bound: use B > 0 and expand.
  -- B(v,v) = Σⱼ vⱼ · ((2I-adj)v)ⱼ = Σⱼ vⱼ(2vⱼ - Σₖ adj(j,k)vₖ)
  -- The j=i term: vᵢ(2vᵢ - Σₖ adj(i,k)vₖ)
  -- All other terms: Σ_{j≠i} vⱼ(2vⱼ - Σₖ adj(j,k)vₖ)
  -- Since v nonneg and B(eⱼ, v) might be negative...
  -- Let's just use: for nonneg integer vectors,
  -- B(v,v) = vᵀ(2I-adj)v ≥ 2vᵢ² (when 2vᵢ ≥ Σ_{k~i} vₖ)
  -- ... not always true.
  -- SIMPLEST: B(v,v) ≥ 0 (positive semidefinite at least).
  -- And v ≠ 0 implies B(v,v) ≥ 2 (by evenness + positivity).
  -- But we need vᵢ² ≤ 2K, not K ≥ 2.
  -- Actually, direct: let e = Pi.single i 1.
  -- B(v,v) ≥ B(vᵢ·eᵢ, vᵢ·eᵢ) - ... no, B is not monotone.
  -- Use Cauchy-Schwarz: B(v, eᵢ)² ≤ B(v,v)·B(eᵢ,eᵢ) = 2K.
  -- But B(v,eᵢ) = (Av)ᵢ, not vᵢ.
  -- PRAGMATIC: sorry this for now, it's a secondary lemma.
  sorry

/-- (Etingof Lemma 6.7.2) For a positive linear combination of simple roots
(not all zero), some power of the Coxeter element produces a negative
coefficient. -/
theorem Lemma6_7_2
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hDynkin : IsDynkinDiagram n adj)
    (β : Fin n → ℤ) (hβ_nonneg : ∀ i, 0 ≤ β i)
    (hβ_nonzero : β ≠ 0) :
    ∃ N : ℕ, ∃ i : Fin n,
      coxeterActionIter n adj N β i < 0 := by
  by_contra h; push_neg at h
  set K := dotProduct β ((cartanMatrix n adj).mulVec β)
  have hK_pos : 0 < K := by
    change 0 < dotProduct β ((cartanMatrix n adj).mulVec β)
    rw [show (cartanMatrix n adj) =
      (2 • (1 : Matrix (Fin n) (Fin n) ℤ) - adj) from rfl]
    exact hDynkin.2.2.2.2 β hβ_nonzero
  have hB_iter : ∀ N, dotProduct (coxeterActionIter n adj N β)
      ((cartanMatrix n adj).mulVec
        (coxeterActionIter n adj N β)) = K :=
    fun N => coxeterActionIter_preserves_B hDynkin β N
  -- Periodicity: orbit is finite since coords bounded
  have hperiod :
      ∃ M : ℕ, 0 < M ∧ coxeterActionIter n adj M β = β := by
    sorry -- pigeonhole on bounded nonneg integer vectors
  obtain ⟨M, hM_pos, hM_eq⟩ := hperiod
  -- Sum is a fixed point of c
  set S := ∑ k ∈ Finset.range M,
    coxeterActionIter n adj k β
  -- c(S) = c(Σ c^k β) = Σ c^{k+1} β
  --      = Σ_{k=1}^{M} c^k β = Σ_{k=0}^{M-1} c^k β = S
  -- (shifting indices, using c^M β = β)
  have hS_fixed : coxeterAction n adj S = S := by
    change coxeterAction n adj
      (∑ k ∈ Finset.range M, coxeterActionIter n adj k β) =
      ∑ k ∈ Finset.range M, coxeterActionIter n adj k β
    sorry -- linearity of coxeterAction + index shift
  have hS_zero := coxeterAction_fixed_zero hDynkin S hS_fixed
  -- But S has a positive coordinate
  have hβ_pos : ∃ i, 0 < β i := by
    by_contra hall; push_neg at hall
    exact hβ_nonzero
      (funext fun i => le_antisymm (hall i) (hβ_nonneg i))
  obtain ⟨i, hi⟩ := hβ_pos
  have hSi : 0 < S i := by
    change 0 < (∑ k ∈ Finset.range M,
      coxeterActionIter n adj k β) i
    rw [Finset.sum_apply]
    calc 0 < β i := hi
      _ = coxeterActionIter n adj 0 β i := rfl
      _ ≤ ∑ k ∈ Finset.range M,
          coxeterActionIter n adj k β i :=
        Finset.single_le_sum (fun k _ => h k i)
          (Finset.mem_range.mpr hM_pos)
  have hSi_eq : S i = 0 := by
    have := congr_fun hS_zero i; simp only [Pi.zero_apply] at this; exact this
  linarith

end Etingof
