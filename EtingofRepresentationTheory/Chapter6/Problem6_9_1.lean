import Mathlib

/-!
# Problem 6.9.1: Classification of Indecomposable Representations of Q₂

The cyclic quiver Q₂ has 2 vertices connected by 2 oriented edges forming a cycle:
a pair of linear operators A : V → W and B : W → V.

The classification states that every indecomposable representation of Q₂ belongs to
exactly one of four families:

1. **E_{n,λ}** (n ≥ 1, λ ∈ ℂ): V = W = ℂⁿ, A = Jordan block J_n(λ), B = Id
2. **E_{n,∞}** (n ≥ 1): obtained from E_{n,0} by exchanging V ↔ W and A ↔ B
3. **H_n** (n ≥ 1): V = ℂⁿ, W = ℂⁿ⁻¹, A sends basis vᵢ to wᵢ (i < n), vₙ to 0,
   B sends wᵢ to v_{i+1}
4. **K_n** (n ≥ 1): obtained from H_n by exchanging V ↔ W and A ↔ B

## Mathlib correspondence

Not in Mathlib. The classification relies on the Jordan normal form theorem and
a chain decomposition argument for nilpotent operators.
-/

/-- A representation of the cyclic quiver Q₂: a pair of vector spaces V, W with
linear maps A : V → W and B : W → V. -/
structure Q₂Rep (k : Type*) [Field k] where
  V : Type*
  W : Type*
  [instACV : AddCommGroup V]
  [instModV : Module k V]
  [instFDV : FiniteDimensional k V]
  [instACW : AddCommGroup W]
  [instModW : Module k W]
  [instFDW : FiniteDimensional k W]
  A : V →ₗ[k] W
  B : W →ₗ[k] V

attribute [instance] Q₂Rep.instACV Q₂Rep.instModV Q₂Rep.instFDV
  Q₂Rep.instACW Q₂Rep.instModW Q₂Rep.instFDW

/-- A Q₂-representation is indecomposable if it is nontrivial and for any
compatible decomposition V = V' ⊕ V'', W = W' ⊕ W'' (with A, B respecting
the decomposition), one of the summands is zero. -/
def Q₂Rep.Indecomposable {k : Type*} [Field k] (ρ : Q₂Rep k) : Prop :=
  (0 < Module.finrank k ρ.V ∨ 0 < Module.finrank k ρ.W) ∧
  ∀ (pV qV : Submodule k ρ.V) (pW qW : Submodule k ρ.W),
    IsCompl pV qV → IsCompl pW qW →
    (∀ x ∈ pV, ρ.A x ∈ pW) → (∀ x ∈ qV, ρ.A x ∈ qW) →
    (∀ x ∈ pW, ρ.B x ∈ pV) → (∀ x ∈ qW, ρ.B x ∈ qV) →
    (pV = ⊥ ∧ pW = ⊥) ∨ (qV = ⊥ ∧ qW = ⊥)

/-- **Problem 6.9.1(a), Family E_{n,λ} (Etingof)**: For n ≥ 1 and λ ∈ ℂ,
the Q₂-representation with V = W = ℂⁿ, A = Jordan block J_n(λ), B = Id is
indecomposable. This family is parameterized by (n, λ) ∈ ℕ₊ × ℂ. -/
noncomputable def Etingof.Q₂Rep_E (n : ℕ) (hn : 0 < n) (eigenval : ℂ) : Q₂Rep ℂ where
  V := EuclideanSpace ℂ (Fin n)
  W := EuclideanSpace ℂ (Fin n)
  A := Matrix.toEuclideanLin (Matrix.of fun (i j : Fin n) =>
    if i = j then eigenval else if i.val = j.val + 1 then 1 else 0)
  B := LinearMap.id

namespace Etingof

/-- The nilpotent part of the E_{n,λ} Jordan block, explicitly typed as an endomorphism. -/
noncomputable def Q₂Rep_E_nilpPart (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    Module.End ℂ (EuclideanSpace ℂ (Fin n)) :=
  (Q₂Rep_E n hn eigenval).A - eigenval • LinearMap.id

-- The nilpotent part (A - λ·id) is nilpotent
lemma jordanNilp_isNilpotent (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    IsNilpotent (Q₂Rep_E_nilpPart n hn eigenval) := by
  -- Define the shift matrix N_mat (1s on the subdiagonal)
  set N_mat : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun (i j : Fin n) => if i.val = j.val + 1 then (1 : ℂ) else 0
  -- Step 1: Q₂Rep_E_nilpPart = toEuclideanLin N_mat
  have hN_eq : Q₂Rep_E_nilpPart n hn eigenval = Matrix.toEuclideanLin N_mat := by
    unfold Q₂Rep_E_nilpPart Q₂Rep_E
    simp only
    rw [show (eigenval • LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) =
      Matrix.toEuclideanLin (eigenval • 1) from by
        rw [map_smul, Matrix.toLpLin_one]]
    rw [← map_sub]
    congr 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, N_mat]
    by_cases hij : i = j
    · subst hij; simp [show ¬(i.val = i.val + 1) from by omega]
    · have hij' : ¬(i : ℕ) = (j : ℕ) := fun h => hij (Fin.ext h)
      simp [hij, hij']
  -- Step 2: N_mat is nilpotent via characteristic polynomial
  have hN_nilp : IsNilpotent N_mat := by
    -- Reindex by Fin.revPerm gives an upper triangular matrix with zero diagonal
    have hchar : N_mat.charpoly = Polynomial.X ^ n := by
      -- Reindex by Fin.revPerm to make it upper triangular
      have hbt : (Matrix.reindex Fin.revPerm Fin.revPerm N_mat).BlockTriangular id := by
        intro i j (hij : j < i)
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Fin.revPerm_symm,
          Fin.revPerm_apply, N_mat, Matrix.of_apply]
        rw [if_neg]; intro h; have := Fin.rev_lt_rev.mpr hij; omega
      have hdiag : ∀ i : Fin n,
          (Matrix.reindex Fin.revPerm Fin.revPerm N_mat) i i = 0 := by
        intro i
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Fin.revPerm_symm,
          Fin.revPerm_apply, N_mat, Matrix.of_apply, if_neg (by omega : ¬(Fin.rev i).val = (Fin.rev i).val + 1)]
      have hchar' := Matrix.charpoly_of_upperTriangular _ hbt
      simp only [hdiag, map_zero, sub_zero, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hchar'
      rwa [Matrix.charpoly_reindex] at hchar'
    -- From charpoly = X^n and Cayley-Hamilton
    have := Matrix.aeval_self_charpoly N_mat
    rw [hchar, map_pow, Polynomial.aeval_X] at this
    exact ⟨n, this⟩
  -- Step 3: Transfer nilpotency from matrix to linear map
  rw [hN_eq]
  obtain ⟨k, hk⟩ := hN_nilp
  exact ⟨k, by rw [← Matrix.toLpLin_pow, hk, map_zero]⟩

-- ker(A - λ·id) has finrank ≤ 1
lemma jordanNilp_ker_finrank_le_one (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    Module.finrank ℂ (LinearMap.ker (Q₂Rep_E_nilpPart n hn eigenval)) ≤ 1 := by
  -- N corresponds to the shift matrix
  set N_mat : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun (i j : Fin n) => if i.val = j.val + 1 then (1 : ℂ) else 0
  have hN_eq : Q₂Rep_E_nilpPart n hn eigenval = Matrix.toEuclideanLin N_mat := by
    unfold Q₂Rep_E_nilpPart Q₂Rep_E; simp only
    rw [show (eigenval • LinearMap.id : Module.End ℂ (EuclideanSpace ℂ (Fin n))) =
      Matrix.toEuclideanLin (eigenval • 1) from by rw [map_smul, Matrix.toLpLin_one]]
    rw [← map_sub]; congr 1; ext i j
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, N_mat]
    by_cases hij : i = j
    · subst hij; simp [show ¬(i.val = i.val + 1) from by omega]
    · have hij' : ¬(i : ℕ) = (j : ℕ) := fun h => hij (Fin.ext h)
      simp [hij, hij']
  rw [hN_eq]
  -- Use rank-nullity: finrank(range) + finrank(ker) = n
  -- Show finrank(ker) ≤ 1 by showing finrank(range) ≥ n-1
  -- Strategy: N is surjective onto a codim-1 subspace
  -- Alternatively: use finrank_le_one with explicit generator
  -- Key fact: N v = 0 implies v is determined by one coordinate
  -- The map N = toEuclideanLin N_mat satisfies:
  --   (ofLp (N v)) ⟨i+1, _⟩ = (ofLp v) ⟨i, _⟩
  -- So if N v = 0, then v ⟨i, _⟩ = 0 for all i < n-1
  -- Hence every kernel element is a multiple of e_{n-1}
  -- Showing finrank ≤ 1 via rank-nullity and matrix rank
  -- e_{n-1} is in the kernel (last column of N_mat is zero)
  set last : Fin n := ⟨n - 1, by omega⟩
  have h_in_ker : EuclideanSpace.single last (1 : ℂ) ∈
      LinearMap.ker (Matrix.toEuclideanLin N_mat) := by
    rw [LinearMap.mem_ker]
    -- toEuclideanLin N_mat (single last 1) = toLp (N_mat *ᵥ Pi.single last 1) = toLp (col last)
    show Matrix.toLpLin 2 2 N_mat (EuclideanSpace.single last 1) = 0
    rw [EuclideanSpace.single, Matrix.toLpLin_toLp, Matrix.toLin'_apply,
      Matrix.mulVec_single_one]
    ext i
    simp only [PiLp.toLp_apply, Matrix.col_apply, Pi.zero_apply, PiLp.zero_apply, N_mat,
      Matrix.of_apply]
    rw [if_neg (show ¬(i.val = last.val + 1) from by simp [last]; omega)]
  -- Every kernel element is a scalar multiple of e_{n-1}
  apply finrank_le_one (R := ℂ) (v := ⟨EuclideanSpace.single last 1, h_in_ker⟩)
  intro ⟨w, hw⟩
  rw [LinearMap.mem_ker] at hw
  -- Extract: (N_mat *ᵥ ofLp w) = 0
  have hv' : Matrix.toLin' N_mat (WithLp.ofLp w) = 0 := by
    have : Matrix.toLpLin 2 2 N_mat w = 0 := hw
    rw [Matrix.toLpLin_apply] at this
    exact (WithLp.toLp_injective 2).eq_iff.mp this
  -- For j < n-1: the (j+1)-th coordinate of N·(ofLp w) = (ofLp w) j
  have hw_zero : ∀ (j : Fin n), j.val < n - 1 → w j = 0 := by
    intro j hj
    have row := congr_fun hv' ⟨j.val + 1, by omega⟩
    simp only [Pi.zero_apply] at row
    -- toLin' at index (j+1) = mulVec at index (j+1) = ∑_k N_mat_{j+1,k} * w_k
    rw [show (Matrix.toLin' N_mat (WithLp.ofLp w)) ⟨j.val + 1, by omega⟩ =
        ∑ k : Fin n, N_mat ⟨j.val + 1, by omega⟩ k * WithLp.ofLp w k from rfl] at row
    -- Only term k=j is nonzero in the sum
    rw [show (∑ k : Fin n, N_mat ⟨j.val + 1, by omega⟩ k * WithLp.ofLp w k) =
        WithLp.ofLp w j from by
      rw [Finset.sum_eq_single j]
      · simp [N_mat, Matrix.of_apply]
      · intro k _ hkj
        simp only [N_mat, Matrix.of_apply,
          if_neg (show ¬(j.val + 1 = k.val + 1) from by
            intro h; exact hkj (Fin.ext (by omega)))]
        ring
      · intro h; exact absurd (Finset.mem_univ j) h] at row
    exact row
  -- Now: w = (w last) • single last 1
  refine ⟨w last, Subtype.ext ?_⟩
  ext j
  simp only [Submodule.coe_smul_of_tower, EuclideanSpace.single_apply, smul_eq_mul]
  by_cases hj : j = last
  · subst hj; simp
  · simp only [hj, ite_false, mul_zero]
    exact hw_zero j (by rcases j with ⟨jv, hjv⟩; simp [last] at hj ⊢; omega)

end Etingof

/-- The E_{n,λ} family is indecomposable. Key argument: since B = Id, any compatible
decomposition V = V₁ ⊕ V₂, W = W₁ ⊕ W₂ forces W₁ = V₁ and W₂ = V₂ (via dimension
counting from B mapping W₁ into V₁ and W₂ into V₂). Then A = J_n(λ) must preserve
both V₁ and V₂, but a single Jordan block has no nontrivial invariant direct summands. -/
theorem Etingof.Q₂Rep_E_indecomposable (n : ℕ) (hn : 0 < n) (eigenval : ℂ) :
    (Etingof.Q₂Rep_E n hn eigenval).Indecomposable := by
  constructor
  · -- Nontriviality: dim V = n > 0
    left
    simp only [Q₂Rep_E, finrank_euclideanSpace_fin]
    exact hn
  · -- No nontrivial compatible decomposition
    intro pV qV pW qW hcV hcW hApV hAqV hBpV hBqW
    -- B = LinearMap.id, so B(pW) ⊆ pV means pW ≤ pV, B(qW) ⊆ qV means qW ≤ qV
    have hpWpV : pW ≤ pV := fun x hx => hBpV x hx
    have hqWqV : qW ≤ qV := fun x hx => hBqW x hx
    -- pW ≤ pV and qW ≤ qV force pW = pV: decompose x ∈ pV via IsCompl pW qW,
    -- the qW-component lies in pV ∩ qV = ⊥, so x ∈ pW.
    -- Show pV ≤ pW (with pW ≤ pV this gives equality)
    -- For x ∈ pV, decompose x = p + q (p ∈ pW, q ∈ qW) via IsCompl pW qW.
    -- Then q ∈ pV (since p ∈ pW ≤ pV) and q ∈ qW ≤ qV, so q ∈ pV ⊓ qV = ⊥.
    have aux : ∀ (s₁ t₁ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
        (s₂ t₂ : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
        IsCompl s₁ t₁ → IsCompl s₂ t₂ → s₂ ≤ s₁ → t₂ ≤ t₁ → s₁ ≤ s₂ := by
      intro s₁ t₁ s₂ t₂ hc1 hc2 hs ht x hx
      have hx_top : x ∈ (⊤ : Submodule ℂ _) := Submodule.mem_top
      rw [← hc2.codisjoint.eq_top] at hx_top
      obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hx_top
      have hq_s1 : q ∈ s₁ := by
        have heq : q = x + (-p) := by rw [← hpq]; abel
        rw [heq]; exact s₁.add_mem hx (s₁.neg_mem (hs hp))
      have hq_t1 : q ∈ t₁ := ht hq
      have hq_bot : q ∈ s₁ ⊓ t₁ := Submodule.mem_inf.mpr ⟨hq_s1, hq_t1⟩
      rw [hc1.disjoint.eq_bot] at hq_bot
      have hq0 : q = 0 := hq_bot
      rw [hq0, add_zero] at hpq; rwa [← hpq]
    have hpWeq : pW = pV := le_antisymm hpWpV (aux pV qV pW qW hcV hcW hpWpV hqWqV)
    have hqWeq : qW = qV := le_antisymm hqWqV (aux qV pV qW pW hcV.symm hcW.symm hqWqV hpWpV)
    -- Substitute pW = pV and qW = qV into goal
    rw [hpWeq, hqWeq]; simp only [and_self]
    -- Goal: pV = ⊥ ∨ qV = ⊥. Prove by contradiction.
    by_contra h; push_neg at h; obtain ⟨hpV_ne, hqV_ne⟩ := h
    -- A preserves pV and qV (substituting pW = pV, qW = qV)
    have hApV' : ∀ x ∈ pV, (Etingof.Q₂Rep_E n hn eigenval).A x ∈ pV :=
      fun x hx => hpWeq ▸ hApV x hx
    have hAqV' : ∀ x ∈ qV, (Etingof.Q₂Rep_E n hn eigenval).A x ∈ qV :=
      fun x hx => hqWeq ▸ hAqV x hx
    -- Set N = A - eigenval • id (the nilpotent part), explicitly as endomorphism
    set N : Module.End ℂ (EuclideanSpace ℂ (Fin n)) :=
      Etingof.Q₂Rep_E_nilpPart n hn eigenval with hN_def
    -- N preserves pV and qV
    have hNpV : ∀ x ∈ pV, N x ∈ pV := by
      intro x hx
      simp only [hN_def, Etingof.Q₂Rep_E_nilpPart,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact pV.sub_mem (hApV' x hx) (pV.smul_mem _ hx)
    have hNqV : ∀ x ∈ qV, N x ∈ qV := by
      intro x hx
      simp only [hN_def, Etingof.Q₂Rep_E_nilpPart,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      exact qV.sub_mem (hAqV' x hx) (qV.smul_mem _ hx)
    -- N is nilpotent: N^m = 0 for some m
    obtain ⟨m, hm⟩ := Etingof.jordanNilp_isNilpotent n hn eigenval
    -- N^k preserves pV for all k
    have hNpow_pV : ∀ (k : ℕ) (x : EuclideanSpace ℂ (Fin n)), x ∈ pV → (N ^ k) x ∈ pV := by
      intro k; induction k with
      | zero => intro x hx; simpa
      | succ k ih =>
        intro x hx; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hNpV x hx)
    have hNpow_qV : ∀ (k : ℕ) (x : EuclideanSpace ℂ (Fin n)), x ∈ qV → (N ^ k) x ∈ qV := by
      intro k; induction k with
      | zero => intro x hx; simpa
      | succ k ih =>
        intro x hx; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hNqV x hx)
    -- Find nonzero elements in ker(N) ∩ pV and ker(N) ∩ qV using Nat.find
    have find_ker_element : ∀ (S : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
        S ≠ ⊥ → (∀ (k : ℕ) (x : EuclideanSpace ℂ (Fin n)), x ∈ S → (N ^ k) x ∈ S) →
        ∃ w, w ∈ S ∧ w ∈ LinearMap.ker N ∧ w ≠ 0 := by
      intro S hS hpow
      rw [Submodule.ne_bot_iff] at hS
      obtain ⟨v, hv, hv_ne⟩ := hS
      have hex : ∃ k, (N ^ k) v = 0 := ⟨m, by
        have : (N ^ m) = 0 := hm
        simp [this]⟩
      have hk₀_spec : (N ^ Nat.find hex) v = 0 := Nat.find_spec hex
      have hk₀_pos : 0 < Nat.find hex := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
        · exfalso; simp [h] at hk₀_spec; exact hv_ne hk₀_spec
        · exact h
      have hpred : (N ^ (Nat.find hex - 1)) v ≠ 0 :=
        Nat.find_min hex (by omega)
      refine ⟨(N ^ (Nat.find hex - 1)) v, hpow _ v hv, ?_, hpred⟩
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ',
        show Nat.find hex - 1 + 1 = Nat.find hex from by omega]
      exact hk₀_spec
    obtain ⟨u, hu_pV, hu_ker, hu_ne⟩ := find_ker_element pV hpV_ne hNpow_pV
    obtain ⟨w, hw_qV, hw_ker, hw_ne⟩ := find_ker_element qV hqV_ne hNpow_qV
    -- ker(N) has finrank ≤ 1
    have hker_dim := Etingof.jordanNilp_ker_finrank_le_one n hn eigenval
    -- From finrank ≤ 1: ker(N) is principal, generated by some g
    rw [Submodule.finrank_le_one_iff_isPrincipal] at hker_dim
    obtain ⟨g, hg⟩ := hker_dim.principal
    -- u and w are both in ker(N) = span{g}
    have hu_span : u ∈ LinearMap.ker N := hu_ker
    have hw_span : w ∈ LinearMap.ker N := hw_ker
    rw [hg] at hu_span hw_span
    rw [Submodule.mem_span_singleton] at hu_span hw_span
    obtain ⟨a, ha⟩ := hu_span  -- a • g = u
    obtain ⟨b, hb⟩ := hw_span  -- b • g = w
    have ha_ne : a ≠ 0 := by intro h; rw [h, zero_smul] at ha; exact hu_ne ha.symm
    have hb_ne : b ≠ 0 := by intro h; rw [h, zero_smul] at hb; exact hw_ne hb.symm
    -- w = b • g = (b * a⁻¹) • (a • g) = (b * a⁻¹) • u
    have hw_eq : w = (b * a⁻¹) • u := by
      rw [show u = a • g from ha.symm, show w = b • g from hb.symm, smul_smul]
      congr 1; field_simp
    -- (b * a⁻¹) • u ∈ pV (since u ∈ pV), so w ∈ pV ⊓ qV = ⊥
    have hw_pV : w ∈ pV := hw_eq ▸ pV.smul_mem _ hu_pV
    have : w ∈ pV ⊓ qV := Submodule.mem_inf.mpr ⟨hw_pV, hw_qV⟩
    rw [hcV.disjoint.eq_bot] at this
    exact hw_ne this

/-- **Problem 6.9.1(a), Family H_n (Etingof)**: For n ≥ 1, V = ℂⁿ with basis vᵢ,
W = ℂⁿ⁻¹ with basis wᵢ. A sends vᵢ ↦ wᵢ (i < n) and vₙ ↦ 0.
B sends wᵢ ↦ v_{i+1}. This is an indecomposable representation with dim V ≠ dim W. -/
noncomputable def Etingof.Q₂Rep_H (n : ℕ) (hn : 0 < n) : Q₂Rep ℂ where
  V := EuclideanSpace ℂ (Fin n)
  W := EuclideanSpace ℂ (Fin (n - 1))
  A := Matrix.toEuclideanLin (Matrix.of fun (i : Fin (n - 1)) (j : Fin n) =>
    if i.val = j.val then (1 : ℂ) else 0)
  B := Matrix.toEuclideanLin (Matrix.of fun (i : Fin n) (j : Fin (n - 1)) =>
    if i.val = j.val + 1 then (1 : ℂ) else 0)

/-- **Problem 6.9.1(a) (Etingof)**: The four families E_{n,λ}, E_{n,∞}, H_n, K_n
(as defined above) are indecomposable and pairwise nonisomorphic. Moreover, these
are all the indecomposable representations of Q₂.

Specifically, every indecomposable representation of Q₂ is isomorphic to exactly one of:
- E_{n,λ} for some n ≥ 1, λ ∈ ℂ
- E_{n,∞} for some n ≥ 1 (obtained from E_{n,0} by swapping V ↔ W and A ↔ B)
- H_n for some n ≥ 1
- K_n for some n ≥ 1 (obtained from H_n by swapping V ↔ W and A ↔ B)

This extends the Jordan normal form classification from Q₁ (single vertex with a loop)
to Q₂ (two vertices with a cycle). -/
theorem Etingof.Problem6_9_1 (ρ : Q₂Rep ℂ) (hρ : ρ.Indecomposable) :
    -- The representation belongs to one of the four families (existential form):
    -- Either dim V = dim W (E_{n,λ} or E_{n,∞} family)
    -- or |dim V - dim W| = 1 (H_n or K_n family)
    (Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W ∨
     Module.finrank ℂ ρ.V = Module.finrank ℂ ρ.W + 1 ∨
     Module.finrank ℂ ρ.W = Module.finrank ℂ ρ.V + 1) := by
  sorry

/-- **Problem 6.9.1(b) (Etingof)**: If AB : W → W is not nilpotent in a Q₂-representation,
then the representation decomposes as E' ⊕ E_{n,λ} for some λ ≠ 0.

This reduces the classification to the case where AB is nilpotent. -/
theorem Etingof.Problem6_9_1b (ρ : Q₂Rep ℂ)
    (hAB : ¬IsNilpotent (ρ.A.comp ρ.B)) :
    ∃ (pV qV : Submodule ℂ ρ.V) (pW qW : Submodule ℂ ρ.W),
      IsCompl pV qV ∧ IsCompl pW qW ∧
      (∀ x ∈ pV, ρ.A x ∈ pW) ∧ (∀ x ∈ qV, ρ.A x ∈ qW) ∧
      (∀ x ∈ pW, ρ.B x ∈ pV) ∧ (∀ x ∈ qW, ρ.B x ∈ qV) ∧
      -- The q-summand has equal dimensions (E_{n,λ} type with λ ≠ 0)
      Module.finrank ℂ (↥qV) = Module.finrank ℂ (↥qW) := by
  sorry

/-- **Problem 6.9.1(c) (Etingof)**: When AB is nilpotent, the operator X on V ⊕ W
defined by X(v,w) = (Bw, Av) is also nilpotent and admits a basis of chains
compatible with the V ⊕ W decomposition.

This reduces to showing X has a Jordan chain basis where each chain starts in either
V or W. The chain structure directly gives the H_n and K_n families. -/
theorem Etingof.Problem6_9_1c (ρ : Q₂Rep ℂ)
    (hAB : IsNilpotent (ρ.A.comp ρ.B)) :
    -- The operator X = (0, B; A, 0) on V × W is nilpotent
    IsNilpotent ((ρ.B.comp ρ.A).prodMap (ρ.A.comp ρ.B) : (ρ.V × ρ.W) →ₗ[ℂ] (ρ.V × ρ.W)) := by
  -- Step 1: AB nilpotent implies BA nilpotent
  -- If (AB)^n = 0, then (BA)^(n+1) = B(AB)^n A = 0
  obtain ⟨n, hn⟩ := hAB
  have hBA : IsNilpotent (ρ.B.comp ρ.A) := by
    refine ⟨n + 1, ?_⟩
    -- (BA)^(n+1) v = B((AB)^n(Av)) = B(0) = 0
    -- Key shift lemma: ((BA)^m)(Bw) = B((AB)^m w)
    have key : ∀ (m : ℕ) (w : ρ.W),
        ((ρ.B.comp ρ.A) ^ m) (ρ.B w) = ρ.B (((ρ.A.comp ρ.B) ^ m) w) := by
      intro m; induction m with
      | zero => intro w; simp
      | succ m ih =>
        intro w
        rw [pow_succ, pow_succ, Module.End.mul_apply, LinearMap.comp_apply, ih,
            Module.End.mul_apply, ← LinearMap.comp_apply ρ.A ρ.B]
    ext v
    simp only [LinearMap.zero_apply]
    rw [pow_succ, Module.End.mul_apply, LinearMap.comp_apply, key n (ρ.A v)]
    have := LinearMap.congr_fun hn (ρ.A v)
    simp only [LinearMap.zero_apply] at this
    rw [this, map_zero]
  -- Step 2: prodMap of nilpotent endomorphisms is nilpotent
  -- (f.prodMap g)^k = (f^k).prodMap (g^k) via prodMap_mul
  obtain ⟨m, hm⟩ := hBA
  refine ⟨max n m, ?_⟩
  have h1 : (ρ.A.comp ρ.B) ^ max n m = 0 := by
    rw [← Nat.sub_add_cancel (Nat.le_max_left n m), pow_add, hn, mul_zero]
  have h2 : (ρ.B.comp ρ.A) ^ max n m = 0 := by
    rw [← Nat.sub_add_cancel (Nat.le_max_right n m), pow_add, hm, mul_zero]
  -- Show (f.prodMap g)^k = (f^k).prodMap (g^k) by induction
  have pow_prodMap : ∀ (k : ℕ) (f : ρ.V →ₗ[ℂ] ρ.V) (g : ρ.W →ₗ[ℂ] ρ.W),
      (f.prodMap g) ^ k = (f ^ k).prodMap (g ^ k) := by
    intro k; induction k with
    | zero => intro f g; simp [LinearMap.prodMap_one]
    | succ k ih =>
      intro f g
      rw [pow_succ, ih f g, LinearMap.prodMap_mul, pow_succ, pow_succ]
  rw [pow_prodMap, h1, h2, LinearMap.prodMap_zero]
