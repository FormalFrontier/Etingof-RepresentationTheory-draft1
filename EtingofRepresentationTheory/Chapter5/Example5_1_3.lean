import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1

/-!
# Example 5.1.3: Type Classification for Specific Groups

Examples of the real/complex/quaternionic classification (Definition 5.1.1):

1. ℤ/nℤ: representations of complex type come in conjugate pairs {V, V*}; the only
   real-type ones are the trivial representation and (for `n` even) the sign
   representation `m ↦ (-1)^m`.
2. S₃: all three irreducible representations `ℂ₊, ℂ₋, ℂ²` are of real type.
3. S₄: all five irreducible representations are of real type.
4. A₅: all five irreducible representations are of real type.
5. Q₈: the 1-dimensional representations are of real type and the 2-dimensional
   one is of quaternionic type.

## Mathlib correspondence

Uses `ZMod`, `Equiv.Perm (Fin n)`, `alternatingGroup`, and `QuaternionGroup` from
Mathlib. Irreducibility is expressed as `IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule`,
and the type predicates `Etingof.IsRealType` / `Etingof.IsQuaternionicType` come from
Definition 5.1.1.
-/

/-- For `ℤ/nℤ` (written multiplicatively), a 1-dimensional representation `ρ` on `ℂ`
whose character `g ↦ ρ g 1` takes some value other than `±1` is **not** of real type
— i.e. it is of complex type. The only real-type characters are those landing in
`{1, -1}`, namely the trivial representation and (for `n` even) the sign representation.
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_ZMod
    {n : ℕ} [NeZero n]
    (ρ : Representation ℂ (Multiplicative (ZMod n)) ℂ)
    (h : ∃ g : Multiplicative (ZMod n), ρ g 1 ≠ 1 ∧ ρ g 1 ≠ -1) :
    ¬ Etingof.IsRealType ρ := by
  -- A `G`-invariant bilinear form `B` on a 1-dimensional character `χ` satisfies
  -- `χ(g)² B(v,w) = B(v,w)`, forcing `χ(g)² = 1`, i.e. `χ(g) ∈ {1, -1}`, for all `g`
  -- where `B` is nondegenerate. The hypothesis `h` exhibits a `g` violating this.
  rintro ⟨B, _hsym, hnondeg, hinv⟩
  obtain ⟨g, hg1, hg2⟩ := h
  set χ : ℂ := ρ g 1 with hχ
  -- Every bilinear form on the 1-dimensional space `ℂ` is `B a b = a·b·(B 1 1)`.
  have key : ∀ a b : ℂ, B a b = a * b * B 1 1 := by
    intro a b
    have step : (B a) b = a • (b • B 1 1) := by
      have h1 : (B a) b = (B (a • (1:ℂ))) (b • (1:ℂ)) := by simp
      rw [h1, show B (a • (1:ℂ)) = a • B 1 from map_smul B a 1,
        LinearMap.smul_apply, show (B 1) (b • (1:ℂ)) = b • (B 1) 1 from map_smul (B 1) b 1]
    rw [step, smul_eq_mul, smul_eq_mul, mul_assoc]
  -- Nondegeneracy forces the single coefficient `B 1 1` to be nonzero.
  have hc : B 1 1 ≠ 0 := by
    intro hc0
    have : (1 : ℂ) = 0 := hnondeg 1 (fun w => by rw [key, hc0, mul_zero])
    exact one_ne_zero this
  -- `G`-invariance at `g` (with `v = w = 1`) gives `χ² · (B 1 1) = B 1 1`.
  have hinvg : χ * χ * B 1 1 = B 1 1 := by
    have := hinv g 1 1
    rw [← hχ, key] at this
    exact this
  -- Cancelling the nonzero coefficient yields `χ² = 1`, hence `χ = ±1` — contradiction.
  have hχχ : χ * χ = 1 := by
    have : χ * χ * B 1 1 = 1 * B 1 1 := by rw [one_mul]; exact hinvg
    exact mul_right_cancel₀ hc this
  rcases mul_self_eq_one_iff.mp hχχ with h1 | h1
  · exact hg1 h1
  · exact hg2 h1

/-- All irreducible representations of `S₃` are of real type: any simple
`ℂ[S₃]`-module carries a nondegenerate `S₃`-invariant symmetric bilinear form.
(The character values of `S₃` are all integers.) (Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_S3
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin 3)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 3))) ρ.asModule) :
    Etingof.IsRealType ρ := by
  -- All three irreducibles `ℂ₊, ℂ₋, ℂ²` have integer (hence real) character values,
  -- so their Frobenius–Schur indicator is `1`, i.e. they are of real type.
  sorry

/-- All irreducible representations of `S₄` are of real type. (Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_S4
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin 4)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) ρ.asModule) :
    Etingof.IsRealType ρ := by
  -- The five irreducibles `ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋` all have real character values.
  sorry

/-- All irreducible representations of `A₅` are of real type. (Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_A5
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (alternatingGroup (Fin 5)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (alternatingGroup (Fin 5))) ρ.asModule) :
    Etingof.IsRealType ρ := by
  -- The five irreducibles `ℂ, ℂ³₊, ℂ³₋, ℂ⁴, ℂ⁵` all have real character values.
  sorry

namespace Etingof.Q8

open Matrix Complex QuaternionGroup

/-- The order-4 generator `a ↦ A`, with `A = diag(√-1, -√-1)`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- The second generator `x ↦ X`, with `X = [[0,1],[-1,0]]`. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

@[simp] lemma det_A : A.det = 1 := by
  simp [A, Matrix.det_fin_two_of, Complex.I_mul_I]

@[simp] lemma det_X : X.det = 1 := by
  simp [X, Matrix.det_fin_two_of]

lemma A_sq : A ^ 2 = -1 := by
  rw [pow_two]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_fin_two]

lemma A_pow_four : A ^ 4 = 1 := by
  have h : A ^ 4 = (A ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, A_sq, neg_one_sq]

/-- `X² = A² = -1`. -/
lemma X_mul_X : X * X = A ^ 2 := by
  rw [A_sq]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

/-- The relation `A·X = X·A³` (equivalently `X⁻¹AX = A⁻¹`). -/
lemma A_mul_X : A * X = X * A ^ 3 := by
  have h3 : A ^ 3 = !![(-Complex.I), 0; 0, Complex.I] := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, A_sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  rw [h3]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, X, Matrix.mul_apply, Fin.sum_univ_two]

/-- `A^a` depends only on `a` mod 4. -/
lemma A_pow_congr {a b : ℕ} (h : (a : ZMod 4) = (b : ZMod 4)) : A ^ a = A ^ b := by
  have e : a % 4 = b % 4 := (ZMod.natCast_eq_natCast_iff a b 4).mp h
  conv_lhs => rw [← Nat.div_add_mod a 4]
  conv_rhs => rw [← Nat.div_add_mod b 4]
  rw [pow_add, pow_add, pow_mul, pow_mul, A_pow_four, one_pow, one_pow, e]

/-- Move a power of `A` across `X`: `A^m · X = X · A^{3m}`. -/
lemma A_pow_mul_X : ∀ m : ℕ, A ^ m * X = X * A ^ (3 * m)
  | 0 => by simp
  | (m + 1) => by
    rw [pow_succ, mul_assoc, A_mul_X, ← mul_assoc, A_pow_mul_X m, mul_assoc, ← pow_add,
      show 3 * m + 3 = 3 * (m + 1) from by ring]

/-- Conjugating `A^m` by `X`: `X · A^m · X = A^{2 + 3m}`. -/
lemma X_mul_A_pow_mul_X (m : ℕ) : X * A ^ m * X = A ^ (2 + 3 * m) := by
  rw [mul_assoc, A_pow_mul_X, ← mul_assoc, X_mul_X, ← pow_add]

/-- The underlying matrix-valued function of the representation. -/
noncomputable def Mfun : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a k => A ^ k.val
  | .xa k => X * A ^ k.val

/-- The representation `Q₈ → GL₂(ℂ)` as a monoid homomorphism into matrices. -/
noncomputable def Mhom : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := Mfun
  map_one' := by
    show Mfun 1 = 1
    rw [QuaternionGroup.one_def]; simp [Mfun]
  map_mul' := by
    rintro (i | i) (j | j)
    · show Mfun (a i * a j) = Mfun (a i) * Mfun (a j)
      rw [QuaternionGroup.a_mul_a]
      simp only [Mfun]
      rw [← pow_add]
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · show Mfun (a i * xa j) = Mfun (a i) * Mfun (xa j)
      rw [QuaternionGroup.a_mul_xa]
      simp only [Mfun]
      rw [← mul_assoc, A_pow_mul_X, mul_assoc, ← pow_add]
      congr 1
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)
    · show Mfun (xa i * a j) = Mfun (xa i) * Mfun (a j)
      rw [QuaternionGroup.xa_mul_a]
      simp only [Mfun]
      rw [mul_assoc, ← pow_add]
      congr 1
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · show Mfun (xa i * xa j) = Mfun (xa i) * Mfun (xa j)
      rw [QuaternionGroup.xa_mul_xa]
      simp only [Mfun]
      rw [← mul_assoc (X * A ^ i.val) X (A ^ j.val), X_mul_A_pow_mul_X, ← pow_add]
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)

/-- The 2-dimensional representation of `Q₈` on `Fin 2 → ℂ`. -/
noncomputable def rho : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) where
  toFun g := Matrix.toLinAlgEquiv' (Mhom g)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

lemma rho_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    rho g v = (Mhom g).mulVec v := by
  simp [rho, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

end Etingof.Q8

/-- The 2-dimensional irreducible representation of `Q₈ = QuaternionGroup 2` is of
quaternionic type: there is a simple `ℂ[Q₈]`-module structure on `Fin 2 → ℂ`
admitting a nondegenerate `Q₈`-invariant skew-symmetric bilinear form.
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_Q8 :
    ∃ ρ : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ),
      IsSimpleModule (MonoidAlgebra ℂ (QuaternionGroup 2)) ρ.asModule ∧
      Etingof.IsQuaternionicType ρ := by
  -- The 2-dimensional irrep uses the Pauli-type matrices `ρ(i) = [[0,1],[-1,0]]`,
  -- `ρ(j) = [[√-1,0],[0,-√-1]]`, `ρ(k) = [[0,-√-1],[-√-1,0]]`. Its FS indicator is
  -- `-1`, witnessed by the invariant skew form `[[0,1],[-1,0]]`.
  refine ⟨Etingof.Q8.rho, ?_, ?_⟩
  · -- Simplicity: the only `ρ`-invariant subspaces are `⊥` and `⊤`, since the diagonal
    -- generator `A` and the swap `X` share no common eigenline.
    -- Evaluate the two generators on an arbitrary vector.
    have hAv : ∀ v : Fin 2 → ℂ, Etingof.Q8.rho (QuaternionGroup.a 1) v
        = ![Complex.I * v 0, -Complex.I * v 1] := by
      intro v
      rw [Etingof.Q8.rho_apply]
      show (Etingof.Q8.Mfun (QuaternionGroup.a 1)).mulVec v = _
      simp only [Etingof.Q8.Mfun, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
      funext i; fin_cases i <;>
        simp [Etingof.Q8.A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hXv : ∀ v : Fin 2 → ℂ, Etingof.Q8.rho (QuaternionGroup.xa 0) v
        = ![v 1, -v 0] := by
      intro v
      rw [Etingof.Q8.rho_apply]
      show (Etingof.Q8.Mfun (QuaternionGroup.xa 0)).mulVec v = _
      simp only [Etingof.Q8.Mfun, show (0 : ZMod (2 * 2)).val = 0 from by decide, pow_zero,
        mul_one]
      funext i; fin_cases i <;>
        simp [Etingof.Q8.X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    -- Reduce `IsSimpleModule` to `IsSimpleOrder` of the invariant-submodule lattice.
    suffices hSO : IsSimpleOrder (Etingof.Q8.rho.invtSubmodule) by
      haveI := (Representation.mapSubmodule Etingof.Q8.rho).isSimpleOrder_iff.mp hSO
      exact ⟨⟩
    refine { eq_bot_or_eq_top := fun a => ?_ }
    have hinv : ∀ g, ∀ x ∈ (a : Submodule ℂ (Fin 2 → ℂ)),
        Etingof.Q8.rho g x ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
      intro g x hx
      have hmem : (a : Submodule ℂ (Fin 2 → ℂ)) ∈ Module.End.invtSubmodule (Etingof.Q8.rho g) :=
        (Representation.mem_invtSubmodule (ρ := Etingof.Q8.rho)).mp a.2 g
      exact ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Etingof.Q8.rho g)).mp hmem) x hx
    rcases eq_or_ne (a : Submodule ℂ (Fin 2 → ℂ)) ⊥ with hbot | hbot
    · exact Or.inl (Subtype.ext (by rw [Representation.invtSubmodule.coe_bot]; exact hbot))
    · refine Or.inr (Subtype.ext ?_)
      rw [Representation.invtSubmodule.coe_top]
      -- Extract a nonzero vector and show both basis vectors lie in `a`.
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
      have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) ∧
          (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
        by_cases hv1 : v 1 = 0
        · -- `v = (v₀, 0)` with `v₀ ≠ 0`: scale to `e₀`, then apply `X` for `e₁`.
          have hv0' : v 0 ≠ 0 := by
            intro h; apply hv0; funext i; fin_cases i
            · simpa using h
            · simpa using hv1
          have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have : (v 0)⁻¹ • v = (![1, 0] : Fin 2 → ℂ) := by
              funext i; fin_cases i
              · simpa using inv_mul_cancel₀ hv0'
              · simpa [hv1]
            rw [← this]; exact (a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hv
          have he1 : (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have hx := hinv (QuaternionGroup.xa 0) _ he0
            rw [hXv] at hx
            have : (![(![1, 0] : Fin 2 → ℂ) 1, -(![1, 0] : Fin 2 → ℂ) 0] : Fin 2 → ℂ)
                = -(![0, 1] : Fin 2 → ℂ) := by funext i; fin_cases i <;> simp
            rw [this] at hx
            simpa using (a : Submodule ℂ (Fin 2 → ℂ)).neg_mem hx
          exact ⟨he0, he1⟩
        · -- `v₁ ≠ 0`: form `I•v - A·v = (0, 2I v₁)`, scale to `e₁`, then apply `X` for `e₀`.
          have hmem : (Complex.I • v - Etingof.Q8.rho (QuaternionGroup.a 1) v)
              ∈ (a : Submodule ℂ (Fin 2 → ℂ)) :=
            (a : Submodule ℂ (Fin 2 → ℂ)).sub_mem
              ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hv) (hinv _ _ hv)
          have heq : Complex.I • v - Etingof.Q8.rho (QuaternionGroup.a 1) v
              = ![0, 2 * Complex.I * v 1] := by
            rw [hAv]; funext i; fin_cases i <;> simp [Pi.smul_apply] <;> ring
          rw [heq] at hmem
          have hc : (2 : ℂ) * Complex.I * v 1 ≠ 0 := by
            simp [hv1, Complex.I_ne_zero]
          have he1 : (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have : (2 * Complex.I * v 1)⁻¹ • (![0, 2 * Complex.I * v 1] : Fin 2 → ℂ)
                = (![0, 1] : Fin 2 → ℂ) := by
              funext i; fin_cases i
              · simp
              · simpa using inv_mul_cancel₀ hc
            rw [← this]; exact (a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hmem
          have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have hx := hinv (QuaternionGroup.xa 0) _ he1
            rw [hXv] at hx
            have : (![(![0, 1] : Fin 2 → ℂ) 1, -(![0, 1] : Fin 2 → ℂ) 0] : Fin 2 → ℂ)
                = (![1, 0] : Fin 2 → ℂ) := by funext i; fin_cases i <;> simp
            rwa [this] at hx
          exact ⟨he0, he1⟩
      -- Two basis vectors span everything.
      rw [eq_top_iff]
      intro w _
      have hw : w = w 0 • (![1, 0] : Fin 2 → ℂ) + w 1 • ![0, 1] := by
        funext i; fin_cases i <;> simp
      rw [hw]
      exact (a : Submodule ℂ (Fin 2 → ℂ)).add_mem
        ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ he0.1)
        ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ he0.2)
  · -- Quaternionic type: the wedge form `B v w = v₀w₁ - v₁w₀` is skew, nondegenerate, and
    -- `Q₈`-invariant (every matrix lies in `SL₂`, so it preserves the determinant form).
    set B : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun v w => v 0 * w 1 - v 1 * w 0)
        (fun v v' w => by simp only [Pi.add_apply]; ring)
        (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
        (fun v w w' => by simp only [Pi.add_apply]; ring)
        (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring) with hBdef
    have hB : ∀ v w : Fin 2 → ℂ, B v w = v 0 * w 1 - v 1 * w 0 := fun v w => rfl
    refine ⟨B, ?_, ?_, ?_⟩
    · -- skew-symmetric
      intro v w; rw [hB, hB]; ring
    · -- nondegenerate
      intro v hv
      have h0 : v 0 = 0 := by have := hv ![0, 1]; rw [hB] at this; simpa using this
      have h1 : v 1 = 0 := by have := hv ![1, 0]; rw [hB] at this; simpa using this
      funext i; fin_cases i
      · simpa using h0
      · simpa using h1
    · -- Q₈-invariant
      intro g v w
      have key : ∀ (N : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 2 → ℂ),
          B (N.mulVec x) (N.mulVec y) = N.det * B x y := by
        intro N x y
        rw [hB, hB]
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
        ring
      rw [Etingof.Q8.rho_apply, Etingof.Q8.rho_apply, key]
      have hdet : (Etingof.Q8.Mhom g).det = 1 := by
        rcases g with k | k
        · show (Etingof.Q8.Mfun (QuaternionGroup.a k)).det = 1
          simp [Etingof.Q8.Mfun, Matrix.det_pow]
        · show (Etingof.Q8.Mfun (QuaternionGroup.xa k)).det = 1
          simp [Etingof.Q8.Mfun, Matrix.det_mul, Matrix.det_pow]
      rw [hdet, one_mul]
