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
  sorry
