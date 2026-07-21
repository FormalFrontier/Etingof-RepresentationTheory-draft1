import Mathlib

/-!
# Problem 4.12.1: representations of the dihedral group (symmetries of a regular `N`-gon)

**Problem 4.12.1.** Let `G` be the group of symmetries of a regular `N`-gon (it has `2N`
elements).

(a) Describe all irreducible complex representations of this group (consider the cases of odd
and even `N`).

(b) Let `V` be the 2-dimensional complex representation of `G` obtained by complexification of
the standard representation on the real plane (the plane of the polygon). Find the
decomposition of `V ⊗ V` in a direct sum of irreducible representations.

## Formalization

We model the symmetry group of the regular `N`-gon by Mathlib's `DihedralGroup N` (order `2N`;
generators `r k` = rotations, `sr k` = reflections).

* **(a)** The faithful content of "describe all irreducibles" is the dimension dichotomy:
  *every* irreducible complex representation of `DihedralGroup N` is `1`- or `2`-dimensional.
  (The precise counts — `2` one-dimensional and `(N-1)/2` two-dimensional for odd `N`; `4`
  one-dimensional and `(N-2)/2` two-dimensional for even `N` — are recorded here in the
  docstring.)

  The proof follows the book: pick an eigenvector `v` of the rotation `ρ (r 1)` (a nonzero
  endomorphism of a nonzero finite-dimensional space over `ℂ` always has one). Then the span of
  `v` and `s • v` (with `s = ρ (sr 0)` a reflection) is stable under the whole group, hence a
  subrepresentation of dimension `≤ 2`; irreducibility forces it to be everything, so
  `dim W ∈ {1, 2}`.

* **(b)** Over `ℂ` the complexified standard representation `V` diagonalizes on rotations with
  eigenvalues `ζ^k, ζ^{-k}` (`ζ = exp(2πi/N)` a primitive `N`-th root of unity), and `V ⊗ V`
  decomposes as `𝟙 ⊕ ε ⊕ V₂`, where `𝟙` is trivial, `ε` is the sign (rotations act by `1`,
  reflections by `-1`), and `V₂` is the `2`-dimensional representation with rotation by
  `4π/N`. We state this at the level of **characters**: with `χ_V`, `χ_ε`, `χ_{V₂}` the
  class functions defined below, `χ_V(g)² = 1 + χ_ε(g) + χ_{V₂}(g)` for all `g`, which is
  exactly `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂` since the character of a tensor product is the product of
  characters.
-/

open Real

noncomputable section

namespace Etingof.Problem4_12_1

variable {N : ℕ}

/-- A primitive `N`-th root of unity `ζ = exp(2πi/N)`. -/
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / N)

/-- **Part (a).** Every irreducible complex representation of the dihedral group
`DihedralGroup N` (for `N ≥ 1`) is either `1`- or `2`-dimensional. -/
theorem irreducible_dim [NeZero N]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (DihedralGroup N) W)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) ρ.asModule) :
    Module.finrank ℂ W = 1 ∨ Module.finrank ℂ W = 2 := by
  classical
  haveI : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) ρ.asModule := hρ
  haveI : Nontrivial W :=
    IsSimpleModule.nontrivial (R := MonoidAlgebra ℂ (DihedralGroup N)) (M := ρ.asModule)
  -- Irreducibility of `ρ`: the lattice of subrepresentations is simple.
  haveI hirr : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  -- An eigenvector `v` of the rotation `ρ (r 1)`.
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (ρ (DihedralGroup.r 1))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  -- The reflection applied to `v`.
  set w₀ : W := ρ (DihedralGroup.sr 0) v with hw₀
  -- The rotation `r j` acts on the eigenvector by the scalar `μ ^ j.val`.
  have hA : ∀ j : ZMod N, ρ (DihedralGroup.r j) v = μ ^ j.val • v := by
    intro j
    have hj : DihedralGroup.r j = (DihedralGroup.r 1 : DihedralGroup N) ^ j.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [hj, map_pow]
    exact hv.pow_apply j.val
  -- The reflection `sr j = sr 0 * r j` sends `v` to `μ ^ j.val • w₀`.
  have hB : ∀ j : ZMod N, ρ (DihedralGroup.sr j) v = μ ^ j.val • w₀ := by
    intro j
    have hj : DihedralGroup.sr j = DihedralGroup.sr 0 * DihedralGroup.r j := by
      rw [DihedralGroup.sr_mul_r, zero_add]
    rw [hj, map_mul, Module.End.mul_apply, hA j, map_smul, hw₀]
  -- The two generators of the span, as members.
  have hvU : v ∈ Submodule.span ℂ ({v, w₀} : Set W) := Submodule.subset_span (by simp)
  have hw₀U : w₀ ∈ Submodule.span ℂ ({v, w₀} : Set W) := Submodule.subset_span (by simp)
  -- `ρ g` on `w₀` is `ρ (g * sr 0)` on `v`.
  have hgsv : ∀ g : DihedralGroup N, ρ g w₀ = ρ (g * DihedralGroup.sr 0) v := by
    intro g; rw [hw₀, map_mul, Module.End.mul_apply]
  -- `span {v, w₀}` is a subrepresentation.
  let Sub : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ ({v, w₀} : Set W)
      apply_mem_toSubmodule := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · cases g with
              | r k => rw [hA k]; exact Submodule.smul_mem _ _ hvU
              | sr k => rw [hB k]; exact Submodule.smul_mem _ _ hw₀U
            · rw [hgsv g]
              cases g with
              | r k =>
                  rw [DihedralGroup.r_mul_sr, hB (0 - k)]; exact Submodule.smul_mem _ _ hw₀U
              | sr k =>
                  rw [DihedralGroup.sr_mul_sr, hA (0 - k)]; exact Submodule.smul_mem _ _ hvU
        | zero => simp
        | add a b _ _ iha ihb => rw [map_add]; exact Submodule.add_mem _ iha ihb
        | smul c a _ ih => rw [map_smul]; exact Submodule.smul_mem _ _ ih }
  -- Irreducibility forces the subrepresentation to be everything.
  have hSubTop : Sub.toSubmodule = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top Sub with h | h
    · exfalso
      apply hv0
      have hbot : Sub.toSubmodule = ⊥ := by rw [h]; rfl
      have hv' : v ∈ (⊥ : Submodule ℂ W) := by rw [← hbot]; exact hvU
      rwa [Submodule.mem_bot] at hv'
    · rw [h]; rfl
  have hspan : Submodule.span ℂ ({v, w₀} : Set W) = ⊤ := hSubTop
  -- Two generators, so the dimension is at most `2`.
  have hrange : Set.range ![v, w₀] = ({v, w₀} : Set W) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hle : Module.finrank ℂ W ≤ 2 := by
    have h := finrank_le_of_span_eq_top (R := ℂ) (v := ![v, w₀]) (by rw [hrange]; exact hspan)
    simpa using h
  have hpos : 0 < Module.finrank ℂ W := Module.finrank_pos
  omega

/-- Character of the complexified standard `2`-dimensional representation `V`:
`χ_V(r k) = ζ^k + ζ^{-k}` on rotations and `0` on reflections. -/
noncomputable def chiStd (N : ℕ) : DihedralGroup N → ℂ
  | .r k => zeta N ^ k.val + (zeta N)⁻¹ ^ k.val
  | .sr _ => 0

/-- Character of the sign representation `ε`: rotations act by `1`, reflections by `-1`. -/
def chiSign (N : ℕ) : DihedralGroup N → ℂ
  | .r _ => 1
  | .sr _ => -1

/-- Character of the `2`-dimensional representation `V₂` (rotation by `4π/N`):
`χ_{V₂}(r k) = ζ^{2k} + ζ^{-2k}` on rotations and `0` on reflections. -/
noncomputable def chiRot2 (N : ℕ) : DihedralGroup N → ℂ
  | .r k => zeta N ^ (2 * k.val) + (zeta N)⁻¹ ^ (2 * k.val)
  | .sr _ => 0

/-- **Part (b).** The decomposition `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂`, expressed as the character identity
`χ_V(g)² = 1 + χ_ε(g) + χ_{V₂}(g)` (the constant `1` is the character of the trivial
representation). -/
theorem tensor_square_character (N : ℕ) (g : DihedralGroup N) :
    chiStd N g ^ 2 = 1 + chiSign N g + chiRot2 N g := by
  cases g with
  | r k =>
    simp only [chiStd, chiSign, chiRot2]
    have hz : zeta N ≠ 0 := by unfold zeta; exact Complex.exp_ne_zero _
    have hab : zeta N ^ k.val * (zeta N)⁻¹ ^ k.val = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    have ha2 : zeta N ^ (2 * k.val) = (zeta N ^ k.val) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm]
    have hb2 : (zeta N)⁻¹ ^ (2 * k.val) = ((zeta N)⁻¹ ^ k.val) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm]
    rw [ha2, hb2]
    linear_combination (2 : ℂ) * hab
  | sr k =>
    simp only [chiStd, chiSign, chiRot2]
    ring

/-!
## Part (a): explicit construction and classification of all irreducibles

We build, for each `j : ZMod N`, an explicit `2`-dimensional representation `Vrep N j` on
`Fin 2 → ℂ` where the rotation `r 1` acts diagonally by `diag(ζ^j, ζ^{-j})` and the reflection
`sr 0` swaps the two coordinates. These are irreducible exactly when `2·j ≠ 0` (equivalently
`ζ^j ≠ ζ^{-j}`), and together with the one-dimensional characters they exhaust the irreducibles.
-/

/-- `ζ = zeta N` is a nonzero complex number. -/
theorem zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := by
  unfold zeta; exact Complex.exp_ne_zero _

/-- `ζ^N = 1`: `zeta N` is an `N`-th root of unity. -/
theorem zeta_pow_card [NeZero N] : zeta N ^ N = 1 := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [show (N : ℂ) * (2 * π * Complex.I / N) = 2 * π * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

/-- The exponent of `ζ` only matters modulo `N`. -/
theorem zeta_pow_mod [NeZero N] (k : ℕ) : zeta N ^ (k % N) = zeta N ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k N, pow_add, pow_mul, zeta_pow_card, one_pow, mul_one]

/-- `k ↦ ζ^{k.val}` turns addition in `ZMod N` into multiplication. -/
theorem zeta_pow_val_add [NeZero N] (a b : ZMod N) :
    zeta N ^ (a + b).val = zeta N ^ a.val * zeta N ^ b.val := by
  rw [ZMod.val_add, zeta_pow_mod, pow_add]

/-- The eigenvalue by which the rotation `r m` acts on the first basis vector of `Vrep N j`:
`ζ^{(j·m)}`. -/
noncomputable def eigen (N : ℕ) (j m : ZMod N) : ℂ := zeta N ^ (j * m).val

@[simp] theorem eigen_zero (N : ℕ) (j : ZMod N) : eigen N j 0 = 1 := by
  simp [eigen]

theorem eigen_ne_zero (N : ℕ) (j m : ZMod N) : eigen N j m ≠ 0 :=
  pow_ne_zero _ (zeta_ne_zero N)

/-- `eigen` is multiplicative in its argument: `eigen j (m + m') = eigen j m · eigen j m'`. -/
theorem eigen_add [NeZero N] (j m m' : ZMod N) :
    eigen N j (m + m') = eigen N j m * eigen N j m' := by
  unfold eigen
  rw [mul_add, zeta_pow_val_add]

theorem eigen_neg [NeZero N] (j m : ZMod N) : eigen N j (-m) = (eigen N j m)⁻¹ := by
  rw [inv_eq_one_div, eq_div_iff (eigen_ne_zero N j m), ← eigen_add, neg_add_cancel, eigen_zero]

theorem eigen_sub [NeZero N] (j m m' : ZMod N) :
    eigen N j (m - m') = eigen N j m * (eigen N j m')⁻¹ := by
  rw [sub_eq_add_neg, eigen_add, eigen_neg]

/-- The matrix of `ρ_j(g)` in the standard basis of `ℂ²`: rotations act diagonally, reflections
antidiagonally. -/
noncomputable def repMat (N : ℕ) (j : ZMod N) : DihedralGroup N → Matrix (Fin 2) (Fin 2) ℂ
  | .r k => !![eigen N j k, 0; 0, (eigen N j k)⁻¹]
  | .sr k => !![0, (eigen N j k)⁻¹; eigen N j k, 0]

theorem repMat_one [NeZero N] (j : ZMod N) : repMat N j 1 = 1 := by
  rw [DihedralGroup.one_def]
  change (!![eigen N j 0, 0; 0, (eigen N j 0)⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) = 1
  rw [eigen_zero, inv_one, Matrix.one_fin_two]

theorem repMat_mul [NeZero N] (j : ZMod N) (g h : DihedralGroup N) :
    repMat N j (g * h) = repMat N j g * repMat N j h := by
  cases g with
  | r a =>
    cases h with
    | r b =>
      rw [DihedralGroup.r_mul_r]
      change (!![eigen N j (a + b), 0; 0, (eigen N j (a + b))⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![eigen N j a, 0; 0, (eigen N j a)⁻¹] * !![eigen N j b, 0; 0, (eigen N j b)⁻¹]
      rw [Matrix.mul_fin_two, eigen_add, mul_inv]
      ext i k; fin_cases i <;> fin_cases k <;> simp
    | sr b =>
      rw [DihedralGroup.r_mul_sr]
      change (!![0, (eigen N j (b - a))⁻¹; eigen N j (b - a), 0] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![eigen N j a, 0; 0, (eigen N j a)⁻¹] * !![0, (eigen N j b)⁻¹; eigen N j b, 0]
      rw [Matrix.mul_fin_two, eigen_sub]
      ext i k; fin_cases i <;> fin_cases k <;> simp [mul_comm]
  | sr a =>
    cases h with
    | r b =>
      rw [DihedralGroup.sr_mul_r]
      change (!![0, (eigen N j (a + b))⁻¹; eigen N j (a + b), 0] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![0, (eigen N j a)⁻¹; eigen N j a, 0] * !![eigen N j b, 0; 0, (eigen N j b)⁻¹]
      rw [Matrix.mul_fin_two, eigen_add, mul_inv]
      ext i k; fin_cases i <;> fin_cases k <;> simp
    | sr b =>
      rw [DihedralGroup.sr_mul_sr]
      change (!![eigen N j (b - a), 0; 0, (eigen N j (b - a))⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)
        = !![0, (eigen N j a)⁻¹; eigen N j a, 0] * !![0, (eigen N j b)⁻¹; eigen N j b, 0]
      rw [Matrix.mul_fin_two, eigen_sub]
      ext i k; fin_cases i <;> fin_cases k <;> simp [mul_comm]

/-- **Part (a), construction.** For each `j : ZMod N`, the explicit `2`-dimensional complex
representation `V_j` of `DihedralGroup N`: the rotation `r 1` acts by `diag(ζ^j, ζ^{-j})` and
the reflection `sr 0` swaps the two basis vectors. -/
noncomputable def Vrep (N : ℕ) [NeZero N] (j : ZMod N) :
    Representation ℂ (DihedralGroup N) (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' (repMat N j g)
  map_one' := by rw [repMat_one]; exact Matrix.toLin'_one
  map_mul' g h := by rw [repMat_mul, Matrix.toLin'_mul]; rfl

@[simp] theorem Vrep_apply (N : ℕ) [NeZero N] (j : ZMod N) (g : DihedralGroup N)
    (v : Fin 2 → ℂ) : Vrep N j g v = (repMat N j g).mulVec v :=
  Matrix.toLin'_apply _ _

end Etingof.Problem4_12_1
