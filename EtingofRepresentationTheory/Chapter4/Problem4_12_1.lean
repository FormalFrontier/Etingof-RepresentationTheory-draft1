import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_S3
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Corollary4_2_4
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

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

* **(a)** The essential content of "describe all irreducibles" is the dimension dichotomy:
  every irreducible complex representation of `DihedralGroup N` is `1`- or `2`-dimensional.
  (The precise counts are: `2` one-dimensional and `(N-1)/2` two-dimensional for odd `N`; `4`
  one-dimensional and `(N-2)/2` two-dimensional for even `N`.)

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

theorem Vrep_apply (N : ℕ) [NeZero N] (j : ZMod N) (g : DihedralGroup N)
    (v : Fin 2 → ℂ) : Vrep N j g v = (repMat N j g).mulVec v :=
  Matrix.toLin'_apply _ _

/-- First coordinate of `r k` acting on `v`. -/
@[simp] theorem Vrep_r_apply_zero (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    Vrep N j (DihedralGroup.r k) v 0 = eigen N j k * v 0 := by
  rw [Vrep_apply]; simp [repMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Second coordinate of `r k` acting on `v`. -/
@[simp] theorem Vrep_r_apply_one (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    Vrep N j (DihedralGroup.r k) v 1 = (eigen N j k)⁻¹ * v 1 := by
  rw [Vrep_apply]; simp [repMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- First coordinate of `sr k` acting on `v` (reflection swaps the coordinates). -/
@[simp] theorem Vrep_sr_apply_zero (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    Vrep N j (DihedralGroup.sr k) v 0 = (eigen N j k)⁻¹ * v 1 := by
  rw [Vrep_apply]; simp [repMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Second coordinate of `sr k` acting on `v` (reflection swaps the coordinates). -/
@[simp] theorem Vrep_sr_apply_one (N : ℕ) [NeZero N] (j k : ZMod N) (v : Fin 2 → ℂ) :
    Vrep N j (DihedralGroup.sr k) v 1 = eigen N j k * v 0 := by
  rw [Vrep_apply]; simp [repMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `zeta N` is a primitive `N`-th root of unity. -/
theorem isPrimitiveRoot_zeta [NeZero N] : IsPrimitiveRoot (zeta N) N := by
  unfold zeta; exact Complex.isPrimitiveRoot_exp N (NeZero.ne N)

/-- **Part (a), irreducibility.** For `j` with `2·j ≠ 0` (equivalently `ζ^j ≠ ζ^{-j}`), the
representation `V_j` is irreducible: the rotation `r 1` has distinct eigenvalues `ζ^{±j}`, so its
only eigenlines are the two coordinate axes, and the reflection `sr 0` swaps them — hence there
is no proper nonzero subrepresentation. -/
theorem Vrep_irreducible [NeZero N] (j : ZMod N) (hj : (2 : ZMod N) * j ≠ 0) :
    IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) (Vrep N j).asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hα0 : eigen N j 1 ≠ 0 := eigen_ne_zero N j 1
  -- `ζ^j ≠ ζ^{-j}` because `2·j ≠ 0`.
  have hsq : (eigen N j 1) ^ 2 ≠ 1 := by
    rw [sq, ← eigen_add]
    intro h
    apply hj
    unfold eigen at h
    have hdvd : N ∣ (j * (1 + 1)).val := (isPrimitiveRoot_zeta.pow_eq_one_iff_dvd _).mp h
    have hz : (j * (1 + 1) : ZMod N) = 0 := by
      have h2 := (ZMod.natCast_eq_zero_iff (j * (1 + 1)).val N).mpr hdvd
      rwa [ZMod.natCast_zmod_val] at h2
    rw [show (2 : ZMod N) * j = j * (1 + 1) by ring]
    exact hz
  have hαsub : eigen N j 1 - (eigen N j 1)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h; apply hsq
    rw [sq]; nth_rewrite 2 [h]; exact mul_inv_cancel₀ hα0
  -- The reflection `sr 0` swaps the two coordinate axes.
  have hswap0 : Vrep N j (DihedralGroup.sr 0) ![1, 0] = ![0, 1] := by
    funext i; fin_cases i <;> simp [eigen_zero]
  have hswap1 : Vrep N j (DihedralGroup.sr 0) ![0, 1] = ![1, 0] := by
    funext i; fin_cases i <;> simp [eigen_zero]
  have hNT : Nontrivial (Subrepresentation (Vrep N j)) := by
    refine ⟨⊥, ⊤, ?_⟩
    intro h
    exact absurd (congrArg Subrepresentation.toSubmodule h) bot_ne_top
  refine { toNontrivial := hNT, eq_bot_or_eq_top := fun σ => ?_ }
  rcases eq_or_ne σ.toSubmodule ⊥ with hbot | hne
  · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    -- From a nonzero vector we extract a coordinate axis, then the swap gives the other.
    have hget0 : v 0 ≠ 0 → ![(1 : ℂ), 0] ∈ σ.toSubmodule := by
      intro hv0'
      have hD : Vrep N j (DihedralGroup.r 1) v - (eigen N j 1)⁻¹ • v ∈ σ.toSubmodule :=
        Submodule.sub_mem _ (σ.apply_mem_toSubmodule _ hv) (Submodule.smul_mem _ _ hv)
      have heq : Vrep N j (DihedralGroup.r 1) v - (eigen N j 1)⁻¹ • v
          = ((eigen N j 1 - (eigen N j 1)⁻¹) * v 0) • ![(1 : ℂ), 0] := by
        funext i
        fin_cases i <;> (simp [Pi.smul_apply, Pi.sub_apply]; try ring)
      rw [heq] at hD
      have hc : (eigen N j 1 - (eigen N j 1)⁻¹) * v 0 ≠ 0 := mul_ne_zero hαsub hv0'
      have := Submodule.smul_mem σ.toSubmodule
        (((eigen N j 1 - (eigen N j 1)⁻¹) * v 0)⁻¹) hD
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hget1 : v 1 ≠ 0 → ![(0 : ℂ), 1] ∈ σ.toSubmodule := by
      intro hv1'
      have hD : Vrep N j (DihedralGroup.r 1) v - (eigen N j 1) • v ∈ σ.toSubmodule :=
        Submodule.sub_mem _ (σ.apply_mem_toSubmodule _ hv) (Submodule.smul_mem _ _ hv)
      have heq : Vrep N j (DihedralGroup.r 1) v - (eigen N j 1) • v
          = (((eigen N j 1)⁻¹ - eigen N j 1) * v 1) • ![(0 : ℂ), 1] := by
        funext i
        fin_cases i <;> (simp [Pi.smul_apply, Pi.sub_apply]; try ring)
      rw [heq] at hD
      have hc : ((eigen N j 1)⁻¹ - eigen N j 1) * v 1 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (sub_ne_zero.mp hαsub).symm) hv1'
      have := Submodule.smul_mem σ.toSubmodule
        ((((eigen N j 1)⁻¹ - eigen N j 1) * v 1)⁻¹) hD
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    -- Both coordinate axes lie in `σ`.
    have hbasis : ![(1 : ℂ), 0] ∈ σ.toSubmodule ∧ ![(0 : ℂ), 1] ∈ σ.toSubmodule := by
      by_cases h0 : v 0 = 0
      · have hv1 : v 1 ≠ 0 := by
          intro h1; apply hv0; funext i; fin_cases i <;> simp_all
        have he1 := hget1 hv1
        exact ⟨by rw [← hswap1]; exact σ.apply_mem_toSubmodule _ he1, he1⟩
      · have he0 := hget0 h0
        exact ⟨he0, by rw [← hswap0]; exact σ.apply_mem_toSubmodule _ he0⟩
    -- Hence `σ` is everything.
    change σ.toSubmodule = (⊤ : Submodule ℂ (Fin 2 → ℂ))
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • ![(1 : ℂ), 0] + x 1 • ![(0 : ℂ), 1] := by
      funext i; fin_cases i <;> simp
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hbasis.1)
      (Submodule.smul_mem _ _ hbasis.2)

/-- The character (trace) of `V_j` on a rotation `r k` is `ζ^{jk} + ζ^{-jk}`. -/
theorem Vrep_trace_r [NeZero N] (j k : ZMod N) :
    LinearMap.trace ℂ (Fin 2 → ℂ) (Vrep N j (DihedralGroup.r k)) =
      eigen N j k + (eigen N j k)⁻¹ := by
  have hrfl : Vrep N j (DihedralGroup.r k) = Matrix.toLin' (repMat N j (DihedralGroup.r k)) := rfl
  rw [hrfl, Matrix.trace_toLin'_eq]
  simp [repMat, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **Part (a), pairwise non-isomorphism (character criterion).** If the rotation characters of
`V_j` and `V_{j'}` differ at `r 1` (i.e. `ζ^j + ζ^{-j} ≠ ζ^{j'} + ζ^{-j'}`), then there is no
representation isomorphism (intertwining linear equivalence) between them. In particular the
`V_j` for distinct rotation-eigenvalue pairs are pairwise non-isomorphic. -/
theorem Vrep_not_iso [NeZero N] {j j' : ZMod N}
    (hne : eigen N j 1 + (eigen N j 1)⁻¹ ≠ eigen N j' 1 + (eigen N j' 1)⁻¹) :
    ¬ ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
        ∀ g, T.toLinearMap.comp (Vrep N j g) = (Vrep N j' g).comp T.toLinearMap := by
  rintro ⟨T, hT⟩
  have hconj : T.conj (Vrep N j (DihedralGroup.r 1)) = Vrep N j' (DihedralGroup.r 1) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.conj_apply_apply]
    have h := LinearMap.congr_fun (hT (DihedralGroup.r 1)) (T.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h
  have htr := LinearMap.trace_conj' (Vrep N j (DihedralGroup.r 1)) T
  rw [hconj, Vrep_trace_r, Vrep_trace_r] at htr
  exact hne htr.symm

/-!
## Part (a): the one-dimensional characters and their count

A one-dimensional complex representation of `DihedralGroup N` is a group homomorphism
`χ : DihedralGroup N →* ℂˣ`.  Such a `χ` is determined by the two values `u = χ (r 1)` and
`w = χ (sr 0)` on the generators, subject to `u ^ N = 1` (the order of `r`), `w ^ 2 = 1` (the
order of `sr`), and `u ^ 2 = 1` (the dihedral relation `sr · r · sr = r⁻¹` forces
`χ (r 1) = χ (r 1)⁻¹`).  Conversely every such pair `(u, w)` extends to a character.  Counting
the pairs gives `2` characters for odd `N` and `4` for even `N`.
-/

section OneDim

variable [NeZero N]

omit [NeZero N] in
/-- For a unit `u` with `u ^ N = 1`, the exponent only matters modulo `N`. -/
theorem upow_val_mod (u : ℂˣ) (hu : u ^ N = 1) (k : ℕ) : u ^ (k % N) = u ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k N, pow_add, pow_mul, hu, one_pow, mul_one]

/-- The map `a ↦ u ^ a.val` turns addition in `ZMod N` into multiplication, when `u ^ N = 1`. -/
theorem upow_val_add (u : ℂˣ) (hu : u ^ N = 1) (a b : ZMod N) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  rw [ZMod.val_add, upow_val_mod u hu, pow_add]

/-- The one-dimensional character of `DihedralGroup N` built from valid generator data
`u = χ (r 1)`, `w = χ (sr 0)`: it sends `r k ↦ u ^ k.val` and `sr k ↦ w · u ^ k.val`.  The three
hypotheses `u ^ N = 1`, `u ^ 2 = 1`, `w ^ 2 = 1` are exactly what makes this multiplicative. -/
def charOfData (u w : ℂˣ) (huN : u ^ N = 1) (hu2 : u ^ 2 = 1) (hw2 : w ^ 2 = 1) :
    DihedralGroup N →* ℂˣ where
  toFun g := match g with
    | .r k => u ^ k.val
    | .sr k => w * u ^ k.val
  map_one' := by change u ^ (0 : ZMod N).val = 1; rw [ZMod.val_zero, pow_zero]
  map_mul' g h := by
    have hadd : ∀ a b : ZMod N, u ^ (a + b).val = u ^ a.val * u ^ b.val := upow_val_add u huN
    have hself : ∀ a : ZMod N, u ^ a.val * u ^ a.val = 1 := fun a => by
      rw [← pow_add, ← two_mul, pow_mul, hu2, one_pow]
    have hsub : ∀ a b : ZMod N, u ^ (a - b).val = u ^ a.val * u ^ b.val := by
      intro a b
      have h1 : u ^ ((-b).val) * u ^ b.val = 1 := by
        rw [← hadd, neg_add_cancel, ZMod.val_zero, pow_zero]
      have hnb : u ^ ((-b).val) = u ^ b.val :=
        mul_right_cancel (h1.trans (hself b).symm)
      rw [sub_eq_add_neg, hadd, hnb]
    have hww : w * w = 1 := by rw [← pow_two, hw2]
    cases g with
    | r a => cases h with
      | r b =>
        rw [DihedralGroup.r_mul_r]
        change u ^ (a + b).val = u ^ a.val * u ^ b.val
        exact hadd a b
      | sr b =>
        rw [DihedralGroup.r_mul_sr]
        change w * u ^ (b - a).val = u ^ a.val * (w * u ^ b.val)
        rw [hsub]; ac_rfl
    | sr a => cases h with
      | r b =>
        rw [DihedralGroup.sr_mul_r]
        change w * u ^ (a + b).val = (w * u ^ a.val) * u ^ b.val
        rw [hadd]; ac_rfl
      | sr b =>
        rw [DihedralGroup.sr_mul_sr]
        change u ^ (b - a).val = (w * u ^ a.val) * (w * u ^ b.val)
        rw [hsub, show (w * u ^ a.val) * (w * u ^ b.val)
              = (w * w) * (u ^ a.val * u ^ b.val) from by ac_rfl, hww, one_mul]
        ac_rfl

@[simp] theorem charOfData_r (u w : ℂˣ) (huN : u ^ N = 1) (hu2 : u ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (k : ZMod N) : charOfData u w huN hu2 hw2 (DihedralGroup.r k) = u ^ k.val := rfl

@[simp] theorem charOfData_sr (u w : ℂˣ) (huN : u ^ N = 1) (hu2 : u ^ 2 = 1) (hw2 : w ^ 2 = 1)
    (k : ZMod N) : charOfData u w huN hu2 hw2 (DihedralGroup.sr k) = w * u ^ k.val := rfl

/-- **Part (a), classification of one-dimensional representations.** A character of
`DihedralGroup N` is the same data as a pair `(u, w) ∈ ℂˣ × ℂˣ` with `u ^ N = 1`, `u ^ 2 = 1`
and `w ^ 2 = 1`, via `χ ↦ (χ (r 1), χ (sr 0))`. -/
def charEquiv (N : ℕ) [NeZero N] :
    (DihedralGroup N →* ℂˣ) ≃
      {p : ℂˣ × ℂˣ // (p.1 ^ N = 1 ∧ p.1 ^ 2 = 1) ∧ p.2 ^ 2 = 1} where
  toFun χ := by
    refine ⟨(χ (DihedralGroup.r 1), χ (DihedralGroup.sr 0)), ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [← map_pow, DihedralGroup.r_one_pow_n, map_one]
    · -- the dihedral relation forces `χ (r 1) ^ 2 = 1`
      have hs2 : χ (DihedralGroup.sr 0) * χ (DihedralGroup.sr 0) = 1 := by
        rw [← map_mul, DihedralGroup.sr_mul_self, map_one]
      have hrel : (DihedralGroup.r 1 : DihedralGroup N)⁻¹
          = DihedralGroup.sr 0 * DihedralGroup.r 1 * DihedralGroup.sr 0 := by
        rw [DihedralGroup.inv_r, DihedralGroup.sr_mul_r, zero_add, DihedralGroup.sr_mul_sr]
        congr 1; ring
      have key : χ (DihedralGroup.sr 0) * χ (DihedralGroup.r 1) * χ (DihedralGroup.sr 0)
          = χ (DihedralGroup.r 1) := by rw [mul_right_comm, hs2, one_mul]
      have hinv : (χ (DihedralGroup.r 1))⁻¹ = χ (DihedralGroup.r 1) := by
        rw [← map_inv, hrel, map_mul, map_mul, key]
      rw [pow_two]; nth_rewrite 2 [← hinv]; exact mul_inv_cancel _
    · rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
  invFun p := charOfData p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2
  left_inv χ := by
    ext g
    cases g with
    | r k =>
      simp only [charOfData_r]
      rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    | sr k =>
      simp only [charOfData_sr]
      rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, ← map_mul,
        DihedralGroup.sr_mul_r, zero_add]
  right_inv p := by
    obtain ⟨⟨u, w⟩, ⟨⟨huN, hu2⟩, hw2⟩⟩ := p
    apply Subtype.ext
    have hval1 : (1 : ZMod N).val = 1 % N := by
      rw [← Nat.cast_one (R := ZMod N), ZMod.val_natCast]
    refine Prod.ext ?_ ?_
    · change charOfData u w huN hu2 hw2 (DihedralGroup.r 1) = u
      rw [charOfData_r, hval1, upow_val_mod u huN, pow_one]
    · change charOfData u w huN hu2 hw2 (DihedralGroup.sr 0) = w
      rw [charOfData_sr, ZMod.val_zero, pow_zero, mul_one]

/-- There are exactly two square roots of unity in `ℂˣ` (namely `±1`). -/
theorem card_sqrtOne : Nat.card {w : ℂˣ // w ^ 2 = 1} = 2 := by
  have e : {w : ℂˣ // w ^ 2 = 1} ≃ (rootsOfUnity 2 ℂ) :=
    Equiv.subtypeEquivRight (fun w => (mem_rootsOfUnity 2 w).symm)
  rw [Nat.card_congr e, Complex.card_rootsOfUnity]

omit [NeZero N] in
/-- For odd `N`, the only unit with `u ^ N = 1` and `u ^ 2 = 1` is `1`. -/
theorem card_u_odd (hodd : Odd N) : Nat.card {u : ℂˣ // u ^ N = 1 ∧ u ^ 2 = 1} = 1 := by
  have hforce : ∀ u : ℂˣ, u ^ N = 1 → u ^ 2 = 1 → u = 1 := by
    intro u huN hu2
    have hg : Nat.gcd N 2 = 1 := Nat.coprime_two_right.mpr hodd
    have hd : orderOf u ∣ 1 :=
      hg ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one huN) (orderOf_dvd_of_pow_eq_one hu2)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨⟨1, one_pow N, one_pow 2⟩⟩⟩
  exact Subtype.ext ((hforce x.1 x.2.1 x.2.2).trans (hforce y.1 y.2.1 y.2.2).symm)

/-- For even `N`, `u ^ 2 = 1` already implies `u ^ N = 1`, so there are two such units. -/
theorem card_u_even (heven : Even N) : Nat.card {u : ℂˣ // u ^ N = 1 ∧ u ^ 2 = 1} = 2 := by
  have hiff : ∀ u : ℂˣ, (u ^ N = 1 ∧ u ^ 2 = 1) ↔ u ^ 2 = 1 := by
    intro u
    refine ⟨fun h => h.2, fun h2 => ⟨?_, h2⟩⟩
    obtain ⟨m, rfl⟩ := heven
    rw [show m + m = 2 * m from by ring, pow_mul, h2, one_pow]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), card_sqrtOne]

/-- **Part (a), count for odd `N`.** The dihedral group `DihedralGroup N` with `N` odd has
exactly `2` one-dimensional complex representations. -/
theorem one_dim_reps_card_odd (hodd : Odd N) : Nat.card (DihedralGroup N →* ℂˣ) = 2 := by
  rw [Nat.card_congr (charEquiv N),
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun u : ℂˣ => u ^ N = 1 ∧ u ^ 2 = 1)
      (q := fun w : ℂˣ => w ^ 2 = 1)),
    Nat.card_prod, card_u_odd hodd, card_sqrtOne]

/-- **Part (a), count for even `N`.** The dihedral group `DihedralGroup N` with `N` even has
exactly `4` one-dimensional complex representations. -/
theorem one_dim_reps_card_even (heven : Even N) : Nat.card (DihedralGroup N →* ℂˣ) = 4 := by
  rw [Nat.card_congr (charEquiv N),
    Nat.card_congr (Equiv.subtypeProdEquivProd (p := fun u : ℂˣ => u ^ N = 1 ∧ u ^ 2 = 1)
      (q := fun w : ℂˣ => w ^ 2 = 1)),
    Nat.card_prod, card_u_even heven, card_sqrtOne]

end OneDim

/-!
## Part (a): exhaustiveness and the odd/even irreducible counts

We now assemble the full classification. The one-dimensional characters
`χ : DihedralGroup N →* ℂˣ` (counted by `one_dim_reps_card_odd`/`_even`) together with the
two-dimensional `Vrep N j` (`2·j ≠ 0`, indexed up to `j ~ -j`) form a complete family of
pairwise non-isomorphic irreducibles whose squared dimensions sum to `|G| = 2N`. By the
Artin-Wedderburn count (`exists_simples_sum_finrank_sq_eq_card`) and a pigeonhole argument,
this family is exactly the set of simples up to isomorphism.
-/

section Classification

open CategoryTheory

variable [NeZero N]

omit [NeZero N] in
/-- `eigen N j 1 = ζ^{j.val}`: the rotation eigenvalue of `V_j` on the first basis vector. -/
theorem eigen_one (j : ZMod N) : eigen N j 1 = zeta N ^ j.val := by
  rw [eigen, mul_one]

/-- Canonical index for the pairwise-non-isomorphic `2`-dimensional irreducibles: the
representative `j` of each pair `{j, -j}` with `2·j ≠ 0`, normalized by `0 < j.val` and
`2·j.val < N`. -/
abbrev TwoDimIdx (N : ℕ) [NeZero N] : Type := {j : ZMod N // 0 < j.val ∧ 2 * j.val < N}

/-- A canonical index really has `2·j ≠ 0`, so `Vrep N j` is irreducible. -/
theorem TwoDimIdx.two_mul_ne (j : TwoDimIdx N) : (2 : ZMod N) * j.1 ≠ 0 := by
  obtain ⟨hpos, hlt⟩ := j.2
  intro hz
  rw [two_mul] at hz
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_add, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hval
  omega

/-- The `2`-dim index type has exactly `(N-1)/2` elements. For even `N` this equals
`(N-2)/2`; for odd `N` it is `(N-1)/2`. -/
theorem card_TwoDimIdx : Fintype.card (TwoDimIdx N) = (N - 1) / 2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  let e : TwoDimIdx N ≃ Fin ((N - 1) / 2) :=
    { toFun := fun j => ⟨j.1.val - 1, by
        obtain ⟨hpos, hlt⟩ := j.2
        have : j.1.val ≤ (N - 1) / 2 := by omega
        omega⟩
      invFun := fun i => ⟨((i.1 + 1 : ℕ) : ZMod N), by
        have hi : i.1 + 1 < N := by have := i.2; omega
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
        have := i.2; omega⟩
      left_inv := fun j => by
        obtain ⟨hpos, hlt⟩ := j.2
        apply Subtype.ext
        change ((j.1.val - 1 + 1 : ℕ) : ZMod N) = j.1
        rw [Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]
      right_inv := fun i => by
        apply Fin.ext
        change ((i.1 + 1 : ℕ) : ZMod N).val - 1 = i.1
        have hi : i.1 + 1 < N := by have := i.2; omega
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
        omega }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- Pigeonhole: an injection `c : ι → Fin n` whose image carries the full positive-weight sum
`∑ f j` is surjective. -/
theorem surj_of_injective_of_sum_eq {n : ℕ} {ι : Type*} [Fintype ι]
    (f : Fin n → ℕ) (hf : ∀ j, 0 < f j) (c : ι → Fin n) (hcinj : Function.Injective c)
    (hsum : ∑ i, f (c i) = ∑ j, f j) : Function.Surjective c := by
  classical
  have himg : ∑ j ∈ Finset.image c Finset.univ, f j = ∑ i, f (c i) :=
    Finset.sum_image (fun a _ b _ hab => hcinj hab)
  have hsplit := Finset.sum_sdiff (f := f) (Finset.subset_univ (Finset.image c Finset.univ))
  rw [himg, hsum] at hsplit
  have hzero : ∑ j ∈ Finset.univ \ Finset.image c Finset.univ, f j = 0 := by omega
  intro j
  have hjmem : j ∈ Finset.image c Finset.univ := by
    by_contra hj
    exact absurd ((Finset.sum_eq_zero_iff.mp hzero) j
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)) (hf j).ne'
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hjmem
  exact ⟨i, hi⟩

/-- `V_j` viewed as an `FDRep`, restricted to a canonical index, is simple. -/
theorem Vrep_fdRep_simple (j : ZMod N) (hj : (2 : ZMod N) * j ≠ 0) :
    Simple (FDRep.of (Vrep N j)) := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) (Vrep N j).asModule :=
    Vrep_irreducible j hj
  exact Etingof.simple_fdRepOf_of_isSimpleModule (Vrep N j)

/-- `FDRep.of (Vrep N j)` is `2`-dimensional. -/
theorem Vrep_finrank (j : ZMod N) : Module.finrank ℂ (FDRep.of (Vrep N j)) = 2 := by
  change Module.finrank ℂ (Fin 2 → ℂ) = 2
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The character of `FDRep.of (Vrep N j)` on the rotation `r k` is `ζ^{jk} + ζ^{-jk}`. -/
theorem Vrep_fdRep_character_r (j k : ZMod N) :
    (FDRep.of (Vrep N j)).character (DihedralGroup.r k) = eigen N j k + (eigen N j k)⁻¹ := by
  have hc : (FDRep.of (Vrep N j)).character (DihedralGroup.r k)
      = LinearMap.trace ℂ _ (Vrep N j (DihedralGroup.r k)) := rfl
  rw [hc, Vrep_trace_r]

/-- Two canonical `2`-dim indices whose rotation characters agree at `r 1` are equal: the value
`ζ^j + ζ^{-j}` determines `{j, -j}`, and the normalization `2·j.val < N` picks out `j`. -/
theorem TwoDimIdx.eq_of_char_eq (j j' : TwoDimIdx N)
    (h : eigen N j.1 1 + (eigen N j.1 1)⁻¹ = eigen N j'.1 1 + (eigen N j'.1 1)⁻¹) :
    j = j' := by
  set a := eigen N j.1 1 with ha_def
  set b := eigen N j'.1 1 with hb_def
  have ha : a ≠ 0 := eigen_ne_zero N j.1 1
  have hb : b ≠ 0 := eigen_ne_zero N j'.1 1
  have hkey : (a - b) * (a * b - 1) = 0 := by
    field_simp at h
    linear_combination h
  rcases mul_eq_zero.mp hkey with hab0 | hab1
  · -- a = b : same eigenvalue, so equal `val`
    have hEq : a = b := sub_eq_zero.mp hab0
    rw [ha_def, hb_def, eigen_one, eigen_one] at hEq
    have hval : (j.1).val = (j'.1).val :=
      isPrimitiveRoot_zeta.pow_inj (ZMod.val_lt j.1) (ZMod.val_lt j'.1) hEq
    exact Subtype.ext (ZMod.val_injective N hval)
  · -- a·b = 1 : forces `j' = -j`, impossible under the normalization
    exfalso
    have hab1' : a * b = 1 := by linear_combination hab1
    rw [ha_def, hb_def, eigen_one, eigen_one, ← pow_add] at hab1'
    have hdvd : N ∣ (j.1).val + (j'.1).val :=
      (isPrimitiveRoot_zeta.pow_eq_one_iff_dvd _).mp hab1'
    obtain ⟨hpos, hlt⟩ := j.2
    obtain ⟨hpos', hlt'⟩ := j'.2
    have hsum_pos : 0 < (j.1).val + (j'.1).val := by omega
    have hsum_lt : (j.1).val + (j'.1).val < N := by omega
    exact absurd (Nat.le_of_dvd hsum_pos hdvd) (by omega)

/-- **Part (a), full classification / exhaustiveness.** Every finite-dimensional simple complex
representation `U` of the dihedral group `DihedralGroup N` is isomorphic either to a
one-dimensional character `charRep χ` (`χ : DihedralGroup N →* ℂˣ`) or to one of the
two-dimensional `Vrep N j` with `2·j ≠ 0`.

The proof exhibits the `Nat.card (DihedralGroup N →* ℂˣ)` characters (`2` for odd `N`, `4` for
even `N`) and the `(N-1)/2` representatives `Vrep N j` as a pairwise non-isomorphic family of
simples whose squared dimensions sum to `|G| = 2N`. Since the Artin-Wedderburn family of all
simples also has squared dimensions summing to `2N` and every term is positive, a pigeonhole
argument shows the exhibited family is complete. -/
theorem simple_iso_char_or_Vrep
    (U : FDRep ℂ (DihedralGroup N)) [hUsimple : Simple U] :
    (∃ χ : DihedralGroup N →* ℂˣ,
        Nonempty (U ≅ FDRep.of (Etingof.Example4_3_S3.charRep χ))) ∨
    (∃ j : ZMod N, (2 : ZMod N) * j ≠ 0 ∧
        Nonempty (U ≅ FDRep.of (Vrep N j))) := by
  classical
  -- `|G| = 2N` is invertible in `ℂ`, so the Wedderburn enumeration applies.
  haveI hNe : NeZero (Nat.card (DihedralGroup N) : ℂ) := by
    refine ⟨?_⟩
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    push_cast
    simpa using mul_ne_zero two_ne_zero hN
  -- The complete family of simples with `∑ dim² = |G| = 2N`.
  obtain ⟨n, V, hVsimple, _hVinj, hVsurj, hVsum⟩ :=
    exists_simples_sum_finrank_sq_eq_card ℂ (DihedralGroup N)
  -- Finiteness (and a `Fintype`) of the character group.
  haveI : Finite (DihedralGroup N →* ℂˣ) := by
    rcases Nat.even_or_odd N with h | h
    · exact Nat.finite_of_card_ne_zero (by rw [one_dim_reps_card_even h]; norm_num)
    · exact Nat.finite_of_card_ne_zero (by rw [one_dim_reps_card_odd h]; norm_num)
  haveI : Fintype (DihedralGroup N →* ℂˣ) := Fintype.ofFinite _
  -- The exhibited family: the characters, and the `2`-dim reps at canonical indices.
  let E : (DihedralGroup N →* ℂˣ) ⊕ TwoDimIdx N → FDRep ℂ (DihedralGroup N) :=
    Sum.elim (fun χ => FDRep.of (Etingof.Example4_3_S3.charRep χ))
      (fun j => FDRep.of (Vrep N j.1))
  have hEfinL : ∀ χ : DihedralGroup N →* ℂˣ, Module.finrank ℂ (E (Sum.inl χ)) = 1 :=
    fun _ => Module.finrank_self ℂ
  have hEfinR : ∀ j : TwoDimIdx N, Module.finrank ℂ (E (Sum.inr j)) = 2 :=
    fun j => Vrep_finrank j.1
  have hEsimple : ∀ i, Simple (E i) := by
    rintro (χ | j)
    · exact Etingof.Example4_3_S3.charRep_simple χ
    · exact Vrep_fdRep_simple j.1 (TwoDimIdx.two_mul_ne j)
  -- The members are pairwise non-isomorphic.
  have hEinj : ∀ i j, Nonempty (E i ≅ E j) → i = j := by
    rintro (χ | j) (χ' | j') ⟨α⟩
    · -- two characters: equal character forces `χ = χ'`
      have hχ : χ = χ' := by
        ext g
        have hg := congrFun (FDRep.char_iso α) g
        rw [show E (Sum.inl χ) = FDRep.of (Etingof.Example4_3_S3.charRep χ) from rfl,
            show E (Sum.inl χ') = FDRep.of (Etingof.Example4_3_S3.charRep χ') from rfl,
            Etingof.Example4_3_S3.charRep_character,
            Etingof.Example4_3_S3.charRep_character] at hg
        exact_mod_cast hg
      rw [hχ]
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinL χ, hEfinR j'] at hfr; omega
    · exfalso
      have hfr := LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv α)
      rw [hEfinR j, hEfinL χ'] at hfr; omega
    · -- two `2`-dim reps: character at `r 1` separates them
      have hg := congrFun (FDRep.char_iso α) (DihedralGroup.r 1)
      rw [show E (Sum.inr j) = FDRep.of (Vrep N j.1) from rfl,
          show E (Sum.inr j') = FDRep.of (Vrep N j'.1) from rfl,
          Vrep_fdRep_character_r, Vrep_fdRep_character_r] at hg
      exact congrArg Sum.inr (TwoDimIdx.eq_of_char_eq j j' hg)
  -- Inject the family into the enumeration.
  choose c hc using fun i => hVsurj (E i) (hEsimple i)
  have hc_inj : Function.Injective c := by
    intro i j hij
    obtain ⟨αi⟩ := hc i; obtain ⟨αj⟩ := hc j
    exact hEinj i j ⟨αi ≪≫ eqToIso (congrArg V hij) ≪≫ αj.symm⟩
  have hfinrankc : ∀ i, Module.finrank ℂ (E i) = Module.finrank ℂ (V (c i)) := fun i =>
    LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hc i).some)
  -- Squared dimensions of the family sum to `2N`.
  have hEsum : ∑ i, (Module.finrank ℂ (E i)) ^ 2 = 2 * N := by
    rw [Fintype.sum_sum_type]
    have hL : ∑ χ : DihedralGroup N →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2
        = Fintype.card (DihedralGroup N →* ℂˣ) := by
      have hone : ∀ χ : DihedralGroup N →* ℂˣ, (Module.finrank ℂ (E (Sum.inl χ))) ^ 2 = 1 := by
        intro χ; rw [hEfinL χ, one_pow]
      rw [Finset.sum_congr rfl (fun χ _ => hone χ), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_one]
    have hR : ∑ j : TwoDimIdx N, (Module.finrank ℂ (E (Sum.inr j))) ^ 2
        = 4 * Fintype.card (TwoDimIdx N) := by
      have hfour : ∀ j : TwoDimIdx N, (Module.finrank ℂ (E (Sum.inr j))) ^ 2 = 4 := by
        intro j; rw [hEfinR j]; norm_num
      rw [Finset.sum_congr rfl (fun j _ => hfour j), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_comm]
    rw [hL, hR]
    -- `#chars + 4·#idx = 2N`, by parity.
    rcases Nat.even_or_odd N with h | h
    · rw [← Nat.card_eq_fintype_card, one_dim_reps_card_even h, card_TwoDimIdx]
      obtain ⟨m, rfl⟩ := h
      have hm : m ≠ 0 := by have := (NeZero.ne (m + m)); omega
      omega
    · rw [← Nat.card_eq_fintype_card, one_dim_reps_card_odd h, card_TwoDimIdx]
      obtain ⟨m, rfl⟩ := h
      omega
  -- The full sum of squared dimensions is also `2N`.
  have hVsum2 : ∑ j, (Module.finrank ℂ (V j)) ^ 2 = 2 * N := by
    rw [hVsum, DihedralGroup.card]
  have hmatch : ∑ i, (Module.finrank ℂ (V (c i))) ^ 2 = ∑ j, (Module.finrank ℂ (V j)) ^ 2 := by
    rw [hVsum2, ← hEsum]
    exact Finset.sum_congr rfl (fun i _ => by rw [hfinrankc i])
  -- Every simple has positive dimension, so the injection `c` is surjective.
  have hVpos : ∀ j, 0 < (Module.finrank ℂ (V j)) ^ 2 := by
    intro j
    haveI : Simple (V j) := hVsimple j
    haveI : IsSimpleModule (MonoidAlgebra ℂ (DihedralGroup N)) (Representation.asModule (V j).ρ) :=
      Etingof.isSimpleModule_asModule_of_simple (V j)
    haveI : Nontrivial (Representation.asModule (V j).ρ) :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (DihedralGroup N)) _
    haveI : Nontrivial ↥(V j) := (Representation.asModuleEquiv (V j).ρ).symm.toEquiv.nontrivial
    exact pow_pos Module.finrank_pos 2
  have hcsurj : Function.Surjective c :=
    surj_of_injective_of_sum_eq _ hVpos c hc_inj hmatch
  -- Read off the branch of the index matching `U`.
  obtain ⟨j0, hj0U⟩ := hVsurj U hUsimple
  obtain ⟨i, hci⟩ := hcsurj j0
  have hUEi : Nonempty (U ≅ E i) :=
    ⟨hj0U.some ≪≫ eqToIso (congrArg V hci).symm ≪≫ (hc i).some.symm⟩
  rcases i with χ | j
  · exact Or.inl ⟨χ, hUEi⟩
  · exact Or.inr ⟨j.1, TwoDimIdx.two_mul_ne j, hUEi⟩

/-- **Part (a), number of `2`-dimensional irreducibles (odd `N`).** There are exactly `(N-1)/2`
isomorphism classes of `2`-dimensional simple complex representations of `DihedralGroup N`,
indexed by `TwoDimIdx N`. -/
theorem two_dim_simples_card_odd (_hodd : Odd N) :
    Fintype.card (TwoDimIdx N) = (N - 1) / 2 := card_TwoDimIdx

/-- **Part (a), number of `2`-dimensional irreducibles (even `N`).** There are exactly `(N-2)/2`
isomorphism classes of `2`-dimensional simple complex representations of `DihedralGroup N`. -/
theorem two_dim_simples_card_even (heven : Even N) :
    Fintype.card (TwoDimIdx N) = (N - 2) / 2 := by
  rw [card_TwoDimIdx]; obtain ⟨m, rfl⟩ := heven; omega

/-- **Part (a), sum-of-squares identity.** The one-dimensional and two-dimensional irreducibles
account for the full regular representation: `#{1-dim}·1² + #{2-dim}·2² = 2N = |G|`. -/
theorem irreps_sum_sq :
    Nat.card (DihedralGroup N →* ℂˣ) * 1 + Fintype.card (TwoDimIdx N) * 4 = 2 * N := by
  rw [card_TwoDimIdx]
  rcases Nat.even_or_odd N with h | h
  · rw [one_dim_reps_card_even h]; obtain ⟨m, rfl⟩ := h
    have hm : m ≠ 0 := by have := (NeZero.ne (m + m)); omega
    omega
  · rw [one_dim_reps_card_odd h]; obtain ⟨m, rfl⟩ := h; omega

/-- **Part (a), total number of irreducibles (odd `N`).** For odd `N` there are `2 + (N-1)/2`
isomorphism classes of irreducible complex representations of `DihedralGroup N`. -/
theorem total_irreps_card_odd (hodd : Odd N) :
    Nat.card (DihedralGroup N →* ℂˣ) + Fintype.card (TwoDimIdx N) = 2 + (N - 1) / 2 := by
  rw [one_dim_reps_card_odd hodd, card_TwoDimIdx]

/-- **Part (a), total number of irreducibles (even `N`).** For even `N` there are `4 + (N-2)/2`
isomorphism classes of irreducible complex representations of `DihedralGroup N`. -/
theorem total_irreps_card_even (heven : Even N) :
    Nat.card (DihedralGroup N →* ℂˣ) + Fintype.card (TwoDimIdx N) = 4 + (N - 2) / 2 := by
  rw [one_dim_reps_card_even heven, two_dim_simples_card_even heven]

end Classification

/-! ## Part (b): the isomorphism-level decomposition `V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂`

The character identity `tensor_square_character` becomes an actual isomorphism of representations
by the fact that over `ℂ` a finite-dimensional representation of a finite group is determined by
its character (`Etingof.Corollary4_2_4`). We identify the complexified standard representation `V`
with `Vrep N 1` (rotation character `ζ^k + ζ^{-k} = χ_V`, by `Vrep_trace_r` at `j = 1`), the
`2`-dimensional rotation-by-`4π/N` representation `V₂` with `Vrep N 2` (character
`ζ^{2k} + ζ^{-2k} = χ_{V₂}`, by `Vrep_trace_r` at `j = 2`), the sign representation `ε` with the
character `signHom`, and `𝟙` with the trivial character. The decomposition holds for every
`N ≥ 1`; for `N ≥ 3` the three summands are the irreducible constituents. -/

section Decomposition

open CategoryTheory MonoidalCategory

variable {N : ℕ}

/-- The trace of `V_j` on a reflection `sr k` is `0` (the matrix is anti-diagonal). -/
theorem Vrep_trace_sr [NeZero N] (j k : ZMod N) :
    LinearMap.trace ℂ (Fin 2 → ℂ) (Vrep N j (DihedralGroup.sr k)) = 0 := by
  have hrfl : Vrep N j (DihedralGroup.sr k)
      = Matrix.toLin' (repMat N j (DihedralGroup.sr k)) := rfl
  rw [hrfl, Matrix.trace_toLin'_eq]
  simp [repMat, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- The character of `FDRep.of (Vrep N j)` on a reflection `sr k` is `0`. -/
theorem Vrep_fdRep_character_sr [NeZero N] (j k : ZMod N) :
    (FDRep.of (Vrep N j)).character (DihedralGroup.sr k) = 0 := by
  have hc : (FDRep.of (Vrep N j)).character (DihedralGroup.sr k)
      = LinearMap.trace ℂ _ (Vrep N j (DihedralGroup.sr k)) := rfl
  rw [hc, Vrep_trace_sr]

/-- **`V = V₁`.** The character of `Vrep N 1` is `chiStd N`, the character of the complexified
standard representation. -/
theorem chiStd_eq_Vrep1_character [NeZero N] (g : DihedralGroup N) :
    (FDRep.of (Vrep N 1)).character g = chiStd N g := by
  cases g with
  | r k => rw [Vrep_fdRep_character_r]; simp only [chiStd, eigen, one_mul, inv_pow]
  | sr k => rw [Vrep_fdRep_character_sr]; rfl

/-- **`V₂ = V₂'`.** The character of `Vrep N 2` is `chiRot2 N`, the character of the
rotation-by-`4π/N` representation. -/
theorem chiRot2_eq_Vrep2_character [NeZero N] (g : DihedralGroup N) :
    (FDRep.of (Vrep N 2)).character g = chiRot2 N g := by
  cases g with
  | r k =>
    have hval : ((2 : ZMod N) * k).val = (2 * k.val) % N := by
      have h : (2 : ZMod N) * k = ((2 * k.val : ℕ) : ZMod N) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [h, ZMod.val_natCast]
    have h2 : eigen N 2 k = zeta N ^ (2 * k.val) := by
      unfold eigen; rw [hval, zeta_pow_mod]
    rw [Vrep_fdRep_character_r, h2]; simp only [chiRot2, inv_pow]
  | sr k => rw [Vrep_fdRep_character_sr]; rfl

/-- The one-dimensional representation on `ℂ` attached to a character `χ : DihedralGroup N →* ℂˣ`:
`g` acts by multiplication by `χ g`. -/
def charRep (χ : DihedralGroup N →* ℂˣ) : Representation ℂ (DihedralGroup N) ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The character of `charRep χ` is `g ↦ χ g`. -/
theorem charRep_character (χ : DihedralGroup N →* ℂˣ) (g : DihedralGroup N) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  have hg : charRep χ g = (χ g : ℂ) • LinearMap.id := rfl
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', hg, map_smul, LinearMap.trace_id]
  simp

/-- The sign character `ε` of the dihedral group: rotations act by `1`, reflections by `-1`. -/
def signHom (N : ℕ) : DihedralGroup N →* ℂˣ where
  toFun g := match g with
    | .r _ => 1
    | .sr _ => -1
  map_one' := by rw [DihedralGroup.one_def]
  map_mul' a b := by
    cases a <;> cases b <;>
      simp [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr]

/-- The values of `signHom` recover the character `chiSign` of the sign representation. -/
theorem signHom_val_eq_chiSign (g : DihedralGroup N) :
    ((signHom N g : ℂˣ) : ℂ) = chiSign N g := by
  cases g with
  | r k => rfl
  | sr k => rfl

/-- Character additivity for the product of two representations. -/
theorem char_prod {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (DihedralGroup N) V) (σ : Representation ℂ (DihedralGroup N) W)
    (g : DihedralGroup N) :
    (FDRep.of (ρ.prod σ)).character g
      = (FDRep.of ρ).character g + (FDRep.of σ).character g := by
  change LinearMap.trace ℂ (V × W) ((ρ.prod σ) g)
    = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)
  have h : (ρ.prod σ) g = (ρ g).prodMap (σ g) := rfl
  rw [h]; exact LinearMap.trace_prodMap' (ρ g) (σ g)

/-- The right-hand side `𝟙 ⊕ ε ⊕ V₂` as a representation of the dihedral group: the trivial
character, the sign character `signHom`, and the `2`-dimensional `Vrep N 2`. -/
noncomputable def rhsRep (N : ℕ) [NeZero N] :
    Representation ℂ (DihedralGroup N) (ℂ × ℂ × (Fin 2 → ℂ)) :=
  (charRep (1 : DihedralGroup N →* ℂˣ)).prod ((charRep (signHom N)).prod (Vrep N 2))

/-- The character of `𝟙 ⊕ ε ⊕ V₂` is `1 + χ_ε + χ_{V₂}`. -/
theorem rhsRep_character [NeZero N] (g : DihedralGroup N) :
    (FDRep.of (rhsRep N)).character g = 1 + chiSign N g + chiRot2 N g := by
  rw [rhsRep, char_prod, char_prod, charRep_character, charRep_character,
    chiRot2_eq_Vrep2_character, signHom_val_eq_chiSign]
  simp only [MonoidHom.one_apply, Units.val_one]
  ring

/-- **Part (b), isomorphism-level decomposition.** As representations of `DihedralGroup N`,
`V ⊗ V ≅ 𝟙 ⊕ ε ⊕ V₂`, where `V = Vrep N 1` is the complexified standard representation, `𝟙` is
trivial, `ε` is the sign representation, and `V₂ = Vrep N 2`. This upgrades the character identity
`tensor_square_character` to a genuine isomorphism of `FDRep ℂ (DihedralGroup N)`, using that over
`ℂ` a finite-dimensional representation of a finite group is determined by its character
(`Etingof.Corollary4_2_4`). -/
theorem tensor_square_decomposition [NeZero N] :
    Nonempty ((FDRep.of (Vrep N 1) ⊗ FDRep.of (Vrep N 1)) ≅ FDRep.of (rhsRep N)) := by
  apply Etingof.Corollary4_2_4 (DihedralGroup N)
  funext g
  rw [FDRep.char_tensor, Pi.mul_apply, chiStd_eq_Vrep1_character, rhsRep_character,
    ← sq, tensor_square_character]

end Decomposition

end Etingof.Problem4_12_1
