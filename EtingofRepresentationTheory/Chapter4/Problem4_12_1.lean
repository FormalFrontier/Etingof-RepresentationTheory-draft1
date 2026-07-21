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

end Etingof.Problem4_12_1
