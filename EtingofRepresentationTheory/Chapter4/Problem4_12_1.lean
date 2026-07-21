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

end Etingof.Problem4_12_1
