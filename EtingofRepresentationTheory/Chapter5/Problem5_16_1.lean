import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1

/-!
# Problem 5.16.1: the branching rule for `Sₙ ⊆ Sₙ₊₁`

**Problem 5.16.1.** For a Young diagram `μ`, let `A(μ)` be the set of Young diagrams obtained by
adding a square to `μ`, and let `R(μ)` be the set of Young diagrams obtained by removing a square
from `μ`.

(a) Show that `Res_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ R(μ)} V_λ`.

(b) Show that `Ind_{S_{n-1}}^{S_n} V_μ = ⨁_{λ ∈ A(μ)} V_λ`.

## Formalization

We index by `n` and `n+1` (avoiding natural-number subtraction). `Sₙ = Equiv.Perm (Fin n)` is
embedded into `Sₙ₊₁ = Equiv.Perm (Fin (n+1))` as the pointwise stabilizer of the last point via
`permEmb := Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb`.

* **Adding/removing a square via containment.** A Young diagram of size `n` obtained by removing one
  square from `μ ⊢ n+1` is exactly a diagram `λ ⊢ n` contained in `μ` (`λ ⊆ μ`); dually a diagram of
  size `n+1` obtained by adding a square to `μ ⊢ n` is a `λ ⊢ n+1` containing `μ`. So
  `removeSquare μ = {λ : Nat.Partition n // λ ⊆ μ}` and `addSquare μ = {λ : Nat.Partition (n+1) //
  μ ⊆ λ}`, using containment of `Nat.Partition.toYoungDiagram`.
* **(a) Restriction.** The character of `Res V_μ` (the character of `V_μ` evaluated on the image of
  `Sₙ` in `Sₙ₊₁`) equals the sum of the characters of the `V_λ` for `λ ∈ R(μ)`. Over `ℂ`, this
  character identity is equivalent to the isomorphism `Res V_μ ≅ ⨁_{λ ∈ R(μ)} V_λ`.
* **(b) Induction.** By Frobenius reciprocity the multiplicity of `V_λ` (`λ ⊢ n+1`) in
  `Ind_{Sₙ}^{Sₙ₊₁} V_μ` equals the multiplicity of `V_μ` in `Res V_λ`, i.e. the reciprocity pairing
  `⟨χ_{V_μ}, Res χ_{V_λ}⟩_{Sₙ}`. We state that this pairing is `1` if `μ ⊆ λ` (`λ ∈ A(μ)`) and `0`
  otherwise — precisely `Ind V_μ = ⨁_{λ ∈ A(μ)} V_λ`.

Statement pass: the proofs are left as `sorry`.
-/

noncomputable section

namespace Etingof

open scoped Classical

/-- The embedding `Sₙ ↪ Sₙ₊₁` as the pointwise stabilizer of the last point of `Fin (n+1)`,
extending a permutation of `Fin n` by the identity via `Fin.castSuccEmb`. -/
noncomputable def permEmb (n : ℕ) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

/-- `R(μ)` for `μ ⊢ n+1`: the Young diagrams obtained by removing one square, i.e. the partitions
`λ ⊢ n` whose diagram is contained in that of `μ`. -/
noncomputable def removeSquare {n : ℕ} (μ : Nat.Partition (n + 1)) :
    Finset (Nat.Partition n) :=
  Finset.univ.filter fun la => la.toYoungDiagram ≤ μ.toYoungDiagram

/-- `A(μ)` for `μ ⊢ n`: the Young diagrams obtained by adding one square, i.e. the partitions
`λ ⊢ n+1` whose diagram contains that of `μ`. -/
noncomputable def addSquare {n : ℕ} (μ : Nat.Partition n) :
    Finset (Nat.Partition (n + 1)) :=
  Finset.univ.filter fun la => μ.toYoungDiagram ≤ la.toYoungDiagram

/-- The Frobenius-reciprocity pairing of two class functions on `Sₙ`:
`⟨χ, ψ⟩ = |Sₙ|⁻¹ Σ_σ χ(σ) ψ(σ⁻¹)`. -/
noncomputable def branchingPairing (n : ℕ)
    (χ ψ : Equiv.Perm (Fin n) → ℂ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), χ σ * ψ σ⁻¹

/-- Problem 5.16.1(a). Branching rule for restriction: for `μ ⊢ n+1`, the restriction of the
Specht module `V_μ` to `Sₙ ⊆ Sₙ₊₁` decomposes as `⨁_{λ ∈ R(μ)} V_λ`. Equivalently, on every
`σ ∈ Sₙ` the character of `V_μ` at the image `permEmb σ` equals the sum of the characters of the
`V_λ` over `λ ∈ R(μ)`. -/
theorem res_spechtModule_character (n : ℕ) (μ : Nat.Partition (n + 1))
    (σ : Equiv.Perm (Fin n)) :
    spechtModuleCharacter (n + 1) μ (permEmb n σ) =
      ∑ la ∈ removeSquare μ, spechtModuleCharacter n la σ := by
  -- Proof strategy (Frobenius character formula / Pieri rule for `p₁`), scoped as a
  -- separate work item. Bridge both sides to `charValue` (Proposition5_21_1) over `N = n+1`
  -- variables via `charValue_eq_spechtModuleCharacter` and
  -- `exists_boundedPartition_weightToPartition_eq`. Writing `Δ = det(alternantMatrix (vandermondeExps))`
  -- and `g = Δ · psumPart (fullCycleTypePartition σ)` (antisymmetric, since `psumPart` is symmetric
  -- and `Δ` antisymmetric), the key facts are:
  --   1. `fullCycleType (n+1) (permEmb n σ) = 1 ::ₘ fullCycleType n σ` (embedding adds a fixed point),
  --      hence `psumPart (fullCycleTypePartition (permEmb n σ)) = psum 1 * psumPart (fullCycleTypePartition σ)`
  --      where `psum 1 = ∑ⱼ Xⱼ`.
  --   2. `coeff_{μ+ρ}((∑ⱼ Xⱼ) · g) = ∑ⱼ coeff_{μ+ρ-eⱼ}(g)` (`MvPolynomial.coeff_X_mul` termwise).
  --   3. `coeff_{μ+ρ-eⱼ}(g) = charValue` of the box-removal `λ = μ - eⱼ` when that is a valid
  --      partition (`μⱼ > μⱼ₊₁`), and `= 0` otherwise, because `μ+ρ-eⱼ` then has a repeated entry and
  --      `g` is antisymmetric (`coeff_zero_of_antisym_repeated`, `rename_alternant_det`).
  --   4. The legal box-removal rows `j` biject with `removeSquare μ = {λ ⊢ n : λ.toYoungDiagram ≤
  --      μ.toYoungDiagram}`, matching `shiftedExps (bp_λ.parts) = μ+ρ-eⱼ`.
  -- See GitHub issue tracking this sub-task.
  sorry

/-- Problem 5.16.1(b). Branching rule for induction: for `μ ⊢ n`, the induced module
`Ind_{Sₙ}^{Sₙ₊₁} V_μ` decomposes as `⨁_{λ ∈ A(μ)} V_λ`. By Frobenius reciprocity the multiplicity
of `V_λ` (`λ ⊢ n+1`) in the induced module is the reciprocity pairing of `χ_{V_μ}` with the
restriction of `χ_{V_λ}`; this multiplicity is `1` when `λ ∈ A(μ)` (i.e. `μ ⊆ λ`) and `0`
otherwise. -/
theorem ind_spechtModule_multiplicity (n : ℕ) (μ : Nat.Partition n)
    (la : Nat.Partition (n + 1)) :
    branchingPairing n (spechtModuleCharacter n μ)
        (fun σ => spechtModuleCharacter (n + 1) la (permEmb n σ)) =
      if μ.toYoungDiagram ≤ la.toYoungDiagram then 1 else 0 := by
  classical
  have hcard : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) = (Nat.factorial n : ℂ) := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hne : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  -- Expand the pairing using part (a) (restriction branching) and character orthonormality.
  have hexpand :
      ∑ σ : Equiv.Perm (Fin n),
        spechtModuleCharacter n μ σ *
          spechtModuleCharacter (n + 1) la (permEmb n σ⁻¹)
        = (Nat.factorial n : ℂ) *
            ∑ ρ ∈ removeSquare la, (if μ = ρ then (1 : ℂ) else 0) := by
    -- Apply the restriction rule at `σ⁻¹`, distribute, swap the sums, and use orthonormality.
    have e1 : ∑ σ : Equiv.Perm (Fin n),
        spechtModuleCharacter n μ σ *
          spechtModuleCharacter (n + 1) la (permEmb n σ⁻¹)
        = ∑ σ : Equiv.Perm (Fin n),
            ∑ ρ ∈ removeSquare la,
              spechtModuleCharacter n μ σ * spechtModuleCharacter n ρ σ⁻¹ := by
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [res_spechtModule_character n la σ⁻¹, Finset.mul_sum]
    rw [e1, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    rw [specht_char_inner n μ ρ]
  unfold branchingPairing
  dsimp only
  rw [hexpand, hcard, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  simp only [Finset.sum_ite_eq, removeSquare, Finset.mem_filter, Finset.mem_univ, true_and]

end Etingof
