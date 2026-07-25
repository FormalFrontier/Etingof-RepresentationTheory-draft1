import Mathlib
import EtingofRepresentationTheory.Infrastructure.FDRepIsotypic
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Section 4.9: Computing tensor product multiplicities using character tables

The introduction to §4.9 states, for irreducibles `Vᵢ, Vⱼ, Vₖ` of a finite group `G` over `ℂ`,

`Vᵢ ⊗ Vⱼ = Σₖ Nᵏᵢⱼ Vₖ`,  `Nᵏᵢⱼ = (χᵢ χⱼ, χₖ)`.

This file formalizes both halves for arbitrary finite-dimensional `X`, `Y` and an arbitrary
complete family of irreducibles.

## Main results

* `Etingof.tensorMultiplicity X Y S = finrank ℂ (S ⟶ X ⊗ Y)` is the multiplicity of `S` in
  `X ⊗ Y`.
* `Etingof.tensorMultiplicity_eq_inner` : the source's inner-product formula
  `Nᵏᵢⱼ = (1/|G|) Σ_g χ_X(g) χ_Y(g) χ_S(g⁻¹)`. It is `FDRep.char_tensor` fed into
  `Etingof.Theorem4_5_1_i` and needs no simplicity hypothesis; simplicity of `S` is what makes
  the Hom dimension a *constituent* multiplicity.
* `Etingof.tensorDecomposition` : an isomorphism in `FDRep ℂ G`

  `X ⊗ Y ≅ ⨁ₖ (Vₖ)^(Nᵏ)`,  `Nᵏ = tensorMultiplicity X Y Vₖ`,

  for any complete family `V` of pairwise non-isomorphic irreducibles. This is a genuine
  representation isomorphism obtained from semisimplicity (Maschke), not a character identity;
  see `EtingofRepresentationTheory.Infrastructure.FDRepIsotypic`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Module

namespace Etingof

variable {G : Type} [Group G] [Fintype G]

/-- The **tensor-product multiplicity** `N^S_{X,Y}` of `S` in `X ⊗ Y`: the dimension of the
space of intertwiners `S → X ⊗ Y`. For simple `S` this is the number of copies of `S` in the
decomposition of `X ⊗ Y` into irreducibles (`Etingof.tensorDecomposition`). -/
noncomputable def tensorMultiplicity (X Y S : FDRep ℂ G) : ℕ := finrank ℂ (S ⟶ X ⊗ Y)

/-- **The multiplicity formula of §4.9**: `Nᵏᵢⱼ = (χᵢ χⱼ, χₖ)`, i.e.

`N = (1/|G|) Σ_{g ∈ G} χ_X(g) χ_Y(g) χ_S(g⁻¹)`.

This is `FDRep.char_tensor` (the character of a tensor product is the product of the
characters) composed with Theorem 4.5.1(i) (the character inner product is a Hom dimension).
No simplicity assumption is needed for the identity itself. -/
theorem tensorMultiplicity_eq_inner (X Y S : FDRep ℂ G) :
    (tensorMultiplicity X Y S : ℂ) =
      ⅟(Fintype.card G : ℂ) • ∑ g : G, (X.character g * Y.character g) * S.character g⁻¹ := by
  rw [tensorMultiplicity, ← Etingof.Theorem4_5_1_i (X ⊗ Y) S]
  simp only [FDRep.char_tensor, Pi.mul_apply]

section Decomposition

variable {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → FDRep ℂ G)
  (hV : ∀ i, Simple (V i)) (hinj : ∀ i j, Nonempty (V i ≅ V j) → i = j)
  (hcomplete : ∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ V i))

/-- The right-hand side `Σₖ Nᵏᵢⱼ Vₖ` of the source's decomposition: the direct sum of
`tensorMultiplicity X Y (V k)` copies of `V k`, over all `k`. -/
noncomputable def tensorDecompositionTarget (X Y : FDRep ℂ G) : FDRep ℂ G :=
  Etingof.FDRep.isotypicSum V (tensorMultiplicity X Y <| V ·)

include hV hinj hcomplete in
/-- **The tensor-product decomposition of §4.9**, as an isomorphism of representations:

`X ⊗ Y ≅ ⨁ₖ (Vₖ)^(Nᵏ)` with `Nᵏ = tensorMultiplicity X Y Vₖ = (χ_X χ_Y, χ_{Vₖ})`.

Here `V` is any complete family of pairwise non-isomorphic irreducibles of `G` over `ℂ`. The
isomorphism comes from semisimplicity of `FDRep ℂ G` (Maschke) together with Schur's lemma; the
multiplicities are identified with the character inner products by
`Etingof.tensorMultiplicity_eq_inner`. -/
theorem tensorDecomposition (X Y : FDRep ℂ G) :
    Nonempty (X ⊗ Y ≅ tensorDecompositionTarget V X Y) := by
  have h := Etingof.FDRep.nonempty_iso_isotypicSum V hV hinj hcomplete (X ⊗ Y)
  have hmul : Etingof.FDRep.multiplicity V (X ⊗ Y) = (tensorMultiplicity X Y <| V ·) := rfl
  rwa [hmul] at h

include hV hinj hcomplete in
/-- The multiplicity read off the decomposition is the one computed by the character formula:
for each `k`, the number of copies of `Vₖ` in `X ⊗ Y` is `dim Hom(Vₖ, X ⊗ Y)`, and
`Etingof.tensorMultiplicity_eq_inner` evaluates it as `(χ_X χ_Y, χ_{Vₖ})`. -/
theorem finrank_hom_eq_sum_tensorMultiplicity (X Y S : FDRep ℂ G) :
    finrank ℂ (S ⟶ X ⊗ Y) =
      ∑ i, tensorMultiplicity X Y (V i) * finrank ℂ (S ⟶ V i) :=
  Etingof.FDRep.finrank_hom_eq_sum_multiplicity V hV hinj hcomplete (X ⊗ Y) S

end Decomposition

/-- **Unconditional form.** Every finite group has a complete family of pairwise
non-isomorphic irreducibles over `ℂ` — the Wedderburn-Artin column representations of
`IrrepDecomp` — so the decomposition `X ⊗ Y ≅ ⨁ₖ (Vₖ)^(Nᵏ)` of §4.9 holds for every pair of
finite-dimensional representations, with no family supplied in advance. -/
theorem exists_tensorDecomposition (X Y : FDRep ℂ G) :
    ∃ (n : ℕ) (V : Fin n → FDRep ℂ G),
      (∀ i, Simple (V i)) ∧ (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ S : FDRep ℂ G, Simple S → ∃ i, Nonempty (S ≅ V i)) ∧
      Nonempty (X ⊗ Y ≅ tensorDecompositionTarget V X Y) := by
  haveI : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let D : IrrepDecomp ℂ G := IrrepDecomp.mk'
  refine ⟨D.n, D.columnFDRep, D.columnFDRep_simple, fun i j h => D.columnFDRep_injective i j h,
    fun S hS => D.columnFDRep_surjective S hS, ?_⟩
  exact tensorDecomposition D.columnFDRep D.columnFDRep_simple
    (fun i j h => D.columnFDRep_injective i j h)
    (fun S hS => D.columnFDRep_surjective S hS) X Y

end Etingof
