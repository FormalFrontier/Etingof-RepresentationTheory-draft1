import Mathlib
import EtingofRepresentationTheory.Chapter5.RealTypeSymmetricGroup
import EtingofRepresentationTheory.Chapter5.Corollary5_1_6

/-!
# Problem 5.12.5: the sum of dimensions of the irreducible representations of `S_n`

**Problem 5.12.5.** Find the sum of dimensions of all irreducible representations of the
symmetric group `S_n`.

*Hint.* Show that all irreducible representations of `S_n` are real, i.e., admit a
nondegenerate invariant symmetric form. Then use the Frobenius-Schur theorem.

## Formalization

The Frobenius-Schur theorem gives, for any finite group `G` all of whose irreducibles are of
real type, the identity
`∑_{V irreducible} dim V = #{g ∈ G : g² = 1}`
(the number of elements whose square is the identity, the "square roots of `1`"). For the
symmetric group every irreducible is real
(`Etingof.isRealType_of_isSimpleModule_symmetricGroup`), so the sought sum of dimensions is
the number of involutions-or-identity of `S_n`.

We phrase the answer against an arbitrary complete, irredundant list of irreducible complex
representations `V : ι → FDRep ℂ (Equiv.Perm (Fin n))`:

* `hsimple`: each `V i` is irreducible (`CategoryTheory.Simple`);
* `hpairwise`: the `V i` are pairwise non-isomorphic;
* `hcomplete`: every irreducible is isomorphic to some `V i`.

Under these hypotheses the sum of dimensions equals `#{g : g * g = 1}`.

The proof: reality (`isRealType_of_isSimpleModule_symmetricGroup`) plus the reverse
Frobenius-Schur result (`frobeniusSchurIndicator_eq_one_of_isRealType`) give `FS = 1` for every
irreducible; `Etingof.Corollary5_1_6` then collapses Theorem 5.1.5's
`∑ dim Vᵢ · FS(Vᵢ)` to `∑ dim Vᵢ = #{g : g² = 1}` for the Wedderburn family `columnFDRep`; a
dimension-preserving bijection aligns the given complete family `V` with that family.
-/

namespace Etingof

open CategoryTheory

/-- The FDRep-level Frobenius-Schur indicator (`FDRep.frobeniusSchurIndicator`) agrees with the
representation-level one (`Etingof.frobeniusSchurIndicator`): both are
`|G|⁻¹ ∑_g χ_V(g²)`, and `V.character g = tr(V.ρ g)`. -/
private lemma fdRep_frobeniusSchurIndicator_eq {G : Type} [Group G] [Fintype G] [DecidableEq G]
    [Invertible (Fintype.card G : ℂ)] (W : FDRep ℂ G) :
    W.frobeniusSchurIndicator = Etingof.frobeniusSchurIndicator W.ρ := by
  unfold FDRep.frobeniusSchurIndicator Etingof.frobeniusSchurIndicator
  rw [invOf_eq_inv, smul_eq_mul]
  rfl

/-- Problem 5.12.5. For a complete irredundant family `V` of irreducible complex representations
of `S_n = Equiv.Perm (Fin n)`, the sum of their dimensions equals the number of elements
`g ∈ S_n` with `g² = 1` (the Frobenius-Schur count, valid because every irreducible of `S_n`
is of real type). -/
theorem sum_finrank_irreducible_eq_card_sq_eq_one
    (n : ℕ)
    (ι : Type) [Fintype ι]
    (V : ι → FDRep ℂ (Equiv.Perm (Fin n)))
    (hsimple : ∀ i, Simple (V i))
    (hpairwise : ∀ i j, Nonempty (V i ≅ V j) → i = j)
    (hcomplete : ∀ W : FDRep ℂ (Equiv.Perm (Fin n)), Simple W → ∃ i, Nonempty (W ≅ V i)) :
    ∑ i, Module.finrank ℂ (V i) =
      Fintype.card {g : Equiv.Perm (Fin n) // g * g = 1} := by
  classical
  set G := Equiv.Perm (Fin n) with hG
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  -- The Wedderburn-Artin family of irreducibles of `ℂ[Sₙ]`.
  let D : IrrepDecomp ℂ G := IrrepDecomp.mk'
  -- Every irreducible has Frobenius-Schur indicator `1` (key reality input).
  have h_all_real : ∀ i, (D.columnFDRep i).frobeniusSchurIndicator = 1 := by
    intro i
    rw [fdRep_frobeniusSchurIndicator_eq]
    exact Etingof.frobeniusSchurIndicator_symmetricGroup_eq_one n (D.columnFDRep i).ρ
      (D.isSimpleModule_columnRep_asModule i)
  -- Corollary 5.1.6 applied to the Wedderburn family: the involution count equals `∑ dim`.
  have hcor := Etingof.Corollary5_1_6 D D.columnFDRep D.columnFDRep_simple
    D.columnFDRep_injective h_all_real
  -- A dimension-preserving bijection aligns `V` with the Wedderburn family.
  have hsumeq : ∑ i, Module.finrank ℂ (V i) = ∑ j, Module.finrank ℂ (D.columnFDRep j) := by
    choose τ hτ using fun i => D.columnFDRep_surjective (V i) (hsimple i)
    have hτinj : Function.Injective τ := fun i j h =>
      hpairwise i j ⟨(hτ i).some ≪≫ (h ▸ (hτ j).some.symm)⟩
    have hτsurj : Function.Surjective τ := by
      intro j
      obtain ⟨i, hi⟩ := hcomplete (D.columnFDRep j) (D.columnFDRep_simple j)
      exact ⟨i, (D.columnFDRep_injective j (τ i) ⟨hi.some ≪≫ (hτ i).some⟩).symm⟩
    let e := Equiv.ofBijective τ ⟨hτinj, hτsurj⟩
    calc ∑ i, Module.finrank ℂ (V i)
        = ∑ i, Module.finrank ℂ (D.columnFDRep (τ i)) :=
          Finset.sum_congr rfl fun i _ =>
            LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv (hτ i).some)
      _ = ∑ j, Module.finrank ℂ (D.columnFDRep j) :=
          Equiv.sum_comp e (fun j => Module.finrank ℂ (D.columnFDRep j))
  -- Cast to `ℂ`, combine, and cast back.
  have hcast : ((∑ i, Module.finrank ℂ (V i) : ℕ) : ℂ)
      = ((∑ j, Module.finrank ℂ (D.columnFDRep j) : ℕ) : ℂ) := by rw [hsumeq]
  have key : ((∑ i, Module.finrank ℂ (V i) : ℕ) : ℂ)
      = (Fintype.card {g : G // g * g = 1} : ℂ) := by
    rw [hcast, Nat.cast_sum, ← hcor, Fintype.card_subtype]
  exact_mod_cast key

end Etingof
