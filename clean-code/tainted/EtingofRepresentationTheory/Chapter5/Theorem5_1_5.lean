import Mathlib
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration
import EtingofRepresentationTheory.Infrastructure.RegularCharacter
import EtingofRepresentationTheory.Chapter5.Definition5_1_4

/-!
# Theorem 5.1.5: Frobenius-Schur Theorem (Involution Count)

The number of involutions (elements g with g² = 1) in a finite group G equals:
  Σ_V dim(V) · FS(V)
where the sum is over all irreducible representations V, and FS(V) is the
Frobenius-Schur indicator.

## Mathlib correspondence

Uses character theory and the Frobenius-Schur indicator.
-/

open FDRep CategoryTheory

universe u

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- Frobenius-Schur indicator of an FDRep object, computed as
(1/|G|) Σ_{g∈G} χ_V(g²). -/
noncomputable def FDRep.frobeniusSchurIndicator
    [Invertible (Fintype.card G : k)]
    (V : FDRep k G) : k :=
  ⅟(Fintype.card G : k) • ∑ g : G, V.character (g * g)

/-- The sum `∑_i dim(V_i) · χ_{V_i}(h)` over all irreducible representations equals the
regular character: `|G|` if `h = 1` and `0` otherwise. -/
private lemma sum_dim_char_eq_regularChar
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    (D : IrrepDecomp k G)
    (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j)
    (h : G) :
    ∑ i, (Module.finrank k (V i) : k) * (V i).character h =
      if h = 1 then (Fintype.card G : k) else 0 := by
  split
  case isTrue heq =>
    subst heq
    simp only [FDRep.char_one]
    -- ∑ finrank(V i)² = ∑ D.d(σ i)² = ∑ D.d(j)² = |G|
    obtain ⟨σ, hσ⟩ := D.d_eq_finrank V hV hinj
    have hcast : ∀ i, (Module.finrank k (V i) : k) = (D.d (σ i) : k) := by
      intro i; congr 1; exact (hσ i).symm
    simp_rw [hcast]
    rw [show ∑ i, (D.d (σ i) : k) * (D.d (σ i) : k) =
      ∑ j, (D.d j : k) * (D.d j : k) from
      Finset.sum_equiv σ (fun _ => by simp) (fun _ _ => rfl)]
    rw [← D.sum_sq_eq_card]; push_cast; congr 1; ext i; ring
  case isFalse hne =>
    exact sum_dim_character_eq_zero D V hV hinj h hne

/-- The number of involutions in G equals Σ_i dim(V_i) · FS(V_i), where the sum ranges over
irreducible representations indexed by a Wedderburn-Artin decomposition.
(Etingof Theorem 5.1.5) -/
theorem Etingof.Theorem5_1_5
    [DecidableEq G] [IsAlgClosed k] [NeZero (Nat.card G : k)]
    [Invertible (Fintype.card G : k)]
    (D : IrrepDecomp k G)
    (V : Fin D.n → FDRep k G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) :
    (Finset.univ.filter (fun g : G => g * g = 1)).card =
    ∑ i : Fin D.n, Module.finrank k (V i) * (V i).frobeniusSchurIndicator := by
  simp only [FDRep.frobeniusSchurIndicator]
  -- Factor out ⅟|G| and rearrange sums
  simp_rw [mul_smul_comm]
  rw [← Finset.smul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Apply the regular character identity
  simp_rw [sum_dim_char_eq_regularChar D V hV hinj]
  -- Simplify: ⅟|G| • ∑_g (if g²=1 then |G| else 0) = #{involutions}
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul, smul_eq_mul]
  -- Goal: ↑card = ⅟↑|G| * ↑card * ↑|G|
  rw [invOf_eq_inv]
  have hne : (Fintype.card G : k) ≠ 0 := Invertible.ne_zero _
  field_simp [hne]

section ComplexIndicatorForm

-- `IrrepDecomp ℂ G` requires `G` in the same universe as `ℂ`, i.e. `Type 0`.
variable {G : Type} [Group G] [Fintype G]

/-- The Definition 5.1.4 Frobenius-Schur indicator (`Etingof.frobeniusSchurIndicator`,
on the underlying `Representation ℂ G ↥V`) agrees with the FDRep-level indicator
`FDRep.frobeniusSchurIndicator`. Both are `|G|⁻¹ ∑_g χ_V(g²)`. -/
lemma Etingof.frobeniusSchurIndicator_ρ_eq
    [DecidableEq G] [Invertible (Fintype.card G : ℂ)]
    (V : FDRep ℂ G) :
    Etingof.frobeniusSchurIndicator V.ρ = V.frobeniusSchurIndicator := by
  simp only [Etingof.frobeniusSchurIndicator, FDRep.frobeniusSchurIndicator,
    FDRep.character, invOf_eq_inv, smul_eq_mul]

/-- **Frobenius-Schur involution count (Definition 5.1.4 form, over ℂ).** The number of
involutions `#{g : G | g² = 1}` equals `∑_i FS(Vᵢ) · dim Vᵢ`, where `i` ranges over the
irreducible `ℂ[G]`-modules and `FS` is the Definition 5.1.4 Frobenius-Schur indicator
(`Etingof.frobeniusSchurIndicator` of the underlying representation `(Vᵢ).ρ`).

This restates `Etingof.Theorem5_1_5` with the bare-representation indicator, the form the
A₅ real-type endgame (`Etingof.A5_frobeniusSchur_all_pos`) consumes. -/
theorem Etingof.frobeniusSchur_involution_count
    [DecidableEq G] [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (D : IrrepDecomp ℂ G)
    (V : Fin D.n → FDRep ℂ G)
    (hV : ∀ i, Simple (V i))
    (hinj : ∀ i j, Nonempty ((V i) ≅ (V j)) → i = j) :
    ((Finset.univ.filter (fun g : G => g * g = 1)).card : ℂ) =
      ∑ i : Fin D.n,
        Etingof.frobeniusSchurIndicator (V i).ρ * (Module.finrank ℂ (V i) : ℂ) := by
  rw [Etingof.Theorem5_1_5 D V hV hinj]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Etingof.frobeniusSchurIndicator_ρ_eq, mul_comm]

end ComplexIndicatorForm
