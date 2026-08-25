import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.Definition5_1_4
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurRealType
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurTraceIdentity

/-!
# Definition 5.1.4: the Frobenius-Schur type trichotomy

For a *simple* finite-dimensional complex representation `ρ` of a finite group, the
Frobenius-Schur indicator `FS(ρ) = |G|⁻¹ ∑_g χ(g²)` (Definition 5.1.4) determines and is
determined by the complex / real / quaternionic type of `ρ` (Definition 5.1.1):

* `IsComplexType ρ ↔ FS(ρ) = 0`;
* `IsRealType ρ ↔ FS(ρ) = 1`;
* `IsQuaternionicType ρ ↔ FS(ρ) = -1`.

The three types are **exhaustive** (every simple `ρ` is of exactly one type) and
**pairwise exclusive**, and in particular `FS(ρ) ∈ {0, 1, -1}`.

## Proof ingredients

Everything is assembled from previously established results:

* real ⟺ `FS = 1`: `isRealType_of_frobeniusSchurIndicator_eq_one` /
  `frobeniusSchurIndicator_eq_one_of_isRealType` (Frobenius-Schur real-type file);
* self-dual character ⟹ `FS = ±1`: `frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple`;
* non-self-dual character ⟹ `FS = 0`: `frobeniusSchurIndicator_eq_zero_of_not_self_dual_simple`;
* self-dual character ⟹ real or quaternionic: `isRealType_or_isQuaternionicType_of_self_dual`;
* real / quaternionic ⟹ not complex: `not_isComplexType_of_isRealType` /
  `not_isComplexType_of_isQuaternionicType`.

Two bridging facts are proved here: a non-complex simple representation has self-dual
character (`selfDualChar_of_not_isComplexType`), and no simple representation is
simultaneously of real and quaternionic type (`not_isRealType_and_isQuaternionicType`),
because the space of invariant bilinear forms is one-dimensional and cannot contain both a
nonzero symmetric and a nonzero skew-symmetric form.
-/

open scoped MonoidAlgebra

namespace Etingof

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- Over `ℂ`, a finite group has invertible/nonzero order; supply the instances required by
the numerical Frobenius-Schur results. -/
private lemma cardCastNeZero : (Fintype.card G : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_pos.ne'

/-- **Bridge: not complex ⟹ self-dual character.** If a representation is not of complex
type, i.e. it admits a `G`-equivariant isomorphism `V ≅ V*`, then its character is self-dual
(`χ(g⁻¹) = χ(g)`): the isomorphism conjugates `ρ g` to `ρ.dual g`, and trace is a conjugation
invariant, while `χ_{V*}(g) = χ(g⁻¹)`. -/
theorem selfDualChar_of_not_isComplexType (ρ : Representation ℂ G V)
    (h : ¬ Etingof.IsComplexType ρ) :
    ∀ g, ρ.character g⁻¹ = ρ.character g := by
  have hex : ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v) := by
    by_contra hc; exact h hc
  obtain ⟨e, he⟩ := hex
  intro g
  have hconj : ρ.dual g = e.conj (ρ g) := by
    ext w
    rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
  calc ρ.character g⁻¹
      = ρ.dual.character g := (ρ.char_dual g).symm
    _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by
          rw [Representation.character, hconj]
    _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
    _ = ρ.character g := rfl

/-- **Real and quaternionic type are exclusive.** For a simple representation the space of
`G`-invariant bilinear forms is one-dimensional (Schur, self-dual), so it cannot contain both
a nonzero symmetric form (real type) and a nonzero skew-symmetric form (quaternionic type):
these would be proportional, forcing a nonzero form to be both symmetric and skew, hence
zero. -/
theorem not_isRealType_and_isQuaternionicType (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    ¬ (Etingof.IsRealType ρ ∧ Etingof.IsQuaternionicType ρ) := by
  classical
  rintro ⟨⟨Bs, hBs_sym, hBs_nd, hBs_inv⟩, ⟨Bq, hBq_skew, hBq_nd, hBq_inv⟩⟩
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  haveI : Nonempty G := ⟨1⟩
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by simp only [ne_eq, Nat.cast_eq_zero]; exact Nat.card_pos.ne')
  haveI hNT : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  -- Self-dual character from the nondegenerate invariant symmetric form `Bs`.
  have hchar_sd : ∀ g, ρ.character g⁻¹ = ρ.character g := by
    obtain ⟨e, he⟩ :=
      Etingof.exists_equivariant_dual_equiv_of_invariant_nondegenerate ρ Bs hBs_nd hBs_inv
    intro g
    have hconj : ρ.dual g = e.conj (ρ g) := by
      ext w; rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
    calc ρ.character g⁻¹
        = ρ.dual.character g := (ρ.char_dual g).symm
      _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by
            rw [Representation.character, hconj]
      _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
      _ = ρ.character g := rfl
  -- The space of invariant bilinear forms is one-dimensional.
  have hd1 : Module.finrank ℂ ((Representation.linHom ρ ρ.dual).invariants) = 1 := by
    have hkey := Representation.card_inv_mul_sum_char_eq_finrank (Representation.linHom ρ ρ.dual)
    have hortho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
    have hchar : ∀ g, (Representation.linHom ρ ρ.dual).character g
        = ρ.character g * ρ.character g⁻¹ := fun g => by
      rw [Representation.char_linHom, Representation.char_dual, hchar_sd g]
    rw [Finset.sum_congr rfl (fun g _ => hchar g), hortho] at hkey
    exact_mod_cast hkey.symm
  -- `Bs` and `Bq`, read as maps `V →ₗ Module.Dual ℂ V`, are invariant.
  have hmem : ∀ B : V →ₗ[ℂ] Module.Dual ℂ V, (∀ g v w, B (ρ g v) (ρ g w) = B v w) →
      B ∈ (Representation.linHom ρ ρ.dual).invariants := by
    intro B hB
    rw [Representation.mem_invariants]
    intro g
    ext v w
    rw [Representation.linHom_apply]
    simp only [LinearMap.comp_apply, Representation.dual_apply, Module.Dual.transpose_apply]
    exact hB g⁻¹ v w
  have memS : (Bs : V →ₗ[ℂ] Module.Dual ℂ V) ∈ (Representation.linHom ρ ρ.dual).invariants :=
    hmem Bs hBs_inv
  have memQ : (Bq : V →ₗ[ℂ] Module.Dual ℂ V) ∈ (Representation.linHom ρ ρ.dual).invariants :=
    hmem Bq hBq_inv
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  have hBsne : (⟨Bs, memS⟩ : (Representation.linHom ρ ρ.dual).invariants) ≠ 0 := by
    intro h0
    have hBs0 : Bs = 0 := by simpa using congrArg Subtype.val h0
    exact hv0 (hBs_nd v0 (fun w => by simp [hBs0]))
  -- Proportionality: `Bq = c • Bs` for some scalar `c`.
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (⟨Bs, memS⟩ : (Representation.linHom ρ ρ.dual).invariants)
      hBsne).mp hd1 ⟨Bq, memQ⟩
  have hcoe : c • Bs = Bq := by simpa using congrArg Subtype.val hc
  -- A symmetric multiple that is also skew must vanish.
  have hBqzero : Bq = 0 := by
    ext v w
    have hxvw : Bq v w = c * Bs v w := by rw [← hcoe]; simp
    have hxwv : Bq w v = c * Bs v w := by rw [← hcoe]; simp [hBs_sym w v]
    have hz : Bq v w = 0 := by
      linear_combination (1 / 2 : ℂ) * hxvw - (1 / 2 : ℂ) * hxwv + (1 / 2 : ℂ) * hBq_skew v w
    simpa using hz
  exact hv0 (hBq_nd v0 (fun w => by simp [hBqzero]))

/-- The nonzero-order instances required by the numerical Frobenius-Schur results, always
available over `ℂ` for a finite group. -/
private noncomputable def invertibleCardCast : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero cardCastNeZero

private theorem neZeroNatCardCast : NeZero (Nat.card G : ℂ) :=
  ⟨by rw [Nat.card_eq_fintype_card]; exact cardCastNeZero⟩

/-- **Real type ⟺ indicator `1`.** (Etingof, Definition 5.1.4, real case.) -/
theorem isRealType_iff_frobeniusSchurIndicator_eq_one (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.IsRealType ρ ↔ Etingof.frobeniusSchurIndicator ρ = 1 :=
  ⟨Etingof.frobeniusSchurIndicator_eq_one_of_isRealType ρ hρ,
    Etingof.isRealType_of_frobeniusSchurIndicator_eq_one ρ hρ⟩

/-- **Quaternionic type ⟹ indicator `-1`.** A quaternionic simple representation is
self-dual, so `FS = ±1`; it cannot be `1` (that would make it real too, contradicting
`not_isRealType_and_isQuaternionicType`), hence `FS = -1`. -/
theorem frobeniusSchurIndicator_eq_neg_one_of_isQuaternionicType (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hq : Etingof.IsQuaternionicType ρ) :
    Etingof.frobeniusSchurIndicator ρ = -1 := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  have hsd := selfDualChar_of_not_isComplexType ρ (not_isComplexType_of_isQuaternionicType hq)
  rcases Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple ρ hρ hsd with h1 | hm1
  · exact absurd ⟨Etingof.isRealType_of_frobeniusSchurIndicator_eq_one ρ hρ h1, hq⟩
      (not_isRealType_and_isQuaternionicType ρ hρ)
  · exact hm1

/-- **Indicator `-1` ⟹ quaternionic type.** If `FS = -1` the character is self-dual (else
`FS = 0`), so `ρ` is real or quaternionic; real would give `FS = 1`, so `ρ` is
quaternionic. -/
theorem isQuaternionicType_of_frobeniusSchurIndicator_eq_neg_one (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.frobeniusSchurIndicator ρ = -1) :
    Etingof.IsQuaternionicType ρ := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  by_cases hsd : ∀ g, ρ.character g⁻¹ = ρ.character g
  · rcases Etingof.isRealType_or_isQuaternionicType_of_self_dual ρ hρ hsd with hr | hq
    · exact absurd (Etingof.frobeniusSchurIndicator_eq_one_of_isRealType ρ hρ hr)
        (by rw [h]; norm_num)
    · exact hq
  · exact absurd (Etingof.frobeniusSchurIndicator_eq_zero_of_not_self_dual_simple ρ hρ hsd)
      (by rw [h]; norm_num)

/-- **Quaternionic type ⟺ indicator `-1`.** (Etingof, Definition 5.1.4, quaternionic case.) -/
theorem isQuaternionicType_iff_frobeniusSchurIndicator_eq_neg_one (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.IsQuaternionicType ρ ↔ Etingof.frobeniusSchurIndicator ρ = -1 :=
  ⟨frobeniusSchurIndicator_eq_neg_one_of_isQuaternionicType ρ hρ,
    isQuaternionicType_of_frobeniusSchurIndicator_eq_neg_one ρ hρ⟩

/-- **The indicator takes the values `0`, `1`, `-1`.** A simple complex representation has
`FS(ρ) ∈ {0, 1, -1}`: `±1` when the character is self-dual, `0` otherwise. -/
theorem frobeniusSchurIndicator_eq_zero_or_one_or_neg_one (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.frobeniusSchurIndicator ρ = 0 ∨ Etingof.frobeniusSchurIndicator ρ = 1 ∨
      Etingof.frobeniusSchurIndicator ρ = -1 := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  by_cases hsd : ∀ g, ρ.character g⁻¹ = ρ.character g
  · rcases Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple ρ hρ hsd with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Etingof.frobeniusSchurIndicator_eq_zero_of_not_self_dual_simple ρ hρ hsd)

/-- The indicator belongs to the set `{0, 1, -1}`. -/
theorem frobeniusSchurIndicator_mem_insert (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.frobeniusSchurIndicator ρ ∈ ({0, 1, -1} : Set ℂ) := by
  rcases frobeniusSchurIndicator_eq_zero_or_one_or_neg_one ρ hρ with h | h | h <;>
    simp [h]

/-- **Complex type ⟺ indicator `0`.** (Etingof, Definition 5.1.4, complex case.) -/
theorem isComplexType_iff_frobeniusSchurIndicator_eq_zero (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.IsComplexType ρ ↔ Etingof.frobeniusSchurIndicator ρ = 0 := by
  haveI := invertibleCardCast (G := G)
  haveI := neZeroNatCardCast (G := G)
  constructor
  · intro hc
    have hnr : ¬ Etingof.IsRealType ρ := fun hr => not_isComplexType_of_isRealType hr hc
    have hnq : ¬ Etingof.IsQuaternionicType ρ := fun hq =>
      not_isComplexType_of_isQuaternionicType hq hc
    rcases frobeniusSchurIndicator_eq_zero_or_one_or_neg_one ρ hρ with h0 | h1 | hm1
    · exact h0
    · exact absurd (Etingof.isRealType_of_frobeniusSchurIndicator_eq_one ρ hρ h1) hnr
    · exact absurd (isQuaternionicType_of_frobeniusSchurIndicator_eq_neg_one ρ hρ hm1) hnq
  · intro h0
    by_contra hnc
    have hsd := selfDualChar_of_not_isComplexType ρ hnc
    rcases Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple ρ hρ hsd with h1 | hm1
    · rw [h0] at h1; norm_num at h1
    · rw [h0] at hm1; norm_num at hm1

/-- **Exhaustiveness of the trichotomy.** Every simple complex representation is of complex,
real, or quaternionic type. -/
theorem isComplexType_or_isRealType_or_isQuaternionicType (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    Etingof.IsComplexType ρ ∨ Etingof.IsRealType ρ ∨ Etingof.IsQuaternionicType ρ := by
  by_cases hsd : ∀ g, ρ.character g⁻¹ = ρ.character g
  · rcases Etingof.isRealType_or_isQuaternionicType_of_self_dual ρ hρ hsd with hr | hq
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hq)
  · refine Or.inl ?_
    by_contra hnc
    exact hsd (selfDualChar_of_not_isComplexType ρ hnc)

/-- Complex and real type are exclusive. -/
theorem not_isComplexType_and_isRealType (ρ : Representation ℂ G V) :
    ¬ (Etingof.IsComplexType ρ ∧ Etingof.IsRealType ρ) :=
  fun ⟨hc, hr⟩ => not_isComplexType_of_isRealType hr hc

/-- Complex and quaternionic type are exclusive. -/
theorem not_isComplexType_and_isQuaternionicType (ρ : Representation ℂ G V) :
    ¬ (Etingof.IsComplexType ρ ∧ Etingof.IsQuaternionicType ρ) :=
  fun ⟨hc, hq⟩ => not_isComplexType_of_isQuaternionicType hq hc

end Etingof
