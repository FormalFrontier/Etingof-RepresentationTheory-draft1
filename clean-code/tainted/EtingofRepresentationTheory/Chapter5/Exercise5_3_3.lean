import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurRealType
import EtingofRepresentationTheory.Chapter5.Theorem5_3_1
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3

/-!
# Exercise 5.3.3: nontrivial irreducibles of an odd-order group are of complex type

**Exercise 5.3.3.** Strengthen the result of Exercise 5.1.7: show that all nontrivial
irreducible representations of a group of odd order are of complex type. (Use that any
representation of quaternionic type is even-dimensional.)

## Formalization

We work with the project's type classification (`Etingof.IsComplexType`, Definition 5.1.1):
a complex representation `ρ : Representation ℂ G V` is of *complex type* if it is **not**
isomorphic (equivariantly) to its dual `ρ.dual`. Irreducibility is
`IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule`, and "nontrivial" is spelled `∃ g, ρ g ≠ 1`
(the action is not the identity on all of `G`).

## Proof structure

The main theorem `isComplexType_of_odd_order_of_nontrivial_irreducible` is assembled, in a
top-down fashion, from three faithful sub-lemmas that isolate the mathematical
content. Being of complex type means not self-dual, so we assume a `G`-equivariant
isomorphism `V ≃ V*` and derive a contradiction:

1. `isRealType_or_isQuaternionicType_of_selfDual`, **Schur dichotomy.** A self-dual
   irreducible representation carries a `G`-invariant nondegenerate bilinear form that is
   unique up to scalar (Schur's lemma: `Hom_G(V, V*) ≅ Hom_G(V, V) ≅ ℂ`). Its symmetric and
   skew-symmetric parts are therefore proportional, forcing the form to be either symmetric
   (real type) or skew-symmetric (quaternionic type).

2. `not_isRealType_of_odd_order_of_nontrivial_irreducible`: for `|G|` odd, the only real-type
   irreducible is the trivial one. (Frobenius–Schur / Brauer permutation lemma: the number of
   self-dual irreducibles equals the number of real conjugacy classes `C = C⁻¹`, and in an
   odd-order group the only such class is `{1}`, since a fixed-point-free involution `x ↦ x⁻¹` on a
   nontrivial real class would force it to have even, hence non-dividing, cardinality.)

3. `not_isQuaternionicType_of_odd_order_of_irreducible`: for `|G|` odd there are no
   quaternionic irreducibles. A quaternionic representation is even-dimensional (the book's
   hint: a nondegenerate skew-symmetric form exists only on even-dimensional spaces), while the
   dimension of an irreducible divides `|G|`, which is odd.

Sub-lemma 3
(`not_isQuaternionicType_of_odd_order_of_irreducible`) is proved by combining the even
dimension of quaternionic type (`Etingof.even_finrank_of_isQuaternionicType`) with "the
dimension of an irreducible divides `|G|`" (`Etingof.Theorem5_3_1`). The Frobenius–Schur
character-sum identity `sum_char_sq_eq_card_of_isRealType` for sub-lemma 2 is obtained by clearing
the `|G|⁻¹` factor in the reverse indicator identity
`Etingof.frobeniusSchurIndicator_eq_one_of_isRealType`.
-/

namespace Etingof

section Exercise533

variable {G : Type*} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-! ### The squaring bijection on an odd-order group

In a finite group of odd order the map `g ↦ g²` is a bijection: with `|G| = 2m - 1`
odd, `(g²)^m = g^(2m) = g^(|G|+1) = g` (using `g^|G| = 1`), so `g ↦ g^((|G|+1)/2)` is a
two-sided inverse. This lets us re-index a sum over `g²` as a sum over `g`. -/

/-- In a finite group of odd order, `g ↦ g²` is a bijection, with inverse
`g ↦ g^((|G|+1)/2)`. -/
def sqEquivOfOdd (hodd : Odd (Fintype.card G)) : G ≃ G where
  toFun g := g ^ 2
  invFun g := g ^ ((Fintype.card G + 1) / 2)
  left_inv g := by
    have hdvd : 2 ∣ Fintype.card G + 1 := hodd.add_one.two_dvd
    change (g ^ 2) ^ ((Fintype.card G + 1) / 2) = g
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, pow_succ, pow_card_eq_one, one_mul]
  right_inv g := by
    have hdvd : 2 ∣ Fintype.card G + 1 := hodd.add_one.two_dvd
    change (g ^ ((Fintype.card G + 1) / 2)) ^ 2 = g
    rw [← pow_mul, Nat.div_mul_cancel hdvd, pow_succ, pow_card_eq_one, one_mul]

@[simp] theorem sqEquivOfOdd_apply (hodd : Odd (Fintype.card G)) (g : G) :
    sqEquivOfOdd hodd g = g ^ 2 := rfl

/-- Re-indexing the character sum by the squaring bijection: for `|G|` odd,
`∑ g, χ(g²) = ∑ g, χ(g)`. -/
theorem sum_char_sq_eq_sum_char (hodd : Odd (Fintype.card G)) (ρ : Representation ℂ G V) :
    ∑ g : G, ρ.character (g ^ 2) = ∑ g : G, ρ.character g :=
  Equiv.sum_comp (sqEquivOfOdd hodd) ρ.character

/-! ### Vanishing of the invariants of a nontrivial irreducible -/

/-- A `ℂ`-submodule `P` of `ρ.asModule` stable under every `ρ g` packages (with the same
underlying set) as a `ℂ[G]`-submodule. This is a local copy of the standard construction;
closure under the whole group algebra follows from closure under each `ρ g` and the scalars
by linearity. -/
private def stableSubmodule (ρ : Representation ℂ G V) (P : Submodule ℂ ρ.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P) :
    Submodule (MonoidAlgebra ℂ G) ρ.asModule where
  carrier := P
  add_mem' hx hy := P.add_mem hx hy
  zero_mem' := P.zero_mem
  smul_mem' r x hx := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r₁ r₂ h₁ h₂ => rw [add_smul]; exact P.add_mem h₁ h₂
    | single g a =>
        have hsingle : (MonoidAlgebra.single g a : MonoidAlgebra ℂ G) =
            a • MonoidAlgebra.single g (1 : ℂ) := by
          rw [MonoidAlgebra.smul_single', mul_one]
        rw [hsingle, smul_assoc]
        apply P.smul_mem
        rw [Representation.single_smul, one_smul]
        exact hP g x hx

private theorem mem_stableSubmodule (ρ : Representation ℂ G V) (P : Submodule ℂ ρ.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P) (x : ρ.asModule) :
    x ∈ stableSubmodule ρ P hP ↔ x ∈ P :=
  Iff.rfl

/-- A nontrivial irreducible representation has no nonzero invariant vectors: the invariants
form a subrepresentation, which by simplicity is `⊥` or `⊤`; if `⊤` then every `ρ g` is the
identity, contradicting nontriviality. -/
theorem invariants_eq_bot_of_nontrivial_irreducible (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) (hnontriv : ∃ g, ρ g ≠ 1) :
    Representation.invariants ρ = ⊥ := by
  have hP : ∀ (g : G), ∀ x ∈ Representation.invariants ρ,
      ρ g (ρ.asModuleEquiv x) ∈ Representation.invariants ρ := by
    intro g x hx
    have hxx : ρ g (ρ.asModuleEquiv x) = x :=
      (Representation.mem_invariants ρ x).mp hx g
    rw [hxx]; exact hx
  rcases hirr.eq_bot_or_eq_top (stableSubmodule ρ (Representation.invariants ρ) hP) with h | h
  · rw [Submodule.eq_bot_iff] at h ⊢
    intro x hx
    exact h x ((mem_stableSubmodule ρ _ hP x).mpr hx)
  · exfalso
    obtain ⟨g, hg⟩ := hnontriv
    apply hg
    ext v
    have hv : v ∈ Representation.invariants ρ :=
      (mem_stableSubmodule ρ _ hP v).mp (h ▸ Submodule.mem_top)
    rw [Module.End.one_apply]
    exact (Representation.mem_invariants ρ v).mp hv g

/-- For a nontrivial irreducible representation of a finite group of odd order,
`∑ g, χ(g²) = 0`: the squaring bijection turns this into `∑ g, χ(g)`, which equals
`|G|·dim(invariants) = 0` because the invariants vanish. -/
theorem sum_char_sq_eq_zero (hodd : Odd (Fintype.card G)) (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) (hnontriv : ∃ g, ρ g ≠ 1) :
    ∑ g : G, ρ.character (g ^ 2) = 0 := by
  rw [sum_char_sq_eq_sum_char hodd ρ]
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have hkey := Representation.card_inv_mul_sum_char_eq_finrank ρ
  rw [invariants_eq_bot_of_nontrivial_irreducible ρ hirr hnontriv, finrank_bot,
    Nat.cast_zero] at hkey
  rcases mul_eq_zero.mp hkey with h | h
  · exact absurd (inv_eq_zero.mp h) hcard
  · exact h

/-! ### Frobenius–Schur character-sum identity

For a self-dual (in particular real-type) irreducible representation, the Frobenius–Schur
indicator `(1/|G|)·∑ χ(g²)` equals `+1`, i.e. `∑ χ(g²) = |G|`. This is the substantive
piece that is not in Mathlib; it is supplied by the reverse indicator identity
`Etingof.frobeniusSchurIndicator_eq_one_of_isRealType` (in `FrobeniusSchurRealType.lean`),
whose proof carries out the symmetric/exterior square analysis (the swap operator on
`(V ⊗ V)^G`, one-dimensional by Schur for a self-dual irreducible, acting by `+1` on the
symmetric invariant tensor supplied by the real-type form). Here we only clear the `|G|⁻¹`
factor to convert the indicator value `1` into the character-sum identity `∑ χ(g²) = |G|`. -/

/-- **Frobenius–Schur character-sum identity.** For a real-type irreducible representation of a finite
group, `∑ g, χ(g²) = |G|`. Unfolding `Etingof.frobeniusSchurIndicator ρ = |G|⁻¹·∑ χ(g²)`,
the value `1` (from `frobeniusSchurIndicator_eq_one_of_isRealType`) clears to `∑ χ(g²) = |G|`. -/
theorem sum_char_sq_eq_card_of_isRealType (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsRealType ρ) :
    ∑ g : G, ρ.character (g ^ 2) = (Fintype.card G : ℂ) := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hFS : Etingof.frobeniusSchurIndicator ρ = 1 :=
    Etingof.frobeniusSchurIndicator_eq_one_of_isRealType ρ hirr h
  rw [Etingof.frobeniusSchurIndicator, inv_mul_eq_one₀ hcard] at hFS
  -- `hFS : (Fintype.card G : ℂ) = ∑ g, trace (ρ (g * g))`; the summands match `χ (g ^ 2)`.
  rw [hFS]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.character, pow_two]

/-- **Schur dichotomy.** A self-dual irreducible representation is of real or quaternionic
type. The space of `G`-invariant bilinear forms on an irreducible `V` is at most
one-dimensional (Schur's lemma), so an invariant nondegenerate form and its transpose are
proportional with proportionality constant `±1`; the `+1` case gives a symmetric form (real
type), the `-1` case a skew-symmetric form (quaternionic type).

The equivariant isomorphism `e : V ≃ V*` supplied by self-duality makes the character
self-dual: `χ_ρ(g⁻¹) = χ_{ρ*}(g) = χ_ρ(g)` (the middle step is `char_dual`, the last is
conjugation-invariance of the trace, `ρ.dual g = e.conj (ρ g)`). We then invoke the
character-level dichotomy `Etingof.isRealType_or_isQuaternionicType_of_self_dual`, which
symmetrises/antisymmetrises a nonzero invariant form (nonzero by `⟨χ, χ⟩ = 1`) and uses
simplicity for nondegeneracy. -/
theorem isRealType_or_isQuaternionicType_of_selfDual
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∃ e : V ≃ₗ[ℂ] Module.Dual ℂ V, ∀ g v, e (ρ g v) = ρ.dual g (e v)) :
    Etingof.IsRealType ρ ∨ Etingof.IsQuaternionicType ρ := by
  classical
  obtain ⟨e, he⟩ := hsd
  -- The equivariant iso `e : V ≃ V*` conjugates `ρ g` to `ρ.dual g`, so the character is
  -- self-dual: `χ(g⁻¹) = χ_{ρ*}(g) = χ(g)`.
  have hchar : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g := by
    intro g
    have hconj : ρ.dual g = e.conj (ρ g) := by
      ext w
      rw [LinearEquiv.conj_apply_apply, he g (e.symm w), LinearEquiv.apply_symm_apply]
    calc Representation.character ρ g⁻¹
        = Representation.character ρ.dual g := (ρ.char_dual g).symm
      _ = LinearMap.trace ℂ (Module.Dual ℂ V) (e.conj (ρ g)) := by rw [Representation.character,
            hconj]
      _ = LinearMap.trace ℂ V (ρ g) := LinearMap.trace_conj' (ρ g) e
      _ = Representation.character ρ g := rfl
  exact isRealType_or_isQuaternionicType_of_self_dual ρ hirr hchar

/-- Odd-order groups have no nontrivial real-type irreducible. Combining the vanishing
`∑ χ(g²) = 0` (squaring bijection + no invariants) with the Frobenius–Schur value
`∑ χ(g²) = |G| ≠ 0` for real type gives a contradiction. -/
theorem not_isRealType_of_odd_order_of_nontrivial_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    ¬ Etingof.IsRealType ρ := by
  intro hreal
  have h0 : ∑ g : G, ρ.character (g ^ 2) = 0 :=
    sum_char_sq_eq_zero hodd ρ hirr hnontriv
  have hc : ∑ g : G, ρ.character (g ^ 2) = (Fintype.card G : ℂ) :=
    sum_char_sq_eq_card_of_isRealType ρ hirr hreal
  rw [h0] at hc
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hc.symm

/-- For a finite group of **odd** order, no irreducible representation is of quaternionic
type. A quaternionic representation is even-dimensional
(`Etingof.even_finrank_of_isQuaternionicType`: a nondegenerate skew-symmetric form exists only
in even dimension), whereas the dimension of an irreducible divides `|G|`
(`Etingof.Theorem5_3_1`), which is odd. An even number dividing an odd number is impossible. -/
theorem not_isQuaternionicType_of_odd_order_of_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    ¬ Etingof.IsQuaternionicType ρ := by
  classical
  intro hquat
  -- Quaternionic type supplies a nondegenerate skew-symmetric form, so `finrank ℂ V` is even.
  have heven : Even (Module.finrank ℂ V) :=
    Etingof.even_finrank_of_isQuaternionicType ρ hquat
  -- Irreducibility makes `FDRep.of ρ` a simple object, whose dimension divides `|G|`.
  haveI : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule := hirr
  haveI := Etingof.simple_fdRepOf_of_isSimpleModule ρ
  -- `Module.finrank ℂ (FDRep.of ρ)` is definitionally `Module.finrank ℂ V`.
  have hdvd : Module.finrank ℂ V ∣ Fintype.card G := Etingof.Theorem5_3_1 G (FDRep.of ρ)
  -- `Even (finrank)` and `finrank ∣ (odd |G|)` give `2 ∣ |G|`, contradicting oddness.
  obtain ⟨k, hk⟩ := heven
  obtain ⟨m, hm⟩ := hdvd
  rw [Nat.odd_iff] at hodd
  have hcard : Fintype.card G = 2 * (k * m) := by rw [hm, hk]; ring
  omega

/-- Exercise 5.3.3. Every nontrivial irreducible representation of a finite group of odd
order is of complex type (`V ≇ V*`).

Being of complex type means not being self-dual, so we assume a `G`-equivariant isomorphism
`V ≃ V*` and derive a contradiction: by the Schur dichotomy such a self-dual irreducible is of
real or quaternionic type, but for odd order neither is possible for a nontrivial
irreducible. -/
theorem isComplexType_of_odd_order_of_nontrivial_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    Etingof.IsComplexType ρ := by
  -- `IsComplexType ρ` unfolds to `¬ (ρ is self-dual)`; assume self-duality and derive `False`.
  intro hsd
  rcases isRealType_or_isQuaternionicType_of_selfDual ρ hirr hsd with hreal | hquat
  · exact not_isRealType_of_odd_order_of_nontrivial_irreducible hodd ρ hirr hnontriv hreal
  · exact not_isQuaternionicType_of_odd_order_of_irreducible hodd ρ hirr hquat

end Exercise533

end Etingof
