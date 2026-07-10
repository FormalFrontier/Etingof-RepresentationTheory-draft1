import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1

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

The mathematical content: for `|G|` odd, a self-dual irreducible carries a nondegenerate
invariant bilinear form, hence is of real or quaternionic type; the Frobenius-Schur indicator
distinguishes these and, by an averaging/counting argument that uses that quaternionic type
forces even dimension while `|G|` odd forces odd-dimensional constituents, the only self-dual
irreducible is the trivial one. So every nontrivial irreducible is of complex type.

Statement pass: the proof is left as `sorry`.
-/

namespace Etingof

section Exercise533

variable {G : Type*} [Group G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

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
    show (g ^ 2) ^ ((Fintype.card G + 1) / 2) = g
    rw [← pow_mul, Nat.mul_div_cancel' hdvd, pow_succ, pow_card_eq_one, one_mul]
  right_inv g := by
    have hdvd : 2 ∣ Fintype.card G + 1 := hodd.add_one.two_dvd
    show (g ^ ((Fintype.card G + 1) / 2)) ^ 2 = g
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
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
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

/-! ### Frobenius–Schur crux (open)

For a self-dual (in particular real-type) irreducible representation, the Frobenius–Schur
indicator `(1/|G|)·∑ χ(g²)` equals `+1`, i.e. `∑ χ(g²) = |G|`. This is the substantive
piece that is not yet in Mathlib; see the sub-issue. It requires the symmetric/exterior
square decomposition of `V ⊗ V` (equivalently, the swap operator on `(V ⊗ V)^G`, which is
one-dimensional by Schur for a self-dual irreducible, and acts by `+1` on the symmetric
invariant tensor supplied by the real-type form). -/

/-- **Frobenius–Schur crux (open).** For a real-type irreducible representation of a finite
group, `∑ g, χ(g²) = |G|`. -/
theorem sum_char_sq_eq_card_of_isRealType (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (h : Etingof.IsRealType ρ) :
    ∑ g : G, ρ.character (g ^ 2) = (Fintype.card G : ℂ) := by
  sorry

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

/-- Exercise 5.3.3. Every nontrivial irreducible representation of a finite group of odd
order is of complex type (`V ≇ V*`). -/
theorem isComplexType_of_odd_order_of_nontrivial_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    Etingof.IsComplexType ρ := by
  sorry

end Exercise533

end Etingof
