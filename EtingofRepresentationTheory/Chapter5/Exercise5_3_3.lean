import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurRealType

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
top-down fashion, from three faithful sub-lemmas that isolate the genuine mathematical
content. Being of complex type means *not* self-dual, so we assume a `G`-equivariant
isomorphism `V ≃ V*` and derive a contradiction:

1. `isRealType_or_isQuaternionicType_of_selfDual` — **Schur dichotomy.** A self-dual
   *irreducible* representation carries a `G`-invariant nondegenerate bilinear form that is
   unique up to scalar (Schur's lemma: `Hom_G(V, V*) ≅ Hom_G(V, V) ≅ ℂ`). Its symmetric and
   skew-symmetric parts are therefore proportional, forcing the form to be either symmetric
   (real type) or skew-symmetric (quaternionic type).

2. `not_isRealType_of_odd_order_of_nontrivial_irreducible` — for `|G|` odd, the only real-type
   irreducible is the trivial one. (Frobenius–Schur / Brauer permutation lemma: the number of
   self-dual irreducibles equals the number of *real* conjugacy classes `C = C⁻¹`, and in an
   odd-order group the only such class is `{1}` — a fixed-point-free involution `x ↦ x⁻¹` on a
   nontrivial real class would force it to have even, hence non-dividing, cardinality.)

3. `not_isQuaternionicType_of_odd_order_of_irreducible` — for `|G|` odd there are no
   quaternionic irreducibles. A quaternionic representation is **even**-dimensional (the book's
   hint: a nondegenerate skew-symmetric form exists only on even-dimensional spaces), while the
   dimension of an irreducible divides `|G|`, which is odd.

The top-level assembly is complete and sorry-free; the three sub-lemmas carry the remaining
`sorry`s, each a self-contained statement requiring character-theoretic infrastructure
(Frobenius–Schur / Brauer, "dimension divides the order", "nondegenerate alternating ⇒ even
dimension") that is not yet available in Mathlib. See the tracking issues for #6215.
-/

namespace Etingof

section Exercise533

variable {G : Type*} [Group G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

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

/-- For a finite group of **odd** order, no nontrivial irreducible representation is of real
type: the only real-type irreducible is the trivial representation.

TODO (#6215): prove via the Frobenius–Schur / Brauer permutation lemma. The number of
self-dual irreducibles equals the number of real conjugacy classes (`C = C⁻¹`); in an
odd-order group the only real class is `{1}`, because `x ↦ x⁻¹` is a fixed-point-free
involution on any nontrivial real class (odd order ⇒ `x² = 1 ⇒ x = 1`), forcing that class to
have even cardinality, contradicting that it divides the odd `|G|`. -/
theorem not_isRealType_of_odd_order_of_nontrivial_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hnontriv : ∃ g, ρ g ≠ 1) :
    ¬ Etingof.IsRealType ρ := by
  sorry

/-- For a finite group of **odd** order, no irreducible representation is of quaternionic
type. A quaternionic representation is even-dimensional (a nondegenerate skew-symmetric form
exists only in even dimension), whereas the dimension of an irreducible divides `|G|`, which
is odd.

TODO (#6215): prove by combining "nondegenerate alternating form ⇒ even `finrank`" with
"`finrank` of an irreducible divides `Fintype.card G`". -/
theorem not_isQuaternionicType_of_odd_order_of_irreducible
    (hodd : Odd (Fintype.card G))
    (ρ : Representation ℂ G V)
    (hirr : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule) :
    ¬ Etingof.IsQuaternionicType ρ := by
  sorry

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
