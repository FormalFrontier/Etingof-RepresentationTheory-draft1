import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Jacobson.Semiprimary

universe u v

/-!
# Definition 3.5.1: Radical of a Finite Dimensional Algebra

The **radical** of a finite dimensional algebra A is the set of all elements of A which act
by 0 in all irreducible representations of A. It is denoted Rad(A).

## Mathlib correspondence

The Jacobson radical is `Ideal.jacobson ⊥` (intersection of all maximal left ideals).
The characterization below shows that this is exactly the radical defined by Etingof;
in fact, the identification holds for every ring.
-/

/-- The radical of a finite dimensional algebra, in the sense of Etingof Definition 3.5.1.
This is the Jacobson radical `Ideal.jacobson ⊥` in Mathlib. -/
abbrev Etingof.Radical (A : Type*) [Ring A] : Ideal A :=
  Ideal.jacobson ⊥

/-- Every element of `Etingof.Radical A` acts by zero on every irreducible
`A`-representation, without any universe restriction on the representation. -/
theorem Etingof.radical_smul_eq_zero {A : Type u} [Ring A] {a : A}
    (ha : a ∈ Etingof.Radical A) (V : Type v) [AddCommGroup V] [Module A V]
    [IsSimpleModule A V] (v : V) : a • v = 0 := by
  have ha' : a ∈ Ring.jacobson A := by
    rwa [← Ideal.jacobson_bot]
  exact Module.mem_annihilator.mp
    (IsSemisimpleModule.jacobson_le_annihilator (R := A) (M := V) ha') v

/-- The Jacobson-radical presentation of `Etingof.Radical` agrees with the book's
definition: its elements are exactly those that act by zero in every irreducible
representation.  It is enough to quantify over modules in the universe of `A`, since
the reverse implication is witnessed by quotients by maximal left ideals. -/
theorem Etingof.mem_radical_iff (A : Type u) [Ring A] (a : A) :
    a ∈ Etingof.Radical A ↔
      ∀ (V : Type u) [AddCommGroup V] [Module A V] [IsSimpleModule A V] (v : V),
        a • v = 0 := by
  constructor
  · intro ha V _ _ _ v
    exact Etingof.radical_smul_eq_zero ha V v
  · intro ha
    rw [Etingof.Radical, Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    refine Ideal.mem_sInf.mpr fun I hI ↦ ?_
    letI : IsSimpleModule A (A ⧸ (I : Submodule A A)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hI)
    have hz := ha (A ⧸ (I : Submodule A A))
      (Submodule.Quotient.mk (p := (I : Submodule A A)) (1 : A))
    rw [← Submodule.Quotient.mk_smul] at hz
    simpa [Submodule.Quotient.mk_eq_zero] using hz
