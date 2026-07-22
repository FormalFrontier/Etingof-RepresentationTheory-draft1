import EtingofRepresentationTheory.Chapter9.Introduction_9_7
import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import EtingofRepresentationTheory.Chapter9.Definition9_7_1
import Mathlib.CategoryTheory.Conj
import Mathlib.Algebra.Ring.Equiv

universe u v

/-!
# §9.7 capstone: the `B_𝐧` enumerate the Morita class of `𝒞`

Etingof §9.7 closes the discussion of projective generators with the claim that ties
the family `B_𝐧 = End(P_𝐧)ᵒᵖ` to Morita equivalence:

> Defining `B_𝐧 = B_𝐧(𝒞) := End(P_𝐧)ᵒᵖ`, we see that the algebras `B_𝐧` are all the
> finite dimensional algebras whose category of finite dimensional modules is
> equivalent to `𝒞`.

and, in the Discussion after Definition 9.7.1, its global restatement:

> Thus, Morita equivalence classes of finite dimensional algebras are the collections
> of the form `{B_𝐧(𝒞), 𝐧 ∈ ℕᵐ}`.

This file formalizes both claims, building on three already-proven pieces:

* `Etingof.Theorem_9_6_4_corollary_of_isNoetherian` — for any progenerator `P` of a finite
  abelian category `𝒞` with `(End P)ᵐᵒᵖ` Noetherian, `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ`. This is
  the ring-level Morita identification: the endomorphism algebra of a progenerator realizes
  `𝒞` as its module category. (The over-a-field headline is `Etingof.Theorem_9_6_4`.)
* `Etingof.progenerator_iff_multBiproduct` — the §9.7 classification: an object `Q` is
  a progenerator **iff** `Q ≅ P_𝐧 := ⊕ᵢ nᵢ Pᵢ` for some multiplicities `nᵢ ≥ 1`.
* `Etingof.isProgenerator_multBiproduct` — each `P_𝐧` with all `nᵢ ≥ 1` is a
  progenerator.

## What is proved here

The project's `IsFiniteAbelianCategory` is a *ring*-level abstraction (an abelian
category with enough projectives and finitely many simples; it carries no `k`-linear
structure), so `B_𝐧 = (End P_𝐧)ᵐᵒᵖ` is a ring and the comparisons below are ring
isomorphisms `≃+*` rather than `k`-algebra isomorphisms.

* `Etingof.Bn` — the algebra `B_𝐧(𝒞) = (End P_𝐧)ᵐᵒᵖ`.
* `Etingof.nonempty_equivalence_fgModuleCat_Bn` — **each `B_𝐧` realizes `𝒞`**:
  `𝒞 ≌ FGModuleCat (B_𝐧)` (the `⊇` of the book's claim).
* `Etingof.ringEquiv_endOp_iff_isBn` — **the capstone biconditional**: a ring `A` is
  (isomorphic to) the endomorphism algebra `(End Q)ᵐᵒᵖ` of *some* progenerator `Q` of
  `𝒞` **iff** `A ≃+* B_𝐧` for some `𝐧` with all `nᵢ ≥ 1`. Via Theorem 9.6.4 the
  left-hand side is exactly "`A`'s module category is `𝒞`", so this is precisely
  Etingof's "the `B_𝐧` are all the algebras whose module category is `𝒞`".
* `Etingof.nonempty_fgModuleCat_equivalence_of_isBn` — **the Discussion restatement**:
  all the `B_𝐧` lie in a single Morita class (their module categories are mutually
  equivalent, both being `𝒞`).
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : C}

/-- Conjugation by an isomorphism `e : X ≅ Y` as a **ring** isomorphism of endomorphism
rings, `End X ≃+* End Y`, `f ↦ e.inv ≫ f ≫ e.hom`. This upgrades Mathlib's multiplicative
`Iso.conj` with additivity, which holds because composition is bilinear in a preadditive
category. -/
def conjRingEquiv (e : X ≅ Y) : End X ≃+* End Y :=
  { e.conj with
    map_add' := fun f g =>
      show e.inv ≫ (f + g) ≫ e.hom = e.inv ≫ f ≫ e.hom + e.inv ≫ g ≫ e.hom by
        rw [Preadditive.add_comp, Preadditive.comp_add] }

@[simp]
theorem conjRingEquiv_apply (e : X ≅ Y) (f : End X) :
    e.conjRingEquiv f = e.inv ≫ f ≫ e.hom := rfl

end CategoryTheory.Iso

namespace Etingof

variable {C : Type u} [Category.{v} C]

/-- **`B_𝐧(𝒞) = End(P_𝐧)ᵒᵖ`** (Etingof §9.7): the (opposite of the) endomorphism ring of
the multiplicity biproduct `P_𝐧 = ⊕ᵢ nᵢ Pᵢ`. The opposite matches the convention of
Theorem 9.6.4, under which `𝒞 ≌ FGModuleCat (End P_𝐧)ᵐᵒᵖ`. -/
noncomputable abbrev Bn [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ) : Type v :=
  (End (multBiproduct P n))ᵐᵒᵖ

variable [IsFiniteAbelianCategory C] [HasFiniteBiproducts C]
  {ι : Type v} [Fintype ι] (P : ι → C)

/-- **Each `B_𝐧` realizes `𝒞`** (the `⊇` direction of Etingof's §9.7 claim).

If every multiplicity `nᵢ ≥ 1`, then `P_𝐧` is a progenerator, so by Theorem 9.6.4 the
category `𝒞` is equivalent to the category of finitely generated `B_𝐧`-modules. -/
theorem nonempty_equivalence_fgModuleCat_Bn
    (hproj : ∀ i, Projective (P i)) [IsProgenerator (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) [IsNoetherianRing (Bn P n)] :
    Nonempty (C ≌ FGModuleCat.{v} (Bn P n)) := by
  haveI : ∀ i, Projective (P i) := hproj
  haveI : IsProgenerator (multBiproduct P n) := isProgenerator_multBiproduct P n hn
  exact Theorem_9_6_4_corollary_of_isNoetherian C (multBiproduct P n)

/-- **§9.7 capstone biconditional.** Let `P : ι → 𝒞` be the indecomposable projectives of
the finite abelian category `𝒞` (each indecomposable, pairwise non-isomorphic, exhausting
the indecomposable projectives, with `⨁ P` a progenerator). Then a ring `A` is isomorphic
to the endomorphism algebra `(End Q)ᵐᵒᵖ` of *some* progenerator `Q` of `𝒞` **iff** `A` is
isomorphic to some `B_𝐧` with all multiplicities `nᵢ ≥ 1`.

By Theorem 9.6.4 the left-hand condition is exactly "`A`'s category of finitely generated
modules is equivalent to `𝒞`". So this is Etingof's statement that the `B_𝐧` are precisely
the algebras whose module category is `𝒞`. -/
theorem ringEquiv_endOp_iff_isBn
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [IsProgenerator (⨁ P)] (A : Type v) [Ring A] :
    (∃ Q : C, IsProgenerator Q ∧ Nonempty (A ≃+* (End Q)ᵐᵒᵖ)) ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (A ≃+* Bn P n) := by
  haveI : ∀ i, Projective (P i) := hproj
  constructor
  · rintro ⟨Q, hQ, ⟨φ⟩⟩
    obtain ⟨n, hn, ⟨e⟩⟩ :=
      (progenerator_iff_multBiproduct P hproj hindec hdistinct hcomplete Q).mp hQ
    exact ⟨n, hn, ⟨φ.trans (RingEquiv.op e.conjRingEquiv)⟩⟩
  · rintro ⟨n, hn, ⟨φ⟩⟩
    haveI : IsProgenerator (multBiproduct P n) := isProgenerator_multBiproduct P n hn
    exact ⟨multBiproduct P n, inferInstance, ⟨φ⟩⟩

/-- **Discussion after Definition 9.7.1: the `B_𝐧` form a single Morita class.**

Any two members `B_𝐧` and `B_𝐧'` of the family have equivalent module categories (both
are equivalent to `𝒞`), so they are Morita equivalent. This is the precise content of
"Morita equivalence classes of finite dimensional algebras are the collections
`{B_𝐧(𝒞), 𝐧 ∈ ℕᵐ}`". -/
theorem nonempty_fgModuleCat_equivalence_of_isBn
    (hproj : ∀ i, Projective (P i)) [IsProgenerator (⨁ P)]
    (n n' : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (hn' : ∀ i, 1 ≤ n' i)
    [IsNoetherianRing (Bn P n)] [IsNoetherianRing (Bn P n')] :
    Nonempty (FGModuleCat.{v} (Bn P n) ≌ FGModuleCat.{v} (Bn P n')) := by
  obtain ⟨e⟩ := nonempty_equivalence_fgModuleCat_Bn P hproj n hn
  obtain ⟨e'⟩ := nonempty_equivalence_fgModuleCat_Bn P hproj n' hn'
  exact ⟨e.symm.trans e'⟩

end Etingof
