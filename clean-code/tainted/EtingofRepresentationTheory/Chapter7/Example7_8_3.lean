import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Example 7.8.3: Split Exact Sequences

The sequence 0 → X → X ⊕ Z → Z → 0 with the obvious morphisms is a short exact
sequence. Such a sequence is called **split**. It corresponds to the trivial
extension of Z by X.

## Mathlib correspondence

Split exact sequences are available in Mathlib. `CategoryTheory.ShortComplex.Splitting`
captures the notion of a splitting of a short complex. The book asserts that the
canonical sequence is *split*, which is strictly stronger than short exactness, so
the primary public object here is the splitting witness itself; short exactness is
recovered as its consequence.
-/

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The canonical short complex `X --inl→ X ⊞ Z --snd→ Z` of Etingof Example 7.8.3. -/
noncomputable abbrev splitShortComplex (X Z : C) : ShortComplex C :=
  ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Z) biprod.snd (by simp)

/-- The canonical **splitting** of the sequence `0 → X → X ⊞ Z → Z → 0`
(Etingof Example 7.8.3).

This is the witness that the sequence is *split*, i.e. that it represents the
trivial extension of `Z` by `X`. Its retraction is `biprod.fst` and its section is
`biprod.inr`; see `split_exact_sequence_splitting_r`, `split_exact_sequence_splitting_s`,
and the retraction/section identities below. -/
noncomputable def split_exact_sequence_splitting (X Z : C) :
    (splitShortComplex X Z).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct X Z

/-- The retraction of the canonical splitting is the first biproduct projection. -/
@[simp]
theorem split_exact_sequence_splitting_r (X Z : C) :
    (split_exact_sequence_splitting X Z).r = biprod.fst := rfl

/-- The section of the canonical splitting is the second biproduct injection. -/
@[simp]
theorem split_exact_sequence_splitting_s (X Z : C) :
    (split_exact_sequence_splitting X Z).s = biprod.inr := rfl

/-- The retraction identity: `biprod.inl ≫ biprod.fst = 𝟙 X`. -/
theorem split_exact_sequence_f_r (X Z : C) :
    (biprod.inl : X ⟶ X ⊞ Z) ≫ (split_exact_sequence_splitting X Z).r = 𝟙 X :=
  (split_exact_sequence_splitting X Z).f_r

/-- The section identity: `biprod.inr ≫ biprod.snd = 𝟙 Z`. -/
theorem split_exact_sequence_s_g (X Z : C) :
    (split_exact_sequence_splitting X Z).s ≫ (biprod.snd : X ⊞ Z ⟶ Z) = 𝟙 Z :=
  (split_exact_sequence_splitting X Z).s_g

/-- The splitting compatibility identity `r ≫ f + g ≫ s = 𝟙 (X ⊞ Z)`. -/
theorem split_exact_sequence_splitting_id (X Z : C) :
    (split_exact_sequence_splitting X Z).r ≫ (biprod.inl : X ⟶ X ⊞ Z) +
      (biprod.snd : X ⊞ Z ⟶ Z) ≫ (split_exact_sequence_splitting X Z).s = 𝟙 (X ⊞ Z) :=
  (split_exact_sequence_splitting X Z).id

/-- The canonical map `X → X ⊞ Z` is a split monomorphism. -/
noncomputable def split_exact_sequence_splitMono (X Z : C) :
    SplitMono (biprod.inl : X ⟶ X ⊞ Z) :=
  (split_exact_sequence_splitting X Z).splitMono_f

/-- The canonical map `X ⊞ Z → Z` is a split epimorphism. -/
noncomputable def split_exact_sequence_splitEpi (X Z : C) :
    SplitEpi (biprod.snd : X ⊞ Z ⟶ Z) :=
  (split_exact_sequence_splitting X Z).splitEpi_g

/-- A split short exact sequence: 0 → X → X ⊕ Z → Z → 0.
(Etingof Example 7.8.3)

In any preadditive category with binary biproducts and a zero object,
the short complex `X --inl→ X ⊞ Z --snd→ Z` admits a splitting
(`split_exact_sequence_splitting`) and is therefore short exact. -/
theorem split_exact_sequence [HasZeroObject C] (X Z : C) :
    (splitShortComplex X Z).ShortExact :=
  (split_exact_sequence_splitting X Z).shortExact

end Etingof
