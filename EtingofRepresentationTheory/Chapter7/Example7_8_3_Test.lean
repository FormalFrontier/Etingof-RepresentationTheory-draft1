import EtingofRepresentationTheory.Chapter7.Example7_8_3

/-!
# Downstream import/`#check` test for Example 7.8.3

This file imports `Chapter7/Example7_8_3.lean` and pins the public API of the split
short exact sequence `0 → X → X ⊞ Z → Z → 0`. Its purpose is to catch a regression in
the source even when cached oleans would otherwise hide it from the aggregate build:
because this file `import`s the item file and re-elaborates the endpoints, it forces a
fresh check of their public signatures.

The book's assertion is that the sequence is *split*, which is stronger than short
exactness. The key regression this test guards against is the splitting witness
disappearing behind a `.ShortExact`-only public surface (issue #7562).

See issue #7562 (expose the canonical splitting witness).
-/

open CategoryTheory CategoryTheory.Limits

-- The primary public object is an actual `ShortComplex.Splitting`, not just short
-- exactness.
#check @Etingof.split_exact_sequence_splitting
#check @Etingof.split_exact_sequence
#check @Etingof.split_exact_sequence_splitMono
#check @Etingof.split_exact_sequence_splitEpi

section
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

-- Clients must be able to recover the splitting witness from the public API, and use
-- its retraction/section identities, without reaching into any private namespace.
noncomputable example (X Z : C) : (Etingof.splitShortComplex X Z).Splitting :=
  Etingof.split_exact_sequence_splitting X Z

example (X Z : C) :
    (biprod.inl : X ⟶ X ⊞ Z) ≫ (Etingof.split_exact_sequence_splitting X Z).r = 𝟙 X :=
  Etingof.split_exact_sequence_f_r X Z

example (X Z : C) :
    (Etingof.split_exact_sequence_splitting X Z).s ≫ (biprod.snd : X ⊞ Z ⟶ Z) = 𝟙 Z :=
  Etingof.split_exact_sequence_s_g X Z

-- The retraction and section are the expected biproduct maps.
example (X Z : C) : (Etingof.split_exact_sequence_splitting X Z).r = biprod.fst :=
  Etingof.split_exact_sequence_splitting_r X Z

example (X Z : C) : (Etingof.split_exact_sequence_splitting X Z).s = biprod.inr :=
  Etingof.split_exact_sequence_splitting_s X Z

-- Short exactness remains available as a consequence of the splitting.
example [HasZeroObject C] (X Z : C) : (Etingof.splitShortComplex X Z).ShortExact :=
  Etingof.split_exact_sequence X Z

end
