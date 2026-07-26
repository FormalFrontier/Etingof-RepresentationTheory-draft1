/-
Copyright (c) 2026 FormalFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier contributors
-/
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Golden
import EtingofRepresentationTheory.Chapter5.CharEqIso

/-!
# The outer automorphism exchanges the two icosahedral representations of `A₅`

Conjugation by the odd permutation `(12)` normalizes `A₅` and induces its outer
automorphism.  It fixes the identity, three-cycle, and double-transposition classes and
exchanges the two conjugacy classes of five-cycles.  Consequently, twisting `ℂ³₊` by this
automorphism exchanges the two golden-ratio character values and produces a representation
isomorphic to `ℂ³₋`.
-/

namespace Etingof.Example4_8_1.A5

open Equiv

noncomputable section

/-- The transposition `(12)` in `S₅`.  It is not itself in `A₅`, but normalizes `A₅`. -/
def outerTransposition : Equiv.Perm (Fin 5) := Equiv.swap 0 1

/-- The automorphism of `A₅` induced by conjugation with `(12) ∈ S₅`. -/
def outerAutomorphism : MulAut G := MulAut.conjNormal outerTransposition

/-- The outer automorphism is literally conjugation by `(12)` on the underlying permutations. -/
@[simp]
theorem outerAutomorphism_apply (g : G) :
    (outerAutomorphism g : Equiv.Perm (Fin 5)) =
      outerTransposition * (g : Equiv.Perm (Fin 5)) * outerTransposition⁻¹ :=
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- Exhaustively checking the explicit 60-element classifier exceeds the default limit.
/-- Conjugation by `(12)` fixes the first three `A₅` classes and swaps the two five-cycle
classes.  The finite verification uses the explicit 60-element model and class classifier. -/
theorem outerAutomorphism_classIdx (g : G) :
    classIdxA5 (outerAutomorphism g) = ![0, 1, 2, 4, 3] (classIdxA5 g) := by
  revert g
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- Exhaustively checking all possible inner conjugators exceeds the default limit.
/-- In particular, conjugation by `(12)` cannot be conjugation by an element of `A₅`: inner
automorphisms preserve the first five-cycle class, whereas this automorphism exchanges it. -/
theorem outerAutomorphism_not_inner : ¬ ∃ a : G, outerAutomorphism = MulAut.conj a := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun f : MulAut G => classIdxA5 (f (classRepA5 3))) ha
  have hinner : classIdxA5 (MulAut.conj a (classRepA5 3)) = 3 := by
    revert a
    decide
  have hrep : classIdxA5 (classRepA5 3) = 3 := by decide
  rw [outerAutomorphism_classIdx, hrep, hinner] at h
  exact (by decide : (![(0 : Fin 5), 1, 2, 4, 3] (3 : Fin 5)) ≠ 3) h

/-- `ℂ³₊` twisted along the outer automorphism of `A₅`. -/
def repC3plusOuterTwist : FDRep ℂ G :=
  FDRep.of (repC3plus.ρ.comp outerAutomorphism.toMonoidHom)

/-- The character of a twist is the original character evaluated at the automorphism. -/
@[simp]
theorem repC3plusOuterTwist_character (g : G) :
    repC3plusOuterTwist.character g = repC3plus.character (outerAutomorphism g) :=
  rfl

private theorem chiA5_outer_swap (j : Fin 5) :
    chiA5 1 (![0, 1, 2, 4, 3] j) = chiA5 2 j := by
  fin_cases j <;> rfl

private theorem character_eq_classRep (V : FDRep ℂ G) (g : G) :
    V.character g = V.character (classRepA5 (classIdxA5 g)) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  calc
    V.character g = V.character (c * classRepA5 (classIdxA5 g) * c⁻¹) :=
      congrArg V.character hc.symm
    _ = V.character (classRepA5 (classIdxA5 g)) := FDRep.char_conj V _ _

/-- Twisting `ℂ³₊` by the outer automorphism exchanges its golden-ratio character values and
gives exactly the character of `ℂ³₋`. -/
theorem repC3plusOuterTwist_character_eq :
    repC3plusOuterTwist.character = repC3minus.character := by
  funext g
  rw [repC3plusOuterTwist_character, character_eq_classRep,
    repC3plus_character, outerAutomorphism_classIdx, chiA5_outer_swap,
    ← repC3minus_character, ← character_eq_classRep repC3minus]

/-- **The two icosahedral representations are exchanged by the outer automorphism of `A₅`.**
This is the source-level relationship between the two golden-ratio rows in the character table.
(Etingof Example 4.8.1) -/
theorem repC3plus_outerTwist_iso_repC3minus :
    Nonempty (repC3plusOuterTwist ≅ repC3minus) :=
  Etingof.charEq_iso _ _ repC3plusOuterTwist_character_eq

end

end Etingof.Example4_8_1.A5
