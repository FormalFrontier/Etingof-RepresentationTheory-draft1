/-
Copyright (c) 2026 FormalFrontier contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalFrontier contributors
-/
import EtingofRepresentationTheory.Chapter4.Example4_3_S3
import EtingofRepresentationTheory.Chapter4.Example4_3_S4
import EtingofRepresentationTheory.Chapter4.Example4_8_1.S4
import EtingofRepresentationTheory.Chapter5.CharEqIso

/-!
# The quotient `S₄ / V₄ ≃ S₃` and the two-dimensional representation

This file supplies the named quotient-and-pullback construction behind the two-dimensional
row of the `S₄` character table.  The action of `S₄` on the three pair-partitions has kernel
the concrete Klein four subgroup.  It is onto `S₃`, hence identifies `S₄ / V₄` with `S₃`.
Restricting the named standard representation of `S₃` along this quotient map gives the
existing two-dimensional representation of `S₄`.
-/

namespace Etingof.Example4_3_S4

open Equiv Function

noncomputable section

/-- The three nonidentity elements of the Klein four subgroup of `S₄`. -/
def kleinFourElement : Fin 3 → S4 :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- The subgroup laws are an exhaustive calculation on the four displayed permutations.
/-- The concrete Klein four subgroup `{1, (01)(23), (02)(13), (03)(12)} ≤ S₄`. -/
def kleinFourSubgroup : Subgroup S4 where
  carrier := {g | g = 1 ∨ ∃ i, g = kleinFourElement i}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide
  inv_mem' := by
    intro a ha
    revert a
    decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- This checks the explicit 24-element action table against the four displayed elements.
/-- The kernel of the action of `S₄` on pair-partitions is exactly `V₄`. -/
theorem actHom_ker_eq_kleinFour : actHom.ker = kleinFourSubgroup := by
  ext g
  change actHom g = 1 ↔ (g = 1 ∨ ∃ i, g = kleinFourElement i)
  revert g
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- Exhaustive search through the six target permutations supplies a preimage for each one.
/-- The action of `S₄` on its three pair-partitions is onto `S₃`. -/
theorem actHom_surjective : Surjective actHom := by
  intro g
  revert g
  decide

instance kleinFourSubgroup_normal : kleinFourSubgroup.Normal := by
  rw [← actHom_ker_eq_kleinFour]
  infer_instance

/-- The book's quotient identification `S₄ / V₄ ≃ S₃`. -/
noncomputable def quotientKleinFourEquivS3 : S4 ⧸ kleinFourSubgroup ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq actHom_ker_eq_kleinFour.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective actHom actHom_surjective)

/-- The named standard representation of `S₃`, pulled back along `actHom : S₄ → S₃`. -/
def s3StandardPullback : FDRep ℂ S4 :=
  (Action.res (FGModuleCat ℂ) actHom).obj Etingof.Example4_3_S3.stdRep

/-- The character of the pullback is the `S₃` standard character evaluated at `actHom g`. -/
@[simp]
theorem s3StandardPullback_character (g : S4) :
    s3StandardPullback.character g = Etingof.Example4_3_S3.stdRep.character (actHom g) :=
  rfl

/-- Fixed points of `actHom g` are exactly pair-partitions fixed by `g`. -/
theorem s3_fixCard_actHom (g : S4) :
    Etingof.Example4_3_S3.fixCard (actHom g) = fix3Card g :=
  rfl

/-- The pullback and the existing sum-zero construction have the same character. -/
theorem s3StandardPullback_character_eq_twoDimRep :
    s3StandardPullback.character = twoDimRep.character := by
  funext g
  rw [s3StandardPullback_character, Etingof.Example4_3_S3.stdRep_character,
    twoDimRep_character, s3_fixCard_actHom]

/-- **The two-dimensional `S₄` representation is the pullback of the standard `S₃`
representation along `S₄ → S₄/V₄ ≃ S₃`.** (Etingof Example 4.8.1) -/
theorem s3StandardPullback_iso_twoDimRep :
    Nonempty (s3StandardPullback ≅ twoDimRep) :=
  Etingof.charEq_iso _ _ s3StandardPullback_character_eq_twoDimRep

end


end Etingof.Example4_3_S4


namespace Etingof.Example4_8_1.S4

open Equiv

noncomputable section

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- The two explicit actions are compared over the 24-by-3 finite action table.
/-- The conjugation action used by the character-table construction agrees with the
pair-partition action defining `Example4_3_S4.actHom`. -/
theorem conjIdxS4_eq_actFun (g : S4) (i : Fin 3) :
    conjIdxS4 g i = Etingof.Example4_3_S4.actFun g i := by
  revert g i
  decide

/-- The two presentations count the same fixed pair-partitions. -/
theorem fixCardM_eq_fix3Card (g : S4) :
    fixCardM (G := S4) (α := Fin 3) g = Etingof.Example4_3_S4.fix3Card g := by
  unfold fixCardM Etingof.Example4_3_S4.fix3Card
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change conjIdxS4 g i = i ↔ Etingof.Example4_3_S4.actFun g i = i
  rw [conjIdxS4_eq_actFun]

/-- The character-table representation `repC2` is the named standard `S₃` pullback. -/
theorem repC2_character_eq_s3StandardPullback :
    repC2.character = Etingof.Example4_3_S4.s3StandardPullback.character := by
  funext g
  rw [repC2, stdRepM_character,
    Etingof.Example4_3_S4.s3StandardPullback_character,
    Etingof.Example4_3_S3.stdRep_character, fixCardM_eq_fix3Card,
    Etingof.Example4_3_S4.s3_fixCard_actHom]

/-- The actual two-dimensional row used in the `S₄` character table is equivariantly
isomorphic to the pullback of the named standard representation of `S₃`. -/
theorem repC2_iso_s3StandardPullback :
    Nonempty (repC2 ≅ Etingof.Example4_3_S4.s3StandardPullback) :=
  Etingof.charEq_iso _ _ repC2_character_eq_s3StandardPullback

end


end Etingof.Example4_8_1.S4
