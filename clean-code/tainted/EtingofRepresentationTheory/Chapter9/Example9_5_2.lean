import EtingofRepresentationTheory.Chapter9.Definition9_5_1
import EtingofRepresentationTheory.Chapter9.Problem9_3_2
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Example 9.5.2: Blocks of specific algebras

(i) For a semisimple algebra A, the blocks of A-fmod correspond to the simple summands.
Each block is equivalent to the category of vector spaces (since every module is a direct
sum of copies of one simple).

(ii) If A is a commutative local artinian algebra, then A has only one block (since there
is only one simple module, the residue field).

(iii) The algebra from Problem 9.3.2 has one block.

## Formalized statements

Part (i) is captured through the project's `Etingof.AreLinked` relation, which, faithful to
Definition 9.5.1, links simple modules via chains of simple modules connected by
`Ext¹`-adjacency. Over a semisimple ring `Ext¹` vanishes identically, so the linking relation
on simples collapses to isomorphism. We prove `Etingof.semisimple_areLinked_iff_iso`: for
simple `X, Y`, `AreLinked X Y ↔ X ≅ Y`, i.e. each block contains a single isomorphism class of
simple objects. `Etingof.semisimple_blocks_singleton` is the forward direction.

The full categorical clause is formalized in `Example9_5_2_BlockEquivalence.lean`. Under the
book's hypotheses (a finite-dimensional semisimple algebra over an algebraically closed field),
`Etingof.Problem953.semisimpleBlockEquivalence` identifies the entire block category
`Etingof.Problem953.BlockCat R S` with `ModuleCat k`, while
`Etingof.Problem953.semisimpleBlockEquivalenceFin` gives the book-faithful restriction to
finite-dimensional objects.

Part (iii), "the algebra of Problem 9.3.2 has one block": the
generators-and-relations algebra `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)` is constructed in
`Chapter9/Problem9_3_2.lean`, together with its two non-isomorphic one-dimensional simple
modules `S₊` and `S₋`. The two simples are linked by a nonsplit extension
`0 → S₋ → P₊ → S₊ → 0`, so `Ext¹(S₊, S₋) ≠ 0`; this is exactly the regime that part (i)
(semisimple) excludes. We re-export the resulting `Etingof.AreLinked` statement as
`Etingof.problem_9_3_2_single_block` below.
-/

universe v u

open CategoryTheory

/-- Over a semisimple ring no two objects of `ModuleCat R` are `Ext¹`-adjacent: every module
is projective, so `Ext¹(A, B)` is subsingleton in both directions and therefore not
nontrivial. -/
theorem Etingof.semisimple_not_extAdjacent
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (A B : ModuleCat.{v} R) : ¬ Etingof.ExtAdjacent R A B := by
  intro h
  rcases h with h | h
  · haveI : Module.Projective R A := Module.projective_of_isSemisimpleRing R A
    haveI := Abelian.Ext.subsingleton_of_projective A B 0
    exact not_nontrivial _ h
  · haveI : Module.Projective R B := Module.projective_of_isSemisimpleRing R B
    haveI := Abelian.Ext.subsingleton_of_projective B A 0
    exact not_nontrivial _ h

/-- For a semisimple ring, the linking relation on simple modules collapses to isomorphism:
two simple modules are linked iff they are isomorphic. Equivalently, each block contains a
single isomorphism class of simples. This is Etingof Example 9.5.2 (i) ("each block is
equivalent to the category of vector spaces, and thus has only one simple object"): since
`Ext¹` vanishes over a semisimple ring, the only chains between simples are isomorphisms. -/
theorem Etingof.semisimple_areLinked_iff_iso
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R) (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) :
    Etingof.AreLinked R X Y ↔ Nonempty (X ≅ Y) := by
  refine ⟨fun hlinked => ?_, fun e => Etingof.areLinked_of_iso R hX hY e.some⟩
  -- With `ExtAdjacent` empty, the only base relation is isomorphism; induct on `EqvGen`.
  -- The simplicity hypotheses are not needed here, and would be reverted by the induction.
  clear hX hY
  induction hlinked with
  | rel _ _ h =>
    obtain ⟨_, _, h⟩ := h
    rcases h with h | h
    · exact absurd h (Etingof.semisimple_not_extAdjacent R _ _)
    · exact h
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨e.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁ ≪≫ e₂⟩

/-- For a semisimple ring, any two linked simple modules are isomorphic, so each simple module
forms its own block. (Etingof Example 9.5.2 (i)) -/
theorem Etingof.semisimple_blocks_singleton
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R)
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y)
    (hlinked : Etingof.AreLinked R X Y) :
    Nonempty (X ≅ Y) :=
  (Etingof.semisimple_areLinked_iff_iso R X Y hX hY).mp hlinked

/-- For a commutative local artinian ring, there is only one simple module (up to
isomorphism), so all modules belong to a single block.
(Etingof Example 9.5.2 (ii)) -/
theorem Etingof.local_artinian_single_block
    (R : Type u) [CommRing R] [Small.{v} R] [IsLocalRing R] [IsArtinianRing R]
    (X Y : ModuleCat.{v} R)
    (hX : IsSimpleModule R X) (hY : IsSimpleModule R Y) :
    Etingof.AreLinked R X Y := by
  -- For a commutative local ring, the unique maximal ideal is IsLocalRing.maximalIdeal R.
  -- Every simple module is isomorphic to R/m. So X ≅ R/m ≅ Y.
  obtain ⟨I, hI, ⟨eX⟩⟩ := isSimpleModule_iff_quot_maximal.mp hX
  obtain ⟨J, hJ, ⟨eY⟩⟩ := isSimpleModule_iff_quot_maximal.mp hY
  have hIm : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
  have hJm : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hJ
  subst hIm; subst hJm
  -- Now eX : X ≃ₗ[R] R ⧸ m and eY : Y ≃ₗ[R] R ⧸ m, so X ≅ Y
  have e : X ≃ₗ[R] Y := eX.trans eY.symm
  exact Etingof.areLinked_of_iso R hX hY
    { hom := ModuleCat.ofHom e.toLinearMap
      inv := ModuleCat.ofHom e.symm.toLinearMap
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }

/-- The algebra `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)` of Problem 9.3.2 has a single block:
its two non-isomorphic simple modules `S₊` and `S₋` are `Etingof.AreLinked`, via the nonsplit
extension `0 → S₋ → P₊ → S₊ → 0` (so `Ext¹(S₊, S₋) ≠ 0`). Unlike parts (i) and (ii), the
linking here is a nonsplit extension rather than an isomorphism.
(Etingof Example 9.5.2 (iii); see `Chapter9/Problem9_3_2.lean` for the construction.) -/
theorem Etingof.problem_9_3_2_single_block :
    Etingof.AreLinked Etingof.Problem932.A
      (ModuleCat.of _ Etingof.Problem932.Splus)
      (ModuleCat.of _ Etingof.Problem932.Sminus) :=
  Etingof.Problem932.areLinked

open Etingof.Problem932 in
/-- Every simple module over the Problem 9.3.2 algebra is linked to `S₊`: by the classification
of simple modules it is isomorphic to `S₊` or to `S₋`, and `S₋` is itself linked to `S₊`. -/
theorem Etingof.problem_9_3_2_areLinked_splus
    (Z : Type) [AddCommGroup Z] [Module ℂ Z] [Module A Z] [IsScalarTower ℂ A Z]
    [IsSimpleModule A Z] :
    Etingof.AreLinked A (ModuleCat.of A Z) (ModuleCat.of A Splus) := by
  have hZ : IsSimpleModule A (ModuleCat.of A Z) := inferInstanceAs (IsSimpleModule A Z)
  have hP : IsSimpleModule A (ModuleCat.of A Splus) := inferInstanceAs (IsSimpleModule A Splus)
  have hM : IsSimpleModule A (ModuleCat.of A Sminus) := inferInstanceAs (IsSimpleModule A Sminus)
  rcases nonempty_linearEquiv_splus_or_sminus Z with h | h
  · obtain ⟨e⟩ := h
    exact Etingof.areLinked_of_iso A hZ hP
      { hom := ModuleCat.ofHom e.toLinearMap
        inv := ModuleCat.ofHom e.symm.toLinearMap
        hom_inv_id := by ext z; exact e.symm_apply_apply z
        inv_hom_id := by ext z; exact e.apply_symm_apply z }
  · obtain ⟨e⟩ := h
    refine Relation.EqvGen.trans _ _ _ (Etingof.areLinked_of_iso A hZ hM
        { hom := ModuleCat.ofHom e.toLinearMap
          inv := ModuleCat.ofHom e.symm.toLinearMap
          hom_inv_id := by ext z; exact e.symm_apply_apply z
          inv_hom_id := by ext z; exact e.apply_symm_apply z })
      (Relation.EqvGen.symm _ _ Etingof.problem_9_3_2_single_block)

open Etingof.Problem932 in
/-- **The Problem 9.3.2 algebra has a single block, for every simple module.** Any two simple
`A`-modules are `Etingof.AreLinked`. This upgrades `Etingof.problem_9_3_2_single_block`, which
only links the two exhibited simples `S₊` and `S₋`, using the classification theorem
`Etingof.Problem932.simple_module_classification`: those two are all the simple modules.
(Etingof Example 9.5.2 (iii).) -/
theorem Etingof.problem_9_3_2_single_block_of_simple
    (X Y : Type) [AddCommGroup X] [Module ℂ X] [Module A X] [IsScalarTower ℂ A X]
    [IsSimpleModule A X] [AddCommGroup Y] [Module ℂ Y] [Module A Y] [IsScalarTower ℂ A Y]
    [IsSimpleModule A Y] :
    Etingof.AreLinked A (ModuleCat.of A X) (ModuleCat.of A Y) :=
  Relation.EqvGen.trans _ _ _ (Etingof.problem_9_3_2_areLinked_splus X)
    (Relation.EqvGen.symm _ _ (Etingof.problem_9_3_2_areLinked_splus Y))
