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
is only one simple module — the residue field).

(iii) The algebra from Problem 9.3.2 has one block.

## Scope of this file

Part (i) is captured through the project's `Etingof.AreLinked` relation, which — faithful to
Definition 9.5.1 — links **simple** modules via chains of *simple* modules connected by
`Ext¹`-adjacency. Over a semisimple ring `Ext¹` vanishes identically, so the linking relation
on simples collapses to isomorphism. We prove `Etingof.semisimple_areLinked_iff_iso`: for
simple `X, Y`, `AreLinked X Y ↔ X ≅ Y`, i.e. each block contains a single isomorphism class of
simple objects. `Etingof.semisimple_blocks_singleton` is the forward direction.

Note the relationship to the book's phrasing "each block is equivalent to the category of
vector spaces". Etingof's block attached to a simple `S` is the full subcategory of modules
whose Jordan–Hölder factors are all in `S`'s linking class (the predicate `Etingof.InBlock`);
over a semisimple ring that subcategory is the isotypic component `{S^{⊕n}}`, equivalent to
vector spaces. The statement formalized here is the load-bearing consequence "one simple object
per block". Promoting the Etingof "≃ Vec" subcategory equivalence would require an
isotypic-subcategory equivalence beyond the scope of Definition 9.5.1.

Part (iii) — "the algebra of Problem 9.3.2 has one block" — is now formalized. The
generators-and-relations algebra `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)` is constructed in
`Chapter9/Problem9_3_2.lean`, together with its two non-isomorphic one-dimensional simple
modules `S₊` and `S₋`. The two simples are linked by a genuine nonsplit extension
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

/-- For a semisimple ring, the linking relation on **simple** modules collapses to isomorphism:
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
linking here is a genuine nonsplit extension rather than an isomorphism.
(Etingof Example 9.5.2 (iii); see `Chapter9/Problem9_3_2.lean` for the construction.) -/
theorem Etingof.problem_9_3_2_single_block :
    Etingof.AreLinked Etingof.Problem932.A
      (ModuleCat.of _ Etingof.Problem932.Splus)
      (ModuleCat.of _ Etingof.Problem932.Sminus) :=
  Etingof.Problem932.areLinked
