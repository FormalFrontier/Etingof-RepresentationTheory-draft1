import EtingofRepresentationTheory.Chapter9.Definition9_5_1
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

Part (i) is captured at the level the project's `Etingof.AreLinked` definition supports.
That definition (Definition 9.5.1) links *all* modules — not only the simple ones — by
`Ext¹`-adjacency, so over a semisimple ring, where `Ext¹` vanishes identically, the linking
relation collapses to isomorphism. We therefore prove the sharp statement
`Etingof.semisimple_areLinked_iff_iso`: over a semisimple ring **every** block is a single
isomorphism class, covering all modules in a block, not just the simple ones. The original
`Etingof.semisimple_blocks_singleton` (linked simples are isomorphic, hence each block has a
unique simple object) is an immediate corollary.

Note the relationship to the book's phrasing "each block is equivalent to the category of
vector spaces". Etingof's block attached to a simple `S` is the full subcategory of modules
whose Jordan–Hölder factors are all `≅ S`; over a semisimple ring that subcategory is the
isotypic component `{S^{⊕n}}`, equivalent to vector spaces with `n` the dimension. The
project's `AreLinked` relation partitions *more finely* — because `Ext¹ = 0` forbids any
nonsplit extension, `S` and `S^{⊕2}` end up in different `AreLinked`-blocks. Both viewpoints
agree on the load-bearing consequence formalized here, "one simple object per block"; the
finer `AreLinked` statement records that no larger module is linked to a simple. Promoting
the Etingof "≃ Vec" subcategory equivalence would require an isotypic-subcategory definition
not present in Definition 9.5.1.

Part (iii) — "the algebra of Problem 9.3.2 has one block" — requires first *constructing*
that generators-and-relations algebra `A = ℂ⟨g, x⟩ / (gx + xg, x², g² - 1)` and then proving
`Ext¹` between its two one-dimensional simples is nonzero (the linking is via a genuine
nonsplit extension, not an isomorphism). That construction is tracked as its own work item
(Problem 9.3.2) and is not formalized here.
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

/-- For a semisimple ring, the linking relation collapses to isomorphism for **all** modules
(not just simple ones): two modules are linked iff they are isomorphic. Equivalently, each
block is a single isomorphism class. This is the "covering all modules in a block" content of
Etingof Example 9.5.2 (i) ("each block is equivalent to the category of vector spaces"): since
`Ext¹` vanishes over a semisimple ring, there are no nonsplit extensions to enlarge a block
beyond one isomorphism class. -/
theorem Etingof.semisimple_areLinked_iff_iso
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R) :
    Etingof.AreLinked R X Y ↔ Nonempty (X ≅ Y) := by
  refine ⟨fun hlinked => ?_, fun e => Etingof.areLinked_of_iso R e.some⟩
  -- With `ExtAdjacent` empty, the only base relation is isomorphism; induct on `EqvGen`.
  induction hlinked with
  | rel _ _ h =>
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

/-- For a semisimple ring, any two non-isomorphic simple modules have
`Ext¹ = 0` in both directions, so each simple module forms its own block.
(Etingof Example 9.5.2 (i)) -/
theorem Etingof.semisimple_blocks_singleton
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R)
    (_hX : IsSimpleModule R X) (_hY : IsSimpleModule R Y)
    (hlinked : Etingof.AreLinked R X Y) :
    Nonempty (X ≅ Y) :=
  (Etingof.semisimple_areLinked_iff_iso R X Y).mp hlinked

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
  exact Etingof.areLinked_of_iso R
    { hom := ModuleCat.ofHom e.toLinearMap
      inv := ModuleCat.ofHom e.symm.toLinearMap
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by ext x; exact e.apply_symm_apply x }
