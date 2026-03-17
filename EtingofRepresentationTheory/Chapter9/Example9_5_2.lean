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
-/

universe v u

open CategoryTheory

/-- For a semisimple ring, any two non-isomorphic simple modules have
`Ext¹ = 0` in both directions, so each simple module forms its own block.
(Etingof Example 9.5.2 (i)) -/
theorem Etingof.semisimple_blocks_singleton
    (R : Type u) [Ring R] [Small.{v} R] [IsSemisimpleRing R]
    (X Y : ModuleCat.{v} R)
    (_hX : IsSimpleModule R X) (_hY : IsSimpleModule R Y)
    (hlinked : Etingof.AreLinked R X Y) :
    Nonempty (X ≅ Y) := by
  -- For semisimple R, all modules are projective, so Ext¹ is subsingleton
  -- (hence not nontrivial). This makes ExtAdjacent vacuously false.
  -- The only way modules can be linked is via isomorphism.
  have not_adj : ∀ (A B : ModuleCat.{v} R), ¬ Etingof.ExtAdjacent R A B := by
    intro A B h
    rcases h with h | h
    · haveI : Module.Projective R A := Module.projective_of_isSemisimpleRing R A
      haveI := Abelian.Ext.subsingleton_of_projective A B 0
      exact not_nontrivial _ h
    · haveI : Module.Projective R B := Module.projective_of_isSemisimpleRing R B
      haveI := Abelian.Ext.subsingleton_of_projective B A 0
      exact not_nontrivial _ h
  -- With ExtAdjacent empty, the only base relation is isomorphism.
  -- Induct on EqvGen to extract the isomorphism.
  clear _hX _hY
  induction hlinked with
  | rel _ _ h =>
    rcases h with h | h
    · exact absurd h (not_adj _ _)
    · exact h
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨e.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨e₁ ≪≫ e₂⟩

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
