import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteLength
import EtingofRepresentationTheory.Chapter9.Definition9_5_1
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_CompositionFactor
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_Connectivity

/-!
# Problem 9.5.3: Blocks and central idempotents

Etingof Problem 9.5.3 relates the block decomposition of a finite abelian category `𝒞`
(here the category of finite dimensional `A`-modules) to the structure of `A`.

* **(i)** There is a natural bijection between blocks of `𝒞` and *indecomposable* central
  idempotents `eₖ` of `A` (central idempotents that cannot be split nontrivially into a sum of
  two orthogonal central idempotents), under which `𝒞ₖ` is the category of `eₖ A`-modules.

* **(ii)** Every indecomposable object of `𝒞` lies in some block `𝒞ₖ`, and
  `Hom(M, N) = 0` whenever `M ∈ 𝒞ₖ`, `N ∈ 𝒞ₗ` with `k ≠ l`. Thus `𝒞 = ⊕ₖ 𝒞ₖ`.

* **(iii)** Determine the blocks of the category of left `A`-modules for `A = k[S₃]` with `k`
  of characteristic `2`. *(Deferred: this concrete modular-representation computation is left
  to a follow-up statement-pass item.)*

## Statement-pass note

Blocks are `Etingof.Block R` and block membership is `Etingof.InBlock R S M` (Definition
9.5.1). "Indecomposable central idempotent" is the predicate
`Etingof.Problem953.IsIndecomposableCentralIdempotent` defined below (a nonzero central
idempotent not expressible as a sum of two nonzero orthogonal central idempotents).
"`Hom(M, N) = 0`" is `Subsingleton (M ⟶ N)`, and "indecomposable object" is
`CategoryTheory.Indecomposable`. Two blocks are distinct exactly when their representative
simple modules are not `Etingof.AreLinked`. Proofs are deferred (`sorry`).
-/

universe v u

open CategoryTheory

namespace Etingof

namespace Problem953

variable (R : Type u) [Ring R]

/-- An **indecomposable central idempotent** of a ring `R`: a nonzero central idempotent that
cannot be written as a sum `e = e₁ + e₂` of two nonzero orthogonal central idempotents. These
are the primitive idempotents of the center; by Problem 9.5.3(i) they index the blocks. -/
def IsIndecomposableCentralIdempotent (e : R) : Prop :=
  e ≠ 0 ∧ IsIdempotentElem e ∧ (∀ y : R, e * y = y * e) ∧
    ¬ ∃ e₁ e₂ : R, e₁ ≠ 0 ∧ e₂ ≠ 0 ∧ IsIdempotentElem e₁ ∧ IsIdempotentElem e₂ ∧
      (∀ y, e₁ * y = y * e₁) ∧ (∀ y, e₂ * y = y * e₂) ∧ e₁ * e₂ = 0 ∧ e = e₁ + e₂

/-- **Central character of a simple module (Schur's lemma).** A central idempotent `e` of a
ring `R` acts on any simple `R`-module `M` as the scalar `0` or `1`: either `e • m = 0` for all
`m`, or `e • m = m` for all `m`.

Indeed `φ : m ↦ e • m` is an `R`-linear endomorphism of `M` (centrality of `e` gives
`φ (r • m) = r • φ m`) which is idempotent (`e² = e`). Since `M` is simple, `Module.End R M` is a
division ring by Schur's lemma, and the only idempotents of a division ring are `0` and `1`, so
`φ = 0` or `φ = id`.

This is the building block for the block ↔ central-idempotent bijection of Problem 9.5.3(i): it
assigns to each simple module the set of central idempotents that act on it as `1` (its "central
character"), and linked simples turn out to share this character. The result holds for an
arbitrary ring; no finiteness is needed here. -/
theorem centralIdempotent_smul_simple {M : Type*} [AddCommGroup M] [Module R M]
    [IsSimpleModule R M] {e : R} (he : IsIdempotentElem e) (hc : ∀ y : R, e * y = y * e) :
    (∀ m : M, e • m = 0) ∨ (∀ m : M, e • m = m) := by
  classical
  -- `φ : m ↦ e • m` as an `R`-linear endomorphism of `M`; `R`-linearity uses centrality of `e`.
  let φ : Module.End R M :=
    { toFun := fun m => e • m
      map_add' := fun m₁ m₂ => smul_add e m₁ m₂
      map_smul' := fun r m => by simp only [RingHom.id_apply, smul_smul, hc r] }
  -- `φ` is idempotent because `e` is.
  have hφ : IsIdempotentElem φ := by
    ext m
    show e • e • m = e • m
    rw [smul_smul, he]
  -- `Module.End R M` is a division ring (Schur), whose only idempotents are `0` and `1`.
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hφ with h | h
  · left; intro m; exact LinearMap.congr_fun h m
  · right; intro m; exact LinearMap.congr_fun h m

/-- The type of **central idempotents** of `R`: idempotent elements lying in the center. This is
the domain of the central-character indicator `centralCharacter`. -/
abbrev CentralIdempotent : Type u :=
  {e : R // IsIdempotentElem e ∧ ∀ y : R, e * y = y * e}

open scoped Classical in
/-- **Central character of a simple module.** By `centralIdempotent_smul_simple` a central
idempotent `e` acts on the simple module `S` either as `0` or as the identity; this Boolean
records which, returning `true` exactly when `e` acts as the identity. It is the "central
character" of `S` at `e`, and Problem 9.5.3(i) shows it is constant on each linkage class. -/
noncomputable def centralCharacter {S : ModuleCat.{v} R} (_hS : IsSimpleModule R S)
    (e : CentralIdempotent R) : Bool :=
  decide (∀ m : (S : Type v), e.1 • m = m)

/-- `centralCharacter` is `true` exactly when the idempotent acts as the identity. -/
theorem centralCharacter_eq_true_iff {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (e : CentralIdempotent R) :
    centralCharacter R hS e = true ↔ ∀ m : (S : Type v), e.1 • m = m := by
  classical
  unfold centralCharacter
  rw [decide_eq_true_eq]

/-- `centralCharacter` is `false` exactly when the idempotent acts as `0`. -/
theorem centralCharacter_eq_false_iff {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (e : CentralIdempotent R) :
    centralCharacter R hS e = false ↔ ∀ m : (S : Type v), e.1 • m = 0 := by
  classical
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  rw [← Bool.not_eq_true, centralCharacter_eq_true_iff]
  constructor
  · intro h
    rcases centralIdempotent_smul_simple R (M := (S : Type v)) (e := e.1) e.2.1 e.2.2 with h0 | h1
    · exact h0
    · exact absurd h1 h
  · intro h0 h1
    obtain ⟨x, hx⟩ := exists_ne (0 : (S : Type v))
    exact hx ((h1 x).symm.trans (h0 x))

/-- **Problem 9.5.3 (i).** For a finite dimensional algebra `R` over a field `k`, there is a
bijection between the blocks of the category of finite dimensional `R`-modules (linkage classes
of simple modules) and the indecomposable central idempotents of `R`.

The finiteness hypothesis is essential and was missing from the original statement of this item.
Over a general ring the two sides differ: for `R = ℤ` the simple modules `ℤ/p` are pairwise
unlinked (`Ext¹_ℤ(ℤ/p, ℤ/q) = 0` for `p ≠ q`), so there is one block per prime — infinitely many
— while the only indecomposable central idempotent of `ℤ` is `1`. A finiteness assumption forcing
a `1 = Σ eₖ` decomposition into primitive central idempotents (here: `FiniteDimensional k R`) is
what makes the two sides match. We keep the ambient ring `R` and simply add that it is a finite
dimensional `k`-algebra, so the block API (`Etingof.Block R`, `IsIndecomposableCentralIdempotent
R`) is unchanged.

The proof (still to be filled) runs through `centralIdempotent_smul_simple`: each simple module
has a central character (which central idempotents act as `1`), linked simples share it, and the
primitive central idempotents `eₖ` in the decomposition `1 = Σ eₖ` are exactly the indicators of
the blocks. -/
theorem blocks_equiv_indecomposableCentralIdempotents
    {k : Type*} [Field k] [Algebra k R] [FiniteDimensional k R] [Small.{v} R] :
    Nonempty (Etingof.Block.{v} R ≃ {e : R // IsIndecomposableCentralIdempotent R e}) := by
  sorry

/-- **Problem 9.5.3 (ii), orthogonality.** If `M` lies in the block of the simple module `S`
and `N` lies in the block of the simple module `T`, and `S`, `T` are not linked (i.e. `M`, `N`
are in different blocks), then `Hom(M, N) = 0`. -/
theorem hom_subsingleton_of_not_linked [Small.{v} R]
    {S T : ModuleCat.{v} R} (hS : IsSimpleModule R S) (hT : IsSimpleModule R T)
    {M N : ModuleCat.{v} R} (hM : Etingof.InBlock R S M) (hN : Etingof.InBlock R T N)
    (hST : ¬ Etingof.AreLinked R S T) :
    Subsingleton (M ⟶ N) := by
  -- It suffices to show every morphism `M ⟶ N` is zero.
  suffices h0 : ∀ f : M ⟶ N, f = 0 by exact ⟨fun f g => by rw [h0 f, h0 g]⟩
  intro f
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_zero]
  by_contra hfhom
  -- If `f.hom ≠ 0` its range is a nonzero submodule of `N`, hence has a composition factor `U`.
  have hrange : LinearMap.range f.hom ≠ ⊥ := by rwa [Ne, LinearMap.range_eq_bot]
  haveI hnt : Nontrivial (LinearMap.range f.hom) := Submodule.nontrivial_iff_ne_bot.mpr hrange
  obtain ⟨U, hU⟩ :=
    Etingof.exists_isCompositionFactor (M := ModuleCat.of R (LinearMap.range f.hom))
  -- `U` is a composition factor of `N` (range is a submodule of `N`) ...
  have hUN : Etingof.IsCompositionFactor R N U :=
    Etingof.IsCompositionFactor.of_submodule (LinearMap.range f.hom) hU
  -- ... and of `M` (range is a surjective image of `M`).
  have hUM : Etingof.IsCompositionFactor R M U :=
    Etingof.IsCompositionFactor.of_surjective f.hom.rangeRestrict
      (LinearMap.surjective_rangeRestrict _) hU
  -- Both blocks then link `S` and `T`, contradicting `hST`.
  have h1 : Etingof.AreLinked R U S := hM U hUM
  have h2 : Etingof.AreLinked R U T := hN U hUN
  exact hST ((Etingof.areLinked_equivalence R).trans
    ((Etingof.areLinked_equivalence R).symm h1) h2)

/-- **Block-connectivity of an indecomposable module.** The composition factors of an
indecomposable finite-length module all lie in a single linkage class: any two composition
factors `S`, `T` of `M` are linked.

This is the mathematical core of Problem 9.5.3(ii). Proof strategy (book proof, contrapositive):
the composition factors of `M` split into linkage classes; if `S` and `T` were *not* linked,
the factors would occupy `≥ 2` distinct linkage classes. Let `𝒮` be the saturated set of
simples linked to `S` and `𝒮'` its complement (a union of full linkage classes, so no simple
in `𝒮` is linked to any simple in `𝒮'`). The largest submodule `M_𝒮 ≤ M` with all composition
factors in `𝒮` and the analogous `M_{𝒮'}` then give a nontrivial biproduct decomposition
`M ≅ M_𝒮 ⊞ M_{𝒮'}` (both nonzero: `S` forces `M_𝒮 ≠ 0`, `T` forces `M_{𝒮'} ≠ 0`),
contradicting `Indecomposable M`. The decomposition itself is the Ext-splitting mechanism behind
`hom_subsingleton_of_not_linked`: `Ext¹(X, Y) = 0` whenever every composition factor of `X` is
unlinked to every composition factor of `Y` (dévissage from the simple base case
`¬ Etingof.AreLinked R S T ⟹ Subsingleton (Abelian.Ext S T 1)` via the covariant/contravariant
Ext long exact sequences), so each layer of the composition series of `M` splits off along the
`𝒮`/`𝒮'` partition. -/
theorem compositionFactors_areLinked [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M)
    {S T : ModuleCat.{v} R}
    (hS : Etingof.IsCompositionFactor R M S) (hT : Etingof.IsCompositionFactor R M T) :
    Etingof.AreLinked R S T :=
  Etingof.compositionFactors_areLinked_aux hM hfl hS hT

/-- **Problem 9.5.3 (ii), decomposition.** Every indecomposable finite-length object lies in
some block: there is a simple module `S` such that all composition factors of `M` are linked to
`S`. The finite-length assumption is the genuine `IsFiniteLength R M` (the earlier
"`∃ composition factor`" form was too weak — it does not force finite length, and the block
statement is false without it, e.g. `M = ℤ` over `R = ℤ`). -/
theorem exists_block_of_indecomposable [Small.{v} R]
    {M : ModuleCat.{v} R} (hM : Indecomposable M) (hfl : IsFiniteLength R M) :
    ∃ S : ModuleCat.{v} R, IsSimpleModule R S ∧ Etingof.InBlock R S M := by
  -- `M` is nonzero (indecomposable), hence its carrier is nontrivial and has a factor `S`.
  haveI hnt : Nontrivial (M : Type v) := by
    rw [← not_subsingleton_iff_nontrivial, ← ModuleCat.isZero_iff_subsingleton]
    exact hM.1
  obtain ⟨S, hS⟩ := Etingof.exists_isCompositionFactor (M := M)
  refine ⟨S, hS.1, ?_⟩
  -- every composition factor `T` of `M` is linked to `S` by block-connectivity.
  intro T hT
  exact (Etingof.areLinked_equivalence R).symm
    (compositionFactors_areLinked R hM hfl hS hT)

end Problem953

end Etingof
