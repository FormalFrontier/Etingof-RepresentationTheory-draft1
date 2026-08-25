import EtingofRepresentationTheory.Chapter9.Example9_5_2
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_BlockCategory
import EtingofRepresentationTheory.Infrastructure.MoritaFGRestriction
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-!
# Example 9.5.2(i): a semisimple block is equivalent to vector spaces

This file completes the categorical clause of Example 9.5.2(i). For a finite-dimensional
semisimple algebra R and a simple R-module S, the full block category attached to S is
equivalent to ModuleCat k.

The proof uses the block/corner equivalence from Problem 9.5.3(i). Its corner algebra is
semisimple, and it is simple because all of its simple modules restrict to simple R-modules in
the one block of S; over a semisimple ring those modules are isomorphic. Artin--Wedderburn
therefore identifies the corner algebra with a matrix algebra over k when k is algebraically
closed, and matrix Morita equivalence supplies the required category equivalence.

The result is stated for the categories of all modules. This is stronger than the book's
finite-dimensional statement and in particular covers every object of the finite-dimensional
block, rather than only its simple objects.
-/

universe u

open CategoryTheory

namespace Etingof

namespace Problem953

variable (R : Type u) [Ring R] [Small.{u} R]
variable (k : Type u) [Field k] [Algebra k R] [FiniteDimensional k R]
variable {S : ModuleCat.{u} R} (hS : IsSimpleModule R S)

include k

private noncomputable instance cornerNontrivial :
    Nontrivial (CornerAlgebra R (blockCentralIdempotent R k hS)) := by
  let e := blockCentralIdempotent R k hS
  refine ⟨⟨1, 0, fun h => (simpleIdempotent R k hS).2.1 ?_⟩⟩
  change e.1 = 0
  rw [← cornerEmbedding_one R e, h]
  exact map_zero (cornerEmbedding R e)

/-- The corner algebra belonging to a block of a finite-dimensional semisimple algebra is a
simple ring.

Indeed the corner is semisimple as a quotient of R. Every simple corner module restricts,
along the quotient map, to a simple R-module in the block of S. Since linkage over a
semisimple ring is the same as isomorphism, any two simple corner modules are isomorphic;
fullness of restriction of scalars lifts the resulting R-module isomorphism back to the
corner. Thus the regular corner module is isotypic, which is the semisimple criterion for a
ring to be simple Artinian. -/
theorem corner_isSimpleRing_of_isSemisimpleRing [IsSemisimpleRing R] :
    IsSimpleRing (CornerAlgebra R (blockCentralIdempotent R k hS)) := by
  let e := blockCentralIdempotent R k hS
  let C := CornerAlgebra R e
  let q := cornerMk R e
  let F := ModuleCat.restrictScalars.{u} q
  letI : RingHomSurjective q := ⟨cornerMk_surjective R e⟩
  letI : IsSemisimpleRing C :=
    RingHom.isSemisimpleRing_of_surjective q (cornerMk_surjective R e)
  have h_isotypic : IsIsotypic C C := by
    intro I hI J hJ
    let XI : ModuleCat.{u} C := ModuleCat.of C I
    let XJ : ModuleCat.{u} C := ModuleCat.of C J
    have hRI : IsSimpleModule R (F.obj XI) := by
      rw [(restrictScalarsSemilinear q XI).isSimpleModule_iff_of_bijective
        Function.bijective_id]
      exact hI
    have hRJ : IsSimpleModule R (F.obj XJ) := by
      rw [(restrictScalarsSemilinear q XJ).isSimpleModule_iff_of_bijective
        Function.bijective_id]
      exact hJ
    have hXI : Etingof.InBlock R S (F.obj XI) := inBlock_restrictScalars R k hS XI
    have hXJ : Etingof.InBlock R S (F.obj XJ) := inBlock_restrictScalars R k hS XJ
    have hlinkedI : Etingof.AreLinked R (F.obj XI) S :=
      hXI (F.obj XI) (Etingof.isCompositionFactor_self hRI)
    have hlinkedJ : Etingof.AreLinked R (F.obj XJ) S :=
      hXJ (F.obj XJ) (Etingof.isCompositionFactor_self hRJ)
    have hlinkedJI : Etingof.AreLinked R (F.obj XJ) (F.obj XI) :=
      (Etingof.areLinked_equivalence R).trans hlinkedJ
        ((Etingof.areLinked_equivalence R).symm hlinkedI)
    obtain ⟨isoR⟩ :=
      (Etingof.semisimple_areLinked_iff_iso R (F.obj XJ) (F.obj XI) hRJ hRI).mp hlinkedJI
    letI : F.Full := restrictScalars_full_of_surjective q (cornerMk_surjective R e)
    haveI : F.Faithful := inferInstance
    exact ⟨(F.preimageIso isoR).toLinearEquiv⟩
  exact (isSimpleRing_isArtinianRing_iff.mpr
    ⟨inferInstance, h_isotypic, inferInstance⟩).1

/-- The intermediate corner form of Example 9.5.2(i). Artin--Wedderburn identifies the
simple block corner with a matrix algebra over k, so matrix Morita equivalence identifies its
module category with k-vector spaces. -/
noncomputable def semisimpleCornerEquivalence [IsAlgClosed k] [IsSemisimpleRing R] :
    ModuleCat.{u} k ≌
      ModuleCat.{u} (CornerAlgebra R (blockCentralIdempotent R k hS)) := by
  let e := blockCentralIdempotent R k hS
  let C := CornerAlgebra R e
  letI : IsSemisimpleRing C :=
    RingHom.isSemisimpleRing_of_surjective (cornerMk R e) (cornerMk_surjective R e)
  letI : IsSimpleRing C := corner_isSimpleRing_of_isSemisimpleRing R k hS
  have hW : Nonempty
      {n : ℕ // NeZero n ∧ Nonempty (C ≃ₐ[k] Matrix (Fin n) (Fin n) k)} := by
    obtain ⟨n, hn, hφ⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k C
    exact ⟨⟨n, hn, hφ⟩⟩
  let W := Classical.choice hW
  letI : NeZero W.1 := W.2.1
  let φ := W.2.2.some
  exact (ModuleCat.matrixEquivalence k (0 : Fin W.1)).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv φ.toRingEquiv)

/-- Etingof Example 9.5.2(i), full categorical form. Let R be a finite-dimensional
semisimple algebra over an algebraically closed field k, and let S be a simple R-module.
Then the entire block category of S is equivalent to the category of k-vector spaces.

This is an equivalence of all module categories, not merely a statement about their simple
objects. -/
noncomputable def semisimpleBlockEquivalence [IsAlgClosed k] [IsSemisimpleRing R] :
    ModuleCat.{u} k ≌ BlockCat R S :=
  (semisimpleCornerEquivalence R k hS).trans (blockEquivalence R k hS)

/-- The finite-dimensional k-vector spaces, expressed using the finite-length convention of
the Chapter 9 categorical development. -/
abbrev FiniteVecCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} k => IsFiniteLength k (M : Type u))

/-- The finite-length (equivalently, under the book hypotheses, finite-dimensional) objects of
the block of S. -/
abbrev FiniteBlockCat : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{u} R =>
      Etingof.InBlock R S M ∧ IsFiniteLength R (M : Type u))

/-- Etingof Example 9.5.2(i), book-faithful finite form. The category of finite-dimensional
k-vector spaces is equivalent to the finite-dimensional block of S.

This is the formal restriction of semisimpleBlockEquivalence: equivalences of module categories
preserve finite generation, and over the Artinian rings here finite generation is equivalent to
finite length. -/
noncomputable def semisimpleBlockEquivalenceFin [IsAlgClosed k] [IsSemisimpleRing R] :
    FiniteVecCat k ≌ FiniteBlockCat R (S := S) := by
  let e := blockCentralIdempotent R k hS
  let C := CornerAlgebra R e
  letI : IsSemisimpleRing C :=
    RingHom.isSemisimpleRing_of_surjective (cornerMk R e) (cornerMk_surjective R e)
  let E : ModuleCat.{u} k ≌ ModuleCat.{u} C := semisimpleCornerEquivalence R k hS
  let Q : ObjectProperty (ModuleCat.{u} C) :=
    fun N => IsFiniteLength C (N : Type u)
  let P : ObjectProperty (ModuleCat.{u} k) :=
    fun M => IsFiniteLength k (M : Type u)
  letI : Q.IsClosedUnderIsomorphisms :=
    ⟨fun iso h => iso.toLinearEquiv.isFiniteLength h⟩
  have hobj : Q.inverseImage E.functor = P := by
    funext M
    apply propext
    exact ((IsArtinianRing.tfae C (E.functor.obj M)).out 0 3).symm.trans
      ((finite_functor_iff E M).trans ((IsArtinianRing.tfae k M).out 0 3))
  exact (E.congrFullSubcategory hobj).trans (blockEquivalenceFin R k hS)

end Problem953

end Etingof
