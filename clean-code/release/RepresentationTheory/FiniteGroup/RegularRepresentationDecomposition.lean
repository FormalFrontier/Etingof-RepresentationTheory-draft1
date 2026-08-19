/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Alignment.Attribute
import RepresentationTheory.FDRep.GroupAlgebraDecomposition

set_option linter.dupNamespace false

open CategoryTheory

universe u

namespace RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition

/-- The group algebra of a finite group over a field is semisimple when the group order is a unit in the field. -/
@[source_ref "Chapter2/Discussion_after_Theorem2.1.2/Derived2" (role := supporting),
  source_ref "Chapter4/Discussion_after_Theorem4.6.3" (role := supporting),
  source_ref "Chapter4/Theorem4.1.1" (role := supporting),
  source_ref "Chapter4/Theorem4.2.1/Derived2" (role := supporting)]
theorem MonoidAlgebra.isSemisimpleRing_of_isUnit_card
    (k : Type*) (G : Type*) [Field k] [Group G] [Fintype G]
    (h : IsUnit (Fintype.card G : k)) :
    IsSemisimpleRing (MonoidAlgebra k G) := by
  haveI : NeZero (Nat.card G : k) := by
    rw [neZero_iff]
    rw [Fintype.card_eq_nat_card] at h
    exact h.ne_zero
  infer_instance

/-- For a finite group over an algebraically closed field in which the group order is nonzero, there is a finite family of positive natural numbers whose squares sum to the group order. -/
@[source_ref "Chapter4/Theorem4.1.1" (role := supporting)]
theorem FiniteGroup.exists_positive_dimensions_sum_sq_eq_card
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (d : Fin n → ℕ),
      (∀ i, NeZero (d i)) ∧ ∑ i, (d i) ^ 2 = Fintype.card G :=
  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  ⟨D.count, D.dimension, D.dimension_neZero, D.sum_dimension_sq_eq_card⟩

/-- There is a complete pairwise nonisomorphic family of simple finite-dimensional representations whose endomorphism algebras form an algebra equivalent to the group algebra, and whose squared dimensions sum to the group order. -/
@[source_ref "Chapter4/Proposition4.1.2/Derived2" (role := primary),
  source_ref "Chapter4/Theorem4.1.1" (role := primary)]
theorem FiniteGroup.exists_complete_simple_family_with_groupAlgebra_equiv
    (k : Type u) (G : Type u) [Field k] [IsAlgClosed k] [Group G] [Fintype G]
    [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      Nonempty (MonoidAlgebra k G ≃ₐ[k] Π i, Module.End k (V i)) ∧
      ∑ i, Module.finrank k (V i) ^ 2 = Fintype.card G :=
  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  ⟨D.count, D.representation, D.simple_representation, D.representation_index_eq_of_iso,
    D.exists_iso_representation_of_simple, ⟨D.groupAlgebraEquivRepresentationEnd⟩,
    D.sum_finrank_sq_eq_card_of_simple_pairwise D.representation D.simple_representation
      D.representation_index_eq_of_iso⟩

/-- The representation of a group on its group algebra by left multiplication. -/
noncomputable def MonoidAlgebra.leftRegularRepresentation (k G : Type u) [Field k] [Group G] :
    Representation k G (MonoidAlgebra k G) where
  toFun g := Algebra.lmul k (MonoidAlgebra k G) (MonoidAlgebra.of k G g)
  map_one' := by rw [map_one, map_one]
  map_mul' g h := by rw [map_mul, map_mul]

/-- The left regular action of g on a group-algebra element x is multiplication of x by the group-algebra element supported at g. -/
@[simp]
theorem MonoidAlgebra.leftRegularRepresentation_apply (k G : Type u) [Field k] [Group G]
    (g : G) (x : MonoidAlgebra k G) :
    MonoidAlgebra.leftRegularRepresentation k G g x = MonoidAlgebra.of k G g * x := rfl

/-- An auxiliary finite-dimensional representation constructed from a field and a finite group. -/
noncomputable def FiniteGroup.auxiliaryFDRep (k G : Type u) [Field k] [Group G] [Fintype G] :
    FDRep k G :=
  FDRep.of (MonoidAlgebra.leftRegularRepresentation k G)

end RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition

namespace RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData

variable {k G : Type u} [Field k] [IsAlgClosed k] [Group G] [Fintype G]
  [NeZero (Nat.card G : k)]

/-- The representation on the indexed family of endomorphism spaces of the displayed auxiliary representations. -/
noncomputable def endomorphismFamilyRepresentation (D : DecompositionData k G) :
    Representation k G (Π i, Module.End k (D.representation i)) where
  toFun g := Algebra.lmul k _ (D.groupAlgebraEquivRepresentationEnd (MonoidAlgebra.of k G g))
  map_one' := by rw [map_one, map_one, map_one]
  map_mul' g h := by rw [map_mul, map_mul, map_mul]

/-- Applying the displayed auxiliary map to the group-algebra element supported at g gives the action of g in each indexed component. -/
@[source_ref "Chapter4/Theorem4.1.1" (role := primary)]
theorem auxiliaryMap_apply_single (D : DecompositionData k G) (g : G) (i : Fin D.count) :
    D.groupAlgebraEquivRepresentationEnd (MonoidAlgebra.of k G g) i = (D.representation i).ρ g := by
  have hproj : (D.groupAlgebraEquivMatrix (MonoidAlgebra.of k G g)) i =
      D.matrixBlockHom i (MonoidAlgebra.of k G g) := rfl
  have : D.groupAlgebraEquivRepresentationEnd (MonoidAlgebra.of k G g) i =
      Matrix.toLinAlgEquiv' (D.matrixBlockHom i (MonoidAlgebra.of k G g)) := by
    rw [← hproj]; rfl
  rw [this]
  ext v
  rw [Matrix.toLinAlgEquiv'_apply]
  rfl

/-- The group action on an indexed endomorphism family is componentwise postcomposition by the corresponding representation map. -/
theorem endomorphismFamilyRepresentation_apply (D : DecompositionData k G) (g : G)
    (F : Π i, Module.End k (D.representation i)) (i : Fin D.count) :
    D.endomorphismFamilyRepresentation g F i = (D.representation i).ρ g ∘ₗ F i := by
  change (D.groupAlgebraEquivRepresentationEnd (MonoidAlgebra.of k G g) * F) i =
    (D.representation i).ρ g ∘ₗ F i
  rw [Pi.mul_apply, D.auxiliaryMap_apply_single g i]
  rfl

/-- The underlying linear map of the algebra equivalence intertwines the action on the group algebra with the action on the indexed endomorphism family. -/
theorem algebraEquiv_intertwines (D : DecompositionData k G) (g : G) :
    D.groupAlgebraEquivRepresentationEnd.toLinearEquiv.toLinearMap ∘ₗ
      (RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.MonoidAlgebra.leftRegularRepresentation k G) g =
      D.endomorphismFamilyRepresentation g ∘ₗ D.groupAlgebraEquivRepresentationEnd.toLinearEquiv.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  exact map_mul D.groupAlgebraEquivRepresentationEnd (MonoidAlgebra.of k G g) x

/-- A second auxiliary finite-dimensional representation associated with the data D. -/
noncomputable def auxiliaryFDRepPrime (D : DecompositionData k G) : FDRep k G :=
  FDRep.of D.endomorphismFamilyRepresentation

/-- An isomorphism from the auxiliary finite-dimensional representation constructed from k and G to the second auxiliary representation associated with D. -/
@[source_ref "Chapter4/Theorem4.1.1" (role := supporting)]
noncomputable def auxiliaryFDRepIsoAuxiliaryPrime (D : DecompositionData k G) :
    RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.auxiliaryFDRep k G ≅
      D.auxiliaryFDRepPrime :=
  Action.mkIso D.groupAlgebraEquivRepresentationEnd.toLinearEquiv.toFGModuleCatIso (fun g => by
    ext : 1
    exact D.algebraEquiv_intertwines g)

/-- A representation on a family of vectors indexed by an auxiliary finite index and a second finite index. -/
noncomputable def indexedVectorFamilyRepresentation (D : DecompositionData k G) :
    Representation k G (Π i, Fin (D.dimension i) → (D.representation i)) where
  toFun g := LinearMap.pi fun i =>
    (((D.representation i).ρ g).compLeft (Fin (D.dimension i))).comp (LinearMap.proj i)
  map_one' := by
    ext w i j
    simp [map_one]
  map_mul' g h := by
    ext w i j
    simp [map_mul]

/-- The indexed-vector-family action applies the group action of the representation in each component. -/
theorem indexedVectorFamilyRepresentation_apply (D : DecompositionData k G) (g : G)
    (w : Π i, Fin (D.dimension i) → (D.representation i)) (i : Fin D.count) (j : Fin (D.dimension i)) :
    D.indexedVectorFamilyRepresentation g w i j = (D.representation i).ρ g (w i j) := rfl

/-- An auxiliary finite-dimensional representation associated with the data D. -/
noncomputable def auxiliaryFDRep (D : DecompositionData k G) : FDRep k G :=
  FDRep.of D.indexedVectorFamilyRepresentation

/-- A linear equivalence from an indexed family of endomorphisms to a doubly indexed family of vectors. -/
noncomputable def endomorphismsEquivIndexedVectorFamily (D : DecompositionData k G) :
    (Π i, Module.End k (D.representation i)) ≃ₗ[k] (Π i, Fin (D.dimension i) → (D.representation i)) :=
  LinearEquiv.piCongrRight fun i =>
    ((Pi.basisFun k (Fin (D.dimension i))).constr (M' := (D.representation i)) k).symm

/-- Evaluating the displayed equivalence at indices i and j gives the i-th endomorphism applied to the j-th standard basis vector. -/
theorem endomorphismsEquivIndexedVectorFamily_apply (D : DecompositionData k G)
    (F : Π i, Module.End k (D.representation i)) (i : Fin D.count) (j : Fin (D.dimension i)) :
    D.endomorphismsEquivIndexedVectorFamily F i j = F i (Pi.basisFun k (Fin (D.dimension i)) j) := rfl

/-- The equivalence from indexed endomorphisms to an indexed vector family intertwines the displayed group actions. -/
theorem endomorphismsEquivIndexedVectorFamily_intertwines (D : DecompositionData k G) (g : G)
    (F : Π i, Module.End k (D.representation i)) :
    D.endomorphismsEquivIndexedVectorFamily (D.endomorphismFamilyRepresentation g F) =
      D.indexedVectorFamilyRepresentation g (D.endomorphismsEquivIndexedVectorFamily F) := by
  ext i j
  rw [indexedVectorFamilyRepresentation_apply, endomorphismsEquivIndexedVectorFamily_apply,
    endomorphismsEquivIndexedVectorFamily_apply, D.endomorphismFamilyRepresentation_apply]
  rfl

/-- An isomorphism between the two auxiliary finite-dimensional representations associated with D. -/
noncomputable def auxiliaryFDRepIso (D : DecompositionData k G) :
    D.auxiliaryFDRepPrime ≅ D.auxiliaryFDRep :=
  Action.mkIso D.endomorphismsEquivIndexedVectorFamily.toFGModuleCatIso (fun g => by
    ext F
    exact D.endomorphismsEquivIndexedVectorFamily_intertwines g F)

/-- An isomorphism from the auxiliary finite-dimensional representation constructed from k and G to the first auxiliary representation associated with D. -/
@[source_ref "Chapter4/Theorem4.1.1" (role := supporting)]
noncomputable def auxiliaryFDRepIsoAuxiliary (D : DecompositionData k G) :
    RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.auxiliaryFDRep k G ≅
      D.auxiliaryFDRep :=
  D.auxiliaryFDRepIsoAuxiliaryPrime ≪≫ D.auxiliaryFDRepIso

end RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData

namespace RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition

/-- There is a complete pairwise nonisomorphic family of simple representations such that the componentwise postcomposition action on their endomorphisms yields a representation isomorphic to the displayed auxiliary finite-dimensional representation. -/
@[source_ref "Chapter4/Theorem4.1.1" (role := supporting)]
theorem FiniteGroup.exists_complete_simple_family_endomorphismRepresentation (k G : Type u)
    [Field k] [IsAlgClosed k] [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G) (ρ_end : Representation k G (Π i, Module.End k (V i))),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      (∀ (g : G) (F : Π i, Module.End k (V i)) (i : Fin n), ρ_end g F i = (V i).ρ g ∘ₗ F i) ∧
      Nonempty (FiniteGroup.auxiliaryFDRep k G ≅ FDRep.of ρ_end) :=
  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  ⟨D.count, D.representation, D.endomorphismFamilyRepresentation, D.simple_representation,
    D.representation_index_eq_of_iso, D.exists_iso_representation_of_simple,
    D.endomorphismFamilyRepresentation_apply, ⟨D.auxiliaryFDRepIsoAuxiliaryPrime⟩⟩

/-- There is a complete pairwise nonisomorphic family of simple representations whose dimensions index a coordinatewise group action isomorphic to the displayed auxiliary finite-dimensional representation. -/
@[source_ref "Chapter4/Proposition4.1.2/Derived3" (role := supporting),
  source_ref "Chapter4/Theorem4.1.1" (role := primary)]
theorem FiniteGroup.exists_complete_simple_family_coordinateRepresentation (k G : Type u)
    [Field k] [IsAlgClosed k] [Group G] [Fintype G] [NeZero (Nat.card G : k)] :
    ∃ (n : ℕ) (V : Fin n → FDRep k G) (d : Fin n → ℕ)
      (ρ_dec : Representation k G (Π i, Fin (d i) → (V i))),
      (∀ i, Simple (V i)) ∧
      (∀ i j, Nonempty (V i ≅ V j) → i = j) ∧
      (∀ W : FDRep k G, Simple W → ∃ i, Nonempty (W ≅ V i)) ∧
      (∀ i, d i = Module.finrank k (V i)) ∧
      (∀ (g : G) (w : Π i, Fin (d i) → (V i)) (i : Fin n) (j : Fin (d i)),
        ρ_dec g w i j = (V i).ρ g (w i j)) ∧
      Nonempty (FiniteGroup.auxiliaryFDRep k G ≅ FDRep.of ρ_dec) :=
  let D : RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData k G :=
    RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.default
  ⟨D.count, D.representation, D.dimension, D.indexedVectorFamilyRepresentation,
    D.simple_representation, D.representation_index_eq_of_iso,
    D.exists_iso_representation_of_simple, fun i => (D.finrank_representation i).symm,
    D.indexedVectorFamilyRepresentation_apply, ⟨D.auxiliaryFDRepIsoAuxiliary⟩⟩

end RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition
