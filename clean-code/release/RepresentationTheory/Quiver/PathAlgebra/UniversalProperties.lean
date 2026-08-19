/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import RepresentationTheory.Quiver.AuxiliaryPathStructures
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.Quiver.PathAlgebra.UniversalProperties

variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

/-- The element of the path algebra associated with a quiver vertex. -/
noncomputable def vertex (i : Q) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q :=
  _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
    (k := k) ⟨i, i, Quiver.Path.nil⟩

/-- The element of the path algebra associated with a quiver arrow. -/
noncomputable def arrow {i j : Q} (e : i ⟶ j) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q :=
  _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
    (k := k) ⟨i, j, e.toPath⟩

/-- The path-algebra element of a path extended by an arrow is the original path element multiplied by the arrow element. -/
theorem pathElement_cons {a b c : Q} (q : Quiver.Path a b) (e : b ⟶ c) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
        (k := k)
        (⟨a, c, q.cons e⟩ :
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) =
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
          (k := k)
          (⟨a, b, q⟩ :
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) *
        arrow k Q e := by
  unfold arrow _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    one_mul, one_smul,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_of_composable,
    Quiver.Path.comp_toPath_eq_cons]

/-- The vertex and arrow elements generate the entire path algebra. -/
theorem vertexArrow_adjoin_eq_top [Fintype Q] :
    Algebra.adjoin k
      ({ x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q |
          ∃ i, x = vertex k Q i } ∪
        { x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q |
          ∃ (i j : Q) (e : i ⟶ j), x = arrow k Q e }) = ⊤ := by
  have hgen : ∀ (a b : Q) (p : Quiver.Path a b),
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
          (k := k)
          (⟨a, b, p⟩ :
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) ∈
        Algebra.adjoin k
          ({ x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q |
              ∃ i, x = vertex k Q i } ∪
            { x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q |
              ∃ (i j : Q) (e : i ⟶ j), x = arrow k Q e }) := by
    intro a b p
    induction p with
    | nil => exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
    | cons q e ih =>
      rw [pathElement_cons]
      exact mul_mem ih (Algebra.subset_adjoin (Or.inr ⟨_, _, e, rfl⟩))
  rw [Algebra.eq_top_iff]
  intro f
  induction f using
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single x c =>
    obtain ⟨a, b, p⟩ := x
    have hsc :
        (Finsupp.single
            (⟨a, b, p⟩ :
              _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) c :
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) =
          c •
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
              (k := k)
              (⟨a, b, p⟩ :
                _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) := by
      exact
        (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.smul_single_one
          c _).symm
    rw [hsc]
    exact Subalgebra.smul_mem _ (hgen a b p) c

/-- For a finite quiver, the sum of all vertex elements in the path algebra is one. -/
theorem sum_vertex_eq_one [Fintype Q] :
    ∑ i, vertex k Q i = 1 := by
  simp only [vertex]
  exact
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.sum_vertexPath_eq_one
      k Q

/-- Every vertex element in the path algebra is idempotent. -/
theorem vertex_mul_self [Fintype Q] (i : Q) :
    vertex k Q i * vertex k Q i = vertex k Q i := by
  unfold vertex _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_vertexPath,
    if_pos rfl, mul_one, one_smul]

/-- Distinct vertex elements in the path algebra multiply to zero. -/
theorem vertex_mul_vertex_of_ne [Fintype Q] (i j : Q) (h : i ≠ j) :
    vertex k Q i * vertex k Q j = 0 := by
  unfold vertex _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_vertexPath,
    if_neg h]
  exact _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.smul_zero _

/-- The source vertex element multiplied on the left by an arrow element leaves the arrow unchanged. -/
theorem sourceVertex_mul_arrow [Fintype Q] {i j : Q} (e : i ⟶ j) :
    vertex k Q i * arrow k Q e = arrow k Q e := by
  unfold vertex arrow
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_vertexPath,
    if_pos rfl, mul_one, one_smul]

/-- A vertex element different from the source multiplied on the left by an arrow element is zero. -/
theorem vertex_mul_arrow_of_ne_source [Fintype Q] {i j : Q} (l : Q) (e : i ⟶ j)
    (h : l ≠ i) :
    vertex k Q l * arrow k Q e = 0 := by
  unfold vertex arrow
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_vertexPath,
    if_neg h]
  exact _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.smul_zero _

/-- An arrow element multiplied on the right by its target vertex element is unchanged. -/
theorem arrow_mul_targetVertex [Fintype Q] {i j : Q} (e : i ⟶ j) :
    arrow k Q e * vertex k Q j = arrow k Q e := by
  unfold arrow vertex
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_pathVertex,
    if_pos rfl, mul_one, one_smul]

/-- An arrow element multiplied on the right by a different vertex element is zero. -/
theorem arrow_mul_vertex_of_ne_target [Fintype Q] {i j : Q} (l : Q) (e : i ⟶ j)
    (h : l ≠ j) :
    arrow k Q e * vertex k Q l = 0 := by
  unfold arrow vertex
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_pathVertex,
    if_neg h.symm]
  exact _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.smul_zero _

/-- The element of the opposite path algebra associated with a quiver vertex. -/
noncomputable def oppositeVertex (i : Q) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q :=
  _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryVertexElement
    (k := k) (Q := Q) i

/-- The element of the opposite path algebra associated with a quiver arrow. -/
noncomputable def oppositeArrow {i j : Q} (e : i ⟶ j) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q :=
  _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElementOfPath
    (k := k) ⟨i, j, e.toPath⟩

/-- The opposite-algebra element of a path extended by an arrow is the arrow element multiplied by the element of the original path. -/
theorem oppositePathElement_cons {a b c : Q} (q : Quiver.Path a b) (e : b ⟶ c) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElementOfPath
        (k := k)
        (⟨a, c, q.cons e⟩ :
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) =
      oppositeArrow k Q e *
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElementOfPath
          (k := k)
          (⟨a, b, q⟩ :
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) := by
  rw [oppositeArrow,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement,
    Quiver.Path.comp_toPath_eq_cons]

/-- The opposite vertex and arrow elements generate the entire displayed algebra. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem oppositeVertexArrow_adjoin_eq_top [Fintype Q] :
    Algebra.adjoin k
      ({ x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q |
          ∃ i, x = oppositeVertex k Q i } ∪
        { x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q |
          ∃ (i j : Q) (e : i ⟶ j), x = oppositeArrow k Q e }) = ⊤ := by
  let S : Set
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q) :=
    { x | ∃ i, x = oppositeVertex k Q i } ∪
      { x | ∃ (i j : Q) (e : i ⟶ j), x = oppositeArrow k Q e }
  have hgen : ∀ (a b : Q) (p : Quiver.Path a b),
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElementOfPath
          (k := k)
          (⟨a, b, p⟩ :
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) ∈
        Algebra.adjoin k S := by
    intro a b p
    induction p with
    | nil =>
        exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)
    | cons q e ih =>
        rw [oppositePathElement_cons]
        exact mul_mem (Algebra.subset_adjoin (Or.inr ⟨_, _, e, rfl⟩)) ih
  change Algebra.adjoin k S = ⊤
  rw [Algebra.eq_top_iff]
  intro x
  rw [← MulOpposite.op_unop x]
  induction x.unop using
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
  | zero => simp
  | add f g hf hg =>
      rw [MulOpposite.op_add]
      exact add_mem hf hg
  | single y c =>
      obtain ⟨a, b, p⟩ := y
      have hsc : MulOpposite.op
          (Finsupp.single
              (⟨a, b, p⟩ :
                _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) c :
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) =
          c •
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElementOfPath
              (k := k)
              (⟨a, b, p⟩ :
                _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) := by
        apply MulOpposite.unop_injective
        exact
          (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.smul_single_one
            c
            (⟨a, b, p⟩ :
              _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q)).symm
      have hmem : c •
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElementOfPath
              (k := k)
              (⟨a, b, p⟩ :
                _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) ∈
            Algebra.adjoin k S :=
        Subalgebra.smul_mem _ (hgen a b p) c
      exact hsc.symm ▸ hmem

/-- For a finite quiver, the sum of all opposite vertex elements is one. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem sum_oppositeVertex_eq_one [Fintype Q] :
    ∑ i, oppositeVertex k Q i = 1 := by
  exact
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.sum_auxiliaryVertexElement_eq_one

/-- Every opposite vertex element is idempotent. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem oppositeVertex_mul_self [Fintype Q] (i : Q) :
    oppositeVertex k Q i * oppositeVertex k Q i = oppositeVertex k Q i := by
  rw [oppositeVertex,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryVertexElement,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement,
    Quiver.Path.nil_comp]

/-- Distinct opposite vertex elements multiply to zero. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem oppositeVertex_mul_oppositeVertex_of_ne [Fintype Q] (i j : Q) (h : i ≠ j) :
    oppositeVertex k Q i * oppositeVertex k Q j = 0 := by
  exact
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement_eq_zero
      Quiver.Path.nil Quiver.Path.nil h.symm

/-- An opposite arrow element multiplied on the right by its source vertex element is unchanged. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem oppositeArrow_mul_sourceVertex [Fintype Q] {i j : Q} (e : i ⟶ j) :
    oppositeArrow k Q e * oppositeVertex k Q i = oppositeArrow k Q e := by
  rw [oppositeArrow, oppositeVertex,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryVertexElement,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement,
    Quiver.Path.nil_comp]

/-- An opposite arrow element multiplied on the right by a different vertex element is zero. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem oppositeArrow_mul_vertex_of_ne_source [Fintype Q] {i j : Q} (l : Q)
    (e : i ⟶ j) (h : l ≠ i) :
    oppositeArrow k Q e * oppositeVertex k Q l = 0 := by
  exact
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement_eq_zero
      Quiver.Path.nil e.toPath h

/-- The target vertex element multiplied on the left by an opposite arrow element leaves the arrow unchanged. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem targetVertex_mul_oppositeArrow [Fintype Q] {i j : Q} (e : i ⟶ j) :
    oppositeVertex k Q j * oppositeArrow k Q e = oppositeArrow k Q e := by
  rw [oppositeVertex,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryVertexElement,
    oppositeArrow,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement,
    Quiver.Path.comp_nil]

/-- A vertex element different from the target multiplied on the left by an opposite arrow element is zero. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem vertex_mul_oppositeArrow_of_ne_target [Fintype Q] {i j : Q} (l : Q)
    (e : i ⟶ j) (h : l ≠ j) :
    oppositeVertex k Q l * oppositeArrow k Q e = 0 := by
  exact
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.auxiliaryElement_mul_auxiliaryElement_eq_zero
      e.toPath Quiver.Path.nil h.symm

section Universal

variable {k Q}
variable {B : Type*} [Ring B] [Algebra k B] (P : Q → B) (A : ∀ i j : Q, (i ⟶ j) → B)

/-- The value in a ring assigned to a quiver path from chosen vertex and arrow values. -/
def pathEvaluation {a : Q} : {b : Q} → Quiver.Path a b → B
  | _, Quiver.Path.nil => P a
  | _, Quiver.Path.cons q e => pathEvaluation q * A _ _ e

omit [DecidableEq Q] in
/-- The evaluation of the empty path at a vertex is the chosen value of that vertex. -/
@[simp] theorem pathEvaluation_nil (a : Q) :
    pathEvaluation P A (Quiver.Path.nil : Quiver.Path a a) = P a := rfl

omit [DecidableEq Q] in
/-- The evaluation of a path extended by an arrow is the evaluation of the original path multiplied by the chosen arrow value. -/
@[simp] theorem pathEvaluation_cons {a b c : Q} (q : Quiver.Path a b) (e : b ⟶ c) :
    pathEvaluation P A (q.cons e) = pathEvaluation P A q * A b c e := rfl

/-- The base-linear map from the path algebra determined by chosen vertex and arrow values. -/
noncomputable def pathLinearMap :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q →ₗ[k] B :=
  Finsupp.linearCombination k
    (fun x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q =>
      pathEvaluation P A x.2.2)

/-- The path-linear map sends a scalar multiple of a single path to that scalar times the chosen evaluation of the path. -/
theorem pathLinearMap_single
    (x : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) (c : k) :
    pathLinearMap P A (Finsupp.single x c) = c • pathEvaluation P A x.2.2 :=
  Finsupp.linearCombination_single (R := k) c x

end Universal

/-- Compatible orthogonal vertex idempotents and arrow elements determine a unique algebra homomorphism from the path algebra. -/
theorem existsUnique_pathAlgebraHom [Fintype Q]
    (B : Type*) [Ring B] [Algebra k B]
    (P : Q → B) (A : ∀ i j : Q, (i ⟶ j) → B)
    (hsum : ∑ i, P i = 1)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (hsa : ∀ i j (e : i ⟶ j), P i * A i j e = A i j e)
    (_hsa0 : ∀ (l : Q) i j (e : i ⟶ j), l ≠ i → P l * A i j e = 0)
    (hat : ∀ i j (e : i ⟶ j), A i j e * P j = A i j e)
    (_hat0 : ∀ (l : Q) i j (e : i ⟶ j), l ≠ j → A i j e * P l = 0) :
    ∃! φ :
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q →ₐ[k] B,
      (∀ i, φ (vertex k Q i) = P i) ∧
        (∀ i j (e : i ⟶ j), φ (arrow k Q e) = A i j e) := by
  have hsrc : ∀ {a b : Q} (p : Quiver.Path a b),
      P a * pathEvaluation P A p = pathEvaluation P A p := by
    intro a b p
    induction p with
    | nil => rw [pathEvaluation_nil]; exact hidem a
    | cons q e ih => rw [pathEvaluation_cons, ← mul_assoc, ih]
  have htgt : ∀ {a b : Q} (p : Quiver.Path a b),
      pathEvaluation P A p * P b = pathEvaluation P A p := by
    intro a b p
    induction p with
    | nil => rw [pathEvaluation_nil]; exact hidem a
    | cons q e ih => rw [pathEvaluation_cons, mul_assoc, hat]
  have hcomp : ∀ {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c),
      pathEvaluation P A (p.comp q) = pathEvaluation P A p * pathEvaluation P A q := by
    intro a b c p q
    induction q with
    | nil => rw [Quiver.Path.comp_nil, pathEvaluation_nil, htgt]
    | cons r e ih =>
      rw [Quiver.Path.comp_cons, pathEvaluation_cons, pathEvaluation_cons, ih, mul_assoc]
  have h1 : pathLinearMap P A
      (1 : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) = 1 := by
    rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.one_eq_sum_ofPath_vertexPath,
      map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
    simp [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath,
      pathLinearMap_single]
  have hmul : ∀ x y :
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q,
      pathLinearMap P A (x * y) = pathLinearMap P A x * pathLinearMap P A y := by
    intro x y
    induction x using
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | add x1 x2 hx1 hx2 => rw [add_mul, map_add, map_add, add_mul, hx1, hx2]
    | single sx a =>
      induction y using
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | add y1 y2 hy1 hy2 => rw [mul_add, map_add, map_add, mul_add, hy1, hy2]
      | single sy b =>
        obtain ⟨xa, xb, xp⟩ := sx
        obtain ⟨ya, yb, yq⟩ := sy
        rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single]
        by_cases hxy : xb = ya
        · subst hxy
          rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_of_composable]
          simp only [map_smul, pathLinearMap_single, one_smul]
          rw [hcomp, smul_mul_assoc, mul_smul_comm, smul_smul]
        · rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_of_not_composable
            _ _ hxy, smul_zero, map_zero]
          simp only [pathLinearMap_single]
          rw [smul_mul_assoc, mul_smul_comm]
          have horthxy : pathEvaluation P A xp * pathEvaluation P A yq = 0 := by
            conv_lhs => rw [← htgt xp, ← hsrc yq]
            rw [mul_assoc, ← mul_assoc (P xb), horth xb ya hxy, zero_mul, mul_zero]
          rw [horthxy, smul_zero, smul_zero]
  let φ : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q →ₐ[k] B :=
    AlgHom.ofLinearMap (pathLinearMap P A) h1 hmul
  have hφapp : ∀ z, φ z = pathLinearMap P A z := fun _ => rfl
  have hφvertex : ∀ i, φ (vertex k Q i) = P i := by
    intro i
    rw [hφapp, vertex,
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath,
      pathLinearMap_single]
    simp
  have hφarrow : ∀ i j (e : i ⟶ j), φ (arrow k Q e) = A i j e := by
    intro i j e
    rw [hφapp, arrow,
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath,
      pathLinearMap_single, one_smul]
    exact hsa i j e
  refine ⟨φ, ⟨hφvertex, hφarrow⟩, ?_⟩
  intro ψ hψ
  apply AlgHom.ext
  intro z
  induction z using
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | single x c =>
    obtain ⟨a, b, p⟩ := x
    have hsc :
        (Finsupp.single
            (⟨a, b, p⟩ :
              _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) c :
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) =
          c •
            _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
              (k := k)
              (⟨a, b, p⟩ :
                _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType Q) := by
      exact
        (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.smul_single_one
          c _).symm
    rw [hsc, map_smul, map_smul]
    congr 1
    clear hsc
    induction p with
    | nil => exact (hψ.1 a).trans (hφvertex a).symm
    | cons q e ih =>
      rw [pathElement_cons, map_mul, map_mul, ih, hψ.2 _ _ e, hφarrow _ _ e]

/-- Compatible orthogonal vertex idempotents and oppositely oriented arrow elements determine a unique algebra homomorphism from the opposite path algebra. -/
@[source_ref "Chapter2/Problem2.8.6" (role := primary)]
theorem existsUnique_oppositePathAlgebraHom [Fintype Q]
    (B : Type*) [Ring B] [Algebra k B]
    (P : Q → B) (A : ∀ i j : Q, (i ⟶ j) → B)
    (hsum : ∑ i, P i = 1)
    (hidem : ∀ i, P i * P i = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0)
    (has : ∀ i j (e : i ⟶ j), A i j e * P i = A i j e)
    (has0 : ∀ (l : Q) i j (e : i ⟶ j), l ≠ i → A i j e * P l = 0)
    (hta : ∀ i j (e : i ⟶ j), P j * A i j e = A i j e)
    (hta0 : ∀ (l : Q) i j (e : i ⟶ j), l ≠ j → P l * A i j e = 0) :
    ∃! φ :
        _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q →ₐ[k] B,
      (∀ i, φ (oppositeVertex k Q i) = P i) ∧
        (∀ i j (e : i ⟶ j), φ (oppositeArrow k Q e) = A i j e) := by
  let Pop : Q → Bᵐᵒᵖ := fun i => MulOpposite.op (P i)
  let Aop : ∀ i j : Q, (i ⟶ j) → Bᵐᵒᵖ :=
    fun i j e => MulOpposite.op (A i j e)
  have hsumOp : ∑ i, Pop i = 1 := by
    apply MulOpposite.unop_injective
    rw [show MulOpposite.unop (∑ i, Pop i) = ∑ i, MulOpposite.unop (Pop i) from
      map_sum MulOpposite.opAddEquiv.symm _ Finset.univ]
    simpa [Pop] using hsum
  have hidemOp : ∀ i, Pop i * Pop i = Pop i := by
    intro i
    apply MulOpposite.unop_injective
    simpa [Pop] using hidem i
  have horthOp : ∀ i j, i ≠ j → Pop i * Pop j = 0 := by
    intro i j hij
    apply MulOpposite.unop_injective
    simpa [Pop] using horth j i hij.symm
  have hsaOp : ∀ i j (e : i ⟶ j), Pop i * Aop i j e = Aop i j e := by
    intro i j e
    apply MulOpposite.unop_injective
    simpa [Pop, Aop] using has i j e
  have hsa0Op : ∀ (l : Q) i j (e : i ⟶ j), l ≠ i → Pop l * Aop i j e = 0 := by
    intro l i j e hli
    apply MulOpposite.unop_injective
    simpa [Pop, Aop] using has0 l i j e hli
  have hatOp : ∀ i j (e : i ⟶ j), Aop i j e * Pop j = Aop i j e := by
    intro i j e
    apply MulOpposite.unop_injective
    simpa [Pop, Aop] using hta i j e
  have hat0Op : ∀ (l : Q) i j (e : i ⟶ j), l ≠ j → Aop i j e * Pop l = 0 := by
    intro l i j e hlj
    apply MulOpposite.unop_injective
    simpa [Pop, Aop] using hta0 l i j e hlj
  obtain ⟨ψ, hψ, huniq⟩ :=
    _root_.RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.existsUnique_pathAlgebraHom
      k Q Bᵐᵒᵖ Pop Aop hsumOp hidemOp horthOp hsaOp hsa0Op hatOp hat0Op
  let φ :
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType k Q →ₐ[k] B :=
    AlgHom.opComm ψ
  have hφvertex : ∀ i, φ (oppositeVertex k Q i) = P i := by
    intro i
    change MulOpposite.unop
        (ψ (_root_.RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.vertex k Q i)) =
      P i
    rw [hψ.1 i]
    rfl
  have hφarrow : ∀ i j (e : i ⟶ j), φ (oppositeArrow k Q e) = A i j e := by
    intro i j e
    change MulOpposite.unop
        (ψ (_root_.RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.arrow k Q e)) =
      A i j e
    rw [hψ.2 i j e]
    rfl
  refine ⟨φ, ⟨hφvertex, hφarrow⟩, ?_⟩
  intro χ hχ
  let χop :
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q →ₐ[k] Bᵐᵒᵖ :=
    AlgHom.opComm.symm χ
  have hχopVertex : ∀ i,
      χop (_root_.RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.vertex k Q i) =
        Pop i := by
    intro i
    change MulOpposite.op (χ (oppositeVertex k Q i)) = MulOpposite.op (P i)
    rw [hχ.1 i]
  have hχopArrow : ∀ i j (e : i ⟶ j),
      χop (_root_.RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.arrow k Q e) =
        Aop i j e := by
    intro i j e
    change MulOpposite.op (χ (oppositeArrow k Q e)) = MulOpposite.op (A i j e)
    rw [hχ.2 i j e]
  have hop : χop = ψ := huniq χop ⟨hχopVertex, hχopArrow⟩
  apply AlgHom.opComm.symm.injective
  simpa [χop, φ] using hop

end RepresentationTheory.Quiver.PathAlgebra.UniversalProperties

attribute [nolint defsWithUnderscore]
  RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.vertex
  RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.arrow
  RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.oppositeVertex
  RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.oppositeArrow
  RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.pathEvaluation
  RepresentationTheory.Quiver.PathAlgebra.UniversalProperties.pathLinearMap
