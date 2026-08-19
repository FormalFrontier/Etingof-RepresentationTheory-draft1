/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Module.Projective
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finite.Sigma
import Mathlib.LinearAlgebra.Dimension.Constructions
import RepresentationTheory.Quiver.AuxiliaryPathStructures
import RepresentationTheory.Quiver.PathAlgebra.UniversalProperties

import RepresentationTheory.ModuleFamilyNatMatrix
import RepresentationTheory.Auxiliary.RingData
import RepresentationTheory.ModuleTensorPresentation
import RepresentationTheory.QuiverAuxiliary
import RepresentationTheory.RingPredicateBounds
import RepresentationTheory.Algebra.Homological.EquivalenceInvariance
import RepresentationTheory.Algebra.Homological.AuxiliaryDimensionTransfer
import RepresentationTheory.Quiver.PathAlgebra.VertexComponents
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Loop quivers and associated algebras

Path finiteness, associated algebras of loop quivers, and a natural-number matrix for quivers.
-/

universe u

open CategoryTheory Limits

namespace RepresentationTheory.Quiver.PathAlgebra.LoopQuiver

section AcyclicFinite

variable {V : Type*} [Quiver V]

/-- A list of vertices associated with a quiver path. -/
def pathVertexList {a : V} : ∀ {b : V}, Quiver.Path a b → List V
  | _, .nil => [a]
  | b, .cons p _ => pathVertexList p ++ [b]

/-- The list associated with a path has length one more than the path length. -/
@[simp] lemma pathVertexList_length {a : V} :
    ∀ {b : V} (p : Quiver.Path a b), (pathVertexList p).length = p.length + 1
  | _, .nil => rfl
  | _, .cons p _ => by
      simp [pathVertexList, Quiver.Path.length_cons, pathVertexList_length p]

/-- Membership in the list associated with a path yields a factorization of that path as a composite. -/
lemma exists_eq_comp_of_mem_pathVertexList {a : V} :
    ∀ {b : V} (p : Quiver.Path a b) {c : V}, c ∈ pathVertexList p →
      ∃ (q : Quiver.Path a c) (r : Quiver.Path c b), p = q.comp r
  | _, .nil, c, hc => by
      rw [pathVertexList, List.mem_singleton] at hc
      subst hc
      exact ⟨.nil, .nil, rfl⟩
  | _, .cons p e, c, hc => by
      rw [pathVertexList, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · obtain ⟨q, r, rfl⟩ := exists_eq_comp_of_mem_pathVertexList p hc
        exact ⟨q, r.cons e, by rw [Quiver.Path.comp_cons]⟩
      · exact ⟨.cons p e, .nil, (Quiver.Path.comp_nil _).symm⟩

/-- When all closed paths are trivial, the list associated with any path has no repeated entries. -/
lemma pathVertexList_nodup_of_no_nontrivial_cycles {a : V}
    (hacyclic : ∀ (v : V) (q : Quiver.Path v v), q = Quiver.Path.nil) :
    ∀ {b : V} (p : Quiver.Path a b), (pathVertexList p).Nodup
  | _, .nil => List.nodup_singleton a
  | b, .cons p e => by
      have hbnotin : b ∉ pathVertexList p := by
        intro hx
        obtain ⟨_, r, _⟩ := exists_eq_comp_of_mem_pathVertexList p hx
        have hloop := hacyclic b (r.cons e)
        have hlen : (r.cons e).length = 0 := by rw [hloop]; rfl
        rw [Quiver.Path.length_cons] at hlen
        exact absurd hlen (Nat.succ_ne_zero _)
      rw [pathVertexList]
      refine (pathVertexList_nodup_of_no_nontrivial_cycles hacyclic p).append
        (List.nodup_singleton b) ?_
      rw [List.disjoint_iff_ne]
      intro x hx c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact fun heq => hbnotin (heq ▸ hx)

/-- In a finite quiver without nontrivial closed paths, every path has length strictly less than the number of vertices. -/
lemma path_length_lt_card_of_no_nontrivial_cycles [Fintype V]
    (hacyclic : ∀ (v : V) (q : Quiver.Path v v), q = Quiver.Path.nil)
    {a b : V} (p : Quiver.Path a b) : p.length < Fintype.card V := by
  have hle := (pathVertexList_nodup_of_no_nontrivial_cycles hacyclic p).length_le_card
  rw [pathVertexList_length] at hle
  omega

private def pathSuccEquiv (a b : V) (n : ℕ) :
    {p : Quiver.Path a b // p.length = n + 1} ≃
      Σ c : V, {p : Quiver.Path a c // p.length = n} × (c ⟶ b) where
  toFun := fun ⟨p, h⟩ => by
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => exact ⟨_, ⟨p', by rw [Quiver.Path.length_cons] at h; omega⟩, e⟩
  invFun x := ⟨x.2.1.1.cons x.2.2, by rw [Quiver.Path.length_cons, x.2.1.2]⟩
  left_inv := fun ⟨p, h⟩ => by
    cases p with
    | nil => simp [Quiver.Path.length_nil] at h
    | cons p' e => rfl
  right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl

/-- In a quiver with finite vertices and arrows, the paths of fixed endpoints and fixed length form a finite type. -/
lemma finite_paths_of_fixed_length [Finite V] [∀ i j : V, Finite (i ⟶ j)] (a : V) :
    ∀ (n : ℕ) (b : V), Finite {p : Quiver.Path a b // p.length = n} := by
  intro n
  induction n with
  | zero =>
    intro b
    haveI : Subsingleton {p : Quiver.Path a b // p.length = 0} := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨p, hp⟩ := x
      obtain ⟨q, hq⟩ := y
      have hab : a = b := Quiver.Path.eq_of_length_zero p hp
      subst hab
      rw [Subtype.mk_eq_mk, Quiver.Path.eq_nil_of_length_zero p hp,
        Quiver.Path.eq_nil_of_length_zero q hq]
    exact Finite.of_injective (fun _ => (0 : Fin 1)) fun x y _ => Subsingleton.elim x y
  | succ n ih =>
    intro b
    haveI : ∀ c : V, Finite {p : Quiver.Path a c // p.length = n} := ih
    exact Finite.of_equiv _ (pathSuccEquiv a b n).symm

/-- A finite quiver with finite arrow sets and no nontrivial closed paths has finitely many paths between any two vertices. -/
lemma finite_paths_between_of_no_nontrivial_cycles [Finite V] [∀ i j : V, Finite (i ⟶ j)]
    (hacyclic : ∀ (v : V) (q : Quiver.Path v v), q = Quiver.Path.nil)
    (a b : V) : Finite (Quiver.Path a b) := by
  haveI := Fintype.ofFinite V
  haveI : ∀ (m : ℕ) (c : V), Finite {p : Quiver.Path a c // p.length = m} :=
    fun m c => finite_paths_of_fixed_length a m c
  refine Finite.of_injective
    (fun p : Quiver.Path a b =>
      (⟨⟨p.length, path_length_lt_card_of_no_nontrivial_cycles hacyclic p⟩, p, rfl⟩ :
        Σ n : Fin (Fintype.card V), {p : Quiver.Path a b // p.length = (n : ℕ)})) ?_
  intro p q h
  exact congrArg
    (fun x : Σ n : Fin (Fintype.card V), {p : Quiver.Path a b // p.length = (n : ℕ)} => x.2.1) h

end AcyclicFinite

/-- The displayed condition holds at index one for the associated algebra of a finite quiver. -/
@[source_ref "Chapter9/Problem9.4.6" (role := supporting)]
theorem quiverAssociatedAlgebra_condition_at_one
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q] :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) 1 := by
  intro M
  have hSES :=
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryShortComplex_shortExact M
  haveI hP1 : Projective
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryShortComplex M).X₁ :=
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.projective_obj
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.functionModuleObject M)
  haveI hP2 : Projective
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryShortComplex M).X₂ :=
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.projective_obj
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.secondaryFunctionModuleObject M)
  exact hSES.hasProjectiveDimensionLT_X₃ 1
    (projective_iff_hasProjectiveDimensionLT_one.mp hP1)
    (hasProjectiveDimensionLT_of_ge _ 1 2 (by omega))

/-- For the associated algebra of a finite quiver with an arrow, the displayed associated value is one. -/
@[source_ref "Chapter9/Problem9.4.6" (role := primary)]
theorem quiverAssociatedAlgebra_associatedValue_eq_one_of_exists_arrow
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hQ : ∃ a b : Q, Nonempty (a ⟶ b)) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) = 1 :=
  RepresentationTheory.RingPredicateBounds.eq_one_of_predicate_one_and_not_predicate_zero
    quiverAssociatedAlgebra_condition_at_one
    (RepresentationTheory.QuiverAuxiliary.not_auxiliary_zero_of_exists_hom hQ)

/-- A family of types indexed by natural numbers. -/
def LoopQuiver (n : ℕ) : Type u := PUnit.{u + 1}

/-- Each type in the indexed family is finite. -/
instance loopQuiverFintype (n : ℕ) : Fintype (LoopQuiver.{u} n) :=
  inferInstanceAs (Fintype PUnit)

instance (n : ℕ) : DecidableEq (LoopQuiver.{u} n) := inferInstanceAs (DecidableEq PUnit)

/-- Each type in the indexed family has exactly one element. -/
instance loopQuiverUnique (n : ℕ) : Unique (LoopQuiver.{u} n) := inferInstanceAs (Unique PUnit)

/-- A quiver structure on each type in the indexed family. -/
instance loopQuiverQuiver (n : ℕ) : Quiver.{u + 1} (LoopQuiver.{u} n) :=
  ⟨fun _ _ => ULift.{u + 1} (Fin n)⟩

/-- The selected element in the type associated with a natural number. -/
abbrev LoopQuiver.vertex (n : ℕ) : LoopQuiver.{u} n := PUnit.unit

open RepresentationTheory.Quiver.PathAlgebra.UniversalProperties

/-- The loop arrow selected by an index at the canonical vertex of a loop quiver. -/
def loopQuiverArrow (n : ℕ) (m : Fin n) : (LoopQuiver.vertex n ⟶ LoopQuiver.vertex n) :=
  ULift.up m

/-- An algebra homomorphism from a free algebra on a finite type to the displayed associated algebra. -/
noncomputable def freeAlgebraToLoopQuiverAssociatedAlgebra (k : Type u) [Field k] (n : ℕ) :
    FreeAlgebra k (Fin n) →ₐ[k]
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k (LoopQuiver.{u} n) :=
  FreeAlgebra.lift k fun m =>
    arrow k (LoopQuiver n) (i := LoopQuiver.vertex n) (j := LoopQuiver.vertex n)
      (loopQuiverArrow n m)

/-- The homomorphism to the associated algebra sends a generator to the displayed term indexed by the corresponding arrow. -/
theorem freeAlgebraToLoopQuiverAssociatedAlgebra_apply_generator
    (k : Type u) [Field k] (n : ℕ) (m : Fin n) :
    freeAlgebraToLoopQuiverAssociatedAlgebra k n (FreeAlgebra.ι k m) =
      arrow k (LoopQuiver n) (i := LoopQuiver.vertex n) (j := LoopQuiver.vertex n)
        (loopQuiverArrow n m) := by
  unfold freeAlgebraToLoopQuiverAssociatedAlgebra
  rw [FreeAlgebra.lift_ι_apply]

/-- There is a unique displayed map satisfying the stated values on vertex and arrow expressions. -/
theorem existsUnique_associatedAlgebraToFreeAlgebra (k : Type u) [Field k] (n : ℕ) :
    ∃! φ : _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
        k (LoopQuiver.{u} n) →ₐ[k] FreeAlgebra k (Fin n),
      (∀ i, φ (vertex k (LoopQuiver n) i) = (1 : FreeAlgebra k (Fin n))) ∧
        (∀ (i j : LoopQuiver n) (e : i ⟶ j),
          φ (arrow k (LoopQuiver n) e) = FreeAlgebra.ι k (ULift.down e)) :=
  existsUnique_pathAlgebraHom k (LoopQuiver n) (FreeAlgebra k (Fin n)) (fun _ => 1)
    (fun _ _ e => FreeAlgebra.ι k (ULift.down e))
    (by rw [Fintype.sum_unique])
    (fun _ => one_mul 1)
    (fun i j h => absurd (Subsingleton.elim i j) h)
    (fun _ _ _ => one_mul _)
    (fun l i _ _ h => absurd (Subsingleton.elim l i) h)
    (fun _ _ _ => mul_one _)
    (fun l _ j _ h => absurd (Subsingleton.elim l j) h)

/-- An algebra homomorphism from the displayed associated algebra to a free algebra on a finite type. -/
noncomputable def loopQuiverAssociatedAlgebraToFreeAlgebra (k : Type u) [Field k] (n : ℕ) :
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
      k (LoopQuiver.{u} n) →ₐ[k] FreeAlgebra k (Fin n) :=
  (existsUnique_associatedAlgebraToFreeAlgebra k n).choose

/-- The homomorphism from the associated algebra sends each displayed vertex expression to one. -/
theorem loopQuiverAssociatedAlgebraToFreeAlgebra_apply_vertex
    (k : Type u) [Field k] (n : ℕ) (i : LoopQuiver.{u} n) :
    loopQuiverAssociatedAlgebraToFreeAlgebra k n (vertex k (LoopQuiver n) i) = 1 :=
  (existsUnique_associatedAlgebraToFreeAlgebra k n).choose_spec.1.1 i

/-- The homomorphism from the associated algebra sends the displayed arrow expression to its indexed free generator. -/
theorem loopQuiverAssociatedAlgebraToFreeAlgebra_apply_arrow
    (k : Type u) [Field k] (n : ℕ) {i j : LoopQuiver.{u} n} (e : i ⟶ j) :
    loopQuiverAssociatedAlgebraToFreeAlgebra k n (arrow k (LoopQuiver n) e) =
      FreeAlgebra.ι k (ULift.down e) :=
  (existsUnique_associatedAlgebraToFreeAlgebra k n).choose_spec.1.2 i j e

/-- The displayed expression associated with a vertex of the indexed quiver is equal to one. -/
theorem loopQuiver_vertexExpression_eq_one
    (k : Type u) [Field k] (n : ℕ) (a : LoopQuiver.{u} n) :
    vertex k (LoopQuiver n) a = 1 := by
  have ha : a = (default : LoopQuiver n) := Subsingleton.elim _ _
  subst ha
  rw [← Fintype.sum_unique (vertex k (LoopQuiver n))]
  exact sum_vertex_eq_one k (LoopQuiver n)

/-- The stated composite fixes the displayed expression associated with each arrow. -/
theorem freeAlgebraToAssociatedAlgebra_comp_associatedAlgebraToFreeAlgebra_apply_arrow
    (k : Type u) [Field k] (n : ℕ) {i j : LoopQuiver.{u} n} (e : i ⟶ j) :
    freeAlgebraToLoopQuiverAssociatedAlgebra k n
        (loopQuiverAssociatedAlgebraToFreeAlgebra k n (arrow k (LoopQuiver n) e)) =
      arrow k (LoopQuiver n) e := by
  obtain rfl : i = LoopQuiver.vertex n := Subsingleton.elim _ _
  obtain rfl : j = LoopQuiver.vertex n := Subsingleton.elim _ _
  rw [loopQuiverAssociatedAlgebraToFreeAlgebra_apply_arrow,
    freeAlgebraToLoopQuiverAssociatedAlgebra_apply_generator]
  rfl

/-- The stated composite fixes the displayed expression associated with each path. -/
theorem freeAlgebraToAssociatedAlgebra_comp_associatedAlgebraToFreeAlgebra_apply_path
    (k : Type u) [Field k] (n : ℕ) {a b : LoopQuiver.{u} n} (p : Quiver.Path a b) :
    freeAlgebraToLoopQuiverAssociatedAlgebra k n
        (loopQuiverAssociatedAlgebraToFreeAlgebra k n
          (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
            (k := k) ⟨a, b, p⟩)) =
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
        (k := k) ⟨a, b, p⟩ := by
  induction p with
  | nil =>
    change freeAlgebraToLoopQuiverAssociatedAlgebra k n
        (loopQuiverAssociatedAlgebraToFreeAlgebra k n (vertex k (LoopQuiver n) a)) =
      vertex k (LoopQuiver n) a
    rw [loopQuiverAssociatedAlgebraToFreeAlgebra_apply_vertex, map_one,
      loopQuiver_vertexExpression_eq_one]
  | cons q e ih =>
    rw [pathElement_cons, map_mul, map_mul, ih,
      freeAlgebraToAssociatedAlgebra_comp_associatedAlgebraToFreeAlgebra_apply_arrow]

/-- The stated composite from the associated algebra through the free algebra is the identity. -/
theorem freeAlgebraToAssociatedAlgebra_comp_associatedAlgebraToFreeAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    (freeAlgebraToLoopQuiverAssociatedAlgebra k n).comp
        (loopQuiverAssociatedAlgebraToFreeAlgebra k n) =
      AlgHom.id k
        (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k (LoopQuiver.{u} n)) := by
  ext f
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single s c =>
    obtain ⟨a, b, p⟩ := s
    have hsc :
        (Finsupp.single
            (⟨a, b, p⟩ :
              _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType (LoopQuiver n)) c :
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k (LoopQuiver n)) =
        c •
          _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
            (k := k)
            (⟨a, b, p⟩ :
              _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType (LoopQuiver n)) := by
      rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath,
        Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsc, map_smul, map_smul,
      freeAlgebraToAssociatedAlgebra_comp_associatedAlgebraToFreeAlgebra_apply_path]

/-- The stated composite from the free algebra through the associated algebra is the identity. -/
theorem associatedAlgebraToFreeAlgebra_comp_freeAlgebraToAssociatedAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    (loopQuiverAssociatedAlgebraToFreeAlgebra k n).comp
        (freeAlgebraToLoopQuiverAssociatedAlgebra k n) =
      AlgHom.id k (FreeAlgebra k (Fin n)) := by
  apply FreeAlgebra.hom_ext
  funext i
  change loopQuiverAssociatedAlgebraToFreeAlgebra k n
      (freeAlgebraToLoopQuiverAssociatedAlgebra k n (FreeAlgebra.ι k i)) = FreeAlgebra.ι k i
  rw [freeAlgebraToLoopQuiverAssociatedAlgebra_apply_generator,
    loopQuiverAssociatedAlgebraToFreeAlgebra_apply_arrow]
  rfl

/-- An algebra equivalence from a free algebra on a finite type to the displayed algebra associated with the indexed type. -/
@[source_ref "Chapter9/Problem9.4.6" (role := supporting)]
noncomputable def freeAlgebraEquivLoopQuiverAssociatedAlgebra
    (k : Type u) [Field k] (n : ℕ) :
    FreeAlgebra k (Fin n) ≃ₐ[k]
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k (LoopQuiver.{u} n) :=
  AlgEquiv.ofAlgHom (freeAlgebraToLoopQuiverAssociatedAlgebra k n)
    (loopQuiverAssociatedAlgebraToFreeAlgebra k n)
    (freeAlgebraToAssociatedAlgebra_comp_associatedAlgebraToFreeAlgebra k n)
    (associatedAlgebraToFreeAlgebra_comp_freeAlgebraToAssociatedAlgebra k n)

/-- The algebra homomorphism from a finitely generated free algebra to its scalar field that sends every generator to zero. -/
noncomputable def freeAlgebraAugmentation
    (k : Type u) [Field k] (n : ℕ) : FreeAlgebra k (Fin n) →ₐ[k] k :=
  FreeAlgebra.lift k fun _ => (0 : k)

/-- The free-algebra augmentation vanishes on each canonical generator. -/
@[simp] theorem freeAlgebraAugmentation_apply_generator
    (k : Type u) [Field k] (n : ℕ) (i : Fin n) :
    freeAlgebraAugmentation k n (FreeAlgebra.ι k i) = 0 := by
  rw [freeAlgebraAugmentation, FreeAlgebra.lift_ι_apply]

/-- For a free algebra on a nonempty finite type, the displayed condition does not hold at index zero. -/
theorem freeAlgebra_not_condition_at_zero
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    ¬ RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
      (FreeAlgebra k (Fin n)) 0 := by
  intro hall
  letI aug : Module (FreeAlgebra k (Fin n)) k :=
    Module.compHom k (freeAlgebraAugmentation k n).toRingHom
  have smul_def : ∀ (a : FreeAlgebra k (Fin n)) (v : k),
      a • v = freeAlgebraAugmentation k n a * v := fun _ _ => rfl
  let MA := ModuleCat.of (FreeAlgebra k (Fin n)) k
  have hpd : CategoryTheory.HasProjectiveDimensionLE MA 0 := hall MA
  haveI hproj : CategoryTheory.Projective MA :=
    projective_iff_hasProjectiveDimensionLT_one.mpr hpd
  haveI hmod : Module.Projective (FreeAlgebra k (Fin n)) k :=
    (IsProjective.iff_projective (R := FreeAlgebra k (Fin n)) k).mpr hproj
  let surj := LinearMap.toSpanSingleton (FreeAlgebra k (Fin n)) k (1 : k)
  have hsurj : Function.Surjective surj := by
    intro v
    refine ⟨algebraMap k (FreeAlgebra k (Fin n)) v, ?_⟩
    show surj (algebraMap k (FreeAlgebra k (Fin n)) v) = v
    rw [LinearMap.toSpanSingleton_apply, smul_def, mul_one, AlgHom.commutes]
    simp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property surj LinearMap.id hsurj
  set w : FreeAlgebra k (Fin n) := s (1 : k) with hw_def
  have hsection : freeAlgebraAugmentation k n w = 1 := by
    have hcf := LinearMap.congr_fun hs (1 : k)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hcf
    rw [LinearMap.toSpanSingleton_apply, smul_def, mul_one] at hcf
    exact hcf
  have hact : (FreeAlgebra.ι k ⟨0, hn⟩ : FreeAlgebra k (Fin n)) • (1 : k) = 0 := by
    rw [smul_def, freeAlgebraAugmentation_apply_generator, zero_mul]
  have hzero : (FreeAlgebra.ι k ⟨0, hn⟩ : FreeAlgebra k (Fin n)) * w = 0 := by
    have h1 := s.map_smul (FreeAlgebra.ι k ⟨0, hn⟩) (1 : k)
    rw [hact, map_zero] at h1
    rw [← smul_eq_mul]; exact h1.symm
  have hw0 : w = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (FreeAlgebra.ι_ne_zero (⟨0, hn⟩ : Fin n))
    · exact h
  rw [hw0, map_zero] at hsection
  exact one_ne_zero hsection.symm

/-- For a free algebra on a nonempty finite type, the displayed associated value is one. -/
@[source_ref "Chapter9/Problem9.4.6" (role := primary)]
theorem freeAlgebra_associatedValue_eq_one
    {k : Type u} [Field k] {n : ℕ} (hn : 1 ≤ n) :
    RepresentationTheory.Auxiliary.RingData.auxiliaryRingENatInvariant
      (FreeAlgebra k (Fin n)) = 1 := by
  have hQ : ∃ a b : LoopQuiver.{u} n, Nonempty (a ⟶ b) :=
    ⟨LoopQuiver.vertex n, LoopQuiver.vertex n, ⟨loopQuiverArrow n ⟨0, hn⟩⟩⟩
  let eRing : ULift.{u + 1} (FreeAlgebra k (Fin n)) ≃+*
      _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
        k (LoopQuiver.{u} n) :=
    (ULift.ringEquiv).trans (freeAlgebraEquivLoopQuiverAssociatedAlgebra k n).toRingEquiv
  have h1 : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
      (FreeAlgebra k (Fin n)) 1 := by
    have hbig : RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
        (ULift.{u + 1} (FreeAlgebra k (Fin n))) 1 := by
      rw [RepresentationTheory.Algebra.Homological.EquivalenceInvariance.ringProperty_iff_of_ringEquiv
        eRing]
      exact quiverAssociatedAlgebra_condition_at_one
    exact
      RepresentationTheory.Algebra.Homological.AuxiliaryDimensionTransfer.auxiliary_ulift_down hbig
  have h0 : ¬ RepresentationTheory.Auxiliary.RingData.auxiliaryRingNatProperty
      (FreeAlgebra k (Fin n)) 0 := freeAlgebra_not_condition_at_zero hn
  exact RepresentationTheory.RingPredicateBounds.eq_one_of_predicate_one_and_not_predicate_zero
    h1 h0

/-- A natural-number matrix associated with a quiver. -/
noncomputable def quiverNatMatrix (Q : Type u) [Quiver Q] : Matrix Q Q ℕ :=
  Matrix.of fun i j => Nat.card (Quiver.Path i j)

/-- Under the stated path-indexed linear-equivalence hypothesis, an associated matrix equals the quiver natural-number matrix. -/
@[source_ref "Chapter9/Problem9.4.6" (role := primary)]
theorem associatedMatrix_eq_quiverNatMatrix_of_pathIndexedLinearEquiv
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hacyclic : ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil)
    [∀ i j : Q, Finite (i ⟶ j)]
    (P : Q → Type*) [∀ i, AddCommGroup (P i)]
    [∀ i, Module (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) (P i)]
    [∀ i, Module k (P i)]
    [∀ i, SMulCommClass
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) k (P i)]
    (hcover : ∀ i j : Q,
      Nonempty
        ((P i →ₗ[_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q] P j) ≃ₗ[k]
          (Quiver.Path i j →₀ k))) :
    RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix
        (k := k)
        (A := _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) P =
      quiverNatMatrix Q := by
  haveI : ∀ i j : Q, Finite (Quiver.Path i j) :=
    fun i j => finite_paths_between_of_no_nontrivial_cycles hacyclic i j
  ext i j
  obtain ⟨e⟩ := hcover i j
  have : Fintype (Quiver.Path i j) := Fintype.ofFinite _
  simp only [RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix,
    quiverNatMatrix, Matrix.of_apply]
  rw [e.finrank_eq, Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

/-- Under the stated finiteness and closed-path hypotheses, a specialized associated matrix equals the quiver natural-number matrix. -/
theorem specializedAssociatedMatrix_eq_quiverNatMatrix
    {k : Type u} [Field k] {Q : Type u} [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]
    (hacyclic : ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil)
    [∀ i j : Q, Finite (i ⟶ j)] :
    RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix
        (k := k)
        (A := _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q)
        (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.AuxiliaryVertexSpace
          k Q) =
      quiverNatMatrix Q :=
  associatedMatrix_eq_quiverNatMatrix_of_pathIndexedLinearEquiv hacyclic
    (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.AuxiliaryVertexSpace k Q)
    (fun i j =>
      ⟨_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.linearMapEquivPathFinsupp
        k Q i j⟩)

end RepresentationTheory.Quiver.PathAlgebra.LoopQuiver
