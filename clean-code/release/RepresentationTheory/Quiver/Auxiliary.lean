/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
import RepresentationTheory.QuiverRepresentation.VertexCompositionSeries
import RepresentationTheory.Alignment.Attribute

/-!
# Auxiliary constructions for quiver representations
-/

namespace RepresentationTheory.Quiver.Auxiliary

open Module

variable {k Q : Type*} [Field k] [Quiver Q]

/-- The additive commutative group structure induced on a module over a field. -/
@[reducible]
noncomputable def addCommGroupOfModule {M : Type*} [inst : AddCommMonoid M] [Module k M] :
    AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup k

/-- Maps a vertex to an opaque value parameterized by a field and a quiver. -/
abbrev auxiliaryObjectAtVertex [DecidableEq Q] (i : Q) :
    RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q :=
  RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.representationAtVertex i

/-- The second auxiliary predicate on a vertex of a quiver. -/
def auxiliaryVertexPropertyTwo (i : Q) : Prop := ∀ j, IsEmpty (j ⟶ i)

/-- The first auxiliary predicate on a vertex of a quiver. -/
def auxiliaryVertexPropertyOne (i : Q) : Prop := ∀ j, IsEmpty (i ⟶ j)

/-- An auxiliary construction whose elaborated type is unavailable in this interface. -/
noncomputable def auxiliaryElidedDefinition
    (V W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) :
    (∀ i, V.obj i →ₗ[k] W.obj i) →
      (∀ p : (Σ i j, (i ⟶ j)), V.obj p.1 →ₗ[k] W.obj p.2.1) :=
  fun f p =>
    letI : AddCommGroup (W.obj p.2.1) := addCommGroupOfModule (k := k)
    W.map p.2.2 ∘ₗ f p.1 - f p.2.1 ∘ₗ V.map p.2.2

/-- A binary proposition on two opaque values parameterized by a field and a quiver. -/
def auxiliaryRelation
    (V W : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) : Prop :=
  Function.Surjective (auxiliaryElidedDefinition V W)

/-- At a vertex satisfying the second distinguished property, every linear object is related to its associated auxiliary object. -/
@[source_ref "Chapter6/Problem6.9.3" (role := primary)]
theorem any_relates_to_auxiliaryObjectAtVertex [DecidableEq Q]
    (i : Q) (hi : auxiliaryVertexPropertyTwo i)
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) :
    auxiliaryRelation V (auxiliaryObjectAtVertex i) := by
  intro g
  refine ⟨0, funext fun p => ?_⟩
  have hbne : p.2.1 ≠ i := by
    intro h
    exact (hi p.1).elim (h ▸ p.2.2)
  have hsub : Subsingleton ((auxiliaryObjectAtVertex (k := k) i).obj p.2.1) := by
    change Subsingleton (Fin (if p.2.1 = i then 1 else 0) → k)
    rw [if_neg hbne]
    exact ⟨fun a b => funext fun x => x.elim0⟩
  exact LinearMap.ext fun x => hsub.elim _ _

/-- At a vertex satisfying the first distinguished property, its associated auxiliary object is related to every linear object. -/
@[source_ref "Chapter6/Problem6.9.3" (role := primary)]
theorem auxiliaryObjectAtVertex_relates_to_any [DecidableEq Q]
    (i : Q) (hi : auxiliaryVertexPropertyOne i)
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q) :
    auxiliaryRelation (auxiliaryObjectAtVertex i) V := by
  intro g
  refine ⟨0, funext fun p => ?_⟩
  have hane : p.1 ≠ i := by
    intro h
    exact (hi p.2.1).elim (h ▸ p.2.2)
  have hsub : Subsingleton ((auxiliaryObjectAtVertex (k := k) i).obj p.1) := by
    change Subsingleton (Fin (if p.1 = i then 1 else 0) → k)
    rw [if_neg hane]
    exact ⟨fun a b => funext fun x => x.elim0⟩
  exact LinearMap.ext fun x => by rw [hsub.elim x 0, map_zero, map_zero]

/-- A natural-number-valued function on the vertices associated with an opaque value. -/
noncomputable def auxiliaryVertexValue
    (V : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    (i : Q) : ℕ :=
  finrank k (V.obj i)

/-- Under the displayed finite-basis hypothesis, the auxiliary value at a vertex equals the supplied natural number. -/
theorem auxiliaryVertexValue_eq_of_fin_basis
    {Vα : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q}
    {α : Q → ℕ} (basis : ∀ v, Basis (Fin (α v)) k (Vα.obj v)) (v : Q) :
    auxiliaryVertexValue Vα v = α v := by
  rw [auxiliaryVertexValue, Module.finrank_eq_card_basis (basis v), Fintype.card_fin]

/-- Under the displayed ordering and finite-basis hypotheses, there is auxiliary data satisfying the two stated equalities. -/
@[source_ref "Chapter6/Problem6.9.3" (role := primary),
  source_ref "Chapter6/Section6.9_heading" (role := supporting)]
theorem existsAuxiliaryDataWithVertexValues [DecidableEq Q]
    (Vα : RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram k Q)
    (n : ℕ) (order : Q ≃ Fin n)
    (horder : ∀ {v w : Q}, (v ⟶ w) → (order w : ℕ) < (order v : ℕ))
    (α : Q → ℕ) (basis : ∀ v, Basis (Fin (α v)) k (Vα.obj v)) :
    ∃ s : RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.VertexCompositionSeries Vα,
      s.length = ∑ l : Fin n, α (order.symm l) ∧
        ∀ i, s.multiplicity i = auxiliaryVertexValue Vα i := by
  obtain ⟨s, hlen, hmult⟩ :=
    RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.exists_vertexCompositionSeries_with_multiplicity
      Vα n order horder α basis
  exact ⟨s, hlen, fun i => (hmult i).trans
    (auxiliaryVertexValue_eq_of_fin_basis basis i).symm⟩

end RepresentationTheory.Quiver.Auxiliary
