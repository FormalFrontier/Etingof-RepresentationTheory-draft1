/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.FunctionRingHom
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option backward.isDefEq.respectTransparency false
set_option linter.dupNamespace false

/-!
# Edge modules for path algebras

This module constructs the two commuting vertex-function actions on finitely supported edge
functions and relates them to multiplication in the path algebra.
-/

universe u

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-- The type of directed edges of a quiver. -/
abbrev Edge (Q : Type u) [Quiver.{u + 1} Q] := Σ (a : Q) (b : Q), (a ⟶ b)

namespace Edge

/-- Returns the source vertex of an edge. -/
def source (x : Edge Q) : Q := x.1

/-- Returns the target vertex of an edge. -/
def target (x : Edge Q) : Q := x.2.1

/-- Converts an edge to the corresponding path datum. -/
def toPath (x : Edge Q) : Quiver.BundledPath Q := ⟨x.1, x.2.1, x.2.2.toPath⟩

omit [DecidableEq Q] in
/-- The source of a constructed edge is its first vertex. -/
@[simp] theorem source_mk (a b : Q) (e : a ⟶ b) :
    Edge.source (⟨a, b, e⟩ : Edge Q) = a := rfl

omit [DecidableEq Q] in
/-- The target of a constructed edge is its second vertex. -/
@[simp] theorem target_mk (a b : Q) (e : a ⟶ b) :
    Edge.target (⟨a, b, e⟩ : Edge Q) = b := rfl

end Edge

/-- Maps an edge into the ambient algebra. -/
noncomputable def ofEdge (x : Edge Q) : Quiver.PathAlgebra k Q := ofPath x.toPath

/-- The linear map induced by sending each edge to its algebra element. -/
noncomputable def edgeLinearMap : (Edge Q →₀ k) →ₗ[k] Quiver.PathAlgebra k Q :=
  Finsupp.linearCombination k ofEdge

/-- The edge linear map sends a singleton to the corresponding scalar multiple. -/
@[simp] theorem edgeLinearMap_single (x : Edge Q) (c : k) :
    edgeLinearMap (Finsupp.single x c) = c • ofEdge (k := k) x := by
  rw [edgeLinearMap, Finsupp.linearCombination_single]

/-- Multiplication of two path elements agrees with their prescribed product. -/
theorem pathElement_mul_pathElement (p q : Quiver.BundledPath Q) :
    (ofPath p : Quiver.PathAlgebra k Q) * ofPath q = mulPath p q := by
  rw [ofPath, ofPath, single_mul_single, one_mul, one_smul]

variable (k Q) in
/-- Scales each edge coefficient by a function evaluated at its weight. -/
noncomputable def weightedScale (wt : Edge Q → Q) (s : Q → k) (v : Edge Q →₀ k) :
    Edge Q →₀ k :=
  Finsupp.ofSupportFinite (fun i => s (wt i) * v i)
    (v.support.finite_toSet.subset (by
      intro i hi
      simp only [Function.mem_support, Finset.mem_coe, Finsupp.mem_support_iff] at hi ⊢
      exact fun h => hi (by rw [h, mul_zero])))

omit [DecidableEq Q] in
/-- Weighted scaling acts on each coefficient by the corresponding scalar. -/
@[simp] theorem weightedScale_apply (wt : Edge Q → Q) (s : Q → k) (v : Edge Q →₀ k)
    (i : Edge Q) : weightedScale k Q wt s v i = s (wt i) * v i := by
  rw [weightedScale, Finsupp.ofSupportFinite_coe]

variable (k Q) in
/-- The module structure on edge functions induced by a vertex-valued weight. -/
@[reducible] noncomputable def weightedEdgeModule (wt : Edge Q → Q) :
    Module (Q → k) (Edge Q →₀ k) where
  smul := weightedScale k Q wt
  one_smul v := by
    change weightedScale k Q wt 1 v = v
    ext i; rw [weightedScale_apply, Pi.one_apply, one_mul]
  mul_smul s t v := by
    change weightedScale k Q wt (s * t) v =
      weightedScale k Q wt s (weightedScale k Q wt t v)
    ext i; simp only [weightedScale_apply, Pi.mul_apply]; ring
  smul_zero s := by
    change weightedScale k Q wt s 0 = 0
    ext i; simp
  smul_add s v w := by
    change weightedScale k Q wt s (v + w) =
      weightedScale k Q wt s v + weightedScale k Q wt s w
    ext i; simp only [weightedScale_apply, Finsupp.add_apply]; ring
  add_smul s t v := by
    change weightedScale k Q wt (s + t) v =
      weightedScale k Q wt s v + weightedScale k Q wt t v
    ext i; simp only [weightedScale_apply, Finsupp.add_apply, Pi.add_apply]; ring
  zero_smul v := by
    change weightedScale k Q wt 0 v = 0
    ext i; simp

variable (k Q) in
/-- The module structure on finitely supported edge functions. -/
@[reducible] noncomputable def edgeFinsuppModule : Module (Q → k) (Edge Q →₀ k) :=
  weightedEdgeModule k Q Edge.source

variable (k Q) in
/-- An alternative module structure on finitely supported edge functions. -/
@[reducible] noncomputable def edgeFinsuppModule' : Module (Q → k) (Edge Q →₀ k) :=
  weightedEdgeModule k Q Edge.target

omit [DecidableEq Q] in
/-- Scaling by source and target vertex functions commutes. -/
theorem source_target_scale_commute (s t : Q → k) (v : Edge Q →₀ k) :
    weightedScale k Q Edge.source s (weightedScale k Q Edge.target t v) =
      weightedScale k Q Edge.target t (weightedScale k Q Edge.source s v) := by
  ext i
  rw [weightedScale_apply, weightedScale_apply, weightedScale_apply, weightedScale_apply]
  ring

/-- Left multiplication by a vertex idempotent selects edges with that source. -/
theorem sourceIdempotent_mul (i : Q) (x : Edge Q) :
    (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q) *
        ofEdge x =
      if i = x.source then ofEdge x else 0 := by
  obtain ⟨a, b, e⟩ := x
  rw [ofEdge, Edge.toPath, pathElement_mul_pathElement, mulPath_vertexPath]
  rfl

/-- Right multiplication by a vertex idempotent selects edges with that target. -/
theorem mul_targetIdempotent (i : Q) (x : Edge Q) :
    ofEdge x *
        (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q) =
      if x.target = i then ofEdge x else 0 := by
  obtain ⟨a, b, e⟩ := x
  rw [ofEdge, Edge.toPath, pathElement_mul_pathElement, mulPath_pathVertex]
  rfl

variable [Fintype Q]

/-- Left multiplication by a vertex function scales an edge by its source value. -/
theorem vertexFunction_mul (s : Q → k) (x : Edge Q) :
    functionRingHom k Q s * ofEdge x = s x.source • ofEdge (k := k) x := by
  have hsingle : ∀ i : Q,
      (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) (s i) :
          Quiver.PathAlgebra k Q) =
        s i • (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)) := by
    intro i; rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [functionRingHom_apply, Finset.sum_congr rfl fun i _ => hsingle i, Finset.sum_mul]
  have hterm : ∀ i : Q,
      (s i • ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)) * ofEdge x =
        if i = x.source then s i • ofEdge (k := k) x else 0 := by
    intro i
    rw [smul_mul, sourceIdempotent_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ x.source,
    if_pos (Finset.mem_univ _)]

/-- Right multiplication by a vertex function scales an edge by its target value. -/
theorem mul_vertexFunction (s : Q → k) (x : Edge Q) :
    ofEdge x * functionRingHom k Q s = s x.target • ofEdge (k := k) x := by
  have hsingle : ∀ i : Q,
      (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) (s i) :
          Quiver.PathAlgebra k Q) =
        s i • (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)) := by
    intro i; rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [functionRingHom_apply, Finset.sum_congr rfl fun i _ => hsingle i, Finset.mul_sum]
  have hterm : ∀ i : Q,
      ofEdge x * (s i • ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)) =
        if x.target = i then s i • ofEdge (k := k) x else 0 := by
    intro i
    rw [mul_smul, mul_targetIdempotent]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq Finset.univ x.target,
    if_pos (Finset.mem_univ _)]

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
