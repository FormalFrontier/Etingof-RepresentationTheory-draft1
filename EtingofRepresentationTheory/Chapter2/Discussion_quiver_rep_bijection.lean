import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Projection

/-!
# Discussion: quiver representations vs. path-algebra modules

The discussion following Definition 2.8.4 in Etingof asserts that a representation of a
quiver `Q` is "the same thing" as a representation (module) of its path algebra `P_Q`, with
mutually inverse assignments `V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ`, giving a bijection between
isomorphism classes.

This file develops the algebraic foundation that both directions of that bijection rest on:
the trivial paths `pᵢ = ofPath ⟨i, i, nil⟩` form a family of **orthogonal idempotents**
summing (for a finite vertex set) to `1`, and they **absorb** an oriented path on the
correct side. Concretely, for an oriented path `a : x ⟶* y`,

* `pₓ · a = a` and `pₖ · a = 0` for `k ≠ x` (the source idempotent acts on the left), and
* `a · p_y = a` and `a · pₖ = 0` for `k ≠ y` (the target idempotent acts on the right).

These are precisely the relations that make `pᵢ V` the `i`-th vertex space and that pin down
which vertex space a single-arrow path maps out of and into.

## Convention / direction note

`Definition2_8_4` builds `P_Q` with Mathlib's **source-to-target** concatenation
(`comp x y` is defined when `target x = source y`, giving a path `source x ⟶* target y`).
This is the *opposite* of Etingof's body-text reading `ab = "first b then a"`; the two
conventions produce mutually opposite algebras. The absorption laws below are stated for the
source-to-target algebra actually constructed.

A consequence worth flagging for the full bijection (tracked in the
`Discussion_quiver_rep_bijection` work item): under this convention, for an arrow
`e : i ⟶ j` the basis element `aₑ = ofPath ⟨i, j, e.toPath⟩` satisfies `pᵢ · aₑ = aₑ` and
`aₑ · p_j = aₑ`, so in a *left* `P_Q`-module the operator `v ↦ aₑ • v` carries `p_j V` into
`pᵢ V`, i.e. it points `Vⱼ → Vᵢ`. Matching this against `Etingof.QuiverRepresentation` (where
an arrow `i ⟶ j` carries `Vᵢ → Vⱼ`) therefore requires either the opposite algebra, right
modules, or `Qᵒᵖ`; that modelling choice is left to the bijection construction itself.
-/

namespace Etingof.PathAlgebra

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The trivial path idempotent `pᵢ` at a vertex `i`: the basis element of `PathAlgebra k Q`
indexed by the empty (length-zero) path at `i`. -/
noncomputable def trivialPath (i : Q) : PathAlgebra k Q :=
  ofPath ⟨i, i, Quiver.Path.nil⟩

theorem trivialPath_def (i : Q) :
    (trivialPath i : PathAlgebra k Q) = Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1 :=
  rfl

/-- Left absorption: multiplying a basis path `a : x ⟶* y` on the left by the trivial path
`pᵢ` returns `a` when `i` is its source, and `0` otherwise. -/
theorem trivialPath_mul_ofPath (i a b : Q) (p : Quiver.Path a b) :
    (trivialPath i : PathAlgebra k Q) * ofPath ⟨a, b, p⟩
      = if i = a then ofPath ⟨a, b, p⟩ else 0 := by
  simp only [trivialPath, ofPath, single_mul_single, one_mul, one_smul, compSingle_nil_left]

/-- Right absorption: multiplying a basis path `a : x ⟶* y` on the right by the trivial path
`pᵢ` returns `a` when `i` is its target, and `0` otherwise. -/
theorem ofPath_mul_trivialPath (a b i : Q) (p : Quiver.Path a b) :
    (ofPath ⟨a, b, p⟩ : PathAlgebra k Q) * trivialPath i
      = if b = i then ofPath ⟨a, b, p⟩ else 0 := by
  simp only [trivialPath, ofPath, single_mul_single, mul_one, one_smul, compSingle_nil_right]

/-- The trivial paths are idempotents: `pᵢ · pᵢ = pᵢ`. -/
theorem trivialPath_mul_self (i : Q) :
    (trivialPath i : PathAlgebra k Q) * trivialPath i = trivialPath i := by
  have h := trivialPath_mul_ofPath (k := k) i i i Quiver.Path.nil
  rw [if_pos rfl] at h
  exact h

/-- The trivial paths are orthogonal: `pᵢ · pⱼ = 0` when `i ≠ j`. -/
theorem trivialPath_mul_of_ne {i j : Q} (h : i ≠ j) :
    (trivialPath i : PathAlgebra k Q) * trivialPath j = 0 := by
  have h2 := trivialPath_mul_ofPath (k := k) i j j Quiver.Path.nil
  rw [if_neg h] at h2
  exact h2

/-- Orthogonal-idempotent product law in one statement: `pᵢ · pⱼ = pᵢ` if `i = j`, else `0`. -/
theorem trivialPath_mul_trivialPath (i j : Q) :
    (trivialPath i : PathAlgebra k Q) * trivialPath j = if i = j then trivialPath i else 0 := by
  by_cases h : i = j
  · subst h; rw [trivialPath_mul_self, if_pos rfl]
  · rw [trivialPath_mul_of_ne h, if_neg h]

/-- The path-algebra basis element `aₑ = ofPath ⟨i, j, e.toPath⟩` of a single arrow `e : i ⟶ j`. -/
noncomputable def ofArrow {i j : Q} (e : i ⟶ j) : PathAlgebra k Q :=
  ofPath ⟨i, j, e.toPath⟩

/-- The source idempotent absorbs an arrow on the left: `pᵢ · aₑ = aₑ` for `e : i ⟶ j`. -/
theorem trivialPath_mul_ofArrow {i j : Q} (e : i ⟶ j) :
    (trivialPath i : PathAlgebra k Q) * ofArrow e = ofArrow e := by
  have h := trivialPath_mul_ofPath (k := k) i i j e.toPath
  rw [if_pos rfl] at h
  exact h

/-- The target idempotent absorbs an arrow on the right: `aₑ · p_j = aₑ` for `e : i ⟶ j`. -/
theorem ofArrow_mul_trivialPath {i j : Q} (e : i ⟶ j) :
    (ofArrow e : PathAlgebra k Q) * trivialPath j = ofArrow e := by
  have h := ofPath_mul_trivialPath (k := k) i j j e.toPath
  rw [if_pos rfl] at h
  exact h

/-- **Remark 2.8.5, restated.** For a finite vertex set, the trivial-path idempotents sum to the
unit: `∑ᵢ pᵢ = 1`. (Restatement of `sum_trivialPaths_eq_one` in terms of `trivialPath`.) -/
theorem sum_trivialPath [Fintype Q] : (∑ i, trivialPath i : PathAlgebra k Q) = 1 := by
  simp only [trivialPath]
  exact sum_trivialPaths_eq_one k Q

/-- The trivial-path idempotents `pᵢ` form a **complete family of orthogonal idempotents** in the
path algebra of a finite quiver: `pᵢ² = pᵢ`, `pᵢ pⱼ = 0` for `i ≠ j`, and `∑ᵢ pᵢ = 1`. This is the
algebraic input to the module-side decomposition `V = ⊕ᵢ pᵢ V` below. -/
theorem completeOrthogonalIdempotents_trivialPath [Fintype Q] :
    CompleteOrthogonalIdempotents (trivialPath (k := k) (Q := Q)) where
  idem i := trivialPath_mul_self i
  ortho := fun {_i _j} hij => trivialPath_mul_of_ne hij
  complete := sum_trivialPath

/-! ## Module side of the bijection: `V = ⊕ᵢ pᵢ V`

Fix a left module `V` over the path algebra of a finite quiver. The trivial-path idempotents act
on `V` as a complete family of orthogonal idempotent endomorphisms (`vertexProj`), whose ranges
are the vertex spaces `Vᵢ = pᵢ V` (`vertexSpace`). Completeness and orthogonality give the
internal direct-sum decomposition `V = ⊕ᵢ Vᵢ` (`isInternal_vertexSpace`).

This is exactly the underlying-module content of the assignment `V ↦ (pᵢ V)` of the discussion:
the decomposition `V ≅ ⊕ᵢ Vᵢ` is what makes `V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ` mutually inverse on
underlying modules. The vertex spaces inherit the arrow maps, and the full functor / iso-class
bijection, sit on top of this decomposition (see the convention note above for the modelling
choice the arrow maps force).
-/

section ModuleDecomposition

variable [Fintype Q] {V : Type*} [AddCommGroup V] [Module k V]
  [Module (PathAlgebra k Q) V] [IsScalarTower k (PathAlgebra k Q) V]

/-- The action of the path algebra on a left module `V`, packaged as a `k`-algebra homomorphism
into the endomorphism ring `Module.End k V` (left multiplication `a ↦ (a • ·)`). -/
noncomputable def moduleEnd : PathAlgebra k Q →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V

@[simp] theorem moduleEnd_apply (a : PathAlgebra k Q) (v : V) :
    (moduleEnd : PathAlgebra k Q →ₐ[k] Module.End k V) a v = a • v := rfl

/-- The vertex projection `pᵢ • -` acting on the module `V` (the action of the trivial-path
idempotent `pᵢ`). -/
noncomputable def vertexProj (i : Q) : Module.End k V :=
  (moduleEnd : PathAlgebra k Q →ₐ[k] Module.End k V) (trivialPath i)

theorem vertexProj_apply (i : Q) (v : V) :
    (vertexProj i : Module.End k V) v = (trivialPath i : PathAlgebra k Q) • v := rfl

/-- The vertex projections form a complete family of orthogonal idempotents in `End k V`: the
image of `completeOrthogonalIdempotents_trivialPath` under the action homomorphism. -/
theorem completeOrthogonalIdempotents_vertexProj :
    CompleteOrthogonalIdempotents (fun i : Q => (vertexProj i : Module.End k V)) :=
  completeOrthogonalIdempotents_trivialPath.map
    (f := (moduleEnd : PathAlgebra k Q →ₐ[k] Module.End k V).toRingHom)

/-- The `i`-th **vertex space** `Vᵢ = pᵢ V` of the module `V`, as a `k`-submodule (the range of
the vertex projection). -/
noncomputable def vertexSpace (i : Q) : Submodule k V :=
  LinearMap.range (vertexProj i : Module.End k V)

theorem vertexSpace_eq (i : Q) :
    (vertexSpace i : Submodule k V) = LinearMap.range (vertexProj i : Module.End k V) := rfl

theorem vertexProj_mem_vertexSpace (i : Q) (v : V) :
    (vertexProj i : Module.End k V) v ∈ (vertexSpace i : Submodule k V) :=
  LinearMap.mem_range_self _ v

/-- A vertex projection fixes its own vertex space pointwise (idempotency). -/
theorem vertexProj_eq_self_of_mem {i : Q} {x : V} (hx : x ∈ (vertexSpace i : Submodule k V)) :
    (vertexProj i : Module.End k V) x = x := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, (completeOrthogonalIdempotents_vertexProj.idem i).eq]

/-- **Module side of the quiver-representation / path-module bijection.** For a left module `V`
over the path algebra of a finite quiver, the vertex spaces `Vᵢ = pᵢ V` give an internal
direct-sum decomposition `V = ⊕ᵢ Vᵢ`. This is the underlying-module content witnessing that the
assignments `V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ` are mutually inverse. -/
theorem isInternal_vertexSpace :
    DirectSum.IsInternal (fun i : Q => (vertexSpace i : Submodule k V)) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- independence: `pᵢ` is the identity on `Vᵢ` and zero on every other `Vⱼ`
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hxsup
    have hker : (⨆ (j) (_ : j ≠ i), (vertexSpace j : Submodule k V))
        ≤ LinearMap.ker (vertexProj i : Module.End k V) := by
      refine iSup₂_le fun j hj => ?_
      rw [vertexSpace_eq, LinearMap.range_le_ker_iff]
      exact completeOrthogonalIdempotents_vertexProj.ortho hj.symm
    have h0 : (vertexProj i : Module.End k V) x = 0 := by
      rw [← LinearMap.mem_ker]; exact hker hxsup
    rw [← vertexProj_eq_self_of_mem hx, h0]
  · -- spanning: every `v = ∑ᵢ pᵢ v` with `pᵢ v ∈ Vᵢ`
    rw [eq_top_iff]
    intro v _
    have hsum : (∑ i : Q, (vertexProj i : Module.End k V)) v = v := by
      rw [completeOrthogonalIdempotents_vertexProj.complete, Module.End.one_apply]
    rw [← hsum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (vertexProj_mem_vertexSpace i v)

/-! ## Arrow maps and the forward functor `V ↦ (pᵢ V, aₑ ↾)`

For an arrow `e : i ⟶ j`, left multiplication by `aₑ = ofArrow e` carries `Vⱼ = pⱼ V` into
`Vᵢ = pᵢ V` (because `pᵢ · aₑ = aₑ`): it points `Vⱼ → Vᵢ`, the *opposite* direction to an arrow
`i ⟶ j` of `Etingof.QuiverRepresentation k Q` (which carries `Vᵢ → Vⱼ`).

This is the modelling decision flagged in the module docstring. We resolve it by assembling the
data into a representation of the **opposite quiver** `Qᵒᵖ`: an arrow `op j ⟶ op i` of `Qᵒᵖ`
(i.e. the opposite of `e : i ⟶ j`) carries `Vⱼ → Vᵢ`, exactly matching `arrowMap e`. So a left
`P_Q`-module `V` yields the quiver representation `forwardRep : QuiverRepresentation k Qᵒᵖ` with
vertex spaces `(Vᵢ)` and arrow maps the restricted left-multiplications. (Equivalently one could
use right modules or `(P_Q)ᵒᵖ`; the opposite quiver keeps everything on the left-module side.)
-/

/-- Left multiplication by an arrow element lands in the source vertex space:
`aₑ • x ∈ Vᵢ` for `e : i ⟶ j`, since `pᵢ · aₑ = aₑ`. (Holds for every `x : V`.) -/
theorem ofArrow_smul_mem {i j : Q} (e : i ⟶ j) (x : V) :
    (ofArrow e : PathAlgebra k Q) • x ∈ (vertexSpace i : Submodule k V) := by
  refine ⟨(ofArrow e : PathAlgebra k Q) • x, ?_⟩
  rw [vertexProj_apply, ← mul_smul, trivialPath_mul_ofArrow]

/-- **Forward arrow map.** For an arrow `e : i ⟶ j`, the restricted left-multiplication by
`aₑ = ofArrow e`, a `k`-linear map `Vⱼ → Vᵢ` between vertex spaces. Note the source-to-target
convention makes this point `Vⱼ → Vᵢ` (opposite to an `i ⟶ j` arrow of a `QuiverRepresentation`
of `Q`); see the opposite-quiver discussion above. -/
noncomputable def arrowMap {i j : Q} (e : i ⟶ j) :
    (vertexSpace j : Submodule k V) →ₗ[k] (vertexSpace i : Submodule k V) :=
  LinearMap.restrict (moduleEnd (ofArrow e)) (fun x _ => ofArrow_smul_mem e x)

@[simp] theorem arrowMap_coe_apply {i j : Q} (e : i ⟶ j) (x : (vertexSpace j : Submodule k V)) :
    (arrowMap e x : V) = (ofArrow e : PathAlgebra k Q) • (x : V) :=
  LinearMap.coe_restrict_apply _ _

/-- **Forward direction of the bijection.** A left `P_Q`-module `V` gives a representation of the
opposite quiver `Qᵒᵖ`: vertex spaces `Vᵢ = pᵢ V`, and for the opposite of an arrow `e : i ⟶ j`
the restricted left-multiplication `arrowMap e : Vⱼ → Vᵢ`. The opposite quiver is forced by the
source-to-target convention of `Definition2_8_4` (see the discussion above). -/
noncomputable def forwardRep : Etingof.QuiverRepresentation k Qᵒᵖ where
  obj X := (vertexSpace (V := V) X.unop : Submodule k V)
  mapLinear {_X _Y} f := arrowMap f.unop

@[simp] theorem forwardRep_obj (X : Qᵒᵖ) :
    (forwardRep (k := k) (Q := Q) (V := V)).obj X = (vertexSpace X.unop : Submodule k V) := rfl

@[simp] theorem forwardRep_mapLinear {X Y : Qᵒᵖ} (f : X ⟶ Y) :
    (forwardRep (k := k) (Q := Q) (V := V)).mapLinear f = arrowMap f.unop := rfl

end ModuleDecomposition

end Etingof.PathAlgebra
