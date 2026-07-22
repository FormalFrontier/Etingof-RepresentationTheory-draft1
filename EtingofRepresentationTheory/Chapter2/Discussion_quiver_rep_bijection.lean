import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter2.Definition2_8_10
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

variable [Fintype Q] {V : Type*} [AddCommMonoid V] [Module k V]
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

/-! ## Reverse direction: `R ↦ ⊕ᵢ R.obj (op i)` as a left `P_Q`-module

**Deliverable 3 of the bijection.** From a representation `R` of the opposite quiver `Qᵒᵖ` we
build a left `P_Q`-module on `M = ⊕ᵢ R.obj (op i)`. A path `p : a ⟶* b` of `Q` acts by the
composite of the arrow maps `R.mapLinear`, read **contravariantly**
(`pathMap (cons p e) = pathMap p ∘ R.mapLinear eᵒᵖ`), sending the `b`-summand to the `a`-summand
and zero on the other summands. The contravariant reading is exactly what turns the
source-to-target product `single⟨a,b,p⟩·single⟨b,d,q⟩ = single⟨a,d,p.comp q⟩` into composition
(`pathMap (p.comp q) = pathMap p ∘ pathMap q`), so the assignment is a genuine **left** action,
packaged as an algebra hom `toEnd : P_Q →ₐ[k] End k M`. This resolves the anti-homomorphism
subtlety flagged in the convention note: the opposite is absorbed into the contravariant
`pathMap`, not into the algebra or the side of the module.
-/

section ReverseDirection

/-- The vertex-space family `i ↦ R.obj (op i)` of a representation `R` of the opposite quiver. -/
abbrev reverseFam (R : Etingof.QuiverRepresentation k Qᵒᵖ) (i : Q) : Type _ :=
  R.obj (Opposite.op i)

/-- The composite arrow map of a path `p : a ⟶* b` of `Q`, a `k`-linear map
`R.obj (op b) → R.obj (op a)`. Defined **contravariantly**: `nil ↦ id` and
`cons p e ↦ pathMap p ∘ R.mapLinear eᵒᵖ`. This is the action of the basis element `single ⟨a,b,p⟩`
between the relevant vertex summands. -/
noncomputable def pathMap (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b : Q}
    (p : Quiver.Path a b) : reverseFam R b →ₗ[k] reverseFam R a :=
  Quiver.Path.rec (motive := fun b _ => reverseFam R b →ₗ[k] reverseFam R a)
    LinearMap.id (fun _ e ih => ih ∘ₗ R.mapLinear e.op) p

omit [DecidableEq Q] in
@[simp] theorem pathMap_nil (R : Etingof.QuiverRepresentation k Qᵒᵖ) (a : Q) :
    pathMap R (Quiver.Path.nil : Quiver.Path a a) = LinearMap.id := rfl

omit [DecidableEq Q] in
@[simp] theorem pathMap_cons (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b c : Q}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    pathMap R (p.cons e) = pathMap R p ∘ₗ R.mapLinear e.op := rfl

omit [DecidableEq Q] in
/-- **Path composition becomes endomorphism composition.** Because `pathMap` is contravariant,
the composite path `p.comp q` (source-to-target) acts as `pathMap p ∘ pathMap q`. This is the
identity that makes the path action a homomorphism rather than an anti-homomorphism. -/
theorem pathMap_comp (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b d : Q}
    (p : Quiver.Path a b) (q : Quiver.Path b d) :
    pathMap R (p.comp q) = pathMap R p ∘ₗ pathMap R q := by
  induction q with
  | nil => simp
  | cons q' e ih => simp only [Quiver.Path.comp_cons, pathMap_cons, ih, LinearMap.comp_assoc]

/-- The endomorphism of `M = ⊕ᵢ R.obj (op i)` attached to a basis path `⟨a,b,p⟩`: project to the
`b`-summand, apply `pathMap p`, inject into the `a`-summand. -/
noncomputable def pathEnd (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    Etingof.QuiverPathIndex Q → Module.End k (DirectSum Q (reverseFam R))
  | ⟨a, b, p⟩ =>
      DirectSum.lof k Q (reverseFam R) a ∘ₗ pathMap R p ∘ₗ DirectSum.component k Q (reverseFam R) b

theorem pathEnd_mk (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b : Q} (p : Quiver.Path a b) :
    pathEnd R ⟨a, b, p⟩ =
      DirectSum.lof k Q (reverseFam R) a ∘ₗ pathMap R p ∘ₗ
        DirectSum.component k Q (reverseFam R) b :=
  rfl

/-- On composable basis paths the endomorphisms compose: `aₚ · a_q = a_{p∘q}` for `p : a ⟶* b`,
`q : b ⟶* d`. The middle `component b ∘ lof b = id` cancels and `pathMap_comp` recombines. -/
theorem pathEnd_comp (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b d : Q}
    (p : Quiver.Path a b) (q : Quiver.Path b d) :
    pathEnd R ⟨a, b, p⟩ * pathEnd R ⟨b, d, q⟩ = pathEnd R ⟨a, d, p.comp q⟩ := by
  ext m
  simp only [Module.End.mul_apply, pathEnd_mk, LinearMap.comp_apply,
    DirectSum.component.lof_self, pathMap_comp]

/-- On non-composable basis paths the endomorphisms compose to `0`: the middle `component b ∘ lof c`
vanishes when `b ≠ c`. -/
theorem pathEnd_comp_zero (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b c d : Q}
    (p : Quiver.Path a b) (q : Quiver.Path c d) (h : b ≠ c) :
    pathEnd R ⟨a, b, p⟩ * pathEnd R ⟨c, d, q⟩ = 0 := by
  ext m
  simp only [Module.End.mul_apply, pathEnd_mk, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [DirectSum.component.of, dif_neg (Ne.symm h), map_zero, map_zero]

/-- The path action as a `k`-linear map `P_Q →ₗ End k M`: the `Finsupp`-extension of `pathEnd`. -/
noncomputable def toEndₗ (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    PathAlgebra k Q →ₗ[k] Module.End k (DirectSum Q (reverseFam R)) :=
  Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (pathEnd R x)

theorem toEndₗ_single (R : Etingof.QuiverRepresentation k Qᵒᵖ) (x : Etingof.QuiverPathIndex Q)
    (c : k) : toEndₗ R (Finsupp.single x c) = c • pathEnd R x := by
  simp only [toEndₗ, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq]

theorem toEndₗ_ofPath (R : Etingof.QuiverRepresentation k Qᵒᵖ) (x : Etingof.QuiverPathIndex Q) :
    toEndₗ R (ofPath x) = pathEnd R x := by
  rw [ofPath, toEndₗ_single, one_smul]

/-- `toEndₗ` sends a product of basis paths to the composition of their endomorphisms; both the
composable and non-composable cases are covered by `pathEnd_comp`/`pathEnd_comp_zero`. -/
theorem toEndₗ_compSingle (R : Etingof.QuiverRepresentation k Qᵒᵖ)
    (x y : Etingof.QuiverPathIndex Q) :
    toEndₗ R (compSingle x y) = pathEnd R x * pathEnd R y := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases h : b = c
  · subst h
    rw [compSingle_eq, toEndₗ_single, one_smul, pathEnd_comp]
  · rw [compSingle_eq_zero _ _ h, map_zero, pathEnd_comp_zero R p q h]

/-- `toEndₗ` is multiplicative: reduce to basis paths via bilinearity, then `toEndₗ_compSingle`. -/
theorem toEndₗ_mul (R : Etingof.QuiverRepresentation k Qᵒᵖ) (f g : PathAlgebra k Q) :
    toEndₗ R (f * g) = toEndₗ R f * toEndₗ R g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f1 f2 h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | single x a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g1 g2 h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | single y b =>
      rw [single_mul_single, map_smul, toEndₗ_compSingle, toEndₗ_single, toEndₗ_single,
        smul_mul_smul_comm]

/-- For a finite vertex set, the inclusions and projections of the direct sum sum to the identity:
`∑ᵢ lofᵢ ∘ componentᵢ = id`. This is the `∑ᵢ pᵢ = 1 ↦ id` content of the unit law. -/
theorem sum_lof_comp_component [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    (∑ i : Q, DirectSum.lof k Q (reverseFam R) i ∘ₗ DirectSum.component k Q (reverseFam R) i)
      = LinearMap.id := by
  refine LinearMap.ext fun m => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  conv_rhs => rw [← DirectSum.sum_univ_of m]
  exact Finset.sum_congr rfl fun i _ => by
    rw [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]

/-- `toEndₗ` is unital: `1 = ∑ᵢ pᵢ` maps to `∑ᵢ lofᵢ ∘ componentᵢ = id`. -/
theorem toEndₗ_one [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    toEndₗ R 1 = 1 := by
  rw [one_def, map_sum, Module.End.one_eq_id, ← sum_lof_comp_component R]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toEndₗ_single, one_smul, pathEnd_mk, pathMap_nil, LinearMap.id_comp]

/-- **Reverse direction of the bijection (deliverable 3).** The left `P_Q`-module structure on
`M = ⊕ᵢ R.obj (op i)` induced by a representation `R` of the opposite quiver `Qᵒᵖ`, packaged as a
`k`-algebra homomorphism `P_Q →ₐ[k] End k M`. On a basis path `⟨a,b,p⟩` it acts by `pathEnd`.
Multiplicativity is `pathMap (p.comp q) = pathMap p ∘ pathMap q` (`toEndₗ_mul`); the unit law is
`∑ᵢ pᵢ = 1 ↦ id` (`toEndₗ_one`). This is the genuine left-module action whose existence the issue
requires (a real `def`, not a `sorry`). -/
noncomputable def toEnd [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    PathAlgebra k Q →ₐ[k] Module.End k (DirectSum Q (reverseFam R)) :=
  AlgHom.ofLinearMap (toEndₗ R) (toEndₗ_one R) (toEndₗ_mul R)

@[simp] theorem toEnd_apply [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ)
    (a : PathAlgebra k Q) : toEnd R a = toEndₗ R a := rfl

@[simp] theorem toEnd_ofPath [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ)
    (x : Etingof.QuiverPathIndex Q) : toEnd R (ofPath x) = pathEnd R x := by
  rw [toEnd_apply, toEndₗ_ofPath]

/-- The left `P_Q`-module structure on `M = ⊕ᵢ R.obj (op i)` from the reverse direction, obtained
by restricting scalars along the algebra hom `toEnd R`. -/
@[reducible] noncomputable def reverseModule [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    Module (PathAlgebra k Q) (DirectSum Q (reverseFam R)) :=
  Module.compHom _ (toEnd R).toRingHom

/-- The reverse-direction action is `a • m = toEnd R a m`. -/
theorem reverseModule_smul_def [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ)
    (a : PathAlgebra k Q) (m : DirectSum Q (reverseFam R)) :
    (letI := reverseModule R; a • m) = toEnd R a m := rfl

/-- The reverse-direction module is compatible with the ground field `k`: `k → P_Q → M` is a
scalar tower, since `toEnd R` is `k`-linear. -/
theorem reverseModule_isScalarTower [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    letI := reverseModule R
    IsScalarTower k (PathAlgebra k Q) (DirectSum Q (reverseFam R)) := by
  letI := reverseModule R
  refine ⟨fun c a m => ?_⟩
  change toEnd R (c • a) m = c • (toEnd R a) m
  rw [map_smul, LinearMap.smul_apply]

end ReverseDirection

/-! ## The two round-trips: `forwardRep` and `reverseModule` are mutually inverse

The discussion following Definition 2.8.4 asserts that the assignments `V ↦ (pᵢ V)`
(`forwardRep`) and `(Vᵢ) ↦ ⊕ᵢ Vᵢ` (`reverseModule`) are mutually inverse, hence give a bijection
between isomorphism classes. We make both round-trips precise:

* **Module round-trip** (`moduleRoundTrip`): a `P_Q`-linear isomorphism
  `V ≅ reverseModule (forwardRep V)`.
* **Representation round-trip** (`repRoundTrip`): an isomorphism of quiver representations
  `R ≅ forwardRep (reverseModule R)`.

Both rest on the underlying-module decomposition `isInternal_vertexSpace` together with the
naturality of the arrow maps, recorded below.
-/

section InternalDecomposition

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]
variable [Fintype Q] {V : Type*} [AddCommGroup V] [Module k V]
  [Module (PathAlgebra k Q) V] [IsScalarTower k (PathAlgebra k Q) V]

/-- **Module side of the quiver-representation / path-module bijection.** For a left module `V`
over the path algebra of a finite quiver, the vertex spaces `Vᵢ = pᵢ V` give an internal
direct-sum decomposition `V = ⊕ᵢ Vᵢ`. This is the underlying-module content witnessing that the
assignments `V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ` are mutually inverse. (Requires `AddCommGroup V`, the
only place subtraction enters: the internal-decomposition criterion is stated for groups.) -/
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

end InternalDecomposition

section RoundTripHelpers

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The product of two basis paths is `compSingle`: `ofPath x · ofPath y = compSingle x y`. -/
theorem ofPath_mul (x y : Etingof.QuiverPathIndex Q) :
    (ofPath x : PathAlgebra k Q) * ofPath y = compSingle x y := by
  rw [ofPath, ofPath, single_mul_single, one_mul, one_smul]

/-- A basis path that ends in an arrow factors as the head path times the arrow:
`ofPath ⟨a,b,p.cons e⟩ = ofPath ⟨a,c,p⟩ · aₑ`. -/
theorem ofPath_cons {a c b : Q} (p : Quiver.Path a c) (e : c ⟶ b) :
    (ofPath ⟨a, b, p.cons e⟩ : PathAlgebra k Q) = ofPath ⟨a, c, p⟩ * ofArrow e := by
  have hidx : (⟨a, b, p.cons e⟩ : Etingof.QuiverPathIndex Q) = ⟨a, b, p.comp e.toPath⟩ := by
    rw [Quiver.Hom.toPath, Quiver.Path.comp_cons, Quiver.Path.comp_nil]
  rw [hidx, ofArrow, ofPath_mul, compSingle_eq, ofPath]

omit [DecidableEq Q] in
/-- The contravariant `pathMap` of a single-arrow path is the arrow map: for `e : a ⟶ b` of `Q`,
`pathMap R e.toPath = R.mapLinear eᵒᵖ`. -/
@[simp] theorem pathMap_toPath (R : Etingof.QuiverRepresentation k Qᵒᵖ) {a b : Q} (e : a ⟶ b) :
    pathMap R e.toPath = R.mapLinear e.op := by
  rw [Quiver.Hom.toPath, pathMap_cons, pathMap_nil, LinearMap.id_comp]

end RoundTripHelpers

section ModuleRoundTrip

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]
variable {V : Type*} [AddCommGroup V] [Module k V]
  [Module (PathAlgebra k Q) V] [IsScalarTower k (PathAlgebra k Q) V]

/-- **Naturality of the forward arrow maps on basis paths.** For a basis path `p : a ⟶* b`, left
multiplication by `ofPath ⟨a,b,p⟩` on a vertex-space element `y ∈ Vᵦ` agrees with the composite of
the forward arrow maps `pathMap (forwardRep V) p : Vᵦ → Vₐ`. This is the identity that pins the
forward functor's arrow data to the genuine `P_Q`-action, proved by induction on `p`. -/
theorem ofPath_smul_eq_pathMap {a b : Q} (p : Quiver.Path a b) :
    ∀ (y : (vertexSpace b : Submodule k V)),
      (ofPath ⟨a, b, p⟩ : PathAlgebra k Q) • (y : V)
        = (vertexSpace a : Submodule k V).subtype (pathMap (forwardRep (k := k) (V := V)) p y) := by
  induction p with
  | nil =>
    intro y
    rw [pathMap_nil, LinearMap.id_apply]
    change (trivialPath a : PathAlgebra k Q) • (y : V) = (y : V)
    rw [← vertexProj_apply]
    exact vertexProj_eq_self_of_mem y.2
  | cons p' e ih =>
    intro y
    rw [ofPath_cons p' e, mul_smul, ← arrowMap_coe_apply e y, ih (arrowMap e y), pathMap_cons,
      LinearMap.comp_apply, forwardRep_mapLinear]
    rfl

attribute [local instance] reverseModule

local instance forwardReverse_tower :
    IsScalarTower k (PathAlgebra k Q) (DirectSum Q (reverseFam (forwardRep (k := k) (V := V)))) :=
  reverseModule_isScalarTower (forwardRep (k := k) (V := V))

/-- Abbreviation: the summing map `⊕ᵢ Vᵢ → V` of the internal decomposition, on the carrier of the
reverse module of `forwardRep V`. -/
private noncomputable abbrev coeV :
    DirectSum Q (reverseFam (forwardRep (k := k) (V := V))) →ₗ[k] V :=
  DirectSum.coeLinearMap (fun i => (vertexSpace (k := k) (V := V) i : Submodule k V))

/-- The summing map sends the `i`-th inclusion of `z` to `z` itself (`coeV ∘ lofᵢ = subtype`).
A `coeLinearMap_lof` restated through the `reverseFam` spelling of the family. -/
private theorem coeV_lof (i : Q) (z : reverseFam (forwardRep (k := k) (V := V)) i) :
    coeV (k := k) (V := V)
        (DirectSum.lof k Q (reverseFam (forwardRep (k := k) (V := V))) i z)
      = (vertexSpace (k := k) (V := V) i : Submodule k V).subtype z :=
  DirectSum.coeLinearMap_lof (fun i => (vertexSpace (k := k) (V := V) i : Submodule k V)) i z

/-- **Path action recovered.** Under the summing map `⊕ᵢ Vᵢ → V`, the reverse-direction
endomorphism `pathEnd (forwardRep V) x` of a basis path `x` corresponds to left multiplication by
`ofPath x` on `V`. The composable case uses the arrow-map naturality lemma `ofPath_smul_eq_pathMap`;
the non-composable case uses the target-idempotent absorption `ofPath · p_c = 0`. -/
theorem coeLinearMap_pathEnd (x : Etingof.QuiverPathIndex Q)
    (m : DirectSum Q (reverseFam (forwardRep (k := k) (V := V)))) :
    coeV (k := k) (V := V) (pathEnd (forwardRep (k := k) (V := V)) x m)
      = (ofPath x : PathAlgebra k Q) • coeV (k := k) (V := V) m := by
  obtain ⟨a, b, p⟩ := x
  have key : (coeV (k := k) (V := V)).comp (pathEnd (forwardRep (k := k) (V := V)) ⟨a, b, p⟩)
      = (moduleEnd (ofPath ⟨a, b, p⟩)).comp (coeV (k := k) (V := V)) := by
    refine DirectSum.linearMap_ext k fun c => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, pathEnd_mk, moduleEnd_apply]
    rw [coeV_lof, coeV_lof]
    by_cases h : c = b
    · subst h
      rw [DirectSum.component.lof_self]
      exact (ofPath_smul_eq_pathMap p y).symm
    · rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]
      -- `ofPath ⟨a,b,p⟩ • ↑y = 0` since `y ∈ V_c` and `b ≠ c`
      symm
      have hy : (trivialPath c : PathAlgebra k Q) •
            (vertexSpace (k := k) (V := V) c : Submodule k V).subtype y
          = (vertexSpace (k := k) (V := V) c : Submodule k V).subtype y := by
        rw [← vertexProj_apply]; exact vertexProj_eq_self_of_mem y.2
      rw [← hy, ← mul_smul, ofPath_mul_trivialPath, if_neg (Ne.symm h), zero_smul]
  have := LinearMap.congr_fun key m
  simpa only [LinearMap.comp_apply, moduleEnd_apply] using this

/-- The reverse-direction action `toEnd (forwardRep V)` corresponds, under the summing map, to the
genuine `P_Q`-action on `V`. Reduces to `coeLinearMap_pathEnd` on basis paths by `k`-linearity. -/
theorem coeLinearMap_toEnd (a : PathAlgebra k Q)
    (m : DirectSum Q (reverseFam (forwardRep (k := k) (V := V)))) :
    coeV (k := k) (V := V) (toEnd (forwardRep (k := k) (V := V)) a m)
      = a • coeV (k := k) (V := V) m := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a1 a2 h1 h2 => rw [map_add, LinearMap.add_apply, map_add, h1, h2, add_smul]
  | single x c =>
    have hs : (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x := by
      rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, LinearMap.smul_apply, map_smul, toEnd_ofPath, coeLinearMap_pathEnd,
      smul_assoc]

/-- **Module round-trip.** A left `P_Q`-module `V` over the path algebra of a finite quiver is
isomorphic, as a `P_Q`-module, to `reverseModule (forwardRep V)` — the module obtained by extracting
the vertex spaces `Vᵢ = pᵢ V` and reassembling them. The underlying `k`-linear isomorphism is the
internal direct-sum decomposition `V ≅ ⊕ᵢ Vᵢ` (`isInternal_vertexSpace`); `P_Q`-linearity is
`coeLinearMap_toEnd`. Together with `repRoundTrip` this realizes the discussion's claim that
`V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ` are mutually inverse. -/
noncomputable def moduleRoundTrip :
    DirectSum Q (reverseFam (forwardRep (k := k) (V := V))) ≃ₗ[PathAlgebra k Q] V :=
  let e : DirectSum Q (reverseFam (forwardRep (k := k) (V := V))) ≃ₗ[k] V :=
    LinearEquiv.ofBijective (coeV (k := k) (V := V)) isInternal_vertexSpace
  { toFun := e
    map_add' := e.map_add
    map_smul' := coeLinearMap_toEnd
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

end ModuleRoundTrip

section RepRoundTrip

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]
variable (R : Etingof.QuiverRepresentation k Qᵒᵖ)

attribute [local instance] reverseModule

local instance reverseModule_tower :
    IsScalarTower k (PathAlgebra k Q) (DirectSum Q (reverseFam R)) :=
  reverseModule_isScalarTower R

/-- The vertex projection of the reverse module is the `i`-th-summand projection
`lofᵢ ∘ componentᵢ` (the trivial path `pᵢ` acts as `pathEnd ⟨i,i,nil⟩`). -/
theorem vertexProj_reverseModule (i : Q) (m : DirectSum Q (reverseFam R)) :
    (vertexProj (k := k) (V := DirectSum Q (reverseFam R)) i) m
      = DirectSum.lof k Q (reverseFam R) i (DirectSum.component k Q (reverseFam R) i m) := by
  rw [vertexProj_apply, reverseModule_smul_def, trivialPath, toEnd_ofPath, pathEnd_mk]
  simp only [LinearMap.comp_apply, pathMap_nil, LinearMap.id_coe, id_eq]

/-- The `i`-th vertex space of the reverse module is the range of the `i`-th inclusion `lofᵢ`. -/
theorem vertexSpace_reverseModule (i : Q) :
    (vertexSpace (k := k) (V := DirectSum Q (reverseFam R)) i)
      = LinearMap.range (DirectSum.lof k Q (reverseFam R) i) := by
  apply le_antisymm
  · rw [vertexSpace_eq]
    rintro x ⟨v, rfl⟩
    rw [vertexProj_reverseModule]
    exact LinearMap.mem_range_self _ _
  · rintro x ⟨y, rfl⟩
    rw [vertexSpace_eq]
    exact ⟨_, by rw [vertexProj_reverseModule, DirectSum.component.lof_self]⟩

/-- On the reverse module, the `i`-th inclusion followed by the `i`-th projection is the identity on
the vertex space: `lofᵢ (componentᵢ y) = y` for `y ∈ Vᵢ`. -/
theorem lof_component_of_mem (i : Q)
    (y : (vertexSpace (k := k) (V := DirectSum Q (reverseFam R)) i)) :
    DirectSum.lof k Q (reverseFam R) i
        (DirectSum.component k Q (reverseFam R) i (y : DirectSum Q (reverseFam R)))
      = (y : DirectSum Q (reverseFam R)) := by
  rw [← vertexProj_reverseModule]
  exact vertexProj_eq_self_of_mem y.2

/-- **Vertex-space recovery.** For a representation `R` of `Qᵒᵖ`, the `i`-th vertex space of the
reverse module `reverseModule R` is canonically isomorphic to `R.obj (op i)` via the `i`-th
inclusion `lofᵢ` (with inverse the `i`-th projection `componentᵢ`). -/
noncomputable def repEquivAt (i : Q) :
    R.obj (Opposite.op i) ≃ₗ[k] (vertexSpace (k := k) (V := DirectSum Q (reverseFam R)) i) :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ (DirectSum.lof k Q (reverseFam R) i)
      (fun y => by rw [vertexSpace_reverseModule]; exact LinearMap.mem_range_self _ y))
    ((DirectSum.component k Q (reverseFam R) i).comp
      (Submodule.subtype (vertexSpace (k := k) (V := DirectSum Q (reverseFam R)) i)))
    (by
      refine LinearMap.ext fun y => ?_
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearMap.id_coe, id_eq]
      exact lof_component_of_mem R i y)
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.lof_self, LinearMap.id_coe, id_eq])

@[simp] theorem repEquivAt_coe (i : Q) (x : R.obj (Opposite.op i)) :
    ((repEquivAt R i x : (vertexSpace (k := k) (V := DirectSum Q (reverseFam R)) i))
        : DirectSum Q (reverseFam R))
      = DirectSum.lof k Q (reverseFam R) i x :=
  rfl

/-- Naturality of the vertex-space-recovery isomorphisms: the arrow map of `forwardRep
(reverseModule R)` corresponds, under `repEquivAt`, to the arrow map of `R`. -/
theorem repEquivAt_naturality {X Y : Qᵒᵖ} (e : X ⟶ Y) (x : R.obj X) :
    repEquivAt R Y.unop (R.mapLinear e x)
      = (forwardRep (k := k) (V := DirectSum Q (reverseFam R))).mapLinear e
          (repEquivAt R X.unop x) := by
  apply Subtype.ext
  change DirectSum.lof k Q (reverseFam R) Y.unop (R.mapLinear e x)
      = toEnd R (ofArrow e.unop) (DirectSum.lof k Q (reverseFam R) X.unop x)
  rw [ofArrow, toEnd_ofPath, pathEnd_mk]
  simp only [LinearMap.comp_apply, DirectSum.component.lof_self, pathMap_toPath]
  rfl

/-- **Representation round-trip.** A representation `R` of `Qᵒᵖ` maps to the representation
`forwardRep (reverseModule R)` (turn `R` into a `P_Q`-module, then extract its vertex spaces) by a
homomorphism of quiver representations whose component at each vertex is the linear *equivalence*
`repEquivAt` — hence an isomorphism `R ≅ forwardRep (reverseModule R)`. Naturality is the identity
`pathMap R e.toPath = R.mapLinear eᵒᵖ` packaged through the reverse-module action. -/
noncomputable def repRoundTrip :
    Etingof.QuiverRepresentationHom k Qᵒᵖ R
      (forwardRep (k := k) (V := DirectSum Q (reverseFam R))) where
  app v := (repEquivAt R v.unop).toLinearMap
  naturality e x := repEquivAt_naturality R e x

end RepRoundTrip

end Etingof.PathAlgebra
