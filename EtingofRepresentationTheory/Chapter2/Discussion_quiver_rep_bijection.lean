import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter2.Definition2_8_10
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.DirectSum.Module

/-!
# Discussion: quiver representations vs. path-algebra modules

The discussion following Definition 2.8.4 in Etingof asserts that a representation of a
quiver `Q` is "the same thing" as a representation (module) of its path algebra `P_Q`, with
mutually inverse assignments `V ↦ (pᵢ V)` and `(Vᵢ) ↦ ⊕ᵢ Vᵢ`, giving a bijection between
isomorphism classes.

This file develops the algebraic foundation that both directions of that bijection rest on:
the trivial paths `pᵢ = ofPath ⟨i, i, nil⟩` form a family of orthogonal idempotents
summing (for a finite vertex set) to `1`, and they absorb an oriented path on the
correct side. Concretely, for an oriented path `a : x ⟶* y`,

* `pₓ · a = a` and `pₖ · a = 0` for `k ≠ x` (the source idempotent acts on the left), and
* `a · p_y = a` and `a · pₖ = 0` for `k ≠ y` (the target idempotent acts on the right).

These are precisely the relations that make `pᵢ V` the `i`-th vertex space and that pin down
which vertex space a single-arrow path maps out of and into.

## Convention / direction note

`Definition2_8_4` builds `P_Q` with Mathlib's source-to-target concatenation
(`comp x y` is defined when `target x = source y`, giving a path `source x ⟶* target y`).
This is the opposite of Etingof's body-text reading `ab = "first b then a"`; the two
conventions produce mutually opposite algebras. The absorption laws below are stated for the
source-to-target algebra actually constructed.

A consequence worth flagging for the full bijection: under this convention, for an arrow
`e : i ⟶ j` the basis element `aₑ = ofPath ⟨i, j, e.toPath⟩` satisfies `pᵢ · aₑ = aₑ` and
`aₑ · p_j = aₑ`, so in a left `P_Q`-module the operator `v ↦ aₑ • v` carries `p_j V` into
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
  change (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
      (Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1) (Finsupp.single ⟨a, b, p⟩ 1)) =
    if i = a then Finsupp.single ⟨a, b, p⟩ 1 else 0
  rw [single_mul_single, one_mul, one_smul, compSingle_nil_left]

/-- Right absorption: multiplying a basis path `a : x ⟶* y` on the right by the trivial path
`pᵢ` returns `a` when `i` is its target, and `0` otherwise. -/
theorem ofPath_mul_trivialPath (a b i : Q) (p : Quiver.Path a b) :
    (ofPath ⟨a, b, p⟩ : PathAlgebra k Q) * trivialPath i
      = if b = i then ofPath ⟨a, b, p⟩ else 0 := by
  change (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
      (Finsupp.single ⟨a, b, p⟩ 1) (Finsupp.single ⟨i, i, Quiver.Path.nil⟩ 1)) =
    if b = i then Finsupp.single ⟨a, b, p⟩ 1 else 0
  rw [single_mul_single, mul_one, one_smul, compSingle_nil_right]

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

/-- The trivial-path idempotents `pᵢ` form a complete family of orthogonal idempotents in the
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
underlying modules. The vertex spaces inherit the arrow maps, and the full functor and
isomorphism-class bijection sit on top of this decomposition (see the convention note above for
the modelling
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
`Vᵢ = pᵢ V` (because `pᵢ · aₑ = aₑ`): it points `Vⱼ → Vᵢ`, the opposite direction to an arrow
`i ⟶ j` of `Etingof.QuiverRepresentation k Q` (which carries `Vᵢ → Vⱼ`).

This is the modelling decision flagged in the module docstring. We resolve it by collecting the
data into a representation of the opposite quiver `Qᵒᵖ`: an arrow `op j ⟶ op i` of `Qᵒᵖ`
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

From a representation `R` of the opposite quiver `Qᵒᵖ` we
build a left `P_Q`-module on `M = ⊕ᵢ R.obj (op i)`. A path `p : a ⟶* b` of `Q` acts by the
composite of the arrow maps `R.mapLinear`, read contravariantly
(`pathMap (cons p e) = pathMap p ∘ R.mapLinear eᵒᵖ`), sending the `b`-summand to the `a`-summand
and zero on the other summands. The contravariant reading is exactly what turns the
source-to-target product `single⟨a,b,p⟩·single⟨b,d,q⟩ = single⟨a,d,p.comp q⟩` into composition
(`pathMap (p.comp q) = pathMap p ∘ pathMap q`), so the assignment is a left action,
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
  -- `PathAlgebra k Q` is a `def` (not a reducible `abbrev`), so unfolding `toEndₗ` leaves the
  -- `Finsupp.lsum` applied at the `PathAlgebra` coercion, where `Finsupp.lsum_single` does not
  -- fire. Restate the goal (defeq) with the underlying `QuiverPathIndex Q →₀ k` coercion.
  change (Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (pathEnd R x))
      (Finsupp.single x c) = c • pathEnd R x
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq]

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
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f1 f2 h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | single x a =>
    induction g using PathAlgebra.induction_linear with
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
  rw [one_eq_ofPath_sum, map_sum, Module.End.one_eq_id, ← sum_lof_comp_component R]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toEndₗ_ofPath, pathEnd_mk, pathMap_nil, LinearMap.id_comp]

/-- **Reverse direction of the bijection.** The left `P_Q`-module structure on
`M = ⊕ᵢ R.obj (op i)` induced by a representation `R` of the opposite quiver `Qᵒᵖ`, packaged as a
`k`-algebra homomorphism `P_Q →ₐ[k] End k M`. On a basis path `⟨a,b,p⟩` it acts by `pathEnd`.
Multiplicativity is `pathMap (p.comp q) = pathMap p ∘ pathMap q` (`toEndₗ_mul`); the unit law is
`∑ᵢ pᵢ = 1 ↦ id` (`toEndₗ_one`). -/
noncomputable def toEnd [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ) :
    PathAlgebra k Q →ₐ[k] Module.End k (DirectSum Q (reverseFam R)) :=
  AlgHom.ofLinearMap (toEndₗ R) (toEndₗ_one R) (toEndₗ_mul R)

@[simp] theorem toEnd_apply [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ)
    (a : PathAlgebra k Q) : toEnd R a = toEndₗ R a := rfl

theorem toEnd_ofPath [Fintype Q] (R : Etingof.QuiverRepresentation k Qᵒᵖ)
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

/-- A path-algebra-linear equivalence induces an equivalence of the representations obtained by
restricting to the vertex spaces. This is the morphism-level compatibility needed to descend
`forwardRep` to isomorphism classes. -/
noncomputable def forwardRepEquiv {W : Type*} [AddCommGroup W] [Module k W]
    [Module (PathAlgebra k Q) W] [IsScalarTower k (PathAlgebra k Q) W]
    (e : V ≃ₗ[PathAlgebra k Q] W) :
    Etingof.QuiverRepresentationEquiv k Qᵒᵖ
      (forwardRep (k := k) (V := V)) (forwardRep (k := k) (V := W)) where
  equivAt v := LinearEquiv.ofLinear
    (LinearMap.codRestrict _
      ((e.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSpace (k := k) (V := V) v.unop)))
      (fun (x : (vertexSpace (k := k) (V := V) v.unop : Submodule k V)) => by
        refine ⟨e (x : V), ?_⟩
        rw [vertexProj_apply, ← e.map_smul, ← vertexProj_apply,
          vertexProj_eq_self_of_mem x.2]
        rfl))
    (LinearMap.codRestrict _
      ((e.symm.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSpace (k := k) (V := W) v.unop)))
      (fun (x : (vertexSpace (k := k) (V := W) v.unop : Submodule k W)) => by
        refine ⟨e.symm (x : W), ?_⟩
        rw [vertexProj_apply, ← e.symm.map_smul, ← vertexProj_apply,
          vertexProj_eq_self_of_mem x.2]
        rfl))
    (by
      refine LinearMap.ext fun x => ?_
      let xw : (vertexSpace (k := k) (V := W) v.unop : Submodule k W) := x
      apply Subtype.ext
      exact e.apply_symm_apply (xw : W))
    (by
      refine LinearMap.ext fun x => ?_
      let xv : (vertexSpace (k := k) (V := V) v.unop : Submodule k V) := x
      apply Subtype.ext
      exact e.symm_apply_apply (xv : V))
  commutes {v w} f x := by
    apply Subtype.ext
    let xv : (vertexSpace (k := k) (V := V) v.unop : Submodule k V) := x
    change e ((ofArrow f.unop : PathAlgebra k Q) • (xv : V)) =
      (ofArrow f.unop : PathAlgebra k Q) • e (xv : V)
    exact e.map_smul _ _

/-- **Naturality of the forward arrow maps on basis paths.** For a basis path `p : a ⟶* b`, left
multiplication by `ofPath ⟨a,b,p⟩` on a vertex-space element `y ∈ Vᵦ` agrees with the composite of
the forward arrow maps `pathMap (forwardRep V) p : Vᵦ → Vₐ`. This is the identity that pins the
forward functor's arrow data to the `P_Q`-action, proved by induction on `p`. -/
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
    · rw [DirectSum.component.of, dif_neg h]
      have hzero : (vertexSpace (k := k) (V := V) a : Submodule k V).subtype
          (pathMap (forwardRep (k := k) (V := V)) p
            (0 : (vertexSpace (k := k) (V := V) b : Submodule k V))) = 0 := by
        calc
          _ = (vertexSpace (k := k) (V := V) a : Submodule k V).subtype 0 :=
            congrArg
              (vertexSpace (k := k) (V := V) a : Submodule k V).subtype
              (LinearMap.map_zero (pathMap (forwardRep (k := k) (V := V)) p))
          _ = 0 := LinearMap.map_zero _
      calc
        _ = 0 := hzero
        _ = (ofPath ⟨a, b, p⟩ : PathAlgebra k Q) •
            (vertexSpace (k := k) (V := V) c : Submodule k V).subtype y := by
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
`P_Q`-action on `V`. Reduces to `coeLinearMap_pathEnd` on basis paths by `k`-linearity. -/
theorem coeLinearMap_toEnd (a : PathAlgebra k Q)
    (m : DirectSum Q (reverseFam (forwardRep (k := k) (V := V)))) :
    coeV (k := k) (V := V) (toEnd (forwardRep (k := k) (V := V)) a m)
      = a • coeV (k := k) (V := V) m := by
  induction a using PathAlgebra.induction_linear with
  | zero => simp
  | add a1 a2 h1 h2 => rw [map_add, LinearMap.add_apply, map_add, h1, h2, add_smul]
  | single x c =>
    have hs : (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x := by
      exact (smul_single_one (k := k) c x).symm
    have hs_smul := congrArg
      (fun z : PathAlgebra k Q => z • coeV (k := k) (V := V) m) hs
    have htower : (c • (ofPath x : PathAlgebra k Q)) • coeV (k := k) (V := V) m =
        c • ((ofPath x : PathAlgebra k Q) • coeV (k := k) (V := V) m) :=
      smul_assoc c (ofPath x : PathAlgebra k Q) (coeV (k := k) (V := V) m)
    have hs_action := hs_smul.trans htower
    rw [toEnd_apply, toEndₗ_single, LinearMap.smul_apply, map_smul, coeLinearMap_pathEnd]
    exact hs_action.symm

/-- **Module round-trip.** A left `P_Q`-module `V` over the path algebra of a finite quiver is
isomorphic, as a `P_Q`-module, to `reverseModule (forwardRep V)`, the module obtained by extracting
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

omit [DecidableEq Q] [Fintype Q] in
/-- An isomorphism of quiver representations intertwines the contravariant maps assigned to
every oriented path. -/
theorem repEquiv_pathMap {S : Etingof.QuiverRepresentation k Qᵒᵖ}
    (e : Etingof.QuiverRepresentationEquiv k Qᵒᵖ R S) {a b : Q}
    (p : Quiver.Path a b) (x : R.obj (Opposite.op b)) :
    e.equivAt (Opposite.op a) (pathMap R p x) =
      pathMap S p (e.equivAt (Opposite.op b) x) := by
  induction p with
  | nil => simp only [pathMap_nil, LinearMap.id_apply]
  | cons p f ih =>
    simp only [pathMap_cons, LinearMap.comp_apply]
    rw [ih, e.commutes f.op]

/-- The direct sum of the vertexwise equivalences underlying an isomorphism of quiver
representations. -/
noncomputable def reverseLinearEquiv {S : Etingof.QuiverRepresentation k Qᵒᵖ}
    (e : Etingof.QuiverRepresentationEquiv k Qᵒᵖ R S) :
    DirectSum Q (reverseFam R) ≃ₗ[k] DirectSum Q (reverseFam S) :=
  DirectSum.congrLinearEquiv fun i => e.equivAt (Opposite.op i)

omit [Fintype Q] in
/-- `reverseLinearEquiv` intertwines the endomorphisms assigned to basis paths. -/
theorem reverseLinearEquiv_pathEnd {S : Etingof.QuiverRepresentation k Qᵒᵖ}
    (e : Etingof.QuiverRepresentationEquiv k Qᵒᵖ R S)
    (x : Etingof.QuiverPathIndex Q) (m : DirectSum Q (reverseFam R)) :
    reverseLinearEquiv R e (pathEnd R x m) =
      pathEnd S x (reverseLinearEquiv R e m) := by
  induction m using DirectSum.induction_on with
  | zero => simp
  | add m n hm hn =>
    rw [map_add, map_add, hm, hn]
    exact (map_add (pathEnd S x) _ _).symm.trans
      (congrArg (pathEnd S x) ((reverseLinearEquiv R e).map_add m n).symm)
  | of i z =>
    rw [← DirectSum.lof_eq_of k]
    obtain ⟨a, b, p⟩ := x
    simp only [pathEnd_mk, LinearMap.comp_apply]
    by_cases h : i = b
    · subst h
      rw [DirectSum.component.lof_self]
      simp only [reverseLinearEquiv, DirectSum.coe_congrLinearEquiv,
        DirectSum.lmap_lof]
      rw [DirectSum.component.lof_self]
      exact congrArg (DirectSum.lof k Q (reverseFam S) a)
        (repEquiv_pathMap R e p z)
    · rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]
      simp only [reverseLinearEquiv, DirectSum.coe_congrLinearEquiv,
        DirectSum.lmap_lof, DirectSum.component.of, dif_neg h, map_zero]

/-- `reverseLinearEquiv` intertwines the full path-algebra actions obtained by linear extension
from basis paths. -/
theorem reverseLinearEquiv_toEnd {S : Etingof.QuiverRepresentation k Qᵒᵖ}
    (e : Etingof.QuiverRepresentationEquiv k Qᵒᵖ R S)
    (a : PathAlgebra k Q) (m : DirectSum Q (reverseFam R)) :
    reverseLinearEquiv R e (toEnd R a m) =
      toEnd S a (reverseLinearEquiv R e m) := by
  induction a using PathAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, ha, hb]
    exact (congrArg
      (fun f : Module.End k (DirectSum Q (reverseFam S)) => f (reverseLinearEquiv R e m))
      (map_add (toEnd S) a b)).symm
  | single x c =>
    rw [toEnd_apply, toEndₗ_single, LinearMap.smul_apply, map_smul, toEnd_apply,
      toEndₗ_single, LinearMap.smul_apply, reverseLinearEquiv_pathEnd]

/-- Isomorphic quiver representations yield isomorphic modules under `reverseModule`. This is
the morphism-level compatibility needed to descend `reverseModule` to isomorphism classes. -/
noncomputable def reverseModuleEquiv {S : Etingof.QuiverRepresentation k Qᵒᵖ}
    (e : Etingof.QuiverRepresentationEquiv k Qᵒᵖ R S) :
    letI := reverseModule R
    letI := reverseModule S
    DirectSum Q (reverseFam R) ≃ₗ[PathAlgebra k Q] DirectSum Q (reverseFam S) := by
  letI := reverseModule R
  letI := reverseModule S
  let ek := reverseLinearEquiv R e
  exact
    { toFun := ek
      map_add' := ek.map_add
      map_smul' := fun a m => reverseLinearEquiv_toEnd R e a m
      invFun := ek.symm
      left_inv := ek.left_inv
      right_inv := ek.right_inv }

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
homomorphism of quiver representations whose component at each vertex is the linear equivalence
`repEquivAt`, hence an isomorphism `R ≅ forwardRep (reverseModule R)`. Naturality is the identity
`pathMap R e.toPath = R.mapLinear eᵒᵖ` packaged through the reverse-module action. -/
noncomputable def repRoundTrip :
    Etingof.QuiverRepresentationEquiv k Qᵒᵖ R
      (forwardRep (k := k) (V := DirectSum Q (reverseFam R))) where
  equivAt v := repEquivAt R v.unop
  commutes e x := repEquivAt_naturality R e x

end RepRoundTrip

/-! ## Bijection on isomorphism classes -/

universe u v w

section IsoClasses

variable (k : Type u) (Q : Type v) [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]

/-- A bundled left module over the path algebra, used as the carrier of the module-side
isomorphism-class quotient. -/
structure PathModule where
  /-- The underlying type of the module. -/
  carrier : Type w
  /-- The additive commutative group structure on the carrier. -/
  addCommGroup : AddCommGroup carrier
  /-- The ground-field module structure on the carrier. -/
  moduleField : Module k carrier
  /-- The path-algebra module structure on the carrier. -/
  modulePathAlgebra : Module (PathAlgebra k Q) carrier
  /-- Compatibility of the ground-field and path-algebra scalar actions. -/
  scalarTower : IsScalarTower k (PathAlgebra k Q) carrier

/-- Two bundled path-algebra modules are isomorphic when their carriers are related by a
path-algebra-linear equivalence. -/
def PathModule.Isomorphic (M N : PathModule k Q) : Prop :=
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  letI := N.addCommGroup
  letI := N.moduleField
  letI := N.modulePathAlgebra
  letI := N.scalarTower
  Nonempty (M.carrier ≃ₗ[PathAlgebra k Q] N.carrier)

/-- Isomorphism of path-algebra modules as a Setoid relation. -/
def pathModuleIsoSetoid : Setoid (PathModule k Q) where
  r := PathModule.Isomorphic k Q
  iseqv := {
    refl := fun M => by
      letI := M.addCommGroup
      letI := M.moduleField
      letI := M.modulePathAlgebra
      letI := M.scalarTower
      exact ⟨LinearEquiv.refl (PathAlgebra k Q) M.carrier⟩
    symm := fun {M N} h => by
      letI := M.addCommGroup
      letI := M.moduleField
      letI := M.modulePathAlgebra
      letI := M.scalarTower
      letI := N.addCommGroup
      letI := N.moduleField
      letI := N.modulePathAlgebra
      letI := N.scalarTower
      change Nonempty (M.carrier ≃ₗ[PathAlgebra k Q] N.carrier) at h
      obtain ⟨e⟩ := h
      exact ⟨e.symm⟩
    trans := fun {M N P} h₁ h₂ => by
      letI := M.addCommGroup
      letI := M.moduleField
      letI := M.modulePathAlgebra
      letI := M.scalarTower
      letI := N.addCommGroup
      letI := N.moduleField
      letI := N.modulePathAlgebra
      letI := N.scalarTower
      letI := P.addCommGroup
      letI := P.moduleField
      letI := P.modulePathAlgebra
      letI := P.scalarTower
      change Nonempty (M.carrier ≃ₗ[PathAlgebra k Q] N.carrier) at h₁
      change Nonempty (N.carrier ≃ₗ[PathAlgebra k Q] P.carrier) at h₂
      obtain ⟨e⟩ := h₁
      obtain ⟨f⟩ := h₂
      exact ⟨e.trans f⟩ }

/-- Isomorphism of representations as a Setoid relation. -/
def quiverRepresentationIsoSetoid :
    Setoid (Etingof.QuiverRepresentation k Qᵒᵖ) where
  r R S := Nonempty (Etingof.QuiverRepresentationEquiv k Qᵒᵖ R S)
  iseqv := {
    refl := fun R => ⟨{
      equivAt := fun i => LinearEquiv.refl k (R.obj i)
      commutes := fun _ _ => rfl }⟩
    symm := fun {R S} ⟨e⟩ => ⟨{
      equivAt := fun i => (e.equivAt i).symm
      commutes := fun f x => by
        rw [LinearEquiv.symm_apply_eq, e.commutes f, LinearEquiv.apply_symm_apply] }⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨{
      equivAt := fun i => (e.equivAt i).trans (f.equivAt i)
      commutes := fun g x => by
        rw [LinearEquiv.trans_apply, e.commutes g, f.commutes g]
        rfl }⟩ }

/-- The isomorphism classes of left modules over `PathAlgebra k Q`. -/
abbrev PathModuleIsoClass := Quotient (pathModuleIsoSetoid k Q)

/-- The isomorphism classes of representations of the opposite quiver. -/
abbrev QuiverRepresentationIsoClass := Quotient (quiverRepresentationIsoSetoid k Q)

/-- Extract the opposite-quiver representation associated to a bundled path-algebra module. -/
noncomputable def PathModule.toQuiverRepresentation (M : PathModule k Q) :
    Etingof.QuiverRepresentation k Qᵒᵖ := by
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  exact forwardRep (k := k) (V := M.carrier)

/-- Reassemble a quiver representation into a bundled path-algebra module. -/
noncomputable def PathModule.ofQuiverRepresentation
    (R : Etingof.QuiverRepresentation k Qᵒᵖ) : PathModule k Q where
  carrier := DirectSum Q (reverseFam R)
  addCommGroup := Module.addCommMonoidToAddCommGroup k
  moduleField := inferInstance
  modulePathAlgebra := reverseModule R
  scalarTower := reverseModule_isScalarTower R

/-- `PathModule.toQuiverRepresentation` respects path-module isomorphisms. -/
theorem PathModule.toQuiverRepresentation_rel {M N : PathModule k Q}
    (h : (pathModuleIsoSetoid k Q).r M N) :
    (quiverRepresentationIsoSetoid k Q).r
      (M.toQuiverRepresentation k Q) (N.toQuiverRepresentation k Q) := by
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  letI := N.addCommGroup
  letI := N.moduleField
  letI := N.modulePathAlgebra
  letI := N.scalarTower
  change Nonempty (M.carrier ≃ₗ[PathAlgebra k Q] N.carrier) at h
  obtain ⟨e⟩ := h
  exact ⟨forwardRepEquiv (k := k) (Q := Q) e⟩

/-- `PathModule.ofQuiverRepresentation` respects representation isomorphisms. -/
theorem PathModule.ofQuiverRepresentation_rel
    {R S : Etingof.QuiverRepresentation k Qᵒᵖ}
    (h : (quiverRepresentationIsoSetoid k Q).r R S) :
    (pathModuleIsoSetoid k Q).r
      (PathModule.ofQuiverRepresentation k Q R)
      (PathModule.ofQuiverRepresentation k Q S) := by
  obtain ⟨e⟩ := h
  letI : AddCommGroup (DirectSum Q (reverseFam R)) :=
    Module.addCommMonoidToAddCommGroup k
  letI : Module (PathAlgebra k Q) (DirectSum Q (reverseFam R)) := reverseModule R
  letI : AddCommGroup (DirectSum Q (reverseFam S)) :=
    Module.addCommMonoidToAddCommGroup k
  letI : Module (PathAlgebra k Q) (DirectSum Q (reverseFam S)) := reverseModule S
  change Nonempty
    (DirectSum Q (reverseFam R) ≃ₗ[PathAlgebra k Q] DirectSum Q (reverseFam S))
  exact ⟨reverseModuleEquiv R e⟩

/-- The assignment `V ↦ (pᵢV)` on isomorphism classes. -/
noncomputable def moduleToRepresentationIsoClass :
    PathModuleIsoClass k Q → QuiverRepresentationIsoClass k Q :=
  Quotient.map (PathModule.toQuiverRepresentation k Q)
    (fun _ _ => PathModule.toQuiverRepresentation_rel k Q)

/-- The assignment `R ↦ ⊕ᵢ Rᵢ` on isomorphism classes. -/
noncomputable def representationToModuleIsoClass :
    QuiverRepresentationIsoClass k Q → PathModuleIsoClass k Q :=
  Quotient.map (PathModule.ofQuiverRepresentation k Q)
    (fun _ _ => PathModule.ofQuiverRepresentation_rel k Q)

set_option maxHeartbeats 800000 in
-- Reducing the nested quotient maps exposes both bundled round trips to the kernel.
/-- The module and representation assignments induce a bijection on isomorphism classes. -/
noncomputable def isoClassEquiv :
    PathModuleIsoClass k Q ≃ QuiverRepresentationIsoClass k Q where
  toFun := moduleToRepresentationIsoClass k Q
  invFun := representationToModuleIsoClass k Q
  left_inv := by
    intro x
    refine Quotient.inductionOn x fun M => ?_
    apply Quotient.sound
    letI := M.addCommGroup
    letI := M.moduleField
    letI := M.modulePathAlgebra
    letI := M.scalarTower
    let FR : Etingof.QuiverRepresentation k Qᵒᵖ :=
      forwardRep (k := k) (V := M.carrier)
    letI : AddCommGroup (DirectSum Q (reverseFam FR)) :=
      Module.addCommMonoidToAddCommGroup k
    letI : Module (PathAlgebra k Q) (DirectSum Q (reverseFam FR)) := reverseModule FR
    change Nonempty
      (DirectSum Q (reverseFam (forwardRep (k := k) (V := M.carrier))) ≃ₗ[PathAlgebra k Q]
        M.carrier)
    exact ⟨moduleRoundTrip (k := k) (Q := Q) (V := M.carrier)⟩
  right_inv := by
    intro x
    refine Quotient.inductionOn x fun R => ?_
    apply Quotient.sound
    letI : AddCommGroup (DirectSum Q (reverseFam R)) :=
      Module.addCommMonoidToAddCommGroup k
    letI : Module (PathAlgebra k Q) (DirectSum Q (reverseFam R)) := reverseModule R
    letI : IsScalarTower k (PathAlgebra k Q) (DirectSum Q (reverseFam R)) :=
      reverseModule_isScalarTower R
    change (quiverRepresentationIsoSetoid k Q).r
      (PathModule.toQuiverRepresentation k Q (PathModule.ofQuiverRepresentation k Q R)) R
    refine ⟨?_⟩
    let e := repRoundTrip R
    let esymm : Etingof.QuiverRepresentationEquiv k Qᵒᵖ
        (forwardRep (k := k) (V := DirectSum Q (reverseFam R))) R := {
      equivAt := fun i => (e.equivAt i).symm
      commutes := fun f x => by
        rw [LinearEquiv.symm_apply_eq, e.commutes f, LinearEquiv.apply_symm_apply] }
    exact esymm

end IsoClasses

end Etingof.PathAlgebra

/-! ## Exact book-facing correspondence

The development above predates `BookPathAlgebra` and faithfully describes modules over the
source-to-target implementation `PathAlgebra k Q`; those correspond to representations of
`Qᵒᵖ`. The following declarations state the book's actual claim using the multiplicative-opposite
façade from Definition 2.8.4. For this algebra, left multiplication by an arrow `i ⟶ j` maps
`p_iV` to `p_jV`, so no opposite quiver appears.
-/

namespace Etingof.BookPathAlgebra

universe u v w q

section Forward

variable {k : Type u} {Q : Type v} [Field k] [Quiver Q] [DecidableEq Q] [Fintype Q]
variable {V : Type w} [AddCommGroup V] [Module k V]
  [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]

/-- The one-edge basis vector in the book-facing path algebra. -/
noncomputable def ofArrow {i j : Q} (e : i ⟶ j) : BookPathAlgebra k Q :=
  ofPath (k := k) ⟨i, j, e.toPath⟩

/-- The book-facing path-algebra action as a `k`-algebra homomorphism to endomorphisms. -/
noncomputable def moduleEnd : BookPathAlgebra k Q →ₐ[k] Module.End k V :=
  Algebra.lsmul k k V

@[simp] theorem moduleEnd_apply (a : BookPathAlgebra k Q) (x : V) :
    moduleEnd (k := k) (V := V) a x = a • x :=
  rfl

/-- The projection onto the vertex space `p_iV`. -/
noncomputable def vertexProj (i : Q) : Module.End k V :=
  moduleEnd (k := k) (V := V) (trivialPath (k := k) (Q := Q) i)

/-- The `i`-th vertex space `V_i = p_iV`. -/
noncomputable def vertexSpace (i : Q) : Submodule k V :=
  LinearMap.range (vertexProj (k := k) (V := V) i)

@[simp] theorem vertexProj_apply (i : Q) (x : V) :
    vertexProj (k := k) (V := V) i x =
      (trivialPath (k := k) (Q := Q) i : BookPathAlgebra k Q) • x :=
  rfl

/-- An arrow `e : i ⟶ j` sends every vector, hence in particular every vector of `p_iV`, into
`p_jV`. This is relation `p_j a_e = a_e` from Problem 2.8.6. -/
theorem ofArrow_smul_mem {i j : Q} (e : i ⟶ j) (x : V) :
    (ofArrow (k := k) e : BookPathAlgebra k Q) • x ∈
      vertexSpace (k := k) (V := V) j := by
  refine ⟨(ofArrow (k := k) e : BookPathAlgebra k Q) • x, ?_⟩
  rw [vertexProj_apply, ← mul_smul]
  change (ofPath (k := k) ⟨j, j, Quiver.Path.nil⟩ *
      ofPath (k := k) ⟨i, j, e.toPath⟩) • x = _
  rw [ofPath_mul_ofPath, Quiver.Path.comp_nil]
  rfl

/-- The arrow map `x_h : V_i → V_j`, obtained by restricting the action of `a_h` to `p_iV`. -/
noncomputable def arrowMap {i j : Q} (e : i ⟶ j) :
    vertexSpace (k := k) (V := V) i →ₗ[k] vertexSpace (k := k) (V := V) j :=
  LinearMap.restrict (moduleEnd (k := k) (V := V) (ofArrow (k := k) e))
    (fun x _ => ofArrow_smul_mem (k := k) e x)

/-- The exact forward assignment from the book: a left `P_Q`-module `V` yields the quiver
representation with vertex spaces `p_iV` and arrow maps given by the one-edge paths. -/
noncomputable def forwardRep : QuiverRepresentation k Q where
  obj i := vertexSpace (k := k) (V := V) i
  mapLinear e := arrowMap (k := k) (V := V) e

end Forward

section IsoClasses

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{q} Q] [DecidableEq Q] [Fintype Q]

/-- A bundled left module over the book-facing path algebra. -/
structure PathModule where
  /-- The underlying type of the module. -/
  carrier : Type w
  /-- The additive commutative group structure on the carrier. -/
  addCommGroup : AddCommGroup carrier
  /-- The ground-field module structure on the carrier. -/
  moduleField : Module k carrier
  /-- The book-facing path-algebra module structure on the carrier. -/
  modulePathAlgebra : Module (BookPathAlgebra k Q) carrier
  /-- Compatibility of the ground-field and path-algebra scalar actions. -/
  scalarTower : IsScalarTower k (BookPathAlgebra k Q) carrier

/-- Isomorphism of bundled book-facing path-algebra modules. -/
def PathModule.Isomorphic (M N : PathModule k Q) : Prop :=
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  letI := N.addCommGroup
  letI := N.moduleField
  letI := N.modulePathAlgebra
  letI := N.scalarTower
  Nonempty (M.carrier ≃ₗ[BookPathAlgebra k Q] N.carrier)

/-- Isomorphism of book-facing path modules as a setoid relation. -/
def pathModuleIsoSetoid : Setoid (PathModule k Q) where
  r := PathModule.Isomorphic k Q
  iseqv := {
    refl := fun M => by
      letI := M.addCommGroup
      letI := M.moduleField
      letI := M.modulePathAlgebra
      letI := M.scalarTower
      exact ⟨LinearEquiv.refl (BookPathAlgebra k Q) M.carrier⟩
    symm := fun {M N} h => by
      letI := M.addCommGroup
      letI := M.moduleField
      letI := M.modulePathAlgebra
      letI := M.scalarTower
      letI := N.addCommGroup
      letI := N.moduleField
      letI := N.modulePathAlgebra
      letI := N.scalarTower
      exact ⟨h.some.symm⟩
    trans := fun {M N R} hMN hNR => by
      letI := M.addCommGroup
      letI := M.moduleField
      letI := M.modulePathAlgebra
      letI := M.scalarTower
      letI := N.addCommGroup
      letI := N.moduleField
      letI := N.modulePathAlgebra
      letI := N.scalarTower
      letI := R.addCommGroup
      letI := R.moduleField
      letI := R.modulePathAlgebra
      letI := R.scalarTower
      exact ⟨hMN.some.trans hNR.some⟩ }

/-- Isomorphism of representations of `Q` as a setoid relation. -/
def quiverRepresentationIsoSetoid : Setoid (QuiverRepresentation k Q) where
  r R S := Nonempty (QuiverRepresentationEquiv k Q R S)
  iseqv := {
    refl := fun R => ⟨{
      equivAt := fun i => LinearEquiv.refl k (R.obj i)
      commutes := fun _ _ => rfl }⟩
    symm := fun {R S} h => ⟨{
      equivAt := fun i => (h.some.equivAt i).symm
      commutes := fun f x => by
        rw [LinearEquiv.symm_apply_eq, h.some.commutes f, LinearEquiv.apply_symm_apply] }⟩
    trans := fun hRS hST => ⟨{
      equivAt := fun i => (hRS.some.equivAt i).trans (hST.some.equivAt i)
      commutes := fun {i j} f x => by
        simp only [LinearEquiv.trans_apply]
        rw [hRS.some.commutes f, hST.some.commutes f] }⟩ }

/-- Isomorphism classes of modules over the book-facing path algebra. -/
abbrev PathModuleIsoClass := Quotient (pathModuleIsoSetoid k Q)

/-- Isomorphism classes of representations of the original quiver `Q`. -/
abbrev QuiverRepresentationIsoClass := Quotient (quiverRepresentationIsoSetoid k Q)

/-- The exact forward construction `V ↦ (p_iV)` on a bundled module. -/
noncomputable def PathModule.toQuiverRepresentation (M : PathModule k Q) :
    QuiverRepresentation k Q := by
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  exact forwardRep (k := k) (Q := Q) (V := M.carrier)

/-- The covariant composite of the arrow maps along a path `p : i ⟶* j`. -/
noncomputable def pathMap (R : QuiverRepresentation k Q) {i j : Q}
    (p : Quiver.Path i j) : R.obj i →ₗ[k] R.obj j :=
  Quiver.Path.rec (motive := fun j _ => R.obj i →ₗ[k] R.obj j)
    LinearMap.id (fun _ e ih => R.mapLinear e ∘ₗ ih) p

/-- The action a basis path must have on `⊕_i V_i`: project to its source, apply the composite
arrow map, and include at its target. -/
noncomputable def pathEnd (R : QuiverRepresentation k Q) :
    QuiverPathIndex Q → Module.End k (DirectSum Q R.obj)
  | ⟨i, j, p⟩ => DirectSum.lof k Q R.obj j ∘ₗ pathMap k Q R p ∘ₗ
      DirectSum.component k Q R.obj i

omit [DecidableEq Q] [Fintype Q] in
@[simp] theorem pathMap_nil (R : QuiverRepresentation k Q) (i : Q) :
    pathMap k Q R (Quiver.Path.nil : Quiver.Path i i) = LinearMap.id :=
  rfl

omit [DecidableEq Q] [Fintype Q] in
@[simp] theorem pathMap_cons (R : QuiverRepresentation k Q) {i j l : Q}
    (p : Quiver.Path i j) (a : j ⟶ l) :
    pathMap k Q R (p.cons a) = R.mapLinear a ∘ₗ pathMap k Q R p :=
  rfl

omit [DecidableEq Q] [Fintype Q] in
/-- Covariant composition of the arrow maps along concatenated paths. -/
theorem pathMap_comp (R : QuiverRepresentation k Q) {i j l : Q}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    pathMap k Q R (p.comp q) = pathMap k Q R q ∘ₗ pathMap k Q R p := by
  induction q with
  | nil => simp
  | cons q a ih => simp only [Quiver.Path.comp_cons, pathMap_cons, ih, LinearMap.comp_assoc]

omit [DecidableEq Q] [Fintype Q] in
@[simp] theorem pathMap_toPath (R : QuiverRepresentation k Q) {i j : Q} (a : i ⟶ j) :
    pathMap k Q R a.toPath = R.mapLinear a := by
  rw [Quiver.Hom.toPath, pathMap_cons, pathMap_nil, LinearMap.comp_id]

omit [Fintype Q] in
theorem pathEnd_mk (R : QuiverRepresentation k Q) {i j : Q} (p : Quiver.Path i j) :
    pathEnd k Q R ⟨i, j, p⟩ =
      DirectSum.lof k Q R.obj j ∘ₗ pathMap k Q R p ∘ₗ
        DirectSum.component k Q R.obj i :=
  rfl

omit [Fintype Q] in
/-- Book-ordered path multiplication becomes composition of the corresponding endomorphisms. -/
theorem pathEnd_comp (R : QuiverRepresentation k Q) {i j l : Q}
    (p : Quiver.Path i j) (q : Quiver.Path j l) :
    pathEnd k Q R ⟨j, l, q⟩ * pathEnd k Q R ⟨i, j, p⟩ =
      pathEnd k Q R ⟨i, l, p.comp q⟩ := by
  ext x
  simp only [Module.End.mul_apply, pathEnd_mk, LinearMap.comp_apply,
    DirectSum.component.lof_self, pathMap_comp]

omit [Fintype Q] in
theorem pathEnd_comp_zero (R : QuiverRepresentation k Q) {i j l m : Q}
    (p : Quiver.Path i j) (q : Quiver.Path l m) (h : j ≠ l) :
    pathEnd k Q R ⟨l, m, q⟩ * pathEnd k Q R ⟨i, j, p⟩ = 0 := by
  ext x
  simp only [Module.End.mul_apply, pathEnd_mk, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]

/-- Linear extension of the covariant path action on the underlying path basis. It is an
anti-homomorphism on `PathAlgebra`; passing to `BookPathAlgebra` reverses that order. -/
noncomputable def pathLinearEnd (R : QuiverRepresentation k Q) :
    PathAlgebra k Q →ₗ[k] Module.End k (DirectSum Q R.obj) :=
  Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (pathEnd k Q R x)

theorem pathLinearEnd_single (R : QuiverRepresentation k Q) (x : QuiverPathIndex Q) (c : k) :
    pathLinearEnd k Q R (Finsupp.single x c) = c • pathEnd k Q R x := by
  change (Finsupp.lsum k fun x => (LinearMap.id : k →ₗ[k] k).smulRight (pathEnd k Q R x))
      (Finsupp.single x c) = c • pathEnd k Q R x
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq]

theorem pathLinearEnd_ofPath (R : QuiverRepresentation k Q) (x : QuiverPathIndex Q) :
    pathLinearEnd k Q R (PathAlgebra.ofPath (k := k) x) = pathEnd k Q R x := by
  rw [PathAlgebra.ofPath, pathLinearEnd_single, one_smul]

theorem pathLinearEnd_compSingle (R : QuiverRepresentation k Q)
    (x y : QuiverPathIndex Q) :
    pathLinearEnd k Q R (PathAlgebra.compSingle x y) =
      pathEnd k Q R y * pathEnd k Q R x := by
  obtain ⟨i, j, p⟩ := x
  obtain ⟨l, m, q⟩ := y
  by_cases h : j = l
  · subst h
    rw [PathAlgebra.compSingle_eq, pathLinearEnd_single, one_smul, pathEnd_comp]
  · rw [PathAlgebra.compSingle_eq_zero _ _ h, map_zero, pathEnd_comp_zero k Q R p q h]

/-- The covariant path action reverses multiplication on the source-to-target implementation. -/
theorem pathLinearEnd_mul (R : QuiverRepresentation k Q) (f g : PathAlgebra k Q) :
    pathLinearEnd k Q R (f * g) = pathLinearEnd k Q R g * pathLinearEnd k Q R f := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, mul_add]
  | single x a =>
    induction g using PathAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, add_mul]
    | single y b =>
      rw [PathAlgebra.single_mul_single, map_smul, pathLinearEnd_compSingle,
        pathLinearEnd_single, pathLinearEnd_single, smul_mul_smul_comm]
      ac_rfl

/-- The path action as a linear map out of the exact book-facing algebra. -/
noncomputable def toEndₗ (R : QuiverRepresentation k Q) :
    BookPathAlgebra k Q →ₗ[k] Module.End k (DirectSum Q R.obj) where
  toFun a := pathLinearEnd k Q R a.unop
  map_add' a b := by rw [MulOpposite.unop_add, map_add]
  map_smul' c a := by simp

@[simp] theorem toEndₗ_ofPath (R : QuiverRepresentation k Q) (x : QuiverPathIndex Q) :
    toEndₗ k Q R (ofPath (k := k) x) = pathEnd k Q R x :=
  pathLinearEnd_ofPath k Q R x

theorem sum_lof_comp_component (R : QuiverRepresentation k Q) :
    (∑ i : Q, DirectSum.lof k Q R.obj i ∘ₗ DirectSum.component k Q R.obj i) =
      LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  conv_rhs => rw [← DirectSum.sum_univ_of x]
  exact Finset.sum_congr rfl fun i _ => by
    rw [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]

theorem toEndₗ_one (R : QuiverRepresentation k Q) : toEndₗ k Q R 1 = 1 := by
  change pathLinearEnd k Q R 1 = 1
  rw [PathAlgebra.one_eq_ofPath_sum, map_sum, Module.End.one_eq_id,
    ← sum_lof_comp_component k Q R]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pathLinearEnd_ofPath, pathEnd_mk, pathMap_nil, LinearMap.id_comp]

theorem toEndₗ_mul (R : QuiverRepresentation k Q) (a b : BookPathAlgebra k Q) :
    toEndₗ k Q R (a * b) = toEndₗ k Q R a * toEndₗ k Q R b := by
  change pathLinearEnd k Q R (b.unop * a.unop) =
    pathLinearEnd k Q R a.unop * pathLinearEnd k Q R b.unop
  exact pathLinearEnd_mul k Q R b.unop a.unop

/-- The left `BookPathAlgebra` action on `⊕ᵢ R.obj i` reconstructed from a quiver
representation. -/
noncomputable def toEnd (R : QuiverRepresentation k Q) :
    BookPathAlgebra k Q →ₐ[k] Module.End k (DirectSum Q R.obj) :=
  AlgHom.ofLinearMap (toEndₗ k Q R) (toEndₗ_one k Q R) (toEndₗ_mul k Q R)

@[simp] theorem toEnd_apply (R : QuiverRepresentation k Q) (a : BookPathAlgebra k Q) :
    toEnd k Q R a = toEndₗ k Q R a :=
  rfl

theorem toEnd_ofPath (R : QuiverRepresentation k Q) (x : QuiverPathIndex Q) :
    toEnd k Q R (ofPath (k := k) x) = pathEnd k Q R x := by
  rw [toEnd_apply, toEndₗ_ofPath]

/-- The left `BookPathAlgebra` module reconstructed from a quiver representation. -/
@[reducible] noncomputable def reverseModule (R : QuiverRepresentation k Q) :
    Module (BookPathAlgebra k Q) (DirectSum Q R.obj) :=
  Module.compHom _ (toEnd k Q R).toRingHom

theorem reverseModule_smul_def (R : QuiverRepresentation k Q) (a : BookPathAlgebra k Q)
    (x : DirectSum Q R.obj) :
    (letI := reverseModule k Q R; a • x) = toEnd k Q R a x :=
  rfl

theorem reverseModule_isScalarTower (R : QuiverRepresentation k Q) :
    letI := reverseModule k Q R
    IsScalarTower k (BookPathAlgebra k Q) (DirectSum Q R.obj) := by
  letI := reverseModule k Q R
  refine ⟨fun c a x => ?_⟩
  change toEnd k Q R (c • a) x = c • toEnd k Q R a x
  rw [map_smul, LinearMap.smul_apply]

@[simp] theorem arrowMap_coe_apply {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    {i j : Q} (a : i ⟶ j) (x : vertexSpace (k := k) (V := V) i) :
    ((arrowMap (k := k) (V := V) a x : vertexSpace (k := k) (V := V) j) : V) =
      (ofArrow (k := k) a : BookPathAlgebra k Q) • (x : V) :=
  rfl

theorem vertexProj_mem_vertexSpace {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    (i : Q) (x : V) :
    vertexProj (k := k) (V := V) i x ∈ vertexSpace (k := k) (V := V) i :=
  LinearMap.mem_range_self _ x

theorem vertexProj_eq_self_of_mem {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    {i : Q} {x : V} (hx : x ∈ vertexSpace (k := k) (V := V) i) :
    vertexProj (k := k) (V := V) i x = x := by
  obtain ⟨y, rfl⟩ := hx
  simp only [vertexProj_apply, ← mul_smul, trivialPath]
  rw [ofPath_mul_ofPath, Quiver.Path.nil_comp]

theorem vertexProj_comp_of_ne {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    {i j : Q} (h : i ≠ j) :
    (vertexProj (k := k) (V := V) i).comp (vertexProj (k := k) (V := V) j) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, vertexProj_apply, ← mul_smul, LinearMap.zero_apply,
    trivialPath]
  rw [ofPath_mul_ofPath_eq_zero Quiver.Path.nil Quiver.Path.nil h.symm, zero_smul]

theorem sum_vertexProj_eq_one {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V] :
    (∑ i : Q, vertexProj (k := k) (V := V) i) = 1 := by
  change (∑ i : Q, moduleEnd (k := k) (V := V) (trivialPath (k := k) (Q := Q) i)) = 1
  rw [← map_sum, sum_trivialPaths_eq_one, map_one]

/-- The spaces `p_iV` form the internal direct-sum decomposition of a book-facing module. -/
theorem isInternal_vertexSpace {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V] :
    DirectSum.IsInternal (fun i : Q => vertexSpace (k := k) (V := V) i) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hxsup
    have hker : (⨆ (j) (_ : j ≠ i), vertexSpace (k := k) (V := V) j) ≤
        LinearMap.ker (vertexProj (k := k) (V := V) i) := by
      refine iSup₂_le fun j hj => ?_
      change LinearMap.range (vertexProj (k := k) (V := V) j) ≤ _
      rw [LinearMap.range_le_ker_iff]
      exact vertexProj_comp_of_ne k Q hj.symm
    have hzero : vertexProj (k := k) (V := V) i x = 0 := by
      rw [← LinearMap.mem_ker]
      exact hker hxsup
    rw [← vertexProj_eq_self_of_mem k Q hx, hzero]
  · rw [eq_top_iff]
    intro x _
    have hsum : (∑ i : Q, vertexProj (k := k) (V := V) i) x = x := by
      rw [sum_vertexProj_eq_one k Q, Module.End.one_apply]
    rw [← hsum, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (vertexProj_mem_vertexSpace k Q i x)

/-- A module isomorphism restricts to an isomorphism of the extracted quiver representations. -/
noncomputable def forwardRepEquiv {V W : Type*}
    [AddCommGroup V] [Module k V] [Module (BookPathAlgebra k Q) V]
    [IsScalarTower k (BookPathAlgebra k Q) V]
    [AddCommGroup W] [Module k W] [Module (BookPathAlgebra k Q) W]
    [IsScalarTower k (BookPathAlgebra k Q) W]
    (e : V ≃ₗ[BookPathAlgebra k Q] W) :
    QuiverRepresentationEquiv k Q (forwardRep (k := k) (Q := Q) (V := V))
      (forwardRep (k := k) (Q := Q) (V := W)) where
  equivAt i := LinearEquiv.ofLinear
    (LinearMap.codRestrict _
      ((e.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSpace (k := k) (V := V) i)))
      (fun (x : vertexSpace (k := k) (V := V) i) => by
        refine ⟨e (x : V), ?_⟩
        rw [vertexProj_apply, ← e.map_smul, ← vertexProj_apply,
          vertexProj_eq_self_of_mem k Q x.2]
        rfl))
    (LinearMap.codRestrict _
      ((e.symm.restrictScalars k).toLinearMap.comp
        (Submodule.subtype (vertexSpace (k := k) (V := W) i)))
      (fun (x : vertexSpace (k := k) (V := W) i) => by
        refine ⟨e.symm (x : W), ?_⟩
        rw [vertexProj_apply, ← e.symm.map_smul, ← vertexProj_apply,
          vertexProj_eq_self_of_mem k Q x.2]
        rfl))
    (by
      refine LinearMap.ext fun x => ?_
      let xw : vertexSpace (k := k) (V := W) i := x
      apply Subtype.ext
      exact e.apply_symm_apply (xw : W))
    (by
      refine LinearMap.ext fun x => ?_
      let xv : vertexSpace (k := k) (V := V) i := x
      apply Subtype.ext
      exact e.symm_apply_apply (xv : V))
  commutes a x := by
    apply Subtype.ext
    let xv : vertexSpace (k := k) (V := V) _ := x
    change e ((ofArrow (k := k) a : BookPathAlgebra k Q) • (xv : V)) =
      (ofArrow (k := k) a : BookPathAlgebra k Q) • e (xv : V)
    exact e.map_smul _ _

/-- A nontrivial book-facing basis path factors as its final arrow times its initial path. -/
theorem ofPath_cons {i j l : Q} (p : Quiver.Path i j) (a : j ⟶ l) :
    (ofPath (k := k) (⟨i, l, p.cons a⟩ : QuiverPathIndex Q) : BookPathAlgebra k Q) =
      ofArrow (k := k) a * ofPath (k := k) (⟨i, j, p⟩ : QuiverPathIndex Q) := by
  rw [ofArrow, ofPath_mul_ofPath, Quiver.Path.comp_toPath_eq_cons]

/-- Acting by a basis path on its source vertex space agrees with the composite quiver map. -/
theorem ofPath_smul_eq_pathMap {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    {i j : Q} (p : Quiver.Path i j) :
    ∀ y : vertexSpace (k := k) (V := V) i,
      (ofPath (k := k) (⟨i, j, p⟩ : QuiverPathIndex Q) : BookPathAlgebra k Q) • (y : V) =
        (vertexSpace (k := k) (V := V) j).subtype
          (pathMap k Q (forwardRep (k := k) (Q := Q) (V := V)) p y) := by
  induction p with
  | nil =>
      intro y
      rw [pathMap_nil, LinearMap.id_apply]
      change (trivialPath (k := k) (Q := Q) i : BookPathAlgebra k Q) • (y : V) = (y : V)
      rw [← vertexProj_apply]
      exact vertexProj_eq_self_of_mem k Q y.2
  | cons p a ih =>
      intro y
      rw [ofPath_cons, mul_smul, ih y]
      let z : vertexSpace (k := k) (V := V) _ :=
        pathMap k Q (forwardRep (k := k) (Q := Q) (V := V)) p y
      change (ofArrow (k := k) a : BookPathAlgebra k Q) • (z : V) =
        (vertexSpace (k := k) (V := V) _).subtype (arrowMap (k := k) (V := V) a z)
      exact (arrowMap_coe_apply k Q a z).symm

attribute [local instance] reverseModule

local instance forwardReverse_tower {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V] :
    IsScalarTower k (BookPathAlgebra k Q)
      (DirectSum Q (forwardRep (k := k) (Q := Q) (V := V)).obj) :=
  reverseModule_isScalarTower k Q (forwardRep (k := k) (Q := Q) (V := V))

private noncomputable abbrev coeV {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V] :
    DirectSum Q (forwardRep (k := k) (Q := Q) (V := V)).obj →ₗ[k] V :=
  DirectSum.coeLinearMap (fun i => vertexSpace (k := k) (V := V) i)

private theorem coeV_lof {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    (i : Q) (x : (forwardRep (k := k) (Q := Q) (V := V)).obj i) :
    coeV (k := k) (Q := Q) (V := V)
        (DirectSum.lof k Q (forwardRep (k := k) (Q := Q) (V := V)).obj i x) =
      (vertexSpace (k := k) (V := V) i).subtype x :=
  DirectSum.coeLinearMap_lof (fun i => vertexSpace (k := k) (V := V) i) i x

theorem coeLinearMap_pathEnd {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    (x : QuiverPathIndex Q)
    (m : DirectSum Q (forwardRep (k := k) (Q := Q) (V := V)).obj) :
    coeV (k := k) (Q := Q) (V := V)
        (pathEnd k Q (forwardRep (k := k) (Q := Q) (V := V)) x m) =
      (ofPath (k := k) x : BookPathAlgebra k Q) •
        coeV (k := k) (Q := Q) (V := V) m := by
  obtain ⟨i, j, p⟩ := x
  have key : (coeV (k := k) (Q := Q) (V := V)).comp
        (pathEnd k Q (forwardRep (k := k) (Q := Q) (V := V)) ⟨i, j, p⟩) =
      (moduleEnd (k := k) (V := V) (ofPath (k := k) ⟨i, j, p⟩)).comp
        (coeV (k := k) (Q := Q) (V := V)) := by
    refine DirectSum.linearMap_ext k fun l => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, pathEnd_mk]
    rw [coeV_lof, coeV_lof]
    by_cases h : l = i
    · subst h
      rw [DirectSum.component.lof_self]
      exact (ofPath_smul_eq_pathMap k Q p y).symm
    · rw [DirectSum.component.of, dif_neg h]
      have hzero : (vertexSpace (k := k) (V := V) j).subtype
          (pathMap k Q (forwardRep (k := k) (Q := Q) (V := V)) p
            (0 : vertexSpace (k := k) (V := V) i)) = 0 := by
        change (((vertexSpace (k := k) (V := V) j).subtype.comp
          (pathMap k Q (forwardRep (k := k) (Q := Q) (V := V)) p))
            (0 : vertexSpace (k := k) (V := V) i)) = 0
        exact LinearMap.map_zero _
      calc
        _ = 0 := hzero
        _ = (ofPath (k := k) (⟨i, j, p⟩ : QuiverPathIndex Q) : BookPathAlgebra k Q) •
            (vertexSpace (k := k) (V := V) l).subtype y := by
          symm
          have hy : (trivialPath (k := k) (Q := Q) l : BookPathAlgebra k Q) •
                (vertexSpace (k := k) (V := V) l).subtype y =
              (vertexSpace (k := k) (V := V) l).subtype y := by
            rw [← vertexProj_apply]
            exact vertexProj_eq_self_of_mem k Q y.2
          rw [← hy, ← mul_smul]
          change (ofPath (k := k) ⟨i, j, p⟩ *
              ofPath (k := k) ⟨l, l, Quiver.Path.nil⟩) • _ = 0
          rw [ofPath_mul_ofPath_eq_zero Quiver.Path.nil p h, zero_smul]
  have h := LinearMap.congr_fun key m
  simpa only [LinearMap.comp_apply, moduleEnd_apply] using h

theorem coeLinearMap_toEnd {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V]
    (a : BookPathAlgebra k Q)
    (m : DirectSum Q (forwardRep (k := k) (Q := Q) (V := V)).obj) :
    coeV (k := k) (Q := Q) (V := V)
        (toEnd k Q (forwardRep (k := k) (Q := Q) (V := V)) a m) =
      a • coeV (k := k) (Q := Q) (V := V) m := by
  let f := a.unop
  change coeV (k := k) (Q := Q) (V := V)
      (pathLinearEnd k Q (forwardRep (k := k) (Q := Q) (V := V)) f m) =
    (MulOpposite.op f : BookPathAlgebra k Q) • coeV (k := k) (Q := Q) (V := V) m
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, map_add, h₁, h₂,
      MulOpposite.op_add, add_smul]
  | single x c =>
      have hs : (MulOpposite.op (Finsupp.single x c : PathAlgebra k Q) :
          BookPathAlgebra k Q) = c • ofPath (k := k) x := by
        apply MulOpposite.unop_injective
        exact (PathAlgebra.smul_single_one c x).symm
      rw [pathLinearEnd_single, LinearMap.smul_apply, map_smul, coeLinearMap_pathEnd,
        hs, smul_assoc]

/-- Reassembling the extracted vertex spaces recovers the original book-facing module. -/
noncomputable def moduleRoundTrip {V : Type*} [AddCommGroup V] [Module k V]
    [Module (BookPathAlgebra k Q) V] [IsScalarTower k (BookPathAlgebra k Q) V] :
    DirectSum Q (forwardRep (k := k) (Q := Q) (V := V)).obj ≃ₗ[BookPathAlgebra k Q] V :=
  let e : DirectSum Q (forwardRep (k := k) (Q := Q) (V := V)).obj ≃ₗ[k] V :=
    LinearEquiv.ofBijective (coeV (k := k) (Q := Q) (V := V))
      (isInternal_vertexSpace k Q)
  { toFun := e
    map_add' := e.map_add
    map_smul' := coeLinearMap_toEnd k Q
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

omit [DecidableEq Q] [Fintype Q] in
/-- A representation isomorphism intertwines the composites along every path. -/
theorem repEquiv_pathMap {R S : QuiverRepresentation k Q}
    (e : QuiverRepresentationEquiv k Q R S) {i j : Q} (p : Quiver.Path i j)
    (x : R.obj i) :
    e.equivAt j (pathMap k Q R p x) = pathMap k Q S p (e.equivAt i x) := by
  induction p with
  | nil => simp only [pathMap_nil, LinearMap.id_apply]
  | cons p a ih =>
      simp only [pathMap_cons, LinearMap.comp_apply]
      rw [e.commutes a, ih]

/-- The direct sum of the vertexwise equivalences of two isomorphic representations. -/
noncomputable def reverseLinearEquiv {R S : QuiverRepresentation k Q}
    (e : QuiverRepresentationEquiv k Q R S) :
    DirectSum Q R.obj ≃ₗ[k] DirectSum Q S.obj :=
  DirectSum.congrLinearEquiv fun i => e.equivAt i

omit [Fintype Q] in
theorem reverseLinearEquiv_pathEnd {R S : QuiverRepresentation k Q}
    (e : QuiverRepresentationEquiv k Q R S) (x : QuiverPathIndex Q)
    (m : DirectSum Q R.obj) :
    reverseLinearEquiv k Q e (pathEnd k Q R x m) =
      pathEnd k Q S x (reverseLinearEquiv k Q e m) := by
  induction m using DirectSum.induction_on with
  | zero => simp
  | add m n hm hn =>
      rw [map_add, map_add, hm, hn]
      exact (map_add (pathEnd k Q S x) _ _).symm.trans
        (congrArg (pathEnd k Q S x) ((reverseLinearEquiv k Q e).map_add m n).symm)
  | of l z =>
      rw [← DirectSum.lof_eq_of k]
      obtain ⟨i, j, p⟩ := x
      simp only [pathEnd_mk, LinearMap.comp_apply]
      by_cases h : l = i
      · subst h
        rw [DirectSum.component.lof_self]
        simp only [reverseLinearEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
        rw [DirectSum.component.lof_self]
        exact congrArg (DirectSum.lof k Q S.obj j) (repEquiv_pathMap k Q e p z)
      · rw [DirectSum.component.of, dif_neg h, map_zero, map_zero]
        simp only [reverseLinearEquiv, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
          DirectSum.component.of, dif_neg h, map_zero]

theorem reverseLinearEquiv_toEnd {R S : QuiverRepresentation k Q}
    (e : QuiverRepresentationEquiv k Q R S) (a : BookPathAlgebra k Q)
    (m : DirectSum Q R.obj) :
    reverseLinearEquiv k Q e (toEnd k Q R a m) =
      toEnd k Q S a (reverseLinearEquiv k Q e m) := by
  let f := a.unop
  change reverseLinearEquiv k Q e (pathLinearEnd k Q R f m) =
    pathLinearEnd k Q S f (reverseLinearEquiv k Q e m)
  induction f using PathAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply, map_add, h₁, h₂]
      exact (congrArg
        (fun g : Module.End k (DirectSum Q S.obj) => g (reverseLinearEquiv k Q e m))
        (map_add (pathLinearEnd k Q S) f₁ f₂)).symm
  | single x c =>
      rw [pathLinearEnd_single, LinearMap.smul_apply, map_smul, pathLinearEnd_single,
        LinearMap.smul_apply, reverseLinearEquiv_pathEnd]

/-- Isomorphic quiver representations yield isomorphic reconstructed path modules. -/
noncomputable def reverseModuleEquiv {R S : QuiverRepresentation k Q}
    (e : QuiverRepresentationEquiv k Q R S) :
    letI := reverseModule k Q R
    letI := reverseModule k Q S
    DirectSum Q R.obj ≃ₗ[BookPathAlgebra k Q] DirectSum Q S.obj := by
  letI := reverseModule k Q R
  letI := reverseModule k Q S
  let ek := reverseLinearEquiv k Q e
  exact {
    toFun := ek
    map_add' := ek.map_add
    map_smul' := fun a m => reverseLinearEquiv_toEnd k Q e a m
    invFun := ek.symm
    left_inv := ek.left_inv
    right_inv := ek.right_inv }

/-- The additive group on a direct sum of vector spaces. -/
local instance directSumAddCommGroup (R : QuiverRepresentation k Q) :
    AddCommGroup (DirectSum Q R.obj) :=
  Module.addCommMonoidToAddCommGroup k

local instance directSum_scalarTower (R : QuiverRepresentation k Q) :
    IsScalarTower k (BookPathAlgebra k Q) (DirectSum Q R.obj) :=
  reverseModule_isScalarTower k Q R

theorem vertexProj_reverseModule (R : QuiverRepresentation k Q) (i : Q)
    (m : DirectSum Q R.obj) :
    (vertexProj (k := k) (V := DirectSum Q R.obj) i) m =
      DirectSum.lof k Q R.obj i (DirectSum.component k Q R.obj i m) := by
  rw [vertexProj_apply, reverseModule_smul_def, trivialPath, toEnd_ofPath, pathEnd_mk]
  simp only [LinearMap.comp_apply, pathMap_nil, LinearMap.id_coe, id_eq]

theorem vertexSpace_reverseModule (R : QuiverRepresentation k Q) (i : Q) :
    vertexSpace (k := k) (V := DirectSum Q R.obj) i =
      LinearMap.range (DirectSum.lof k Q R.obj i) := by
  apply le_antisymm
  · change LinearMap.range (vertexProj (k := k) (V := DirectSum Q R.obj) i) ≤ _
    rintro x ⟨m, rfl⟩
    rw [vertexProj_reverseModule]
    exact LinearMap.mem_range_self _ _
  · rintro x ⟨y, rfl⟩
    change _ ∈ LinearMap.range (vertexProj (k := k) (V := DirectSum Q R.obj) i)
    exact ⟨_, by rw [vertexProj_reverseModule, DirectSum.component.lof_self]⟩

theorem lof_component_of_mem (R : QuiverRepresentation k Q) (i : Q)
    (y : vertexSpace (k := k) (V := DirectSum Q R.obj) i) :
    DirectSum.lof k Q R.obj i (DirectSum.component k Q R.obj i (y : DirectSum Q R.obj)) =
      (y : DirectSum Q R.obj) := by
  rw [← vertexProj_reverseModule]
  exact vertexProj_eq_self_of_mem k Q y.2

/-- The recovered `i`-th vertex space is canonically equivalent to the original `R.obj i`. -/
noncomputable def repEquivAt (R : QuiverRepresentation k Q) (i : Q) :
    R.obj i ≃ₗ[k] vertexSpace (k := k) (V := DirectSum Q R.obj) i :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ (DirectSum.lof k Q R.obj i)
      (fun y => by rw [vertexSpace_reverseModule]; exact LinearMap.mem_range_self _ y))
    ((DirectSum.component k Q R.obj i).comp
      (Submodule.subtype (vertexSpace (k := k) (V := DirectSum Q R.obj) i)))
    (by
      refine LinearMap.ext fun y => ?_
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        LinearMap.id_coe, id_eq]
      exact lof_component_of_mem k Q R i y)
    (by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
        DirectSum.component.lof_self, LinearMap.id_coe, id_eq])

@[simp] theorem repEquivAt_coe (R : QuiverRepresentation k Q) (i : Q) (x : R.obj i) :
    ((repEquivAt k Q R i x : vertexSpace (k := k) (V := DirectSum Q R.obj) i) :
      DirectSum Q R.obj) = DirectSum.lof k Q R.obj i x :=
  rfl

theorem repEquivAt_naturality (R : QuiverRepresentation k Q) {i j : Q}
    (a : i ⟶ j) (x : R.obj i) :
    repEquivAt k Q R j (R.mapLinear a x) =
      (forwardRep (k := k) (Q := Q) (V := DirectSum Q R.obj)).mapLinear a
        (repEquivAt k Q R i x) := by
  apply Subtype.ext
  change DirectSum.lof k Q R.obj j (R.mapLinear a x) =
    toEnd k Q R (ofArrow (k := k) a) (DirectSum.lof k Q R.obj i x)
  rw [ofArrow, toEnd_ofPath, pathEnd_mk]
  simp only [LinearMap.comp_apply, DirectSum.component.lof_self, pathMap_toPath]

/-- Reconstructing a module and extracting its vertex spaces recovers the original
representation. -/
noncomputable def repRoundTrip (R : QuiverRepresentation k Q) :
    QuiverRepresentationEquiv k Q R
      (forwardRep (k := k) (Q := Q) (V := DirectSum Q R.obj)) where
  equivAt i := repEquivAt k Q R i
  commutes a x := repEquivAt_naturality k Q R a x

/-- Reassemble a quiver representation into its direct-sum book-facing path module. -/
noncomputable def PathModule.ofQuiverRepresentation (R : QuiverRepresentation k Q) :
    PathModule k Q where
  carrier := DirectSum Q R.obj
  addCommGroup := Module.addCommMonoidToAddCommGroup k
  moduleField := inferInstance
  modulePathAlgebra := reverseModule k Q R
  scalarTower := reverseModule_isScalarTower k Q R

theorem PathModule.toQuiverRepresentation_rel {M N : PathModule k Q}
    (h : (pathModuleIsoSetoid k Q).r M N) :
    (quiverRepresentationIsoSetoid k Q).r
      (M.toQuiverRepresentation k Q) (N.toQuiverRepresentation k Q) := by
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  letI := N.addCommGroup
  letI := N.moduleField
  letI := N.modulePathAlgebra
  letI := N.scalarTower
  change Nonempty (M.carrier ≃ₗ[BookPathAlgebra k Q] N.carrier) at h
  exact ⟨forwardRepEquiv k Q h.some⟩

theorem PathModule.ofQuiverRepresentation_rel {R S : QuiverRepresentation k Q}
    (h : (quiverRepresentationIsoSetoid k Q).r R S) :
    (pathModuleIsoSetoid k Q).r
      (PathModule.ofQuiverRepresentation k Q R)
      (PathModule.ofQuiverRepresentation k Q S) := by
  letI : AddCommGroup (DirectSum Q R.obj) := Module.addCommMonoidToAddCommGroup k
  letI : Module (BookPathAlgebra k Q) (DirectSum Q R.obj) := reverseModule k Q R
  letI : AddCommGroup (DirectSum Q S.obj) := Module.addCommMonoidToAddCommGroup k
  letI : Module (BookPathAlgebra k Q) (DirectSum Q S.obj) := reverseModule k Q S
  change Nonempty (DirectSum Q R.obj ≃ₗ[BookPathAlgebra k Q] DirectSum Q S.obj)
  exact ⟨reverseModuleEquiv k Q h.some⟩

/-- The exact forward assignment on isomorphism classes. -/
noncomputable def moduleToRepresentationIsoClass :
    PathModuleIsoClass k Q → QuiverRepresentationIsoClass k Q :=
  Quotient.map (PathModule.toQuiverRepresentation k Q)
    (fun _ _ => PathModule.toQuiverRepresentation_rel k Q)

/-- The direct-sum reconstruction on isomorphism classes. -/
noncomputable def representationToModuleIsoClass :
    QuiverRepresentationIsoClass k Q → PathModuleIsoClass k Q :=
  Quotient.map (PathModule.ofQuiverRepresentation k Q)
    (fun _ _ => PathModule.ofQuiverRepresentation_rel k Q)

set_option maxHeartbeats 800000 in
-- Quotient induction expands both bundled round trips and needs extra elaboration time.
/-- The two exact assignments are inverse on isomorphism classes. -/
noncomputable def isoClassEquiv :
    PathModuleIsoClass k Q ≃ QuiverRepresentationIsoClass k Q where
  toFun := moduleToRepresentationIsoClass k Q
  invFun := representationToModuleIsoClass k Q
  left_inv := by
    intro x
    refine Quotient.inductionOn x fun M => ?_
    apply Quotient.sound
    letI := M.addCommGroup
    letI := M.moduleField
    letI := M.modulePathAlgebra
    letI := M.scalarTower
    let FR := forwardRep (k := k) (Q := Q) (V := M.carrier)
    letI : AddCommGroup (DirectSum Q FR.obj) := Module.addCommMonoidToAddCommGroup k
    letI : Module (BookPathAlgebra k Q) (DirectSum Q FR.obj) := reverseModule k Q FR
    change Nonempty
      (DirectSum Q (forwardRep (k := k) (Q := Q) (V := M.carrier)).obj ≃ₗ[BookPathAlgebra k Q]
        M.carrier)
    exact ⟨moduleRoundTrip k Q⟩
  right_inv := by
    intro x
    refine Quotient.inductionOn x fun R => ?_
    apply Quotient.sound
    letI : AddCommGroup (DirectSum Q R.obj) := Module.addCommMonoidToAddCommGroup k
    letI : Module (BookPathAlgebra k Q) (DirectSum Q R.obj) := reverseModule k Q R
    letI : IsScalarTower k (BookPathAlgebra k Q) (DirectSum Q R.obj) :=
      reverseModule_isScalarTower k Q R
    change (quiverRepresentationIsoSetoid k Q).r
      (PathModule.toQuiverRepresentation k Q (PathModule.ofQuiverRepresentation k Q R)) R
    have h : (quiverRepresentationIsoSetoid k Q).r R
        (forwardRep (k := k) (Q := Q) (V := DirectSum Q R.obj)) :=
      ⟨repRoundTrip k Q R⟩
    exact (quiverRepresentationIsoSetoid k Q).iseqv.symm h

/-- A bundled module realizes the book's reverse assignment when its carrier is linearly
equivalent to `⊕_i V_i` and every basis path acts by the corresponding composite arrow map. -/
def IsDirectSumRealization (R : QuiverRepresentation k Q) (M : PathModule k Q) : Prop :=
  letI := M.addCommGroup
  letI := M.moduleField
  letI := M.modulePathAlgebra
  letI := M.scalarTower
  ∃ e : M.carrier ≃ₗ[k] DirectSum Q R.obj,
    ∀ (i j : Q) (p : Quiver.Path i j) (x : M.carrier),
      e ((ofPath (k := k) (⟨i, j, p⟩ : QuiverPathIndex Q) : BookPathAlgebra k Q) • x) =
        pathEnd k Q R ⟨i, j, p⟩ (e x)

/-- **The exact book claim, with both assignments specified.** There is a bijection between
isomorphism classes of left modules over `BookPathAlgebra k Q` and representations of `Q`; its
forward map is exactly `V ↦ (p_iV)`, and its inverse is represented by `⊕_i V_i` with path action
given by composition of the arrow maps.

The equivalence below is induced by the explicit forward and direct-sum constructions above. -/
theorem exists_isoClassEquiv_induced_by_book_assignments :
    ∃ e : PathModuleIsoClass.{u, v, q, max v w} k Q ≃
        QuiverRepresentationIsoClass.{u, v, q, max v w} k Q,
      (∀ M : PathModule.{u, v, max v w, q} k Q,
        e (Quotient.mk _ M) = Quotient.mk _ (M.toQuiverRepresentation k Q)) ∧
      (∀ R : QuiverRepresentation.{u, v, max v w, q} k Q,
        ∃ M : PathModule.{u, v, max v w, q} k Q,
        IsDirectSumRealization k Q R M ∧
          e.symm (Quotient.mk _ R) = Quotient.mk _ M) := by
  refine ⟨isoClassEquiv k Q, ?_, ?_⟩
  · intro M
    rfl
  · intro R
    refine ⟨PathModule.ofQuiverRepresentation k Q R, ?_, ?_⟩
    · change ∃ e : DirectSum Q R.obj ≃ₗ[k] DirectSum Q R.obj,
        ∀ (i j : Q) (p : Quiver.Path i j) (x : DirectSum Q R.obj),
          e (toEnd k Q R (ofPath (k := k) (⟨i, j, p⟩ : QuiverPathIndex Q)) x) =
            pathEnd k Q R ⟨i, j, p⟩ (e x)
      refine ⟨LinearEquiv.refl k _, ?_⟩
      intro i j p x
      simp only [LinearEquiv.refl_apply, toEnd_ofPath]
    · rfl

end IsoClasses

end Etingof.BookPathAlgebra
