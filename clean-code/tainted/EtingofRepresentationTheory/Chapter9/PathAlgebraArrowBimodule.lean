import EtingofRepresentationTheory.Chapter9.PathAlgebraVertexSubalgebra
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# The arrow `S`-bimodule of a path algebra

In the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i)), write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra (embedded by `f := vertexEmbedding : S →+* A`), and let `V` be the `S`-bimodule
spanned by the arrows of `Q`. This file constructs `V` together with the two commuting
`S`-actions (by source and target vertex idempotents) and its inclusion into `A`.

## Contents

* `Etingof.PathAlgebra.ArrowIndex Q`: the type of arrows `Σ a b, (a ⟶ b)`, with `src`/`tgt`.
* `Etingof.PathAlgebra.arrowElt` / `arrowInclusion`: an arrow as the corresponding length-`1`
  path element of `A`, and its `k`-linear extension `V → A`.
* `Etingof.PathAlgebra.vertexEmbedding_mul_arrowElt` /
  `arrowElt_mul_vertexEmbedding`: left/right multiplication of an arrow by `f s` scales it by
  the source/target coordinate `s (src)` / `s (tgt)`. These realize the two `S`-actions inside
  `A` and are what make the resolution's boundary map `d` well-defined.
* `Etingof.PathAlgebra.arrowSourceModule` / `arrowTargetModule`: the source and target
  `S = (Q → k)`-module structures on `V` (as explicit `Module` values, to avoid a
  typeclass diamond on the single carrier `ArrowIndex Q →₀ k`), the two commuting halves of the
  `S`-bimodule structure.

The arrow bimodule `V`, together with the induction functor `A ⊗_S -` from
`Chapter9/PathAlgebraInduction.lean`, forms the standard short complex
`0 → A ⊗_S (V ⊗_S M) → A ⊗_S M → M → 0`.
-/

universe u

open Etingof

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-- The type of arrows of `Q`: a source, a target, and an arrow between them. The `k`-span
`ArrowIndex Q →₀ k` is the arrow bimodule `V`. -/
abbrev ArrowIndex (Q : Type u) [Quiver.{u + 1} Q] := Σ (a : Q) (b : Q), (a ⟶ b)

namespace ArrowIndex

/-- The source vertex of an arrow. -/
def src (x : ArrowIndex Q) : Q := x.1

/-- The target vertex of an arrow. -/
def tgt (x : ArrowIndex Q) : Q := x.2.1

/-- The oriented path (of length `1`) underlying an arrow. -/
def toPathIndex (x : ArrowIndex Q) : QuiverPathIndex Q := ⟨x.1, x.2.1, x.2.2.toPath⟩

omit [DecidableEq Q] in
@[simp] theorem src_mk (a b : Q) (e : a ⟶ b) : ArrowIndex.src (⟨a, b, e⟩ : ArrowIndex Q) = a := rfl
omit [DecidableEq Q] in
@[simp] theorem tgt_mk (a b : Q) (e : a ⟶ b) : ArrowIndex.tgt (⟨a, b, e⟩ : ArrowIndex Q) = b := rfl

end ArrowIndex

/-- An arrow `x`, viewed as the corresponding length-`1` basis path element of `A`. -/
noncomputable def arrowElt (x : ArrowIndex Q) : PathAlgebra k Q := ofPath x.toPathIndex

/-- **The arrow bimodule `V` as a subspace of `A`.** The `k`-linear map `V = (ArrowIndex Q →₀ k)
→ A` extending `x ↦ arrowElt x`, i.e. a formal `k`-combination of arrows to the corresponding
combination of length-`1` paths. -/
noncomputable def arrowInclusion : (ArrowIndex Q →₀ k) →ₗ[k] PathAlgebra k Q :=
  Finsupp.linearCombination k arrowElt

@[simp] theorem arrowInclusion_single (x : ArrowIndex Q) (c : k) :
    arrowInclusion (Finsupp.single x c) = c • arrowElt (k := k) x := by
  rw [arrowInclusion, Finsupp.linearCombination_single]

/-- The product of two basis path elements is their concatenation `compSingle` (both have
coefficient `1`). -/
theorem ofPath_mul_ofPath (p q : QuiverPathIndex Q) :
    (ofPath p : PathAlgebra k Q) * ofPath q = compSingle p q := by
  rw [ofPath, ofPath, single_mul_single, one_mul, one_smul]

/-! ## The two `S`-module structures on `V`

`V = ArrowIndex Q →₀ k` carries two commuting `S = (Q → k)`-module structures, scaling the
arrow component `⟨a, b, e⟩` by the source coordinate `s a` (left action) and by the target
coordinate `s b` (right action). We package these as explicit `Module` values rather than
instances: both act on the single carrier `ArrowIndex Q →₀ k`, so registering both as instances
would create a diamond. The tensor-product construction that uses them selects the appropriate one
via a type synonym. -/

variable (k Q) in
/-- The twisted scalar action `(s • v) i = s (wt i) * v i` on `ArrowIndex Q →₀ k`, where
`wt : ArrowIndex Q → Q` is a "weight" assigning each arrow a vertex (`src` or `tgt`). -/
noncomputable def wSMul (wt : ArrowIndex Q → Q) (s : Q → k) (v : ArrowIndex Q →₀ k) :
    ArrowIndex Q →₀ k :=
  Finsupp.ofSupportFinite (fun i => s (wt i) * v i)
    (v.support.finite_toSet.subset (by
      intro i hi
      simp only [Function.mem_support, Finset.mem_coe, Finsupp.mem_support_iff] at hi ⊢
      exact fun h => hi (by rw [h, mul_zero])))

omit [DecidableEq Q] in
@[simp] theorem wSMul_apply (wt : ArrowIndex Q → Q) (s : Q → k) (v : ArrowIndex Q →₀ k)
    (i : ArrowIndex Q) : wSMul k Q wt s v i = s (wt i) * v i := by
  rw [wSMul, Finsupp.ofSupportFinite_coe]

variable (k Q) in
/-- The `(Q → k)`-module structure on `ArrowIndex Q →₀ k` with scalar action twisted by
`wt : ArrowIndex Q → Q`. Both the source and target `S`-actions of the arrow bimodule are
instances of this construction (with `wt = src` and `wt = tgt`). -/
@[reducible] noncomputable def wModule (wt : ArrowIndex Q → Q) :
    Module (Q → k) (ArrowIndex Q →₀ k) where
  smul := wSMul k Q wt
  one_smul v := by
    change wSMul k Q wt 1 v = v
    ext i; rw [wSMul_apply, Pi.one_apply, one_mul]
  mul_smul s t v := by
    change wSMul k Q wt (s * t) v = wSMul k Q wt s (wSMul k Q wt t v)
    ext i; simp only [wSMul_apply, Pi.mul_apply]; ring
  smul_zero s := by
    change wSMul k Q wt s 0 = 0
    ext i; simp
  smul_add s v w := by
    change wSMul k Q wt s (v + w) = wSMul k Q wt s v + wSMul k Q wt s w
    ext i; simp only [wSMul_apply, Finsupp.add_apply]; ring
  add_smul s t v := by
    change wSMul k Q wt (s + t) v = wSMul k Q wt s v + wSMul k Q wt t v
    ext i; simp only [wSMul_apply, Finsupp.add_apply, Pi.add_apply]; ring
  zero_smul v := by
    change wSMul k Q wt 0 v = 0
    ext i; simp

variable (k Q) in
/-- **Left (source) `S`-action of the arrow bimodule `V`.** Scales `⟨a, b, e⟩` by `s a`; under
`arrowInclusion` it corresponds to left multiplication by `f s` (`vertexEmbedding_mul_arrowElt`). -/
@[reducible] noncomputable def arrowSourceModule : Module (Q → k) (ArrowIndex Q →₀ k) :=
  wModule k Q ArrowIndex.src

variable (k Q) in
/-- **Right (target) `S`-action of the arrow bimodule `V`.** Scales `⟨a, b, e⟩` by `s b`; under
`arrowInclusion` it corresponds to right multiplication by `f s` (`arrowElt_mul_vertexEmbedding`).
This is the action over which the inner tensor `V ⊗_S M` is formed. -/
@[reducible] noncomputable def arrowTargetModule : Module (Q → k) (ArrowIndex Q →₀ k) :=
  wModule k Q ArrowIndex.tgt

omit [DecidableEq Q] in
/-- **The bimodule compatibility.** The source and target `S`-actions commute, so `V` is an
`(S, S)`-bimodule. -/
theorem wSMul_comm (s t : Q → k) (v : ArrowIndex Q →₀ k) :
    wSMul k Q ArrowIndex.src s (wSMul k Q ArrowIndex.tgt t v)
      = wSMul k Q ArrowIndex.tgt t (wSMul k Q ArrowIndex.src s v) := by
  ext i
  rw [wSMul_apply, wSMul_apply, wSMul_apply, wSMul_apply]
  ring

/-! ## Vertex idempotents acting on arrows -/

/-- Left multiplication of an arrow by a trivial-path idempotent `eᵢ`: the arrow survives when
`i` is its source, and is killed otherwise. -/
theorem vertexIdem_mul_arrowElt (i : Q) (x : ArrowIndex Q) :
    (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) : PathAlgebra k Q) * arrowElt x
      = if i = x.src then arrowElt x else 0 := by
  obtain ⟨a, b, e⟩ := x
  rw [arrowElt, ArrowIndex.toPathIndex, ofPath_mul_ofPath, compSingle_nil_left]
  rfl

/-- Right multiplication of an arrow by a trivial-path idempotent `eᵢ`: the arrow survives when
`i` is its target, and is killed otherwise. -/
theorem arrowElt_mul_vertexIdem (i : Q) (x : ArrowIndex Q) :
    arrowElt x * (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) : PathAlgebra k Q)
      = if x.tgt = i then arrowElt x else 0 := by
  obtain ⟨a, b, e⟩ := x
  rw [arrowElt, ArrowIndex.toPathIndex, ofPath_mul_ofPath, compSingle_nil_right]
  rfl

variable [Fintype Q]

/-- **Source action inside `A`.** Left multiplication of an arrow by `f s = vertexEmbedding s`
scales it by the source coordinate `s (src x)`: `f s · x = s(src x) • x`. This is the left
`S`-action of the arrow bimodule, realized inside `A`. -/
theorem vertexEmbedding_mul_arrowElt (s : Q → k) (x : ArrowIndex Q) :
    vertexEmbedding k Q s * arrowElt x = s x.src • arrowElt (k := k) x := by
  have hsingle : ∀ i : Q, (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (s i)
        : PathAlgebra k Q) = s i • (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)) := by
    intro i; rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [vertexEmbedding_apply, Finset.sum_congr rfl fun i _ => hsingle i, Finset.sum_mul]
  have hterm : ∀ i : Q,
      (s i • ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)) * arrowElt x
        = if i = x.src then s i • arrowElt (k := k) x else 0 := by
    intro i
    rw [smul_mul, vertexIdem_mul_arrowElt]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ x.src,
    if_pos (Finset.mem_univ _)]

/-- **Target action inside `A`.** Right multiplication of an arrow by `f s = vertexEmbedding s`
scales it by the target coordinate `s (tgt x)`: `x · f s = s(tgt x) • x`. This is the right
`S`-action of the arrow bimodule, realized inside `A`. -/
theorem arrowElt_mul_vertexEmbedding (s : Q → k) (x : ArrowIndex Q) :
    arrowElt x * vertexEmbedding k Q s = s x.tgt • arrowElt (k := k) x := by
  have hsingle : ∀ i : Q, (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (s i)
        : PathAlgebra k Q) = s i • (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)) := by
    intro i; rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [vertexEmbedding_apply, Finset.sum_congr rfl fun i _ => hsingle i, Finset.mul_sum]
  have hterm : ∀ i : Q,
      arrowElt x * (s i • ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q))
        = if x.tgt = i then s i • arrowElt (k := k) x else 0 := by
    intro i
    rw [mul_smul', arrowElt_mul_vertexIdem]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq Finset.univ x.tgt,
    if_pos (Finset.mem_univ _)]

end Etingof.PathAlgebra
