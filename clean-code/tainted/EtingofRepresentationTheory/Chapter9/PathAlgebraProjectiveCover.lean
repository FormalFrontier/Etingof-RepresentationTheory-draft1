import EtingofRepresentationTheory.Chapter2.Definition2_8_4
import EtingofRepresentationTheory.Chapter9.PathAlgebraVertexSubalgebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finsupp.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Projective covers of the path algebra and the Hom-space identification

For the path algebra `A = PathAlgebra k Q` of a finite quiver, the principal left ideals
`Pᵢ = A · eᵢ`, where `eᵢ = ofPath ⟨i, i, nil⟩` is the trivial-path idempotent at vertex `i`,
are the projective covers of the simple modules once `Q` is acyclic
(`Chapter9/PathAlgebraVertexCovers.lean`). This file constructs that family and proves the
Hom-space identification that carries the mathematical content of Problem 9.4.6 (ii):

`Hom_A(A·eᵢ, A·eⱼ) ≅ eᵢ · A · eⱼ ≅ (paths i → j) →₀ k.`

The first isomorphism is the standard idempotent fact `Hom_A(A·e, M) ≅ e·M` (a hom `f` is
determined by `f(e) ∈ e·M`, and every `x ∈ e·M` gives back the hom `y ↦ y·x`). The second is
the observation that `eᵢ · A · eⱼ` is spanned by the basis paths from `i` to `j`.

## Main definitions and results

* `Etingof.PathAlgebra.pathAlgebraProj k Q i`: the principal left ideal `A · eᵢ`, as the
  left submodule `Submodule.span A {eᵢ}` with its inherited `A`- and `k`-module structures.
* `Etingof.PathAlgebra.pathAlgebraHomEquiv`:
  `(A·eᵢ →ₗ[A] A·eⱼ) ≃ₗ[k] (Quiver.Path i j →₀ k)`, the Hom-space identification.
-/

universe u

open Etingof
open scoped Classical

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-- The underlying finsupp coefficient of a path-algebra element at a basis index. Because
`PathAlgebra k Q` is a `def` (not a reducible `abbrev`), there is no `FunLike` instance to apply
elements as functions directly; `coeff f x` is the coefficient `f x` of the underlying finsupp. -/
noncomputable def coeff (f : PathAlgebra k Q) (x : QuiverPathIndex Q) : k :=
  @DFunLike.coe (QuiverPathIndex Q →₀ k) (QuiverPathIndex Q) (fun _ => k) _ f x

@[simp] theorem coeff_zero (x : QuiverPathIndex Q) : coeff (0 : PathAlgebra k Q) x = 0 := rfl

theorem coeff_add (f g : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (f + g) x = coeff f x + coeff g x :=
  Finsupp.add_apply _ _ _

theorem coeff_smul (c : k) (f : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (c • f) x = c * coeff f x :=
  Finsupp.smul_apply _ _ _

@[simp] theorem coeff_single (x y : QuiverPathIndex Q) (c : k) :
    coeff (Finsupp.single x c : PathAlgebra k Q) y = if x = y then c else 0 :=
  Finsupp.single_apply

/-- Two path-algebra elements are equal iff all their coefficients agree. -/
theorem coeff_ext {f g : PathAlgebra k Q} (h : ∀ x, coeff f x = coeff g x) : f = g :=
  Finsupp.ext h

/-- The trivial-path idempotent `eᵢ = ofPath ⟨i, i, nil⟩` at vertex `i`. -/
noncomputable def eIdem (i : Q) : PathAlgebra k Q := ofPath ⟨i, i, Quiver.Path.nil⟩

/-- `eᵢ` is idempotent: `eᵢ * eᵢ = eᵢ`. -/
theorem eIdem_mul_self (i : Q) : (eIdem i : PathAlgebra k Q) * eIdem i = eIdem i := by
  rw [eIdem, ofPath_nil_mul_ofPath_nil, if_pos rfl]

/-- Coefficient of `eᵢ * a` at an index `x`: it keeps the paths whose source is `i` and kills
the others. -/
theorem coeff_eIdem_mul (i : Q) (a : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (eIdem i * a) x = if x.1 = i then coeff a x else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [mul_zero]
  | add u v hu hv =>
    rw [mul_add, coeff_add, hu, hv, coeff_add]
    split_ifs <;> ring
  | single y c =>
    obtain ⟨s, t, p⟩ := y
    simp only [eIdem, ofPath]
    rw [single_mul_single, one_mul, compSingle_nil_left]
    by_cases his : i = s
    · rw [if_pos his]; subst his
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hx : x = (⟨i, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [coeff_single]
      · simp [coeff_single, Ne.symm hx]
    · rw [if_neg his, smul_zero, coeff_zero]
      by_cases hx : x = (⟨s, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [Ne.symm his]
      · simp [coeff_single, Ne.symm hx]

/-- Coefficient of `a * eⱼ` at an index `x`: it keeps the paths whose target is `j` and kills
the others. -/
theorem coeff_mul_eIdem (j : Q) (a : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (a * eIdem j) x = if x.2.1 = j then coeff a x else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add u v hu hv =>
    rw [add_mul, coeff_add, hu, hv, coeff_add]
    split_ifs <;> ring
  | single y c =>
    obtain ⟨s, t, p⟩ := y
    simp only [eIdem, ofPath]
    rw [single_mul_single, mul_one, compSingle_nil_right]
    by_cases htj : t = j
    · rw [if_pos htj]; subst htj
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hx : x = (⟨s, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [coeff_single]
      · simp [coeff_single, Ne.symm hx]
    · rw [if_neg htj, smul_zero, coeff_zero]
      by_cases hx : x = (⟨s, t, p⟩ : QuiverPathIndex Q)
      · subst hx; simp [htj]
      · simp [coeff_single, Ne.symm hx]

/-- Coefficient of `eᵢ * a * eⱼ` at an index `x = ⟨s, t, p⟩`: it keeps the paths from `i` to `j`
and kills the others. This is the combinatorial heart of the identification
`eᵢ A eⱼ ≅ paths i → j`. -/
theorem coeff_eIdem_mul_eIdem (i j : Q) (a : PathAlgebra k Q) (x : QuiverPathIndex Q) :
    coeff (eIdem i * a * eIdem j) x = if x.1 = i ∧ x.2.1 = j then coeff a x else 0 := by
  rw [coeff_mul_eIdem, coeff_eIdem_mul]
  by_cases htj : x.2.1 = j
  · by_cases his : x.1 = i
    · rw [if_pos htj, if_pos his, if_pos ⟨his, htj⟩]
    · rw [if_pos htj, if_neg his, if_neg (fun h => his h.1)]
  · rw [if_neg htj, if_neg (fun h => htj h.2)]

/-! ## The principal left ideal `Pᵢ = A · eᵢ` -/

variable (k Q) in
/-- The principal left submodule `Pᵢ = A · eᵢ` generated by the trivial-path idempotent `eᵢ`.
Its inherited `A`-, `k`-module and scalar-tower instances are found automatically from
`Submodule.module'`. Note `PathAlgebra k Q` lives in `Type (u + 1)`, so its principal submodules
do too.

For a finite acyclic quiver, `Pᵢ` is the projective cover of the vertex simple module `Sᵢ`; that
is proved in `Chapter9/PathAlgebraVertexCovers.lean`, where it is packaged as an
`Etingof.ProjectiveCover`. -/
noncomputable abbrev pathAlgebraProj (i : Q) : Type (u + 1) :=
  ↥(Submodule.span (PathAlgebra k Q) {eIdem (k := k) i})

variable (k Q) in
/-- `eᵢ` as an element of its own principal submodule `Pᵢ = A · eᵢ`. -/
noncomputable def eIdemMem (i : Q) : pathAlgebraProj k Q i :=
  ⟨eIdem i, Submodule.mem_span_singleton_self _⟩

@[simp] theorem eIdemMem_val (i : Q) : ((eIdemMem k Q i : pathAlgebraProj k Q i) : PathAlgebra k Q)
    = eIdem i := rfl

/-! ## The two-sided cut `eᵢ · A · eⱼ` -/

variable (k Q) in
/-- The two-sided cut `eᵢ · A · eⱼ`, realized as the range of the `k`-linear map
`x ↦ eᵢ * x * eⱼ`. It is spanned by the basis paths from `i` to `j`. -/
noncomputable def eCut (i j : Q) : Submodule k (PathAlgebra k Q) :=
  LinearMap.range (LinearMap.mulLeftRight k (eIdem (k := k) i, eIdem (k := k) j))

theorem mem_eCut_iff {i j : Q} {x : PathAlgebra k Q} :
    x ∈ eCut k Q i j ↔ ∃ a, eIdem i * a * eIdem j = x := by
  simp only [eCut, LinearMap.mem_range, LinearMap.mulLeftRight_apply]

/-- Elements of the cut are fixed by `eᵢ` on the left. -/
theorem eCut_eIdem_mul {i j : Q} {x : PathAlgebra k Q} (hx : x ∈ eCut k Q i j) :
    eIdem i * x = x := by
  obtain ⟨a, rfl⟩ := mem_eCut_iff.mp hx
  rw [← mul_assoc, ← mul_assoc, eIdem_mul_self]

/-- Elements of the cut are fixed by `eⱼ` on the right. -/
theorem eCut_mul_eIdem {i j : Q} {x : PathAlgebra k Q} (hx : x ∈ eCut k Q i j) :
    x * eIdem j = x := by
  obtain ⟨a, rfl⟩ := mem_eCut_iff.mp hx
  rw [mul_assoc, eIdem_mul_self]

/-- Any element of the codomain submodule `A · eⱼ` is fixed by `eⱼ` on the right. -/
theorem mul_eIdem_of_mem_span {j : Q} {y : PathAlgebra k Q}
    (hy : y ∈ Submodule.span (PathAlgebra k Q) {eIdem j}) : y * eIdem j = y := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [smul_eq_mul, mul_assoc, eIdem_mul_self]

/-! ## Step 1: `Hom_A(A·eᵢ, A·eⱼ) ≅ eᵢ · A · eⱼ` -/

/-- Left-idempotent fixing of the evaluation `f(eᵢ)`: for an `A`-linear `f : A·eᵢ → A·eⱼ`,
`eᵢ · f(eᵢ) = f(eᵢ)`. This is `A`-linearity of `f` together with `eᵢ² = eᵢ`. -/
theorem eIdem_mul_hom_val {i j : Q} (f : pathAlgebraProj k Q i →ₗ[PathAlgebra k Q]
    pathAlgebraProj k Q j) :
    eIdem i * ((f (eIdemMem k Q i) : pathAlgebraProj k Q j) : PathAlgebra k Q)
      = ((f (eIdemMem k Q i) : pathAlgebraProj k Q j) : PathAlgebra k Q) := by
  have hfix : (eIdem (k := k) i • eIdemMem k Q i : pathAlgebraProj k Q i) = eIdemMem k Q i := by
    apply Subtype.ext
    change eIdem i * eIdem i = eIdem i
    exact eIdem_mul_self i
  have hms : f (eIdem (k := k) i • eIdemMem k Q i) = eIdem (k := k) i • f (eIdemMem k Q i) :=
    f.map_smul (eIdem i) (eIdemMem k Q i)
  have key : (eIdem (k := k) i • f (eIdemMem k Q i) : pathAlgebraProj k Q j)
      = f (eIdemMem k Q i) := by
    rw [← hms, hfix]
  exact congrArg Subtype.val key

/-- The evaluation-at-`eᵢ` map lands in the cut `eᵢ · A · eⱼ`. -/
theorem hom_val_mem_eCut {i j : Q} (f : pathAlgebraProj k Q i →ₗ[PathAlgebra k Q]
    pathAlgebraProj k Q j) :
    ((f (eIdemMem k Q i) : pathAlgebraProj k Q j) : PathAlgebra k Q) ∈ eCut k Q i j := by
  refine mem_eCut_iff.mpr ⟨((f (eIdemMem k Q i) : pathAlgebraProj k Q j) : PathAlgebra k Q), ?_⟩
  rw [mul_assoc, mul_eIdem_of_mem_span (f (eIdemMem k Q i)).2, eIdem_mul_hom_val]

/-- **Step 1, forward map.** Evaluation at `eᵢ`, corestricted to the cut:
`f ↦ f(eᵢ) ∈ eᵢ · A · eⱼ`. -/
noncomputable def homToCut (i j : Q) :
    (pathAlgebraProj k Q i →ₗ[PathAlgebra k Q] pathAlgebraProj k Q j) →ₗ[k] ↥(eCut k Q i j) where
  toFun f := ⟨((f (eIdemMem k Q i) : pathAlgebraProj k Q j) : PathAlgebra k Q), hom_val_mem_eCut f⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' c f := by apply Subtype.ext; simp

/-- **Step 1, backward map.** Right multiplication by an element `x` of the cut:
`x ↦ (y ↦ y · x)`. -/
noncomputable def cutToHom (i j : Q) :
    ↥(eCut k Q i j) →ₗ[k]
      (pathAlgebraProj k Q i →ₗ[PathAlgebra k Q] pathAlgebraProj k Q j) where
  toFun x := LinearMap.codRestrict (Submodule.span (PathAlgebra k Q) {eIdem j})
    ((LinearMap.mulRight (PathAlgebra k Q) (x : PathAlgebra k Q)).comp
      (Submodule.span (PathAlgebra k Q) {eIdem i}).subtype)
    (fun y => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulRight_apply]
      refine Submodule.mem_span_singleton.mpr ⟨(y : PathAlgebra k Q) * x, ?_⟩
      rw [smul_eq_mul, mul_assoc, eCut_mul_eIdem x.2])
  map_add' x y := LinearMap.ext fun z => Subtype.ext <| by
    change (z : PathAlgebra k Q) * ((x + y : ↥(eCut k Q i j)) : PathAlgebra k Q)
      = (z : PathAlgebra k Q) * x + (z : PathAlgebra k Q) * y
    rw [Submodule.coe_add, mul_add]
  map_smul' c x := LinearMap.ext fun z => Subtype.ext <| by
    change (z : PathAlgebra k Q) * ((c • x : ↥(eCut k Q i j)) : PathAlgebra k Q)
      = c • ((z : PathAlgebra k Q) * x)
    rw [Submodule.coe_smul, mul_smul_comm]

/-- **Step 1.** The idempotent Hom identification `Hom_A(A·eᵢ, A·eⱼ) ≃ₗ[k] eᵢ · A · eⱼ`. -/
noncomputable def homCutEquiv (i j : Q) :
    (pathAlgebraProj k Q i →ₗ[PathAlgebra k Q] pathAlgebraProj k Q j) ≃ₗ[k] ↥(eCut k Q i j) :=
  LinearEquiv.ofLinear (homToCut i j) (cutToHom i j)
    (by
      -- `homToCut ∘ cutToHom = id`: evaluate `y ↦ y·x` at `eᵢ`, giving `eᵢ·x = x`.
      refine LinearMap.ext fun x => Subtype.ext ?_
      exact eCut_eIdem_mul x.2)
    (by
      -- `cutToHom ∘ homToCut = id`: `y ↦ y·f(eᵢ)` equals `f` by `A`-linearity.
      refine LinearMap.ext fun f => LinearMap.ext fun y => Subtype.ext ?_
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
      have hy : y = a • eIdemMem k Q i := Subtype.ext ha.symm
      change (y : PathAlgebra k Q) *
          ((f (eIdemMem k Q i) : pathAlgebraProj k Q j) : PathAlgebra k Q)
        = ((f y : pathAlgebraProj k Q j) : PathAlgebra k Q)
      rw [hy, map_smul, Submodule.coe_smul, Submodule.coe_smul, eIdemMem_val, smul_eq_mul,
        smul_eq_mul, mul_assoc, eIdem_mul_hom_val])

/-! ## Step 2: `eᵢ · A · eⱼ ≅ (paths i → j) →₀ k` -/

/-- The embedding of the `i → j` paths into all oriented paths, `p ↦ ⟨i, j, p⟩`. -/
def pathEmb (i j : Q) : Quiver.Path i j ↪ QuiverPathIndex Q where
  toFun p := ⟨i, j, p⟩
  inj' p q h := by simpa using h

@[simp] theorem pathEmb_apply (i j : Q) (p : Quiver.Path i j) :
    pathEmb i j p = (⟨i, j, p⟩ : QuiverPathIndex Q) := rfl

/-- An index is in the range of `pathEmb i j` iff its source is `i` and target is `j`. -/
theorem mem_range_pathEmb_iff {i j : Q} {y : QuiverPathIndex Q} :
    y ∈ Set.range (pathEmb i j) ↔ y.1 = i ∧ y.2.1 = j := by
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨rfl, rfl⟩
  · obtain ⟨a, b, p⟩ := y
    rintro ⟨rfl, rfl⟩
    exact ⟨p, rfl⟩

/-- Coefficients of a cut element vanish off the `i → j` paths. -/
theorem coeff_eq_zero_of_mem_eCut {i j : Q} {x : PathAlgebra k Q} (hx : x ∈ eCut k Q i j)
    {y : QuiverPathIndex Q} (hy : ¬ (y.1 = i ∧ y.2.1 = j)) : coeff x y = 0 := by
  obtain ⟨a, rfl⟩ := mem_eCut_iff.mp hx
  rw [coeff_eIdem_mul_eIdem, if_neg hy]

/-- The `embDomain` of any `i → j` finsupp lands in the cut `eᵢ · A · eⱼ`. -/
theorem embDomain_mem_eCut {i j : Q} (c : Quiver.Path i j →₀ k) :
    (Finsupp.embDomain (pathEmb i j) c : PathAlgebra k Q) ∈ eCut k Q i j := by
  refine mem_eCut_iff.mpr ⟨Finsupp.embDomain (pathEmb i j) c, coeff_ext fun y => ?_⟩
  rw [coeff_eIdem_mul_eIdem]
  by_cases hy : y.1 = i ∧ y.2.1 = j
  · rw [if_pos hy]
  · rw [if_neg hy]
    exact (Finsupp.embDomain_notin_range _ _ _
      (fun h => hy (mem_range_pathEmb_iff.mp h))).symm

/-- **Step 2.** The identification `eᵢ · A · eⱼ ≃ₗ[k] (paths i → j) →₀ k`: restrict a cut element's
support to the `i → j` paths (forward) and `embDomain` back (inverse). -/
noncomputable def cutPathEquiv (i j : Q) :
    ↥(eCut k Q i j) ≃ₗ[k] (Quiver.Path i j →₀ k) where
  toFun x := Finsupp.comapDomain (pathEmb i j) (x : PathAlgebra k Q)
    ((pathEmb i j).injective.injOn)
  map_add' x y := by
    refine Finsupp.ext fun p => ?_
    rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.comapDomain_apply,
      Finsupp.comapDomain_apply]
    exact congrFun (congrArg _ (Submodule.coe_add x y)) _
  map_smul' c x := by
    refine Finsupp.ext fun p => ?_
    rw [RingHom.id_apply, Finsupp.comapDomain_apply, Finsupp.smul_apply,
      Finsupp.comapDomain_apply]
    exact congrFun (congrArg _ (Submodule.coe_smul c x)) _
  invFun c := ⟨Finsupp.embDomain (pathEmb i j) c, embDomain_mem_eCut c⟩
  left_inv x := by
    refine Subtype.ext (coeff_ext fun y => ?_)
    simp only [coeff]
    by_cases hy : ∃ p, pathEmb i j p = y
    · obtain ⟨p, rfl⟩ := hy
      rw [Finsupp.embDomain_apply_self, Finsupp.comapDomain_apply]
    · have hnotin : y ∉ Set.range (pathEmb i j) := fun h => hy (Set.mem_range.mp h)
      rw [Finsupp.embDomain_notin_range _ _ _ hnotin]
      exact (coeff_eq_zero_of_mem_eCut x.2
        (fun h => hnotin (mem_range_pathEmb_iff.mpr h))).symm
  right_inv c := by
    refine Finsupp.ext fun p => ?_
    rw [Finsupp.comapDomain_apply]
    exact Finsupp.embDomain_apply_self _ _ _

/-! ## The Hom-space identification `Hom_A(A·eᵢ, A·eⱼ) ≅ (paths i → j) →₀ k` -/

variable (k Q) in
/-- **The Hom-space identification (Problem 9.4.6 (ii)).**
`Hom_A(A·eᵢ, A·eⱼ) ≃ₗ[k] (Quiver.Path i j →₀ k)`, composing the idempotent Hom identification
`homCutEquiv` with the cut/paths identification `cutPathEquiv`. -/
noncomputable def pathAlgebraHomEquiv (i j : Q) :
    (pathAlgebraProj k Q i →ₗ[PathAlgebra k Q] pathAlgebraProj k Q j) ≃ₗ[k]
      (Quiver.Path i j →₀ k) :=
  (homCutEquiv i j).trans (cutPathEquiv i j)

end Etingof.PathAlgebra
