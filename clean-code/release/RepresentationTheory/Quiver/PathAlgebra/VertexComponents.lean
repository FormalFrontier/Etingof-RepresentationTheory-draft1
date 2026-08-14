/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import RepresentationTheory.Quiver.PathAlgebra
import RepresentationTheory.FunctionRingHom
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finsupp.Basic

set_option backward.isDefEq.respectTransparency false



universe u

open scoped Classical

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]


/-- Returns the coefficient of a quiver path index in an element of the ambient algebra. -/
noncomputable def coeff (f : Quiver.PathAlgebra k Q) (x : Quiver.BundledPath Q) : k :=
  @DFunLike.coe (Quiver.BundledPath Q →₀ k) (Quiver.BundledPath Q) (fun _ => k) _ f x

/-- Every path coefficient of the zero element is zero. -/
@[simp] theorem coeff_zero (x : Quiver.BundledPath Q) : coeff (0 : Quiver.PathAlgebra k Q) x = 0 := rfl

/-- The coefficient of a sum is the sum of the corresponding coefficients. -/
theorem coeff_add (f g : Quiver.PathAlgebra k Q) (x : Quiver.BundledPath Q) :
    coeff (f + g) x = coeff f x + coeff g x :=
  Finsupp.add_apply _ _ _

/-- Taking a path coefficient commutes with scalar multiplication. -/
theorem coeff_smul (c : k) (f : Quiver.PathAlgebra k Q) (x : Quiver.BundledPath Q) :
    coeff (c • f) x = c * coeff f x :=
  Finsupp.smul_apply _ _ _

/-- The coefficient of a singleton-supported element is its value at the selected index and zero elsewhere. -/
@[simp] theorem coeff_single (x y : Quiver.BundledPath Q) (c : k) :
    coeff (Finsupp.single x c : Quiver.PathAlgebra k Q) y = if x = y then c else 0 :=
  Finsupp.single_apply


/-- Two algebra elements are equal when all of their path coefficients agree. -/
theorem ext {f g : Quiver.PathAlgebra k Q} (h : ∀ x, coeff f x = coeff g x) : f = g :=
  Finsupp.ext h


/-- Associates an element of the ambient quiver algebra to each vertex. -/
noncomputable def auxiliaryVertexIdempotent (i : Q) : Quiver.PathAlgebra k Q := ofPath ⟨i, i, Quiver.Path.nil⟩


/-- The algebra element associated to a vertex is idempotent. -/
theorem auxiliaryVertexIdempotent_mul_self (i : Q) : (auxiliaryVertexIdempotent i : Quiver.PathAlgebra k Q) * auxiliaryVertexIdempotent i = auxiliaryVertexIdempotent i := by
  rw [auxiliaryVertexIdempotent, auxiliary_nilPath_mul, if_pos rfl]


/-- Left multiplication by a vertex idempotent retains exactly the coefficients whose source is that vertex. -/
theorem coeff_vertexIdempotent_mul (i : Q) (a : Quiver.PathAlgebra k Q) (x : Quiver.BundledPath Q) :
    coeff (auxiliaryVertexIdempotent i * a) x = if x.1 = i then coeff a x else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [mul_zero]
  | add u v hu hv =>
    rw [mul_add, coeff_add, hu, hv, coeff_add]
    split_ifs <;> ring
  | single y c =>
    obtain ⟨s, t, p⟩ := y
    simp only [auxiliaryVertexIdempotent, ofPath]
    rw [single_mul_single, one_mul, mulPath_vertexPath]
    by_cases his : i = s
    · rw [if_pos his]; subst his
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hx : x = (⟨i, t, p⟩ : Quiver.BundledPath Q)
      · subst hx; simp [coeff_single]
      · simp [coeff_single, Ne.symm hx]
    · rw [if_neg his, smul_zero, coeff_zero]
      by_cases hx : x = (⟨s, t, p⟩ : Quiver.BundledPath Q)
      · subst hx; simp [Ne.symm his]
      · simp [coeff_single, Ne.symm hx]


/-- Right multiplication by a vertex idempotent retains exactly the coefficients whose target is that vertex. -/
theorem coeff_mul_vertexIdempotent (j : Q) (a : Quiver.PathAlgebra k Q) (x : Quiver.BundledPath Q) :
    coeff (a * auxiliaryVertexIdempotent j) x = if x.2.1 = j then coeff a x else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp [zero_mul]
  | add u v hu hv =>
    rw [add_mul, coeff_add, hu, hv, coeff_add]
    split_ifs <;> ring
  | single y c =>
    obtain ⟨s, t, p⟩ := y
    simp only [auxiliaryVertexIdempotent, ofPath]
    rw [single_mul_single, mul_one, mulPath_pathVertex]
    by_cases htj : t = j
    · rw [if_pos htj]; subst htj
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      by_cases hx : x = (⟨s, t, p⟩ : Quiver.BundledPath Q)
      · subst hx; simp [coeff_single]
      · simp [coeff_single, Ne.symm hx]
    · rw [if_neg htj, smul_zero, coeff_zero]
      by_cases hx : x = (⟨s, t, p⟩ : Quiver.BundledPath Q)
      · subst hx; simp [htj]
      · simp [coeff_single, Ne.symm hx]


/-- Multiplication by vertex idempotents on both sides retains coefficients with the prescribed source and target. -/
theorem coeff_vertexIdempotent_mul_vertexIdempotent (i j : Q) (a : Quiver.PathAlgebra k Q) (x : Quiver.BundledPath Q) :
    coeff (auxiliaryVertexIdempotent i * a * auxiliaryVertexIdempotent j) x = if x.1 = i ∧ x.2.1 = j then coeff a x else 0 := by
  rw [coeff_mul_vertexIdempotent, coeff_vertexIdempotent_mul]
  by_cases htj : x.2.1 = j
  · by_cases his : x.1 = i
    · rw [if_pos htj, if_pos his, if_pos ⟨his, htj⟩]
    · rw [if_pos htj, if_neg his, if_neg (fun h => his h.1)]
  · rw [if_neg htj, if_neg (fun h => htj h.2)]



variable (k Q) in

/-- An auxiliary vertex-indexed type whose internal structure is not exposed by the displayed signature. -/
noncomputable abbrev AuxiliaryVertexSpace (i : Q) : Type (u + 1) :=
  ↥(Submodule.span (Quiver.PathAlgebra k Q) {auxiliaryVertexIdempotent (k := k) i})

variable (k Q) in

/-- Provides an auxiliary element of the opaque vertex-indexed type. -/
noncomputable def auxiliaryVertexElement (i : Q) : AuxiliaryVertexSpace k Q i :=
  ⟨auxiliaryVertexIdempotent i, Submodule.mem_span_singleton_self _⟩

/-- The underlying algebra element of the auxiliary vertex element is the corresponding vertex idempotent. -/
@[simp] theorem coe_auxiliaryVertexElement (i : Q) : ((auxiliaryVertexElement k Q i : AuxiliaryVertexSpace k Q i) : Quiver.PathAlgebra k Q)
    = auxiliaryVertexIdempotent i := rfl



variable (k Q) in

/-- The submodule of algebra elements belonging to a prescribed pair of vertices. -/
noncomputable def pathComponent (i j : Q) : Submodule k (Quiver.PathAlgebra k Q) :=
  LinearMap.range (LinearMap.mulLeftRight k (auxiliaryVertexIdempotent (k := k) i, auxiliaryVertexIdempotent (k := k) j))

/-- An algebra element lies in a source-target component exactly when it is obtained by multiplying some element by the corresponding vertex idempotents. -/
theorem mem_pathComponent_iff {i j : Q} {x : Quiver.PathAlgebra k Q} :
    x ∈ pathComponent k Q i j ↔ ∃ a, auxiliaryVertexIdempotent i * a * auxiliaryVertexIdempotent j = x := by
  simp only [pathComponent, LinearMap.mem_range, LinearMap.mulLeftRight_apply]


/-- The source vertex idempotent acts as a left identity on its source-target component. -/
theorem vertexIdempotent_mul_eq_of_mem_pathComponent {i j : Q} {x : Quiver.PathAlgebra k Q} (hx : x ∈ pathComponent k Q i j) :
    auxiliaryVertexIdempotent i * x = x := by
  obtain ⟨a, rfl⟩ := mem_pathComponent_iff.mp hx
  rw [← mul_assoc, ← mul_assoc, auxiliaryVertexIdempotent_mul_self]


/-- The target vertex idempotent acts as a right identity on its source-target component. -/
theorem mul_vertexIdempotent_eq_of_mem_pathComponent {i j : Q} {x : Quiver.PathAlgebra k Q} (hx : x ∈ pathComponent k Q i j) :
    x * auxiliaryVertexIdempotent j = x := by
  obtain ⟨a, rfl⟩ := mem_pathComponent_iff.mp hx
  rw [mul_assoc, auxiliaryVertexIdempotent_mul_self]


/-- Right multiplication by a vertex idempotent fixes every element in its singleton span. -/
theorem mul_vertexIdempotent_eq_of_mem_span {j : Q} {y : Quiver.PathAlgebra k Q}
    (hy : y ∈ Submodule.span (Quiver.PathAlgebra k Q) {auxiliaryVertexIdempotent j}) : y * auxiliaryVertexIdempotent j = y := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [smul_eq_mul, mul_assoc, auxiliaryVertexIdempotent_mul_self]




/-- The source vertex idempotent fixes the underlying value obtained by applying a linear map to the auxiliary vertex element. -/
theorem vertexIdempotent_mul_apply_auxiliaryVertexElement {i j : Q} (f : AuxiliaryVertexSpace k Q i →ₗ[Quiver.PathAlgebra k Q]
    AuxiliaryVertexSpace k Q j) :
    auxiliaryVertexIdempotent i * ((f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q)
      = ((f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q) := by
  have hfix : (auxiliaryVertexIdempotent (k := k) i • auxiliaryVertexElement k Q i : AuxiliaryVertexSpace k Q i) = auxiliaryVertexElement k Q i := by
    apply Subtype.ext
    change auxiliaryVertexIdempotent i * auxiliaryVertexIdempotent i = auxiliaryVertexIdempotent i
    exact auxiliaryVertexIdempotent_mul_self i
  have hms : f (auxiliaryVertexIdempotent (k := k) i • auxiliaryVertexElement k Q i) = auxiliaryVertexIdempotent (k := k) i • f (auxiliaryVertexElement k Q i) :=
    f.map_smul (auxiliaryVertexIdempotent i) (auxiliaryVertexElement k Q i)
  have key : (auxiliaryVertexIdempotent (k := k) i • f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j)
      = f (auxiliaryVertexElement k Q i) := by
    rw [← hms, hfix]
  exact congrArg Subtype.val key


/-- Applying a linear map to the auxiliary source element yields an algebra element in the matching source-target component. -/
theorem apply_auxiliaryVertexElement_mem_pathComponent {i j : Q} (f : AuxiliaryVertexSpace k Q i →ₗ[Quiver.PathAlgebra k Q]
    AuxiliaryVertexSpace k Q j) :
    ((f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q) ∈ pathComponent k Q i j := by
  refine mem_pathComponent_iff.mpr ⟨((f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q), ?_⟩
  rw [mul_assoc, mul_vertexIdempotent_eq_of_mem_span (f (auxiliaryVertexElement k Q i)).2, vertexIdempotent_mul_apply_auxiliaryVertexElement]


/-- Maps linear maps between two vertex spaces linearly into the corresponding source-target component. -/
noncomputable def linearMapToPathComponent (i j : Q) :
    (AuxiliaryVertexSpace k Q i →ₗ[Quiver.PathAlgebra k Q] AuxiliaryVertexSpace k Q j) →ₗ[k] ↥(pathComponent k Q i j) where
  toFun f := ⟨((f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q), apply_auxiliaryVertexElement_mem_pathComponent f⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' c f := by apply Subtype.ext; simp


/-- Maps a fixed source-target component linearly to linear maps between the associated vertex spaces. -/
noncomputable def pathComponentToLinearMap (i j : Q) :
    ↥(pathComponent k Q i j) →ₗ[k]
      (AuxiliaryVertexSpace k Q i →ₗ[Quiver.PathAlgebra k Q] AuxiliaryVertexSpace k Q j) where
  toFun x := LinearMap.codRestrict (Submodule.span (Quiver.PathAlgebra k Q) {auxiliaryVertexIdempotent j})
    ((LinearMap.mulRight (Quiver.PathAlgebra k Q) (x : Quiver.PathAlgebra k Q)).comp
      (Submodule.span (Quiver.PathAlgebra k Q) {auxiliaryVertexIdempotent i}).subtype)
    (fun y => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulRight_apply]
      refine Submodule.mem_span_singleton.mpr ⟨(y : Quiver.PathAlgebra k Q) * x, ?_⟩
      rw [smul_eq_mul, mul_assoc, mul_vertexIdempotent_eq_of_mem_pathComponent x.2])
  map_add' x y := LinearMap.ext fun z => Subtype.ext <| by
    change (z : Quiver.PathAlgebra k Q) * ((x + y : ↥(pathComponent k Q i j)) : Quiver.PathAlgebra k Q)
      = (z : Quiver.PathAlgebra k Q) * x + (z : Quiver.PathAlgebra k Q) * y
    rw [Submodule.coe_add, mul_add]
  map_smul' c x := LinearMap.ext fun z => Subtype.ext <| by
    change (z : Quiver.PathAlgebra k Q) * ((c • x : ↥(pathComponent k Q i j)) : Quiver.PathAlgebra k Q)
      = c • ((z : Quiver.PathAlgebra k Q) * x)
    rw [Submodule.coe_smul, mul_smul_comm]


/-- Identifies linear maps between two vertex spaces with the corresponding source-target component. -/
noncomputable def linearMapEquivPathComponent (i j : Q) :
    (AuxiliaryVertexSpace k Q i →ₗ[Quiver.PathAlgebra k Q] AuxiliaryVertexSpace k Q j) ≃ₗ[k] ↥(pathComponent k Q i j) :=
  LinearEquiv.ofLinear (linearMapToPathComponent i j) (pathComponentToLinearMap i j)
    (by
      -- `linearMapToPathComponent ∘ pathComponentToLinearMap = id`: evaluate `y ↦ y·x` at `eᵢ`, giving `eᵢ·x = x`.
      refine LinearMap.ext fun x => Subtype.ext ?_
      exact vertexIdempotent_mul_eq_of_mem_pathComponent x.2)
    (by
      -- `pathComponentToLinearMap ∘ linearMapToPathComponent = id`: `y ↦ y·f(eᵢ)` equals `f` by `A`-linearity.
      refine LinearMap.ext fun f => LinearMap.ext fun y => Subtype.ext ?_
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
      have hy : y = a • auxiliaryVertexElement k Q i := Subtype.ext ha.symm
      change (y : Quiver.PathAlgebra k Q) *
          ((f (auxiliaryVertexElement k Q i) : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q)
        = ((f y : AuxiliaryVertexSpace k Q j) : Quiver.PathAlgebra k Q)
      rw [hy, map_smul, Submodule.coe_smul, Submodule.coe_smul, coe_auxiliaryVertexElement, smul_eq_mul,
        smul_eq_mul, mul_assoc, vertexIdempotent_mul_apply_auxiliaryVertexElement])




/-- Embeds paths with fixed endpoints into the global quiver path index type. -/
def pathEmbedding (i j : Q) : Quiver.Path i j ↪ Quiver.BundledPath Q where
  toFun p := ⟨i, j, p⟩
  inj' p q h := by simpa using h

/-- The path embedding records a path together with its source and target vertices. -/
@[simp] theorem pathEmbedding_apply (i j : Q) (p : Quiver.Path i j) :
    pathEmbedding i j p = (⟨i, j, p⟩ : Quiver.BundledPath Q) := rfl


/-- A global path index belongs to the path embedding's range exactly when it has the specified source and target. -/
theorem mem_range_pathEmbedding_iff {i j : Q} {y : Quiver.BundledPath Q} :
    y ∈ Set.range (pathEmbedding i j) ↔ y.1 = i ∧ y.2.1 = j := by
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨rfl, rfl⟩
  · obtain ⟨a, b, p⟩ := y
    rintro ⟨rfl, rfl⟩
    exact ⟨p, rfl⟩


/-- An element of a fixed source-target component has zero coefficient outside that component. -/
theorem coeff_eq_zero_of_mem_pathComponent {i j : Q} {x : Quiver.PathAlgebra k Q} (hx : x ∈ pathComponent k Q i j)
    {y : Quiver.BundledPath Q} (hy : ¬ (y.1 = i ∧ y.2.1 = j)) : coeff x y = 0 := by
  obtain ⟨a, rfl⟩ := mem_pathComponent_iff.mp hx
  rw [coeff_vertexIdempotent_mul_vertexIdempotent, if_neg hy]


/-- Embedding a finitely supported function on paths into the global index type produces an element of the matching source-target component. -/
theorem embDomain_mem_pathComponent {i j : Q} (c : Quiver.Path i j →₀ k) :
    (Finsupp.embDomain (pathEmbedding i j) c : Quiver.PathAlgebra k Q) ∈ pathComponent k Q i j := by
  refine mem_pathComponent_iff.mpr ⟨Finsupp.embDomain (pathEmbedding i j) c, ext fun y => ?_⟩
  rw [coeff_vertexIdempotent_mul_vertexIdempotent]
  by_cases hy : y.1 = i ∧ y.2.1 = j
  · rw [if_pos hy]
  · rw [if_neg hy]
    exact (Finsupp.embDomain_notin_range _ _ _
      (fun h => hy (mem_range_pathEmbedding_iff.mp h))).symm


/-- Identifies a fixed source-target component linearly with finitely supported functions on paths between the vertices. -/
noncomputable def pathComponentEquivFinsupp (i j : Q) :
    ↥(pathComponent k Q i j) ≃ₗ[k] (Quiver.Path i j →₀ k) where
  toFun x := Finsupp.comapDomain (pathEmbedding i j) (x : Quiver.PathAlgebra k Q)
    ((pathEmbedding i j).injective.injOn)
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
  invFun c := ⟨Finsupp.embDomain (pathEmbedding i j) c, embDomain_mem_pathComponent c⟩
  left_inv x := by
    refine Subtype.ext (ext fun y => ?_)
    simp only [coeff]
    by_cases hy : ∃ p, pathEmbedding i j p = y
    · obtain ⟨p, rfl⟩ := hy
      rw [Finsupp.embDomain_apply_self, Finsupp.comapDomain_apply]
    · have hnotin : y ∉ Set.range (pathEmbedding i j) := fun h => hy (Set.mem_range.mp h)
      rw [Finsupp.embDomain_notin_range _ _ _ hnotin]
      exact (coeff_eq_zero_of_mem_pathComponent x.2
        (fun h => hnotin (mem_range_pathEmbedding_iff.mpr h))).symm
  right_inv c := by
    refine Finsupp.ext fun p => ?_
    rw [Finsupp.comapDomain_apply]
    exact Finsupp.embDomain_apply_self _ _ _



variable (k Q) in

/-- Identifies linear maps between vertex spaces with finitely supported functions on paths between the vertices. -/
noncomputable def linearMapEquivPathFinsupp (i j : Q) :
    (AuxiliaryVertexSpace k Q i →ₗ[Quiver.PathAlgebra k Q] AuxiliaryVertexSpace k Q j) ≃ₗ[k]
      (Quiver.Path i j →₀ k) :=
  (linearMapEquivPathComponent i j).trans (pathComponentEquivFinsupp i j)

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
