import RepresentationTheory.Quiver.EdgeModule
import RepresentationTheory.PolynomialModule.Finsupp

set_option backward.isDefEq.respectTransparency false
set_option linter.dupNamespace false

universe u

namespace RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-- The natural-number degree assigned to a path. -/
def pathDegree (p : Quiver.BundledPath Q) : ℕ := p.2.2.length

omit [DecidableEq Q] in
/-- The path degree equals the path length. -/
@[simp] theorem pathDegree_eq_length {a b : Q} (p : Quiver.Path a b) :
    pathDegree (⟨a, b, p⟩ : Quiver.BundledPath Q) = p.length := rfl

omit [DecidableEq Q] in
/-- The degree of a composite path is the sum of the path degrees. -/
theorem pathDegree_comp {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    pathDegree (⟨a, d, p.comp q⟩ : Quiver.BundledPath Q) =
      pathDegree (⟨a, b, p⟩ : Quiver.BundledPath Q) +
        pathDegree (⟨b, d, q⟩ : Quiver.BundledPath Q) := by
  simp [pathDegree, Quiver.Path.length_comp]

variable (k Q) in
/-- Sends a finitely supported path combination to its finitely supported family of degree components. -/
noncomputable def pathDegreeDecomposition :
    (Quiver.BundledPath Q →₀ k) →ₗ[k] (ℕ →₀ Quiver.PathAlgebra k Q) :=
  Finsupp.lsum k fun p =>
    (LinearMap.id : k →ₗ[k] k).smulRight (Finsupp.single (pathDegree p) (ofPath p))

/-- Describes the path-degree decomposition of a single path term. -/
@[simp] theorem pathDegreeDecomposition_single (p : Quiver.BundledPath Q) (c : k) :
    pathDegreeDecomposition k Q (Finsupp.single p c) =
      Finsupp.single (pathDegree p) (Finsupp.single p c : Quiver.PathAlgebra k Q) := by
  rw [pathDegreeDecomposition, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_coe, id_eq, Finsupp.smul_single, ofPath, Finsupp.smul_single, smul_eq_mul,
    mul_one]

variable (k Q) in
/-- Sums a finitely supported family of degree components. -/
noncomputable def sumDegreeComponents :
    (ℕ →₀ Quiver.PathAlgebra k Q) →ₗ[k] Quiver.PathAlgebra k Q :=
  Finsupp.lsum k fun _ => LinearMap.id

/-- Summing a family supported at one degree returns its value. -/
@[simp] theorem sumDegreeComponents_single (n : ℕ) (a : Quiver.PathAlgebra k Q) :
    sumDegreeComponents k Q (Finsupp.single n a) = a := by
  rw [sumDegreeComponents, Finsupp.lsum_single, LinearMap.id_coe, id_eq]

/-- Summing the degree decomposition of an element recovers that element. -/
@[simp] theorem sumDegreeComponents_decomposition (a : Quiver.PathAlgebra k Q) :
    sumDegreeComponents k Q (pathDegreeDecomposition k Q a) = a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single p c => rw [pathDegreeDecomposition_single, sumDegreeComponents_single]

/-- The path-degree decomposition map is injective. -/
theorem pathDegreeDecomposition_injective : Function.Injective (pathDegreeDecomposition k Q) :=
  Function.LeftInverse.injective (sumDegreeComponents_decomposition (k := k) (Q := Q))

variable (k Q) in
/-- The linear projection onto the component of a specified natural-number degree. -/
noncomputable def degreeProjection (n : ℕ) :
    (Quiver.BundledPath Q →₀ k) →ₗ[k] Quiver.PathAlgebra k Q :=
  (Finsupp.lapply n).comp (pathDegreeDecomposition k Q)

/-- Applying a degree projection returns the corresponding decomposition component. -/
theorem degreeProjection_apply (n : ℕ) (a : Quiver.BundledPath Q →₀ k) :
    degreeProjection k Q n a = pathDegreeDecomposition k Q a n := rfl

/-- Projecting a single path term returns that term at its path degree and zero at every other degree. -/
@[simp] theorem degreeProjection_single (n : ℕ) (p : Quiver.BundledPath Q) (c : k) :
    degreeProjection k Q n (Finsupp.single p c) =
      if pathDegree p = n then (Finsupp.single p c : Quiver.PathAlgebra k Q) else 0 := by
  rw [degreeProjection_apply, pathDegreeDecomposition_single]
  exact Finsupp.single_apply

/-- Projecting a single path term at its path degree leaves it unchanged. -/
theorem degreeProjection_single_pathDegree (p : Quiver.BundledPath Q) (c : k) :
    degreeProjection k Q (pathDegree p) (Finsupp.single p c) =
      (Finsupp.single p c : Quiver.PathAlgebra k Q) := by
  rw [degreeProjection_single, if_pos rfl]

/-- Composing the projections at two degrees returns the latter projection when the degrees agree and zero otherwise. -/
theorem degreeProjection_comp (m n : ℕ) (a : Quiver.BundledPath Q →₀ k) :
    degreeProjection k Q m (degreeProjection k Q n a) =
      if m = n then degreeProjection k Q n a else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, map_add, hf, hg]
      split_ifs <;> simp
  | single p c =>
      by_cases hpn : pathDegree p = n
      · subst hpn
        rw [degreeProjection_single_pathDegree, degreeProjection_single]
        by_cases hmp : pathDegree p = m
        · rw [if_pos hmp, if_pos hmp.symm]
        · rw [if_neg hmp, if_neg (fun h => hmp h.symm)]
      · rw [degreeProjection_single, if_neg hpn, map_zero, ite_self]

omit [DecidableEq Q] in
/-- Appending an arrow increases path degree by one. -/
theorem pathDegree_comp_arrow {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    pathDegree (⟨a, c, p.comp e.toPath⟩ : Quiver.BundledPath Q) = p.length + 1 := by
  change (p.comp e.toPath).length = p.length + 1
  rw [Quiver.Path.length_comp, Quiver.Path.length_toPath]

/-- The product of the terms associated to a path and a composable arrow is the term associated to their concatenation. -/
theorem path_mul_arrow_eq_comp {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    (ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q) * ofEdge ⟨b, c, e⟩ =
      ofPath (⟨a, c, p.comp e.toPath⟩ : Quiver.BundledPath Q) := by
  rw [ofEdge, Edge.toPath, pathElement_mul_pathElement, mulPath_of_composable, ofPath]

/-- Projection at one more than the path length fixes the product of the terms associated to the path and arrow. -/
theorem degreeProjection_path_mul_arrow {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    degreeProjection k Q (p.length + 1)
        ((ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q) * ofEdge ⟨b, c, e⟩) =
      (ofPath (⟨a, b, p⟩ : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q) * ofEdge ⟨b, c, e⟩ := by
  rw [path_mul_arrow_eq_comp, ofPath, ← pathDegree_comp_arrow p e,
    degreeProjection_single_pathDegree]

end RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
