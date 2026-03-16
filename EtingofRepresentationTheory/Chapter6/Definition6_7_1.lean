import Mathlib

/-!
# Definition 6.7.1: Coxeter Element

Let Q be a quiver with underlying graph Γ. Fix a labeling 1, …, n of the vertices.
The **Coxeter element** c corresponding to this labeling is c = s₁ s₂ ⋯ sₙ,
the product of all simple reflections.

## Mathlib correspondence

Mathlib has `CoxeterSystem` and `CoxeterGroup` with simple reflections in
`Mathlib.GroupTheory.Coxeter.Basic`. The Coxeter element as a product of all
generators needs a custom construction using `Finset.prod` over the simple
reflections.
-/

/-- The Coxeter element of a quiver Q with n vertices: the ordered product s₁ s₂ ⋯ sₙ
of all simple reflections. (Etingof Definition 6.7.1) -/
noncomputable def Etingof.coxeterElement
    (n : ℕ) (W : Type*) [Group W] (s : Fin n → W) : W :=
  (List.ofFn s).prod
