import Mathlib

/-!
# Definition 5.23.1: Algebraic Representation of GL(V)

A finite dimensional representation Y of GL(V) is *algebraic* (or rational,
or polynomial) if its matrix elements are polynomial functions of the entries
of g, g⁻¹, for g ∈ GL(V), i.e., belong to k[gᵢⱼ][1/det(g)].

## Mathlib correspondence

- `Matrix.GeneralLinearGroup (Fin n) k` for GL_n(k)
- `MvPolynomial` for multivariate polynomials over k
- `Basis.repr` for matrix coefficients of the representation
-/

/-- The type of variables for the coordinate ring of GL_n:
matrix entries (Fin n × Fin n) together with one extra variable
representing 1/det(g). -/
abbrev Etingof.GLCoordVars (n : ℕ) := (Fin n × Fin n) ⊕ Unit

/-- Evaluate a polynomial in `k[Xᵢⱼ, D]` at a matrix g ∈ GL_n(k),
substituting Xᵢⱼ ↦ gᵢⱼ and D ↦ det(g)⁻¹. -/
noncomputable def Etingof.evalAtGL {k : Type*} [Field k] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k)
    (p : MvPolynomial (Etingof.GLCoordVars n) k) : k :=
  MvPolynomial.eval
    (Sum.elim (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2)
              (fun _ => ((g : Matrix (Fin n) (Fin n) k).det)⁻¹))
    p

/-- A family of endomorphisms `ρ : GL_n(k) → (Y →ₗ[k] Y)` has *algebraic matrix
coefficients* if there exists a basis of Y such that all matrix coefficients of
`ρ g` are polynomial functions of the matrix entries `gᵢⱼ` and `det(g)⁻¹`.

Concretely: there exist polynomials Pₐ_c ∈ k[Xᵢⱼ, D] (where Xᵢⱼ are
variables for the n² matrix entries and D represents 1/det) such that
for all g ∈ GL_n(k), the (a,c)-th matrix coefficient of ρ(g) equals
Pₐ_c(gᵢⱼ, det(g)⁻¹).

This is the *raw coefficient-regularity* condition on an arbitrary family. It
does **not** by itself require `ρ` to be a group representation (see the
regression `exists_algebraicCoefficientFamily_not_representation`). The textbook
notion of an algebraic representation is `Etingof.IsAlgebraicRepresentation`,
which bundles this condition with a genuine `Representation`. The name is kept
distinct precisely because the reusable transport lemmas
(`IsAlgebraicCoefficientFamily.restrict`, `.detTwist`, `.of_linearEquiv`, …)
naturally act on raw families, some of which are not packaged as
`Representation` objects.

(Etingof Definition 5.23.1) -/
def Etingof.IsAlgebraicCoefficientFamily
    {k : Type*} [Field k]
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (Etingof.GLCoordVars n) k),
    ∀ (g : Matrix.GeneralLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (ρ g (b c)) a = Etingof.evalAtGL g (P a c)

/-- **Definition 5.23.1 (algebraic representation).** A finite-dimensional
representation `ρ` of `GL_n(k)` on `Y` is *algebraic* (also called *rational* or
*polynomial*) if its matrix coefficients are polynomial functions of the entries
`gᵢⱼ` and of `det(g)⁻¹`.

Unlike `IsAlgebraicCoefficientFamily`, the input here is a bundled
`Representation k (GL_n k) Y` — a genuine group homomorphism `g ↦ ρ g` — so the
identity and multiplicativity action laws are part of the data. The predicate
then asserts algebraicity of the underlying coefficient family `⇑ρ`. This
faithfully captures Etingof's notion, whose subject is *a representation*.

(Etingof Definition 5.23.1) -/
def Etingof.IsAlgebraicRepresentation
    {k : Type*} [Field k]
    (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y) : Prop :=
  Etingof.IsAlgebraicCoefficientFamily n (fun g => ρ g)

/-- `IsAlgebraicRepresentation` unfolds to algebraicity of the underlying
coefficient family. This is definitional, but stated for readability at use
sites and to bridge the two predicates. -/
theorem Etingof.isAlgebraicRepresentation_iff
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y) :
    Etingof.IsAlgebraicRepresentation n ρ ↔
      Etingof.IsAlgebraicCoefficientFamily n (fun g => ρ g) :=
  Iff.rfl

/-- **Compatibility wrapper.** A genuine representation whose coefficient family
is algebraic is an algebraic representation. -/
theorem Etingof.IsAlgebraicCoefficientFamily.toRepresentation
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y}
    (h : Etingof.IsAlgebraicCoefficientFamily n (fun g => ρ g)) :
    Etingof.IsAlgebraicRepresentation n ρ := h

/-- **Regression witness.** Coefficient-regularity alone does not imply the
representation laws: over a nonzero finite-dimensional `Y`, the constant-zero
family has (trivially polynomial) zero matrix coefficients, hence is an
`IsAlgebraicCoefficientFamily`, yet it fails `ρ 1 = 1` and so is not the
coefficient family of any representation. This is exactly the family the old,
too-broad `IsAlgebraicRepresentation` mistakenly accepted. -/
theorem Etingof.exists_algebraicCoefficientFamily_not_representation
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    [Nontrivial Y] :
    ∃ ρ : Matrix.GeneralLinearGroup (Fin n) k → Y →ₗ[k] Y,
      Etingof.IsAlgebraicCoefficientFamily n ρ ∧ ρ 1 ≠ LinearMap.id := by
  classical
  refine ⟨fun _ => 0, ?_, ?_⟩
  · -- Zero coefficients are the evaluation of the zero polynomial.
    refine ⟨_, Module.finBasis k Y, fun _ _ => 0, fun g a c => ?_⟩
    simp [Etingof.evalAtGL]
  · -- `0 = id` would force every vector to be zero, contradicting nontriviality.
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    have hz := congrArg (fun f : Y →ₗ[k] Y => f y) h
    simp only [LinearMap.zero_apply, LinearMap.id_apply] at hz
    exact hy hz.symm
