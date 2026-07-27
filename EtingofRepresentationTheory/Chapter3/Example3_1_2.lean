import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Example 3.1.2: End(V) as a Semisimple Representation

Let V be an irreducible representation of A of dimension n. Then Y = End(V), with action
of A by left multiplication, is a semisimple representation of A, isomorphic to nV
(the direct sum of n copies of V). Indeed, any basis v₁, …, vₙ of V gives rise to an
isomorphism of representations End(V) → nV, given by x ↦ (xv₁, …, xvₙ).

## Proof strategy

Given a k-basis b of V, the evaluation map f ↦ (f(b₀), …, f(bₙ₋₁)) is an A-linear
bijection from End_k(V) to V^n. Since V is simple (hence semisimple), V^n is semisimple,
and semisimplicity transfers along the equivalence.

## Main statements

* `Etingof.endEquivPiOfBasis` — the concrete `A`-linear equivalence
  `Module.End k V ≃ₗ[A] (ι → V)` attached to a chosen basis `b`, evaluating an
  endomorphism on the basis vectors. This is the explicit isomorphism `End(V) ≅ nV`
  of the example (`f ↦ (f(b i))ᵢ`).
* `Etingof.endEquivPi` — the same equivalence for the canonical finite basis,
  `Module.End k V ≃ₗ[A] (Fin (finrank k V) → V)`.
* `Etingof.endomorphism_semisimple` — `End_k(V)` is a semisimple `A`-module, obtained
  by transporting semisimplicity of `nV` along `endEquivPi`.
-/

set_option autoImplicit false

namespace Etingof

section

variable {k : Type*} {A : Type*} {V : Type*} {ι : Type*}
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The evaluation map sending `f ∈ End_k(V)` to `(f(b i))ᵢ` is `A`-linear.
This is the map `x ↦ (xv₁, …, xvₙ)` of Etingof Example 3.1.2. -/
noncomputable def evalMap (b : Module.Basis ι k V) :
    Module.End k V →ₗ[A] (ι → V) where
  toFun f i := f (b i)
  map_add' f g := by ext i; simp
  map_smul' (a : A) f := by ext i; simp [LinearMap.smul_apply]

/-- Evaluating `evalMap b f` at `i` gives the value of `f` on the basis vector `b i`. -/
@[simp] theorem evalMap_apply (b : Module.Basis ι k V) (f : Module.End k V) (i : ι) :
    evalMap (A := A) b f i = f (b i) := rfl

/- Finiteness is a proof hypothesis for surjectivity, although it does not occur in the
proposition returned by `Function.Bijective`. -/
set_option linter.unusedFintypeInType false in
/-- The evaluation map associated to a finite basis is bijective. -/
theorem evalMap_bijective [Fintype ι] (b : Module.Basis ι k V) :
    Function.Bijective (evalMap (A := A) b) := by
  constructor
  · intro f g h
    ext v
    have hfg : ∀ i, f (b i) = g (b i) := congr_fun h
    rw [← b.sum_repr v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hfg i]
  · intro g
    refine ⟨b.constr k g, ?_⟩
    ext i
    rw [evalMap_apply]
    exact b.constr_basis k g i

/-- The `A`-linear isomorphism `End_k(V) ≃ (ι → V)` attached to a basis `b` indexed by a
finite type `ι`, sending `f` to `(f(b i))ᵢ`. This is the explicit representation
isomorphism `End(V) ≅ nV` of Etingof Example 3.1.2. -/
noncomputable def endEquivPiOfBasis [Fintype ι] (b : Module.Basis ι k V) :
    Module.End k V ≃ₗ[A] (ι → V) :=
  LinearEquiv.ofBijective (evalMap b) (evalMap_bijective b)

/-- The equivalence `endEquivPiOfBasis` acts by evaluation on the chosen basis. -/
@[simp] theorem endEquivPiOfBasis_apply [Fintype ι] (b : Module.Basis ι k V)
    (f : Module.End k V) (i : ι) : endEquivPiOfBasis (A := A) b f i = f (b i) := rfl

/-- The `A`-linear isomorphism `End_k(V) ≃ (Fin (dim V) → V)` for the canonical finite
basis of a finite-dimensional `V`: `End(V) ≅ nV` with `n = dim V`. -/
noncomputable def endEquivPi [FiniteDimensional k V] :
    Module.End k V ≃ₗ[A] (Fin (Module.finrank k V) → V) :=
  endEquivPiOfBasis (Module.finBasis k V)

/-- The canonical equivalence `endEquivPi` acts by evaluation on the canonical finite basis. -/
@[simp] theorem endEquivPi_apply [FiniteDimensional k V] (f : Module.End k V)
    (i : Fin (Module.finrank k V)) :
    endEquivPi (A := A) f i = f (Module.finBasis k V i) := rfl

end

/-- End(V) with left multiplication by A is isomorphic to n copies of V as a representation,
where n = dim V; in particular it is semisimple. This is derived by transporting
semisimplicity of `nV` along `endEquivPi`. Etingof Example 3.1.2. -/
theorem endomorphism_semisimple (k : Type*) (A : Type*) (V : Type*)
    [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [FiniteDimensional k V] [IsSimpleModule A V] :
    IsSemisimpleModule A (Module.End k V) :=
  IsSemisimpleModule.congr (endEquivPi (k := k) (A := A) (V := V))

end Etingof
