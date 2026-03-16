import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Example 7.3.2: Examples of Natural Transformations

1. On the category of finite dimensional vector spaces FVect_k, the functors id and **
   are isomorphic via the standard maps a_V : V → V**. But on Vect_k they are not
   isomorphic (infinite dimensional V is not isomorphic to V**).
2. On FVect_k' (morphisms = isomorphisms), V ↦ V* is a functor where V ≅ F(V) for
   all V, but it is not isomorphic to the identity functor.
3. If F : A-mod → Vect_k is the forgetful functor, then End(F) = A.
4. The endomorphisms of the identity functor on A-mod is the center of A.

## Mathlib correspondence

The double dual natural isomorphism is captured by `Module.evalEquiv` (for reflexive
modules) and its naturality by `Module.Dual.eval_naturality`. Finite-dimensional
modules over a field are automatically reflexive (`IsReflexive.of_finite_of_free`).
-/

/-- The canonical evaluation map gives a linear equivalence `V ≃ₗ[k] V**` for any
finite-dimensional vector space V over a field k. (Etingof Example 7.3.2(1))

The key point is that this isomorphism is *natural*: for any linear map `f : V →ₗ[k] W`,
the diagram `V → V** → W**` commutes with `V → W → W**`, which is captured by
`Module.Dual.eval_naturality`. -/
noncomputable def Etingof.double_dual_iso
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V] :
    V ≃ₗ[k] Module.Dual k (Module.Dual k V) :=
  Module.evalEquiv k V

/-- The double dual evaluation map is natural: for any linear map `f : V →ₗ[k] W`,
we have `f.dualMap.dualMap ∘ eval k V = eval k W ∘ f`. This is the naturality
condition for Example 7.3.2(1), showing the evaluation maps form a natural
transformation from the identity functor to the double dual functor. -/
theorem Etingof.double_dual_naturality
    (k : Type*) [CommSemiring k] (V W : Type*) [AddCommMonoid V] [AddCommMonoid W]
    [Module k V] [Module k W] (f : V →ₗ[k] W) :
    f.dualMap.dualMap ∘ₗ Module.Dual.eval k V = Module.Dual.eval k W ∘ₗ f :=
  Module.Dual.eval_naturality f
