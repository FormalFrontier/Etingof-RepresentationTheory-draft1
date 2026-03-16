import Mathlib

/-!
# Definition 6.6.4: Reflection Functor F⁻ᵢ (at a Source)

Let Q be a quiver and i ∈ Q be a source. Let ψ : V_i → ⊕_{i→j} V_j be the
canonical map. The reflection functor F⁻ᵢ : Rep Q → Rep Q̄ᵢ is defined by:
- F⁻ᵢ(V)_k = V_k for k ≠ i
- F⁻ᵢ(V)_i = Coker(ψ) = (⊕_{i→j} V_j) / Im ψ

All maps now pointing into i are replaced by the compositions of the inclusions
V_k → ⊕_{i→j} V_j with the natural quotient map ⊕_{i→j} V_j → (⊕_{i→j} V_j)/Im ψ.

## Mathlib correspondence

BGP reflection functors are not in Mathlib. The cokernel-based construction uses
`Submodule.mkQ` for quotient maps and `LinearMap.range` for image.
-/

/-- The reflection functor F⁻ᵢ at a source vertex i, sending representations of Q
to representations of Q̄ᵢ. At vertex i, replaces V_i with coker(V_i → ⊕_{i→j} V_j).
(Etingof Definition 6.6.4) -/
noncomputable def Etingof.reflectionFunctorMinus
    (V : Type*) [Quiver V] [DecidableEq V] (i : V) :
    sorry := -- TODO: needs Rep Q and Rep Q̄ᵢ types
  sorry
