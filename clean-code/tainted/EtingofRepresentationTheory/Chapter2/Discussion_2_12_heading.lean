import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower

/-!
# Section 2.12: The tensor algebra

For a vector space `V` over `k`, the tensor algebra is the direct sum of all tensor powers,
with multiplication given by concatenation of tensors.  A choice of basis indexed by `ι`
identifies it with the free algebra on `ι`.

Mathlib's `TensorAlgebra k V` is defined by its universal property.  The two equivalences below
record both concrete descriptions from the section's introductory prose.  The pure-tensor formula
states explicitly that the direct-sum equivalence sends an `n`-fold product of generators to the
degree-`n` tensor-power summand.
-/

namespace Etingof

open scoped DirectSum TensorProduct

universe u v w

variable (k : Type u) [Field k]
variable (V : Type v) [AddCommGroup V] [Module k V]

/-- The tensor algebra `T(V)` from the introduction to §2.12. -/
abbrev TensorAlgebraDef := TensorAlgebra k V

/-- The source definition `T(V) = ⨁ n, V^{⊗ n}`, as an algebra equivalence.  Multiplication on
the direct sum is the graded concatenation product on tensor powers. -/
noncomputable def tensorAlgebraEquivDirectSum :
    TensorAlgebraDef k V ≃ₐ[k] ⨁ n : ℕ, ⨂[k]^n V :=
  TensorAlgebra.equivDirectSum

/-- Under the direct-sum description, a pure `n`-fold tensor lies in exactly the degree-`n`
summand. -/
theorem tensorAlgebraEquivDirectSum_tprod {n : ℕ} (x : Fin n → V) :
    tensorAlgebraEquivDirectSum k V (TensorAlgebra.tprod k V n x) =
      DirectSum.of (fun n : ℕ => ⨂[k]^n V) n (PiTensorProduct.tprod k x) :=
  TensorAlgebra.toDirectSum_tensorPower_tprod x

/-- Multiplication of homogeneous tensors in `T(V)` is the concatenation product on tensor
powers, exactly as in the source definition. -/
theorem tensorAlgebra_mul_homogeneous {n m : ℕ} (a : ⨂[k]^n V) (b : ⨂[k]^m V) :
    TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b =
      TensorPower.toTensorAlgebra
        (@GradedMonoid.GMul.mul ℕ (fun d : ℕ => ⨂[k]^d V) _ TensorPower.gMul n m a b) :=
  (TensorPower.toTensorAlgebra_gMul a b).symm

/-- A choice of basis identifies `T(V)` with the free algebra on the basis indices. -/
noncomputable def tensorAlgebraEquivFreeAlgebra {ι : Type w} (b : Module.Basis ι k V) :
    TensorAlgebraDef k V ≃ₐ[k] FreeAlgebra k ι :=
  TensorAlgebra.equivFreeAlgebra b

/-- The basis/free-algebra identification takes a basis vector to the correspondingly named free
generator. -/
@[simp] theorem tensorAlgebraEquivFreeAlgebra_ι {ι : Type w} (b : Module.Basis ι k V) (i : ι) :
    tensorAlgebraEquivFreeAlgebra k V b (TensorAlgebra.ι k (b i)) = FreeAlgebra.ι k i :=
  TensorAlgebra.equivFreeAlgebra_ι_apply b i

/-- The degree-one generators embed faithfully in the tensor algebra, ruling out a vacuous
generator model. -/
theorem tensorAlgebra_ι_injective :
    Function.Injective (TensorAlgebra.ι k : V → TensorAlgebra k V) :=
  TensorAlgebra.ι_leftInverse.injective

end Etingof
