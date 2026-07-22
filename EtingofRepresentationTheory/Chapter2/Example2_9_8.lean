import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.OfAssociative
import EtingofRepresentationTheory.Chapter2.Definition2_9_7

/-!
# Example 2.9.8: Examples of Representations of Lie Algebras

Etingof lists three examples of representations of a Lie algebra `𝔤`:

(1) `V = 0` (the zero representation).
(2) Any vector space `V` with `ρ = 0` (the trivial representation).
(3) The adjoint representation `V = 𝔤` with `ρ(a)(b) := [a, b]`. That this is a
    representation follows from the Jacobi identity (equation (2.9.1)); the meaning of the
    Jacobi identity is precisely that it is equivalent to the existence of the adjoint
    representation.

A representation of `𝔤` is (Definition 2.9.7) a `LieModule k 𝔤 V`, recorded here as
`Etingof.LieAlgebraRepresentation`.

## Mathlib correspondence

Exact match. `TrivialLieModule k L V` carries the trivial Lie action (`ρ = 0`) on an
arbitrary `R`-module `V`, and `LieAlgebra.ad k L : L →ₗ⁅k⁆ Module.End k L` is the adjoint
representation, with `LieAlgebra.ad_apply` giving `ρ(a)(b) = [a, b]`.
-/

open Etingof

-- The Lie ring structure on `Module.End k L` (commutator bracket), needed to state the
-- adjoint representation `ρ : 𝔤 → End(𝔤)`, is a local instance in Mathlib.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [CommRing k] (L : Type*) [LieRing L] [LieAlgebra k L]

/-! ## (1) The zero representation `V = 0`

The zero vector space, realised as `PUnit`, carries a representation. Its underlying space is
genuinely zero (`Subsingleton`), and the action is necessarily zero. -/

/-- (1) The zero representation: `V = 0` is a representation of `𝔤`. (Etingof 2.9.8(1)) -/
example : LieAlgebraRepresentation k L (TrivialLieModule k L PUnit) := inferInstance

/-- The underlying space of the zero representation is genuinely zero. -/
example : Subsingleton (TrivialLieModule k L PUnit) := inferInstanceAs (Subsingleton PUnit)

/-! ## (2) The trivial representation `ρ = 0`

Any vector space `V` carries the trivial representation, where `ρ = 0`, i.e. every Lie
algebra element acts as `0`. -/

variable (V : Type*) [AddCommGroup V] [Module k V]

/-- (2) The trivial representation: any vector space `V` with `ρ = 0` is a representation.
(Etingof 2.9.8(2)) -/
example : LieAlgebraRepresentation k L (TrivialLieModule k L V) := inferInstance

/-- The trivial representation genuinely has `ρ = 0`: every element of `𝔤` acts as `0`. -/
example (a : L) (v : TrivialLieModule k L V) : ⁅a, v⁆ = 0 := rfl

/-! ## (3) The adjoint representation `V = 𝔤`, `ρ(a)(b) := [a, b]`

The adjoint representation is `LieAlgebra.ad`, the Lie algebra homomorphism
`ρ : 𝔤 → End(𝔤)` sending `a` to `[a, -]`. The fact that `ad` preserves the Lie bracket —
`ad ⁅a, b⁆ = ⁅ad a, ad b⁆` in `End(𝔤)` — is exactly the content of the Jacobi identity, so
the existence of the adjoint representation is equivalent to the Jacobi identity. -/

/-- (3) The adjoint representation: `V = 𝔤` is a representation of `𝔤`. (Etingof 2.9.8(3)) -/
example : LieAlgebraRepresentation k L L := inferInstance

/-- The adjoint representation as the Lie algebra homomorphism `ρ : 𝔤 → End(𝔤)` of
Definition 2.9.7. -/
noncomputable example : L →ₗ⁅k⁆ Module.End k L := LieAlgebra.ad k L

/-- The adjoint action is `ρ(a)(b) = [a, b]`, as Etingof specifies. -/
example (a b : L) : LieAlgebra.ad k L a b = ⁅a, b⁆ := LieAlgebra.ad_apply k L a b

/-- That `ρ = ad` preserves the bracket, `ad ⁅a, b⁆ = ⁅ad a, ad b⁆`, is exactly the Jacobi
identity: this is what makes the adjoint action a representation. -/
example (a b : L) : LieAlgebra.ad k L ⁅a, b⁆ = ⁅LieAlgebra.ad k L a, LieAlgebra.ad k L b⁆ :=
  LieHom.map_lie (LieAlgebra.ad k L) a b
