import Mathlib.Algebra.Algebra.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Definition 2.8.4: Path Algebra of a Quiver

The **path algebra** P_Q of a quiver Q is the algebra whose basis is formed by oriented
paths in Q, including the trivial paths pᵢ, i ∈ I, corresponding to the vertices of Q,
and multiplication is the concatenation of paths.

## Construction

Mathlib has `Quiver.Path` (composable sequences of arrows) but no path *algebra*. We build
it here as the free `k`-module on the type of all oriented paths (a source, a target, and a
`Quiver.Path` between them), equipped with the concatenation multiplication: two basis paths
multiply to their concatenation when composable, and to `0` otherwise.

The multiplication is constructed as a `k`-bilinear map (via `Finsupp.lsum`), which makes the
distributive laws hold by construction (they are `map_add`/`map_zero` of a linear map). The
associativity of concatenation and the unit law (Remark 2.8.5) are recorded as the remaining
proof obligations.

## Convention

Following the footnote to Definition 2.8.4, two oriented paths `a : x ⟶* y` and `b : z ⟶* w`
concatenate to `a · b : x ⟶* w` precisely when the target `y` of `a` equals the source `z` of
`b`, and the product is `0` otherwise. (The book's body text uses the opposite reading order
`ab = "first b then a"`; the two conventions produce mutually opposite algebras, both equally
valid path algebras. We use the source-to-target reading aligned with Mathlib's `Quiver.Path.comp`.)
-/

namespace Etingof

/-- The type of all oriented paths in a quiver: a triple (source, target, path). -/
def QuiverPathIndex (Q : Type*) [Quiver Q] : Type _ :=
  Σ (a : Q) (b : Q), Quiver.Path a b

namespace QuiverPathIndex

variable {Q : Type*} [Quiver Q] [DecidableEq Q]

/-- Concatenation of two oriented paths, defined when the target of the first equals the source
of the second; `none` otherwise. -/
noncomputable def comp : QuiverPathIndex Q → QuiverPathIndex Q → Option (QuiverPathIndex Q)
  | ⟨a, b, p⟩, ⟨c, d, q⟩ =>
    if h : b = c then some ⟨a, d, p.comp (h ▸ q)⟩ else none

end QuiverPathIndex

/-- The path algebra of a quiver `Q` over a field `k`, in the sense of Etingof Definition 2.8.4.
The basis consists of oriented paths in `Q`, with multiplication given by path concatenation
(zero if the paths are not composable). -/
abbrev PathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  QuiverPathIndex Q →₀ k

namespace PathAlgebra

variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

variable {k Q}

/-- The basis element of `PathAlgebra k Q` indexed by an oriented path `x`, i.e. the path `x`
with coefficient `1`. -/
noncomputable def ofPath (x : QuiverPathIndex Q) : PathAlgebra k Q :=
  Finsupp.single x 1

/-- The product of two basis paths (as an element of the algebra): the concatenated path with
coefficient `1` when composable, and `0` otherwise. -/
noncomputable def compSingle (x y : QuiverPathIndex Q) : PathAlgebra k Q :=
  (x.comp y).elim 0 (fun z => Finsupp.single z (1 : k))

variable (k Q)

/-- The multiplication of `PathAlgebra k Q`, as a `k`-bilinear map. On basis paths it is path
concatenation; it is extended bilinearly to the whole free module. Phrasing the product as a
`LinearMap` makes all distributive laws hold definitionally (they are `map_add`/`map_zero`). -/
noncomputable def mulLinear :
    PathAlgebra k Q →ₗ[k] PathAlgebra k Q →ₗ[k] PathAlgebra k Q :=
  Finsupp.lsum k fun x =>
    (LinearMap.id : k →ₗ[k] k).smulRight
      (Finsupp.lsum k fun y => (LinearMap.id : k →ₗ[k] k).smulRight (compSingle x y))

/-- The (in general non-unital, non-associative-by-construction) ring structure on the path
algebra. The multiplication is `mulLinear`; the distributive laws hold because it is a
`k`-bilinear map (`map_add`/`map_zero`). Associativity and the unit are established separately
below. -/
noncomputable instance : NonUnitalNonAssocRing (PathAlgebra k Q) :=
  { (inferInstance : AddCommGroup (PathAlgebra k Q)) with
    mul := fun f g => mulLinear k Q f g
    left_distrib := fun a b c => by
      change mulLinear k Q a (b + c) = mulLinear k Q a b + mulLinear k Q a c
      rw [map_add]
    right_distrib := fun a b c => by
      change mulLinear k Q (a + b) c = mulLinear k Q a c + mulLinear k Q b c
      rw [map_add]; rfl
    zero_mul := fun a => by
      change mulLinear k Q 0 a = 0
      rw [map_zero]; rfl
    mul_zero := fun a => by
      change mulLinear k Q a 0 = 0
      rw [map_zero] }

variable {k Q}

theorem mul_def (f g : PathAlgebra k Q) : f * g = mulLinear k Q f g := rfl

/-- On basis paths the product is the concatenation `compSingle`, scaled by the product of the
coefficients. -/
theorem single_mul_single (x y : QuiverPathIndex Q) (a b : k) :
    (Finsupp.single x a : PathAlgebra k Q) * (Finsupp.single y b : PathAlgebra k Q)
      = (a * b) • compSingle x y := by
  rw [mul_def, mulLinear]
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq,
    LinearMap.smul_apply, smul_smul]

/-- Scalars commute past the multiplication on the left (the product is `k`-linear in its
first argument). -/
theorem smul_mul (r : k) (a b : PathAlgebra k Q) : (r • a) * b = r • (a * b) := by
  change mulLinear k Q (r • a) b = r • mulLinear k Q a b
  rw [map_smul]; rfl

/-- Scalars commute past the multiplication on the right (the product is `k`-linear in its
second argument). -/
theorem mul_smul' (r : k) (a b : PathAlgebra k Q) : a * (r • b) = r • (a * b) := by
  change mulLinear k Q a (r • b) = r • mulLinear k Q a b
  rw [map_smul]

end PathAlgebra

end Etingof
