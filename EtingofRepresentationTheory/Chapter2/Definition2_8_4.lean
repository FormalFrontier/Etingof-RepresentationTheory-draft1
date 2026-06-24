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
abbrev QuiverPathIndex (Q : Type*) [Quiver Q] : Type _ :=
  Σ (a : Q) (b : Q), Quiver.Path a b

namespace QuiverPathIndex

variable {Q : Type*} [Quiver Q] [DecidableEq Q]

/-- Concatenation of two oriented paths, defined when the target of the first equals the source
of the second; `none` otherwise. -/
noncomputable def comp : QuiverPathIndex Q → QuiverPathIndex Q → Option (QuiverPathIndex Q)
  | ⟨a, b, p⟩, ⟨c, d, q⟩ =>
    if h : b = c then some ⟨a, d, p.comp (h ▸ q)⟩ else none

/-- When the target of the first path equals the source of the second, the composite is their
concatenation. -/
theorem comp_eq_some {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    comp (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨b, d, q⟩ = some ⟨a, d, p.comp q⟩ := by
  simp [comp]

/-- When the target of the first path does not match the source of the second, the composite is
undefined (`none`). -/
theorem comp_eq_none {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d) (h : b ≠ c) :
    comp (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨c, d, q⟩ = none := by
  simp only [comp, dif_neg h]

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

/-- On composable basis paths, `compSingle` is the single concatenated path. -/
theorem compSingle_eq {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    compSingle (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨b, d, q⟩
      = Finsupp.single (⟨a, d, p.comp q⟩ : QuiverPathIndex Q) (1 : k) := by
  rw [compSingle, QuiverPathIndex.comp_eq_some]; rfl

/-- On non-composable basis paths, `compSingle` is zero. -/
theorem compSingle_eq_zero {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (h : b ≠ c) : compSingle (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨c, d, q⟩ = (0 : PathAlgebra k Q) := by
  rw [compSingle, QuiverPathIndex.comp_eq_none _ _ h]; rfl

/-- Multiplying a trivial path `p_i` on the left: the result is the original path if it starts at
`i`, and zero otherwise. -/
theorem compSingle_nil_left (i a b : Q) (p : Quiver.Path a b) :
    compSingle (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) ⟨a, b, p⟩
      = if i = a then Finsupp.single (⟨a, b, p⟩ : QuiverPathIndex Q) (1 : k) else 0 := by
  by_cases h : i = a
  · subst h
    rw [compSingle_eq, Quiver.Path.nil_comp, if_pos rfl]
  · rw [compSingle_eq_zero _ _ h, if_neg h]

/-- Multiplying a trivial path `p_i` on the right: the result is the original path if it ends at
`i`, and zero otherwise. -/
theorem compSingle_nil_right (i a b : Q) (p : Quiver.Path a b) :
    compSingle (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨i, i, Quiver.Path.nil⟩
      = if b = i then Finsupp.single (⟨a, b, p⟩ : QuiverPathIndex Q) (1 : k) else 0 := by
  by_cases h : b = i
  · subst h
    rw [compSingle_eq, Quiver.Path.comp_nil, if_pos rfl]
  · rw [compSingle_eq_zero _ _ h, if_neg h]

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
    (Finsupp.single x a * Finsupp.single y b : PathAlgebra k Q)
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

/-- Associativity of the multiplication on three basis paths. This is where the associativity of
path concatenation (`Quiver.Path.comp_assoc`) enters; the partial composition cases all collapse
to `0`. -/
theorem single_mul_single_assoc (x y z : QuiverPathIndex Q) (a b c : k) :
    (Finsupp.single x a * Finsupp.single y b * Finsupp.single z c : PathAlgebra k Q)
      = Finsupp.single x a * (Finsupp.single y b * Finsupp.single z c) := by
  obtain ⟨xa, xb, xp⟩ := x
  obtain ⟨yc, yd, yq⟩ := y
  obtain ⟨ze, zf, zr⟩ := z
  by_cases hbc : xb = yc
  · subst hbc
    by_cases hde : yd = ze
    · subst hde
      -- fully composable: reduces to associativity of path concatenation
      rw [single_mul_single, compSingle_eq, smul_mul, single_mul_single, compSingle_eq,
        single_mul_single, compSingle_eq, mul_smul', single_mul_single, compSingle_eq,
        Quiver.Path.comp_assoc, smul_smul, smul_smul]
      congr 1
      ring
    · -- composable on the left, not on the right
      rw [single_mul_single, compSingle_eq, smul_mul, single_mul_single,
        compSingle_eq_zero _ _ hde, smul_zero, smul_zero, single_mul_single,
        compSingle_eq_zero _ _ hde, smul_zero, mul_zero]
  · -- not composable on the left
    by_cases hde : yd = ze
    · subst hde
      rw [single_mul_single, compSingle_eq_zero _ _ hbc, smul_zero, zero_mul,
        single_mul_single, compSingle_eq, mul_smul', single_mul_single,
        compSingle_eq_zero _ _ hbc, smul_zero, smul_zero]
    · rw [single_mul_single, compSingle_eq_zero _ _ hbc, smul_zero, zero_mul,
        single_mul_single, compSingle_eq_zero _ _ hde, smul_zero, mul_zero]

/-- Associativity of path-algebra multiplication, reduced to the basis case via bilinearity. -/
protected theorem mul_assoc (f g h : PathAlgebra k Q) : f * g * h = f * (g * h) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [zero_mul]
  | add f1 f2 hf1 hf2 => rw [add_mul, add_mul, add_mul, hf1, hf2]
  | single x a =>
    induction g using Finsupp.induction_linear with
    | zero => simp only [mul_zero, zero_mul]
    | add g1 g2 hg1 hg2 => rw [mul_add, add_mul, add_mul, mul_add, hg1, hg2]
    | single y b =>
      induction h using Finsupp.induction_linear with
      | zero => simp only [mul_zero]
      | add h1 h2 hh1 hh2 => rw [mul_add, mul_add, mul_add, hh1, hh2]
      | single z c => exact single_mul_single_assoc x y z a b c

variable (k Q)

/-- The path algebra is an (in general non-unital) associative `k`-algebra: an associative ring
whose multiplication is `k`-bilinear path concatenation. -/
noncomputable instance : NonUnitalRing (PathAlgebra k Q) :=
  { (inferInstance : NonUnitalNonAssocRing (PathAlgebra k Q)) with
    mul_assoc := PathAlgebra.mul_assoc }

/-- For a quiver with finitely many vertices, the sum `∑ᵢ pᵢ` of the trivial paths is the
candidate unit of the path algebra (Remark 2.8.5). -/
noncomputable def one [Fintype Q] : PathAlgebra k Q :=
  ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (1 : k)

noncomputable instance [Fintype Q] : One (PathAlgebra k Q) := ⟨one k Q⟩

variable {k Q}

theorem one_def [Fintype Q] :
    (1 : PathAlgebra k Q) = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) 1 :=
  rfl

/-- The sum of trivial paths is a left unit (Remark 2.8.5). -/
protected theorem one_mul [Fintype Q] (f : PathAlgebra k Q) : (1 : PathAlgebra k Q) * f = f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [mul_zero]
  | add f g hf hg => rw [mul_add, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_def, Finset.sum_mul]
    have hterm : ∀ i : Q, (Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (1 : k)
        * Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a : PathAlgebra k Q)
        = if i = xa then (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a : PathAlgebra k Q)
          else 0 := by
      intro i
      rw [single_mul_single, compSingle_nil_left]
      by_cases h : i = xa
      · simp only [if_pos h, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
      · simp only [if_neg h, smul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_ite_eq' Finset.univ xa, if_pos (Finset.mem_univ xa)]

/-- The sum of trivial paths is a right unit (Remark 2.8.5). -/
protected theorem mul_one [Fintype Q] (f : PathAlgebra k Q) : f * (1 : PathAlgebra k Q) = f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [zero_mul]
  | add f g hf hg => rw [add_mul, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_def, Finset.mul_sum]
    have hterm : ∀ i : Q, (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a
        * Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (1 : k) : PathAlgebra k Q)
        = if xb = i then (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a : PathAlgebra k Q)
          else 0 := by
      intro i
      rw [single_mul_single, compSingle_nil_right]
      by_cases h : xb = i
      · simp only [if_pos h, mul_one, Finsupp.smul_single, smul_eq_mul]
      · simp only [if_neg h, smul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Finset.sum_ite_eq Finset.univ xb, if_pos (Finset.mem_univ xb)]

variable (k Q)

/-- The path algebra of a quiver with finitely many vertices is a unital ring: the multiplication
is associative path concatenation, with unit `∑ᵢ pᵢ` (Remark 2.8.5). -/
noncomputable instance [Fintype Q] : Ring (PathAlgebra k Q) :=
  { (inferInstance : NonUnitalRing (PathAlgebra k Q)),
    (inferInstance : One (PathAlgebra k Q)) with
    one_mul := PathAlgebra.one_mul
    mul_one := PathAlgebra.mul_one }

/-- The path algebra of a quiver with finitely many vertices is a `k`-algebra (Remark 2.8.5).
The algebra structure is provided by `Algebra.ofModule`, using that path-concatenation is
`k`-bilinear (`smul_mul`, `mul_smul'`). -/
noncomputable instance [Fintype Q] : Algebra k (PathAlgebra k Q) :=
  Algebra.ofModule smul_mul mul_smul'

/-- **Remark 2.8.5.** For a quiver with finitely many vertices, the sum of the trivial paths
`∑ᵢ pᵢ` is the unit of the path algebra. -/
theorem sum_trivialPaths_eq_one [Fintype Q] :
    (∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) : PathAlgebra k Q) = 1 := by
  rw [one_def]; rfl

end PathAlgebra

end Etingof
