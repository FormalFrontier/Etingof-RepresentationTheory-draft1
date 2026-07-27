import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Definition 2.8.4: Path Algebra of a Quiver

The **path algebra** P_Q of a quiver Q is the algebra whose basis is formed by oriented
paths in Q, including the trivial paths pᵢ, i ∈ I, corresponding to the vertices of Q.
The book reads `a * b` as "first `b`, then `a`".

## Construction

Mathlib has `Quiver.Path` (composable sequences of arrows) but no path *algebra*. The established
implementation `PathAlgebra` below is the free `k`-module on all oriented paths, with the
source-to-target multiplication naturally induced by `Quiver.Path.comp`. The public book-facing
type `BookPathAlgebra`, defined at the end of the file, is its multiplicative opposite. Thus it has
the same path basis while its multiplication agrees literally with the book's reading order.

The internal multiplication is constructed as a `k`-bilinear map (via `Finsupp.lsum`), which
makes the distributive laws hold by construction (they are `map_add`/`map_zero` of a linear map).
The associativity of concatenation and the unit law (Remark 2.8.5) are recorded as the remaining
proof obligations.

## Convention

In `PathAlgebra`, paths `p : x ⟶* y` and `q : y ⟶* z` multiply as `p * q = p.comp q`, matching
Mathlib's source-to-target `Quiver.Path.comp`. In `BookPathAlgebra`, the displayed product is
reversed: `ofPath q * ofPath p = ofPath (p.comp q)`. Hence its product `a * b` is defined exactly
when the path `b` ends where `a` begins and is the path obtained by first tracing `b`, then `a`,
exactly as Definition 2.8.4 states.
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

/-- The source-to-target implementation underlying the book-facing path algebra of a quiver `Q`.
The basis consists of oriented paths in `Q`, with multiplication given by path concatenation
(zero if the paths are not composable).

This is a (semireducible) `def`, not an `abbrev`, following Mathlib's `MonoidAlgebra` pattern
(`def MonoidAlgebra k G := G →₀ k`). Were it a reducible `abbrev`, instance synthesis would unfold
it to `QuiverPathIndex Q →₀ k` and pick up `Finsupp`'s *pointwise* multiplication
(`Finsupp.instMul` from `Mathlib.Data.Finsupp.Pointwise`), which under `import Mathlib` outranks the
intended path-concatenation ring multiplication built below. As a `def`, instance synthesis (which
unfolds only reducible definitions) no longer sees the `Finsupp` instances, so the path-algebra ring
structure is the unique `Mul`. The `Finsupp` module-level structure is re-exposed explicitly via
`inferInstanceAs` in the instances immediately following; elaboration still unfolds the `def` at
default transparency, so `Finsupp.single`/`Finsupp.lsum`/etc. continue to typecheck at type
`PathAlgebra k Q`. The `DecidableEq Q` parameter is intentionally retained on the carrier because
it selects the path-composition multiplication API defined below. -/
def PathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  QuiverPathIndex Q →₀ k

namespace PathAlgebra

section Instances
variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

/-- The additive-group structure on `PathAlgebra k Q`, re-exposed from `Finsupp`. Needed because
`PathAlgebra` is a `def` (not a reducible `abbrev`), so the `Finsupp` instance is no longer found
for it by instance synthesis. -/
noncomputable instance : AddCommGroup (PathAlgebra k Q) :=
  inferInstanceAs (AddCommGroup (QuiverPathIndex Q →₀ k))

/-- The `k`-module structure on `PathAlgebra k Q`, re-exposed from `Finsupp`. -/
noncomputable instance : Module k (PathAlgebra k Q) :=
  inferInstanceAs (Module k (QuiverPathIndex Q →₀ k))

instance : Inhabited (PathAlgebra k Q) :=
  inferInstanceAs (Inhabited (QuiverPathIndex Q →₀ k))

end Instances

variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

variable {k Q}

/-- The basis element of `PathAlgebra k Q` indexed by an oriented path `x`, i.e. the path `x`
with coefficient `1`. -/
noncomputable def ofPath (x : QuiverPathIndex Q) : PathAlgebra k Q :=
  Finsupp.single x 1

omit [DecidableEq Q] in
/-- Scaling a basis path by `c` reindexes its coefficient: `c • single x 1 = single x c`. Stated at
the underlying `QuiverPathIndex Q →₀ k` type so the `Finsupp.smul_single` rewrite fires directly;
it is applied to `PathAlgebra k Q` goals through the definitional equality (an `exact` closes the
`instances`-transparency gap that would block a direct rewrite). -/
theorem smul_single_one (c : k) (x : QuiverPathIndex Q) :
    c • Finsupp.single x (1 : k) = Finsupp.single x c := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Scaling the zero path algebra element gives zero. Proved at the underlying
`QuiverPathIndex Q →₀ k` type: instance synthesis does not find `SMulZeroClass k (PathAlgebra k Q)`
directly (the `def` wrapper hides the `Finsupp` module from synthesis), so the generic `smul_zero`
is applied at the `Finsupp` type and transported to `PathAlgebra k Q` through the definitional
equality. -/
theorem smul_pathAlgebra_zero (c : k) : c • (0 : PathAlgebra k Q) = 0 :=
  (smul_zero c : c • (0 : QuiverPathIndex Q →₀ k) = 0)

/-- The product of two basis paths: the concatenated path with coefficient `1` when composable,
and `0` otherwise. This is typed as `PathAlgebra k Q` (not the underlying `QuiverPathIndex Q →₀ k`)
so that goals such as `(a * b) • compSingle x y * Finsupp.single z c`, which arise in the
associativity and unit proofs, stay homogeneously typed. Were `compSingle` typed as the raw
`Finsupp`, such a product would mix a `Finsupp`-valued scalar action with the `PathAlgebra`
multiplication and fail the `instances`-transparency type check. `PathAlgebra k Q` is definitionally
`QuiverPathIndex Q →₀ k`, so `compSingle` still feeds the `Finsupp`-typed `mulLinear` below. -/
noncomputable def compSingle (x y : QuiverPathIndex Q) : PathAlgebra k Q :=
  (x.comp y).elim 0 (fun z => Finsupp.single z (1 : k))

/-- On composable basis paths, `compSingle` is the single concatenated path. -/
theorem compSingle_eq {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    compSingle (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨b, d, q⟩
      = Finsupp.single (⟨a, d, p.comp q⟩ : QuiverPathIndex Q) (1 : k) := by
  rw [compSingle, QuiverPathIndex.comp_eq_some]; rfl

/-- On non-composable basis paths, `compSingle` is zero. -/
theorem compSingle_eq_zero {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (h : b ≠ c) :
    compSingle (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨c, d, q⟩ = (0 : PathAlgebra k Q) := by
  rw [compSingle, QuiverPathIndex.comp_eq_none _ _ h]; rfl

/-- Multiplying a trivial path `p_i` on the left: the result is the original path if it starts at
`i`, and zero otherwise. -/
theorem compSingle_nil_left (i a b : Q) (p : Quiver.Path a b) :
    compSingle (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) ⟨a, b, p⟩
      = if i = a then Finsupp.single (⟨a, b, p⟩ : QuiverPathIndex Q) (1 : k) else 0 := by
  by_cases h : i = a
  · subst h
    rw [compSingle_eq, Quiver.Path.nil_comp, if_pos rfl]
  · rw [if_neg h]; exact compSingle_eq_zero _ _ h

/-- Multiplying a trivial path `p_i` on the right: the result is the original path if it ends at
`i`, and zero otherwise. -/
theorem compSingle_nil_right (i a b : Q) (p : Quiver.Path a b) :
    compSingle (⟨a, b, p⟩ : QuiverPathIndex Q) ⟨i, i, Quiver.Path.nil⟩
      = if b = i then Finsupp.single (⟨a, b, p⟩ : QuiverPathIndex Q) (1 : k) else 0 := by
  by_cases h : b = i
  · subst h
    rw [compSingle_eq, Quiver.Path.comp_nil, if_pos rfl]
  · rw [if_neg h]; exact compSingle_eq_zero _ _ h

variable (k Q)

/-- The multiplication of `PathAlgebra k Q`, as a `k`-bilinear map. On basis paths it is path
concatenation; it is extended bilinearly to the whole free module. Phrasing the product as a
`LinearMap` makes all distributive laws hold definitionally (they are `map_add`/`map_zero`). -/
noncomputable def mulLinear :
    (QuiverPathIndex Q →₀ k) →ₗ[k] (QuiverPathIndex Q →₀ k) →ₗ[k] PathAlgebra k Q :=
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
    -- The distributive/annihilation laws are `map_add`/`map_zero` of the bilinear `mulLinear`.
    -- They are stated in term mode (rather than via `change`/`rw`) because a tactic goal
    -- containing `mulLinear k Q a` with `a : PathAlgebra k Q` is not type-correct at the
    -- `instances` transparency level (`mulLinear` expects the underlying `Finsupp`), so `rw`
    -- refuses to fire; term-mode elaboration checks against the goal up to definitional
    -- equality and accepts the defeq `PathAlgebra k Q = QuiverPathIndex Q →₀ k`.
    left_distrib := fun a b c => map_add (mulLinear k Q a) b c
    right_distrib := fun a b c =>
      (LinearMap.congr_fun (map_add (mulLinear k Q) a b) c).trans (LinearMap.add_apply _ _ _)
    zero_mul := fun a =>
      (LinearMap.congr_fun (map_zero (mulLinear k Q)) a).trans (LinearMap.zero_apply a)
    mul_zero := fun a => map_zero (mulLinear k Q a) }

variable {k Q}

theorem mul_def (f g : PathAlgebra k Q) : f * g = mulLinear k Q f g := rfl

/-- On basis paths the product is the concatenation `compSingle`, scaled by the product of the
coefficients. -/
theorem single_mul_single (x y : QuiverPathIndex Q) (a b : k) :
    (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
        (Finsupp.single x a) (Finsupp.single y b))
      = (a * b) • compSingle x y := by
  rw [mul_def, mulLinear]
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq,
    LinearMap.smul_apply, smul_smul]

/-- Scalars commute past the multiplication on the left (the product is `k`-linear in its
first argument). -/
theorem smul_mul (r : k) (a b : PathAlgebra k Q) : (r • a) * b = r • (a * b) :=
  (LinearMap.congr_fun (map_smul (mulLinear k Q) r a) b).trans (LinearMap.smul_apply r _ b)

/-- Scalars commute past the multiplication on the right (the product is `k`-linear in its
second argument). -/
theorem mul_smul' (r : k) (a b : PathAlgebra k Q) : a * (r • b) = r • (a * b) :=
  map_smul (mulLinear k Q a) r b

/-- Associativity of the multiplication on three basis paths. This is where the associativity of
path concatenation (`Quiver.Path.comp_assoc`) enters; the partial composition cases all collapse
to `0`. -/
theorem single_mul_single_assoc (x y z : QuiverPathIndex Q) (a b c : k) :
    (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
        (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
          (Finsupp.single x a) (Finsupp.single y b))
        (Finsupp.single z c))
      = (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
          (Finsupp.single x a)
          (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
            (Finsupp.single y b) (Finsupp.single z c))) := by
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

/-- Linearity induction for `PathAlgebra k Q`: to prove a predicate for every element it suffices
to prove it for `0`, for sums, and for the basis paths `Finsupp.single x a`. This transports
`Finsupp.induction_linear` to `PathAlgebra k Q`. Crucially the step hypotheses are stated with
`PathAlgebra k Q`-typed pieces, rather than the underlying `QuiverPathIndex Q →₀ k` pieces that
`Finsupp.induction_linear` would introduce by unfolding the `def`. Keeping the pieces at
`PathAlgebra k Q` means the ring multiplication in the downstream `mul_assoc`/`one_mul`/`mul_one`
proofs stays homogeneously typed, so `rw` with `add_mul`, `mul_add`, `zero_mul`, `mul_zero`, and
`Finset.sum_mul` continues to fire (a `QuiverPathIndex Q →₀ k` piece fed to the `PathAlgebra k Q`
multiplication is not type-correct at the `instances` transparency level, which blocks `rw`). -/
@[elab_as_elim]
theorem induction_linear {motive : PathAlgebra k Q → Prop} (f : PathAlgebra k Q)
    (zero : motive 0) (add : ∀ g h : PathAlgebra k Q, motive g → motive h → motive (g + h))
    (single : ∀ (x : QuiverPathIndex Q) (a : k), motive (Finsupp.single x a)) : motive f :=
  Finsupp.induction_linear f zero add single

/-- Associativity of path-algebra multiplication, reduced to the basis case via bilinearity. -/
protected theorem mul_assoc (f g h : PathAlgebra k Q) : f * g * h = f * (g * h) := by
  induction f using PathAlgebra.induction_linear with
  | zero => simp only [zero_mul]
  | add f1 f2 hf1 hf2 => rw [add_mul, add_mul, add_mul, hf1, hf2]
  | single x a =>
    induction g using PathAlgebra.induction_linear with
    | zero => simp only [mul_zero, zero_mul]
    | add g1 g2 hg1 hg2 => rw [mul_add, add_mul, add_mul, mul_add, hg1, hg2]
    | single y b =>
      induction h using PathAlgebra.induction_linear with
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
candidate unit of the path algebra (Remark 2.8.5). The summand is written with `ofPath`, whose
declared return type is `PathAlgebra k Q`, so the finite sum genuinely uses the `PathAlgebra k Q`
additive structure. Writing the summand as a bare `Finsupp.single …` (even ascribed to
`PathAlgebra k Q`) would leave the sum in the native `QuiverPathIndex Q →₀ k` additive structure
(the ascription is erased during elaboration), and `Finset.sum_mul`/`Finset.mul_sum` in the unit
proofs would then fail to recognise it as a product in the path-algebra semiring. -/
noncomputable def one [Fintype Q] : PathAlgebra k Q :=
  ∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)

noncomputable instance [Fintype Q] : One (PathAlgebra k Q) := ⟨one k Q⟩

variable {k Q}

theorem one_def [Fintype Q] :
    (1 : PathAlgebra k Q) = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) 1 :=
  rfl

/-- The unit written as a sum of `ofPath` basis paths. Definitionally identical to `one_def`, but
the summand `ofPath` has declared type `PathAlgebra k Q`, so the finite sum genuinely lives in the
`PathAlgebra k Q` additive structure. This is the form the `one_mul`/`mul_one` proofs rewrite with,
so that `Finset.sum_mul`/`Finset.mul_sum` recognise the product in the path-algebra semiring;
`one_def` keeps the `Finsupp.single` form used by downstream clients. -/
theorem one_eq_ofPath_sum [Fintype Q] :
    (1 : PathAlgebra k Q) = ∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) :=
  rfl

/-- The sum of trivial paths is a left unit (Remark 2.8.5). -/
protected theorem one_mul [Fintype Q] (f : PathAlgebra k Q) : (1 : PathAlgebra k Q) * f = f := by
  induction f using PathAlgebra.induction_linear with
  | zero => rw [mul_zero]
  | add f g hf hg => rw [mul_add, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_eq_ofPath_sum, Finset.sum_mul]
    have hterm : ∀ i : Q,
        (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
          (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q))
          (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a))
        = if i = xa then (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a : PathAlgebra k Q)
          else 0 := by
      intro i
      unfold ofPath
      rw [single_mul_single, compSingle_nil_left]
      by_cases h : i = xa
      · rw [one_mul, if_pos h, if_pos h]; exact smul_single_one a _
      · rw [if_neg h, if_neg h]; exact smul_pathAlgebra_zero _
    rw [Finset.sum_eq_single_of_mem xa (Finset.mem_univ xa)
        (fun b _ hb => (hterm b).trans (if_neg hb)), hterm xa, if_pos rfl]

/-- The sum of trivial paths is a right unit (Remark 2.8.5). -/
protected theorem mul_one [Fintype Q] (f : PathAlgebra k Q) : f * (1 : PathAlgebra k Q) = f := by
  induction f using PathAlgebra.induction_linear with
  | zero => rw [zero_mul]
  | add f g hf hg => rw [add_mul, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_eq_ofPath_sum, Finset.mul_sum]
    have hterm : ∀ i : Q,
        (@HMul.hMul (PathAlgebra k Q) (PathAlgebra k Q) (PathAlgebra k Q) _
          (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a)
          (ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q)))
        = if xb = i then (Finsupp.single (⟨xa, xb, xp⟩ : QuiverPathIndex Q) a : PathAlgebra k Q)
          else 0 := by
      intro i
      unfold ofPath
      rw [single_mul_single, compSingle_nil_right]
      by_cases h : xb = i
      · rw [mul_one, if_pos h, if_pos h]; exact smul_single_one a _
      · rw [if_neg h, if_neg h]; exact smul_pathAlgebra_zero _
    rw [Finset.sum_eq_single_of_mem xb (Finset.mem_univ xb)
        (fun b _ hb => (hterm b).trans (if_neg (Ne.symm hb))), hterm xb, if_pos rfl]

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
    (∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) : PathAlgebra k Q) = 1 :=
  one_eq_ofPath_sum.symm

end PathAlgebra

/-! ## The book-facing multiplication order

`PathAlgebra k Q` is retained as the established source-to-target implementation used by later
chapters. Etingof's Definition 2.8.4 uses the opposite convention: a displayed product `a * b`
means first traverse `b`, then traverse `a`. The multiplicative opposite below is therefore not a
mere explanatory equivalence: it is the public construction whose multiplication is literally the
one printed in the book.
-/

/-- The path algebra with Etingof's exact multiplication convention: `a * b` means first trace
`b`, then trace `a`. It has the same additive path basis as `PathAlgebra k Q` and the opposite
multiplication. -/
abbrev BookPathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  (PathAlgebra k Q)ᵐᵒᵖ

namespace BookPathAlgebra

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The book-facing basis vector indexed by an oriented path. -/
noncomputable def ofPath (x : QuiverPathIndex Q) : BookPathAlgebra k Q :=
  MulOpposite.op (PathAlgebra.ofPath (k := k) x)

@[simp]
theorem unop_ofPath (x : QuiverPathIndex Q) :
    MulOpposite.unop (ofPath (k := k) x) = PathAlgebra.ofPath (k := k) x :=
  rfl

/-- Etingof's exact multiplication rule on composable basis paths. If `p : a ⟶* b` is traversed
first and `q : b ⟶* c` second, their book-ordered product is `q * p = p.comp q`. -/
theorem ofPath_mul_ofPath {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    ofPath (k := k) (⟨b, c, q⟩ : QuiverPathIndex Q) *
        ofPath (k := k) (⟨a, b, p⟩ : QuiverPathIndex Q) =
      ofPath (k := k) (⟨a, c, p.comp q⟩ : QuiverPathIndex Q) := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul]
  simp only [unop_ofPath]
  unfold PathAlgebra.ofPath
  rw [PathAlgebra.single_mul_single, one_mul, one_smul, PathAlgebra.compSingle_eq]

/-- Non-composable basis paths multiply to zero in the book-facing path algebra. The right-hand
path is traversed first, so composability requires its target to equal the left-hand path's
source. -/
theorem ofPath_mul_ofPath_eq_zero {a b c d : Q} (p : Quiver.Path a b)
    (q : Quiver.Path c d) (h : b ≠ c) :
    ofPath (k := k) (⟨c, d, q⟩ : QuiverPathIndex Q) *
        ofPath (k := k) (⟨a, b, p⟩ : QuiverPathIndex Q) = 0 := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul]
  simp only [unop_ofPath, MulOpposite.unop_zero]
  unfold PathAlgebra.ofPath
  rw [PathAlgebra.single_mul_single, PathAlgebra.compSingle_eq_zero _ _ h, smul_zero]

/-- The trivial path at vertex `i`, in the book-facing path algebra. -/
noncomputable def trivialPath (i : Q) : BookPathAlgebra k Q :=
  ofPath (k := k) ⟨i, i, Quiver.Path.nil⟩

/-- **Remark 2.8.5.** For finitely many vertices, the sum of the trivial paths is the unit in the
book-facing path algebra. -/
theorem sum_trivialPaths_eq_one [Fintype Q] :
    (∑ i, trivialPath (k := k) (Q := Q) i : BookPathAlgebra k Q) = 1 := by
  apply MulOpposite.unop_injective
  rw [show MulOpposite.unop
      (∑ i, trivialPath (k := k) (Q := Q) i : BookPathAlgebra k Q) =
        ∑ i, MulOpposite.unop (trivialPath (k := k) (Q := Q) i) from
      map_sum MulOpposite.opAddEquiv.symm _ Finset.univ]
  simp only [trivialPath, unop_ofPath, MulOpposite.unop_one]
  exact PathAlgebra.sum_trivialPaths_eq_one k Q

end BookPathAlgebra

end Etingof

-- Although the carrier does not inspect this instance, it deliberately indexes the multiplication
-- API and keeps all `PathAlgebra` operations under one consistent set of assumptions.
attribute [nolint unusedArguments] Etingof.PathAlgebra
