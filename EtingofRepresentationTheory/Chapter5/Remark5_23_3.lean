import Mathlib
import Batteries.Util.ProofWanted
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2Core

/-!
# Remark 5.23.3: Extension of the GL(V) theory to 𝔰𝔩(V) and SL(V)

Etingof's Remark 5.23.3 observes that, since `𝔰𝔩(V)` (traceless operators) is the quotient of
`𝔤𝔩(V)` by scalars and `SL(V)` is the subgroup of determinant-`1` operators, the classification of
algebraic representations of `GL(V)` (Theorem 5.23.2) carries over to `𝔰𝔩(V)` / `SL(V)`. The one
change is that the determinant character becomes trivial: on `SL(V)` the representation `L_λ` and
its determinant twist `L_{λ + 1ᴺ}` coincide, so the irreducibles are parametrized by dominant
weights `λ₁ ≥ ⋯ ≥ λ_N` **only up to a simultaneous shift by a constant**. Etingof also states,
without proof ("we will not do this here"), that every finite-dimensional `𝔰𝔩(V)`-representation is
completely reducible and every irreducible is an `L_λ`. For `dim V = 2` this recovers the
representation theory of `𝔰𝔩(2)` from Problem 2.15.1.

## What is formalized here

The load-bearing, genuinely provable content of the remark is the **parametrization up to a
simultaneous constant shift**. We make this precise on `Etingof.DominantWeight`:

* `Etingof.DominantWeight.constShift lam c`: the simultaneous shift `λ ↦ λ + c·1ᴺ` (adding the
  same integer `c` to every entry). This is the weight-side of tensoring `L_λ` with `det^c`.
* `Etingof.DominantWeight.shiftSetoid`: the equivalence relation "differ by a simultaneous constant
  shift", together with `Etingof.SLWeightParam n := Quotient (shiftSetoid n)`, the type that
  parametrizes the irreducible `SL_N`-representations. This is exactly Etingof's "`λ₁ ≥ ⋯ ≥ λ_N` up
  to a simultaneous shift by a constant".

The remaining two assertions are recorded with `proof_wanted` (no `sorry`, no axiom), because they
are either disavowed by the book or require representation-theoretic structure on the `L_λ` that
this development does not build:

* `Etingof.algIrrepGL_finrank_constShift`: the dimension-level shadow of `L_λ ≅ L_{λ + c·1ᴺ}`.
  Twisting by a power of the (one-dimensional) determinant character does not change the underlying
  dimension, so `dim L_λ = dim L_{λ + c·1ᴺ}`. This is the statable consequence of the `SL(V)`
  isomorphism at the current infrastructure level: an honest `SL_N`-equivariant isomorphism would
  require an `SL_N`-action on `AlgIrrepGL`, which is not constructed here.
* `Etingof.sl_finiteDimensional_completely_reducible`: complete reducibility of an arbitrary
  finite-dimensional `𝔰𝔩(V)`-module, stated in the same "every submodule has a complement" form as
  the `𝔰𝔩(2)` case `Etingof.Sl2Irrep.complete_reducibility` (Problem 2.15.1). Etingof explicitly
  omits the proof ("we will not do this here"); the companion assertion that every irreducible is an
  `L_λ` is the highest-weight classification, whose parameter set is `SLWeightParam N` above.
-/

namespace Etingof

namespace DominantWeight

variable {n : ℕ}

/-- **Simultaneous constant shift** `λ ↦ λ + c·1ᴺ`: add the same integer `c` to every entry of a
dominant weight. This is the effect on highest weights of tensoring `L_λ` with the `c`-th power of
the determinant character `det^c`. Adding a constant preserves the weakly-decreasing (antitone)
condition, so the result is again a dominant weight. -/
def constShift (lam : DominantWeight n) (c : ℤ) : DominantWeight n :=
  ⟨fun i => lam.val i + c, fun _ _ h => by dsimp only; have := lam.property h; omega⟩

@[simp] lemma constShift_val (lam : DominantWeight n) (c : ℤ) (i : Fin n) :
    (lam.constShift c).val i = lam.val i + c := rfl

@[simp] lemma constShift_zero (lam : DominantWeight n) : lam.constShift 0 = lam := by
  apply Subtype.ext; funext i; simp

lemma constShift_constShift (lam : DominantWeight n) (c d : ℤ) :
    (lam.constShift c).constShift d = lam.constShift (c + d) := by
  apply Subtype.ext; funext i; simp [add_assoc]

/-- Two dominant weights are **shift-equivalent** when they differ by a simultaneous constant shift,
i.e. `μ = λ + c·1ᴺ` for some `c : ℤ`. On `SL(V)` this is exactly the relation that identifies
`L_λ` with its determinant twists, so shift-equivalence classes index the irreducibles of `SL_N`. -/
def ShiftEquiv (lam mu : DominantWeight n) : Prop := ∃ c : ℤ, mu = lam.constShift c

/-- Shift-equivalence is an equivalence relation on dominant weights. -/
def shiftSetoid (n : ℕ) : Setoid (DominantWeight n) where
  r := ShiftEquiv
  iseqv :=
    { refl := fun lam => ⟨0, (lam.constShift_zero).symm⟩
      symm := fun {lam mu} ⟨c, hc⟩ => ⟨-c, by
        apply Subtype.ext; funext i; subst hc; simp⟩
      trans := fun {lam mu nu} ⟨c, hc⟩ ⟨d, hd⟩ => ⟨c + d, by
        subst hc; subst hd; rw [constShift_constShift]⟩ }

@[simp] lemma shiftSetoid_r (lam mu : DominantWeight n) :
    (shiftSetoid n).r lam mu ↔ ∃ c : ℤ, mu = lam.constShift c := Iff.rfl

end DominantWeight

/-- **The parameter set for the irreducible representations of `SL_N`.** By Remark 5.23.3 the
irreducibles of `SL(V)` are the images of the `GL(V)`-irreducibles `L_λ`, with `L_λ` and
`L_{λ + c·1ᴺ}` identified; equivalently they are parametrized by dominant weights
`λ₁ ≥ ⋯ ≥ λ_N` up to a simultaneous constant shift. -/
abbrev SLWeightParam (n : ℕ) := Quotient (DominantWeight.shiftSetoid n)

/-- **Determinant is trivial on `SL_N`** — the source of the `SL(V)` identification. For an element
`g` of the special linear group, the determinant of the underlying matrix is `1`; hence the
determinant character `det^c` acts trivially and `L_λ ≅ L_{λ + c·1ᴺ}` as `SL_N`-representations. -/
lemma specialLinear_det_eq_one {n : ℕ} {k : Type*} [CommRing k]
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (g : Matrix (Fin n) (Fin n) k).det = 1 :=
  g.property

/-- **Dimension-level statement of `L_λ ≅ L_{λ + c·1ᴺ}` (Remark 5.23.3).** Tensoring `L_λ` with the
`c`-th power of the one-dimensional determinant character does not change the underlying dimension,
so `dim L_λ = dim L_{λ + c·1ᴺ}`. On `SL(V)` (where `det = 1`, `specialLinear_det_eq_one`) this
common dimension reflects an actual isomorphism of `SL_N`-representations; capturing that
isomorphism `SL_N`-equivariantly would require an `SL_N`-action on `AlgIrrepGL`, which this
development does not build, so we record the statable dimension identity.
(Etingof Remark 5.23.3) -/
proof_wanted algIrrepGL_finrank_constShift
    {n : ℕ} {k : Type*} [Field k] [IsAlgClosed k]
    (lam : DominantWeight n) (c : ℤ) :
    Module.finrank k (AlgIrrepGL n (lam.constShift c) k)
      = Module.finrank k (AlgIrrepGL n lam k)

open LieAlgebra in
/-- **Complete reducibility of finite-dimensional `𝔰𝔩(V)`-representations (Remark 5.23.3).** Every
finite-dimensional `𝔰𝔩_N(k)`-module `M` is completely reducible: every `𝔰𝔩_N`-submodule `N` has an
`𝔰𝔩_N`-complement `N'` (`IsCompl N N'`, i.e. `M = N ⊕ N'`). This is the same "every submodule is a
direct summand" formulation as the `𝔰𝔩(2)` case `Etingof.Sl2Irrep.complete_reducibility`
(Problem 2.15.1), to which this specializes for `N = 2`.

Etingof states this without proof ("we will not do this here"), so it is recorded via
`proof_wanted` — no `sorry`, no axiom. The companion assertion, that every irreducible is of the
form `L_λ`, is the highest-weight classification; its parameter set is `SLWeightParam N` (dominant
weights up to a simultaneous constant shift). Stating that classification `𝔰𝔩_N`-equivariantly would
require an `𝔰𝔩_N`-action on the `L_λ`, which this development does not build.
(Etingof Remark 5.23.3) -/
proof_wanted sl_finiteDimensional_completely_reducible
    {n : ℕ} {k : Type*} [Field k] [CharZero k]
    {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [LieRingModule (SpecialLinear.sl (Fin n) k) M]
    [LieModule k (SpecialLinear.sl (Fin n) k) M]
    (N : LieSubmodule k (SpecialLinear.sl (Fin n) k) M) :
    ∃ N' : LieSubmodule k (SpecialLinear.sl (Fin n) k) M, IsCompl N N'

end Etingof
