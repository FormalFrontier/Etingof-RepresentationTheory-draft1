import Mathlib
import Batteries.Util.ProofWanted
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2Core
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2

/-!
# Remark 5.23.3: Extension of the GL(V) theory to 𝔰𝔩(V) and SL(V)

Etingof's Remark 5.23.3 observes that, since `𝔰𝔩(V)` (traceless operators) is the quotient of
`𝔤𝔩(V)` by scalars and `SL(V)` is the subgroup of determinant-`1` operators, the classification of
algebraic representations of `GL(V)` (Theorem 5.23.2) carries over to `𝔰𝔩(V)` / `SL(V)`. The one
change is that the determinant character becomes trivial: on `SL(V)` the representation `L_λ` and
its determinant twist `L_{λ + 1ᴺ}` coincide, so the irreducibles are parametrized by dominant
weights `λ₁ ≥ ⋯ ≥ λ_N` only up to a simultaneous shift by a constant. Etingof also states,
without proof ("we will not do this here"), that every finite-dimensional `𝔰𝔩(V)`-representation is
completely reducible and every irreducible is an `L_λ`. For `dim V = 2` this recovers the
representation theory of `𝔰𝔩(2)` from Problem 2.15.1.

## What is formalized here

The provable content of the remark is the parametrization up to a
simultaneous constant shift. We make this precise on `Etingof.DominantWeight`:

* `Etingof.DominantWeight.constShift lam c`: the simultaneous shift `λ ↦ λ + c·1ᴺ` (adding the
  same integer `c` to every entry). This is the weight-side of tensoring `L_λ` with `det^c`.
* `Etingof.DominantWeight.shiftSetoid`: the equivalence relation "differ by a simultaneous constant
  shift", together with `Etingof.SLWeightParam n := Quotient (shiftSetoid n)`, the type that
  parametrizes the irreducible `SL_N`-representations. This is exactly Etingof's "`λ₁ ≥ ⋯ ≥ λ_N` up
  to a simultaneous shift by a constant".

The dimension-level shadow of the `SL(V)` isomorphism is proved as a `theorem`; the remaining
assertion is recorded with `proof_wanted`, because the book omits its proof:

* `Etingof.algIrrepGL_finrank_constShift`: the dimension-level shadow of `L_λ ≅ L_{λ + c·1ᴺ}`,
  proved as a `theorem`. Twisting by a power of the (one-dimensional) determinant character does
  not change the underlying dimension, so `dim L_λ = dim L_{λ + c·1ᴺ}` (proved via the `+1`
  det-twist identity of Proposition 5.22.2, iterated). This is the consequence of the
  `SL(V)` isomorphism available here: an `SL_N`-equivariant isomorphism
  would require an `SL_N`-action on `AlgIrrepGL`, which is not constructed here.
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

/-- Two dominant weights are shift-equivalent when they differ by a simultaneous constant shift,
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

/-- **Determinant is trivial on `SL_N`**, the source of the `SL(V)` identification. For an element
`g` of the special linear group, the determinant of the underlying matrix is `1`; hence the
determinant character `det^c` acts trivially and `L_λ ≅ L_{λ + c·1ᴺ}` as `SL_N`-representations. -/
lemma specialLinear_det_eq_one {n : ℕ} {k : Type*} [CommRing k]
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (g : Matrix (Fin n) (Fin n) k).det = 1 :=
  g.property

/-- The non-negative weight `λ.toNatWeight` recovers `λ` up to its shift:
`(λ.toNatWeight i : ℤ) = λ_i + shift`. The shift is chosen (as the negative of the minimal
entry) so that `λ_i + shift ≥ 0`, hence the `Int.toNat` in `toNatWeight` is exact. -/
private lemma toNatWeight_cast {n : ℕ} (lam : DominantWeight n) (i : Fin n) :
    (lam.toNatWeight i : ℤ) = lam.val i + (lam.shift : ℤ) := by
  have hnonneg : (0 : ℤ) ≤ lam.val i + (lam.shift : ℤ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
    have hlast : lam.val (Fin.last m) ≤ lam.val i := lam.property (Fin.le_last i)
    change (0 : ℤ) ≤ lam.val i + (((-(lam.val (Fin.last m))).toNat : ℕ) : ℤ)
    omega
  change (((lam.val i + (lam.shift : ℤ)).toNat : ℕ) : ℤ) = lam.val i + (lam.shift : ℤ)
  rw [Int.toNat_of_nonneg hnonneg]

/-- `λ.toNatWeight` is antitone: shifting an antitone integer weight by a constant and clamping
at `0` (which never triggers, by `toNatWeight_cast`'s nonnegativity) preserves the order. -/
private lemma toNatWeight_antitone {n : ℕ} (lam : DominantWeight n) :
    Antitone lam.toNatWeight := by
  intro i j hij
  simp only [DominantWeight.toNatWeight]
  exact Int.toNat_le_toNat (by have := lam.property hij; omega)

/-- **Single `+1` step (dimension shadow of Proposition 5.22.2).** For an antitone `ℕ`-weight `μ`,
tensoring the Schur module `L_μ` by the one-dimensional determinant character gives `L_{μ + 1ᴺ}`
without changing the underlying vector space, so the two Schur modules have equal dimension. This
is the dimension consequence of `schurModule_shift_iso_detTwist`. -/
private lemma finrank_schurModuleSubmodule_succ {N : ℕ} {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (μ : Fin N → ℕ) (hμ : Antitone μ) :
    Module.finrank k (SchurModuleSubmodule k N (fun i => μ i + 1))
      = Module.finrank k (SchurModuleSubmodule k N μ) := by
  obtain ⟨e⟩ := schurModule_shift_iso_detTwist k N μ hμ
  exact (FDRep.isoToLinearEquiv e).finrank_eq

/-- **Constant `+m` shift preserves the Schur-module dimension.** Iterating the single-step
`+1` identity (`finrank_schurModuleSubmodule_succ`): for an antitone `ℕ`-weight `μ` and any
`m : ℕ`, `dim L_{μ + m·1ᴺ} = dim L_μ`. -/
private lemma finrank_schurModuleSubmodule_add_const {N : ℕ} {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (μ : Fin N → ℕ) (hμ : Antitone μ) (m : ℕ) :
    Module.finrank k (SchurModuleSubmodule k N (fun i => μ i + m))
      = Module.finrank k (SchurModuleSubmodule k N μ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have key : Module.finrank k (SchurModuleSubmodule k N (fun i => μ i + (m + 1)))
        = Module.finrank k (SchurModuleSubmodule k N (fun i => μ i + m)) := by
      have hidx : (fun i => μ i + (m + 1)) = (fun i => (μ i + m) + 1) := by
        funext i; omega
      rw [hidx]
      exact finrank_schurModuleSubmodule_succ (fun j => μ j + m)
        (fun a b h => Nat.add_le_add_right (hμ h) m)
    rw [key, ih]

/-- **Dimension-level statement of `L_λ ≅ L_{λ + c·1ᴺ}` (Remark 5.23.3).** Tensoring `L_λ` with the
`c`-th power of the one-dimensional determinant character does not change the underlying dimension,
so `dim L_λ = dim L_{λ + c·1ᴺ}`. On `SL(V)` (where `det = 1`, `specialLinear_det_eq_one`) this
common dimension reflects an isomorphism of `SL_N`-representations; capturing that
isomorphism `SL_N`-equivariantly would require an `SL_N`-action on `AlgIrrepGL`, which this
development does not build, so only the dimension identity is stated here.

The two `AlgIrrepGL` carriers are `SchurModuleSubmodule k n (·).toNatWeight` at the two dominant
weights; `constShift c` adds the same integer `c` to every entry, so the two `ℕ`-valued weights
`(lam.constShift c).toNatWeight` and `lam.toNatWeight` differ by a single constant `Δ` (whichever
is pointwise larger equals the other plus `|Δ|`). The identity then follows from
`finrank_schurModuleSubmodule_add_const`. As with the rest of the Schur–Weyl / character theory in
this chapter, this lives over an algebraically closed field of characteristic zero.
(Etingof Remark 5.23.3) -/
theorem algIrrepGL_finrank_constShift
    {n : ℕ} {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    (lam : DominantWeight n) (c : ℤ) :
    Module.finrank k (AlgIrrepGL n (lam.constShift c) k)
      = Module.finrank k (AlgIrrepGL n lam k) := by
  change Module.finrank k (SchurModuleSubmodule k n (lam.constShift c).toNatWeight)
    = Module.finrank k (SchurModuleSubmodule k n lam.toNatWeight)
  have ha_anti : Antitone lam.toNatWeight := toNatWeight_antitone lam
  have hb_anti : Antitone (lam.constShift c).toNatWeight := toNatWeight_antitone (lam.constShift c)
  set Δ : ℤ := c + ((lam.constShift c).shift : ℤ) - (lam.shift : ℤ) with hΔdef
  have hrel : ∀ i, ((lam.constShift c).toNatWeight i : ℤ) = (lam.toNatWeight i : ℤ) + Δ := by
    intro i
    rw [toNatWeight_cast (lam.constShift c) i, toNatWeight_cast lam i,
      DominantWeight.constShift_val, hΔdef]
    ring
  rcases le_total 0 Δ with hΔ | hΔ
  · have hbrw : (lam.constShift c).toNatWeight = (fun i => lam.toNatWeight i + Δ.toNat) := by
      funext i; have := hrel i; omega
    rw [hbrw]
    exact finrank_schurModuleSubmodule_add_const lam.toNatWeight ha_anti Δ.toNat
  · have harw : lam.toNatWeight = (fun i => (lam.constShift c).toNatWeight i + (-Δ).toNat) := by
      funext i; have := hrel i; omega
    rw [harw]
    exact (finrank_schurModuleSubmodule_add_const (lam.constShift c).toNatWeight hb_anti
      (-Δ).toNat).symm

open LieAlgebra in
/-- **Complete reducibility of finite-dimensional `𝔰𝔩(V)`-representations (Remark 5.23.3).** Every
finite-dimensional `𝔰𝔩_N(k)`-module `M` is completely reducible: every `𝔰𝔩_N`-submodule `N` has an
`𝔰𝔩_N`-complement `N'` (`IsCompl N N'`, i.e. `M = N ⊕ N'`). This is the same "every submodule is a
direct summand" formulation as the `𝔰𝔩(2)` case `Etingof.Sl2Irrep.complete_reducibility`
(Problem 2.15.1), to which this specializes for `N = 2`.

Etingof states this without proof ("we will not do this here"), so it is recorded via
`proof_wanted`. The companion assertion, that every irreducible is of the
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
