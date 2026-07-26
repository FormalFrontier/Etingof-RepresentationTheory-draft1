import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2Core
import EtingofRepresentationTheory.Chapter5.Proposition5_22_2
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLRep

-- These mirror the lakefile's project-wide `[leanOptions]` so the module also type-checks under a
-- bare `lake env lean`, which does not read the lakefile options. `maxSynthPendingDepth 3` clears
-- the deep Schur-module instance chains; `backward.isDefEq.respectTransparency false` restores the
-- full-transparency `isDefEq` the `charTwistRep`/Schur carrier identifications rely on.
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

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

**Weights.** The parametrization up to a simultaneous constant shift is made precise on
`Etingof.DominantWeight`:

* `Etingof.DominantWeight.constShift lam c`: the simultaneous shift `λ ↦ λ + c·1ᴺ` (adding the
  same integer `c` to every entry). This is the weight-side of tensoring `L_λ` with `det^c`.
* `Etingof.DominantWeight.shiftSetoid`: the equivalence relation "differ by a simultaneous constant
  shift", together with `Etingof.SLWeightParam n := Quotient (shiftSetoid n)`, the type that
  parametrizes the irreducible `SL_N`-representations. This is exactly Etingof's "`λ₁ ≥ ⋯ ≥ λ_N` up
  to a simultaneous shift by a constant".

**The `SL_N`-action and the isomorphism `L_λ ≅ L_{λ + c·1ᴺ}`.**

* `Etingof.slRestrict ρ`: the restriction of a `GL_N(k)`-representation to `SL_N(k)` along
  `Matrix.SpecialLinearGroup.toGL`. Applied to `Etingof.algIrrepGLRepρ` this is the bundled
  `SL_N`-action on `L_λ`.
* `Etingof.slRestrict_charTwistRep_detChar_zpow`: any power of the determinant character becomes
  trivial after restriction, so `det`-twists are invisible on `SL_N`. This is the one input that
  makes the whole `GL_N` theory descend.
* `Etingof.algIrrepGL_slEquiv_constShift`: the `SL_N`-equivariant isomorphism
  `L_{λ + c·1ᴺ}|_{SL_N} ≅ L_λ|_{SL_N}` as a `Representation.Equiv`, obtained by restricting the
  `GL_N`-level determinant-twist isomorphism of Proposition 5.22.2 and observing that the twist
  disappears. `Etingof.algIrrepGL_finrank_constShift` is its dimension shadow.

**The parametrization by `SLWeightParam N`.**

* `Etingof.slIsoSetoid n k`: the relation "the `SL_N`-restrictions of `L_λ` and `L_μ` are
  isomorphic" on dominant weights, an equivalence relation because `Representation.Equiv` has
  `refl`/`symm`/`trans`.
* `Etingof.slIrrepClass`: the induced map `SLWeightParam n → Quotient (slIsoSetoid n k)`. It is
  well defined by `Etingof.shiftEquiv_slIso` (shift-equivalent weights give isomorphic `SL_N`
  representations) and surjective by `Etingof.slIrrepClass_surjective`. Injectivity of this map,
  and the statement that the `L_λ|_{SL_N}` exhaust the irreducibles, are the two remaining halves
  of the classification; the latter rests on the `GL_N` highest-weight classification, which this
  development does not yet prove.

**What is intentionally omitted.** Etingof states, and explicitly declines to prove ("we will not
do this here"), that every finite-dimensional `𝔰𝔩(V)`-representation is completely reducible and
every irreducible one is an `L_λ`. Following the project's omission policy, this file carries no
declaration for those assertions; the decision is recorded in `skipped-exercises.md` under
"Remark 5.23.3". The `𝔰𝔩(2)` case that the remark points at is proved independently as
`Etingof.Sl2Irrep.complete_reducibility` (Problem 2.15.1).
-/

open Etingof.KernelLemmaKPrime

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

/-! ## Restriction of `GL_N`-representations to `SL_N`

Etingof's remark is about restricting the `GL(V)`-theory along `SL(V) ⊆ GL(V)`. We build that
restriction and record the one fact that drives the whole descent: the determinant character, and
hence every power of it, becomes trivial on `SL_N`. -/

section SLRestriction

variable {n : ℕ} {k : Type*} [CommRing k] {V : Type*} [AddCommMonoid V] [Module k V]

/-- **Restriction of a `GL_N(k)`-representation to `SL_N(k)`**, along Mathlib's embedding
`Matrix.SpecialLinearGroup.toGL` of the determinant-one matrices into the general linear group.
This is the bundled `SL_N`-action that Remark 5.23.3 is about. -/
def slRestrict (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V) :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k) V :=
  MonoidHom.comp ρ Matrix.SpecialLinearGroup.toGL

@[simp] lemma slRestrict_apply (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (g : Matrix.SpecialLinearGroup (Fin n) k) (v : V) :
    slRestrict ρ g v = ρ (Matrix.SpecialLinearGroup.toGL g) v := rfl

/-- **The determinant character is trivial on `SL_N`.** This is the single input that makes the
`GL(V)`-theory descend to `SL(V)`: the determinant twists that separate `L_λ` from `L_{λ + c·1ᴺ}`
become invisible after restriction. -/
@[simp] lemma detChar_toGL (g : Matrix.SpecialLinearGroup (Fin n) k) :
    detChar k n (Matrix.SpecialLinearGroup.toGL g) = 1 :=
  Units.ext (by simp [detChar, Matrix.GeneralLinearGroup.det])

/-- Twisting by any integer power of the determinant character leaves the restriction to `SL_N`
unchanged: `(det^c · ρ)|_{SL_N} = ρ|_{SL_N}`. -/
lemma slRestrict_charTwistRep_detChar_zpow (c : ℤ)
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V) :
    slRestrict (charTwistRep (detChar k n ^ c) ρ) = slRestrict ρ := by
  ext g v
  simp [MonoidHom.zpow_apply]

end SLRestriction

/-- Transport a categorical isomorphism `FDRep.of ρ ≅ FDRep.of σ` to an isomorphism of the
underlying representations. The underlying linear equivalence is `FDRep.isoToLinearEquiv`, and its
intertwining property is `FDRep.Iso.conj_ρ`, which says exactly that conjugating `ρ g` by it gives
`σ g`. -/
noncomputable def fdRepIsoToEquiv {K : Type} [Field K] {G : Type*} [Monoid G]
    {V W : Type} [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (ρ : Representation K G V) (σ : Representation K G W)
    (α : FDRep.of ρ ≅ FDRep.of σ) : Representation.Equiv ρ σ :=
  Representation.Equiv.mk (FDRep.isoToLinearEquiv α) fun g => by
    have h := FDRep.Iso.conj_ρ α g
    rw [FDRep.of_ρ', FDRep.of_ρ'] at h
    rw [h, LinearEquiv.conj_apply]
    refine LinearMap.ext fun v => ?_
    simp

/-- Restrict an isomorphism of `GL_N`-representations to an isomorphism of their `SL_N`
restrictions. -/
def slRestrictEquiv {n : ℕ} {k : Type*} [CommRing k] {V W : Type*}
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V}
    {σ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) W}
    (E : Representation.Equiv ρ σ) :
    Representation.Equiv (slRestrict ρ) (slRestrict σ) :=
  Representation.Equiv.mk E.toLinearEquiv fun g =>
    E.isIntertwining' (Matrix.SpecialLinearGroup.toGL g)

/-! ## The `SL_N`-equivariant isomorphism `L_λ ≅ L_{λ + c·1ᴺ}`

The `GL_N`-level input is Proposition 5.22.2 in the form
`schurModule_shift_iso_detTwist : L_{μ+1ᴺ} ≅ L_μ ⊗ det`. Restriction to `SL_N` makes the `det`
factor trivial, so `L_{μ+1ᴺ}|_{SL_N} ≅ L_μ|_{SL_N}`; iterating gives the constant shift. The
`det^{-shift}` normalization built into `algIrrepGLRepρ` is invisible for the same reason, which
extends the statement from non-negative to integer weights. -/

section SLEquiv

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

omit [IsAlgClosed k] [CharZero k] in
/-- The determinant twist of Proposition 5.22.2 is the character twist by `detChar`. -/
lemma detTwistedSchurModuleRep_eq_charTwistRep (N : ℕ) (lam : Fin N → ℕ) :
    detTwistedSchurModuleRep k N lam = charTwistRep (detChar k N) (schurModuleRep k N lam) := rfl

omit [IsAlgClosed k] [CharZero k] in
/-- The determinant-twisted Schur module and the Schur module have the same `SL_N`-restriction:
the twisting scalar `det g` is `1` on `SL_N`. -/
lemma slRestrict_detTwistedSchurModuleRep (N : ℕ) (lam : Fin N → ℕ) :
    slRestrict (detTwistedSchurModuleRep k N lam) = slRestrict (schurModuleRep k N lam) := by
  rw [detTwistedSchurModuleRep_eq_charTwistRep, ← zpow_one (detChar k N)]
  exact slRestrict_charTwistRep_detChar_zpow 1 _

/-- **One shift step, `SL_N`-equivariantly.** Restricting Proposition 5.22.2's determinant-twist
isomorphism `L_{μ+1ᴺ} ≅ L_μ ⊗ det` to `SL_N`, where the `det` factor is trivial. -/
theorem schurModule_slEquiv_succ (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (Representation.Equiv (slRestrict (schurModuleRep k N (fun i => lam i + 1)))
      (slRestrict (schurModuleRep k N lam))) := by
  obtain ⟨e⟩ := schurModule_shift_iso_detTwist k N lam hlam
  refine ⟨?_⟩
  have E := slRestrictEquiv (fdRepIsoToEquiv _ _ e)
  rwa [slRestrict_detTwistedSchurModuleRep N lam] at E

omit [IsAlgClosed k] [CharZero k] in
/-- Transporting along an equality of `ℕ`-weights. Stated separately because rewriting the weight
inside `slRestrict (schurModuleRep k N ·)` also rewrites the carrier type. -/
theorem schurModule_slEquiv_congr (N : ℕ) {lam mu : Fin N → ℕ} (h : lam = mu) :
    Nonempty (Representation.Equiv (slRestrict (schurModuleRep k N lam))
      (slRestrict (schurModuleRep k N mu))) := by
  subst h; exact ⟨Representation.Equiv.refl _⟩

/-- **Constant `+m` shift, `SL_N`-equivariantly.** Iterating `schurModule_slEquiv_succ`. -/
theorem schurModule_slEquiv_add_const (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) (m : ℕ) :
    Nonempty (Representation.Equiv (slRestrict (schurModuleRep k N (fun i => lam i + m)))
      (slRestrict (schurModuleRep k N lam))) := by
  induction m with
  | zero =>
    exact schurModule_slEquiv_congr (k := k) N
      (show (fun i => lam i + 0) = lam by funext i; omega)
  | succ m ih =>
    obtain ⟨E⟩ := ih
    obtain ⟨F⟩ := schurModule_slEquiv_succ (k := k) N (fun i => lam i + m)
      (fun a b h => Nat.add_le_add_right (hlam h) m)
    obtain ⟨G⟩ := schurModule_slEquiv_congr (k := k) N
      (show (fun i => lam i + (m + 1)) = (fun i => (lam i + m) + 1) by funext i; omega)
    exact ⟨(G.trans F).trans E⟩

omit [CharZero k] in
/-- The `SL_N`-restriction of `L_λ` is the `SL_N`-restriction of the underlying Schur module: the
`det^{-λ.shift}` normalization built into `algIrrepGLRepρ` is invisible on `SL_N`. -/
lemma slRestrict_algIrrepGLRepρ {n : ℕ} (lam : DominantWeight n) :
    slRestrict (algIrrepGLRepρ n lam k) = slRestrict (schurModuleRep k n lam.toNatWeight) :=
  slRestrict_charTwistRep_detChar_zpow _ _

/-- **The `SL_N`-equivariant isomorphism `L_{λ + c·1ᴺ} ≅ L_λ` (Remark 5.23.3).** On `SL(V)` the
determinant character is trivial, so the `GL(V)`-representations `L_λ` and its determinant twists
`L_{λ + c·1ᴺ}` become isomorphic. This is the representation-level statement whose dimension
shadow is `algIrrepGL_finrank_constShift`.
(Etingof Remark 5.23.3) -/
theorem algIrrepGL_slEquiv_constShift {n : ℕ} (lam : DominantWeight n) (c : ℤ) :
    Nonempty (Representation.Equiv (slRestrict (algIrrepGLRepρ n (lam.constShift c) k))
      (slRestrict (algIrrepGLRepρ n lam k))) := by
  rw [slRestrict_algIrrepGLRepρ, slRestrict_algIrrepGLRepρ]
  have ha_anti : Antitone lam.toNatWeight := toNatWeight_antitone lam
  have hb_anti : Antitone (lam.constShift c).toNatWeight := toNatWeight_antitone (lam.constShift c)
  set Δ : ℤ := c + ((lam.constShift c).shift : ℤ) - (lam.shift : ℤ) with hΔdef
  have hrel : ∀ i, ((lam.constShift c).toNatWeight i : ℤ) = (lam.toNatWeight i : ℤ) + Δ := by
    intro i
    rw [toNatWeight_cast (lam.constShift c) i, toNatWeight_cast lam i,
      DominantWeight.constShift_val, hΔdef]
    ring
  rcases le_total 0 Δ with hΔ | hΔ
  · obtain ⟨G⟩ := schurModule_slEquiv_congr (k := k) n
      (show (lam.constShift c).toNatWeight = (fun i => lam.toNatWeight i + Δ.toNat) by
        funext i; have := hrel i; omega)
    obtain ⟨E⟩ := schurModule_slEquiv_add_const (k := k) n lam.toNatWeight ha_anti Δ.toNat
    exact ⟨G.trans E⟩
  · obtain ⟨G⟩ := schurModule_slEquiv_congr (k := k) n
      (show lam.toNatWeight = (fun i => (lam.constShift c).toNatWeight i + (-Δ).toNat) by
        funext i; have := hrel i; omega)
    obtain ⟨E⟩ := schurModule_slEquiv_add_const (k := k) n (lam.constShift c).toNatWeight hb_anti
      (-Δ).toNat
    exact ⟨(G.trans E).symm⟩

end SLEquiv

/-! ## The parametrization of the `L_λ|_{SL_N}` by `SLWeightParam N` -/

section SLParam

variable (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

/-- **Isomorphism of `SL_N`-restrictions**, as an equivalence relation on dominant weights: `λ` and
`μ` are related when `L_λ` and `L_μ` become isomorphic after restricting to `SL_N`. It is an
equivalence relation because `Representation.Equiv` carries `refl`, `symm` and `trans`. -/
def slIsoSetoid : Setoid (DominantWeight n) where
  r lam mu := Nonempty (Representation.Equiv (slRestrict (algIrrepGLRepρ n lam k))
    (slRestrict (algIrrepGLRepρ n mu k)))
  iseqv :=
    { refl := fun _ => ⟨Representation.Equiv.refl _⟩
      symm := fun ⟨E⟩ => ⟨E.symm⟩
      trans := fun ⟨E⟩ ⟨F⟩ => ⟨E.trans F⟩ }

variable {n k}

/-- **Shift-equivalent weights give isomorphic `SL_N`-representations.** This is what makes the
parametrization of the `L_λ|_{SL_N}` by `SLWeightParam N` well defined: the shift relation refines
the isomorphism relation. -/
theorem shiftEquiv_slIso {lam mu : DominantWeight n}
    (h : DominantWeight.ShiftEquiv lam mu) : (slIsoSetoid n k).r lam mu := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨(algIrrepGL_slEquiv_constShift (k := k) lam c).some.symm⟩

variable (n k)

/-- **The parametrization map.** Etingof's "the irreducible `SL(V)`-representations are
parametrized by `λ₁ ≥ ⋯ ≥ λ_N` up to a simultaneous shift by a constant" says that
`λ ↦ L_λ|_{SL_N}` descends to `SLWeightParam N` and is a bijection onto the irreducibles. The
descent is `shiftEquiv_slIso`; the resulting map lands in the isomorphism classes of the
`SL_N`-restrictions of the `L_λ`. -/
def slIrrepClass : SLWeightParam n → Quotient (slIsoSetoid n k) :=
  Quotient.map' id fun _ _ h => shiftEquiv_slIso h

@[simp] lemma slIrrepClass_mk (lam : DominantWeight n) :
    slIrrepClass n k (Quotient.mk _ lam) = Quotient.mk _ lam := rfl

/-- The parametrization map is surjective: every `SL_N`-restriction `L_λ|_{SL_N}` is named by the
shift class of `λ`. Injectivity, i.e. that weights in different shift classes give
non-isomorphic `SL_N`-representations, is not proved here. -/
theorem slIrrepClass_surjective : Function.Surjective (slIrrepClass n k) := by
  intro q
  induction q using Quotient.inductionOn with
  | h lam => exact ⟨Quotient.mk _ lam, rfl⟩

end SLParam

end Etingof
