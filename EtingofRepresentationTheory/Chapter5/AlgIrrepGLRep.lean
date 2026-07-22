import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2Core
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime
import EtingofRepresentationTheory.Chapter5.SchurModuleSimple

/-!
# `AlgIrrepGLRep`: the genuine `GL_N(k)`-representation structure on `AlgIrrepGL`

`AlgIrrepGL n lam k` (`Theorem5_23_2.lean`) is, by design, only the underlying
`k`-module of the irreducible algebraic representation `L_λ` — its GL-action is
discarded. This file equips that module with a genuine representation
`AlgIrrepGLRep n lam k : FDRep k (GL_n(k))`, defined as the Schur module
`SchurModule k n λ.toNatWeight` twisted by `det^{-λ.shift}` via `charTwistRep`,
so that the carrier of `AlgIrrepGLRep n lam k` is definitionally `AlgIrrepGL n lam k`.

Two facts are recorded:

* `formalCharacter_algIrrepGLRep_of_shift_zero` — for an already-non-negative
  weight (`λ.shift = 0`) the formal character is the Schur polynomial
  `schurPoly n λ.toNatWeight` (Weyl character formula, `Theorem5_22_1`).
* `algIrrepGLRep_isSimple` — `AlgIrrepGLRep` is irreducible as a
  `GL_n(k)`-representation (over `ℂ`, with `∑ λ.toNatWeight ≤ n`), via the
  character-twist invariance of simplicity and `schurModule_isSimple`.

The twist-invariance of simplicity is isolated as the reusable
`isSimpleModule_charTwistRep`: twisting a representation by a one-dimensional
character does not change its lattice of `k[G]`-submodules.
-/

noncomputable section

namespace Etingof

open Etingof.KernelLemmaKPrime

/-! ## A `k`-submodule stable under a representation is a `k[G]`-submodule -/

section StableSubmodule

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A `k`-submodule `P` of `ρ.asModule` stable under every `ρ g` packages, with the
same underlying set, as a `k[G]`-submodule of `ρ.asModule`. Closure under the whole
group algebra follows from closure under each `ρ g` and the `k`-scalars by linearity
(`MonoidAlgebra.induction_linear`). -/
def Representation.stableSubmodule (ρ : Representation k G V)
    (P : Submodule k ρ.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P) :
    Submodule (MonoidAlgebra k G) ρ.asModule where
  carrier := P
  add_mem' hx hy := P.add_mem hx hy
  zero_mem' := P.zero_mem
  smul_mem' r x hx := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r₁ r₂ h₁ h₂ => rw [add_smul]; exact P.add_mem h₁ h₂
    | single g a =>
        have hsingle : (MonoidAlgebra.single g a : MonoidAlgebra k G) =
            a • MonoidAlgebra.single g (1 : k) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [hsingle, smul_assoc]
        apply P.smul_mem
        rw [Representation.single_smul, one_smul]
        exact hP g x hx

@[simp] theorem Representation.mem_stableSubmodule (ρ : Representation k G V)
    (P : Submodule k ρ.asModule)
    (hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P)
    (x : ρ.asModule) :
    x ∈ Representation.stableSubmodule ρ P hP ↔ x ∈ P :=
  Iff.rfl

end StableSubmodule

/-! ## Twisting by a character preserves simplicity -/

section CharTwistSimple

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- **Character-twist invariance of irreducibility.** If `ρ.asModule` is a simple
`k[G]`-module, then so is `(charTwistRep c ρ).asModule`: twisting `ρ` by a
one-dimensional character `c : G →* kˣ` rescales each `ρ g` by the unit `c g`, so a
`k`-subspace is `ρ`-stable iff it is `charTwistRep c ρ`-stable. The lattice of
subrepresentations — hence simplicity — is unchanged. -/
theorem isSimpleModule_charTwistRep (c : G →* kˣ) (ρ : Representation k G V)
    [hsimp : IsSimpleModule (MonoidAlgebra k G) ρ.asModule] :
    IsSimpleModule (MonoidAlgebra k G) (charTwistRep c ρ).asModule := by
  haveI hnt : Nontrivial ρ.asModule :=
    (Submodule.nontrivial_iff (MonoidAlgebra k G)).mp hsimp.toNontrivial
  haveI : Nontrivial (charTwistRep c ρ).asModule :=
    (show Nontrivial ρ.asModule from hnt)
  haveI : Nontrivial (Submodule (MonoidAlgebra k G) (charTwistRep c ρ).asModule) :=
    (Submodule.nontrivial_iff (MonoidAlgebra k G)).mpr inferInstance
  rw [isSimpleModule_iff]
  refine ⟨fun W => ?_⟩
  -- `P` is the carrier of `W` reinterpreted as a `k`-submodule of `ρ.asModule`
  -- (the two `asModule`s share the same `k`-module structure).
  let P : Submodule k ρ.asModule := W.restrictScalars k
  -- membership in `P` is membership in `W`.
  have hmemP : ∀ x : ρ.asModule, x ∈ P ↔
      (show (charTwistRep c ρ).asModule from x) ∈ W := fun _ => Iff.rfl
  -- `P` is stable under every `ρ g`.
  have hP : ∀ (g : G), ∀ x ∈ P, ρ g (ρ.asModuleEquiv x) ∈ P := by
    intro g x hx
    rw [hmemP] at hx
    have heq : ρ g (ρ.asModuleEquiv x) =
        ((c g)⁻¹ : k) • ((MonoidAlgebra.single g (1 : k)) •
          (show (charTwistRep c ρ).asModule from x)) := by
      rw [Representation.single_smul, one_smul, charTwistRep_apply, smul_smul,
        inv_mul_cancel₀ (Units.ne_zero (c g)), one_smul]
      rfl
    rw [hmemP, heq]
    exact (W.restrictScalars k).smul_mem _ (W.smul_mem _ hx)
  -- Transport simplicity along the carrier-preserving `stableSubmodule`.
  rcases hsimp.eq_bot_or_eq_top (Representation.stableSubmodule ρ P hP) with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro x hx
    exact h x ((Representation.mem_stableSubmodule ρ P hP x).mpr ((hmemP x).mpr hx))
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro x
    exact (hmemP x).mp ((Representation.mem_stableSubmodule ρ P hP x).mp (h x))

/-- **Character-twist invariance of semisimplicity.** If `ρ.asModule` is a semisimple
`k[G]`-module, then so is `(charTwistRep c ρ).asModule`. Twisting `ρ` by a
one-dimensional character `c : G →* kˣ` rescales each `ρ g` by the unit `c g`, so a
`k`-subspace is `ρ`-stable iff it is `charTwistRep c ρ`-stable: the two `k[G]`-submodule
lattices are carrier-identical, hence order-isomorphic, and `ComplementedLattice`
(= semisimplicity) transports across the order isomorphism.

This is the reusable "untwist" step for transferring complete reducibility across a
`det^s`-twist (cf. `Theorem5_23_2_i`). -/
theorem isSemisimpleModule_charTwistRep (c : G →* kˣ) (ρ : Representation k G V)
    [hss : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule] :
    IsSemisimpleModule (MonoidAlgebra k G) (charTwistRep c ρ).asModule := by
  -- carrier of a `charTwistRep c ρ`-submodule is `ρ`-stable
  have hPρ : ∀ (W : Submodule (MonoidAlgebra k G) (charTwistRep c ρ).asModule)
      (g : G), ∀ x ∈ W.restrictScalars k, ρ g (ρ.asModuleEquiv x) ∈ W.restrictScalars k := by
    intro W g x hx
    have heq : ρ g (ρ.asModuleEquiv x) =
        ((c g)⁻¹ : k) • ((MonoidAlgebra.single g (1 : k)) •
          (show (charTwistRep c ρ).asModule from x)) := by
      rw [Representation.single_smul, one_smul, charTwistRep_apply, smul_smul,
        inv_mul_cancel₀ (Units.ne_zero (c g)), one_smul]
      rfl
    rw [heq]
    exact (W.restrictScalars k).smul_mem _ (W.smul_mem _ hx)
  -- carrier of a `ρ`-submodule is `charTwistRep c ρ`-stable
  have hPχ : ∀ (V' : Submodule (MonoidAlgebra k G) ρ.asModule)
      (g : G), ∀ x ∈ V'.restrictScalars k,
        (charTwistRep c ρ) g ((charTwistRep c ρ).asModuleEquiv x) ∈ V'.restrictScalars k := by
    intro V' g x hx
    have heq : (charTwistRep c ρ) g ((charTwistRep c ρ).asModuleEquiv x) =
        ((c g : k)) • ((MonoidAlgebra.single g (1 : k)) • (show ρ.asModule from x)) := by
      rw [Representation.single_smul, one_smul, charTwistRep_apply]
      rfl
    rw [heq]
    exact (V'.restrictScalars k).smul_mem _ (V'.smul_mem _ hx)
  -- carrier-preserving order isomorphism of the two `k[G]`-submodule lattices
  let toρ : Submodule (MonoidAlgebra k G) (charTwistRep c ρ).asModule →
      Submodule (MonoidAlgebra k G) ρ.asModule :=
    fun W => Representation.stableSubmodule ρ (W.restrictScalars k) (hPρ W)
  let toχ : Submodule (MonoidAlgebra k G) ρ.asModule →
      Submodule (MonoidAlgebra k G) (charTwistRep c ρ).asModule :=
    fun V' => Representation.stableSubmodule (charTwistRep c ρ) (V'.restrictScalars k) (hPχ V')
  have mem_toρ : ∀ (W : Submodule (MonoidAlgebra k G) (charTwistRep c ρ).asModule)
      (x : ρ.asModule), x ∈ toρ W ↔ x ∈ W :=
    fun W x => Representation.mem_stableSubmodule ρ _ (hPρ W) x
  have mem_toχ : ∀ (V' : Submodule (MonoidAlgebra k G) ρ.asModule)
      (x : (charTwistRep c ρ).asModule), x ∈ toχ V' ↔ x ∈ V' :=
    fun V' x => Representation.mem_stableSubmodule (charTwistRep c ρ) _ (hPχ V') x
  let e : Submodule (MonoidAlgebra k G) (charTwistRep c ρ).asModule ≃o
      Submodule (MonoidAlgebra k G) ρ.asModule :=
    { toFun := toρ
      invFun := toχ
      left_inv := fun W => SetLike.ext fun x => by rw [mem_toχ, mem_toρ]
      right_inv := fun V' => SetLike.ext fun x => by rw [mem_toρ, mem_toχ]
      map_rel_iff' := by
        intro W₁ W₂
        constructor
        · intro h x hx
          exact (mem_toρ W₂ x).mp (h ((mem_toρ W₁ x).mpr hx))
        · intro h x hx
          exact (mem_toρ W₂ x).mpr (h ((mem_toρ W₁ x).mp hx)) }
  exact (isSemisimpleModule_iff _ _).mpr e.symm.complementedLattice

end CharTwistSimple

/-! ## The genuine representation `AlgIrrepGLRep` -/

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- `λ.toNatWeight` is antitone: shifting an antitone integer weight by a constant
and truncating to `ℕ` preserves the order. -/
theorem DominantWeight.toNatWeight_antitone {n : ℕ} (lam : DominantWeight n) :
    Antitone lam.toNatWeight := by
  intro i j hij
  exact Int.toNat_le_toNat (by simpa [DominantWeight.toNatWeight] using lam.property hij)

/-- The genuine irreducible algebraic representation `L_λ` of `GL_n(k)`:
the Schur module `SchurModule k n λ.toNatWeight` twisted by the character
`det^{-λ.shift}`. Its underlying `k`-module is definitionally `AlgIrrepGL n lam k`. -/
noncomputable def AlgIrrepGLRep (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    FDRep k (Matrix.GeneralLinearGroup (Fin n) k) :=
  FDRep.of (charTwistRep (detChar k n ^ (-(lam.shift : ℤ)))
    (schurModuleRep k n lam.toNatWeight))

/-- The underlying representation of `AlgIrrepGLRep` is the twisted Schur-module
representation. -/
@[simp] theorem algIrrepGLRep_ρ (n : ℕ) (lam : DominantWeight n) :
    (AlgIrrepGLRep n lam k).ρ =
      charTwistRep (detChar k n ^ (-(lam.shift : ℤ))) (schurModuleRep k n lam.toNatWeight) :=
  rfl

/-- When the weight is already non-negative (`λ.shift = 0`), `AlgIrrepGLRep` is the
untwisted Schur module, so its formal character is the Schur polynomial
`schurPoly n λ.toNatWeight` (Weyl character formula). -/
theorem formalCharacter_algIrrepGLRep_of_shift_zero
    [CharZero k] (n : ℕ) (lam : DominantWeight n) (hshift : lam.shift = 0) :
    formalCharacter k n (AlgIrrepGLRep n lam k) = schurPoly n lam.toNatWeight := by
  have hchar : (detChar k n ^ (-(lam.shift : ℤ))) = 1 := by
    rw [hshift]; simp
  have hrep2 :
      charTwistRep (1 : Matrix.GeneralLinearGroup (Fin n) k →* kˣ)
        (schurModuleRep k n lam.toNatWeight) = schurModuleRep k n lam.toNatWeight := by
    ext g v
    simp [charTwistRep_apply]
  have hrep : AlgIrrepGLRep n lam k = SchurModule k n lam.toNatWeight := by
    rw [AlgIrrepGLRep, hchar, hrep2, SchurModule]
  rw [hrep, formalCharacter_schurModule_eq_schurPoly k n lam.toNatWeight
    lam.toNatWeight_antitone]

/-- **Irreducibility of `AlgIrrepGLRep`.** Over `ℂ`, with the weight fitting in the
Schur-Weyl range (`∑ λ.toNatWeight ≤ n`), `AlgIrrepGLRep` is a simple
`GL_n(ℂ)`-representation. Combines `schurModule_isSimple` with the character-twist
invariance of simplicity. -/
theorem algIrrepGLRep_isSimple (n : ℕ) (lam : DominantWeight n)
    (hN : (∑ i, lam.toNatWeight i) ≤ n) :
    IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (Representation.asModule (AlgIrrepGLRep n lam ℂ).ρ) := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Matrix.GeneralLinearGroup (Fin n) ℂ))
      (Representation.asModule (schurModuleRep ℂ n lam.toNatWeight)) :=
    schurModule_isSimple n lam.toNatWeight lam.toNatWeight_antitone hN
  rw [algIrrepGLRep_ρ]
  exact isSimpleModule_charTwistRep (detChar ℂ n ^ (-(lam.shift : ℤ)))
    (schurModuleRep ℂ n lam.toNatWeight)

/-! ## The dual representation and bare-`Representation` forms

For the Peter-Weyl decomposition we need the underlying `Representation`s with
carriers *literally* `AlgIrrepGL`/`AlgIrrepGLDual` (so they tensor and sum to the
right-hand side of Theorem 5.23.2(ii)). `algIrrepGLRepρ` is the det-twisted
Schur-module representation as a bare `Representation` (its carrier is
definitionally `AlgIrrepGL n lam k`, matching `(AlgIrrepGLRep n lam k).ρ`). -/

/-- The genuine irreducible algebraic representation `L_λ` as a bare
`Representation` on the carrier `AlgIrrepGL n lam k`: the Schur module twisted by
`det^{-λ.shift}`. Equals `(AlgIrrepGLRep n lam k).ρ` up to the carrier coercion. -/
noncomputable def algIrrepGLRepρ (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k (Matrix.GeneralLinearGroup (Fin n) k) (AlgIrrepGL n lam k) :=
  charTwistRep (detChar k n ^ (-(lam.shift : ℤ))) (schurModuleRep k n lam.toNatWeight)

/-- The contragredient `L*_λ` as an `FDRep`: by the highest-weight classification
for `GL_n`, the dual of `L_λ` is `L_{-w₀λ}`, so `AlgIrrepGLRepDual` is just
`AlgIrrepGLRep` at the `w₀`-twisted weight. Its carrier is definitionally
`AlgIrrepGLDual n lam k`. -/
noncomputable def AlgIrrepGLRepDual (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    FDRep k (Matrix.GeneralLinearGroup (Fin n) k) :=
  AlgIrrepGLRep n lam.w0Twist k

/-- The contragredient `L*_λ` as a bare `Representation` on the carrier
`AlgIrrepGLDual n lam k`. -/
noncomputable def algIrrepGLRepDualρ (n : ℕ) (lam : DominantWeight n)
    (k : Type*) [Field k] [IsAlgClosed k] :
    Representation k (Matrix.GeneralLinearGroup (Fin n) k) (AlgIrrepGLDual n lam k) :=
  algIrrepGLRepρ n lam.w0Twist k

end Etingof
