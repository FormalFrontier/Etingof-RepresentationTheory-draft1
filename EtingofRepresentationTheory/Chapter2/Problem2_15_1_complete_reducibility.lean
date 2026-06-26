import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dimension.Finite
import EtingofRepresentationTheory.Chapter2.Sl2Irrep

/-!
# Complete reducibility of finite-dimensional `sl(2)`-representations (Problem 2.15.1(h)–(k))

Etingof Problem 2.15.1(h)–(k) proves **Weyl's complete-reducibility theorem for
`sl(2)`**: every finite-dimensional representation of `sl(2)` is a direct sum of
the irreducibles `V_λ`. The book gives the elementary **Casimir argument** (not the
general Weyl theorem, which is not in Mathlib):

* **(h)** On an indecomposable `V`, the Casimir `C = EF + FE + H²/2` has a single
  eigenvalue `λ(λ+2)/2` for some `λ ∈ ℕ` (generalized eigenspaces of the central
  element `C` are subrepresentations, so an indecomposable `V` lives in one block).
* **(i)** `V` has a subrep `W ≅ V_λ` with `V/W ≅ n·V_λ` (use (h) + a minimal
  counterexample).
* **(j)** the `H`-eigenspace `V(λ)` is `(n+1)`-dimensional, and `{Fʲvᵢ}` is a basis
  of `V`. The key sub-lemma: if `Fx = 0` and `Hx = μx` with `x ≠ 0`, then
  `Cx = μ(μ-2)/2 · x`, which forces `μ = -λ` (the lowest weight is `-λ`).
* **(k)** `Wᵢ = span(vᵢ, Fvᵢ, …, F^λ vᵢ)` are subreps with `V = ⊕Wᵢ`, each `≅ V_λ`,
  contradicting indecomposability unless `n = 0`, i.e. `V` is irreducible.

## What is in this file

The reusable **Casimir eigenvalue toolkit** at the level of an *arbitrary*
`sl(2)`-module `M` (operators `E = ⁅sl2_e, ·⁆`, `F = ⁅sl2_f, ·⁆`, `H = ⁅sl2_h, ·⁆`):

* `casimir M : Module.End ℂ M`, the Casimir operator `C = EF + FE + H²/2`, with its
  unfolding `casimir_apply`.
* `casimir_highest_weight`: on a highest-weight vector (`Ex = 0`, `Hx = μx`),
  `Cx = μ(μ+2)/2 · x`. This is the general-module form of `casimir_eq_scalar_lambda`
  and of `casimir_cgHW`, and is the input to (h)/(i).
* `casimir_lowest_weight`: on a lowest-weight vector (`Fx = 0`, `Hx = μx`),
  `Cx = μ(μ-2)/2 · x`. This is **the key sub-lemma of (j)** (the book's
  "if `Fx = 0` and `Hx = μx` then `Cx = μ(μ-2)/2·x`").

The final complete-reducibility statement `complete_reducibility` is recorded here
in its cleanest equivalent form — *every `sl(2)`-submodule of a finite-dimensional
module has an `sl(2)`-complement* — with the proof left as `sorry` pending the
(h)–(k) assembly, which is being tracked as dependency-ordered follow-up issues.

The Casimir computations rely only on the `sl(2)`-triple bracket relations
`⁅E,F⁆ = H`, `⁅H,E⁆ = 2E`, `⁅H,F⁆ = -2F` (`Sl2Irrep.lie_e_f` etc.) and the Leibniz
rule, so they hold for *any* `sl(2)`-module, finite-dimensional or not.
-/

open Etingof Etingof.Sl2Irrep

namespace Etingof.Sl2Irrep

section Casimir

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule sl2 M] [LieModule ℂ sl2 M]

/-- **The Casimir operator `C = EF + FE + H²/2`** on an arbitrary `sl(2)`-module `M`,
where `E = ⁅sl2_e, ·⁆`, `F = ⁅sl2_f, ·⁆`, `H = ⁅sl2_h, ·⁆` are the actions of the
standard `sl(2)`-triple. It is a genuine element of `Module.End ℂ M`, built from the
Lie-module structure map `LieModule.toEnd`. -/
noncomputable def casimir (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule sl2 M] [LieModule ℂ sl2 M] : Module.End ℂ M :=
  LieModule.toEnd ℂ sl2 M sl2_e * LieModule.toEnd ℂ sl2 M sl2_f
    + LieModule.toEnd ℂ sl2 M sl2_f * LieModule.toEnd ℂ sl2 M sl2_e
    + (2⁻¹ : ℂ) • (LieModule.toEnd ℂ sl2 M sl2_h * LieModule.toEnd ℂ sl2 M sl2_h)

/-- Unfolding the Casimir operator into iterated brackets:
`C x = ⁅E, ⁅F, x⁆⁆ + ⁅F, ⁅E, x⁆⁆ + ½ ⁅H, ⁅H, x⁆⁆`. -/
theorem casimir_apply (x : M) :
    casimir M x = ⁅sl2_e, ⁅sl2_f, x⁆⁆ + ⁅sl2_f, ⁅sl2_e, x⁆⁆
      + (2⁻¹ : ℂ) • ⁅sl2_h, ⁅sl2_h, x⁆⁆ := by
  simp only [casimir, LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LieModule.toEnd_apply_apply]

/-- **Casimir scalar on a highest-weight vector (the (g)/(h) input).** If `x` is killed
by the raising operator `E` and is an `H`-eigenvector of weight `μ`, then the Casimir
operator acts on `x` by the scalar `μ(μ+2)/2`.

This is the general-`sl(2)`-module form of `casimir_eq_scalar_lambda` (which is the
special case `M = V_λ`, `μ = λ`) and of `casimir_cgHW`. -/
theorem casimir_highest_weight (μ : ℂ) (x : M) (hE : ⁅sl2_e, x⁆ = 0)
    (hH : ⁅sl2_h, x⁆ = μ • x) :
    casimir M x = ((μ * (μ + 2)) / 2) • x := by
  -- `EF·x = ⁅⁅E,F⁆, x⁆ + ⁅F, E·x⁆ = ⁅H, x⁆ = μ·x` (Leibniz, `⁅E,F⁆ = H`, `E·x = 0`).
  have hEF : ⁅sl2_e, ⁅sl2_f, x⁆⁆ = μ • x := by
    rw [leibniz_lie sl2_e sl2_f x, lie_e_f, hH, hE, lie_zero, add_zero]
  -- `FE·x = ⁅F, E·x⁆ = 0`.
  have hFE : ⁅sl2_f, ⁅sl2_e, x⁆⁆ = 0 := by rw [hE, lie_zero]
  -- `H²·x = μ²·x`.
  have hHH : ⁅sl2_h, ⁅sl2_h, x⁆⁆ = (μ * μ) • x := by rw [hH, lie_smul, hH, smul_smul]
  rw [casimir_apply, hEF, hFE, hHH, add_zero, smul_smul, ← add_smul]
  congr 1
  ring

/-- **Casimir scalar on a lowest-weight vector — the key sub-lemma of Problem 2.15.1(j).**
If `x` is killed by the lowering operator `F` and is an `H`-eigenvector of weight `μ`,
then the Casimir operator acts on `x` by the scalar `μ(μ-2)/2`.

In the book this is "if `Fx = 0` and `Hx = μx` (with `x ≠ 0`) then `Cx = μ(μ-2)/2·x`",
the identity used to pin the lowest weight of `V_λ` to `μ = -λ`. -/
theorem casimir_lowest_weight (μ : ℂ) (x : M) (hF : ⁅sl2_f, x⁆ = 0)
    (hH : ⁅sl2_h, x⁆ = μ • x) :
    casimir M x = ((μ * (μ - 2)) / 2) • x := by
  -- `EF·x = ⁅E, F·x⁆ = 0`.
  have hEF : ⁅sl2_e, ⁅sl2_f, x⁆⁆ = 0 := by rw [hF, lie_zero]
  -- `FE·x = -μ·x`: from Leibniz, `0 = EF·x = ⁅H, x⁆ + FE·x = μ·x + FE·x`.
  have hFE : ⁅sl2_f, ⁅sl2_e, x⁆⁆ = -(μ • x) := by
    have h := leibniz_lie sl2_e sl2_f x
    rw [lie_e_f, hH, hEF] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  -- `H²·x = μ²·x`.
  have hHH : ⁅sl2_h, ⁅sl2_h, x⁆⁆ = (μ * μ) • x := by rw [hH, lie_smul, hH, smul_smul]
  rw [casimir_apply, hEF, hFE, hHH, zero_add, smul_smul, ← neg_smul, ← add_smul]
  congr 1
  ring

end Casimir

section Central

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule sl2 M] [LieModule ℂ sl2 M]

-- Re-enable the Lie ring structure on the associative ring `Module.End ℂ M` so that
-- `LieHom.map_lie` (bracket preservation of `LieModule.toEnd`) and the commutator
-- bracket `⁅a, b⁆ = a * b - b * a` are available. Local to this section.
attribute [local instance 100] LieRing.ofAssociativeRing

omit [LieRingModule sl2 M] [LieModule ℂ sl2 M] in
/-- The commutator bracket on `Module.End ℂ M` is a derivation of the associative
product: `⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆`. -/
private theorem lie_mul' (a b c : Module.End ℂ M) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * c + b * ⁅a, c⁆ := by
  simp only [Ring.lie_def]; noncomm_ring

/-- `C` commutes with `E` (`= ⁅sl2_e, ·⁆`): `⁅E, C⁆ = 0`. The Casimir's commutator
with the raising operator vanishes via `⁅E,E⁆ = 0`, `⁅E,F⁆ = H`, `⁅E,H⁆ = -2E`. -/
private theorem lie_e_casimir : ⁅LieModule.toEnd ℂ sl2 M sl2_e, casimir M⁆ = 0 := by
  rw [casimir]
  set E := LieModule.toEnd ℂ sl2 M sl2_e with hE
  set F := LieModule.toEnd ℂ sl2 M sl2_f with hF
  set H := LieModule.toEnd ℂ sl2 M sl2_h with hH
  have bEF : ⁅E, F⁆ = H := by rw [hE, hF, hH, ← LieHom.map_lie, lie_e_f]
  have bHE : ⁅H, E⁆ = 2 • E := by rw [hH, hE, ← LieHom.map_lie, lie_h_e, map_nsmul]
  have bEH : ⁅E, H⁆ = -(2 • E) := by rw [(lie_skew E H).symm, bHE]
  rw [lie_add, lie_add, lie_mul', lie_mul', lie_smul, lie_mul']
  simp only [lie_self, bEF, bEH, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  module

/-- `C` commutes with `F` (`= ⁅sl2_f, ·⁆`): `⁅F, C⁆ = 0`, via `⁅F,E⁆ = -H`,
`⁅F,H⁆ = 2F`, `⁅F,F⁆ = 0`. -/
private theorem lie_f_casimir : ⁅LieModule.toEnd ℂ sl2 M sl2_f, casimir M⁆ = 0 := by
  rw [casimir]
  set E := LieModule.toEnd ℂ sl2 M sl2_e with hE
  set F := LieModule.toEnd ℂ sl2 M sl2_f with hF
  set H := LieModule.toEnd ℂ sl2 M sl2_h with hH
  have bFE : ⁅F, E⁆ = -H := by
    rw [(lie_skew F E).symm, hF, hE, hH, ← LieHom.map_lie, lie_e_f]
  have bHF : ⁅H, F⁆ = -(2 • F) := by
    rw [hH, hF, ← LieHom.map_lie, lie_h_f, map_neg, map_nsmul]
  have bFH : ⁅F, H⁆ = 2 • F := by rw [(lie_skew F H).symm, bHF, neg_neg]
  rw [lie_add, lie_add, lie_mul', lie_mul', lie_smul, lie_mul']
  simp only [lie_self, bFE, bFH, zero_mul, mul_zero, add_zero, zero_add,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  module

/-- `C` commutes with `H` (`= ⁅sl2_h, ·⁆`): `⁅H, C⁆ = 0`, via `⁅H,E⁆ = 2E`,
`⁅H,F⁆ = -2F`, `⁅H,H⁆ = 0`. -/
private theorem lie_h_casimir : ⁅LieModule.toEnd ℂ sl2 M sl2_h, casimir M⁆ = 0 := by
  rw [casimir]
  set E := LieModule.toEnd ℂ sl2 M sl2_e with hE
  set F := LieModule.toEnd ℂ sl2 M sl2_f with hF
  set H := LieModule.toEnd ℂ sl2 M sl2_h with hH
  have bHE : ⁅H, E⁆ = 2 • E := by rw [hH, hE, ← LieHom.map_lie, lie_h_e, map_nsmul]
  have bHF : ⁅H, F⁆ = -(2 • F) := by
    rw [hH, hF, ← LieHom.map_lie, lie_h_f, map_neg, map_nsmul]
  rw [lie_add, lie_add, lie_mul', lie_mul', lie_smul, lie_mul']
  simp only [lie_self, bHE, bHF, zero_mul, mul_zero, add_zero,
    neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
  module

/-- Every element of `sl(2)` is the `ℂ`-combination `X = X₀₁·e + X₁₀·f + X₀₀·h` of the
standard triple, read off from its matrix entries (the `(1,1)` entry is `-X₀₀` by
tracelessness). -/
theorem sl2_decomp (x : sl2) :
    x = (x.val 0 1) • sl2_e + (x.val 1 0) • sl2_f + (x.val 0 0) • sl2_h := by
  apply Subtype.ext
  push_cast
  simp only [sl2_e, sl2_f, sl2_h,
    LieAlgebra.SpecialLinear.val_single, LieAlgebra.SpecialLinear.val_singleSubSingle]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.single, sl2_traceless x]

/-- The Casimir commutes with the action of every `x ∈ sl(2)`: `⁅toEnd x, C⁆ = 0`.
By `ℂ`-bilinearity of the bracket this reduces to the three generators `e, f, h`. -/
theorem casimir_lie_toEnd (x : sl2) :
    ⁅LieModule.toEnd ℂ sl2 M x, casimir M⁆ = 0 := by
  rw [sl2_decomp x, map_add, map_add, map_smul, map_smul, map_smul,
    add_lie, add_lie, smul_lie, smul_lie, smul_lie,
    lie_e_casimir, lie_f_casimir, lie_h_casimir, smul_zero, smul_zero, smul_zero,
    add_zero, add_zero]

/-- **The Casimir operator is central (Problem 2.15.1(g)).** On any `sl(2)`-module `M`,
`C = casimir M` commutes with the `sl(2)`-action: `⁅x, C m⁆ = C ⁅x, m⁆` for all
`x ∈ sl(2)` and `m ∈ M`. This is the book's "`C` commutes with `E`, `F`, `H`" at the
general-module level, and is the prerequisite for part (h): the generalized eigenspaces
of the central operator `C` are sub-`sl(2)`-modules. -/
theorem casimir_central (x : sl2) (m : M) :
    ⁅x, casimir M m⁆ = casimir M ⁅x, m⁆ := by
  have hcomm : LieModule.toEnd ℂ sl2 M x * casimir M
      = casimir M * LieModule.toEnd ℂ sl2 M x := by
    have h := casimir_lie_toEnd (M := M) x
    rwa [Ring.lie_def, sub_eq_zero] at h
  calc ⁅x, casimir M m⁆
      = LieModule.toEnd ℂ sl2 M x (casimir M m) := (LieModule.toEnd_apply_apply ..).symm
    _ = (LieModule.toEnd ℂ sl2 M x * casimir M) m := (Module.End.mul_apply ..).symm
    _ = (casimir M * LieModule.toEnd ℂ sl2 M x) m := by rw [hcomm]
    _ = casimir M (LieModule.toEnd ℂ sl2 M x m) := Module.End.mul_apply ..
    _ = casimir M ⁅x, m⁆ := by rw [LieModule.toEnd_apply_apply]

end Central

/-! ## The complete-reducibility conclusion

The statement of complete reducibility, recorded in its cleanest equivalent form for a
finite-dimensional module: every `sl(2)`-submodule has an `sl(2)`-complement (this is
the meaning of "semisimple"; for finite-dimensional modules it is equivalent to being a
direct sum of irreducibles, hence of `V_λ`'s by the classification (f)). The proof, by
the book's Casimir argument (h)–(k), is left as `sorry` and tracked as follow-up. -/

section CompleteReducibility

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
  [LieRingModule sl2 M] [LieModule ℂ sl2 M]

/-- **Complete reducibility of finite-dimensional `sl(2)`-representations
(Problem 2.15.1(h)–(k)).** Every `sl(2)`-submodule `N` of a finite-dimensional
`sl(2)`-module `M` has an `sl(2)`-complement `N'` (`IsCompl N N'`). Equivalently, `M`
is a direct sum of irreducible subrepresentations, each isomorphic to some `V_λ`.

The intended proof is the book's elementary Casimir argument: reduce to showing an
indecomposable finite-dimensional `sl(2)`-module is irreducible, using that the
generalized eigenspaces of the central Casimir operator `casimir M` are
subrepresentations (parts (h)–(k)), with `casimir_highest_weight` /
`casimir_lowest_weight` as the eigenvalue inputs. -/
theorem complete_reducibility (N : LieSubmodule ℂ sl2 M) :
    ∃ N' : LieSubmodule ℂ sl2 M, IsCompl N N' := by
  sorry

end CompleteReducibility

end Etingof.Sl2Irrep
