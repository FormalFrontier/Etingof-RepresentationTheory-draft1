import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Syzygies of a projective resolution

For a projective resolution `P : CategoryTheory.ProjectiveResolution M` of an object `M`
in an abelian category, this file constructs the *syzygy objects* `Ωⁿ M` together with the
*syzygy short exact sequences*

`0 ⟶ Ωⁿ⁺¹ M ⟶ Pₙ ⟶ Ωⁿ M ⟶ 0`

with projective middle term `Pₙ = P.complex.X n`. Here `Ω⁰ M = M` (via the augmentation
`P.π`), `Ω¹ M = ker(P₀ → M)`, and in general `Ωⁿ⁺¹ M = ker(Pₙ → Ωⁿ M)`.

Mathlib bundles projective resolutions (`CategoryTheory.ProjectiveResolution`) but provides no
syzygy API. This file is the foundation used to iterate dimension shifting along an arbitrary
projective resolution (Etingof, Problem 9.4.2(iii)).

## Main declarations

* `Etingof.ProjectiveResolution.syzygy P n` — the `n`-th syzygy object `Ωⁿ M`.
* `Etingof.ProjectiveResolution.syzygySES P n` — the short complex
  `0 ⟶ Ωⁿ⁺¹ M ⟶ Pₙ ⟶ Ωⁿ M ⟶ 0`.
* `Etingof.ProjectiveResolution.syzygySES_shortExact P n` — it is short exact.
* `Etingof.ProjectiveResolution.syzygy_zero`, `syzygySES_X₁`, `syzygySES_X₂`, `syzygySES_X₃` —
  the endpoints, notably `Ω⁰ M = M`, `(syzygySES P n).X₁ = Ωⁿ⁺¹ M`, `.X₃ = Ωⁿ M`, and
  `.X₂ = Pₙ` (projective).

## Indexing note

In `ChainComplex C ℕ` (`ComplexShape.down ℕ`) the differential out of `X i` is
`d i (i-1)`, and `d 0 j = 0`, so `cycles 0 = X 0`. The bottom syzygy `Ω⁰ M = M` therefore
comes from the augmentation `P.π`, not from `cycles`; the recursion below folds the
augmentation into its base case so that all degrees are treated uniformly.
-/

universe v u

open CategoryTheory Limits

namespace Etingof.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {M : C} (P : ProjectiveResolution M)

/-- The data attached to degree `n` of a projective resolution `P` of `M`: the `n`-th syzygy
object `obj = Ωⁿ M` together with the epimorphism `p : Pₙ ↠ Ωⁿ M` whose kernel is the next
syzygy. The `exact` field records that `Pₙ₊₁ ⟶ Pₙ ⟶ Ωⁿ M` is exact at `Pₙ` — this is what
makes the corestriction of `Pₙ₊₁ ⟶ Pₙ` onto `ker p = Ωⁿ⁺¹ M` an epimorphism, feeding the
recursion. -/
structure SyzygyStep (n : ℕ) where
  /-- the `n`-th syzygy object `Ωⁿ M` -/
  obj : C
  /-- the epimorphism `Pₙ ↠ Ωⁿ M` -/
  p : P.complex.X n ⟶ obj
  /-- the differential into `Pₙ` composes to zero with `p` -/
  w : P.complex.d (n + 1) n ≫ p = 0
  /-- `p` is an epimorphism -/
  epi_p : Epi p
  /-- `Pₙ₊₁ ⟶ Pₙ ⟶ Ωⁿ M` is exact at `Pₙ` -/
  exact : (ShortComplex.mk (P.complex.d (n + 1) n) p w).Exact

namespace SyzygyStep

variable {P}

/-- The inductive step: from the datum at degree `n` produce the datum at degree `n + 1`.
The new syzygy object is `ker p`, and the new epimorphism is the corestriction of the
differential `Pₙ₊₁ ⟶ Pₙ` through `ker p`, which is epi precisely by the exactness recorded in
the previous step. -/
noncomputable def succ {n : ℕ} (s : SyzygyStep P n) : SyzygyStep P (n + 1) where
  obj := kernel s.p
  p := kernel.lift s.p (P.complex.d (n + 1) n) s.w
  w := by
    rw [← cancel_mono (kernel.ι s.p), zero_comp, Category.assoc, kernel.lift_ι]
    exact P.complex.d_comp_d _ _ _
  epi_p := s.exact.epi_kernelLift
  exact := by
    -- Map the sequence `Pₙ₊₂ ⟶ Pₙ₊₁ ⟶ ker(Pₙ ↠ Ωⁿ M)` to the resolution's own exact
    -- sequence `Pₙ₊₂ ⟶ Pₙ₊₁ ⟶ Pₙ` via identities on the first two terms and `ker.ι` on the
    -- third; exactness transfers along a map with epi/iso/mono components.
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (P.complex.d (n + 1 + 1) (n + 1))
        (kernel.lift s.p (P.complex.d (n + 1) n) s.w)
        (by rw [← cancel_mono (kernel.ι s.p), zero_comp, Category.assoc, kernel.lift_ι]
            exact P.complex.d_comp_d _ _ _))
      (S₂ := ShortComplex.mk (P.complex.d (n + 1 + 1) (n + 1)) (P.complex.d (n + 1) n)
        (P.complex.d_comp_d _ _ _))
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι s.p
        comm₂₃ := by simp }).mpr (P.exact_succ n)

end SyzygyStep

/-- The syzygy datum at each degree of the projective resolution `P`, defined by recursion.
The base case uses the augmentation `P.π` so that `Ω⁰ M = M`. -/
noncomputable def syzygyStep : ∀ n, SyzygyStep P n
  | 0 =>
    { obj := M
      p := P.π.f 0
      w := P.complex_d_comp_π_f_zero
      epi_p := inferInstance
      exact := ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork }
  | n + 1 => (syzygyStep n).succ

/-- The `n`-th syzygy `Ωⁿ M` of the projective resolution `P`. By convention `Ω⁰ M = M`, and
`Ωⁿ⁺¹ M = ker(Pₙ ↠ Ωⁿ M)`. -/
noncomputable def syzygy (n : ℕ) : C := (syzygyStep P n).obj

@[simp] lemma syzygy_zero : syzygy P 0 = M := rfl

/-- The syzygy short exact sequence `0 ⟶ Ωⁿ⁺¹ M ⟶ Pₙ ⟶ Ωⁿ M ⟶ 0`. -/
noncomputable def syzygySES (n : ℕ) : ShortComplex C :=
  ShortComplex.kernelSequence (syzygyStep P n).p

@[simp] lemma syzygySES_X₂ (n : ℕ) : (syzygySES P n).X₂ = P.complex.X n := rfl

@[simp] lemma syzygySES_X₃ (n : ℕ) : (syzygySES P n).X₃ = syzygy P n := rfl

@[simp] lemma syzygySES_X₁ (n : ℕ) : (syzygySES P n).X₁ = syzygy P (n + 1) := rfl

/-- The middle term of the syzygy short exact sequence is projective. -/
instance (n : ℕ) : Projective (syzygySES P n).X₂ := by
  rw [syzygySES_X₂]; exact P.projective n

/-- **Syzygy short exact sequence.** For every `n`, the sequence
`0 ⟶ Ωⁿ⁺¹ M ⟶ Pₙ ⟶ Ωⁿ M ⟶ 0` is short exact, with projective middle term. -/
lemma syzygySES_shortExact (n : ℕ) : (syzygySES P n).ShortExact := by
  haveI hp : Epi (syzygyStep P n).p := (syzygyStep P n).epi_p
  change (ShortComplex.kernelSequence (syzygyStep P n).p).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) ?_ hp
  exact (inferInstance : Mono (kernel.ι (syzygyStep P n).p))

end Etingof.ProjectiveResolution
