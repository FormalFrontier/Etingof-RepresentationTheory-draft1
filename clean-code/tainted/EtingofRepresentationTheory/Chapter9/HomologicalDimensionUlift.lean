import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Ring.ULift
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionRingEquiv

/-!
# Homological dimension is invariant under a universe lift

`Etingof.homologicalDimension R` (Definition 9.4.3) quantifies over `ModuleCat.{u} R`, where `u`
is the universe of `R`. This file proves that lifting `R` to a larger universe can only increase
the collection of modules under consideration, so it cannot lower the homological dimension:

* `Etingof.homologicalDimension_le_ulift`:
  `homologicalDimension R ≤ homologicalDimension (ULift R)`.

## Strategy

The key categorical input is that the universe-lift functor
`ModuleCat.uliftFunctor.{v, u} R : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R` is additive, exact
(preserves finite limits and colimits) and fully faithful, and, since `R : Type u` is `u`-small,
preserves projective objects. A fully faithful exact functor preserving projectives reflects
projective dimension: `HasProjectiveDimensionLT (F.obj X) n → HasProjectiveDimensionLT X n`
(`Etingof.hasProjectiveDimensionLT_of_map`). This mirrors the preservation statement
`hasProjectiveDimensionLT_map` from `HomologicalDimensionRingEquiv.lean`, but for a plain
fully-faithful functor rather than an equivalence, and in the reverse (reflecting) direction.

Combined with the same-universe ring-equivalence transfer
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv)` (which identifies
`ModuleCat.{max u v} (ULift R)` with `ModuleCat.{max u v} R`) this shows that if every big-universe
`ULift R`-module has projective dimension `≤ d`, then so does every small-universe `R`-module,
which is exactly the inequality of homological dimensions.

The reverse inequality (a universe lift cannot raise the homological dimension) is harder: it
requires reducing the projective dimension of arbitrary big modules to small ones (an
Auslander-style argument), and is not needed for the free-algebra corollary of Problem 9.4.6,
so it is not proved here.
-/

universe v u

open CategoryTheory Limits CategoryTheory.Limits

namespace Etingof

section Reflect

variable {C : Type*} {D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- A fully faithful additive exact functor `F : C ⥤ D` preserving projective objects (with `C`
having enough projectives) reflects projective dimension: if `F.obj X` has projective dimension
`< n`, then so does `X`.

Strong induction on `n`, dual to `Etingof.hasProjectiveDimensionLT_map`. The base cases are
`n = 0` (`F` is faithful, so it reflects zero objects) and `n = 1` (`F` reflects projectives,
being full, faithful and epimorphism-preserving, by `Functor.projective_of_map_projective`). For
`n + 2` one takes a projective presentation `0 → K → P → X → 0` in `C`, maps it to the short exact
sequence `0 → F K → F P → F X → 0`, shifts `F X`'s dimension down to `F K`
(`hasProjectiveDimensionLT_X₁`), applies the induction hypothesis to `K`, and shifts back up along
the original presentation (`hasProjectiveDimensionLT_X₃`). -/
theorem hasProjectiveDimensionLT_of_map (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [F.PreservesEpimorphisms] [PreservesFiniteColimits F] [PreservesFiniteLimits F]
    [F.PreservesProjectiveObjects] [EnoughProjectives C] :
    ∀ (n : ℕ) (X : C), HasProjectiveDimensionLT (F.obj X) n → HasProjectiveDimensionLT X n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    match n, IH with
    | 0, _ =>
        intro X hX
        rw [hasProjectiveDimensionLT_zero_iff_isZero] at hX ⊢
        rw [IsZero.iff_id_eq_zero] at hX ⊢
        apply F.map_injective
        rw [F.map_id, F.map_zero]
        exact hX
    | 1, _ =>
        intro X hX
        haveI : Projective (F.obj X) := projective_iff_hasProjectiveDimensionLT_one.mpr hX
        exact projective_iff_hasProjectiveDimensionLT_one.mp (F.projective_of_map_projective ‹_›)
    | (m + 2), IH =>
        intro X hX
        -- A projective presentation `0 → K → P → X → 0` in `C`.
        obtain ⟨P⟩ : Nonempty (ProjectivePresentation X) := EnoughProjectives.presentation X
        let S : ShortComplex C := ShortComplex.mk _ _ (kernel.condition P.f)
        have hSE : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
        -- Map the short exact sequence across the exact functor `F`.
        have hSEF : (S.map F).ShortExact := hSE.map_of_exact F
        -- `F P` is projective, hence has projective dimension `< 1 ≤ m + 1`.
        haveI : Projective (S.map F).X₂ := by
          change Projective (F.obj P.p); infer_instance
        have hFP1 : HasProjectiveDimensionLT (S.map F).X₂ (m + 1) :=
          hasProjectiveDimensionLT_of_ge (S.map F).X₂ 1 (m + 1) (by omega)
        -- Dimension shift down: `pd (F X) < m + 2` gives `pd (F K) < m + 1`.
        have hFK : HasProjectiveDimensionLT (S.map F).X₁ (m + 1) :=
          hSEF.hasProjectiveDimensionLT_X₁ (m + 1) hFP1 hX
        -- The induction hypothesis reflects this down to the syzygy `K`.
        have hK : HasProjectiveDimensionLT S.X₁ (m + 1) := by
          have : HasProjectiveDimensionLT (F.obj S.X₁) (m + 1) := hFK
          exact IH (m + 1) (by omega) S.X₁ this
        -- `P` is projective, hence has projective dimension `< 1 ≤ m + 2`.
        haveI hP1 : HasProjectiveDimensionLT P.p 1 :=
          projective_iff_hasProjectiveDimensionLT_one.mp P.projective
        have hP2 : HasProjectiveDimensionLT S.X₂ (m + 2) :=
          hasProjectiveDimensionLT_of_ge P.p 1 (m + 2) (by omega)
        -- Dimension shift back up along the presentation: `pd X < m + 2`.
        exact hSE.hasProjectiveDimensionLT_X₃ (m + 1) hK hP2

end Reflect

/-- **Universe-lift invariance of homological dimension (predicate form).** If every module over
the universe lift `ULift.{v} R` has projective dimension `≤ d`, then so does every module over `R`.

Transfer along the ring equivalence `ULift R ≃+* R` at the big module universe
(`restrictScalarsEquivalenceOfRingEquiv`), then reflect down to the small module universe with the
fully-faithful exact `ModuleCat.uliftFunctor` (`hasProjectiveDimensionLT_of_map`). -/
theorem hasHomologicalDimensionLE_of_ulift {R : Type u} [Ring R] {d : ℕ}
    (h : HasHomologicalDimensionLE (ULift.{v} R) d) : HasHomologicalDimensionLE R d := by
  -- `E : ModuleCat.{max u v} R ≌ ModuleCat.{max u v} (ULift R)` from the ring equivalence.
  let E : ModuleCat.{max u v} R ≌ ModuleCat.{max u v} (ULift.{v} R) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv (ULift.ringEquiv (R := R))
  -- Step 1: every big `R`-module has projective dimension `≤ d`.
  have hbig : ∀ N : ModuleCat.{max u v} R, HasProjectiveDimensionLE N d := by
    intro N
    exact (hasProjectiveDimensionLT_map_iff E (d + 1) N).mp (h (E.functor.obj N))
  -- Step 2: reflect down to the small `R`-modules through the universe-lift functor.
  intro M
  have := hbig ((ModuleCat.uliftFunctor.{v, u} R).obj M)
  exact hasProjectiveDimensionLT_of_map (ModuleCat.uliftFunctor.{v, u} R) (d + 1) M this

/-- **Universe-lift invariance of homological dimension (one direction).** The homological
dimension of `R` is at most that of its universe lift `ULift.{v} R`. A universe lift can only
enlarge the collection of modules, so it cannot lower the homological dimension. -/
theorem homologicalDimension_le_ulift {R : Type u} [Ring R] :
    homologicalDimension R ≤ homologicalDimension (ULift.{v} R) := by
  unfold homologicalDimension
  exact le_iInf₂ fun d hd => iInf₂_le d (hasHomologicalDimensionLE_of_ulift hd)

end Etingof
