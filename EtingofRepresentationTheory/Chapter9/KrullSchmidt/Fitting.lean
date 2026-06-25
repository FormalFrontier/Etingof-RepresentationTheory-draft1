import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Length
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Conj
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Fitting's lemma and local endomorphism rings (Krull–Schmidt, link 3/5)

This file is the **hard core** of the Krull–Schmidt chain for a finite abelian category `C`. It
records Fitting's lemma — the `ker`/`im` block decomposition of an endomorphism — and derives the
two facts the uniqueness half of Krull–Schmidt rests on:

* **`Etingof.isNilpotent_or_isIso_of_indecomposable`** — every endomorphism of an indecomposable
  object is nilpotent or an isomorphism;
* **`Etingof.isLocalRing_End_of_indecomposable`** — the endomorphism ring of an indecomposable
  object is local.

## Design and the Fitting crux

Mathlib has the Fitting decomposition only for Artinian **modules**
(`Mathlib/RingTheory/Artinian/Module.lean`); there is nothing for an abstract abelian category.
The categorical statement,

```
∃ n, X ≅ ker (f ^ n) ⊞ im (f ^ n),  with f nilpotent on the kernel and iso on the image,
```

needs the descending image chain `im (f^n)` and the ascending kernel chain `ker (f^n)` to
*stabilise*. That stabilisation is exactly the finite-length input of `KrullSchmidt/Length.lean`:
the chains are measured by `Etingof.clength`, whose finiteness/monotonicity is the (still `sorry`-d)
categorical Jordan–Hölder content of link 1/5. The Fitting decomposition `fitting_decomposition`
is therefore stated here in the convenient block-conjugation form

```
f = e.hom ≫ biprod.map fK fI ≫ e.inv,   IsNilpotent fK,   IsIso fI,
```

and its proof is deferred to that finite-length infrastructure (documented `sorry`, tracked as a
follow-up). **Everything downstream of it in this file — the nilpotent-or-iso dichotomy and the
local-ring property — is proved unconditionally from that statement**, so once the Fitting
decomposition is discharged the whole link closes with no further work.

The two reductions are elementary once the block form is in hand:

* For an indecomposable `X`, the block iso `e : X ≅ K ⊞ I` forces `IsZero K` or `IsZero I`. In the
  first case `fK` is an iso (any endomorphism of a zero object is), so both blocks are isos and `f`
  is an iso; in the second case `fI` is nilpotent (it is `0`), so both blocks are nilpotent and `f`
  is nilpotent. Conjugation by `e` (as `Iso.conj`, a multiplicative equivalence sending `0` to `0`)
  transports nilpotence and invertibility from the block map back to `f`.
* The local-ring property uses the characterisation `∀ a, IsUnit a ∨ IsUnit (1 - a)`
  (`IsLocalRing.of_isUnit_or_isUnit_one_sub_self`): an iso `a` is a unit, and a nilpotent `a` makes
  `1 - a` a unit (`IsNilpotent.isUnit_one_sub`). The ring `End X` is nontrivial because `X` is
  nonzero (`𝟙 X ≠ 0`).
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

-- An abelian category has finite biproducts; Mathlib keeps this as a local instance only
-- (a global instance breaks unrelated `ModuleCat` files), so we re-activate it here.
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [IsFiniteAbelianCategory C]

section BiprodMap

variable {K I : C}

/-- Horizontal composition of two block-diagonal maps is block-diagonal. -/
private theorem biprodMap_comp (a c : K ⟶ K) (b d : I ⟶ I) :
    biprod.map a b ≫ biprod.map c d = biprod.map (a ≫ c) (b ≫ d) := by
  ext <;> simp

/-- Powers of a block-diagonal endomorphism are block-diagonal: `(fK ⊞ fI)^n = fK^n ⊞ fI^n`.
`M` is carried as an explicit `End (K ⊞ I)` so that the monoid power resolves through `End`. -/
private theorem biprodMap_pow (a : End K) (b : End I) (M : End (K ⊞ I))
    (hM : (M : K ⊞ I ⟶ K ⊞ I) = biprod.map (a : K ⟶ K) (b : I ⟶ I)) (n : ℕ) :
    (M ^ n : K ⊞ I ⟶ K ⊞ I)
      = biprod.map ((a ^ n : End K) : K ⟶ K) ((b ^ n : End I) : I ⟶ I) := by
  induction n with
  | zero => simp only [pow_zero, End.one_def]; apply biprod.hom_ext' <;> simp
  | succ n ih =>
    rw [pow_succ, End.mul_def, ih, hM, biprodMap_comp]
    congr 1

/-- A block-diagonal endomorphism with both blocks nilpotent is nilpotent. -/
private theorem biprodMap_isNilpotent (a : End K) (b : End I) (M : End (K ⊞ I))
    (hM : (M : K ⊞ I ⟶ K ⊞ I) = biprod.map (a : K ⟶ K) (b : I ⟶ I))
    (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent M := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  refine ⟨p + q, ?_⟩
  have hpow := biprodMap_pow a b M hM (p + q)
  rw [pow_eq_zero_of_le (Nat.le_add_right p q) hp,
    pow_eq_zero_of_le (Nat.le_add_left q p) hq] at hpow
  have hz : biprod.map (0 : K ⟶ K) (0 : I ⟶ I) = (0 : K ⊞ I ⟶ K ⊞ I) := by ext <;> simp
  rw [hz] at hpow
  exact hpow

end BiprodMap

/-- Conjugation by an isomorphism preserves nilpotence of endomorphisms. `Iso.conj` is a
multiplicative equivalence that additionally sends the zero morphism to the zero morphism, so it
carries `f ^ n = 0` to `(e.conj f) ^ n = 0`. -/
private theorem isNilpotent_conj {X Y : C} (e : X ≅ Y) {g : End X} (h : IsNilpotent g) :
    IsNilpotent (e.conj g) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← map_pow, hn, Iso.conj_apply]
  simp

/-- **Fitting's lemma** for a finite abelian category. For an endomorphism `f` of `X` there is a
biproduct splitting `X ≅ K ⊞ I` conjugating `f` into a block-diagonal map `fK ⊞ fI` with `fK`
nilpotent and `fI` an isomorphism.

`K` is the eventual kernel `ker (f^n)` and `I` the eventual image `im (f^n)` for `n` large enough
that both chains have stabilised. Stabilisation is the finite-length content of
`KrullSchmidt/Length.lean` (the still-`sorry`-d categorical Jordan–Hölder input); see the module
doc. The downstream dichotomy and local-ring results below are proved unconditionally from this
statement. -/
theorem fitting_decomposition {X : C} (f : End X) :
    ∃ (K I : C) (e : X ≅ K ⊞ I) (fK : End K) (fI : End I),
      IsNilpotent fK ∧ IsIso (fI : I ⟶ I) ∧
        (f : X ⟶ X) = e.hom ≫ biprod.map (fK : K ⟶ K) (fI : I ⟶ I) ≫ e.inv := by
  -- Requires stabilisation of the `im (f^n)`/`ker (f^n)` chains, i.e. finiteness of `clength`
  -- in a finite abelian category (the categorical Jordan–Hölder input of link 1/5).
  sorry

/-- **Endomorphisms of an indecomposable are nilpotent or invertible.** From the Fitting
decomposition `X ≅ K ⊞ I`, indecomposability forces one of `K`, `I` to be zero: if `K` is zero both
blocks are isos and `f` is an iso; if `I` is zero both blocks are nilpotent and `f` is nilpotent. -/
theorem isNilpotent_or_isIso_of_indecomposable {X : C} (hX : CategoryTheory.Indecomposable X)
    (f : End X) : IsNilpotent f ∨ IsIso (f : X ⟶ X) := by
  obtain ⟨K, I, e, fK, fI, hNil, hIso, hf⟩ := fitting_decomposition f
  set M : End (K ⊞ I) := biprod.map (fK : K ⟶ K) (fI : I ⟶ I) with hM
  -- `f` is the conjugate of the block map `M` by `e`.
  have hfM : f = e.symm.conj M := by
    rw [Iso.conj_apply, Iso.symm_inv, Iso.symm_hom]
    exact hf
  rcases hX.2 K I e with hzK | hzI
  · -- `K` zero: `fK` is an iso, hence so is the block map and `f`.
    right
    have hKiso : IsIso (fK : K ⟶ K) := by
      rw [hzK.eq_of_src (fK : K ⟶ K) (𝟙 K)]; infer_instance
    have hMiso : IsIso (M : K ⊞ I ⟶ K ⊞ I) := by
      have hMe : (M : K ⊞ I ⟶ K ⊞ I)
          = (biprod.mapIso (asIso (fK : K ⟶ K)) (asIso (fI : I ⟶ I))).hom := by
        rw [hM]; simp
      rw [hMe]; infer_instance
    rw [hfM, ← isUnit_iff_isIso]
    exact ((isUnit_iff_isIso M).mpr hMiso).map e.symm.conj
  · -- `I` zero: `fI` is `0`, so both blocks are nilpotent, hence so are `M` and `f`.
    left
    have hInil : IsNilpotent (fI : End I) := by
      rw [show (fI : End I) = (0 : End I) from hzI.eq_of_src (fI : I ⟶ I) 0]
      exact IsNilpotent.zero
    have hMnil : IsNilpotent M := biprodMap_isNilpotent fK fI M hM hNil hInil
    rw [hfM]
    exact isNilpotent_conj e.symm hMnil

/-- **The endomorphism ring of an indecomposable object is local.** A unit is exactly an iso; by the
nilpotent-or-iso dichotomy, for every `a` either `a` is a unit (iso case) or `1 - a` is a unit
(nilpotent case), which is the local-ring criterion. -/
theorem isLocalRing_End_of_indecomposable {X : C} (hX : CategoryTheory.Indecomposable X) :
    IsLocalRing (End X) := by
  haveI : Nontrivial (End X) :=
    nontrivial_of_ne 1 0 fun h =>
      hX.1 <| (IsZero.iff_id_eq_zero X).mpr <| by rw [← End.one_def]; exact h
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  rcases isNilpotent_or_isIso_of_indecomposable hX a with hnil | hiso
  · right
    exact hnil.isUnit_one_sub
  · left
    exact (isUnit_iff_isIso a).mpr hiso

end Etingof
