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
is stated here in the convenient block-conjugation form

```
f = e.hom ≫ biprod.map fK fI ≫ e.inv,   IsNilpotent fK,   IsIso fI,
```

and is **proved** from the single finite-length input `Etingof.exists_pow_stabilizes`: at the
stabilising power `n` the image restriction `g' := image.ι (fⁿ) ≫ factorThruImage (fⁿ)` is an
isomorphism. Given that iso the whole construction is elementary abelian-category algebra:
`factorThruImage (fⁿ)` becomes a split epi (section `(g')⁻¹ ≫ image.ι (fⁿ)`), its kernel and image
split `X` as a biproduct, `f` is block-diagonal because it preserves both summands (the kernel
summand directly, the image summand because `f` maps `im (fⁿ)` into `im (fⁿ⁺¹) ⊆ im (fⁿ)`), and the
two blocks are read off from `(fK)ⁿ = (fⁿ)|_K = 0` and `(fI)ⁿ = (fⁿ)|_I = g'`. The only `sorry`
upstream is in the `clength_*` finiteness lemmas that `exists_pow_stabilizes` rests on.
**Everything downstream of `fitting_decomposition` in this file — the nilpotent-or-iso dichotomy and
the local-ring property — is proved unconditionally from its statement.**

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

`K` is the kernel `ker (factorThruImage (fⁿ)) = ker (fⁿ)` and `I` the eventual image `im (fⁿ)` for
the stabilising power `n` supplied by `Etingof.exists_pow_stabilizes` (the finite-length content of
`KrullSchmidt/Length.lean`, which rests on the still-`sorry`-d `clength_*` lemmas); see the module
doc for the proof outline. The downstream dichotomy and local-ring results below are proved
unconditionally from this statement. -/
theorem fitting_decomposition {X : C} (f : End X) :
    ∃ (K I : C) (e : X ≅ K ⊞ I) (fK : End K) (fI : End I),
      IsNilpotent fK ∧ IsIso (fI : I ⟶ I) ∧
        (f : X ⟶ X) = e.hom ≫ biprod.map (fK : K ⟶ K) (fI : I ⟶ I) ≫ e.inv := by
  -- Step 1: stabilising power `n` and the iso `g' := i ≫ p` on the eventual image.
  obtain ⟨n, hn, hiso⟩ := exists_pow_stabilizes f
  set g : X ⟶ X := (f : X ⟶ X) ^ n with hg
  set I : C := Abelian.image g with hI
  set i : I ⟶ X := Abelian.image.ι g with hi
  set p : X ⟶ I := Abelian.factorThruImage g with hp
  have hpi : p ≫ i = g := by rw [hp, hi]; exact Abelian.image.fac g
  haveI hmono_i : Mono i := by rw [hi]; infer_instance
  haveI : IsIso (i ≫ p) := hiso
  -- `g` commutes with `f`, and the kernel inclusion of `p` kills `g`.
  have hcomm : (f : X ⟶ X) ≫ g = g ≫ (f : X ⟶ X) := by
    have h1 : (f : X ⟶ X) ≫ g = (f : X ⟶ X) ^ (n + 1) := by rw [hg, pow_succ]; rfl
    have h2 : g ≫ (f : X ⟶ X) = (f : X ⟶ X) ^ (n + 1) := by rw [hg, pow_succ']; rfl
    rw [h1, h2]
  have hKg : kernel.ι p ≫ g = 0 := by
    rw [← hpi, ← Category.assoc, kernel.condition, zero_comp]
  -- Step 2: split the epi `p` with the explicit section `s := (g')⁻¹ ≫ i`.
  set s : I ⟶ X := inv (i ≫ p) ≫ i with hs
  have hsp : s ≫ p = 𝟙 I := by rw [hs, Category.assoc, IsIso.inv_hom_id]
  -- The `K`-projector idempotent `eK := 𝟙 - p ≫ s` and the kernel object `K := ker p`.
  set eK : X ⟶ X := 𝟙 X - p ≫ s with heK
  have heKp : eK ≫ p = 0 := by
    rw [heK, Preadditive.sub_comp, Category.id_comp, Category.assoc, hsp, Category.comp_id,
      sub_self]
  have hieK : i ≫ eK = 0 := by
    rw [heK, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hs, ← Category.assoc,
      IsIso.hom_inv_id, Category.id_comp, sub_self]
  set K : C := kernel p with hK
  set fstB : X ⟶ K := kernel.lift p eK heKp with hfstB
  have hfst_ι : fstB ≫ kernel.ι p = eK := kernel.lift_ι p eK heKp
  -- Step 3: assemble the bilimit binary bicone with point `X`.
  have hbinl_fst : kernel.ι p ≫ fstB = 𝟙 K := by
    rw [← cancel_mono (kernel.ι p), Category.assoc, hfst_ι, Category.id_comp, heK,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, kernel.condition, zero_comp,
      sub_zero]
  have hbinr_fst : s ≫ fstB = 0 := by
    rw [← cancel_mono (kernel.ι p), Category.assoc, hfst_ι, zero_comp, heK, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, hsp, Category.id_comp, sub_self]
  set b : BinaryBicone K I :=
    { pt := X
      fst := fstB
      snd := p
      inl := kernel.ι p
      inr := s
      inl_fst := hbinl_fst
      inl_snd := kernel.condition p
      inr_fst := hbinr_fst
      inr_snd := hsp } with hb
  have htotal : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt := by
    change fstB ≫ kernel.ι p + p ≫ s = 𝟙 X
    rw [hfst_ι, heK, sub_add_cancel]
  have hbil : b.IsBilimit := isBinaryBilimitOfTotal b htotal
  set e : X ≅ K ⊞ I := biprod.uniqueUpToIso K I hbil with he
  have ehom : e.hom = biprod.lift fstB p := biprod.uniqueUpToIso_hom K I hbil
  have einv : e.inv = biprod.desc (kernel.ι p) s := biprod.uniqueUpToIso_inv K I hbil
  -- Step 4: the block restrictions and block-diagonality of `f`.
  set fK : End K := kernel.ι p ≫ (f : X ⟶ X) ≫ fstB with hfK
  set fI : End I := s ≫ (f : X ⟶ X) ≫ p with hfI
  -- Off-diagonal A: `f` preserves `K = ker p`.
  have hA : kernel.ι p ≫ (f : X ⟶ X) ≫ p = 0 := by
    rw [← cancel_mono i, zero_comp, Category.assoc, Category.assoc, hpi, hcomm, ← Category.assoc,
      hKg, zero_comp]
  -- `f` preserves the image: `i ≫ f` factors through `i`.
  have hif : (inv (i ≫ p) ≫ i ≫ (f : X ⟶ X) ≫ p) ≫ i = i ≫ (f : X ⟶ X) := by
    calc (inv (i ≫ p) ≫ i ≫ (f : X ⟶ X) ≫ p) ≫ i
        = inv (i ≫ p) ≫ i ≫ (f : X ⟶ X) ≫ (p ≫ i) := by simp only [Category.assoc]
      _ = inv (i ≫ p) ≫ i ≫ ((f : X ⟶ X) ≫ g) := by rw [hpi]
      _ = inv (i ≫ p) ≫ i ≫ (g ≫ (f : X ⟶ X)) := by rw [hcomm]
      _ = inv (i ≫ p) ≫ (i ≫ p) ≫ i ≫ (f : X ⟶ X) := by rw [← hpi]; simp only [Category.assoc]
      _ = i ≫ (f : X ⟶ X) := by rw [IsIso.inv_hom_id_assoc]
  -- `i ≫ f ≫ eK = 0`: the image summand is killed by the `K`-projector.
  have hifeK : i ≫ (f : X ⟶ X) ≫ eK = 0 := by
    rw [← Category.assoc, ← hif, Category.assoc, hieK, comp_zero]
  -- Off-diagonal B: `f` preserves `I = im g`.
  have hB : s ≫ (f : X ⟶ X) ≫ fstB = 0 := by
    rw [hs, ← cancel_mono (kernel.ι p), zero_comp]
    simp only [Category.assoc]
    rw [hfst_ι, hifeK, comp_zero]
  -- Block-diagonality: `e.inv ≫ f ≫ e.hom = fK ⊞ fI`.
  have hmap : e.inv ≫ (f : X ⟶ X) ≫ e.hom = biprod.map (fK : K ⟶ K) (fI : I ⟶ I) := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [einv, ehom, Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.lift_fst, biprod.lift_snd, biprod.inl_map_assoc, biprod.inr_map_assoc,
        biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, Category.comp_id,
        comp_zero, hfK, hfI, hA, hB]
  refine ⟨K, I, e, fK, fI, ?_, ?_, ?_⟩
  · -- Step 5a: `fK` is nilpotent — `fK ^ n = 0`.
    refine ⟨n, ?_⟩
    have hM : (e.conj f : K ⊞ I ⟶ K ⊞ I) = biprod.map (fK : K ⟶ K) (fI : I ⟶ I) := by
      rw [Iso.conj_apply]; exact hmap
    have hpow2 : biprod.map ((fK ^ n : End K) : K ⟶ K) ((fI ^ n : End I) : I ⟶ I)
        = e.inv ≫ g ≫ e.hom := by
      rw [← biprodMap_pow fK fI (e.conj f) hM n, ← map_pow, Iso.conj_apply]
    have h := congrArg (fun m => biprod.inl ≫ m ≫ biprod.fst) hpow2
    simp only [einv, ehom, Category.assoc, biprod.inl_map_assoc, biprod.inl_fst,
      biprod.inl_desc_assoc, biprod.lift_fst, Category.comp_id] at h
    rw [← Category.assoc, hKg, zero_comp] at h
    exact h
  · -- Step 5b: `fI` is an iso — `fI ^ n = i ≫ p` is an iso.
    have hM : (e.conj f : K ⊞ I ⟶ K ⊞ I) = biprod.map (fK : K ⟶ K) (fI : I ⟶ I) := by
      rw [Iso.conj_apply]; exact hmap
    have hpow2 : biprod.map ((fK ^ n : End K) : K ⟶ K) ((fI ^ n : End I) : I ⟶ I)
        = e.inv ≫ g ≫ e.hom := by
      rw [← biprodMap_pow fK fI (e.conj f) hM n, ← map_pow, Iso.conj_apply]
    have hsgp : s ≫ g ≫ p = i ≫ p := by
      calc s ≫ g ≫ p = (s ≫ p) ≫ (i ≫ p) := by rw [← hpi]; simp only [Category.assoc]
        _ = i ≫ p := by rw [hsp, Category.id_comp]
    have h := congrArg (fun m => biprod.inr ≫ m ≫ biprod.snd) hpow2
    simp only [einv, ehom, Category.assoc, biprod.inr_map_assoc, biprod.inr_snd,
      biprod.inr_desc_assoc, biprod.lift_snd, Category.comp_id] at h
    rw [hsgp] at h
    have hisoFn : IsIso ((fI ^ n : End I) : I ⟶ I) := by rw [h]; infer_instance
    exact (isUnit_iff_isIso fI).mp
      ((isUnit_pow_iff hn.ne').mp ((isUnit_iff_isIso (fI ^ n : End I)).mpr hisoFn))
  · -- Step 4 (packaging): conjugate the block map back to `f`.
    rw [← hmap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

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
