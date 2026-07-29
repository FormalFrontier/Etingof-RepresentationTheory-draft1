import Mathlib
import EtingofRepresentationTheory.Chapter7.Problem7_8_7
import EtingofRepresentationTheory.Chapter7.KunnethChainComplexNat

set_option backward.isDefEq.respectTransparency false

/-!
# Künneth for `ℕ`-indexed cochain complexes via `ℕ`/`ℤ` reindexing (cochain case)

Chapter 7's Künneth formula (`Etingof.Problem7_8_7_iv`) is stated for cohomologically
indexed `CochainComplex (ModuleCat k) ℤ`. The `Ext` construction of Problem 8.2.8, however,
works with the Hom cochain complexes `Hom_A(P•, N)`, which are `ℕ`-indexed cochain complexes
`CochainComplex (ModuleCat.{u} k) ℕ` (`= HomologicalComplex _ (ComplexShape.up ℕ)`). This file
provides a Künneth isomorphism for `ℕ`-indexed cochain complexes, obtained by
reindexing the `ℤ` result rather than reproving it.

This is the exact mirror of `Etingof.kunnethChainComplexNat`
(`EtingofRepresentationTheory/Chapter7/KunnethChainComplexNat.lean`, the `down ℕ` chain case) along
the embedding `ComplexShape.embeddingUpNat : Embedding (up ℕ) (up ℤ)` (`n ↦ n`, support `ℤ≥0`)
instead of `embeddingDownNat` (`n ↦ -n`, support `ℤ≤0`). The `CoproductSupport` API
(`sigmaIsoOfInjOfIsZeroCompl`, `sigmaSupport{Hom,Inv}`) is embedding-agnostic and reused directly
from that file.

## The reindexing embedding

Mathlib's `ComplexShape.embeddingUpNat : Embedding (up ℕ) (up ℤ)` sends `n ↦ n`
(`Mathlib/Algebra/Homology/Embedding/Basic.lean`), with the needed `IsRelIff`/`IsTruncGE`
instances. `HomologicalComplex.extend embeddingUpNat` sends a `CochainComplex ℕ` to a
`CochainComplex ℤ` supported on `ℤ≥0` (the image of `n ↦ n`), zero elsewhere.

Homology transport is Mathlib's `HomologicalComplex.extendHomologyIso`:
`Hⁱ(extend C) ≅ Hⁿ(C)` at `i = n` in the image, and `extend_exactAt` gives vanishing outside the
image. These two facts are proved here as `homology_extend_iso_up` and `homology_extend_isZero_up`.

## The `up ℕ` tensor sign

Mathlib ships `TensorSigns (ComplexShape.up ℤ)` and `TensorSigns (ComplexShape.down ℕ)` but not
`TensorSigns (ComplexShape.up ℕ)`; without it `HomologicalComplex.tensorObj` does not elaborate on
`up ℕ` complexes. We supply the missing instance here (`ε n = (-1)^n`, identical data to the
`down ℕ` instance, only the `Rel` direction differs).

## Tensor ∘ extend compatibility

`extend e C ⊗ extend e D ≅ extend e (C ⊗ D)`  (in the `up ℤ` monoidal structure).

Degreewise both sides are `⨁_{p+q=n} C_p ⊗ D_q` at `+n` and zero at negative degrees; the content
is matching the `ιTensorObj` injections and the Koszul-signed total differential. The only
non-mechanical step is the sign match, here `negOnePow_natCast` (`Int.negOnePow (n : ℤ) = (-1)^n`),
simpler than the chain case (no `negOnePow_neg`). This is `nonempty_tensorObj_extend_iso` below,
constructed via `TensorExtend.tensorObjExtendIso`.

The comparison is moreover natural in `(C, D)`:
`TensorExtendUp.tensorObjExtendIso_hom_naturality` states the joint naturality square, and
`TensorExtendUp.tensorObjExtendNatIso` packages the whole comparison as an isomorphism of the
bifunctors `(C, D) ↦ extend C ⊗ extend D` and `(C, D) ↦ extend (C ⊗ D)`.

## The resulting isomorphism

`Hᵢ(C ⊗ D)` (`ℕ`) `≅ Hᵢ(extend (C ⊗ D))` `≅ Hᵢ(extend C ⊗ extend D)` (compatibility)
`≅ ⨁_{a+b=i} H_a(extend C) ⊗ H_b(extend D)` (Chapter 7 Künneth at universe `u`, degree `i`)
`≅ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)` (reindex `a = p`, `b = q`; the `a < 0` / `b < 0` summands are zero by
`homology_extend_isZero_up`).

The objectwise deliverable is `kunnethCochainComplexNatIso`; `kunnethCochainComplexNat` is its
`Nonempty` compatibility corollary. `KunnethNatBifunctor.lean` packages these same components as
the natural isomorphism `kunnethCochainComplexNatNatIso`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- The `TensorSigns` structure on `ComplexShape.up ℕ`, missing from Mathlib (which ships only
`down ℕ` and `up ℤ`). The vertical sign is `ε n = (-1)^n`, the same data as the `down ℕ` instance;
only the `Rel` direction (`n + 1 = m` vs `m + 1 = n`) differs. -/
instance : (ComplexShape.up ℕ).TensorSigns where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by simp only [ComplexShape.up_Rel]; omega
  add_rel p q r (hpq : p + 1 = q) := by simp only [ComplexShape.up_Rel]; omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -(-1 : ℤˣ) ^ p
    rw [pow_add, pow_one, mul_neg, mul_one]

@[simp]
lemma ε_up_ℕ (n : ℕ) : (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

/-- Homology of `extend e C` at the embedded degree `n` recovers `Hⁿ(C)`. Direct instance of
Mathlib's `extendHomologyIso` for `embeddingUpNat` (`e.f n = n`). -/
noncomputable def homology_extend_iso_up (C : CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (C.extend ComplexShape.embeddingUpNat).homology (n : ℤ) ≅ C.homology n :=
  C.extendHomologyIso ComplexShape.embeddingUpNat (by simp)

/-- **`homology_extend_iso_up` is natural in the complex.** For `φ : C ⟶ D` the comparison
squares of `Hⁿ(extend -) ≅ Hⁿ(-)` commute; Mathlib's `extendHomologyIso_hom_naturality` at
`e = embeddingUpNat`. This supplies the naturality of steps 1 and 4 of
`kunnethCochainComplexNatIso` (see that definition's docstring). -/
@[reassoc]
lemma homology_extend_iso_up_hom_naturality {C D : CochainComplex (ModuleCat.{u} k) ℕ} (φ : C ⟶ D)
    (n : ℕ) :
    homologyMap (extendMap φ ComplexShape.embeddingUpNat) (n : ℤ) ≫
        (homology_extend_iso_up D n).hom =
      (homology_extend_iso_up C n).hom ≫ homologyMap φ n :=
  HomologicalComplex.extendHomologyIso_hom_naturality (φ := φ)
    (e := ComplexShape.embeddingUpNat) (hj' := by simp)

/-- Homology of `extend e C` vanishes at negative degrees `j' < 0`, which lie outside the image
`{n : n : ℕ} = ℤ≥0` of `embeddingUpNat`. -/
theorem homology_extend_isZero_up (C : CochainComplex (ModuleCat.{u} k) ℕ) (j' : ℤ) (hj' : j' < 0) :
    IsZero ((C.extend ComplexShape.embeddingUpNat).homology j') := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine HomologicalComplex.extend_exactAt _ _ j' (fun j => ?_)
  simp only [ComplexShape.embeddingUpNat_f]
  omega

namespace TensorExtendUp

/-!
## Milestone (a): the degreewise object isomorphism

This section constructs, for every `j' : ℤ`, the degreewise isomorphism
`(extend C ⊗ extend D).X j' ≅ (extend (C ⊗ D)).X j'` (`tensorExtendXIso`). The nonzero degrees are
`j' = n`, where both sides identify with `⨁_{p+q=n} C_p ⊗ D_q`; negative degrees are zero on both
sides. Mirror of `KunnethChainComplexNat.TensorExtend`, degrees `+n` in place of `-n`.
-/

/-- The reindexing embedding `n ↦ n`. -/
noncomputable abbrev e : ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpNat

/-- If the left factor is zero, the tensor is zero. -/
lemma isZero_tensorObj_left {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {X Y : C} (hX : IsZero X) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, hX.eq_of_src (𝟙 X) 0]
  simp

/-- If the right factor is zero, the tensor is zero. -/
lemma isZero_tensorObj_right {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] {X Y : C} (hY : IsZero Y) : IsZero (X ⊗ Y) := by
  rw [IsZero.iff_id_eq_zero, ← MonoidalCategory.id_tensorHom_id, hY.eq_of_src (𝟙 Y) 0]
  simp

variable (C D : CochainComplex (ModuleCat.{u} k) ℕ)

/-- Summand inclusion into `(tensorObj C D).X n`, spelled as `ιMapBifunctor`. -/
noncomputable abbrev ιN (p q n : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    ((curriedTensor (ModuleCat.{u} k)).obj (C.X p)).obj (D.X q) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.ιMapBifunctor C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ)
    p q n h

/-- Summand inclusion into `(tensorObj (extend C) (extend D)).X j`, spelled as `ιMapBifunctor`. -/
noncomputable abbrev ιZ (a b j : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = j) :
    ((curriedTensor (ModuleCat.{u} k)).obj ((C.extend e).X a)).obj ((D.extend e).X b) ⟶
      (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X j :=
  HomologicalComplex.ιMapBifunctor (C.extend e) (D.extend e) (curriedTensor (ModuleCat.{u} k))
    (ComplexShape.up ℤ) a b j h

/-- Forward per-summand map for the degree `n` iso. -/
noncomputable def phiFwd (n : ℕ) (a b : ℤ) (h : a + b = (n : ℤ)) :
    (C.extend e).X a ⊗ (D.extend e).X b ⟶ (HomologicalComplex.tensorObj C D).X n :=
  match ha : e.r a, hb : e.r b with
  | some p, some q =>
      ((C.extendXIso e (e.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso e (e.f_eq_of_r_eq_some hb)).hom) ≫
        ιN C D p q n (by
          have hp := e.f_eq_of_r_eq_some ha
          have hq := e.f_eq_of_r_eq_some hb
          simp only [ComplexShape.embeddingUpNat_f] at hp hq
          have : p + q = n := by omega
          simpa using this)
  | _, _ => 0

/-- Reduction of `phiFwd` on the nonzero (some/some) summands. -/
lemma phiFwd_some (n : ℕ) {a b : ℤ} (h : a + b = (n : ℤ)) {p q : ℕ}
    (ha : e.r a = some p) (hb : e.r b = some q)
    (hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    phiFwd C D n a b h =
      ((C.extendXIso e (show e.f p = a from e.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso e (show e.f q = b from e.f_eq_of_r_eq_some hb)).hom) ≫ ιN C D p q n hpq := by
  rw [phiFwd]
  split
  next p' q' hh1 hh2 =>
    obtain rfl : p' = p := Option.some.inj (hh1 ▸ ha)
    obtain rfl : q' = q := Option.some.inj (hh2 ▸ hb)
    rfl
  next hh => exact (hh p q ha hb).elim

/-- Inverse per-summand map for the degree `n` iso. -/
noncomputable def phiInv (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    C.X p ⊗ D.X q ⟶ (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (n : ℤ) :=
  ((C.extendXIso e (show e.f p = (p : ℤ) by simp)).inv ⊗ₘ
    (D.extendXIso e (show e.f q = (q : ℤ) by simp)).inv) ≫
    ιZ C D (p : ℤ) (q : ℤ) (n : ℤ) (by
      have hpq : p + q = n := by simpa using h
      have : (p : ℤ) + q = n := by exact_mod_cast hpq
      simpa using this)

/-- Forward map for the degree `n` iso. -/
noncomputable def fwdNat (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (n : ℤ) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.mapBifunctorDesc (fun a b h => phiFwd C D n a b h)

/-- Inverse map for the degree `n` iso. -/
noncomputable def invNat (n : ℕ) :
    (HomologicalComplex.tensorObj C D).X n ⟶
      (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (n : ℤ) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => phiInv C D n p q h)

/-- `e.r p = some p`. -/
lemma r_nat (p : ℕ) : e.r (p : ℤ) = some p :=
  e.r_eq_some (show e.f p = (p : ℤ) by simp)

/-- Reduction of `fwdNat` on a summand inclusion. -/
lemma ιZ_fwdNat (n : ℕ) (a b : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = (n : ℤ)) :
    ιZ C D a b (n : ℤ) h ≫ fwdNat C D n = phiFwd C D n a b h := by
  simp only [ιZ, fwdNat, ι_mapBifunctorDesc]

/-- Reduction of `invNat` on a summand inclusion. -/
lemma ιN_invNat (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    ιN C D p q n h ≫ invNat C D n = phiInv C D n p q h := by
  simp only [ιN, invNat, ι_mapBifunctorDesc]

set_option backward.isDefEq.respectTransparency false in
/-- `phiInv` followed by `fwdNat` is the summand inclusion. -/
lemma phiInv_comp_fwdNat (n p q : ℕ)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    phiInv C D n p q h ≫ fwdNat C D n = ιN C D p q n h := by
  rw [phiInv, Category.assoc, ιZ_fwdNat, phiFwd_some C D n _ (r_nat p) (r_nat q) h]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- `phiFwd` on a nonzero summand followed by `invNat` is the summand inclusion. -/
lemma phiFwd_comp_invNat (n : ℕ) (a b : ℤ) (h : a + b = (n : ℤ)) {p q : ℕ}
    (ha : e.r a = some p) (hb : e.r b = some q)
    (hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n) :
    phiFwd C D n a b h ≫ invNat C D n = ιZ C D a b (n : ℤ) h := by
  obtain rfl : a = (p : ℤ) := by have := e.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = (q : ℤ) := by have := e.f_eq_of_r_eq_some hb; simpa using this.symm
  rw [phiFwd_some C D n _ (r_nat p) (r_nat q) hpq, Category.assoc, ιN_invNat, phiInv]
  simp

/-- The degree `n` component isomorphism `(extend C ⊗ extend D).X n ≅ (C ⊗ D).X n`. -/
noncomputable def isoNat (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (n : ℤ) ≅
      (HomologicalComplex.tensorObj C D).X n where
  hom := fwdNat C D n
  inv := invNat C D n
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h'
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor C D _ _ p q n h' = ιN C D p q n h' from rfl,
      ιN_invNat]
    exact phiInv_comp_fwdNat C D n p q h'
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b h'
    rcases ha : e.r a with _ | p
    · exact (isZero_tensorObj_left (C.isZero_extend_X' e a ha)).eq_of_src _ _
    rcases hb : e.r b with _ | q
    · exact (isZero_tensorObj_right (D.isZero_extend_X' e b hb)).eq_of_src _ _
    have hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n := by
      have hpa := e.f_eq_of_r_eq_some ha
      have hqb := e.f_eq_of_r_eq_some hb
      simp only [ComplexShape.embeddingUpNat_f] at hpa hqb
      have h2 : a + b = (n : ℤ) := h'
      have : p + q = n := by omega
      simpa using this
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor (C.extend e) (D.extend e) _ _ a b (n : ℤ) h'
        = ιZ C D a b (n : ℤ) h' from rfl,
      ιZ_fwdNat]
    exact phiFwd_comp_invNat C D n a b h' ha hb hpq

/-- The `ℤ`-tensor of the extensions vanishes in negative degrees. -/
lemma isZero_tensorObj_extend_X_of_neg (j' : ℤ) (hj' : j' < 0) :
    IsZero ((HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X j') := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  have hab' : a + b = j' := hab
  rw [Category.comp_id, comp_zero]
  refine (?_ : IsZero _).eq_of_src _ _
  by_cases ha : 0 ≤ a
  · have hb : b < 0 := by omega
    exact isZero_tensorObj_right
      (D.isZero_extend_X e b (fun i => by simp only [ComplexShape.embeddingUpNat_f]; omega))
  · exact isZero_tensorObj_left
      (C.isZero_extend_X e a (fun i => by simp only [ComplexShape.embeddingUpNat_f]; omega))

/-- `e.f n = n` as a stored equality. -/
lemma ef_eq (n : ℕ) : e.f n = (n : ℤ) := by simp

/-- The degree `n` component iso, landing directly in the extension of `C ⊗ D`. -/
noncomputable def isoNatExt (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (n : ℤ) ≅
      ((HomologicalComplex.tensorObj C D).extend e).X (n : ℤ) :=
  isoNat C D n ≪≫
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) e (ef_eq n)).symm

/-- **Milestone (a): the degreewise object iso.** For every `j' : ℤ`,
`(extend C ⊗ extend D).X j' ≅ (extend (C ⊗ D)).X j'`. On the nonzero degrees `j' = n` it is
`isoNatExt`; on negative degrees both sides vanish. -/
noncomputable def tensorExtendXIso (j' : ℤ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X j' ≅
      ((HomologicalComplex.tensorObj C D).extend e).X j' :=
  match hj : e.r j' with
  | some n =>
      eqToIso (congrArg (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X
        (show j' = (n : ℤ) by
          have := e.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingUpNat_f] at this; omega)) ≪≫
      isoNatExt C D n ≪≫
      eqToIso (congrArg ((HomologicalComplex.tensorObj C D).extend e).X
        (show (n : ℤ) = j' by
          have := e.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingUpNat_f] at this; omega))
  | none =>
      IsZero.iso
        (isZero_tensorObj_extend_X_of_neg C D j' (by
          by_contra hle
          have hr : e.r j' = some (j'.toNat) :=
            e.r_eq_some (by simp only [ComplexShape.embeddingUpNat_f]; omega)
          rw [hr] at hj
          simp at hj))
        (HomologicalComplex.isZero_extend_X' _ e j' hj)

/-- `tensorExtendXIso` at `n` is `isoNatExt`. -/
lemma tensorExtendXIso_nat (n : ℕ) :
    tensorExtendXIso C D (n : ℤ) = isoNatExt C D n := by
  rw [tensorExtendXIso]
  split
  next m hm =>
    obtain rfl : m = n := (Option.some.inj ((r_nat n).symm.trans hm)).symm
    apply Iso.ext
    simp
  next hm => rw [r_nat] at hm; simp at hm

set_option backward.isDefEq.respectTransparency false in
/-- **Milestone (a) simp lemma (`.hom`).** Composing the iso with the extend transport recovers
the coproduct forward map `fwdNat`. -/
@[simp]
lemma tensorExtendXIso_hom_extendXIso (n : ℕ) :
    (tensorExtendXIso C D (n : ℤ)).hom ≫
        (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) e (ef_eq n)).hom =
      fwdNat C D n := by
  rw [tensorExtendXIso_nat, isoNatExt]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Milestone (a) simp lemma (`.inv`).** Composing the extend transport with the iso's inverse
recovers the coproduct inverse map `invNat`. -/
@[simp]
lemma extendXIso_inv_tensorExtendXIso_inv (n : ℕ) :
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) e (ef_eq n)).inv ≫
        (tensorExtendXIso C D (n : ℤ)).inv = invNat C D n := by
  rw [tensorExtendXIso_nat, isoNatExt]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id_assoc]
  rfl

/-!
## Milestone (b): differential compatibility

The degreewise isos `tensorExtendXIso` are packaged, via `fwdNat_comm`, into an honest isomorphism
of cochain complexes `tensorObjExtendIso`. The only non-mechanical step is the Koszul sign match
`negOnePow_natCast`. In the `up` case the factor differentials `C.d p (p+1)` never vanish (unlike
the `down` case's `C.d p (p-1)` at `p = 0`), so there are no boundary sub-cases.
-/

/-- **Koszul sign identity.** The `up ℤ` vertical sign `(n : ℤ).negOnePow` agrees with the `up ℕ`
vertical sign `(-1)^n`. -/
lemma negOnePow_natCast (p : ℕ) : Int.negOnePow (p : ℤ) = (-1 : ℤˣ) ^ p := by
  simp [Int.negOnePow, zpow_natCast]

/-- **Milestone (b): differential compatibility of the coproduct forward maps.** The degree-`n`
isos `fwdNat` commute with the (Koszul-signed) total differentials: `fwdNat n` followed by the
`up ℕ` differential of `C ⊗ D` equals the `up ℤ` differential of `extend C ⊗ extend D` followed by
`fwdNat (n+1)`. Proved summand-by-summand via `mapBifunctor.hom_ext`; the `d₁` summands carry sign
`1` on both sides, and the `d₂` summands match through `negOnePow_natCast`. -/
@[reassoc]
lemma fwdNat_comm (n : ℕ) :
    fwdNat C D n ≫ (HomologicalComplex.tensorObj C D).d n (n + 1) =
      (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫
        fwdNat C D (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : e.r a with _ | p
  · exact (isZero_tensorObj_left (C.isZero_extend_X' e a ha)).eq_of_src _ _
  rcases hb : e.r b with _ | q
  · exact (isZero_tensorObj_right (D.isZero_extend_X' e b hb)).eq_of_src _ _
  obtain rfl : a = (p : ℤ) := by
    have := e.f_eq_of_r_eq_some ha
    simp only [ComplexShape.embeddingUpNat_f] at this; omega
  obtain rfl : b = (q : ℤ) := by
    have := e.f_eq_of_r_eq_some hb
    simp only [ComplexShape.embeddingUpNat_f] at this; omega
  have hpq : p + q = n := by
    have h2 : (p : ℤ) + (q : ℤ) = (n : ℤ) := hab
    omega
  rw [← Category.assoc, ιZ_fwdNat C D n (p : ℤ) (q : ℤ) hab,
      phiFwd_some C D n hab (r_nat p) (r_nat q) hpq, Category.assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- d₁ part (factor 1 differential): C.d p (p+1); sign ε₁ = 1
    have hpn : (p + 1) + q = n + 1 := by omega
    rw [mapBifunctor.d₁_eq C D _ (ComplexShape.up ℕ)
          (show (ComplexShape.up ℕ).Rel p (p + 1) by rw [ComplexShape.up_Rel]) q (n + 1) hpn,
        mapBifunctor.d₁_eq (C.extend e) (D.extend e) _ (ComplexShape.up ℤ)
          (show (ComplexShape.up ℤ).Rel (p : ℤ) ((p + 1 : ℕ) : ℤ) by
            rw [ComplexShape.up_Rel]; push_cast; ring) (q : ℤ) ((n + 1 : ℕ) : ℤ)
          (by push_cast; omega : ((p + 1 : ℕ) : ℤ) + (q : ℤ) = ((n + 1 : ℕ) : ℤ)),
        extend_d_eq C e (ef_eq p) (ef_eq (p + 1)),
        show ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q)
          = (1 : ℤˣ) from rfl,
        show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              ((p : ℤ), (q : ℤ)) = (1 : ℤˣ) from rfl]
    simp only [one_smul, Category.assoc]
    rw [ιZ_fwdNat C D (n + 1) ((p + 1 : ℕ) : ℤ) (q : ℤ)
          (by push_cast; omega : ((p + 1 : ℕ) : ℤ) + (q : ℤ) = ((n + 1 : ℕ) : ℤ)),
        phiFwd_some C D (n + 1) _ (r_nat (p + 1)) (r_nat q) (by simpa using hpn)]
    simp only [Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app,
      Category.assoc, MonoidalCategory.tensorHom_def, whisker_exchange_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
  · -- d₂ part (factor 2 differential): D.d q (q+1); sign ε₂ = (-1)^p
    have hpn : p + (q + 1) = n + 1 := by omega
    rw [mapBifunctor.d₂_eq C D _ (ComplexShape.up ℕ) p
          (show (ComplexShape.up ℕ).Rel q (q + 1) by rw [ComplexShape.up_Rel]) (n + 1) hpn,
        mapBifunctor.d₂_eq (C.extend e) (D.extend e) _ (ComplexShape.up ℤ) (p : ℤ)
          (show (ComplexShape.up ℤ).Rel (q : ℤ) ((q + 1 : ℕ) : ℤ) by
            rw [ComplexShape.up_Rel]; push_cast; ring) ((n + 1 : ℕ) : ℤ)
          (by push_cast; omega : (p : ℤ) + ((q + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)),
        extend_d_eq D e (ef_eq q) (ef_eq (q + 1)),
        show ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q)
          = Int.negOnePow (p : ℤ) from (negOnePow_natCast p).symm,
        show ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              ((p : ℤ), (q : ℤ)) = Int.negOnePow (p : ℤ) from rfl]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
    rw [ιZ_fwdNat C D (n + 1) (p : ℤ) ((q + 1 : ℕ) : ℤ)
          (by push_cast; omega : (p : ℤ) + ((q + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)),
        phiFwd_some C D (n + 1) _ (r_nat p) (r_nat (q + 1)) (by simpa using hpn)]
    congr 1
    simp only [curriedTensor_obj_map, Category.assoc,
      MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Milestone (c): the complex isomorphism.** Assemble the degreewise isos `tensorExtendXIso`
into an isomorphism of `ℤ`-cochain complexes `extend C ⊗ extend D ≅ extend (C ⊗ D)`, using
`fwdNat_comm` for differential compatibility on the nonzero degrees `j = n` and vanishing of the
source on negative degrees. -/
noncomputable def tensorObjExtendIso :
    HomologicalComplex.tensorObj (C.extend e) (D.extend e) ≅
      (HomologicalComplex.tensorObj C D).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun j' => tensorExtendXIso C D j') (by
    intro i j hij
    by_cases hi : i < 0
    · exact (isZero_tensorObj_extend_X_of_neg C D i hi).eq_of_src _ _
    · rw [not_lt] at hi
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) := ⟨i.toNat, by omega⟩
      obtain rfl : j = ((n + 1 : ℕ) : ℤ) := by
        have : (n : ℤ) + 1 = j := hij
        push_cast; omega
      rw [HomologicalComplex.extend_d_eq (HomologicalComplex.tensorObj C D) e
            (ef_eq n) (ef_eq (n + 1)),
          ← Category.assoc, tensorExtendXIso_hom_extendXIso C D n,
          fwdNat_comm_assoc C D n]
      congr 1
      rw [← tensorExtendXIso_hom_extendXIso C D (n + 1), Category.assoc, Iso.hom_inv_id,
        Category.comp_id])

/-!
## Naturality of the comparison

The cochain mirror of `TensorExtend`'s milestone (d). `tensorObjExtendIso` is natural in
`(C, D)`: degreewise it is a `mapBifunctorDesc` over the `ιTensorObj` injections, and both those
injections (`ι_mapBifunctorMap`) and the `extendXIso` transports (`extendMap_f`) are natural.

`fwdNat_naturality` is the degreewise square, `tensorObjExtendIso_hom_naturality` the
complex-level one (with `_left`/`_right` giving the one-variable specialisations), and
`tensorObjExtendNatIso` packages the comparison as an isomorphism of the two bifunctors
`(C, D) ↦ extend C ⊗ extend D` and `(C, D) ↦ extend (C ⊗ D)`.
-/

section Naturality

variable {C₁ C₂ D₁ D₂ : CochainComplex (ModuleCat.{u} k) ℕ}

/-- **Naturality of the degree `n` forward map.** The coproduct forward maps `fwdNat` intertwine
`tensorHom (extendMap f) (extendMap g)` with `tensorHom f g`. Proved summand-by-summand: the
summands outside the image of the embedding have zero source, and on an `(a, b) = (p, q)` summand
both sides reduce to `((extendXIso C₁).hom ≫ f.f p) ⊗ₘ ((extendXIso D₁).hom ≫ g.f q)` followed by
the `ℕ`-side injection `ιN C₂ D₂ p q n`. -/
lemma fwdNat_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) (n : ℕ) :
    (HomologicalComplex.tensorHom (HomologicalComplex.extendMap f e)
          (HomologicalComplex.extendMap g e)).f (n : ℤ) ≫ fwdNat C₂ D₂ n =
      fwdNat C₁ D₁ n ≫ (HomologicalComplex.tensorHom f g).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : e.r a with _ | p
  · exact (isZero_tensorObj_left (C₁.isZero_extend_X' e a ha)).eq_of_src _ _
  rcases hb : e.r b with _ | q
  · exact (isZero_tensorObj_right (D₁.isZero_extend_X' e b hb)).eq_of_src _ _
  obtain rfl : a = (p : ℤ) := by have := e.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = (q : ℤ) := by have := e.f_eq_of_r_eq_some hb; simpa using this.symm
  have hab' : (p : ℤ) + (q : ℤ) = (n : ℤ) := hab
  have hpq : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = n := by
    have : p + q = n := by omega
    simpa using this
  rw [show HomologicalComplex.ιMapBifunctor (C₁.extend e) (D₁.extend e)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (p : ℤ) (q : ℤ) (n : ℤ) hab = ιZ C₁ D₁ _ _ _ hab from rfl]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, ιZ_fwdNat,
    phiFwd_some C₂ D₂ n _ (r_nat p) (r_nat q) hpq,
    ← Category.assoc (ιZ C₁ D₁ _ _ _ hab), ιZ_fwdNat,
    phiFwd_some C₁ D₁ n _ (r_nat p) (r_nat q) hpq,
    Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.extendMap_f f e (ef_eq p),
    HomologicalComplex.extendMap_f g e (ef_eq q)]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id]

-- The reassociated form of `tensorExtendXIso_hom_extendXIso`, used to strip the extend
-- transport off the middle of a composite in `tensorObjExtendIso_hom_naturality`.
attribute [reassoc] tensorExtendXIso_hom_extendXIso

/-- **Naturality of the complex isomorphism.** The tensor/extend comparison
`extend C ⊗ extend D ≅ extend (C ⊗ D)` commutes with the maps induced by arbitrary cochain maps
`f : C₁ ⟶ C₂` and `g : D₁ ⟶ D₂`. Degreewise this is `fwdNat_naturality`; the degrees outside the
image of the embedding are handled by vanishing of the target. -/
theorem tensorObjExtendIso_hom_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f e)
          (HomologicalComplex.extendMap g e) ≫ (tensorObjExtendIso C₂ D₂).hom =
      (tensorObjExtendIso C₁ D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f g) e := by
  ext j' : 1
  by_cases hj : j' < 0
  · exact (HomologicalComplex.isZero_extend_X (HomologicalComplex.tensorObj C₂ D₂) e j'
      (fun m => by simp only [ComplexShape.embeddingUpNat_f]; omega)).eq_of_tgt _ _
  · rw [not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j' = (n : ℤ) := ⟨j'.toNat, by omega⟩
    rw [← cancel_mono (HomologicalComplex.extendXIso
      (HomologicalComplex.tensorObj C₂ D₂) e (ef_eq n)).hom,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      show (tensorObjExtendIso C₂ D₂).hom.f (n : ℤ) = (tensorExtendXIso C₂ D₂ (n : ℤ)).hom
        from rfl,
      show (tensorObjExtendIso C₁ D₁).hom.f (n : ℤ) = (tensorExtendXIso C₁ D₁ (n : ℤ)).hom
        from rfl,
      tensorExtendXIso_hom_extendXIso,
      HomologicalComplex.extendMap_f (HomologicalComplex.tensorHom f g) e (ef_eq n),
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      tensorExtendXIso_hom_extendXIso_assoc]
    exact fwdNat_naturality f g n

/-- Naturality in the first argument. -/
theorem tensorObjExtendIso_hom_naturality_left (f : C₁ ⟶ C₂)
    (D : CochainComplex (ModuleCat.{u} k) ℕ) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f e) (𝟙 (D.extend e)) ≫
        (tensorObjExtendIso C₂ D).hom =
      (tensorObjExtendIso C₁ D).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f (𝟙 D)) e := by
  simpa using tensorObjExtendIso_hom_naturality f (𝟙 D)

/-- Naturality in the second argument. -/
theorem tensorObjExtendIso_hom_naturality_right (C : CochainComplex (ModuleCat.{u} k) ℕ)
    (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (𝟙 (C.extend e)) (HomologicalComplex.extendMap g e) ≫
        (tensorObjExtendIso C D₂).hom =
      (tensorObjExtendIso C D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom (𝟙 C) g) e := by
  simpa using tensorObjExtendIso_hom_naturality (𝟙 C) g

end Naturality

section Bifunctor

/-- The tensor bifunctor on `ℕ`-cochain complexes. -/
noncomputable abbrev tensorBifunctorN :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℕ :=
  (curriedTensor (ModuleCat.{u} k)).map₂HomologicalComplex
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)

/-- `extend` along `embeddingUpNat` as a functor `CochainComplex ℕ ⥤ CochainComplex ℤ`. -/
noncomputable abbrev extFunctor :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  e.extendFunctor (ModuleCat.{u} k)

/-- The bifunctor `(C, D) ↦ extend C ⊗ extend D`. -/
noncomputable abbrev tensorExtendSrc :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (extFunctor ⋙ TensorExtend.tensorBifunctorZ) ⋙
    (CategoryTheory.Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj extFunctor

/-- The bifunctor `(C, D) ↦ extend (C ⊗ D)`. -/
noncomputable abbrev tensorExtendTgt :
    CochainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  tensorBifunctorN ⋙
    (CategoryTheory.Functor.whiskeringRight (CochainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj extFunctor

/-- **The tensor/extend comparison as an isomorphism of bifunctors (cochain case).** Assembles
`tensorObjExtendIso` over all `(C, D)` into a `NatIso` between `tensorExtendSrc` and
`tensorExtendTgt`; the objectwise isos are recovered as `(tensorObjExtendNatIso.app C).app D`. -/
noncomputable def tensorObjExtendNatIso :
    tensorExtendSrc (k := k) ≅ tensorExtendTgt (k := k) :=
  NatIso.ofComponents
    (fun C => NatIso.ofComponents (fun D => tensorObjExtendIso C D) (fun {D₁ D₂} g => by
      have h := tensorObjExtendIso_hom_naturality (𝟙 C) g
      rw [HomologicalComplex.extendMap_id] at h
      exact h))
    (fun {C₁ C₂} f => by
      ext D : 2
      simp only [NatTrans.comp_app]
      have h := tensorObjExtendIso_hom_naturality f (𝟙 D)
      rw [HomologicalComplex.extendMap_id] at h
      exact h)

/-- The objectwise components of `tensorObjExtendNatIso` are the original `tensorObjExtendIso`. -/
@[simp]
lemma tensorObjExtendNatIso_app_app (C D : CochainComplex (ModuleCat.{u} k) ℕ) :
    (tensorObjExtendNatIso.app C).app D = tensorObjExtendIso C D :=
  rfl

end Bifunctor

end TensorExtendUp

/-- **Tensor ∘ extend compatibility (cochain case).** The `ℤ`-tensor of the extensions is the
extension of the `ℕ`-tensor:
`extend e C ⊗ extend e D ≅ extend e (C ⊗ D)`, `e = embeddingUpNat`.

Degreewise both sides are `⨁_{p+q=n} C_p ⊗ D_q` at `+n` and zero at negative degrees; the content
is matching the `ιTensorObj` injections and the Koszul-signed total differential. Universe-general
and independent of Chapter 7. Constructed via `TensorExtendUp.tensorObjExtendIso`. -/
theorem nonempty_tensorObj_extend_iso_up (C D : CochainComplex (ModuleCat.{u} k) ℕ) :
    Nonempty (HomologicalComplex.tensorObj (C.extend ComplexShape.embeddingUpNat)
        (D.extend ComplexShape.embeddingUpNat) ≅
      (HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingUpNat) :=
  ⟨TensorExtendUp.tensorObjExtendIso C D⟩

/-- **Künneth for `ℕ`-indexed cochain complexes.** For cochain complexes `C, D` of `k`-vector
spaces indexed over `ℕ`, the homology of the tensor product decomposes as a direct sum:
`Hⁱ(C ⊗ D) ≅ ⨁_{p+q=i} Hᵖ(C) ⊗ Hᵍ(D)`.

Reindexes Chapter 7's `Etingof.Problem7_8_7_iv` along `embeddingUpNat`; the exact mirror of
`kunnethChainComplexNatIso`. Consumed by the Problem 8.2.8 `Ext` construction on the Hom cochain
complexes `Hom_A(P•, N)`.

## Naturality of the four steps

As in the chain case, **all four steps are natural in `(C, D)`** and none is a non-natural
choice: `α₁`, `α₄` by `homology_extend_iso_up_hom_naturality`, `α₃` by `Etingof.kunnethNatIso`.
Step `α₂` is formalized by `TensorExtendUp.tensorObjExtendIso_hom_naturality` and packaged by
`TensorExtendUp.tensorObjExtendNatIso`. `KunnethNatBifunctor.lean` composes all four squares into
`kunnethCochainComplexNatNatIso`, whose component theorem recovers this isomorphism. -/
noncomputable def kunnethCochainComplexNatIso (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2 := by
  let e := ComplexShape.embeddingUpNat
  -- Step 1: `Hⁱ(C ⊗ D) ≅ Hⁱ(extend (C ⊗ D))`.
  let α₁ : (HomologicalComplex.tensorObj C D).homology i ≅
      ((HomologicalComplex.tensorObj C D).extend e).homology (i : ℤ) :=
    (homology_extend_iso_up (HomologicalComplex.tensorObj C D) i).symm
  -- Step 2: apply `Hⁱ` to the compatibility iso `extend (C ⊗ D) ≅ extend C ⊗ extend D`.
  let φ : (HomologicalComplex.tensorObj C D).extend e ≅
      HomologicalComplex.tensorObj (C.extend e) (D.extend e) :=
    (TensorExtendUp.tensorObjExtendIso C D).symm
  let α₂ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (i : ℤ)).mapIso φ
  -- Step 3: Chapter 7's universe-general Künneth at degree `i`, as the honest isomorphism
  -- inverse to the natural cross product `kunnethMap`.
  let α₃ := Problem7_8_7_iv (C.extend e) (D.extend e) (i : ℤ)
  -- Step 4: reindex the `ℤ`-coproduct `⨁_{a+b=i}` onto the `ℕ`-antidiagonal `⨁_{p+q=i}`;
  -- the summands with `a < 0` or `b < 0` vanish by `homology_extend_isZero_up`.
  let ι : {p : ℕ × ℕ // p.1 + p.2 = i} → {p : ℤ × ℤ // p.1 + p.2 = (i : ℤ)} :=
    fun p => ⟨((p.1.1 : ℤ), (p.1.2 : ℤ)), by
      have h2 : (p.1.1 : ℤ) + (p.1.2 : ℤ) = (i : ℤ) := by exact_mod_cast p.2
      exact h2⟩
  have hι : Function.Injective ι := by
    intro p p' hpp
    apply Subtype.ext
    have hv : (ι p).1 = (ι p').1 := congrArg Subtype.val hpp
    have h1 : (p.1.1 : ℤ) = (p'.1.1 : ℤ) := congrArg Prod.fst hv
    have h2 : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := congrArg Prod.snd hv
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  let α₄ : (∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = (i : ℤ)}) =>
        (C.extend e).homology p.1.1 ⊗ (D.extend e).homology p.1.2) ≅
      (∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) :=
    sigmaIsoOfInjOfIsZeroCompl ι hι
      (fun a => tensorIso (homology_extend_iso_up C a.1.1) (homology_extend_iso_up D a.1.2))
      (by
        rintro ⟨⟨a, b⟩, hab⟩ hj
        by_cases ha : a < 0
        · exact TensorExtendUp.isZero_tensorObj_left (homology_extend_isZero_up C a ha)
        by_cases hb : b < 0
        · exact TensorExtendUp.isZero_tensorObj_right (homology_extend_isZero_up D b hb)
        rw [not_lt] at ha hb
        exfalso
        have hp : ((a.toNat) : ℤ) = a := Int.toNat_of_nonneg ha
        have hq : ((b.toNat) : ℤ) = b := Int.toNat_of_nonneg hb
        have hpq : a.toNat + b.toNat = i := by
          have : ((a.toNat) : ℤ) + ((b.toNat) : ℤ) = (i : ℤ) := by rw [hp, hq]; exact hab
          exact_mod_cast this
        refine hj ⟨(a.toNat, b.toNat), hpq⟩ (Subtype.ext ?_)
        change (((a.toNat : ℕ) : ℤ), ((b.toNat : ℕ) : ℤ)) = (a, b)
        rw [Prod.mk.injEq]
        exact ⟨hp, hq⟩)
  exact α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄

/-- **Künneth for `ℕ`-indexed cochain complexes**, `Nonempty` form. A one-line corollary of
`kunnethCochainComplexNatIso`, kept so that existing consumers phrased in terms of `Nonempty`
keep working; new consumers should use the `Iso` directly. -/
theorem kunnethCochainComplexNat (C D : CochainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    Nonempty ((HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2) :=
  ⟨kunnethCochainComplexNatIso C D i⟩

end Etingof
