import Mathlib
import EtingofRepresentationTheory.Chapter7.Problem7_8_7
import EtingofRepresentationTheory.Chapter7.KunnethIso

set_option backward.isDefEq.respectTransparency false

/-!
# Künneth for `ℕ`-indexed chain complexes via `ℕ`/`ℤ` reindexing

Chapter 7's Künneth formula (`Etingof.Problem7_8_7_iv`) is stated for cohomologically
indexed `CochainComplex (ModuleCat k) ℤ`. The `Tor`/`Ext` construction of Problem 8.2.8,
however, works with its own complexes `P• ⊗_A N`, which are homologically indexed
`ChainComplex (ModuleCat.{u} k) ℕ`
(`= HomologicalComplex _ (ComplexShape.down ℕ)`). This file provides a Künneth
isomorphism for `ℕ`-indexed chain complexes, obtained by reindexing the `ℤ` result rather than
reproving it.

## The reindexing embedding

Mathlib's `ComplexShape.embeddingDownNat : Embedding (down ℕ) (up ℤ)` sends `n ↦ -n`
(`Mathlib/Algebra/Homology/Embedding/Basic.lean`), with the needed `IsRelIff`/`IsTruncLE`
instances. `HomologicalComplex.extend embeddingDownNat` sends a `ChainComplex ℕ` to a
`CochainComplex ℤ` supported on `ℤ≤0` (the image of `n ↦ -n`), zero elsewhere.

Homology transport is Mathlib's `HomologicalComplex.extendHomologyIso`:
`Hⁱ(extend C) ≅ H_{-i}(C)` at `i = -n` in the image, and `extend_exactAt` gives vanishing
outside the image. These two facts are proved here as `homology_extend_iso` and
`homology_extend_isZero`.

## Tensor ∘ extend compatibility

The remaining step, with no direct Mathlib support, is the compatibility of `extend` with the
monoidal (tensor) structure:

`extend e C ⊗ extend e D ≅ extend e (C ⊗ D)`  (in the `up ℤ` monoidal structure).

Degreewise this reads: `(extend C ⊗ extend D)_{j'} = ⨁_{a+b=j'} (extend C)_a ⊗ (extend D)_b`.
Since `extend C` is supported on `ℤ≤0`, the only nonzero summands have `a = -p`, `b = -q` with
`p, q : ℕ`; when `j' = -n` these are exactly the `p + q = n` summands, matching
`(C ⊗ D)_n = ⨁_{p+q=n} C_p ⊗ D_q = (extend (C ⊗ D))_{-n}`. Both sides vanish for `j' > 0`. The
categorical work is to assemble this degreewise identification into an isomorphism of complexes,
matching the `ιTensorObj` injections and the Koszul-signed total differential (`d₁` and `d₂`
summands). This is `nonempty_tensorObj_extend_iso` below, constructed via
`TensorExtend.tensorObjExtendIso` (milestones (a)–(c)).

The comparison is moreover natural in `(C, D)` (milestone (d)):
`TensorExtend.tensorObjExtendIso_hom_naturality` states the joint naturality square, and
`TensorExtend.tensorObjExtendNatIso` packages the whole comparison as an isomorphism of the
bifunctors `(C, D) ↦ extend C ⊗ extend D` and `(C, D) ↦ extend (C ⊗ D)`.

Note `extend C ⊗ extend D` is itself supported on `ℤ≤0`, i.e. on the image of the embedding, so
this iso can equivalently be read as "the `ℤ`-tensor of the extends is the extension of the
`ℕ`-tensor".

## The resulting isomorphism

`Hᵢ(C ⊗ D)` (`ℕ`) `≅ H_{-i}(extend (C ⊗ D))` `≅ H_{-i}(extend C ⊗ extend D)` (compatibility)
`≅ ⨁_{a+b=-i} H_a(extend C) ⊗ H_b(extend D)` (Chapter 7 Künneth at universe `u`, degree `-i`)
`≅ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)` (reindex `a = -p`, `b = -q`; the `a > 0` / `b > 0` summands are
zero by `homology_extend_isZero`).

The final identification uses the universe-general `Problem7_8_7_iv`, the honest isomorphism
inverse to the natural cross product `Etingof.kunnethMap`. The reindex of the coproduct is not a
bare index bijection: the `ℤ`-side sum `⨁_{a+b=-i}` ranges over all of `ℤ × ℤ`, and the extra
summands vanish only via `homology_extend_isZero`.

The objectwise deliverable is `kunnethChainComplexNatIso`; `kunnethChainComplexNat` is its
`Nonempty` compatibility corollary. `KunnethNatBifunctor.lean` packages these same components as
the natural isomorphism `kunnethChainComplexNatNatIso`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace Etingof

universe u

variable {k : Type u} [Field k]

/-- Homology of `extend e C` at the embedded degree `-n` recovers `H_n(C)`. Direct instance of
Mathlib's `extendHomologyIso` for `embeddingDownNat` (`e.f n = -n`). -/
noncomputable def homology_extend_iso (C : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (C.extend ComplexShape.embeddingDownNat).homology (-(n : ℤ)) ≅ C.homology n :=
  C.extendHomologyIso ComplexShape.embeddingDownNat (by simp)

/-- **`homology_extend_iso` is natural in the complex.** For `φ : C ⟶ D` the square

`H_{-n}(extend C) → H_{-n}(extend D)`
`      ↓                  ↓        `
`   H_n(C)      →      H_n(D)      `

commutes, the horizontal maps being `homologyMap (extendMap φ e) (-n)` and `homologyMap φ n`.
This is Mathlib's `extendHomologyIso_hom_naturality` at `e = embeddingDownNat`; it supplies the
naturality of steps 1 and 4 of `kunnethChainComplexNatIso` (see that definition's docstring). -/
@[reassoc]
lemma homology_extend_iso_hom_naturality {C D : ChainComplex (ModuleCat.{u} k) ℕ} (φ : C ⟶ D)
    (n : ℕ) :
    homologyMap (extendMap φ ComplexShape.embeddingDownNat) (-(n : ℤ)) ≫
        (homology_extend_iso D n).hom =
      (homology_extend_iso C n).hom ≫ homologyMap φ n :=
  HomologicalComplex.extendHomologyIso_hom_naturality (φ := φ)
    (e := ComplexShape.embeddingDownNat) (hj' := by simp)

/-- Homology of `extend e C` vanishes at positive degrees `j' > 0`, which lie outside the image
`{-n : n : ℕ} = ℤ≤0` of `embeddingDownNat`. -/
theorem homology_extend_isZero (C : ChainComplex (ModuleCat.{u} k) ℕ) (j' : ℤ) (hj' : 0 < j') :
    IsZero ((C.extend ComplexShape.embeddingDownNat).homology j') := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine HomologicalComplex.extend_exactAt _ _ j' (fun j => ?_)
  simp only [ComplexShape.embeddingDownNat_f]
  omega

namespace TensorExtend

/-!
## Milestone (a): the degreewise object isomorphism

This section constructs, for every `j' : ℤ`, the degreewise isomorphism
`(extend C ⊗ extend D).X j' ≅ (extend (C ⊗ D)).X j'` (`tensorExtendXIso`), the object-level half
of `nonempty_tensorObj_extend_iso`. The nonzero degrees are `j' = -n`, where both sides
identify with `⨁_{p+q=n} C_p ⊗ D_q`; positive degrees are zero on both sides.

The forward/inverse maps are assembled out of `mapBifunctorDesc` over the summand maps `phiFwd`
(nonzero summands `(a,b) = (-p,-q)`) and `phiInv`, and packaged as `isoNeg`. The two summand
compatibility lemmas `tensorExtendXIso_hom_extendXIso` and `extendXIso_inv_tensorExtendXIso_inv`
are what milestone (b) consumes to check differential compatibility.
-/

/-- The reindexing embedding `n ↦ -n`. -/
noncomputable abbrev e : ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) :=
  ComplexShape.embeddingDownNat

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

variable (C D : ChainComplex (ModuleCat.{u} k) ℕ)

/-- Summand inclusion into `(tensorObj C D).X n`, spelled as `ιMapBifunctor`. -/
noncomputable abbrev ιN (p q n : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    ((curriedTensor (ModuleCat.{u} k)).obj (C.X p)).obj (D.X q) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.ιMapBifunctor C D (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ)
    p q n h

/-- Summand inclusion into `(tensorObj (extend C) (extend D)).X j`, spelled as `ιMapBifunctor`. -/
noncomputable abbrev ιZ (a b j : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = j) :
    ((curriedTensor (ModuleCat.{u} k)).obj ((C.extend e).X a)).obj ((D.extend e).X b) ⟶
      (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X j :=
  HomologicalComplex.ιMapBifunctor (C.extend e) (D.extend e) (curriedTensor (ModuleCat.{u} k))
    (ComplexShape.up ℤ) a b j h

/-- Forward per-summand map for the degree `-n` iso. -/
noncomputable def phiFwd (n : ℕ) (a b : ℤ) (h : a + b = -(n : ℤ)) :
    (C.extend e).X a ⊗ (D.extend e).X b ⟶ (HomologicalComplex.tensorObj C D).X n :=
  match ha : e.r a, hb : e.r b with
  | some p, some q =>
      ((C.extendXIso e (e.f_eq_of_r_eq_some ha)).hom ⊗ₘ
        (D.extendXIso e (e.f_eq_of_r_eq_some hb)).hom) ≫
        ιN C D p q n (by
          have hp := e.f_eq_of_r_eq_some ha
          have hq := e.f_eq_of_r_eq_some hb
          simp only [ComplexShape.embeddingDownNat_f] at hp hq
          have : p + q = n := by omega
          simpa using this)
  | _, _ => 0

/-- Reduction of `phiFwd` on the nonzero (some/some) summands. -/
lemma phiFwd_some (n : ℕ) {a b : ℤ} (h : a + b = -(n : ℤ)) {p q : ℕ}
    (ha : e.r a = some p) (hb : e.r b = some q)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
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

/-- Inverse per-summand map for the degree `-n` iso. -/
noncomputable def phiInv (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    C.X p ⊗ D.X q ⟶ (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (-(n : ℤ)) :=
  ((C.extendXIso e (show e.f p = -(p : ℤ) by simp)).inv ⊗ₘ
    (D.extendXIso e (show e.f q = -(q : ℤ) by simp)).inv) ≫
    ιZ C D (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by
      have hpq : p + q = n := by simpa using h
      have : (p : ℤ) + q = n := by exact_mod_cast hpq
      simpa using by omega)

/-- Forward map for the degree `-n` iso. -/
noncomputable def fwdNeg (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (-(n : ℤ)) ⟶
      (HomologicalComplex.tensorObj C D).X n :=
  HomologicalComplex.mapBifunctorDesc (fun a b h => phiFwd C D n a b h)

/-- Inverse map for the degree `-n` iso. -/
noncomputable def invNeg (n : ℕ) :
    (HomologicalComplex.tensorObj C D).X n ⟶
      (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (-(n : ℤ)) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h => phiInv C D n p q h)

/-- `e.r (-p) = some p`. -/
lemma r_negNat (p : ℕ) : e.r (-(p : ℤ)) = some p :=
  e.r_eq_some (show e.f p = -(p : ℤ) by simp)

/-- Reduction of `fwdNeg` on a summand inclusion. -/
lemma ιZ_fwdNeg (n : ℕ) (a b : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = -(n : ℤ)) :
    ιZ C D a b (-(n : ℤ)) h ≫ fwdNeg C D n = phiFwd C D n a b h := by
  simp only [ιZ, fwdNeg, ι_mapBifunctorDesc]

/-- Reduction of `invNeg` on a summand inclusion. -/
lemma ιN_invNeg (n : ℕ) (p q : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    ιN C D p q n h ≫ invNeg C D n = phiInv C D n p q h := by
  simp only [ιN, invNeg, ι_mapBifunctorDesc]

set_option backward.isDefEq.respectTransparency false in
/-- `phiInv` followed by `fwdNeg` is the summand inclusion. -/
lemma phiInv_comp_fwdNeg (n p q : ℕ)
    (h : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    phiInv C D n p q h ≫ fwdNeg C D n = ιN C D p q n h := by
  rw [phiInv, Category.assoc, ιZ_fwdNeg, phiFwd_some C D n _ (r_negNat p) (r_negNat q) h]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- `phiFwd` on a nonzero summand followed by `invNeg` is the summand inclusion. -/
lemma phiFwd_comp_invNeg (n : ℕ) (a b : ℤ) (h : a + b = -(n : ℤ)) {p q : ℕ}
    (ha : e.r a = some p) (hb : e.r b = some q)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n) :
    phiFwd C D n a b h ≫ invNeg C D n = ιZ C D a b (-(n : ℤ)) h := by
  obtain rfl : a = -(p : ℤ) := by have := e.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = -(q : ℤ) := by have := e.f_eq_of_r_eq_some hb; simpa using this.symm
  rw [phiFwd_some C D n _ (r_negNat p) (r_negNat q) hpq, Category.assoc, ιN_invNeg, phiInv]
  simp

/-- The degree `-n` component isomorphism `(extend C ⊗ extend D).X (-n) ≅ (C ⊗ D).X n`. -/
noncomputable def isoNeg (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (-(n : ℤ)) ≅
      (HomologicalComplex.tensorObj C D).X n where
  hom := fwdNeg C D n
  inv := invNeg C D n
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h'
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor C D _ _ p q n h' = ιN C D p q n h' from rfl,
      ιN_invNeg]
    exact phiInv_comp_fwdNeg C D n p q h'
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b h'
    rcases ha : e.r a with _ | p
    · exact (isZero_tensorObj_left (C.isZero_extend_X' e a ha)).eq_of_src _ _
    rcases hb : e.r b with _ | q
    · exact (isZero_tensorObj_right (D.isZero_extend_X' e b hb)).eq_of_src _ _
    have hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n := by
      have hpa := e.f_eq_of_r_eq_some ha
      have hqb := e.f_eq_of_r_eq_some hb
      simp only [ComplexShape.embeddingDownNat_f] at hpa hqb
      have h2 : a + b = -(n : ℤ) := h'
      have : p + q = n := by omega
      simpa using this
    rw [Category.comp_id, ← Category.assoc,
      show HomologicalComplex.ιMapBifunctor (C.extend e) (D.extend e) _ _ a b (-(n : ℤ)) h'
        = ιZ C D a b (-(n : ℤ)) h' from rfl,
      ιZ_fwdNeg]
    exact phiFwd_comp_invNeg C D n a b h' ha hb hpq

/-- The `ℤ`-tensor of the extensions vanishes in positive degrees. -/
lemma isZero_tensorObj_extend_X_of_pos (j' : ℤ) (hj' : 0 < j') :
    IsZero ((HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X j') := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  have hab' : a + b = j' := hab
  rw [Category.comp_id, comp_zero]
  refine (?_ : IsZero _).eq_of_src _ _
  by_cases ha : a ≤ 0
  · have hb : 0 < b := by omega
    exact isZero_tensorObj_right
      (D.isZero_extend_X e b (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega))
  · exact isZero_tensorObj_left
      (C.isZero_extend_X e a (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega))

/-- `e.f n = -n` as a stored equality. -/
lemma ef_eq_neg (n : ℕ) : e.f n = -(n : ℤ) := by simp

/-- The degree `-n` component iso, landing directly in the extension of `C ⊗ D`. -/
noncomputable def isoNegExt (n : ℕ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X (-(n : ℤ)) ≅
      ((HomologicalComplex.tensorObj C D).extend e).X (-(n : ℤ)) :=
  isoNeg C D n ≪≫
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) e (ef_eq_neg n)).symm

/-- **Milestone (a): the degreewise object iso.** For every `j' : ℤ`,
`(extend C ⊗ extend D).X j' ≅ (extend (C ⊗ D)).X j'`. On the nonzero degrees `j' = -n` it is
`isoNegExt`; on positive degrees both sides vanish. -/
noncomputable def tensorExtendXIso (j' : ℤ) :
    (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X j' ≅
      ((HomologicalComplex.tensorObj C D).extend e).X j' :=
  match hj : e.r j' with
  | some n =>
      eqToIso (congrArg (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).X
        (show j' = -(n : ℤ) by
          have := e.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingDownNat_f] at this; omega)) ≪≫
      isoNegExt C D n ≪≫
      eqToIso (congrArg ((HomologicalComplex.tensorObj C D).extend e).X
        (show -(n : ℤ) = j' by
          have := e.f_eq_of_r_eq_some hj
          simp only [ComplexShape.embeddingDownNat_f] at this; omega))
  | none =>
      IsZero.iso
        (isZero_tensorObj_extend_X_of_pos C D j' (by
          by_contra hle
          have hr : e.r j' = some ((-j').toNat) :=
            e.r_eq_some (by simp only [ComplexShape.embeddingDownNat_f]; omega)
          rw [hr] at hj
          simp at hj))
        (HomologicalComplex.isZero_extend_X' _ e j' hj)

/-- `tensorExtendXIso` at `-n` is `isoNegExt`. -/
lemma tensorExtendXIso_neg (n : ℕ) :
    tensorExtendXIso C D (-(n : ℤ)) = isoNegExt C D n := by
  rw [tensorExtendXIso]
  split
  next m hm =>
    obtain rfl : m = n := (Option.some.inj ((r_negNat n).symm.trans hm)).symm
    apply Iso.ext
    simp
  next hm => rw [r_negNat] at hm; simp at hm

set_option backward.isDefEq.respectTransparency false in
/-- **Milestone (a) simp lemma (`.hom`).** Composing the iso with the extend transport recovers
the coproduct forward map `fwdNeg` (whose action on summand inclusions is `ιZ_fwdNeg`). -/
@[simp]
lemma tensorExtendXIso_hom_extendXIso (n : ℕ) :
    (tensorExtendXIso C D (-(n : ℤ))).hom ≫
        (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) e (ef_eq_neg n)).hom =
      fwdNeg C D n := by
  rw [tensorExtendXIso_neg, isoNegExt]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Milestone (a) simp lemma (`.inv`).** Composing the extend transport with the iso's inverse
recovers the coproduct inverse map `invNeg` (whose action on summand inclusions is `ιN_invNeg`). -/
@[simp]
lemma extendXIso_inv_tensorExtendXIso_inv (n : ℕ) :
    (HomologicalComplex.extendXIso (HomologicalComplex.tensorObj C D) e (ef_eq_neg n)).inv ≫
        (tensorExtendXIso C D (-(n : ℤ))).inv = invNeg C D n := by
  rw [tensorExtendXIso_neg, isoNegExt]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.inv_hom_id_assoc]
  rfl

/-!
## Milestone (b): differential compatibility

The degreewise isos `tensorExtendXIso` (milestone (a)) are packaged, via `fwdNeg_comm`, into an
honest isomorphism of chain complexes `tensorObjExtendIso`, discharging
`nonempty_tensorObj_extend_iso`. The only non-mechanical step is the Koszul sign match
`negOnePow_neg_natCast`.
-/

/-- **Koszul sign identity.** Under the reindex `a = -p`, the `up ℤ` vertical sign `a.negOnePow`
agrees with the `down ℕ` vertical sign `(-1)^p`. -/
lemma negOnePow_neg_natCast (p : ℕ) : Int.negOnePow (-(p : ℤ)) = (-1 : ℤˣ) ^ p := by
  rw [Int.negOnePow_neg]
  simp [Int.negOnePow, zpow_natCast]

/-- **Milestone (b): differential compatibility of the coproduct forward maps.** The degree-`-n`
isos `fwdNeg` commute with the (Koszul-signed) total differentials: `fwdNeg (n+1)` followed by the
`down ℕ` differential of `C ⊗ D` equals the `up ℤ` differential of `extend C ⊗ extend D` followed
by `fwdNeg n`. Proved summand-by-summand via `mapBifunctor.hom_ext`; the `d₁` summands carry sign
`1` on both sides, and the `d₂` summands match through `negOnePow_neg_natCast`. -/
@[reassoc]
lemma fwdNeg_comm (n : ℕ) :
    fwdNeg C D (n + 1) ≫ (HomologicalComplex.tensorObj C D).d (n + 1) n =
      (HomologicalComplex.tensorObj (C.extend e) (D.extend e)).d (-(↑(n + 1) : ℤ)) (-(n : ℤ)) ≫
        fwdNeg C D n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : e.r a with _ | p
  · exact (isZero_tensorObj_left (C.isZero_extend_X' e a ha)).eq_of_src _ _
  rcases hb : e.r b with _ | q
  · exact (isZero_tensorObj_right (D.isZero_extend_X' e b hb)).eq_of_src _ _
  obtain rfl : a = -(p : ℤ) := by
    have := e.f_eq_of_r_eq_some ha
    simp only [ComplexShape.embeddingDownNat_f] at this; omega
  obtain rfl : b = -(q : ℤ) := by
    have := e.f_eq_of_r_eq_some hb
    simp only [ComplexShape.embeddingDownNat_f] at this; omega
  have hpq : p + q = n + 1 := by
    have h2 : (-(p : ℤ)) + (-(q : ℤ)) = -(↑(n + 1) : ℤ) := hab
    omega
  rw [← Category.assoc, ιZ_fwdNeg C D (n + 1) (-(p : ℤ)) (-(q : ℤ)) hab,
      phiFwd_some C D (n + 1) hab (r_negNat p) (r_negNat q) hpq, Category.assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  refine congr_arg₂ (· + ·) ?_ ?_
  · -- d₁ part (factor 1 differential)
    rcases p with _ | p
    · -- p = 0: both sides vanish (no `down ℕ` relation resp. zero extended differential)
      have h0 : (C.extend e).d 0 1 = 0 :=
        (C.isZero_extend_X e 1
          (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
      rw [mapBifunctor.d₁_eq_zero C D _ (ComplexShape.down ℕ) 0 q n
            (by intro h; rw [ComplexShape.down_Rel] at h; omega), comp_zero,
          show (-(↑(0 : ℕ)) : ℤ) = 0 by simp,
          mapBifunctor.d₁_eq (C.extend e) (D.extend e) _ (ComplexShape.up ℤ)
            (show (ComplexShape.up ℤ).Rel 0 1 by simp) (-(q : ℤ)) (-(n : ℤ))
            (by omega : (1 : ℤ) + (-(q : ℤ)) = -(n : ℤ))]
      simp [h0]
    · -- p = p' + 1
      have hpn : p + q = n := by omega
      rw [mapBifunctor.d₁_eq C D _ (ComplexShape.down ℕ)
            (show (ComplexShape.down ℕ).Rel (p + 1) p by rw [ComplexShape.down_Rel]) q n hpn,
          mapBifunctor.d₁_eq (C.extend e) (D.extend e) _ (ComplexShape.up ℤ)
            (show (ComplexShape.up ℤ).Rel (-(↑(p + 1) : ℤ)) (-(p : ℤ)) by
              rw [ComplexShape.up_Rel]; push_cast; ring) (-(q : ℤ)) (-(n : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          extend_d_eq C e (show e.f (p + 1) = -(↑(p + 1) : ℤ) by simp)
            (show e.f p = -(p : ℤ) by simp)]
      dsimp
      simp only [one_smul, Category.assoc]
      rw [ιZ_fwdNeg C D n (-(p : ℤ)) (-(q : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          phiFwd_some C D n _ (r_negNat p) (r_negNat q) hpn]
      simp only [Functor.map_comp, NatTrans.comp_app, curriedTensor_map_app,
        Category.assoc, MonoidalCategory.tensorHom_def, whisker_exchange_assoc,
        ← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
        MonoidalCategory.id_whiskerRight, Category.id_comp]
  · -- d₂ part (factor 2 differential)
    rcases q with _ | q
    · -- q = 0: both sides vanish
      have h0 : (D.extend e).d 0 1 = 0 :=
        (D.isZero_extend_X e 1
          (fun i => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
      rw [mapBifunctor.d₂_eq_zero C D _ (ComplexShape.down ℕ) p 0 n
            (by intro h; rw [ComplexShape.down_Rel] at h; omega), comp_zero,
          show (-(↑(0 : ℕ)) : ℤ) = 0 by simp,
          mapBifunctor.d₂_eq (C.extend e) (D.extend e) _ (ComplexShape.up ℤ) (-(p : ℤ))
            (show (ComplexShape.up ℤ).Rel 0 1 by simp) (-(n : ℤ))
            (by omega : (-(p : ℤ)) + (1 : ℤ) = -(n : ℤ))]
      simp [h0]
    · -- q = q' + 1
      have hpn : p + q = n := by omega
      rw [mapBifunctor.d₂_eq C D _ (ComplexShape.down ℕ) p
            (show (ComplexShape.down ℕ).Rel (q + 1) q by rw [ComplexShape.down_Rel]) n hpn,
          mapBifunctor.d₂_eq (C.extend e) (D.extend e) _ (ComplexShape.up ℤ) (-(p : ℤ))
            (show (ComplexShape.up ℤ).Rel (-(↑(q + 1) : ℤ)) (-(q : ℤ)) by
              rw [ComplexShape.up_Rel]; push_cast; ring) (-(n : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          extend_d_eq D e (show e.f (q + 1) = -(↑(q + 1) : ℤ) by simp)
            (show e.f q = -(q : ℤ) by simp)]
      dsimp
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
      rw [ιZ_fwdNeg C D n (-(p : ℤ)) (-(q : ℤ))
            (by omega : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ)),
          phiFwd_some C D n _ (r_negNat p) (r_negNat q) hpn, negOnePow_neg_natCast]
      congr 1
      simp only [curriedTensor_obj_map, Category.assoc,
        MonoidalCategory.tensorHom_def, ← whisker_exchange_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Milestone (c): the complex isomorphism.** Assemble the degreewise isos `tensorExtendXIso`
into an isomorphism of `ℤ`-cochain complexes `extend C ⊗ extend D ≅ extend (C ⊗ D)`, using
`fwdNeg_comm` for differential compatibility on the nonzero degrees `j = -n` and vanishing of the
target on positive degrees. -/
noncomputable def tensorObjExtendIso :
    HomologicalComplex.tensorObj (C.extend e) (D.extend e) ≅
      (HomologicalComplex.tensorObj C D).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun j' => tensorExtendXIso C D j') (by
    intro i j hij
    by_cases hj : 0 < j
    · exact (HomologicalComplex.isZero_extend_X _ e j
        (fun m => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
    · rw [not_lt] at hj
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
      obtain rfl : i = -(↑(n + 1) : ℤ) := by
        have : i + 1 = -(n : ℤ) := hij
        push_cast; omega
      rw [HomologicalComplex.extend_d_eq (HomologicalComplex.tensorObj C D) e
            (ef_eq_neg (n + 1)) (ef_eq_neg n),
          ← Category.assoc, tensorExtendXIso_hom_extendXIso C D (n + 1),
          fwdNeg_comm_assoc C D n]
      congr 1
      rw [← tensorExtendXIso_hom_extendXIso C D n, Category.assoc, Iso.hom_inv_id,
        Category.comp_id])

/-!
## Milestone (d): naturality of the comparison

`tensorObjExtendIso` is natural in `(C, D)`. Degreewise it is a `mapBifunctorDesc` over the
`ιTensorObj` injections, and both those injections (`ι_mapBifunctorMap`) and the `extendXIso`
transports (`extendMap_f`) are natural, so the comparison intertwines
`tensorHom (extendMap f) (extendMap g)` with `extendMap (tensorHom f g)`.

`fwdNeg_naturality` is the degreewise square, `tensorObjExtendIso_hom_naturality` the
complex-level one (with `_left`/`_right` giving the one-variable specialisations), and
`tensorObjExtendNatIso` packages the comparison as an isomorphism of the two bifunctors
`(C, D) ↦ extend C ⊗ extend D` and `(C, D) ↦ extend (C ⊗ D)`.
-/

section Naturality

variable {C₁ C₂ D₁ D₂ : ChainComplex (ModuleCat.{u} k) ℕ}

/-- **Naturality of the degree `-n` forward map.** The coproduct forward maps `fwdNeg` intertwine
`tensorHom (extendMap f) (extendMap g)` with `tensorHom f g`. Proved summand-by-summand: the
summands outside the image of the embedding have zero source, and on an `(a, b) = (-p, -q)`
summand both sides reduce to
`((extendXIso C₁).hom ≫ f.f p) ⊗ₘ ((extendXIso D₁).hom ≫ g.f q)` followed by the `ℕ`-side
injection `ιN C₂ D₂ p q n`. -/
lemma fwdNeg_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) (n : ℕ) :
    (HomologicalComplex.tensorHom (HomologicalComplex.extendMap f e)
          (HomologicalComplex.extendMap g e)).f (-(n : ℤ)) ≫ fwdNeg C₂ D₂ n =
      fwdNeg C₁ D₁ n ≫ (HomologicalComplex.tensorHom f g).f n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rcases ha : e.r a with _ | p
  · exact (isZero_tensorObj_left (C₁.isZero_extend_X' e a ha)).eq_of_src _ _
  rcases hb : e.r b with _ | q
  · exact (isZero_tensorObj_right (D₁.isZero_extend_X' e b hb)).eq_of_src _ _
  obtain rfl : a = -(p : ℤ) := by have := e.f_eq_of_r_eq_some ha; simpa using this.symm
  obtain rfl : b = -(q : ℤ) := by have := e.f_eq_of_r_eq_some hb; simpa using this.symm
  have hab' : (-(p : ℤ)) + (-(q : ℤ)) = -(n : ℤ) := hab
  have hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = n := by
    have : p + q = n := by omega
    simpa using this
  rw [show HomologicalComplex.ιMapBifunctor (C₁.extend e) (D₁.extend e)
        (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) hab = ιZ C₁ D₁ _ _ _ hab from rfl]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, ιZ_fwdNeg,
    phiFwd_some C₂ D₂ n _ (r_negNat p) (r_negNat q) hpq,
    ← Category.assoc (ιZ C₁ D₁ _ _ _ hab), ιZ_fwdNeg,
    phiFwd_some C₁ D₁ n _ (r_negNat p) (r_negNat q) hpq,
    Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.extendMap_f f e (ef_eq_neg p),
    HomologicalComplex.extendMap_f g e (ef_eq_neg q)]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, Functor.map_comp, NatTrans.comp_app,
    Category.assoc, ← MonoidalCategory.tensorHom_id, ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
    Iso.inv_hom_id]

-- The reassociated form of `tensorExtendXIso_hom_extendXIso`, used to strip the extend
-- transport off the middle of a composite in `tensorObjExtendIso_hom_naturality`.
attribute [reassoc] tensorExtendXIso_hom_extendXIso

/-- **Milestone (d): naturality of the complex isomorphism.** The tensor/extend comparison
`extend C ⊗ extend D ≅ extend (C ⊗ D)` commutes with the maps induced by arbitrary chain maps
`f : C₁ ⟶ C₂` and `g : D₁ ⟶ D₂`. Degreewise this is `fwdNeg_naturality`; the degrees outside the
image of the embedding are handled by vanishing of the target. -/
theorem tensorObjExtendIso_hom_naturality (f : C₁ ⟶ C₂) (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f e)
          (HomologicalComplex.extendMap g e) ≫ (tensorObjExtendIso C₂ D₂).hom =
      (tensorObjExtendIso C₁ D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f g) e := by
  ext j' : 1
  by_cases hj : 0 < j'
  · exact (HomologicalComplex.isZero_extend_X (HomologicalComplex.tensorObj C₂ D₂) e j'
      (fun m => by simp only [ComplexShape.embeddingDownNat_f]; omega)).eq_of_tgt _ _
  · rw [not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j' = -(n : ℤ) := ⟨(-j').toNat, by omega⟩
    rw [← cancel_mono (HomologicalComplex.extendXIso
      (HomologicalComplex.tensorObj C₂ D₂) e (ef_eq_neg n)).hom,
      HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
      show (tensorObjExtendIso C₂ D₂).hom.f (-(n : ℤ)) = (tensorExtendXIso C₂ D₂ (-(n : ℤ))).hom
        from rfl,
      show (tensorObjExtendIso C₁ D₁).hom.f (-(n : ℤ)) = (tensorExtendXIso C₁ D₁ (-(n : ℤ))).hom
        from rfl,
      tensorExtendXIso_hom_extendXIso,
      HomologicalComplex.extendMap_f (HomologicalComplex.tensorHom f g) e (ef_eq_neg n),
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      tensorExtendXIso_hom_extendXIso_assoc]
    exact fwdNeg_naturality f g n

/-- Naturality in the first argument. -/
theorem tensorObjExtendIso_hom_naturality_left (f : C₁ ⟶ C₂)
    (D : ChainComplex (ModuleCat.{u} k) ℕ) :
    HomologicalComplex.tensorHom (HomologicalComplex.extendMap f e) (𝟙 (D.extend e)) ≫
        (tensorObjExtendIso C₂ D).hom =
      (tensorObjExtendIso C₁ D).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom f (𝟙 D)) e := by
  simpa using tensorObjExtendIso_hom_naturality f (𝟙 D)

/-- Naturality in the second argument. -/
theorem tensorObjExtendIso_hom_naturality_right (C : ChainComplex (ModuleCat.{u} k) ℕ)
    (g : D₁ ⟶ D₂) :
    HomologicalComplex.tensorHom (𝟙 (C.extend e)) (HomologicalComplex.extendMap g e) ≫
        (tensorObjExtendIso C D₂).hom =
      (tensorObjExtendIso C D₁).hom ≫
        HomologicalComplex.extendMap (HomologicalComplex.tensorHom (𝟙 C) g) e := by
  simpa using tensorObjExtendIso_hom_naturality (𝟙 C) g

end Naturality

section Bifunctor

/-- The tensor bifunctor on `ℤ`-cochain complexes, as `map₂HomologicalComplex`. Its object map is
`HomologicalComplex.tensorObj` and its morphism maps are `HomologicalComplex.tensorHom`. -/
noncomputable abbrev tensorBifunctorZ :
    CochainComplex (ModuleCat.{u} k) ℤ ⥤ CochainComplex (ModuleCat.{u} k) ℤ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (curriedTensor (ModuleCat.{u} k)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The tensor bifunctor on `ℕ`-chain complexes. -/
noncomputable abbrev tensorBifunctorN :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ ⥤
      ChainComplex (ModuleCat.{u} k) ℕ :=
  (curriedTensor (ModuleCat.{u} k)).map₂HomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)

/-- `extend` along `embeddingDownNat` as a functor `ChainComplex ℕ ⥤ CochainComplex ℤ`. -/
noncomputable abbrev extFunctor :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  e.extendFunctor (ModuleCat.{u} k)

/-- The bifunctor `(C, D) ↦ extend C ⊗ extend D`. -/
noncomputable abbrev tensorExtendSrc :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  (extFunctor ⋙ tensorBifunctorZ) ⋙
    (CategoryTheory.Functor.whiskeringLeft (ChainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj extFunctor

/-- The bifunctor `(C, D) ↦ extend (C ⊗ D)`. -/
noncomputable abbrev tensorExtendTgt :
    ChainComplex (ModuleCat.{u} k) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ ⥤
      CochainComplex (ModuleCat.{u} k) ℤ :=
  tensorBifunctorN ⋙
    (CategoryTheory.Functor.whiskeringRight (ChainComplex (ModuleCat.{u} k) ℕ)
      (ChainComplex (ModuleCat.{u} k) ℕ)
      (CochainComplex (ModuleCat.{u} k) ℤ)).obj extFunctor

/-- **The tensor/extend comparison as an isomorphism of bifunctors.** Assembles
`tensorObjExtendIso` over all `(C, D)` into a `NatIso` between `tensorExtendSrc` and
`tensorExtendTgt`; the objectwise isos are recovered as `(tensorObjExtendNatIso.app C).app D`.
Both naturality squares are `tensorObjExtendIso_hom_naturality` with one argument an identity. -/
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
lemma tensorObjExtendNatIso_app_app (C D : ChainComplex (ModuleCat.{u} k) ℕ) :
    (tensorObjExtendNatIso.app C).app D = tensorObjExtendIso C D :=
  rfl

end Bifunctor

end TensorExtend

section CoproductSupport

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {J I : Type*} {F : J → C} {G : I → C} [HasCoproduct F] [HasCoproduct G]

open Classical in
/-- Forward map for `sigmaIsoOfInjOfIsZeroCompl`: on a summand `F j` with `j = ι a` in the image
of `ι` it is `(iso a).hom` into the `a`-summand of `∐ G`; off the image `F j` is a zero object,
so the map is `0`. -/
noncomputable def sigmaSupportHom (ι : I → J) (iso : ∀ a, F (ι a) ≅ G a) : (∐ F) ⟶ (∐ G) :=
  Sigma.desc fun j =>
    if h : ∃ a, ι a = j then
      eqToHom (congrArg F h.choose_spec.symm) ≫ (iso h.choose).hom ≫ Sigma.ι G h.choose
    else 0

/-- Inverse map: send the `a`-summand `G a` back to the `ι a`-summand of `∐ F` via `(iso a).inv`. -/
noncomputable def sigmaSupportInv (ι : I → J) (iso : ∀ a, F (ι a) ≅ G a) : (∐ G) ⟶ (∐ F) :=
  Sigma.desc fun a => (iso a).inv ≫ Sigma.ι F (ι a)

omit [HasZeroMorphisms C] [HasZeroObject C] in
@[reassoc]
lemma ι_sigmaSupportInv (ι : I → J) (iso : ∀ a, F (ι a) ≅ G a) (a : I) :
    Sigma.ι G a ≫ sigmaSupportInv ι iso = (iso a).inv ≫ Sigma.ι F (ι a) := by
  rw [sigmaSupportInv, Sigma.ι_desc]

omit [HasZeroObject C] in
@[reassoc]
lemma ι_sigmaSupportHom (ι : I → J) (hι : Function.Injective ι) (iso : ∀ a, F (ι a) ≅ G a) (a : I) :
    Sigma.ι F (ι a) ≫ sigmaSupportHom ι iso = (iso a).hom ≫ Sigma.ι G a := by
  rw [sigmaSupportHom, Sigma.ι_desc, dif_pos ⟨a, rfl⟩]
  suffices H : ∀ (c : I) (hc : ι c = ι a),
      eqToHom (congrArg F hc.symm) ≫ (iso c).hom ≫ Sigma.ι G c = (iso a).hom ≫ Sigma.ι G a by
    exact H _ (Exists.choose_spec (⟨a, rfl⟩ : ∃ a', ι a' = ι a))
  intro c hc
  obtain rfl : c = a := hι hc
  simp

/-- **Coproduct supported on the image of an injection.** If `F j` is a zero object for every `j`
outside the image of an injective `ι : I → J`, and `F (ι a) ≅ G a` for each `a`, then
`∐ F ≅ ∐ G`. The extra summands of `∐ F` contribute nothing. -/
noncomputable def sigmaIsoOfInjOfIsZeroCompl (ι : I → J) (hι : Function.Injective ι)
    (iso : ∀ a, F (ι a) ≅ G a) (hz : ∀ j, (∀ a, ι a ≠ j) → IsZero (F j)) :
    (∐ F) ≅ (∐ G) where
  hom := sigmaSupportHom ι iso
  inv := sigmaSupportInv ι iso
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Category.comp_id]
    by_cases h : ∃ a, ι a = j
    · obtain ⟨a, rfl⟩ := h
      rw [ι_sigmaSupportHom_assoc ι hι iso, ι_sigmaSupportInv, Iso.hom_inv_id_assoc]
    · have hj : ∀ a, ι a ≠ j := fun a ha => h ⟨a, ha⟩
      rw [(hz j hj).eq_of_src (Sigma.ι F j) 0, zero_comp]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [Category.comp_id, ι_sigmaSupportInv_assoc, ι_sigmaSupportHom ι hι iso, Iso.inv_hom_id_assoc]

end CoproductSupport

/-- **Tensor ∘ extend compatibility.** The `ℤ`-tensor of the extensions is the extension
of the `ℕ`-tensor:
`extend e C ⊗ extend e D ≅ extend e (C ⊗ D)`, `e = embeddingDownNat`.

Degreewise both sides are `⨁_{p+q=n} C_p ⊗ D_q` at `-n` and zero at positive degrees; the content
is matching the `ιTensorObj` injections and the Koszul-signed total differential. Universe-general
and independent of Chapter 7. Constructed via `TensorExtend.tensorObjExtendIso` (milestones
(a)–(c)). -/
theorem nonempty_tensorObj_extend_iso (C D : ChainComplex (ModuleCat.{u} k) ℕ) :
    Nonempty (HomologicalComplex.tensorObj (C.extend ComplexShape.embeddingDownNat)
        (D.extend ComplexShape.embeddingDownNat) ≅
      (HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingDownNat) :=
  ⟨TensorExtend.tensorObjExtendIso C D⟩

/-- **Künneth for `ℕ`-indexed chain complexes**, as an honest isomorphism. For chain complexes
`C, D` of `k`-vector spaces indexed over `ℕ`,
`Hᵢ(C ⊗ D) ≅ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)`.

Reindexes Chapter 7's `Etingof.Problem7_8_7_iv` along `embeddingDownNat`; see the module
docstring for the derivation. Consumed by the Problem 8.2.8 `Tor`/`Ext` construction.

## Naturality of the four steps

The composite is `α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄`, and **every one of the four steps is natural in
`(C, D)`**; nothing here is a non-natural choice, and no step uses `Classical.choice` to
extract an isomorphism from a `Nonempty`. What differs is how much of that naturality is
currently *formalized*:

* `α₁`, `α₄` (the `extend` homology comparison): naturality is proved, as
  `homology_extend_iso_hom_naturality` (a restatement of Mathlib's
  `extendHomologyIso_hom_naturality`).
* `α₃` (Chapter 7 Künneth): naturality is proved, as `Etingof.kunnethNatIso` — the underlying
  map is the choice-free cross product `Etingof.kunnethMap`.
* `α₂` (the tensor/extend compatibility): naturality is proved by
  `TensorExtend.tensorObjExtendIso_hom_naturality` and packaged by
  `TensorExtend.tensorObjExtendNatIso`.

`KunnethNatBifunctor.lean` composes these four squares into
`kunnethChainComplexNatNatIso`; its component theorem recovers this isomorphism. -/
noncomputable def kunnethChainComplexNatIso (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2 := by
  let e := ComplexShape.embeddingDownNat
  -- Step 1: `Hᵢ(C ⊗ D) ≅ H_{-i}(extend (C ⊗ D))`.
  let α₁ : (HomologicalComplex.tensorObj C D).homology i ≅
      ((HomologicalComplex.tensorObj C D).extend e).homology (-(i : ℤ)) :=
    (homology_extend_iso (HomologicalComplex.tensorObj C D) i).symm
  -- Step 2: apply `H_{-i}` to the compatibility iso `extend (C ⊗ D) ≅ extend C ⊗ extend D`.
  let φ : (HomologicalComplex.tensorObj C D).extend e ≅
      HomologicalComplex.tensorObj (C.extend e) (D.extend e) :=
    (TensorExtend.tensorObjExtendIso C D).symm
  let α₂ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℤ)
    (-(i : ℤ))).mapIso φ
  -- Step 3: Chapter 7's universe-general Künneth at degree `-i`, as the honest isomorphism
  -- inverse to the natural cross product `kunnethMap`.
  let α₃ := Problem7_8_7_iv (C.extend e) (D.extend e) (-(i : ℤ))
  -- Step 4: reindex the `ℤ`-coproduct `⨁_{a+b=-i}` onto the `ℕ`-antidiagonal `⨁_{p+q=i}`;
  -- the summands with `a > 0` or `b > 0` vanish by `homology_extend_isZero`.
  let ι : {p : ℕ × ℕ // p.1 + p.2 = i} → {p : ℤ × ℤ // p.1 + p.2 = -(i : ℤ)} :=
    fun p => ⟨(-(p.1.1 : ℤ), -(p.1.2 : ℤ)), by
      have h2 : (p.1.1 : ℤ) + (p.1.2 : ℤ) = (i : ℤ) := by exact_mod_cast p.2
      change -(p.1.1 : ℤ) + -(p.1.2 : ℤ) = -(i : ℤ); omega⟩
  have hι : Function.Injective ι := by
    intro p p' hpp
    apply Subtype.ext
    have hv : (ι p).1 = (ι p').1 := congrArg Subtype.val hpp
    have h1 : (p.1.1 : ℤ) = (p'.1.1 : ℤ) := neg_injective (congrArg Prod.fst hv)
    have h2 : (p.1.2 : ℤ) = (p'.1.2 : ℤ) := neg_injective (congrArg Prod.snd hv)
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  let α₄ : (∐ fun (p : {p : ℤ × ℤ // p.1 + p.2 = -(i : ℤ)}) =>
        (C.extend e).homology p.1.1 ⊗ (D.extend e).homology p.1.2) ≅
      (∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) => C.homology p.1.1 ⊗ D.homology p.1.2) :=
    sigmaIsoOfInjOfIsZeroCompl ι hι
      (fun a => tensorIso (homology_extend_iso C a.1.1) (homology_extend_iso D a.1.2))
      (by
        rintro ⟨⟨a, b⟩, hab⟩ hj
        by_cases ha : 0 < a
        · exact TensorExtend.isZero_tensorObj_left (homology_extend_isZero C a ha)
        by_cases hb : 0 < b
        · exact TensorExtend.isZero_tensorObj_right (homology_extend_isZero D b hb)
        rw [not_lt] at ha hb
        exfalso
        have hp : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
        have hq : ((-b).toNat : ℤ) = -b := Int.toNat_of_nonneg (by omega)
        have hpq : (-a).toNat + (-b).toNat = i := by
          have : ((-a).toNat : ℤ) + ((-b).toNat : ℤ) = (i : ℤ) := by rw [hp, hq]; omega
          exact_mod_cast this
        refine hj ⟨((-a).toNat, (-b).toNat), hpq⟩ (Subtype.ext ?_)
        change (-(((-a).toNat : ℕ) : ℤ), -(((-b).toNat : ℕ) : ℤ)) = (a, b)
        rw [Prod.mk.injEq]
        exact ⟨by rw [hp]; ring, by rw [hq]; ring⟩)
  exact α₁ ≪≫ α₂ ≪≫ α₃ ≪≫ α₄

/-- **Künneth for `ℕ`-indexed chain complexes**, `Nonempty` form. A one-line corollary of
`kunnethChainComplexNatIso`, kept so that existing consumers phrased in terms of `Nonempty`
keep working; new consumers should use the `Iso` directly. -/
theorem kunnethChainComplexNat (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    Nonempty ((HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2) :=
  ⟨kunnethChainComplexNatIso C D i⟩

end Etingof
