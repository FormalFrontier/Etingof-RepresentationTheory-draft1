import Mathlib

/-!
# Künneth for `ℕ`-indexed chain complexes: the `ℕ`/`ℤ` reindex bridge

Chapter 7's Künneth formula (`Etingof.Problem7_8_7_iv`) is stated for cohomologically indexed
`CochainComplex (ModuleCat k) ℤ`. The `Tor`/`Ext` assembly of Problem 8.2.8, however, works with
its own complexes `P• ⊗_A N`, which are homologically indexed `ChainComplex (ModuleCat.{u} k) ℕ`
(`= HomologicalComplex _ (ComplexShape.down ℕ)`). This file provides the bridge: a Künneth
isomorphism for `ℕ`-indexed chain complexes, obtained by **reindexing** the `ℤ` result rather than
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

## The crux: tensor ∘ extend compatibility

The remaining gap — with no direct Mathlib support — is the compatibility of `extend` with the
monoidal (tensor) structure:

`extend e C ⊗ extend e D ≅ extend e (C ⊗ D)`  (in the `up ℤ` monoidal structure).

Degreewise this reads: `(extend C ⊗ extend D)_{j'} = ⨁_{a+b=j'} (extend C)_a ⊗ (extend D)_b`.
Since `extend C` is supported on `ℤ≤0`, the only nonzero summands have `a = -p`, `b = -q` with
`p, q : ℕ`; when `j' = -n` these are exactly the `p + q = n` summands, matching
`(C ⊗ D)_n = ⨁_{p+q=n} C_p ⊗ D_q = (extend (C ⊗ D))_{-n}`. Both sides vanish for `j' > 0`. The
categorical work is to assemble this degreewise identification into an isomorphism of complexes,
matching the `ιTensorObj` injections and the Koszul-signed total differential (`d₁` and `d₂`
summands). This is stated below as `nonempty_tensorObj_extend_iso` (Prop-valued, `sorry`).

Note `extend C ⊗ extend D` is itself supported on `ℤ≤0`, i.e. on the image of the embedding, so
this iso can equivalently be read as "the `ℤ`-tensor of the extends is the extension of the
`ℕ`-tensor".

## The payoff

`Hᵢ(C ⊗ D)` (`ℕ`) `≅ H_{-i}(extend (C ⊗ D))` `≅ H_{-i}(extend C ⊗ extend D)` (crux)
`≅ ⨁_{a+b=-i} H_a(extend C) ⊗ H_b(extend D)` (Chapter 7 Künneth at universe `u`, degree `-i`)
`≅ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)` (reindex `a = -p`, `b = -q`; the `a > 0` / `b > 0` summands are
zero by `homology_extend_isZero`).

The final identification uses the **universe-general** `Problem7_8_7_iv` (universe half of #6666,
PR https://github.com/.../pull/6673). The reindex of the coproduct is not a bare index bijection:
the `ℤ`-side sum `⨁_{a+b=-i}` ranges over all of `ℤ × ℤ`, and the extra summands vanish only via
`homology_extend_isZero`.

The main deliverable `kunnethChainComplexNat` is stated below (Prop-valued, `sorry`), pinning the
API that the Problem 8.2.8 assembler (#6657) consumes.
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
of the crux `nonempty_tensorObj_extend_iso`. The nonzero degrees are `j' = -n`, where both sides
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

end TensorExtend

/-- **Crux (tensor ∘ extend compatibility).** The `ℤ`-tensor of the extensions is the extension
of the `ℕ`-tensor:
`extend e C ⊗ extend e D ≅ extend e (C ⊗ D)`, `e = embeddingDownNat`.

Degreewise both sides are `⨁_{p+q=n} C_p ⊗ D_q` at `-n` and zero at positive degrees; the content
is matching the `ιTensorObj` injections and the Koszul-signed total differential. Universe-general
and independent of Chapter 7. Stated Prop-valued (`Nonempty`) so the missing construction is a
`sorry` rather than a sorried definition. -/
theorem nonempty_tensorObj_extend_iso (C D : ChainComplex (ModuleCat.{u} k) ℕ) :
    Nonempty (HomologicalComplex.tensorObj (C.extend ComplexShape.embeddingDownNat)
        (D.extend ComplexShape.embeddingDownNat) ≅
      (HomologicalComplex.tensorObj C D).extend ComplexShape.embeddingDownNat) :=
  ⟨sorry⟩

/-- **Künneth for `ℕ`-indexed chain complexes.** For chain complexes `C, D` of `k`-vector spaces
indexed over `ℕ`, the homology of the tensor product decomposes as a direct sum:
`Hᵢ(C ⊗ D) ≅ ⨁_{p+q=i} H_p(C) ⊗ H_q(D)`.

Reindexes Chapter 7's `Problem7_8_7_iv` along `embeddingDownNat`; see the module docstring for the
route. Consumed by the Problem 8.2.8 `Tor`/`Ext` assembler (#6657). -/
theorem kunnethChainComplexNat (C D : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    Nonempty ((HomologicalComplex.tensorObj C D).homology i ≅
      ∐ fun (p : {p : ℕ × ℕ // p.1 + p.2 = i}) =>
        C.homology p.1.1 ⊗ D.homology p.1.2) :=
  ⟨sorry⟩

end Etingof
