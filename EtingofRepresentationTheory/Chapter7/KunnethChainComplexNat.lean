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
