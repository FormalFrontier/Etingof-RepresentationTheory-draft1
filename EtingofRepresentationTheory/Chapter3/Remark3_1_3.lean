import Mathlib.LinearAlgebra.TensorProduct.Basic
import EtingofRepresentationTheory.Chapter2.Corollary2_3_10

/-!
# Remark 3.1.3: Canonical decomposition of a semisimple representation

By Schur's lemma, a semisimple finite dimensional representation `V` of `A` is canonically
identified with `⨁_X Hom_A(X, V) ⊗ X`, where `X` runs over the irreducible representations
of `A`. The identification is the natural map

`f : ⨁_X Hom_A(X, V) ⊗ X → V`, `g ⊗ x ↦ g(x)`.

This file constructs the canonical evaluation map `g ⊗ x ↦ g(x)` (the building block of
`f`, for each individual irreducible `X`) as genuine data — `Etingof.evalTensor` — and
proves the heart of the remark: when `V` is irreducible (the case the book reduces to via
"one may assume that `V` is irreducible"), the evaluation map

`Hom_A(V, V) ⊗_k V → V`

is a `k`-linear isomorphism. Indeed `Hom_A(V, V) = k · id` by Schur over the algebraically
closed field `k` (Corollary 2.3.10), so the map has the explicit two-sided inverse
`v ↦ id ⊗ v`.

The assembly of the per-`X` maps into the full direct-sum isomorphism over all irreducibles
remains; see the surrounding development of the isotypic decomposition.
-/

open scoped TensorProduct

namespace Etingof

variable (k : Type*) (A : Type*) (X : Type*) (V : Type*)
  [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The `k`-bilinear evaluation pairing `Hom_A(X, V) × X → V`, `(g, x) ↦ g(x)`, packaged as
a `k`-linear map `Hom_A(X, V) →ₗ[k] (X →ₗ[k] V)` sending an `A`-linear `g` to its underlying
`k`-linear map. -/
def evalBilinear : (X →ₗ[A] V) →ₗ[k] (X →ₗ[k] V) where
  toFun g := g.restrictScalars k
  map_add' g g' := LinearMap.restrictScalars_add g g'
  map_smul' c g := LinearMap.restrictScalars_smul c g

/-- The canonical evaluation map `Hom_A(X, V) ⊗_k X → V`, `g ⊗ x ↦ g(x)`. This is the
building block of the natural map `f` of Remark 3.1.3. -/
noncomputable def evalTensor : (X →ₗ[A] V) ⊗[k] X →ₗ[k] V :=
  TensorProduct.lift (evalBilinear k A X V)

@[simp]
theorem evalTensor_tmul (g : X →ₗ[A] V) (x : X) :
    evalTensor k A X V (g ⊗ₜ[k] x) = g x := rfl

end Etingof

namespace Etingof

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [IsSimpleModule A V] [FiniteDimensional k V]

/-- For an irreducible finite dimensional representation `V` over an algebraically closed
field, the canonical evaluation map `Hom_A(V, V) ⊗_k V → V`, `g ⊗ x ↦ g(x)`, is a `k`-linear
isomorphism. This is the irreducible base case of Remark 3.1.3 (the case to which the book
reduces the general statement). The inverse is `v ↦ id ⊗ v`. -/
noncomputable def evalTensorEquivOfIsSimple :
    (V →ₗ[A] V) ⊗[k] V ≃ₗ[k] V :=
  LinearEquiv.ofLinear
    (evalTensor k A V V)
    (TensorProduct.mk k (V →ₗ[A] V) V LinearMap.id)
    (by
      ext v
      simp)
    (by
      refine TensorProduct.ext' fun g x => ?_
      -- Goal: id ⊗ₜ (evalTensor (g ⊗ₜ x)) = g ⊗ₜ x
      obtain ⟨c, hc⟩ := Etingof.Corollary_2_3_10 (k := k) g
      have hg : g = c • LinearMap.id := by
        ext v; rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hc v
      simp only [LinearMap.coe_comp, Function.comp_apply, evalTensor_tmul,
        TensorProduct.mk_apply, LinearMap.id_coe, id_eq]
      rw [hc x, ← TensorProduct.smul_tmul, ← hg])

@[simp]
theorem evalTensorEquivOfIsSimple_tmul (g : V →ₗ[A] V) (x : V) :
    evalTensorEquivOfIsSimple k A V (g ⊗ₜ[k] x) = g x := rfl

end Etingof
