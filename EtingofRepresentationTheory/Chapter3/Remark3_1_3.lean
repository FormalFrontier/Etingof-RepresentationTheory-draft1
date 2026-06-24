import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.SimpleModule.Isotypic
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

namespace Etingof

section PerX

variable (k : Type*) (A : Type*) (X : Type*) (V : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [IsSimpleModule A X] [FiniteDimensional k X]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V]

/-- The per-irreducible evaluation map `evalTensor : Hom_A(X, V) ⊗_k X → V`, `g ⊗ x ↦ g(x)`, is
injective when `X` is a finite dimensional irreducible over an algebraically closed field `k` and
`V` is finite dimensional.

Choosing a `k`-basis `bⱼ` of `Hom_A(X, V)`, the assembled `A`-linear map
`G : (Fin n →₀ X) → V`, `y ↦ ∑ⱼ bⱼ(yⱼ)`, factors the evaluation map through the basis-induced
surjection `F : (Fin n →₀ X) → Hom_A(X, V) ⊗_k X`, `single j x ↦ bⱼ ⊗ x`. So it suffices that
`G` is injective. A nonzero kernel element of `G` contains a simple submodule `S ≅ X`; the
component maps `S → X` are scalars `cⱼ` (Corollary 2.3.10), and `∑ cⱼ bⱼ = 0` forces all `cⱼ = 0`
by linear independence of the basis, which collapses `S` to `0`, contradicting simplicity. -/
theorem evalTensor_injective : Function.Injective (evalTensor k A X V) := by
  haveI : Module.Finite k (X →ₗ[A] V) :=
    Module.Finite.of_injective (evalBilinear k A X V) (fun g g' h =>
      LinearMap.ext fun x => LinearMap.congr_fun h x)
  set n := Module.finrank k (X →ₗ[A] V) with hn
  set b : Module.Basis (Fin n) k (X →ₗ[A] V) := Module.finBasis k (X →ₗ[A] V) with hb
  -- the assembled A-linear map G : (Fin n →₀ X) → V, y ↦ ∑ⱼ bⱼ(yⱼ)
  set G : (Fin n →₀ X) →ₗ[A] V := ∑ j, (b j).comp (Finsupp.lapply j) with hG_def
  -- the basis-induced k-linear map F : (Fin n →₀ X) → Hom ⊗ X, single j x ↦ bⱼ ⊗ x
  set F : (Fin n →₀ X) →ₗ[k] (X →ₗ[A] V) ⊗[k] X :=
    ∑ j, (TensorProduct.mk k (X →ₗ[A] V) X (b j)).comp (Finsupp.lapply j) with hF_def
  have hFsingle : ∀ (j : Fin n) (x : X), F (Finsupp.single j x) = b j ⊗ₜ[k] x := by
    intro j x
    simp only [hF_def, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
      Finsupp.lapply_apply, TensorProduct.mk_apply]
    rw [Finset.sum_eq_single j
      (fun l _ hl => by rw [Finsupp.single_eq_of_ne hl, TensorProduct.tmul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Finsupp.single_eq_same]
  have hGF : ∀ y : Fin n →₀ X, evalTensor k A X V (F y) = G y := by
    intro y
    simp only [hF_def, hG_def, LinearMap.coe_sum, Finset.sum_apply, map_sum,
      LinearMap.comp_apply, Finsupp.lapply_apply, TensorProduct.mk_apply, evalTensor_tmul]
  have hFsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul g x =>
        rw [← b.sum_repr g, TensorProduct.sum_tmul]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [← TensorProduct.smul_tmul']
        exact Submodule.smul_mem _ _ ⟨Finsupp.single j x, hFsingle j x⟩
    | add p q hp hq => exact add_mem hp hq
  -- the heart: G is injective
  have hG : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot]
    haveI : IsSemisimpleModule A (Fin n →₀ X) := inferInstance
    haveI : IsSemisimpleModule A (LinearMap.ker G) := inferInstance
    rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (LinearMap.ker G) with
      hbot | ⟨S, hSle, hSsimple⟩
    · exact hbot
    · exfalso
      haveI := hSsimple
      haveI : Nontrivial S := hSsimple.nontrivial
      have hincl_inj : Function.Injective S.subtype := S.subtype_injective
      -- some projection S → X is nonzero
      have hex : ∃ j, ((Finsupp.lapply j).comp S.subtype : S →ₗ[A] X) ≠ 0 := by
        by_contra hall
        push_neg at hall
        obtain ⟨s, hs⟩ := exists_ne (0 : S)
        apply hs
        apply hincl_inj
        rw [map_zero]
        ext j
        have h2 : ((Finsupp.lapply j).comp S.subtype) s = 0 := by rw [hall j]; rfl
        simpa [Finsupp.lapply_apply] using h2
      obtain ⟨j₀, hj₀⟩ := hex
      have hbij : Function.Bijective ((Finsupp.lapply j₀).comp S.subtype) :=
        ((Finsupp.lapply j₀).comp S.subtype).bijective_of_ne_zero hj₀
      set e : S ≃ₗ[A] X := LinearEquiv.ofBijective _ hbij with he
      -- component maps S → X are scalars
      have hc : ∀ l : Fin n, ∃ c : k, ∀ x : X,
          (S.subtype (e.symm x)) l = c • x := by
        intro l
        obtain ⟨c, hcl⟩ := Etingof.Corollary_2_3_10 (k := k)
          (((Finsupp.lapply l).comp S.subtype).comp e.symm.toLinearMap)
        refine ⟨c, fun x => ?_⟩
        have := hcl x
        simpa [Finsupp.lapply_apply] using this
      choose c hc using hc
      -- ∑ cₗ bₗ = 0
      have hsum0 : (∑ l, c l • b l) = 0 := by
        ext x
        rw [LinearMap.sum_apply, LinearMap.zero_apply]
        have hGz : G (S.subtype (e.symm x)) = 0 :=
          LinearMap.mem_ker.mp (hSle (Submodule.coe_mem (e.symm x)))
        have hGexp : G (S.subtype (e.symm x)) = ∑ l, b l ((S.subtype (e.symm x)) l) := by
          simp only [hG_def, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
            Finsupp.lapply_apply]
        rw [hGz] at hGexp
        rw [Finset.sum_congr rfl (fun l _ => ?_), ← hGexp]
        rw [LinearMap.smul_apply, ← (b l).map_smul_of_tower (c l) x, hc l x]
      have hc0 : ∀ l, c l = 0 :=
        Fintype.linearIndependent_iff.mp b.linearIndependent c hsum0
      haveI : Nontrivial X := IsSimpleModule.nontrivial (R := A) (M := X)
      obtain ⟨x₀, hx₀⟩ := exists_ne (0 : X)
      apply hx₀
      have h1 : (S.subtype (e.symm x₀)) j₀ = x₀ := e.apply_symm_apply x₀
      rw [hc j₀ x₀, hc0 j₀, zero_smul] at h1
      exact h1.symm
  -- conclude: evalTensor injective via surjectivity of F and injectivity of G
  refine (injective_iff_map_eq_zero (evalTensor k A X V)).mpr fun t ht => ?_
  obtain ⟨y, rfl⟩ := hFsurj t
  rw [hGF y] at ht
  rw [hG (ht.trans (map_zero G).symm), map_zero]

end PerX

end Etingof

namespace Etingof

open scoped DirectSum

variable (k : Type*) (A : Type*) {ι : Type*} (X : ι → Type*) (V : Type*)
  [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
  [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)] [∀ i, Module A (X i)]
  [∀ i, IsScalarTower k A (X i)]
  [∀ i, IsSimpleModule A (X i)] [∀ i, FiniteDimensional k (X i)]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V] [IsSemisimpleModule A V]

/-- The full natural map `f` of Remark 3.1.3, assembled from the per-irreducible evaluation
maps `Etingof.evalTensor`. With `{X i}` a finite family of irreducibles, this is the `k`-linear
map `⨁_i Hom_A(X i, V) ⊗_k X i → V`, `g ⊗ x ↦ g(x)`. -/
noncomputable def evalDirectSum :
    (⨁ i, (X i →ₗ[A] V) ⊗[k] X i) →ₗ[k] V :=
  DirectSum.toModule k ι V (fun i => evalTensor k A (X i) V)

@[simp]
theorem evalDirectSum_lof_tmul (i : ι) (g : X i →ₗ[A] V) (x : X i) :
    evalDirectSum k A X V (DirectSum.lof k ι (fun i => (X i →ₗ[A] V) ⊗[k] X i) i (g ⊗ₜ[k] x))
      = g x := by
  simp [evalDirectSum]

/-- Schur vanishing: a homomorphism between non-isomorphic simple modules is zero. -/
theorem linearMap_eq_zero_of_isEmpty_linearEquiv {Y Z : Type*}
    [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z]
    [IsSimpleModule A Y] [IsSimpleModule A Z]
    (h : IsEmpty (Y ≃ₗ[A] Z)) (f : Y →ₗ[A] Z) : f = 0 := by
  by_contra hf
  exact h.elim (LinearEquiv.ofBijective f (f.bijective_of_ne_zero hf))

/-- Every simple `A`-submodule of `V` is contained in the range of `evalDirectSum`: if `W ≃ X i`
then the inclusion `W ↪ V` is `g(e w) = w` for `g = W.subtype ∘ e⁻¹ ∈ Hom_A(X i, V)`, so each
`w ∈ W` is hit. -/
theorem simpleSubmodule_le_range_evalDirectSum
    (hcomplete : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i))
    (W : Submodule A V) (hW : IsSimpleModule A W) :
    (W : Set V) ⊆ LinearMap.range (evalDirectSum k A X V) := by
  obtain ⟨i, ⟨e⟩⟩ := hcomplete W hW
  intro w hw
  refine ⟨DirectSum.lof k ι _ i ((W.subtype ∘ₗ e.symm.toLinearMap) ⊗ₜ[k] e ⟨w, hw⟩), ?_⟩
  rw [evalDirectSum_lof_tmul]
  simp

/-- `evalDirectSum` is surjective when `{X i}` is complete: `V` is the supremum of its simple
`A`-submodules (semisimplicity), each of which lies in the range. -/
theorem evalDirectSum_surjective
    (hcomplete : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i)) :
    Function.Surjective (evalDirectSum k A X V) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff]
  intro v _
  have htop : v ∈ sSup { m : Submodule A V | IsSimpleModule A m } := by
    rw [IsSemisimpleModule.sSup_simples_eq_top A V]; trivial
  rw [sSup_eq_iSup'] at htop
  refine Submodule.iSup_induction _
    (motive := fun y => y ∈ LinearMap.range (evalDirectSum k A X V))
    htop (fun m y hy => ?_) (LinearMap.range _).zero_mem
    (fun _ _ => (LinearMap.range _).add_mem)
  exact simpleSubmodule_le_range_evalDirectSum k A X V hcomplete m.1 m.2 hy

/-- `evalDirectSum` is injective.

Proof strategy (Schur, using `Etingof.Corollary_2_3_10` that `End_A(X i) = k·id`): if
`∑ᵢ evalTensor (ξ i) = 0`, each summand `evalTensor (ξ i)` lies in the `X i`-isotypic component
of `V`. By pairwise non-isomorphism these components are independent (`sSupIndep`), so each
`evalTensor (ξ i) = 0`. The per-`X` map `evalTensor : Hom_A(X i, V) ⊗_k X i → V` is injective:
choosing a `k`-basis `gⱼ` of `Hom_A(X i, V)`, a nonzero kernel element would give a simple
submodule `S ≅ X i` of `(X i)ⁿ` inside `ker (yⱼ ↦ ∑ gⱼ(yⱼ))`; its component maps `X i → X i`
are scalars `cⱼ` (Corollary 2.3.10), and `∑ cⱼ gⱼ = 0` forces all `cⱼ = 0`, contradicting
simplicity. Hence `ξ i = 0`. -/
theorem evalDirectSum_injective
    (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j)) :
    Function.Injective (evalDirectSum k A X V) := by
  sorry

/-- The Remark 3.1.3 isomorphism: for a semisimple finite dimensional representation `V`, the
natural map `⨁_i Hom_A(X i, V) ⊗_k X i → V`, `g ⊗ x ↦ g(x)`, is a `k`-linear isomorphism,
where `{X i}` is a complete set of pairwise non-isomorphic irreducibles.

Following Etingof's reduction: `V` decomposes as a direct sum of its isotypic components, the
map restricts on each summand to an isomorphism onto the corresponding component, and Schur's
lemma kills the cross terms. -/
noncomputable def evalDirectSumEquiv
    (hpair : ∀ i j, i ≠ j → IsEmpty (X i ≃ₗ[A] X j))
    (hcomplete : ∀ (W : Submodule A V), IsSimpleModule A W → ∃ i, Nonempty (W ≃ₗ[A] X i)) :
    (⨁ i, (X i →ₗ[A] V) ⊗[k] X i) ≃ₗ[k] V :=
  LinearEquiv.ofBijective (evalDirectSum k A X V)
    ⟨evalDirectSum_injective k A X V hpair, evalDirectSum_surjective k A X V hcomplete⟩

end Etingof
