import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplittingIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The standard resolution short exact sequence

Eighth (assembly) layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i), parent #6420). Write `A := PathAlgebra k Q`, `S := Q → k`, `V` the arrow
bimodule. The standard short complex

```
A ⊗_S (V ⊗_S M) →ᵈ A ⊗_S M →ᵉ M
```

(`Chapter9/PathAlgebraStandardComplex.lean`, `standardComplex M`) is assembled here into a short
**exact** sequence. `Epi ε` is `epi_stdε`; `d ≫ ε = 0` is `stdd_comp_stdε`. This file adds:

* **middle exactness** `ker ε = im d` (`standardComplex_exact`), by the downward length-degree
  telescoping — the noncommutative analogue of the `koszulSES_shortExact` exactness argument
  (`Chapter9/Example9_4_4.lean`), built on the cons-preimage `exists_stdΦ_preimage_topDegree`
  (surjectivity of `Φ` onto each top length component) and the coordinate shift relations
  `inducedCoordMap_stdd_shift`(`_zero`) from `Chapter9/PathAlgebraConsSplittingIso.lean`.

The bottom of the telescoping bottoms out at degree `0`, where `A_0 = f(S)` and `A_0 ⊗_S M ≅ M`
(`inducedCoordMap_zero_eq`, `stdε_injective_of_higher_coord_zero`): the multiplication `ε` is
injective on the length-`0` component, so `ξ ∈ ker ε` concentrated in degree `0` is `0`.

`Mono (stdd M)` — injectivity of `d` — is the residual deliverable of #6512 (needs the
cons-splitting `A_n ⊗_S V ≅ A_{n+1}` injectivity packaged as a left inverse of `stdΦ`), tracked
separately; once landed, `standardResolution_shortExact` assembles the full
`(standardComplex M).ShortExact` from `Mono d`, `Epi ε`, and `standardComplex_exact`.

Consumer: `hasHomologicalDimensionLE_pathAlgebra_one` in `Chapter9/Problem9_4_6.lean` (issue
#6438), completing Problem 9.4.6 (i).
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-! ## The length-`0` component: `ε` is injective there -/

/-- **Length-`0` component is a vertex scalar.** The degree-`0` part `lengthProj 0 a` of any
`a ∈ A` lies in `f(S) = vertexEmbedding`, so tensoring it against `m` moves it across the balanced
tensor: `(lengthProj 0 a) ⊗ m = 1 ⊗ (lengthProj 0 a · m)`. Proof by reduction to a single basis
path, which at length `0` is a trivial-path idempotent `eᵢ = vertexEmbedding (Pi.single i c)`. -/
theorem lengthProj_zero_tmul (a : PathAlgebra k Q) (m : restrictObj M) :
    ((lengthProj k Q 0 a) ⊗ₜ[Q → k] (m : M) : inducedCarrier M)
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k]
          ((lengthProj k Q 0 a) • (m : M) : restrictObj M) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, TensorProduct.add_tmul, hf, hg, add_smul, TensorProduct.tmul_add]
  | single x c =>
      obtain ⟨a, b, p⟩ := x
      rw [lengthProj_single, pathLen_mk]
      cases p with
      | nil =>
          rw [if_pos Quiver.Path.length_nil]
          have hv : (Finsupp.single (⟨a, a, Quiver.Path.nil⟩ : QuiverPathIndex Q) c
                : PathAlgebra k Q)
              = vertexEmbedding k Q (Pi.single a c) := by
            rw [vertexEmbedding_apply, Finset.sum_eq_single a]
            · rw [Pi.single_eq_same]
            · intro j _ hj; rw [Pi.single_eq_of_ne hj, Finsupp.single_zero]
            · intro h; exact absurd (Finset.mem_univ a) h
          rw [hv, ← one_tmul_smul]
      | cons q e =>
          rw [if_neg (by rw [Quiver.Path.length_cons]; exact Nat.succ_ne_zero _)]
          rw [TensorProduct.zero_tmul, zero_smul, TensorProduct.tmul_zero]

/-- **The length-`0` coordinate is `1 ⊗ ε(it)`.** For any `ξ`, its degree-`0` homogeneous
coordinate `inducedCoordMap M ξ 0 ∈ A ⊗_S M` equals `1 ⊗ ε(that coordinate)`. This is the
`A_0 ⊗_S M ≅ M` identification at the coordinate level, reducing (by additivity) to
`lengthProj_zero_tmul`. -/
theorem inducedCoordMap_zero_eq (ξ : inducedRestrictObj M) :
    inducedCoordMap M ξ 0
      = (1 : PathAlgebra k Q) ⊗ₜ[Q → k]
          (show restrictObj M from (stdε M).hom (inducedCoordMap M ξ 0)) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [inducedCoordMap_tmul, stdε_tmul]
      exact lengthProj_zero_tmul M a m
  | add x y hx hy =>
      have hsum : inducedCoordMap M (x + y) 0
          = inducedCoordMap M x 0 + inducedCoordMap M y 0 := by
        rw [map_add, Finsupp.add_apply]
      rw [hsum, map_add, TensorProduct.tmul_add, ← hx, ← hy]

/-- **The length-`0` coordinate is length-homogeneous.** The coordinate map of the degree-`0`
component `inducedCoordMap M ξ 0` is concentrated in degree `0`. By `lengthProj_lengthProj`. -/
theorem inducedCoordMap_coord_zero (ξ : inducedRestrictObj M) :
    inducedCoordMap M (inducedCoordMap M ξ 0) = Finsupp.single 0 (inducedCoordMap M ξ 0) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      ext n
      rw [inducedCoordMap_tmul, inducedCoordMap_tmul, lengthProj_lengthProj, Finsupp.single_apply]
      by_cases h : n = 0
      · subst h; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg (fun he : (0 : ℕ) = n => h he.symm), TensorProduct.zero_tmul]
  | add x y hx hy =>
      have hsum : inducedCoordMap M (x + y) 0
          = inducedCoordMap M x 0 + inducedCoordMap M y 0 := by
        rw [map_add, Finsupp.add_apply]
      rw [hsum, map_add, Finsupp.single_add, hx, hy]

/-- **`ε` is injective on the length-`0` component.** If all higher length coordinates of `ξ`
vanish and `ε ξ = 0`, then `ξ = 0`. This is the base case of the middle-exactness telescoping:
`A_0 ⊗_S M ≅ M` and `ε` is that isomorphism, so a degree-`0` element of `ker ε` is `0`. -/
theorem stdε_injective_of_higher_coord_zero (ξ : inducedRestrictObj M)
    (h : ∀ n, inducedCoordMap M ξ (n + 1) = 0) (hε : (stdε M).hom ξ = 0) :
    ξ = 0 := by
  have hξ : ξ = inducedCoordMap M ξ 0 := by
    apply inducedCoordMap_injective
    rw [inducedCoordMap_coord_zero]
    ext n
    cases n with
    | zero => rw [Finsupp.single_apply, if_pos rfl]
    | succ m => rw [h m, Finsupp.single_apply, if_neg (by omega : ¬ (0 = m + 1))]
  have key := inducedCoordMap_zero_eq M ξ
  rw [← hξ, hε, TensorProduct.tmul_zero] at key
  exact key

/-! ## Middle exactness via the downward length-degree telescoping -/

/-- **The telescoping induction.** For every `N`, if the length coordinates of `ξ` vanish above
degree `N` and `ε ξ = 0`, then `ξ ∈ im d`. The step subtracts `d η`, where `η` is the degree-`N`
cons-preimage of the top component `inducedCoordMap M ξ (N+1)` (`exists_stdΦ_preimage_topDegree`),
which lowers the top degree by one; the base `N = 0` is `stdε_injective_of_higher_coord_zero`. -/
theorem standardComplex_exact_aux :
    ∀ (N : ℕ) (ξ : inducedRestrictObj M),
      (∀ n, N < n → inducedCoordMap M ξ n = 0) → (stdε M).hom ξ = 0 →
        ∃ ζ : inducedVtensObj M, (stdd M).hom ζ = ξ := by
  intro N
  induction N with
  | zero =>
      intro ξ h hε
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      refine stdε_injective_of_higher_coord_zero M ξ (fun n => h (n + 1) (Nat.succ_pos n)) hε
  | succ N ih =>
      intro ξ h hε
      obtain ⟨η, hηN, hηj, hηΦ⟩ := exists_stdΦ_preimage_topDegree M ξ N
      have hdε : (stdε M).hom ((stdd M).hom η) = 0 := by
        have e := congrArg (fun f : inducedVtensObj M ⟶ M => f.hom η) (stdd_comp_stdε M)
        simpa using e
      set ξ' : inducedRestrictObj M := ξ - (stdd M).hom η with hξ'
      have hε' : (stdε M).hom ξ' = 0 := by
        rw [hξ', map_sub, hε, hdε, sub_zero]
      have hcoord : ∀ n, N < n → inducedCoordMap M ξ' n = 0 := by
        intro n hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hξ', map_sub, Finsupp.sub_apply, inducedCoordMap_stdd_shift M η m]
        by_cases hmN : m = N
        · subst hmN
          rw [hηN, hηj (m + 1) (by omega), map_zero, sub_zero, hηΦ, sub_self]
        · rw [hηj m hmN, hηj (m + 1) (by omega), map_zero, map_zero, sub_zero,
            h (m + 1) (by omega), zero_sub, neg_zero]
      obtain ⟨ζ', hζ'⟩ := ih ξ' hcoord hε'
      exact ⟨ζ' + η, by rw [map_add, hζ', hξ']; abel⟩

/-- **Middle exactness of the standard short complex**: `ker ε = im d`. Given `ξ ∈ ker ε`, run the
telescoping `standardComplex_exact_aux` with `N` the top length degree of `ξ` (a finite support).
The `im d ⊆ ker ε` inclusion is `stdd_comp_stdε`. -/
theorem standardComplex_exact : (standardComplex M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro ξ hξ
  set F := inducedCoordMap M ξ with hF
  by_cases hne : F.support.Nonempty
  · have hhigh : ∀ n, F.support.max' hne < n → inducedCoordMap M ξ n = 0 := by
      intro n hn
      have hnm : n ∉ F.support := fun hmem => by
        have := Finset.le_max' _ _ hmem; omega
      simpa [hF] using Finsupp.notMem_support_iff.mp hnm
    exact standardComplex_exact_aux M (F.support.max' hne) ξ hhigh hξ
  · have hF0 : F = 0 := by
      rw [← Finsupp.support_eq_empty, Finset.not_nonempty_iff_eq_empty.mp hne]
    have hhigh : ∀ n, 0 < n → inducedCoordMap M ξ n = 0 := by
      intro n _; rw [← hF, hF0, Finsupp.zero_apply]
    exact standardComplex_exact_aux M 0 ξ hhigh hξ

/-! ## Assembly of the short exact sequence

The full `(standardComplex M).ShortExact` needs `Mono (stdd M)` (injectivity of `d`), the residual
deliverable of #6512 — the cons-splitting `A_n ⊗_S V ≅ A_{n+1}` injectivity packaged as a left
inverse of `stdΦ`. Once available as `stdd_mono`, the assembly is:

```
theorem standardResolution_shortExact : (standardComplex M).ShortExact where
  exact := standardComplex_exact M
  mono_f := stdd_mono M
  epi_g := epi_stdε M
```
-/

end Etingof.PathAlgebra
