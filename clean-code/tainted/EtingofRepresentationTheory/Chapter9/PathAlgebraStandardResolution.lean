import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplittingIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option backward.isDefEq.respectTransparency false

/-!
# The standard resolution short exact sequence

The standard length-`1` projective resolution of path-algebra modules is completed here
(Problem 9.4.6 (i)). Write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra, `V` the arrow bimodule. The standard short complex

```
A ⊗_S (V ⊗_S M) →ᵈ A ⊗_S M →ᵉ M
```

(`Chapter9/PathAlgebraStandardComplex.lean`, `standardComplex M`) is assembled here into a short
exact sequence `(standardComplex M).ShortExact`. `Epi ε` is `epi_stdε`; `d ≫ ε = 0` is
`stdd_comp_stdε`. This file adds the two remaining halves and assembles them:

## Injectivity of the boundary `d` (`Mono d`)

The main point is the injectivity of the top half `Φ = stdΦ` of `d`
(`Chapter9/PathAlgebraConsSplittingIso.lean`), i.e. the injectivity content of the cons-splitting
`A_n ⊗_S V ≅ A_{n+1}` tensored with `M`. We build an additive retraction `stdΦRetr` of
`Φ` from the combinatorial cons-decomposition (`Chapter9/PathAlgebraConsSplitting.lean`): every
length-`(n+1)` basis path `q = p·e` splits into its initial length-`n` path `p` and final arrow
`e`, and the retraction sends `(x·arrow) ⊗ m ↦ x ⊗ (arrow ⊗ m)`. Injectivity of `Φ` then feeds the
top-degree telescoping: from `d ξ = 0` one gets `Φ(ξ_n) = Ψ(ξ_{n+1})`, and the retraction turns
this into `ξ_n = R(Ψ(ξ_{n+1}))`, so `finsupp_shift_eq_zero` forces the graded components of `ξ` to
vanish, hence `ξ = 0` (`inducedCoordMapGen_injective`). This is the noncommutative analogue of the
top-degree argument `pm_koszul_injective` / `finsupp_shift_eq_zero` (`Chapter9/KoszulHelpers.lean`).

Because the tensors are formed over `S = Q → k` (not the base field `k`), a bare `k`-scalar does not
act on them. We express every `k`-scalar `r` through the constant function `const r : Q → k`,
using `r • a = (const r) • a` in the path algebra (`kSMul_eq_constSMul`) together with the
`S`-balancing of the tensors.

## Middle exactness (`ker ε = im d`)

Middle exactness `standardComplex_exact` is the noncommutative analogue of the
`koszulSES_shortExact` exactness argument (`Chapter9/Example9_4_4.lean`), by the downward
length-degree telescoping built on
the cons-preimage `exists_stdΦ_preimage_topDegree` (surjectivity of `Φ` onto each top length
component) and the coordinate shift relations `inducedCoordMap_stdd_shift`(`_zero`) from
`Chapter9/PathAlgebraConsSplittingIso.lean`. The telescoping bottoms out at degree `0`, where
`A_0 = f(S)` and `A_0 ⊗_S M ≅ M` (`inducedCoordMap_zero_eq`,
`stdε_injective_of_higher_coord_zero`): the multiplication `ε` is injective on the length-`0`
component, so `ξ ∈ ker ε` concentrated in degree `0` is `0`.

This is used by `hasHomologicalDimensionLE_pathAlgebra_one` (`Chapter9/Problem9_4_6.lean`) to
complete Problem 9.4.6 (i).
-/

universe u

open CategoryTheory TensorProduct
open ModuleCat (restrictScalars)

namespace Etingof.PathAlgebra

variable {k Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

variable (M : ModuleCat.{u + 1} (PathAlgebra k Q))

/-! ## Routing a base-field scalar through the vertex subalgebra -/

/-- **A base-field scalar acts as the constant function.** For `r : k`, scaling `a : A` by `r`
equals the `S`-action of the constant vertex family `const r : Q → k` (right multiplication by
`f (const r) = r • 1`). This lets us move a `k`-scalar across the `S`-balanced tensors. -/
theorem kSMul_eq_constSMul (r : k) (a : PathAlgebra k Q) :
    r • a = (Function.const Q r : Q → k) • a := by
  rw [vertex_smul_def]
  have h1 : vertexEmbedding k Q (Function.const Q r) = r • (1 : PathAlgebra k Q) := by
    have hone : (1 : PathAlgebra k Q)
        = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : QuiverPathIndex Q) (1 : k) := by
      have := (vertexEmbedding k Q).map_one
      rw [vertexEmbedding_apply] at this
      simp only [Pi.one_apply] at this
      exact this.symm
    rw [vertexEmbedding_apply, hone, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.const_apply, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1, mul_smul_comm, mul_one]

/-! ## The combinatorial cons-splitting contribution of a basis path -/

/-- **The cons-split of a single basis path (with coefficient).** A length-`0` (vertex) path
contributes `0`; a positive-length path `q = cons p e` with coefficient `c` contributes
`(c • p) ⊗ (e ⊗ m)`, splitting off its final arrow `e`. This is the per-basis-path core of the
additive retraction `stdΦRetr` of the top half `Φ` of the boundary `d`. -/
noncomputable def consContrib (x : QuiverPathIndex Q) (c : k) (m : restrictObj M) :
    inducedVtensObj M :=
  match x with
  | ⟨_, _, .nil⟩ => 0
  | ⟨a, d, .cons (b := b) p e⟩ =>
      ((c • ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, d, e⟩ : ArrowIndex Q) (1 : k) : ArrowTgt k Q) ⊗ₜ[Q → k] m
          : VtensObj M) : inducedVtensObj M)

@[simp] theorem consContrib_nil (a : Q) (c : k) (m : restrictObj M) :
    consContrib M (⟨a, a, Quiver.Path.nil⟩ : QuiverPathIndex Q) c m = 0 := rfl

@[simp] theorem consContrib_cons {a b d : Q} (p : Quiver.Path a b) (e : b ⟶ d) (c : k)
    (m : restrictObj M) :
    consContrib M (⟨a, d, Quiver.Path.cons p e⟩ : QuiverPathIndex Q) c m
      = ((c • ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) ⊗ₜ[Q → k]
        ((Finsupp.single (⟨b, d, e⟩ : ArrowIndex Q) (1 : k) : ArrowTgt k Q) ⊗ₜ[Q → k] m
          : VtensObj M) : inducedVtensObj M) := rfl

theorem consContrib_add_coeff (x : QuiverPathIndex Q) (c c' : k) (m : restrictObj M) :
    consContrib M x (c + c') m = consContrib M x c m + consContrib M x c' m := by
  obtain ⟨a, d, q⟩ := x
  cases q with
  | nil => simp
  | cons p e => rw [consContrib_cons, consContrib_cons, consContrib_cons, add_smul,
      TensorProduct.add_tmul]

theorem consContrib_add_right (x : QuiverPathIndex Q) (c : k) (m m' : restrictObj M) :
    consContrib M x c (m + m') = consContrib M x c m + consContrib M x c m' := by
  obtain ⟨a, d, q⟩ := x
  cases q with
  | nil => simp
  | cons p e => rw [consContrib_cons, consContrib_cons, consContrib_cons, TensorProduct.tmul_add,
      TensorProduct.tmul_add]

/-- The per-path contribution as an `AddMonoidHom` in `(coefficient, m)`, ready for
`Finsupp.liftAddHom`. -/
noncomputable def consContribHom (x : QuiverPathIndex Q) :
    k →+ (restrictObj M →+ inducedVtensObj M) :=
  AddMonoidHom.mk'
    (fun c => AddMonoidHom.mk' (fun m => consContrib M x c m) (consContrib_add_right M x c))
    (fun c c' => by ext m; exact consContrib_add_coeff M x c c' m)

/-! ## The additive retraction `stdΦRetr` of `Φ` -/

/-- The `S`-balanced bilinear datum `A × M → A ⊗_S (V ⊗_S M)` underlying the retraction: on a basis
path with coefficient it applies `consContrib`, summed over the paths of `a`. -/
noncomputable def Rbilin : PathAlgebra k Q →+ (restrictObj M →+ inducedVtensObj M) :=
  Finsupp.liftAddHom (consContribHom M)

@[simp] theorem Rbilin_single (x : QuiverPathIndex Q) (c : k) (m : restrictObj M) :
    Rbilin M (Finsupp.single x c) m = consContrib M x c m := by
  have h : Rbilin M (Finsupp.single x c) = consContribHom M x c := by
    rw [Rbilin]; exact Finsupp.liftAddHom_apply_single (consContribHom M) x c
  rw [h]; rfl

/-- **`consContrib` is `S`-balanced.** Scaling the coefficient by the target vertex value
`s (tgt x)` equals scaling `m` by the `S`-action of `s`. -/
theorem consContrib_balanced (s : Q → k) (x : QuiverPathIndex Q) (c : k) (m : restrictObj M) :
    consContrib M x (s x.2.1 * c) m = consContrib M x c (s • m) := by
  obtain ⟨a, d, q⟩ := x
  cases q with
  | nil => simp
  | cons p e =>
      -- target balancing of the inner tensor: `single e 1 ⊗ (s • m) = single e (s d) ⊗ m`
      have hR : ((Finsupp.single (⟨_, d, e⟩ : ArrowIndex Q) (1 : k) : ArrowTgt k Q)
            ⊗ₜ[Q → k] (s • m : restrictObj M) : VtensObj M)
          = ((Finsupp.single (⟨_, d, e⟩ : ArrowIndex Q) (s d) : ArrowTgt k Q) ⊗ₜ[Q → k] m
            : VtensObj M) := by
        rw [← TensorProduct.smul_tmul]
        congr 1
        change wSMul k Q ArrowIndex.tgt s _ = _
        rw [wSMul_single]; simp
      rw [consContrib_cons, consContrib_cons, hR]
      -- LHS: (s d * c) • ofPath p = const (s d) • (c • ofPath p)
      rw [show ((s d * c) • ofPath (⟨a, _, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q)
            = (Function.const Q (s d) : Q → k) • (c • ofPath (⟨a, _, p⟩ : QuiverPathIndex Q))
            from by rw [mul_smul, ← kSMul_eq_constSMul]]
      -- outer balancing then compute the source action on the inner arrow
      rw [TensorProduct.smul_tmul]
      congr 1
      change (Function.const Q (s d) : Q → k) • (_ : VtensObj M) = _
      rw [vtens_smul_def, vtens_smul_tmul, srcHom_apply]
      congr 1
      change wSMul k Q ArrowIndex.src _ _ = _
      rw [wSMul_single]; simp

theorem Rbilin_balanced (s : Q → k) (a : PathAlgebra k Q) (m : restrictObj M) :
    Rbilin M (s • a) m = Rbilin M a (s • m) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [smul_add, map_add, AddMonoidHom.add_apply, hf, hg, map_add, AddMonoidHom.add_apply]
  | single x c =>
      rw [vertex_smul_def, single_mul_vertexEmbedding, Finsupp.smul_single, smul_eq_mul,
        Rbilin_single, Rbilin_single, consContrib_balanced]

/-- **The additive retraction of the top half `Φ` of `d`.** The `A ⊗_S (V ⊗_S M)`-valued map on
`A ⊗_S M` splitting off, in each basis path of the first factor, its final arrow. Well-defined by
the `S`-balancing `Rbilin_balanced`. -/
noncomputable def stdΦRetr : (inducedRestrictObj M : Type (u + 1)) →+ inducedVtensObj M :=
  TensorProduct.liftAddHom (Rbilin M) (Rbilin_balanced M)

@[simp] theorem stdΦRetr_tmul (a : PathAlgebra k Q) (m : restrictObj M) :
    stdΦRetr M (a ⊗ₜ[Q → k] m) = Rbilin M a m := rfl

/-! ## The retraction identity and injectivity of `Φ` -/

/-- **The retraction inverts `Φ` on basis generators.** Splitting off the final arrow of the
product `a · v` recovers the pure tensor `a ⊗ (v ⊗ m)`. Reduces, via bi-additivity, to a single
path `x` times a single arrow `y`: when composable, cons-uniqueness identifies the split; when not,
both sides vanish (the domain pure tensor by the source-action balancing). -/
theorem Rbilin_mul_arrowInclusion (a : PathAlgebra k Q) (v : ArrowTgt k Q) (m : restrictObj M) :
    Rbilin M (a * arrowInclusion v) m
      = (a ⊗ₜ[Q → k] ((v ⊗ₜ[Q → k] m : VtensObj M)) : inducedVtensObj M) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [add_mul, map_add, AddMonoidHom.add_apply, hf, hg, TensorProduct.add_tmul]
  | single x c =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw =>
          rw [map_add, mul_add, map_add, AddMonoidHom.add_apply, hv, hw,
            TensorProduct.add_tmul, TensorProduct.tmul_add]
      | single y d =>
          rw [arrowInclusion_single]
          rw [show (Finsupp.single x c : PathAlgebra k Q) = c • ofPath x from by
                rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]]
          rw [show (c • ofPath x : PathAlgebra k Q) * (d • arrowElt y)
                = (c * d) • (ofPath x * arrowElt y) from by rw [smul_mul_smul_comm]]
          obtain ⟨a₀, b₀, p⟩ := x
          obtain ⟨c₀, d₀, e⟩ := y
          by_cases hbc : b₀ = c₀
          · subst hbc
            -- composable: `x · y = cons p e`
            rw [ofPath_mul_arrowElt, Quiver.Path.comp_toPath_eq_cons,
              show ((c * d) • ofPath (⟨a₀, d₀, Quiver.Path.cons p e⟩ : QuiverPathIndex Q)
                    : PathAlgebra k Q)
                  = Finsupp.single (⟨a₀, d₀, Quiver.Path.cons p e⟩ : QuiverPathIndex Q) (c * d)
                  from by rw [ofPath, Finsupp.smul_single, smul_eq_mul, mul_one],
              Rbilin_single, consContrib_cons]
            -- move `d` from the coefficient onto the arrow via `const d` and the balancing
            rw [show ((c * d) • ofPath (⟨a₀, b₀, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q)
                  = (Function.const Q d : Q → k) • (c • ofPath (⟨a₀, b₀, p⟩ : QuiverPathIndex Q))
                  from by rw [mul_comm, mul_smul, ← kSMul_eq_constSMul]]
            rw [TensorProduct.smul_tmul]
            congr 1
            change (Function.const Q d : Q → k) • (_ : VtensObj M) = _
            rw [vtens_smul_def, vtens_smul_tmul, srcHom_apply]
            congr 1
            change wSMul k Q ArrowIndex.src _ _ = _
            rw [wSMul_single]; simp
          · -- non-composable: both sides are zero
            have hz : wSMul k Q ArrowIndex.src (Pi.single b₀ 1)
                (Finsupp.single (⟨c₀, d₀, e⟩ : ArrowIndex Q) d) = 0 := by
              rw [wSMul_single]
              simp only [ArrowIndex.src_mk, Pi.single_eq_of_ne (Ne.symm hbc), zero_mul,
                Finsupp.single_zero]
            rw [arrowElt, ArrowIndex.toPathIndex, ofPath_mul_ofPath, compSingle_eq_zero _ _ hbc,
              smul_zero, map_zero, AddMonoidHom.zero_apply]
            symm
            rw [show (c • ofPath (⟨a₀, b₀, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q)
                  = (Pi.single b₀ 1 : Q → k) • (c • ofPath (⟨a₀, b₀, p⟩ : QuiverPathIndex Q))
                  from by rw [vertex_smul_def, smul_mul_assoc, ofPath_mul_vertexEmbedding]; simp]
            rw [TensorProduct.smul_tmul, vtens_smul_def, vtens_smul_tmul, srcHom_apply, hz,
              TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-- **The additive retraction inverts `Φ`.** `stdΦRetr ∘ Φ = id`; the retraction splits
off the arrow that `Φ` multiplied in. -/
theorem stdΦRetr_stdΦ (x : inducedVtensObj M) :
    stdΦRetr M ((stdΦ M).hom x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v m => rw [stdΦ_tmul, stdΦRetr_tmul, Rbilin_mul_arrowInclusion]
      | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
  | add x z hx hz => rw [map_add, map_add, hx, hz]

/-- **Injectivity of the top half `Φ` of `d`.** From the additive retraction `stdΦRetr`. This is
the injectivity content of the cons-splitting `A_n ⊗_S V ≅ A_{n+1}` tensored with `M`. -/
theorem stdΦ_injective : Function.Injective (stdΦ M).hom :=
  Function.LeftInverse.injective (stdΦRetr_stdΦ M)

/-! ## Injectivity of the boundary `d` -/

/-- **`Mono (stdd M)`: the boundary map `d` is injective.** Top-degree telescoping: from `d ξ = 0`
and the coordinate shift `inducedCoordMap_stdd_shift`, the graded components satisfy
`Φ(ξ_n) = Ψ(ξ_{n+1})`; applying the retraction gives `ξ_n = R(Ψ(ξ_{n+1}))`, so
`finsupp_shift_eq_zero` forces every `ξ_n = 0`, hence `ξ = 0` by `inducedCoordMapGen_injective`. The
noncommutative analogue of the `Mono d` half of `koszulSES_shortExact`. -/
theorem stdd_injective : Function.Injective (stdd M).hom := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  set g : inducedVtensObj M → inducedVtensObj M :=
    fun y => stdΦRetr M ((stdΨ M).hom y) with hg
  have hF : inducedCoordMapGen (VtensObj M) ξ = 0 := by
    refine finsupp_shift_eq_zero g (by rw [hg]; simp) _ (fun n => ?_)
    have key := inducedCoordMap_stdd_shift M ξ n
    rw [hξ] at key
    simp only [map_zero, Finsupp.zero_apply] at key
    have hΦΨ : (stdΦ M).hom (inducedCoordMapGen (VtensObj M) ξ n)
        = (stdΨ M).hom (inducedCoordMapGen (VtensObj M) ξ (n + 1)) := by
      rw [← sub_eq_zero]; exact key.symm
    rw [hg]
    calc inducedCoordMapGen (VtensObj M) ξ n
        = stdΦRetr M ((stdΦ M).hom (inducedCoordMapGen (VtensObj M) ξ n)) :=
          (stdΦRetr_stdΦ M _).symm
      _ = stdΦRetr M ((stdΨ M).hom (inducedCoordMapGen (VtensObj M) ξ (n + 1))) := by rw [hΦΨ]
  have := inducedCoordMapGen_injective (VtensObj M)
  apply this
  rw [hF, map_zero]

/-- **`Mono (stdd M)`.** Injectivity of the boundary map `d` of the standard short complex, as a
categorical monomorphism. Together with `standardComplex_exact` (middle exactness) and `epi_stdε`,
it assembles `(standardComplex M).ShortExact`. -/
theorem stdd_mono : Mono (stdd M) := by
  rw [ModuleCat.mono_iff_injective]
  exact stdd_injective M

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

/-! ## The short exact sequence -/

/-- **The standard resolution short exact sequence**: `(standardComplex M).ShortExact`. Assembled
from `Mono (stdd M)` (injectivity of `d`, `stdd_mono`), middle exactness `standardComplex_exact`,
and `Epi (stdε M)` (`epi_stdε`). This is the length-`1` projective resolution of `M` over the path
algebra, used by `hasHomologicalDimensionLE_pathAlgebra_one`
(`Chapter9/Problem9_4_6.lean`). -/
theorem standardResolution_shortExact : (standardComplex M).ShortExact where
  exact := standardComplex_exact M
  mono_f := stdd_mono M
  epi_g := epi_stdε M

end Etingof.PathAlgebra
