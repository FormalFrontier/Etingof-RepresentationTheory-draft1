import EtingofRepresentationTheory.Chapter9.PathAlgebraConsSplittingIso

/-!
# Injectivity of the boundary map of the standard short complex

Eighth layer of the standard length-`1` projective resolution of path-algebra modules
(Problem 9.4.6 (i), parent #6420). Write `A := PathAlgebra k Q`, `S := Q → k` the vertex
subalgebra, `V` the arrow bimodule. This file proves `Mono (stdd M)` — injectivity of the
boundary map `d` of the standard short complex
(`Chapter9/PathAlgebraStandardComplex.lean`) — the noncommutative analogue of the top-degree
argument `pm_koszul_injective` / `finsupp_shift_eq_zero` (`Chapter9/KoszulHelpers.lean`).

The crux is the **injectivity of the top half** `Φ = stdΦ` of `d`
(`Chapter9/PathAlgebraConsSplittingIso.lean`), i.e. the injectivity content of the cons-splitting
`A_n ⊗_S V ≅ A_{n+1}` tensored with `M`. We build a genuine additive **retraction** `stdΦRetr` of
`Φ` from the combinatorial cons-decomposition (`Chapter9/PathAlgebraConsSplitting.lean`): every
length-`(n+1)` basis path `q = p·e` splits into its initial length-`n` path `p` and final arrow
`e`, and the retraction sends `(x·arrow) ⊗ m ↦ x ⊗ (arrow ⊗ m)`. Injectivity of `Φ` then feeds the
top-degree telescoping: from `d ξ = 0` one gets `Φ(ξ_n) = Ψ(ξ_{n+1})`, and the retraction turns
this into `ξ_n = R(Ψ(ξ_{n+1}))`, so `finsupp_shift_eq_zero` forces the graded components of `ξ` to
vanish, hence `ξ = 0` (`inducedCoordMapGen_injective`).

Because the tensors are formed over `S = Q → k` (not the base field `k`), a bare `k`-scalar does not
act on them. We route every `k`-scalar `r` through the **constant function** `const r : Q → k`,
using `r • a = (const r) • a` in the path algebra (`kSMul_eq_constSMul`) together with the
`S`-balancing of the tensors.
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

/-- **The additive retraction inverts `Φ`.** `stdΦRetr ∘ Φ = id`; the retraction genuinely splits
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
categorical monomorphism. This is the residual deliverable of the standard resolution short exact
sequence (issue #6512): together with `standardComplex_exact` (middle exactness) and `epi_stdε`, it
assembles `(standardComplex M).ShortExact`. -/
theorem stdd_mono : Mono (stdd M) := by
  rw [ModuleCat.mono_iff_injective]
  exact stdd_injective M

end Etingof.PathAlgebra
