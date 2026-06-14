import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.SchurWeylGLTransfer
import EtingofRepresentationTheory.Chapter5.PolynomialRepEmbedding
import EtingofRepresentationTheory.Chapter5.SemisimpleIsotypic

/-!
# Schur-Weyl #5, Step E: a polynomial `GL_N`-rep is a direct sum of abstract simples

This file assembles the *equivariant complete reducibility* of a polynomial
`GL_N(k)`-representation (Etingof §5.23, issue #2482). The main result,
`decompose_polynomial_gl_rep`, says that a finite-dimensional algebraic
`GL_N(k)`-representation `M`, all of whose weights have degree `n`, decomposes
`GL_N`-equivariantly (i.e. as a `MonoidAlgebra k GL_N`-module) as a finite
direct sum of the **abstract simple summands `L i`** of `V^{⊗n}`
(`V = Fin N → k`).

## Abstract-summand form (resolves the circularity with #6)

The decomposition is stated in terms of the abstract `L i` of the Schur-Weyl
decomposition of `V^{⊗n}` (`glTensorRep_equivariant_schurWeyl_decomposition`),
*not* in terms of concrete `SchurModule k N λ`. The concrete identification
`L i ≅ SchurModule k N λ` is the highest-weight classification that the
consumer #6 (`iso_of_formalCharacter_eq_schurPoly`) needs; routing it there
keeps the dependency graph acyclic (see the analysis recorded on issue #2482
and in `FormalCharacterIso.lean:1053`).

## Proof structure (and the remaining infrastructure gaps)

The assembly composes three already-merged pieces with two documented bridge
lemmas:

* **#4598** `polynomial_homog_rep_equivariant_embedding` — the `GL_N`-equivariant
  `k`-linear embedding `M ↪ (V^{⊗n})^m`.
* **#4600** `submodule_of_directSum_simple_iso_directSum` — a submodule of a
  finite direct sum of simple `R`-modules is itself a direct sum of those
  simples.
* `glTensorRep_equivariant_schurWeyl_decomposition` (equivariance) and
  `Theorem5_18_4_GL_rep_decomposition_simple` (simplicity of each `L i`).

The two named decomposition theorems build the **same** `L i = FDRep.of ρ_i`
but expose disjoint clauses (one the equivariance, the other the simplicity).
Unifying them, and transferring the `k`-linear equivariant data to the
`MonoidAlgebra k GL_N`-module level expected by the isotypic engine, are the
two bridge lemmas left as `sorry` here:

* `glTensorRep_schurWeyl_decomposition_equivariant_simple` — the unified
  equivariant + simple decomposition (merge the two existing proofs, both over
  `FDRep.of ρ_i`).
* `polynomial_homog_rep_asModule_embeds_directSum_simple` — package #4598 +
  the unified decomposition + the `asModule` transfer + the `Fin m`-fold
  product splitting into a single `R`-linear embedding of `M.asModule` as a
  submodule of a finite direct sum of the simple `L i`.

Given those two, `decompose_polynomial_gl_rep` is a clean application of the
isotypic engine #4600. The two bridges are filed as sub-issues of #2482.
-/

open scoped TensorProduct DirectSum
open CategoryTheory

namespace Etingof.PolynomialGLDecomposition

universe u

variable (k : Type u) [Field k] (N : ℕ)

/-- Abbreviation for the group algebra of `GL_N(k)`, the ring over which the
`GL_N`-equivariant decompositions are stated. -/
abbrev GLAlg := MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k)

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Unified equivariant + simple Schur-Weyl decomposition of `V^{⊗n}`.**

This is `glTensorRep_equivariant_schurWeyl_decomposition`
(`FormalCharacterIso.lean:775`) strengthened with the simplicity clause of
`Theorem5_18_4_GL_rep_decomposition_simple` (`SchurWeylGLTransfer.lean:659`):
each abstract summand `L i` is *simple* as a `MonoidAlgebra k GL_N`-module.

The heartbeat budgets match the source proofs (`Theorem5_18_4_GL_rep_decomposition_explicit`
/ `_simple`): the simplicity-enriched explicit existential has 14 binders whose
`Submodule → Module k` instance synthesis exceeds the default budget.

Both source theorems are built from the same explicit bimodule decomposition
(`Theorem5_18_4_bimodule_decomposition_explicit`) and produce the *same*
`L i = FDRep.of ρ_i` with `ρ_i = (postCompCentralizerMonoidHom …).comp glHom`.
The proof therefore re-runs the equivariance computation of the former while
keeping the centralizer-side simplicity clause that
`isSimpleModule_monoidAlgebra_GL_of_centralizer_simple` transports to `GL_N`.

TODO (sub-issue of #2482): merge the two existing proofs. -/
theorem glTensorRep_schurWeyl_decomposition_equivariant_simple
    [IsAlgClosed k] [CharZero k] (n : ℕ) (hN : n ≤ N) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (S : ι → Type u)
      (_ : ∀ i, AddCommGroup (S i))
      (_ : ∀ i, Module k (S i))
      (_ : ∀ i, Module.Finite k (S i))
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (GLAlg k N) (Representation.asModule (L i).ρ)),
      ∃ (e : TensorPower k (Fin N → k) n ≃ₗ[k]
          (DirectSum ι (fun i => S i ⊗[k] (L i : Type u)))),
        ∀ (g : Matrix.GeneralLinearGroup (Fin N) k)
          (v : TensorPower k (Fin N → k) n),
          e (glTensorRep k N n g v) =
            Representation.directSum (fun i =>
              (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
                (S i)).tprod (L i).ρ) g (e v) := by
  classical
  -- Get the explicit GL_N decomposition together with the per-`i` simplicity
  -- clause (`Theorem5_18_4_GL_rep_decomposition_explicit_simple`, issue #4666).
  obtain ⟨ι, hιFin, hιDec, S', hS'_simp, hS'_dist, hSi_fin, L, L_carrier,
      hL_simple, e, he, h_act⟩ :=
    Theorem5_18_4_GL_rep_decomposition_explicit_simple k N n hN
  refine ⟨ι, hιFin, hιDec, fun i => ↥(S' i),
    fun _ => inferInstance, fun _ => inferInstance,
    fun i => hSi_fin i, L, hL_simple, ?_, ?_⟩
  · exact e
  intro g v
  -- Reduce equivariance to: (glTensorRep g) ∘ e.symm = e.symm ∘ directSum_action g.
  -- This is the equivariance computation of
  -- `glTensorRep_equivariant_schurWeyl_decomposition` (FormalCharacterIso.lean),
  -- now run over the simplicity-enriched explicit data.
  have h_lin :
      (glTensorRep k N n g) ∘ₗ (e.symm : _ →ₗ[k] _) =
        (e.symm : _ →ₗ[k] _) ∘ₗ
          (Representation.directSum (fun i =>
            (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
              (↥(S' i))).tprod (L i).ρ) g) := by
    refine DirectSum.linearMap_ext k fun i => ?_
    apply TensorProduct.ext'
    intro s l
    change (glTensorRep k N n g) (e.symm
        (DirectSum.lof k ι (fun i => ↥(S' i) ⊗[k] (L i : Type u)) i
          (s ⊗ₜ[k] l))) =
      e.symm ((Representation.directSum (fun i =>
        (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
          (↥(S' i))).tprod (L i).ρ) g)
        (DirectSum.lof k ι _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lof_eq_of, he i s l]
    change _ = e.symm (DirectSum.lmap
      (fun i => ((Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (DirectSum.of _ i (s ⊗ₜ[k] l)))
    rw [DirectSum.lmap_of, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.trivial_apply, he i s ((L i).ρ g l)]
    exact (h_act i g l s).symm
  -- Apply h_lin at z := e v and reduce.
  have h := LinearMap.congr_fun h_lin (e v)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [show (e.symm : _ →ₗ[k] _) (e v) = v from e.symm_apply_apply v] at h
  rw [show (e.symm : _ →ₗ[k] _) ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) =
    e.symm ((Representation.directSum (fun i =>
      (Representation.trivial k (Matrix.GeneralLinearGroup (Fin N) k)
        (↥(S' i))).tprod (L i).ρ) g) (e v)) from rfl] at h
  exact (LinearEquiv.eq_symm_apply e).mp h

/-- **`M` embeds `R`-linearly as a submodule of a finite direct sum of the
abstract simple summands `L i`.**

Bundles three steps into the single form consumed by the isotypic engine:

1. `polynomial_homog_rep_equivariant_embedding` (#4598): the `GL_N`-equivariant
   `k`-linear embedding `M ↪ (V^{⊗n})^m`.
2. `glTensorRep_schurWeyl_decomposition_equivariant_simple`: the ambient
   `V^{⊗n}` (hence `(V^{⊗n})^m`) decomposes equivariantly into the simple
   `L i`, with multiplicities (each `S i ⊗ L i` is `dim(S i)` copies of `L i`).
3. The `asModule` transfer: a `GL_N`-equivariant `k`-linear map is exactly a
   `MonoidAlgebra k GL_N`-linear map between the `asModule`s.

The output exposes an index `κ`, a map `g : κ → ι` recording which simple each
ambient summand is, an `R`-linear identification `e` of the ambient
`(V^{⊗n})^m`-module with `⨁_{c : κ} asModule (L (g c))`, and a submodule `M'`
of that ambient module together with an `R`-linear iso `asModule M.ρ ≃ M'`.

TODO (sub-issue of #2482): supply the `asModule` transfer glue and the
`Fin m`-fold product / `S ⊗ L` splitting. -/
theorem polynomial_homog_rep_asModule_embeds_directSum_simple
    [IsAlgClosed k] [CharZero k] (n : ℕ) (hN : n ≤ N)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (GLAlg k N) (Representation.asModule (L i).ρ))
      (κ : Type) (_ : Finite κ) (gκ : κ → ι)
      (W : Type u) (_ : AddCommGroup W) (_ : Module (GLAlg k N) W)
      (_ : W ≃ₗ[GLAlg k N]
        DirectSum κ (fun c => Representation.asModule (L (gκ c)).ρ))
      (M' : Submodule (GLAlg k N) W),
      Nonempty (Representation.asModule M.ρ ≃ₗ[GLAlg k N] M') :=
  sorry

/-- **A polynomial `GL_N`-representation is a direct sum of abstract simple
summands of `V^{⊗n}`** (Schur-Weyl #5, Step E, issue #2482).

Let `M` be a finite-dimensional algebraic `GL_N(k)`-representation all of whose
weight spaces are concentrated in total degree `n`. Then `M` decomposes, as a
`MonoidAlgebra k GL_N`-module (i.e. `GL_N`-equivariantly), as a finite direct
sum of the abstract simple summands `L i` of `V^{⊗n}`:
`M.asModule ≃ ⨁_{j : Fin p} (L (f j)).asModule`.

Reading off `mult i := Nat.card {j // f j = i}` recovers the
multiplicity-indexed form `M ≅ ⨁_i (Fin (mult i) → L i)`. The decomposition is
stated for the *abstract* `L i` (not concrete Schur modules) to keep the
dependency graph with the consumer #6 acyclic. -/
theorem decompose_polynomial_gl_rep
    [IsAlgClosed k] [CharZero k] (n : ℕ) (hN : n ≤ N)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (L : ι → FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
      (_ : ∀ i, IsSimpleModule (GLAlg k N) (Representation.asModule (L i).ρ))
      (p : ℕ) (f : Fin p → ι),
      Nonempty (Representation.asModule M.ρ ≃ₗ[GLAlg k N]
        DirectSum (Fin p) (fun j => Representation.asModule (L (f j)).ρ)) := by
  classical
  -- Embed `M.asModule` as a submodule `M'` of an ambient module `W` that is
  -- `R`-linearly a finite direct sum of the simple `L (gκ c)`.
  obtain ⟨ι, hιFin, hιDec, L, hLsimp, κ, hκFin, gκ, W, hWacg, hWmod, e, M', ⟨eM⟩⟩ :=
    polynomial_homog_rep_asModule_embeds_directSum_simple k N n hN M halg h_homog
  -- The ambient summand family, indexed by `κ`.
  set Lsum : κ → Type u := fun c => Representation.asModule (L (gκ c)).ρ with hLsum
  haveI : ∀ c, IsSimpleModule (GLAlg k N) (Lsum c) := fun c => hLsimp (gκ c)
  -- Apply the generic isotypic-extraction engine (#4600) to the submodule `M'`.
  obtain ⟨p, h, ⟨eM'⟩⟩ :=
    SemisimpleIsotypic.submodule_of_directSum_simple_iso_directSum
      (R := GLAlg k N) Lsum (fun c => hLsimp (gκ c)) e M'
  -- Compose: `M.asModule ≃ M' ≃ ⨁_{j} Lsum (h j) = ⨁_{j} asModule (L (gκ (h j)))`.
  refine ⟨ι, hιFin, hιDec, L, hLsimp, p, fun j => gκ (h j), ⟨?_⟩⟩
  exact eM.trans eM'

end Etingof.PolynomialGLDecomposition
