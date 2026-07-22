import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialGLDecomposition
import EtingofRepresentationTheory.Chapter5.PolynomialWeightSaturation
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso

/-!
# A general polynomial `GL_N`-representation is semisimple (Schur-Weyl #5, steps 2-4)

`decompose_polynomial_gl_rep` (`PolynomialGLDecomposition.lean`) proves
`GL_N`-equivariant complete reducibility — hence
`IsSemisimpleModule (GLAlg k N) M.asModule` — for a *weight-homogeneous* polynomial
algebraic rep (hypotheses `h_span` + `h_homog`).

This file removes the homogeneity hypothesis: a *general* polynomial representation
`M` (with `IsPolynomialRepresentation N M.ρ`) is semisimple. The reduction groups
`M`'s weight spaces by total degree `d = ∑ᵢ μ i`. Each total-degree component `M_d`
is the `t₀^d`-eigenspace of the central scalar operator `M.ρ (scalarGL t₀)` (for a
fixed `t₀` of infinite multiplicative order, available in characteristic zero), hence
a `GL_N`-stable subrepresentation; it is polynomial and weight-homogeneous of degree
`d`, so `decompose_polynomial_gl_rep` makes it semisimple. `M` is the (finite) direct
sum of the `M_d`, and a sum of semisimple submodules is semisimple.

Book: Etingof §5.23(i), `blobs/Chapter5/Discussion_proof_of_Theorem5.23.2.md`.
-/

open CategoryTheory
open scoped TensorProduct DirectSum

noncomputable section

namespace Etingof.PolynomialGLSemisimple

open Etingof Etingof.PolynomialRepEmbedding Etingof.PolynomialGLDecomposition

/-! ## A general lattice lemma -/

/-- If `T i ≤ E i` pointwise, the `E i` are sup-independent, and the `T i` already
sup to `⊤`, then `T i = E i` for every `i`. (Modular-lattice "filling" argument:
`E i ≤ ⊤ = ⨆ T j ≤ T i ⊔ ⨆_{j≠i} E j`, then modularity + independence collapse the
extra summand.) -/
theorem eq_of_le_iSupIndep_iSup_top
    {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {ι : Type*} {T E : ι → Submodule R M}
    (hle : ∀ i, T i ≤ E i) (hE : iSupIndep E) (hT : ⨆ i, T i = ⊤) (i : ι) :
    T i = E i := by
  refine le_antisymm (hle i) ?_
  have hcover : E i ≤ T i ⊔ ⨆ (j) (_ : j ≠ i), E j := by
    calc E i ≤ ⊤ := le_top
      _ = ⨆ j, T j := hT.symm
      _ ≤ T i ⊔ ⨆ (j) (_ : j ≠ i), E j := by
          refine iSup_le (fun j => ?_)
          by_cases hj : j = i
          · subst hj; exact le_sup_left
          · exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le hj (hle j)))
  have hstep : E i = (T i ⊔ ⨆ (j) (_ : j ≠ i), E j) ⊓ E i := (inf_eq_right.mpr hcover).symm
  rw [hstep, sup_inf_assoc_of_le _ (hle i), inf_comm, (hE i).eq_bot, sup_bot_eq]

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)

/-! ## The homogeneous case -/

/-- A weight-homogeneous polynomial algebraic `GL_N`-representation is semisimple.
This packages `decompose_polynomial_gl_rep` (which decomposes such an `M` as a finite
direct sum of *simple* `GLAlg`-modules) with the fact that a direct sum of simple
modules is semisimple. -/
theorem polynomialHomogRep_isSemisimple (n : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    IsSemisimpleModule (GLAlg k N) (Representation.asModule M.ρ) := by
  obtain ⟨ι, _, _, S, _, _, _, L, hLsimp, _, _, e, he, p, f, ⟨eM⟩⟩ :=
    decompose_polynomial_gl_rep k N n M halg h_span h_homog
  haveI : ∀ j : Fin p, IsSimpleModule (GLAlg k N) (Representation.asModule (L (f j)).ρ) :=
    fun j => hLsimp (f j)
  haveI : ∀ j : Fin p, IsSemisimpleModule (GLAlg k N) (Representation.asModule (L (f j)).ρ) :=
    fun j => inferInstance
  haveI : IsSemisimpleModule (GLAlg k N)
      (DirectSum (Fin p) (fun j => Representation.asModule (L (f j)).ρ)) :=
    inferInstanceAs (IsSemisimpleModule (GLAlg k N)
      (Π₀ j : Fin p, Representation.asModule (L (f j)).ρ))
  exact IsSemisimpleModule.congr eM

/-! ## A central scalar of infinite order -/

/-- A fixed unit of infinite multiplicative order (characteristic zero): `2`. -/
def t0 : kˣ := Units.mk0 (2 : k) two_ne_zero

theorem t0_val : (t0 k : k) = 2 := rfl

theorem t0_pow_injective : Function.Injective (fun d : ℕ => (t0 k : k) ^ d) := by
  intro a b hab
  simp only [t0_val] at hab
  have h : ((2 ^ a : ℕ) : k) = ((2 ^ b : ℕ) : k) := by push_cast; exact hab
  exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h)

/-- The scalar matrix `t • 1` is central in `GL_N(k)`. -/
theorem scalarGL_central (t : kˣ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    scalarGL k N t * g = g * scalarGL k N t := by
  apply Units.ext
  change (scalarGL k N t).val * (g : Matrix (Fin N) (Fin N) k)
      = (g : Matrix (Fin N) (Fin N) k) * (scalarGL k N t).val
  have hval : (scalarGL k N t).val = Matrix.scalar (Fin N) (t : k) := by
    rw [Matrix.scalar_apply]; rfl
  rw [hval]
  exact Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) (g : Matrix (Fin N) (Fin N) k)

/-- `scalarGL t = ∏ᵢ diagUnit i t` (copied from the `private`
`PolynomialRepEmbedding.scalarGL_eq_noncommProd`). -/
theorem scalarGL_eq_noncommProd' (t : kˣ) :
    scalarGL k N t
      = Finset.univ.noncommProd (fun i => diagUnit k N i t)
          (fun i _ j _ _ => diagUnit_comm k N i t j t) := by
  apply Units.ext
  have gen : ∀ (s : Finset (Fin N))
      (comm : (↑s : Set (Fin N)).Pairwise
        fun a b => Commute (diagUnit k N a t) (diagUnit k N b t)),
      (s.noncommProd (fun i => diagUnit k N i t) comm).val
        = Matrix.diagonal (fun j => if j ∈ s then (t : k) else 1) := by
    intro s
    induction s using Finset.induction with
    | empty => intro comm; simp [Matrix.diagonal_one]
    | @insert a s ha ih =>
        intro comm
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Units.val_mul, ih]
        change Matrix.diagonal (Function.update (1 : Fin N → k) a (t : k))
            * Matrix.diagonal (fun j => if j ∈ s then (t : k) else 1)
            = Matrix.diagonal (fun j => if j ∈ insert a s then (t : k) else 1)
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext j
        by_cases hja : j = a
        · subst hja; simp [Function.update_self, ha]
        · rw [Function.update_of_ne hja]; simp [Finset.mem_insert, hja]
  rw [gen Finset.univ]
  change Matrix.diagonal (fun _ => (t : k))
      = Matrix.diagonal (fun j => if j ∈ (Finset.univ : Finset (Fin N)) then (t : k) else 1)
  simp

/-- On the weight space for `μ`, the central scalar `scalarGL t₀` acts by `t₀^(∑μ)`;
hence the weight space is contained in the `t₀^(∑μ)`-eigenspace. -/
theorem glWeightSpace_le_scalar_eigenspace
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k)) (μ : Fin N →₀ ℕ) :
    glWeightSpace k N M (fun i => μ i)
      ≤ Module.End.eigenspace (M.ρ (scalarGL k N (t0 k))) ((t0 k : k) ^ (∑ i, μ i)) := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff]
  have heig : ∀ i : Fin N, M.ρ (diagUnit k N i (t0 k)) x = ((t0 k : k) ^ μ i) • x := by
    intro i
    have hmem : x ∈ glWeightSpace k N M (fun j => μ j) := hx
    rw [glWeightSpace, Submodule.mem_iInf] at hmem
    have h2 := (Submodule.mem_iInf _).1 (hmem i) (t0 k)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
      LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2
  have act : ∀ (s : Finset (Fin N))
      (comm : (↑s : Set (Fin N)).Pairwise
        fun a b => Commute (M.ρ (diagUnit k N a (t0 k))) (M.ρ (diagUnit k N b (t0 k)))),
      (s.noncommProd (fun i => M.ρ (diagUnit k N i (t0 k))) comm) x
        = (∏ i ∈ s, (t0 k : k) ^ μ i) • x := by
    intro s
    induction s using Finset.induction with
    | empty => intro comm; simp
    | @insert a s ha ih =>
        intro comm
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Module.End.mul_apply, ih,
          Finset.prod_insert ha, map_smul, heig a, smul_smul, mul_comm]
  rw [scalarGL_eq_noncommProd', Finset.map_noncommProd, act Finset.univ,
    Finset.prod_pow_eq_pow_sum]

/-! ## The total-degree grading -/

variable (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))

/-- The total-degree-`d` component: the sup of all weight spaces of total degree `d`. -/
abbrev degComponent (d : ℕ) : Submodule k M :=
  ⨆ (μ : Fin N →₀ ℕ) (_ : ∑ i, μ i = d), glWeightSpace k N M (fun i => μ i)

/-- The `t₀^d`-eigenspace of the central scalar operator `M.ρ (scalarGL t₀)`. -/
abbrev scalarEigenComp (d : ℕ) : Submodule k M :=
  Module.End.eigenspace (M.ρ (scalarGL k N (t0 k))) ((t0 k : k) ^ d)

theorem degComponent_le_scalarEigen (d : ℕ) :
    degComponent k N M d ≤ scalarEigenComp k N M d := by
  refine iSup₂_le (fun μ hμ => ?_)
  have h := glWeightSpace_le_scalar_eigenspace k N M μ
  rwa [hμ] at h

theorem scalarEigen_iSupIndep : iSupIndep (scalarEigenComp k N M) :=
  (Module.End.eigenspaces_iSupIndep (M.ρ (scalarGL k N (t0 k)))).comp (t0_pow_injective k)

theorem iSup_degComponent
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ d : ℕ, degComponent k N M d = ⊤ := by
  rw [← h_span]
  apply le_antisymm
  · exact iSup_le (fun _ => iSup₂_le (fun μ _ =>
      le_iSup (fun ν : Fin N →₀ ℕ => glWeightSpace k N M (fun i => ν i)) μ))
  · exact iSup_le (fun μ => le_iSup_of_le (∑ i, μ i) (le_iSup₂_of_le μ rfl le_rfl))

theorem degComponent_eq_scalarEigen
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    degComponent k N M d = scalarEigenComp k N M d :=
  eq_of_le_iSupIndep_iSup_top (degComponent_le_scalarEigen k N M)
    (scalarEigen_iSupIndep k N M) (iSup_degComponent k N M h_span) d

/-- The total-degree component is `GL_N`-stable: it is an eigenspace of the central
scalar operator, which commutes with every `M.ρ g`. -/
theorem degComponent_stable
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (d : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ∀ x ∈ degComponent k N M d, M.ρ g x ∈ degComponent k N M d := by
  intro x hx
  rw [degComponent_eq_scalarEigen k N M h_span] at hx ⊢
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hcomm : M.ρ (scalarGL k N (t0 k)) (M.ρ g x) = M.ρ g (M.ρ (scalarGL k N (t0 k)) x) := by
    have hmul : M.ρ (scalarGL k N (t0 k)) * M.ρ g = M.ρ g * M.ρ (scalarGL k N (t0 k)) := by
      rw [← map_mul, ← map_mul, scalarGL_central]
    have := LinearMap.congr_fun hmul x
    rwa [Module.End.mul_apply, Module.End.mul_apply] at this
  rw [hcomm, hx, map_smul]

/-- The total-degree-`d` component as a subrepresentation of `M`. -/
def degSubrep
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    Subrepresentation M.ρ where
  toSubmodule := degComponent k N M d
  apply_mem_toSubmodule g v hv := degComponent_stable k N M h_span d g v hv

/-! ## Weight spaces of a subrepresentation -/

/-- The weight space of the restriction of `M` to a `GL_N`-stable submodule `σ` is the
preimage (`comap`) of the weight space of `M`. -/
theorem glWeightSpace_restrict (σ : Subrepresentation M.ρ) (μ : Fin N → ℕ) :
    glWeightSpace k N (FDRep.of σ.toRepresentation) μ
      = Submodule.comap σ.toSubmodule.subtype (glWeightSpace k N M μ) := by
  unfold glWeightSpace
  rw [Submodule.comap_iInf]
  refine iInf_congr (fun i => ?_)
  rw [Submodule.comap_iInf]
  refine iInf_congr (fun t => ?_)
  ext x
  have key : (((FDRep.of σ.toRepresentation).ρ (diagUnit k N i t)) x : M)
      = M.ρ (diagUnit k N i t) (x : M) := rfl
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.id_apply, Submodule.coe_subtype, Subtype.ext_iff, ZeroMemClass.coe_zero,
    Submodule.coe_sub, Submodule.coe_smul, key]

/-! ## Each total-degree component is semisimple -/

/-- Algebraicity of the restriction to the total-degree component. -/
theorem degSubrep_isAlgebraic
    (hpoly : IsPolynomialRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    Etingof.IsAlgebraicRepresentation N (FDRep.of (degSubrep k N M h_span d).toRepresentation).ρ :=
  (hpoly.isAlgebraic).restrict (degSubrep k N M h_span d).toSubmodule
    (fun g v hv => (degSubrep k N M h_span d).apply_mem_toSubmodule g hv)

/-- The restriction to the total-degree-`d` component is weight-homogeneous of degree `d`. -/
theorem degSubrep_h_homog
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) (d : ℕ)
    (μ : Fin N → ℕ)
    (hne : glWeightSpace k N (FDRep.of (degSubrep k N M h_span d).toRepresentation) μ ≠ ⊥) :
    ∑ i, μ i = d := by
  by_contra hsum
  apply hne
  rw [glWeightSpace_restrict]
  -- weight space `μ` is disjoint from the degree-`d` component
  set ν : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm μ with hν
  have hνμ : (fun i => ν i) = μ := by funext i; simp [hν]
  have hsumν : ∑ i, ν i = ∑ i, μ i := by rw [hνμ]
  have hdis : Disjoint (glWeightSpace k N M (fun i => ν i))
      (degComponent k N M d) := by
    have hindep := glWeightSpace_iSupIndep k N M
    refine Disjoint.mono_right ?_ (hindep ν)
    refine iSup₂_le (fun ξ hξ => ?_)
    refine le_iSup₂_of_le ξ ?_ le_rfl
    intro h
    rw [h] at hξ
    exact hsum (hsumν ▸ hξ)
  rw [eq_bot_iff]
  rintro ⟨y, hymem⟩ hy
  rw [Submodule.mem_comap, Submodule.coe_subtype] at hy
  rw [hνμ] at hdis
  have hzero : y = 0 := hdis.le_bot (Submodule.mem_inf.mpr ⟨hy, hymem⟩)
  exact (Submodule.mem_bot k).mpr (Subtype.ext hzero)

/-- The restriction to the total-degree-`d` component is spanned by its weight spaces. -/
theorem degSubrep_h_span
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    ⨆ (μ : Fin N →₀ ℕ),
        glWeightSpace k N (FDRep.of (degSubrep k N M h_span d).toRepresentation) (fun i => μ i)
      = ⊤ := by
  simp_rw [glWeightSpace_restrict]
  apply Submodule.map_injective_of_injective (Submodule.subtype_injective _)
  rw [Submodule.map_iSup, Submodule.map_subtype_top]
  simp_rw [Submodule.map_comap_subtype]
  apply le_antisymm
  · exact iSup_le (fun _ => inf_le_left)
  · change degComponent k N M d ≤ _
    refine iSup₂_le (fun ξ hξ => ?_)
    have hle : glWeightSpace k N M (fun i => ξ i) ≤ degComponent k N M d :=
      le_iSup₂_of_le ξ hξ le_rfl
    calc glWeightSpace k N M (fun i => ξ i)
        = degComponent k N M d ⊓ glWeightSpace k N M (fun i => ξ i) := (inf_eq_right.mpr hle).symm
      _ ≤ ⨆ μ : Fin N →₀ ℕ, degComponent k N M d ⊓ glWeightSpace k N M (fun i => μ i) :=
          le_iSup
            (fun ν : Fin N →₀ ℕ => degComponent k N M d ⊓ glWeightSpace k N M (fun i => ν i)) ξ

/-- The `GLAlg`-module `↥(asSubmodule σ)` is semisimple if the restricted representation
`σ.toRepresentation` is. -/
theorem asSubmodule_semisimple_of_toRep
    {G W : Type*} [Monoid G] [AddCommGroup W] [Module k W]
    {ρ : Representation k G W} (σ : Subrepresentation ρ)
    (h : IsSemisimpleModule (MonoidAlgebra k G) σ.toRepresentation.asModule) :
    IsSemisimpleModule (MonoidAlgebra k G) (Subrepresentation.asSubmodule σ) := by
  haveI := h
  have hf : ∀ (g : G) (x : σ.toSubmodule),
      σ.toSubmodule.subtype (σ.toRepresentation g x) = ρ g (σ.toSubmodule.subtype x) :=
    fun _ _ => rfl
  let F := Representation.asModuleHomOfIntertwiner (ρ := σ.toRepresentation) (σ := ρ)
    σ.toSubmodule.subtype hf
  have hFinj : Function.Injective F := by
    intro a b hab
    refine Subtype.coe_injective ?_
    simpa [F, Representation.asModuleHomOfIntertwiner_apply] using hab
  have hrange : LinearMap.range F = Subrepresentation.asSubmodule σ := by
    apply SetLike.ext
    intro y
    simp only [LinearMap.mem_range, Subrepresentation.mem_asSubmodule_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact x.2
    · intro hy; exact ⟨⟨y, hy⟩, rfl⟩
  have e : σ.toRepresentation.asModule ≃ₗ[MonoidAlgebra k G] Subrepresentation.asSubmodule σ :=
    (LinearEquiv.ofInjective F hFinj).trans (LinearEquiv.ofEq _ _ hrange)
  exact IsSemisimpleModule.congr e.symm

theorem degSubrep_asSubmodule_semisimple
    (hpoly : IsPolynomialRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) (d : ℕ) :
    IsSemisimpleModule (GLAlg k N)
      (Subrepresentation.asSubmodule (degSubrep k N M h_span d)) := by
  have hss : IsSemisimpleModule (GLAlg k N)
      (Representation.asModule (FDRep.of (degSubrep k N M h_span d).toRepresentation).ρ) :=
    polynomialHomogRep_isSemisimple k N d (FDRep.of (degSubrep k N M h_span d).toRepresentation)
      (degSubrep_isAlgebraic k N M hpoly h_span d)
      (degSubrep_h_span k N M h_span d)
      (degSubrep_h_homog k N M h_span d)
  exact asSubmodule_semisimple_of_toRep (k := k) (degSubrep k N M h_span d) hss

/-! ## Main theorem -/

/-- The total-degree components cover `M`. -/
theorem restrictScalars_asSubmodule (σ : Subrepresentation M.ρ) :
    (Subrepresentation.asSubmodule σ).restrictScalars k = σ.toSubmodule := rfl

theorem iSup_asSubmodule_degSubrep
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ⨆ d : ℕ, Subrepresentation.asSubmodule (degSubrep k N M h_span d) = ⊤ := by
  have h1 : (⨆ d : ℕ, Subrepresentation.asSubmodule (degSubrep k N M h_span d)).restrictScalars k
      = ⊤ := by
    refine top_unique ?_
    calc (⊤ : Submodule k M)
        = ⨆ d : ℕ, degComponent k N M d := (iSup_degComponent k N M h_span).symm
      _ ≤ (⨆ d : ℕ, Subrepresentation.asSubmodule (degSubrep k N M h_span d)).restrictScalars k := by
          refine iSup_le (fun d => ?_)
          calc degComponent k N M d
              = (Subrepresentation.asSubmodule (degSubrep k N M h_span d)).restrictScalars k :=
                (restrictScalars_asSubmodule k N M (degSubrep k N M h_span d)).symm
            _ ≤ (⨆ d : ℕ,
                  Subrepresentation.asSubmodule (degSubrep k N M h_span d)).restrictScalars k :=
                Submodule.restrictScalars_mono (S := k)
                  (le_iSup (fun d => Subrepresentation.asSubmodule (degSubrep k N M h_span d)) d)
  have h2 := Submodule.restrictScalars_injective k (GLAlg k N) (Representation.asModule M.ρ)
  apply h2
  rw [h1, Submodule.restrictScalars_top]

/-- **A general polynomial `GL_N`-representation is semisimple** (Etingof §5.23(i),
the general case beyond the weight-homogeneous `decompose_polynomial_gl_rep`).

`M` is the finite direct sum of its total-degree components, each of which is a
weight-homogeneous polynomial subrepresentation and so semisimple by
`polynomialHomogRep_isSemisimple`; a sum of semisimple submodules is semisimple. -/
theorem polynomialRep_isSemisimple
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hpoly : IsPolynomialRepresentation N M.ρ) :
    IsSemisimpleModule (GLAlg k N) (Representation.asModule M.ρ) := by
  have h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤ :=
    polynomial_rep_iSup_glWeightSpace_eq_top M hpoly
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun d => Subrepresentation.asSubmodule (degSubrep k N M h_span d))
    (fun d => degSubrep_asSubmodule_semisimple k N M hpoly h_span d)
    (iSup_asSubmodule_degSubrep k N M h_span)

end Etingof.PolynomialGLSemisimple
