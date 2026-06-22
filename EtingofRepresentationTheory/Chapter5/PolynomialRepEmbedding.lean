import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialTensorBridge
import EtingofRepresentationTheory.Chapter5.Definition5_23_1
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.EvalEqOnGL
import EtingofRepresentationTheory.Chapter5.DetInvElim

/-!
# Polynomial GL_N-rep embedding into a tensor power (Schur-Weyl #2b)

Etingof §5.23. A finite-dimensional polynomial GL_N-representation `M` whose
matrix coefficients are homogeneous polynomials of degree `n` in the matrix
entries `g_ij` admits a `k`-linear injection into `(V^⊗n)^m` for some `m`,
where `V := Fin N → k`.

The construction uses
`Etingof.PolynomialTensorBridge.homogeneousPolyToTensor` (Schur-Weyl #2a) to
realize each matrix-coefficient polynomial as an element of
`V^⊗n ⊗ (V^*)^⊗n`, then splits off the `(V^*)^⊗n` factor via the standard
basis to land in `(V^⊗n)^m`.

## Status

This file lands the **injection** part of the deliverable from issue #2478:
`polynomialRep_embeds_in_tensorPower_inj` exhibits `m`, the linear map `φ`,
and proves injectivity. **GL_N-equivariance** of `φ` is deferred to a sibling
issue, since the equivariance proof requires equivariance of the underlying
bridge `homogeneousPolyToTensor` for the right-translation action on
polynomials versus `g ↦ g^⊗n ⊗ 1` on the tensor target — itself a substantial
chunk that the bridge file (`Chapter5/PolynomialTensorBridge.lean`) explicitly
defers.

## Main result

* `Etingof.PolynomialRepEmbedding.polynomialRep_embeds_in_tensorPower_inj` —
  the linear injection of a hom-degree-`n` polynomial GL_N-rep into
  `(V^⊗n)^m`.
-/

open scoped TensorProduct
open MvPolynomial

namespace Etingof

namespace PolynomialRepEmbedding

universe u

open PolynomialTensorBridge

variable (k : Type u) [Field k] (N n : ℕ)

/-- Splitting the right `(V^*)^⊗n` factor of `V^⊗n ⊗ (V^*)^⊗n` via the
standard basis: `V^⊗n ⊗ (V^*)^⊗n ≃ₗ[k] (Fin n → Fin N) → V^⊗n`. The
GL_N-action on `(V^*)^⊗n` is *not* used here; we are merely splitting the
target of the bridge into a `Fin (N^n)`-indexed direct sum of `V^⊗n`-copies. -/
noncomputable def splitDualBasis :
    PolyTensorTgt k N n ≃ₗ[k] ((Fin n → Fin N) → TensorPower k (StdV k N) n) :=
  let bDual : Module.Basis (Fin n → Fin N) k
      (TensorPower k (Module.Dual k (StdV k N)) n) :=
    Basis.piTensorProduct (fun _ : Fin n => stdDualBasis k N)
  LinearEquiv.lTensor _ bDual.equivFun ≪≫ₗ
    TensorProduct.piScalarRight k k _ (Fin n → Fin N)

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The matrix coefficient polynomial for row `a` of `x ∈ M`, in basis `b`,
given polynomial witnesses `P a c`: `x ↦ Σ_c (b.coord c x) • P a c`. -/
noncomputable def matrixCoeffPoly {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k) (a : Fin d) :
    M →ₗ[k] MvPolynomial (Fin N × Fin N) k :=
  ∑ c : Fin d, LinearMap.smulRight (b.coord c) (P a c)

@[simp]
lemma matrixCoeffPoly_apply {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k) (a : Fin d) (x : M) :
    matrixCoeffPoly k N b P a x = ∑ c : Fin d, (b.coord c x) • P a c := by
  unfold matrixCoeffPoly
  rw [LinearMap.sum_apply]
  rfl

/-- A `k`-linear combination of homogeneous degree-`n` polynomials is itself
homogeneous of degree `n`. -/
lemma matrixCoeffPoly_mem_homogeneous {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) (x : M) :
    matrixCoeffPoly k N b P a x ∈
      MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n := by
  rw [matrixCoeffPoly_apply]
  refine Submodule.sum_mem _ ?_
  intro c _
  exact Submodule.smul_mem _ _ (hhom a c)

/-- For a single endomorphism `T : M →ₗ[k] M` whose matrix coefficients in
basis `b` agree with `MvPolynomial.eval s ∘ P` (at a fixed evaluation `s`),
evaluating the matrix-coefficient polynomial at `s` recovers the row-`a`
coordinate of `T x`. This is the matrix-coefficient identity on the level of
generic `x`, deduced from the case `x = b c` via `k`-linearity. -/
lemma eval_matrixCoeffPoly {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (T : M →ₗ[k] M) (s : Fin N × Fin N → k)
    (hP : ∀ a c, b.coord a (T (b c)) = MvPolynomial.eval s (P a c))
    (a : Fin d) (x : M) :
    MvPolynomial.eval s (matrixCoeffPoly k N b P a x) = b.coord a (T x) := by
  classical
  rw [matrixCoeffPoly_apply, map_sum]
  -- T x = Σ_c (b.coord c x) • b c
  have hx_repr : x = ∑ c : Fin d, b.coord c x • b c := by
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Module.Basis.coord_apply]
  -- b.coord a (T x) = Σ_c (b.coord c x) * b.coord a (T (b c))
  conv_rhs => rw [hx_repr, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  -- LHS term: eval s ((b.coord c x) • P a c) = (b.coord c x) * eval s (P a c)
  rw [MvPolynomial.smul_eval]
  -- RHS term: b.coord a (T ((b.coord c x) • b c)) =
  --   (b.coord c x) * b.coord a (T (b c))
  rw [show T ((b.coord c) x • b c) = (b.coord c) x • T (b c) from
        T.map_smul _ _,
      show (b.coord a) ((b.coord c) x • T (b c)) =
             (b.coord c) x • (b.coord a) (T (b c)) from
        (b.coord a).map_smul _ _,
      smul_eq_mul, hP]

/-- Bridge each row `a` of the matrix-coefficient polynomial to
`V^⊗n ⊗ (V^*)^⊗n` via `homogeneousPolyToTensor` (Schur-Weyl #2a). -/
noncomputable def polyTensorRow {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) :
    M →ₗ[k] PolyTensorTgt k N n :=
  (homogeneousPolyToTensor k N n).comp <|
    LinearMap.codRestrict
      (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
      (matrixCoeffPoly k N b P a)
      (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)

lemma polyTensorRow_eq_zero_iff {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (a : Fin d) (x : M) :
    polyTensorRow k N n b P hhom a x = 0 ↔ matrixCoeffPoly k N b P a x = 0 := by
  unfold polyTensorRow
  rw [LinearMap.comp_apply,
    show ((homogeneousPolyToTensor k N n)
            (LinearMap.codRestrict
              (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
              (matrixCoeffPoly k N b P a)
              (matrixCoeffPoly_mem_homogeneous k N n b P hhom a) x) = 0) ↔
          (LinearMap.codRestrict
              (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
              (matrixCoeffPoly k N b P a)
              (matrixCoeffPoly_mem_homogeneous k N n b P hhom a) x = 0) from
      ⟨fun h => (homogeneousPolyToTensor_injective k N n)
        (h.trans (map_zero _).symm),
       fun h => h ▸ map_zero _⟩]
  -- Now: codRestrict ... x = 0 ↔ matrixCoeffPoly ... x = 0
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg Subtype.val h
    simpa [LinearMap.codRestrict] using this
  · apply Subtype.ext
    simpa [LinearMap.codRestrict] using h

/-- The bundled embedding: `M →ₗ[k] (Fin d × (Fin n → Fin N)) → V^⊗n`. -/
noncomputable def polyTensorBundle {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) :
    M →ₗ[k] (Fin d × (Fin n → Fin N) → TensorPower k (StdV k N) n) :=
  LinearMap.pi fun p =>
    ((LinearMap.proj p.2 : ((Fin n → Fin N) → TensorPower k (StdV k N) n) →ₗ[k]
        TensorPower k (StdV k N) n).comp
      ((splitDualBasis k N n).toLinearMap.comp
        (polyTensorRow k N n b P hhom p.1)))

lemma polyTensorBundle_apply {d : ℕ} [CharZero k]
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n) (x : M)
    (p : Fin d × (Fin n → Fin N)) :
    polyTensorBundle k N n b P hhom x p =
      (splitDualBasis k N n) (polyTensorRow k N n b P hhom p.1 x) p.2 := by
  rfl

/-- **Polynomial GL_N-rep embeds in tensor power** (Etingof §5.23,
Schur-Weyl #2b — injection part).

A finite-dimensional polynomial GL_N-representation `M`, presented by a basis
and matrix-coefficient polynomial witnesses that are homogeneous of degree `n`
in the matrix entries `g_ij` (with no `det⁻¹` factor), admits a `k`-linear
injection into `(V^⊗n)^m` for some `m`, where `V := Fin N → k`.

The construction is via the bridge `homogeneousPolyToTensor` from Schur-Weyl
#2a: each row `a` of the matrix-coefficient polynomial of `x ∈ M` is a
homogeneous degree-`n` polynomial; bridge it to `V^⊗n ⊗ (V^*)^⊗n`, then split
off the dual factor via the standard basis to land in
`(Fin n → Fin N) → V^⊗n`. Bundle over the `Fin d`-many basis indices.

GL_N-equivariance of the embedding is **not** stated here; it is deferred to a
sibling issue together with equivariance of the underlying bridge.

(Etingof Definition 5.23.1 + Theorem 5.23.2 setup. Issue #2478.) -/
theorem polynomialRep_embeds_in_tensorPower_inj
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (_halg : IsAlgebraicRepresentation N (ρ : _ → _))
    (hpoly : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
      Function.Injective φ := by
  classical
  obtain ⟨d, b, P, hhom, hP⟩ := hpoly
  -- Re-index Fin d × (Fin n → Fin N) ≃ Fin m
  let m := Fintype.card (Fin d × (Fin n → Fin N))
  let e : Fin d × (Fin n → Fin N) ≃ Fin m := Fintype.equivFin _
  let reindex :
      (Fin d × (Fin n → Fin N) → TensorPower k (StdV k N) n) ≃ₗ[k]
        (Fin m → TensorPower k (StdV k N) n) :=
    LinearEquiv.piCongrLeft k (fun _ : Fin m => TensorPower k (StdV k N) n) e
  let φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n) :=
    reindex.toLinearMap.comp (polyTensorBundle k N n b P hhom)
  refine ⟨m, φ, ?_⟩
  -- Injectivity: kernel of φ is trivial.
  rw [show Function.Injective φ ↔ Function.Injective (polyTensorBundle k N n b P hhom) from
    by simp [φ, LinearMap.coe_comp, reindex.injective.of_comp_iff]]
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  -- hx : polyTensorBundle ... x = 0 (function on Fin d × (Fin n → Fin N))
  -- For each (a, j), polyTensorBundle x (a, j) = 0.
  have hx_pt : ∀ p : Fin d × (Fin n → Fin N),
      polyTensorBundle k N n b P hhom x p = 0 :=
    fun p => congrFun hx p
  -- For each a, splitDualBasis (polyTensorRow a x) = 0 (function on (Fin n → Fin N)).
  have hx_split : ∀ a : Fin d,
      (splitDualBasis k N n) (polyTensorRow k N n b P hhom a x) = 0 := by
    intro a
    funext j
    have := hx_pt (a, j)
    rw [polyTensorBundle_apply] at this
    simpa using this
  -- splitDualBasis is a LinearEquiv; hence polyTensorRow a x = 0 for each a.
  have hx_row : ∀ a : Fin d, polyTensorRow k N n b P hhom a x = 0 :=
    fun a => (splitDualBasis k N n).map_eq_zero_iff.mp (hx_split a)
  -- Hence matrixCoeffPoly k N b P a x = 0 for each a.
  have hx_poly : ∀ a : Fin d, matrixCoeffPoly k N b P a x = 0 :=
    fun a => (polyTensorRow_eq_zero_iff k N n b P hhom a x).mp (hx_row a)
  -- Translate to: ρ g x has zero coordinates in basis b, for every g.
  have hcoord_zero : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d),
      b.coord a (ρ g x) = 0 := by
    intro g a
    have hP_g : ∀ a' c', b.coord a' ((ρ g) (b c')) =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a' c') := by
      intro a' c'
      have h := hP g a' c'
      rwa [Module.Basis.coord_apply]
    have h := eval_matrixCoeffPoly k N b P (ρ g)
      (fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) hP_g a x
    rw [hx_poly a, map_zero] at h
    exact h.symm
  -- Hence ρ g x = 0 for every g.
  have hρ_zero : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ρ g x = 0 := by
    intro g
    apply b.repr.injective
    ext a
    rw [LinearEquiv.map_zero, Finsupp.zero_apply]
    have := hcoord_zero g a
    rwa [Module.Basis.coord_apply] at this
  -- Set g = 1: ρ 1 x = x via ρ.map_one, hence x = 0.
  have hone : ρ 1 = LinearMap.id := ρ.map_one
  have h := hρ_zero 1
  rw [hone, LinearMap.id_apply] at h
  exact h

/-! ## GL_N-equivariance of the embedding -/

/-- `splitDualBasis` intertwines the `g^⊗n ⊗ id` action on `V^⊗n ⊗ (V^*)^⊗n`
with the pointwise `PiTensorProduct.map g.toLin'` action on each
`V^⊗n`-coordinate. -/
lemma splitDualBasis_tgtGLAction (g : Matrix (Fin N) (Fin N) k)
    (z : PolyTensorTgt k N n) (j : Fin n → Fin N) :
    splitDualBasis k N n (PolynomialTensorBridge.tgtGLAction k N n g z) j =
      PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' g)
        (splitDualBasis k N n z j) := by
  classical
  -- Prove the underlying LinearMap equality by TensorProduct.ext.
  suffices h :
      ((LinearMap.proj j : ((Fin n → Fin N) → TensorPower k (StdV k N) n) →ₗ[k]
              TensorPower k (StdV k N) n).comp
          (splitDualBasis k N n).toLinearMap).comp
        (PolynomialTensorBridge.tgtGLAction k N n g) =
        (PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' g)).comp
          ((LinearMap.proj j).comp (splitDualBasis k N n).toLinearMap) by
    have := congrArg (fun f => f z) h
    simpa using this
  apply TensorProduct.ext'
  intro u v
  simp only [LinearMap.comp_apply, splitDualBasis, PolynomialTensorBridge.tgtGLAction,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    LinearEquiv.lTensor_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, LinearMap.proj_apply, map_smul]

/-- **Matrix-coefficient polynomial equivariance.** Given the polynomial matrix-
coefficient multiplicativity hypothesis `hP_mul`, the matrix-coefficient
polynomial of `ρ g x` equals the right-translation of the matrix-coefficient
polynomial of `x` by `g`. -/
lemma matrixCoeffPoly_polyRightTransl {d : ℕ} (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      PolynomialTensorBridge.polyRightTransl k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d) (x : M) :
    matrixCoeffPoly k N b P a (ρ g x) =
      PolynomialTensorBridge.polyRightTransl k N
        (g : Matrix (Fin N) (Fin N) k) (matrixCoeffPoly k N b P a x) := by
  classical
  -- Abbreviations.
  set eg : MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
    PolynomialTensorBridge.polyRightTransl k N (g : Matrix (Fin N) (Fin N) k) with hegd
  set eval_g : MvPolynomial (Fin N × Fin N) k → k :=
    fun p => MvPolynomial.eval
      (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) p with hevalg
  -- Key identity: b.coord c' (ρ g x) = Σ_c (b.coord c x) * eval_g (P c' c).
  have hrepr : ∀ c' : Fin d,
      b.coord c' (ρ g x) = ∑ c : Fin d, b.coord c x * eval_g (P c' c) := by
    intro c'
    have hx : x = ∑ c : Fin d, b.coord c x • b c := by
      conv_lhs => rw [← b.sum_repr x]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Module.Basis.coord_apply]
    conv_lhs => rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [(ρ g).map_smul, (b.coord c').map_smul, smul_eq_mul]
    congr 1
    have := hP g c' c
    rwa [Module.Basis.coord_apply]
  -- Both sides expand as Σ_c b.coord c x • eg(P a c).
  have hLHS :
      matrixCoeffPoly k N b P a (ρ g x) =
        ∑ c : Fin d, b.coord c x • eg (P a c) := by
    rw [matrixCoeffPoly_apply]
    simp_rw [hrepr]
    -- Σ_{c'} (Σ_c a_c * e_{c',c}) • P a c' = Σ_c a_c • (Σ_{c'} e_{c',c} • P a c')
    have hswap :
        (∑ c' : Fin d, (∑ c : Fin d, b.coord c x * eval_g (P c' c)) • P a c') =
          (∑ c : Fin d, b.coord c x • (∑ c' : Fin d, eval_g (P c' c) • P a c')) := by
      simp_rw [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [← smul_smul, ← mul_smul, mul_comm]
    rw [hswap]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [hP_mul g a c]
  have hRHS : eg (matrixCoeffPoly k N b P a x) =
      ∑ c : Fin d, b.coord c x • eg (P a c) := by
    rw [matrixCoeffPoly_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul]
  rw [hLHS, hRHS]

/-- Equivariance of `polyTensorRow`: right-translation on the polynomial side
matches `tgtGLAction` on the tensor side. -/
lemma polyTensorRow_equivariant [CharZero k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      PolynomialTensorBridge.polyRightTransl k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d) (x : M) :
    polyTensorRow k N n b P hhom a (ρ g x) =
      PolynomialTensorBridge.tgtGLAction k N n (g : Matrix (Fin N) (Fin N) k)
        (polyTensorRow k N n b P hhom a x) := by
  unfold polyTensorRow
  simp only [LinearMap.comp_apply]
  -- After codRestrict, the subtypes carry matrixCoeffPoly. Push through the equality.
  have hmc := matrixCoeffPoly_polyRightTransl k N b P ρ hP hP_mul g a x
  have heq :
      (LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
          (matrixCoeffPoly k N b P a)
          (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)) (ρ g x) =
      ⟨PolynomialTensorBridge.polyRightTransl k N (g : Matrix (Fin N) (Fin N) k)
          ((LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
            (matrixCoeffPoly k N b P a)
            (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)) x).val,
       PolynomialTensorBridge.polyRightTransl_isHomogeneous (k := k) (N := N) (m := n)
         (g : Matrix (Fin N) (Fin N) k)
         ((LinearMap.codRestrict (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k n)
            (matrixCoeffPoly k N b P a)
            (matrixCoeffPoly_mem_homogeneous k N n b P hhom a)) x).property⟩ := by
    apply Subtype.ext
    simpa [LinearMap.codRestrict] using hmc
  rw [heq,
    PolynomialTensorBridge.homogeneousPolyToTensor_equivariant (k := k) (N := N) (n := n)
      (g := (g : Matrix (Fin N) (Fin N) k))]

/-- Equivariance of `polyTensorBundle` on each coordinate. -/
lemma polyTensorBundle_equivariant [CharZero k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hhom : ∀ a c, (P a c).IsHomogeneous n)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
      b.repr (ρ g (b c)) a =
        MvPolynomial.eval
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c))
    (hP_mul : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
      PolynomialTensorBridge.polyRightTransl k N
          (g : Matrix (Fin N) (Fin N) k) (P a c') =
        ∑ c, MvPolynomial.eval
               (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P c c') • P a c)
    (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M)
    (p : Fin d × (Fin n → Fin N)) :
    polyTensorBundle k N n b P hhom (ρ g x) p =
      PiTensorProduct.map (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
        (polyTensorBundle k N n b P hhom x p) := by
  rw [polyTensorBundle_apply, polyTensorBundle_apply,
    polyTensorRow_equivariant (k := k) (N := N) (n := n) b P hhom ρ hP hP_mul g p.1 x,
    splitDualBasis_tgtGLAction k N n (g : Matrix (Fin N) (Fin N) k)
      (polyTensorRow k N n b P hhom p.1 x) p.2]

/-- **Polynomial GL_N-rep embeds equivariantly into a tensor power**
(Etingof §5.23, Schur-Weyl #2b — full version with equivariance).

The upgraded form of `polynomialRep_embeds_in_tensorPower_inj`: in addition to
exhibiting an injective `k`-linear embedding `φ : M → (V^⊗n)^m`, the embedding
is `GL_N`-equivariant — it intertwines the representation `ρ` on `M` with the
tensor-power action `g ↦ PiTensorProduct.map (g^⊗n)` on each coordinate of the
target.

The equivariance requires, in addition to the matrix-coefficient evaluation
hypothesis `hP`, the **polynomial matrix-coefficient multiplicativity**
hypothesis `hP_mul` asserting the polynomial-level identity
`polyRightTransl g (P a c') = Σ_c eval g (P c c') • P a c`. This identity
holds at the evaluation level for all `g ∈ GL_N` (by `ρ.map_mul` and the
polynomial-matrix-coefficient setup), and from `[CharZero k]` (hence
`Infinite k`) one can derive the polynomial-level statement via the
determinant/funext trick. We take it as a hypothesis here to keep the bundle
focused on the equivariance assembly; the derivation is deferred to a
follow-up.

(Etingof Definition 5.23.1 + Theorem 5.23.2 setup. Issue #2537 / #2527 Part B.) -/
theorem polynomialRep_embeds_in_tensorPower
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (_halg : IsAlgebraicRepresentation N (ρ : _ → _))
    (hpoly : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c',
           PolynomialTensorBridge.polyRightTransl k N
               (g : Matrix (Fin N) (Fin N) k) (P a c') =
             ∑ c, MvPolynomial.eval
                    (fun ij : Fin N × Fin N =>
                      (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
                    (P c c') • P a c)) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  classical
  obtain ⟨d, b, P, hhom, hP, hP_mul⟩ := hpoly
  -- Unpack and keep the explicit φ so we can also state equivariance.
  let m := Fintype.card (Fin d × (Fin n → Fin N))
  let e : Fin d × (Fin n → Fin N) ≃ Fin m := Fintype.equivFin _
  let reindex :
      (Fin d × (Fin n → Fin N) → TensorPower k (StdV k N) n) ≃ₗ[k]
        (Fin m → TensorPower k (StdV k N) n) :=
    LinearEquiv.funCongrLeft k (TensorPower k (StdV k N) n) e.symm
  let φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n) :=
    reindex.toLinearMap.comp (polyTensorBundle k N n b P hhom)
  refine ⟨m, φ, ?_, ?_⟩
  · -- Injectivity: identical to `polynomialRep_embeds_in_tensorPower_inj`.
    rw [show Function.Injective φ ↔
          Function.Injective (polyTensorBundle k N n b P hhom) from by
      simp [φ, LinearMap.coe_comp, reindex.injective.of_comp_iff]]
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx_pt : ∀ p : Fin d × (Fin n → Fin N),
        polyTensorBundle k N n b P hhom x p = 0 :=
      fun p => congrFun hx p
    have hx_split : ∀ a : Fin d,
        (splitDualBasis k N n) (polyTensorRow k N n b P hhom a x) = 0 := by
      intro a
      funext j
      have := hx_pt (a, j)
      rw [polyTensorBundle_apply] at this
      simpa using this
    have hx_row : ∀ a : Fin d, polyTensorRow k N n b P hhom a x = 0 :=
      fun a => (splitDualBasis k N n).map_eq_zero_iff.mp (hx_split a)
    have hx_poly : ∀ a : Fin d, matrixCoeffPoly k N b P a x = 0 :=
      fun a => (polyTensorRow_eq_zero_iff k N n b P hhom a x).mp (hx_row a)
    have hcoord_zero : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (a : Fin d),
        b.coord a (ρ g x) = 0 := by
      intro g a
      have hP_g : ∀ a' c', b.coord a' ((ρ g) (b c')) =
          MvPolynomial.eval
            (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
            (P a' c') := by
        intro a' c'
        have h := hP g a' c'
        rwa [Module.Basis.coord_apply]
      have h := eval_matrixCoeffPoly k N b P (ρ g)
        (fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) hP_g a x
      rw [hx_poly a, map_zero] at h
      exact h.symm
    have hρ_zero : ∀ g : Matrix.GeneralLinearGroup (Fin N) k, ρ g x = 0 := by
      intro g
      apply b.repr.injective
      ext a
      rw [LinearEquiv.map_zero, Finsupp.zero_apply]
      have := hcoord_zero g a
      rwa [Module.Basis.coord_apply] at this
    have hone : ρ 1 = LinearMap.id := ρ.map_one
    have h := hρ_zero 1
    rw [hone, LinearMap.id_apply] at h
    exact h
  · -- Equivariance: φ (ρ g x) i = PiTensorProduct.map g.toLin' (φ x i).
    intro g x i
    -- reindex is funCongrLeft e.symm, so evaluation at i gives the value at e.symm i.
    change polyTensorBundle k N n b P hhom (ρ g x) (e.symm i) =
      PiTensorProduct.map (fun _ => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
        (polyTensorBundle k N n b P hhom x (e.symm i))
    exact polyTensorBundle_equivariant (k := k) (N := N) (n := n) b P hhom ρ hP hP_mul
      g x (e.symm i)

end PolynomialRepEmbedding

end Etingof

/-! ## Polynomial-identity-from-GL-evaluation

The hypothesis `hP_mul` of `polynomialRep_embeds_in_tensorPower` is a
*polynomial-level* identity in `MvPolynomial (Fin N × Fin N) k`. It holds at
the evaluation level for every `g ∈ GL_N` (by `ρ.map_mul` and the
matrix-coefficient setup). Over an infinite field — in particular when
`[CharZero k]` — polynomial equality follows from equality on evaluations
at every invertible matrix: the set of invertible matrices is Zariski-dense
in `Matrix (Fin N) (Fin N) k` since the generic determinant polynomial is
nonzero. We record that density argument here and then derive `hP_mul` from
`ρ.map_mul`. -/

namespace Etingof.PolynomialRepEmbedding

open PolynomialTensorBridge

variable (k : Type u) [Field k] (N : ℕ)

/-- Evaluating `polyRightTransl g p` at `h` coincides with evaluating `p` at
the product matrix `h * g`. The algebra homs `eval_h ∘ polyRightTransl_g` and
`eval_{h·g}` agree on generators `X_{ij}` (both give `(h*g)_{ij}`). -/
lemma eval_polyRightTransl
    (g h : Matrix (Fin N) (Fin N) k) (p : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => h ij.1 ij.2)
        (PolynomialTensorBridge.polyRightTransl k N g p) =
      MvPolynomial.eval (fun ij : Fin N × Fin N => (h * g) ij.1 ij.2) p := by
  classical
  suffices halgs :
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => h ij.1 ij.2)).comp
        (PolynomialTensorBridge.polyRightTransl k N g) =
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => (h * g) ij.1 ij.2) :
        MvPolynomial (Fin N × Fin N) k →ₐ[k] k) by
    have := AlgHom.congr_fun halgs p
    simpa [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using this
  apply MvPolynomial.algHom_ext
  intro ij
  rw [AlgHom.comp_apply, PolynomialTensorBridge.polyRightTransl_X, map_sum,
    MvPolynomial.aeval_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Algebra.algebraMap_self_apply]

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- **Derivation of `hP_mul` from `hP`.** Given the matrix-coefficient
evaluation identity `hP`, the polynomial-level multiplicativity identity
`hP_mul` follows from `ρ.map_mul`: both sides of `hP_mul` agree under
evaluation at every `h ∈ GL_N` (via `MvPolynomial.eq_of_eval_eq_on_gl`),
because `h · g ∈ GL_N` and `ρ.map_mul` gives `ρ(h·g) = ρ h ∘ ρ g`. -/
lemma hP_mul_of_hP [Infinite k] {d : ℕ}
    (b : Module.Basis (Fin d) k M)
    (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (hP : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))
    (g : Matrix.GeneralLinearGroup (Fin N) k) (a c' : Fin d) :
    PolynomialTensorBridge.polyRightTransl k N
        (g : Matrix (Fin N) (Fin N) k) (P a c') =
      ∑ c, MvPolynomial.eval
             (fun ij : Fin N × Fin N =>
               (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
             (P c c') • P a c := by
  classical
  -- Convenience rewrite from `hP`: each evaluation coincides with a basis coord.
  have hP_coord : ∀ (e : Matrix.GeneralLinearGroup (Fin N) k) (a c : Fin d),
      MvPolynomial.eval
          (fun ij : Fin N × Fin N => (e : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (P a c) = b.coord a (ρ e (b c)) :=
    fun e a c => by rw [← hP e a c, Module.Basis.coord_apply]
  apply MvPolynomial.eq_of_eval_eq_on_gl
  intro h
  rw [eval_polyRightTransl k N (g : Matrix (Fin N) (Fin N) k)
       (h : Matrix (Fin N) (Fin N) k) (P a c'), map_sum]
  simp only [MvPolynomial.smul_eval]
  -- `eval_{h·g}(P a c') = b.coord a (ρ(h·g)(b c')) = b.coord a (ρ h (ρ g (b c')))`.
  -- `((h·g : GL_N) : Matrix) = h · g` is `Units.val_mul`, definitionally rfl.
  have hLHS : MvPolynomial.eval
                (fun ij : Fin N × Fin N =>
                  ((h : Matrix (Fin N) (Fin N) k) * (g : Matrix (Fin N) (Fin N) k))
                    ij.1 ij.2) (P a c') =
              b.coord a (ρ h (ρ g (b c'))) := by
    have hPhg := hP_coord (h * g) a c'
    rwa [ρ.map_mul, Module.End.mul_apply] at hPhg
  rw [hLHS]
  simp_rw [hP_coord]
  -- Expand `ρ g (b c')` in the basis, then push `ρ h` and `b.coord a` through the sum.
  conv_lhs =>
    rw [show ρ g (b c') = ∑ c : Fin d, b.coord c (ρ g (b c')) • b c from by
      simp_rw [Module.Basis.coord_apply]; exact (b.sum_repr _).symm]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(ρ h).map_smul, (b.coord a).map_smul, smul_eq_mul]

/-- **Polynomial GL_N-rep embeds equivariantly into a tensor power (primed
form).** The polynomial-level matrix-coefficient multiplicativity hypothesis
`hP_mul` of `polynomialRep_embeds_in_tensorPower` is supplied internally via
`hP_mul_of_hP` (using `ρ.map_mul` and the polynomial-identity-from-GL-
evaluation lemma). Callers need only provide the homogeneity and
matrix-coefficient evaluation witnesses `(hhom, hP)`.

Downstream consumers (Schur-Weyl #5, issue #2482) should cite this form. -/
theorem polynomialRep_embeds_in_tensorPower' (n : ℕ)
    [CharZero k]
    [Module.Finite k M]
    (ρ : Matrix.GeneralLinearGroup (Fin N) k →* (M →ₗ[k] M))
    (halg : IsAlgebraicRepresentation N (ρ : _ → _))
    (hpoly' : ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c))) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  obtain ⟨d, b, P, hhom, hP⟩ := hpoly'
  exact polynomialRep_embeds_in_tensorPower k N n ρ halg
    ⟨d, b, P, hhom, hP, fun g a c' => hP_mul_of_hP k N b P ρ hP g a c'⟩

/-- The scalar matrix `t • 1 ∈ GL_N(k)`.  Diagonal with the unit `t` in every
slot; equivalently `Matrix.diagonal (fun _ => (t : k)) = (t : k) • 1`.  This is
the element `∏ᵢ diagUnit i t` referenced in the `det⁻¹`-elimination strategy. -/
noncomputable def scalarGL (t : kˣ) :
    Matrix.GeneralLinearGroup (Fin N) k where
  val := Matrix.diagonal fun _ => (t : k)
  inv := Matrix.diagonal fun _ => ((t⁻¹ : kˣ) : k)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv]
    exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul]
    exact Matrix.diagonal_one

/-- The scalar matrix is the (commuting) product of the one-parameter diagonal
generators: `scalarGL t = ∏ᵢ diagUnit i t`, the diagonal matrix with `t` in every
slot.  The generators pairwise commute (`diagUnit_comm`), so this is a
`Finset.noncommProd` (the ambient `GL` is noncommutative). -/
private lemma scalarGL_eq_noncommProd (t : kˣ) :
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

/-- **Piece 1 of `det⁻¹` elimination — the scalar matrix acts by `t^n`.**
On a *polynomial* (all weights nonnegative) weight-homogeneous-of-degree-`n`
`GL_N`-representation, the scalar matrix `scalarGL t = t • 1` acts as the scalar
`t ^ n`.

**Hypotheses (corrected, issue #4654).** `h_span` — that the `ℕ`-indexed weight
spaces span `M` — is *essential* and was missing from the original
decomposition. Without it the statement is **false**: the diagonal torus need
not act diagonalisably with nonnegative weights. Concrete counterexample
(`N = 2`, `n = 1`): `M = V ⊕ (det⁻¹)` where `V` is the standard rep. The center
`scalarGL t` acts by `t` on `V` but by `t⁻²` on the `det⁻¹` summand, so it is
*not* the scalar `t¹ • id`; yet `halg` holds and `h_homog` holds for `n = 1`
(the only `ℕ`-valued weights are `(1,0),(0,1)`, both summing to `1`; the weight
`(-1,-1)` of `det⁻¹` is not expressible in the `ℕ`-indexed `glWeightSpace`, so
it imposes no constraint). The weight spaces do *not* span (`V ≠ M`), so `h_span`
correctly excludes it.

Strategy (now that `h_span` is a hypothesis): on a weight space `M_μ` the
generator `diagUnit i t` acts by *exactly* `t ^ (μ i)` (by definition of
`glWeightSpace` as the relevant kernel), so `scalarGL t = ∏ᵢ diagUnit i t` acts
by `t ^ (∑ᵢ μ i) = t ^ n` (`h_homog`). Since the weight spaces span (`h_span`),
this extends to all of `M`: `M.ρ (scalarGL t) = t^n • id`. The general
weight-span hypothesis is proven for Schur modules at
`SchurWeylFormalCharacterIso.glWeightSpace_schurModule_iSup_eq_top`. -/
private theorem scalarGL_acts_as_pow (n : ℕ)
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n)
    (t : kˣ) :
    M.ρ (scalarGL k N t) = ((t : k) ^ n) • LinearMap.id := by
  rw [← sub_eq_zero]
  set L : M →ₗ[k] M := M.ρ (scalarGL k N t) - ((t : k) ^ n) • LinearMap.id with hL
  -- `L` kills every weight space, hence all of `M` (by `h_span`).
  have hker : (⨆ μ : Fin N →₀ ℕ, glWeightSpace k N M (fun i => μ i)) ≤ LinearMap.ker L := by
    rw [iSup_le_iff]
    intro μ w hw
    rw [LinearMap.mem_ker]
    by_cases hw0 : w = 0
    · simp [hw0]
    · -- `w` is a simultaneous eigenvector for the diagonal generators.
      have heig : ∀ i : Fin N, M.ρ (diagUnit k N i t) w = ((t : k) ^ μ i) • w := by
        intro i
        have hmem : w ∈ glWeightSpace k N M (fun j => μ j) := hw
        rw [glWeightSpace, Submodule.mem_iInf] at hmem
        have h2 := (Submodule.mem_iInf _).1 (hmem i) t
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero,
          LinearMap.smul_apply, LinearMap.id_apply] at h2
        exact h2
      -- `scalarGL t = ∏ᵢ diagUnit i t` acts as `∏ᵢ t^(μ i) = t^(∑ μ)`.
      have act : ∀ (s : Finset (Fin N))
          (comm : (↑s : Set (Fin N)).Pairwise
            fun a b => Commute (M.ρ (diagUnit k N a t)) (M.ρ (diagUnit k N b t))),
          (s.noncommProd (fun i => M.ρ (diagUnit k N i t)) comm) w
            = (∏ i ∈ s, (t : k) ^ μ i) • w := by
        intro s
        induction s using Finset.induction with
        | empty => intro comm; simp
        | @insert a s ha ih =>
            intro comm
            rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, Module.End.mul_apply, ih,
              Finset.prod_insert ha, map_smul, heig a, smul_smul, mul_comm]
      have hprod : M.ρ (scalarGL k N t) w = ((t : k) ^ (∑ i, μ i)) • w := by
        rw [scalarGL_eq_noncommProd, Finset.map_noncommProd, act Finset.univ,
          Finset.prod_pow_eq_pow_sum]
      -- `w ≠ 0` lies in this weight space, so it is nonzero and `∑ μ = n`.
      have hne : glWeightSpace k N M (fun i => μ i) ≠ ⊥ := by
        intro h; exact hw0 ((Submodule.mem_bot k).1 (h ▸ hw))
      have hsum : ∑ i, μ i = n := h_homog (fun i => μ i) hne
      rw [hL, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hprod, hsum,
        sub_self]
  rw [h_span, top_le_iff, LinearMap.ker_eq_top] at hker
  exact hker

/-- Scaling all evaluation points by `c` multiplies the value of a degree-`i`
homogeneous polynomial by `c ^ i`. -/
private lemma eval_mul_pow_of_isHomogeneous {i : ℕ}
    {p : MvPolynomial (Fin N × Fin N) k} (hp : p.IsHomogeneous i)
    (c : k) (x : Fin N × Fin N → k) :
    MvPolynomial.eval (fun s => c * x s) p = c ^ i * MvPolynomial.eval x p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPolynomial.mem_support_iff] at hd
  have hdeg : d.degree = i := by by_contra h; exact hd (hp.coeff_eq_zero h)
  have hsum : (∑ s ∈ d.support, d s) = i := by rw [← hdeg]; rfl
  rw [Finset.prod_congr rfl (fun s _ => mul_pow c (x s) (d s)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]
  ring

/-- **Homogeneity from `GL`-scaling.** A polynomial in the matrix entries whose
evaluation scales as `Q(t • g) = tⁿ Q(g)` for every `g ∈ GL` and unit `t` is
homogeneous of degree `n`. Each homogeneous component `Qᵈ` contributes `tᵈ·eval g Qᵈ`
to the scaling, so the univariate polynomial `∑ᵈ (eval g Qᵈ) Tᵈ - (eval g Q) Tⁿ`
vanishes on all of `kˣ` (infinite), hence is `0`; reading off its coefficients
forces `eval g Qᵈ = 0` for `d ≠ n` on all of `GL`, so `Qᵈ = 0` by
`eq_of_eval_eq_on_gl`. -/
private lemma isHomogeneous_of_gl_scaling [Infinite k] {n : ℕ}
    (Q : MvPolynomial (Fin N × Fin N) k)
    (hsc : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (t : kˣ),
       MvPolynomial.eval (fun ij : Fin N × Fin N =>
           (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q
       = (t : k) ^ n *
         MvPolynomial.eval (fun ij : Fin N × Fin N =>
           (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q) :
    Q.IsHomogeneous n := by
  classical
  have key : ∀ i, i ≠ n → MvPolynomial.homogeneousComponent i Q = 0 := by
    intro i hi
    apply MvPolynomial.eq_of_eval_eq_on_gl
    intro g
    rw [map_zero]
    set G : Fin N × Fin N → k :=
      fun ij => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2 with hG
    set td := Q.totalDegree with htd
    set c : ℕ → k := fun e => MvPolynomial.eval G (MvPolynomial.homogeneousComponent e Q) with hc
    have hsum_id : ∀ t : k, MvPolynomial.eval (fun ij => t * G ij) Q
        = ∑ e ∈ Finset.range (td+1), c e * t^e := by
      intro t
      conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent Q]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [eval_mul_pow_of_isHomogeneous k N (MvPolynomial.homogeneousComponent_isHomogeneous e Q) t G]
      rw [hc]; ring
    by_cases hile : i ≤ td
    · set P : Polynomial k :=
        (∑ e ∈ Finset.range (td+1), Polynomial.C (c e) * Polynomial.X ^ e)
          - Polynomial.C (MvPolynomial.eval G Q) * Polynomial.X ^ n with hP
      have hroot : ∀ t : k, t ≠ 0 → P.IsRoot t := by
        intro t ht
        have hu : MvPolynomial.eval (fun ij => ((Units.mk0 t ht : kˣ):k) * G ij) Q
            = ((Units.mk0 t ht : kˣ):k)^n * MvPolynomial.eval G Q := hsc g (Units.mk0 t ht)
        simp only [Units.val_mk0] at hu
        have key2 : (∑ e ∈ Finset.range (td+1), c e * t^e) = t^n * MvPolynomial.eval G Q := by
          rw [← hsum_id t]; exact hu
        rw [Polynomial.IsRoot.def, hP]
        simp only [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [key2]; ring
      have hinf : Set.Infinite {t : k | P.IsRoot t} := by
        apply Set.Infinite.mono _ ((Set.finite_singleton (0:k)).infinite_compl)
        intro t ht
        exact hroot t (by simpa using ht)
      have hP0 : P = 0 := Polynomial.eq_zero_of_infinite_isRoot P hinf
      have hcoeff : P.coeff i = c i := by
        rw [hP]
        simp only [Polynomial.coeff_sub, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq (Finset.range (td+1)) i (fun e => c e)]
        simp only [Finset.mem_range, Nat.lt_succ_iff, hile, if_true]
        rw [if_neg hi]
        ring
      rw [hP0] at hcoeff
      simpa [hc] using hcoeff.symm
    · rw [show MvPolynomial.homogeneousComponent i Q = 0 from
          MvPolynomial.homogeneousComponent_eq_zero (φ := Q) (n := i) (by omega), map_zero]
  have hQeq : Q = MvPolynomial.homogeneousComponent n Q := by
    ext d
    rw [MvPolynomial.coeff_homogeneousComponent]
    by_cases hd : d.degree = n
    · rw [if_pos hd]
    · rw [if_neg hd]
      have h0 := key d.degree hd
      have h2 : MvPolynomial.coeff d (MvPolynomial.homogeneousComponent d.degree Q)
          = MvPolynomial.coeff d Q := by
        rw [MvPolynomial.coeff_homogeneousComponent, if_pos rfl]
      rw [h0, MvPolynomial.coeff_zero] at h2
      exact h2.symm
  rw [hQeq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous n Q

/-- **det⁻¹ elimination proper (the genuine `h_span` content of issue #4654).**
On a *genuinely polynomial* algebraic representation — one whose `ℕ`-indexed
weight spaces span `M` (`h_span`) — the algebraic-representation matrix
coefficients, a priori living in `k[Xᵢⱼ, D]` with `D = det⁻¹`, are already
*bare-entry* polynomials in `k[Xᵢⱼ]`: the `det⁻¹` variable can be eliminated.

This is the hard mathematical core (Etingof Theorem 5.23.2(i), polynomial case):
`h_span` is *essential* and `h_scalar` alone is **insufficient**. The naive
"clear the denominator `P = Q/det^r`, match the scaling degree, conclude `r = 0`"
argument only shows each cleared numerator `Q` is *multi-homogeneous* (degree
`s + μ(a)ᵢ` in row `i`, `s + μ(c)ⱼ` in column `j`); multi-homogeneity does **not**
imply `det^s ∣ Q` (e.g. `N = 2, s = 1`: `α·g₁₁g₂₂ + β·g₁₂g₂₁` is row/column
multi-homogeneous of degree `1` but `det = g₁₁g₂₂ - g₁₂g₂₁` divides it only when
`α = -β`). Divisibility — equivalently, that the rep extends to the matrix monoid
`Mₙ(k)`, equivalently nonnegativity of *all* weights — is exactly the global
representation structure supplied by `h_span` (the `Sym²(V) ⊗ det⁻¹`
counterexample, with ℤ-weights `(1,-1),(0,0),(-1,1)`, fails `h_span` precisely
because its negative-entry weights leave the `ℕ`-indexed weight spaces
non-spanning). No homogeneity is asserted here; that is `matrixCoeff_isHomogeneous`.

TODO (issue #4654 sub, det⁻¹ elimination): the genuine proof. Routes: (a) book's
structural route — `R` (the matrix-coefficient ring) decomposes through
`Sⁿ(V ⊗ V*) ⊗ (∧ᴺV*)^s` and `h_span` forces `s = 0`; (b) monoid-extension —
`ρ : GLₙ → GL(M)` with all weights `≥ 0` extends to `Mₙ(k) → End(M)`, whose
matrix coefficients are the bare polynomials. -/
private theorem detInv_elim_of_polynomial (n : ℕ) [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (Q a c) := by
  -- The det⁻¹-elimination core (issue #4695): assembled from the kernel lemma
  -- (#4694) via the weight-eigenbasis + right-translation argument in
  -- `Etingof.DetInvElim.detInv_elim`. See the docstring for why `h_span` is needed.
  exact Etingof.DetInvElim.detInv_elim n M halg h_span

/-- **Homogeneity extraction.** Once the `det⁻¹` variable has been eliminated
(`detInv_elim_of_polynomial`), the bare-entry matrix-coefficient polynomials `Q`
are automatically **homogeneous of degree `n`**, provided the scalar matrix acts
by `t ^ n` (`h_scalar`).

Unlike the det⁻¹ elimination, this step is purely formal: each matrix coefficient
`f(g) = b.repr (M.ρ g (b c)) a = eval g (Q a c)` satisfies `f(t • g) = tⁿ f(g)`
(from `h_scalar` and `M.ρ.map_mul`, since `scalarGL t * g = t • g`), so on each
homogeneous component `Qᵈ` of `Q` the identity
`∑ᵈ tᵈ · eval g Qᵈ = tⁿ · eval g Q` holds for all `t ∈ kˣ`; as a univariate
polynomial in `t` with infinitely many (all of `kˣ`) roots it vanishes, forcing
`eval g Qᵈ = 0` for `d ≠ n` on all of `GL`, hence `Qᵈ = 0` by
`eq_of_eval_eq_on_gl`, i.e. `Q` is homogeneous of degree `n`. -/
private theorem matrixCoeff_isHomogeneous (n : ℕ) [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (h_scalar : ∀ t : kˣ, M.ρ (scalarGL k N t) = ((t : k) ^ n) • LinearMap.id)
    {d : ℕ} (b : Module.Basis (Fin d) k M)
    (Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k)
    (hQ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (Q a c))
    (a c : Fin d) : (Q a c).IsHomogeneous n := by
  apply isHomogeneous_of_gl_scaling
  intro g t
  -- The scalar matrix `scalarGL t` times `g` has entries `t * g_ij`.
  have hmatrix : ∀ ij : Fin N × Fin N,
      ((scalarGL k N t * g : Matrix.GeneralLinearGroup (Fin N) k) :
          Matrix (Fin N) (Fin N) k) ij.1 ij.2
        = (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2 := by
    intro ij
    show ((scalarGL k N t : Matrix (Fin N) (Fin N) k) *
        (g : Matrix (Fin N) (Fin N) k)) ij.1 ij.2 = _
    rw [show (scalarGL k N t : Matrix (Fin N) (Fin N) k)
          = Matrix.diagonal (fun _ => (t : k)) from rfl, Matrix.diagonal_mul]
  -- Rewrite the scaled evaluation as the matrix coefficient at `scalarGL t * g`.
  have hpt : (fun ij : Fin N × Fin N => (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
      = (fun ij : Fin N × Fin N =>
          ((scalarGL k N t * g : Matrix.GeneralLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) ij.1 ij.2) := by
    funext ij; exact (hmatrix ij).symm
  have hL : MvPolynomial.eval (fun ij : Fin N × Fin N =>
        (t : k) * (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) (Q a c)
      = b.repr (M.ρ (scalarGL k N t * g) (b c)) a := by
    rw [hpt]; exact (hQ (scalarGL k N t * g) a c).symm
  rw [hL, map_mul, h_scalar t, Module.End.mul_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, map_smul, Finsupp.smul_apply, smul_eq_mul, hQ g a c]

/-- **Piece 2 of `det⁻¹` elimination — assembly given the scalar action.**
On a *polynomial* (all weights nonnegative) representation whose scalar matrix
acts by `t ^ n` (`h_scalar`, Piece 1 `scalarGL_acts_as_pow`), the
algebraic-representation matrix coefficients are bare-entry polynomials in
`Fin N × Fin N`, homogeneous of degree `n`.

**Hypotheses (corrected, issue #4654).** `h_span` — that the `ℕ`-indexed weight
spaces span `M` — is *essential*. With only `h_scalar` the statement is
**false**: `h_scalar` records the aggregate action of the center but not the
nonnegativity of the individual weights that kills the `det⁻¹` denominator.
Concrete counterexample (`N = 2`, `n = 0`): `M = Sym²(V) ⊗ det⁻¹`. The center
`scalarGL t = t • 1` acts by `t² · t⁻² = t⁰ = 1`, so `h_scalar` holds with
`n = 0`; `M` is algebraic; and the only `ℕ`-valued weight is `(0,0)` (weights
`(1,-1),(-1,1)` are not expressible in the `ℕ`-indexed `glWeightSpace`), so
`h_homog` holds vacuously. But the conclusion would force every matrix
coefficient to be a homogeneous degree-`0` polynomial — a constant — i.e.
`M.ρ g = M.ρ 1 = id` for all `g`, contradicting that `Sym²V ⊗ det⁻¹` is a
nontrivial `3`-dimensional representation. The weight spaces do not span (only
the `1`-dimensional `(0,0)`-space is `ℕ`-indexed), so `h_span` excludes it.

Strategy (now that `h_span` is a hypothesis): each matrix coefficient
`f_{a,c}(g) = b.repr (M.ρ g (b c)) a` satisfies `f (t • g) = t^n f(g)` by
`h_scalar` and `M.ρ.map_mul` (since `scalarGL t * g = t • g`). The algebraic-rep
polynomial `P a c ∈ k[Xᵢⱼ, D]` (`evalAtGL` substitutes `D ↦ det⁻¹`, scaling by
`t^{-N}` under `g ↦ t • g`). Writing `P a c = Q / det^r` and matching the
`t`-degree forces `Q` homogeneous of degree `n + N r`; nonnegativity of the
weights — guaranteed by `h_span`, which is what makes `M` genuinely polynomial —
forces the minimal `r = 0`, so `f` is a genuine bare-entry polynomial
homogeneous of degree `n`. Identity over all of `GL` upgrades to a polynomial
identity by `MvPolynomial.eq_of_eval_eq_on_gl` (cf. `hP_mul_of_hP`). -/
private theorem hpoly'_of_scalarGL_action (n : ℕ)
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_scalar : ∀ t : kˣ, M.ρ (scalarGL k N t) = ((t : k) ^ n) • LinearMap.id) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) := by
  -- Assemble: eliminate `det⁻¹` (`detInv_elim_of_polynomial`, the `h_span` core),
  -- then read off homogeneity of the bare-entry polynomials
  -- (`matrixCoeff_isHomogeneous`, formal from `h_scalar`).
  obtain ⟨d, b, Q, hQ⟩ := detInv_elim_of_polynomial k N n M halg h_span
  exact ⟨d, b, Q,
    fun a c => matrixCoeff_isHomogeneous k N n M h_scalar b Q hQ a c, hQ⟩

/-- **Weight-homogeneity kills the `det⁻¹` variable (issue #4598 core).**
A weight-homogeneous-of-degree-`n` algebraic `GL_N`-representation `M` has its
matrix coefficients given, in a suitable basis, by **homogeneous degree-`n`
polynomials in the bare matrix entries** `Fin N × Fin N` — i.e. the raw
`hpoly'` witness consumed by `polynomialRep_embeds_in_tensorPower'`.

This bridges `Etingof.IsAlgebraicRepresentation` (matrix coefficients in
`k[Xᵢⱼ, D]`, `D = det⁻¹`, no homogeneity) to the bare-entry homogeneous data.

**Hypotheses (corrected, issue #4654).** `h_span` — that the `ℕ`-indexed weight
spaces span `M` — is *essential* and was missing from the original statement.
Without it the theorem is **false**: `IsAlgebraicRepresentation` allows weights
in `ℤ^N` (the `det⁻¹` variable), whereas the bare-entry-polynomial conclusion
needs all weights in `ℕ^N`. Counterexample (`N = 2`, `n = 0`):
`M = Sym²(V) ⊗ det⁻¹` is algebraic and satisfies `h_homog` vacuously (its only
`ℕ`-valued weight is `(0,0)`), but its degree-`0` matrix coefficients are not
constant. `h_span` (equivalently: `M` is a genuinely *polynomial* — not merely
rational/algebraic — representation) rules such cases out; it holds for Schur
modules by `SchurWeylFormalCharacterIso.glWeightSpace_schurModule_iSup_eq_top`.

Proof strategy (the genuine mathematical content, deferred — see issue #4598
decomposition): evaluate the matrix-coefficient identity at the scalar matrix
`t • 1 = ∏ᵢ diagUnit i t`. By `h_span` the weight spaces span `M`, so
`M.ρ (t • 1) = t^n • id` (each weight `μ` has `∑ μ = n` by `h_homog`). Hence
every matrix coefficient `g ↦ b.repr (ρ g (b c)) a` is homogeneous of degree `n`
under `g ↦ t • g`. Writing the algebraic-rep polynomial `P a c` over
`GLCoordVars = (Fin N × Fin N) ⊕ Unit` as `Q / det^r` with `Q` homogeneous,
homogeneity plus weight-nonnegativity forces the `det⁻¹` exponent to `0` and the
entry-degree to exactly `n` (clear denominators, then use Zariski density of
`GL` in `Matrix` via `MvPolynomial.eq_of_eval_eq_on_gl`), yielding the bare-entry
degree-`n` polynomial. -/
theorem polynomialRep_homogeneous_hpoly'
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k M)
       (P : Fin d → Fin d → MvPolynomial (Fin N × Fin N) k),
         (∀ a c, (P a c).IsHomogeneous n) ∧
         (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) a c,
           b.repr (M.ρ g (b c)) a =
             MvPolynomial.eval
               (fun ij : Fin N × Fin N =>
                 (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
               (P a c)) :=
  -- Assemble Piece 2 (det⁻¹ elimination) over Piece 1 (scalar action).
  hpoly'_of_scalarGL_action k N n M halg h_span
    (fun t => scalarGL_acts_as_pow k N n M halg h_span h_homog t)

/-- **A weight-homogeneous-of-degree-`n` algebraic `GL_N`-rep embeds
`GL_N`-equivariantly into `(V^{⊗n})^m`** (issue #4598, FDRep-facing corollary
of `polynomialRep_embeds_in_tensorPower'`). The det⁻¹ elimination is supplied
by `polynomialRep_homogeneous_hpoly'`; the equivariant embedding then follows
from the primed embedding lemma. Downstream: the Schur-Weyl #5 assembly
(issue #2482) views `(Fin m → TensorPower …)` as the ambient semisimple
`(V^{⊗n})^m`. -/
theorem polynomial_homog_rep_equivariant_embedding
    [CharZero k] [IsAlgClosed k]
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (halg : Etingof.IsAlgebraicRepresentation N M.ρ)
    (h_span : ⨆ (μ : Fin N →₀ ℕ), glWeightSpace k N M (fun i => μ i) = ⊤)
    (h_homog : ∀ μ : Fin N → ℕ, glWeightSpace k N M μ ≠ ⊥ → ∑ i, μ i = n) :
    ∃ (m : ℕ) (φ : M →ₗ[k] (Fin m → TensorPower k (StdV k N) n)),
      Function.Injective φ ∧
      (∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (x : M) (i : Fin m),
        φ (M.ρ g x) i =
          PiTensorProduct.map
            (fun _ : Fin n => Matrix.toLin' (g : Matrix (Fin N) (Fin N) k))
            (φ x i)) := by
  obtain ⟨d, b, P, hhom, hP⟩ :=
    polynomialRep_homogeneous_hpoly' k N M halg h_span h_homog
  exact polynomialRep_embeds_in_tensorPower' k N n M.ρ halg ⟨d, b, P, hhom, hP⟩

end Etingof.PolynomialRepEmbedding
