import EtingofRepresentationTheory.Chapter2.Problem2_15_1_l
import EtingofRepresentationTheory.Chapter2.Problem2_15_1_m_Module

/-!
# Jordan normal form of `A = J ⊗ Id + Id ⊗ J` (Problem 2.15.1(n))

The final part of Etingof's Problem 2.15.1. Let `V = ℂ^M ⊗ ℂ^N` and
`A = J_{0,M} ⊗ Id_N + Id_M ⊗ J_{0,N}`, where `J_{0,n}` is the nilpotent Jordan block of
size `n` (`J_{0,n} e_i = e_{i-1}`, `J_{0,n} e_1 = 0`). We find the Jordan normal form of
`A` from parts (l) and (m).

Writing `M = λ+1`, `N = μ+1`, the argument is the book's:

* By part (l) (`sl2RepOfBlock`, Problem 2.15.1(l)), the nilpotent Jordan block `J_{0,M}`
  is the raising operator `E` of an `sl(2)`-structure on `ℂ^M ≅ V_λ` obtained by
  conjugating the irreducible representation by the factorial rescaling `factScale`.
  Consequently `A` is, up to the conjugation `factScale ⊗ factScale`, exactly the `E`
  action on the tensor product `V_λ ⊗ V_μ` (`jordanTensorOp` vs. `⁅sl2_e, ·⁆`, lemma
  `factScale_congr_intertwines_e`).
* By part (m) (`clebsch_gordan_module_iso`, Problem 2.15.1(m)),
  `V_λ ⊗ V_μ ≅ ⨁_{k=0}^{min(λ,μ)} V_{λ+μ−2k}` as `sl(2)`-modules, so `E` on the tensor
  product is conjugate to `E` acting summand-by-summand on `⨁_k V_{λ+μ−2k}`.
* On each irreducible summand `V_{λ+μ−2k}`, conjugating by `factScale` again turns `E` into
  the single nilpotent Jordan block `J_{0, λ+μ−2k+1}` (`cgScale_intertwines_e`).

Chaining the three conjugations gives a linear isomorphism
`Θ : ℂ^M ⊗ ℂ^N ≃ₗ ⨁_k ℂ^{M+N-1-2k}` intertwining `A` with the block-diagonal sum of standard
Jordan blocks `⨁_k J_{0, M+N-1-2k}` (`cgJordan`). This is exactly the statement that the
Jordan normal form of `A` is the collection of Jordan blocks of sizes
`{M+N-1-2k : k = 0 … min(M,N)-1}`, all with eigenvalue `0` (`jordan_normal_form_tensor`).
-/

open scoped TensorProduct DirectSum
open Etingof Etingof.Sl2Irrep

namespace Etingof.Sl2Irrep

/-! ## The operators `A` and its Jordan normal form -/

/-- The operator `A = J_{0,M} ⊗ Id_N + Id_M ⊗ J_{0,N}` on `ℂ^M ⊗ ℂ^N` (`M = λ+1`,
`N = μ+1`), built from the standard nilpotent Jordan blocks `jordanShift`. -/
noncomputable def jordanTensorOp (lam mu : ℕ) :
    Module.End ℂ ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  TensorProduct.map (jordanShift (lam + 1)) LinearMap.id
    + TensorProduct.map LinearMap.id (jordanShift (mu + 1))

theorem jordanTensorOp_tmul (lam mu : ℕ) (a : Fin (lam + 1) → ℂ) (b : Fin (mu + 1) → ℂ) :
    jordanTensorOp lam mu (a ⊗ₜ[ℂ] b)
      = jordanShift (lam + 1) a ⊗ₜ[ℂ] b + a ⊗ₜ[ℂ] jordanShift (mu + 1) b := by
  simp only [jordanTensorOp, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_coe,
    id_eq]

/-- The block-diagonal Jordan operator `⨁_k J_{0, M+N-1-2k}` on `⨁_k ℂ^{M+N-1-2k}` — the
Jordan normal form of `A`. -/
noncomputable def cgJordan (lam mu : ℕ) :
    Module.End ℂ (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) :=
  DirectSum.toModule ℂ _ _
    (fun k => (DirectSum.lof ℂ _ _ k).comp (jordanShift (lam + mu - 2 * (k : ℕ) + 1)))

theorem cgJordan_lof (lam mu : ℕ) (k : Fin (min lam mu + 1))
    (w : Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) :
    cgJordan lam mu (DirectSum.lof ℂ _ _ k w)
      = DirectSum.lof ℂ _ _ k (jordanShift (lam + mu - 2 * (k : ℕ) + 1) w) := by
  rw [cgJordan, DirectSum.toModule_lof]
  rfl

/-- The block-diagonal factorial rescaling `⨁_k factScale` on `⨁_k ℂ^{M+N-1-2k}`, a linear
automorphism used to conjugate the irreducible `E` action into the standard Jordan block. -/
noncomputable def cgScale (lam mu : ℕ) :
    (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) ≃ₗ[ℂ]
      (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) :=
  DirectSum.congrLinearEquiv (fun k => factScale (lam + mu - 2 * (k : ℕ) + 1))

theorem cgScale_lof (lam mu : ℕ) (k : Fin (min lam mu + 1))
    (w : Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ) :
    cgScale lam mu (DirectSum.lof ℂ _ _ k w)
      = DirectSum.lof ℂ _ _ k (factScale (lam + mu - 2 * (k : ℕ) + 1) w) := by
  rw [cgScale, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  rfl

/-! ## The factorial rescaling conjugates the irreducible `E` action into a Jordan block

The single scalar identity behind the whole computation: on `ℂ^n = V_{n-1}`, conjugating the
raising operator `⁅sl2_e, ·⁆` by `factScale n` produces the standard nilpotent shift
`jordanShift n`. This is `sl2RepOfBlock_e` re-expressed pointwise. -/

/-- Conjugating the irreducible raising operator `⁅sl2_e, ·⁆` on `ℂ^n` by `factScale n` gives
the standard Jordan block: `factScale n ⁅sl2_e, v⁆ = J_{0,n} (factScale n v)`. -/
theorem factScale_lie_e (n : ℕ) (v : Fin n → ℂ) :
    factScale n ⁅sl2_e, v⁆ = jordanShift n (factScale n v) := by
  have h : (factScale n).conjAlgEquiv ℂ (rhoLieHom n sl2_e) = jordanShift n := by
    rw [← sl2RepOfBlock_apply]; exact sl2RepOfBlock_e n
  have h2 := LinearMap.congr_fun h (factScale n v)
  rw [LinearEquiv.conjAlgEquiv_apply] at h2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
  rw [lie_eq_rhoLieHom]
  exact h2

/-! ## The three conjugations as linear-map intertwiners -/

/-- **Tensor conjugation.** The rescaling `factScale ⊗ factScale` conjugates the `sl(2)` raising
operator `⁅sl2_e, ·⁆` on `V_λ ⊗ V_μ` into the Jordan operator `A = J_{0,M} ⊗ Id + Id ⊗ J_{0,N}`. -/
theorem factScale_congr_intertwines_e (lam mu : ℕ) :
    (TensorProduct.congr (factScale (lam + 1)) (factScale (mu + 1))).toLinearMap
        ∘ₗ LieModule.toEnd ℂ sl2 ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) sl2_e
      = jordanTensorOp lam mu ∘ₗ
          (TensorProduct.congr (factScale (lam + 1)) (factScale (mu + 1))).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe]
  rw [lie_tmul, map_add, TensorProduct.congr_tmul, TensorProduct.congr_tmul,
    TensorProduct.congr_tmul, jordanTensorOp_tmul, factScale_lie_e, factScale_lie_e]

/-- **Direct-sum conjugation.** The block rescaling `⨁ factScale` conjugates the `sl(2)` raising
operator `⁅sl2_e, ·⁆` on `⨁_k V_{λ+μ−2k}` into the block-diagonal Jordan operator `cgJordan`. -/
theorem cgScale_intertwines_e (lam mu : ℕ) :
    (cgScale lam mu).toLinearMap ∘ₗ
        LieModule.toEnd ℂ sl2
          (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)) sl2_e
      = cgJordan lam mu ∘ₗ (cgScale lam mu).toLinearMap := by
  apply DirectSum.linearMap_ext
  intro k
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe]
  rw [lie_lof, cgScale_lof, cgScale_lof, cgJordan_lof, factScale_lie_e]

/-! ## Assembling the Jordan normal form -/

/-- **Jordan normal form of `A` (Problem 2.15.1(n)).** For `V = ℂ^M ⊗ ℂ^N` (`M = λ+1`,
`N = μ+1`) and `A = J_{0,M} ⊗ Id_N + Id_M ⊗ J_{0,N}`, there is a linear isomorphism
`Θ : ℂ^M ⊗ ℂ^N ≃ₗ ⨁_{k=0}^{min(λ,μ)} ℂ^{M+N-1-2k}` intertwining `A` with the block-diagonal
sum of standard nilpotent Jordan blocks `⨁_k J_{0, M+N-1-2k}`.

Equivalently: the Jordan normal form of `A` consists of Jordan blocks of sizes
`{M+N-1-2k : k = 0 … min(M,N)-1}`, each with eigenvalue `0`. The isomorphism is assembled
from the factorial rescalings (part (l)) and the Clebsch–Gordan module isomorphism (part (m)).
This completes the `sl(2)` exercise series 2.15.1(a)–(n). -/
theorem jordan_normal_form_tensor (lam mu : ℕ) :
    ∃ Θ : ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) ≃ₗ[ℂ]
        (⨁ k : Fin (min lam mu + 1), (Fin (lam + mu - 2 * (k : ℕ) + 1) → ℂ)),
      ∀ z, Θ (jordanTensorOp lam mu z) = cgJordan lam mu (Θ z) := by
  obtain ⟨Φ⟩ := clebsch_gordan_module_iso lam mu
  set T := TensorProduct.congr (factScale (lam + 1)) (factScale (mu + 1)) with hT
  -- `Φ` intertwines the raising operator since it is an `sl(2)`-module isomorphism.
  have hΦ : ∀ z, Φ ⁅sl2_e, z⁆ = ⁅sl2_e, Φ z⁆ := fun z => Φ.toLieModuleHom.map_lie sl2_e z
  refine ⟨T.symm ≪≫ₗ Φ.toLinearEquiv ≪≫ₗ cgScale lam mu, fun z => ?_⟩
  -- Step 1: `factScale ⊗ factScale` moves `A` to the raising operator on the tensor product.
  have e1 : ⁅sl2_e, T.symm z⁆ = T.symm (jordanTensorOp lam mu z) := by
    have h := LinearMap.congr_fun (factScale_congr_intertwines_e lam mu) (T.symm z)
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, ← hT] at h
    rw [← h, LinearEquiv.symm_apply_apply]
  -- Step 3: `⨁ factScale` moves the raising operator on `⨁ V_{λ+μ−2k}` to `cgJordan`.
  have e2 := LinearMap.congr_fun (cgScale_intertwines_e lam mu) (Φ (T.symm z))
  simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe] at e2
  -- Chain the three conjugations.
  simp only [LinearEquiv.trans_apply, LieModuleEquiv.coe_toLinearEquiv]
  rw [← e1, hΦ (T.symm z), e2]

end Etingof.Sl2Irrep
