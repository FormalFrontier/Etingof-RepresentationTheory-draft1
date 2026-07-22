import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_4

/-!
# The Frobenius-Schur trace identity (the `FS ∈ {±1}` crux)

This file proves the central Frobenius-Schur dichotomy in numerical form: for a
*simple* complex representation `ρ` with a *self-dual* character (`χ(g⁻¹) = χ(g)`),
the Frobenius-Schur indicator `FS(ρ) = |G|⁻¹ ∑_g χ(g²)` is `±1`.

## Proof strategy (the trace identity)

Work on `V ⊗ V` with the diagonal representation `T = tprod ρ ρ` and the swap
involution `τ = TensorProduct.comm`. Then:

* **Core trace identity.** For any `A : V →ₗ[ℂ] V`,
  `trace (τ ∘ map A A) = trace (A ∘ A)` (a matrix computation: the swap is a
  permutation matrix, `map A A` is a Kronecker product). With `A = ρ g`, this is
  `trace (τ ∘ T g) = χ(g²)`.
* **Projector form.** Averaging over `G`, `FS(ρ) = trace (τ ∘ P)` where
  `P = averageMap T` is the projection onto the invariants `I = T.invariants`.
* **Restriction.** `τ` preserves `I` and `P` is the identity on `I`, so
  `trace (τ ∘ P) = trace (τ|_I)`.
* **Dimension count.** For self-dual simple `ρ`, character orthonormality gives
  `dim I = |G|⁻¹ ∑_g χ(g)² = |G|⁻¹ ∑_g χ(g)χ(g⁻¹) = 1`. A linear involution on a
  one-dimensional space has trace `±1`.

The same content discharges the still-isolated trace identity in
`FrobeniusSchurRealType.lean` (`exists_nonzero_invariant_symmetric_of_FS_eq_one`,
tracked separately).
-/

open scoped MonoidAlgebra Matrix Kronecker TensorProduct
open Representation

namespace Etingof

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- **Matrix form of the swap-trace identity.** For a square matrix `A`, the trace of
the swap-permutation matrix times the Kronecker square `A ⊗ₖ A` equals `tr(A²)`. -/
private lemma matrix_trace_swap_kronecker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    (((1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix Prod.swap _root_.id) * (A ⊗ₖ A)).trace
      = (A * A).trace := by
  -- The diagonal entry at `p` of `(Pswap * K)` is `K (Prod.swap p) p`.
  have hdiag : ∀ p : ι × ι,
      (((1 : Matrix (ι × ι) (ι × ι) ℂ).submatrix Prod.swap _root_.id) * (A ⊗ₖ A)) p p
        = (A ⊗ₖ A) (Prod.swap p) p := by
    intro p
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (Prod.swap p)]
    · simp [Matrix.submatrix_apply, Matrix.one_apply]
    · intro q _ hq
      rw [Matrix.submatrix_apply, Matrix.one_apply, if_neg (by simpa [eq_comm] using hq),
        zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, hdiag, Matrix.kroneckerMap_apply, Prod.fst_swap, Prod.snd_swap,
    Matrix.mul_apply]
  -- `∑_{(i,j)} A j i * A i j = ∑_i ∑_j A i j * A j i`.
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- **The core trace identity.** For any endomorphism `A` of `V`, the trace of the swap
`τ` composed with `A ⊗ A` on `V ⊗ V` equals the trace of `A ∘ A` on `V`. -/
private lemma trace_comm_comp_map (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (V ⊗[ℂ] V)
        ((TensorProduct.comm ℂ V V : V ⊗[ℂ] V →ₗ[ℂ] V ⊗[ℂ] V) ∘ₗ TensorProduct.map A A)
      = LinearMap.trace ℂ V (A ∘ₗ A) := by
  classical
  let b := Module.finBasis ℂ V
  let bb := b.tensorProduct b
  rw [LinearMap.trace_eq_matrix_trace ℂ bb, LinearMap.trace_eq_matrix_trace ℂ b,
    LinearMap.toMatrix_comp bb bb bb, LinearMap.toMatrix_comp b b b,
    TensorProduct.toMatrix_comm b b, TensorProduct.toMatrix_map b b b b]
  exact matrix_trace_swap_kronecker (LinearMap.toMatrix b b A)

/-- **A linear involution on a one-dimensional space has trace `±1`.** -/
private lemma trace_involution_eq_pm_one {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (h1 : Module.finrank ℂ W = 1)
    (g : W →ₗ[ℂ] W) (hg : g ∘ₗ g = LinearMap.id) :
    LinearMap.trace ℂ W g = 1 ∨ LinearMap.trace ℂ W g = -1 := by
  classical
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 1) ℂ W) :=
    ⟨(Module.finBasis ℂ W).reindex (finCongr h1)⟩
  set M := LinearMap.toMatrix b b g with hM
  have hM2 : M * M = 1 := by
    rw [hM, ← LinearMap.toMatrix_comp b b b, hg, LinearMap.toMatrix_id]
  have htr : LinearMap.trace ℂ W g = M 0 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_fin_one]
  have hsq : M 0 0 * M 0 0 = 1 := by
    have h := congrFun (congrFun hM2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply] using h
  rw [htr]
  exact mul_self_eq_one_iff.mp hsq

/-- **Frobenius-Schur dichotomy (numerical form).** A simple complex representation with
self-dual character (`χ(g⁻¹) = χ(g)`) has Frobenius-Schur indicator `±1`.

This is the trace identity `FS = dim(Sym²)^G − dim(Λ²)^G` together with the Schur
bound `dim(Bil)^G = 1` for self-dual simple representations. -/
theorem frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (hsd : ∀ g, ρ.character g⁻¹ = ρ.character g) :
    Etingof.frobeniusSchurIndicator ρ = 1 ∨ Etingof.frobeniusSchurIndicator ρ = -1 := by
  classical
  haveI : Invertible (Nat.card G : ℂ) := by
    rw [Nat.card_eq_fintype_card]; infer_instance
  haveI : Representation.IsIrreducible ρ :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr hρ
  -- The diagonal representation `T` on `V ⊗ V`, the swap `cm`, and the projector `P`.
  set T : Representation ℂ G (V ⊗[ℂ] V) := Representation.tprod ρ ρ with hT
  set cm : V ⊗[ℂ] V →ₗ[ℂ] V ⊗[ℂ] V :=
    (TensorProduct.comm ℂ V V : V ⊗[ℂ] V →ₗ[ℂ] V ⊗[ℂ] V) with hcm
  -- `cm` is `G`-equivariant: `cm ∘ T g = T g ∘ cm`.
  have hequiv : ∀ g, cm ∘ₗ T g = T g ∘ₗ cm := by
    intro g
    rw [hcm, hT, Representation.tprod_apply]
    apply TensorProduct.ext'
    intro x y
    simp [TensorProduct.map_tmul]
  -- `cm` is an involution.
  have hcm2 : cm ∘ₗ cm = LinearMap.id := by
    rw [hcm]; apply TensorProduct.ext'; intro x y; simp
  -- `cm` preserves the invariants `T.invariants`.
  have hpres : ∀ x ∈ T.invariants, cm x ∈ T.invariants := by
    intro x hx
    rw [Representation.mem_invariants]
    intro g
    have key : (T g ∘ₗ cm) x = (cm ∘ₗ T g) x := by rw [hequiv]
    have hxg : T g x = x := hx g
    simpa [hxg] using key
  -- The dimension of the invariants is `1`.
  have hdim : Module.finrank ℂ (T.invariants) = 1 := by
    have hkey := Representation.card_inv_mul_sum_char_eq_finrank T
    have hortho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at hortho
    have hchar : ∀ g, T.character g = ρ.character g * ρ.character g := by
      intro g; rw [hT, Representation.char_tensor]; rfl
    have hsum : (Nat.card G : ℂ)⁻¹ * ∑ g : G, T.character g = 1 := by
      rw [Finset.sum_congr rfl (fun g _ => hchar g)]
      rw [show (∑ g : G, ρ.character g * ρ.character g)
            = ∑ g : G, ρ.character g * ρ.character g⁻¹ from
          Finset.sum_congr rfl (fun g _ => by rw [hsd g])]
      exact hortho
    rw [hkey] at hsum
    exact_mod_cast hsum
  -- `FS(ρ) = trace (cm ∘ averageMap T)`.
  have hP : T.averageMap = ⅟(Fintype.card G : ℂ) • ∑ g : G, T g := by
    simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
      Representation.asAlgebraHom_of]
  have hdist : cm ∘ₗ (∑ g : G, T g) = ∑ g : G, cm ∘ₗ T g := by
    ext z
    simp [LinearMap.sum_apply, map_sum]
  have hterm : ∀ g : G, LinearMap.trace ℂ V (ρ (g * g))
      = LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T g) := by
    intro g
    rw [hcm, hT, Representation.tprod_apply, trace_comm_comp_map,
      show ρ (g * g) = ρ g ∘ₗ ρ g by rw [map_mul]; rfl]
  have hFS : Etingof.frobeniusSchurIndicator ρ
      = LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T.averageMap) := by
    have hR : LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T.averageMap)
        = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ (V ⊗[ℂ] V) (cm ∘ₗ T g) := by
      rw [hP, LinearMap.comp_smul, hdist]
      simp only [map_smul, map_sum, smul_eq_mul, invOf_eq_inv]
    rw [hR, Etingof.frobeniusSchurIndicator]
    exact congrArg (fun s => (Fintype.card G : ℂ)⁻¹ * s)
      (Finset.sum_congr rfl (fun g _ => hterm g))
  -- Restrict to the invariants and apply the involution argument.
  have hmaps : ∀ x, (cm ∘ₗ T.averageMap) x ∈ T.invariants := by
    intro x
    exact hpres _ (T.averageMap_invariant x)
  have hmaps' : ∀ x ∈ T.invariants, (cm ∘ₗ T.averageMap) x ∈ T.invariants :=
    fun x _ => hmaps x
  have htr := LinearMap.trace_restrict_eq_of_forall_mem T.invariants
    (cm ∘ₗ T.averageMap) hmaps hmaps'
  -- The restricted map is an involution on the 1-dimensional invariants.
  set g₀ := (cm ∘ₗ T.averageMap).restrict hmaps' with hg₀
  have hg₀sq : g₀ ∘ₗ g₀ = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hx : (x : V ⊗[ℂ] V) ∈ T.invariants := x.2
    have e1 : (g₀ x : V ⊗[ℂ] V) = cm x := by
      change (cm ∘ₗ T.averageMap) (x : V ⊗[ℂ] V) = cm x
      rw [LinearMap.comp_apply, T.averageMap_id _ hx]
    have hcmx : cm (x : V ⊗[ℂ] V) ∈ T.invariants := hpres _ hx
    have e2 : (g₀ (g₀ x) : V ⊗[ℂ] V) = (x : V ⊗[ℂ] V) := by
      change (cm ∘ₗ T.averageMap) ((g₀ x : V ⊗[ℂ] V)) = (x : V ⊗[ℂ] V)
      rw [e1, LinearMap.comp_apply, T.averageMap_id _ hcmx]
      have hinv := LinearMap.congr_fun hcm2 (x : V ⊗[ℂ] V)
      simpa using hinv
    rw [LinearMap.comp_apply, e2]
    simp
  rw [hFS, ← htr]
  exact trace_involution_eq_pm_one hdim g₀ hg₀sq

end Etingof
