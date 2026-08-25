import Mathlib
import EtingofRepresentationTheory.Chapter5.MatrixCoeffInjective
import EtingofRepresentationTheory.Chapter5.CharacterIndependence

/-!
# Matrix coefficients of pairwise non-isomorphic simple representations are independent

This file proves the *cross-summand* half of Peter-Weyl orthogonality at the abstract
level. The within-summand half (`matrixCoeff_injective_of_isSimpleModule`, in
`MatrixCoeffInjective.lean`) says the matrix coefficients of a single simple
representation are independent. Here we upgrade to a finite family of pairwise
non-isomorphic simples: a tuple of matrix coefficients summing to zero forces each
summand to vanish.

Concretely, for a finite family `ρ i : Representation k G (V i)` of finite-dimensional
representations whose `asModule`s are simple `k[G]`-modules and pairwise non-isomorphic,
if `z i : Dual k (V i) ⊗ V i` satisfy

  `∑ i, contractLeft k (V i) (id ⊗ ρ i g) (z i) = 0`   for every `g : G`,

then every `z i = 0`.

## Proof strategy

The hypothesis is `k`-linear in `g`, so it extends from group elements to the whole
group algebra `k[G]` (using `Representation.asAlgebraHom`). The Jacobson-density
**separating elements** of `CharacterIndependence.exists_separating` provide, for each
index `j`, an algebra element `a` acting as the identity on `V j` and as zero on every
other `V i`. Plugging `a * g` into the extended hypothesis collapses the sum to its
`j`-th term and replaces `ρ j (a * g)` by `ρ j g`, yielding the single-summand
hypothesis `∀ g, contractLeft k (V j) (id ⊗ ρ j g) (z j) = 0`; the within-summand
engine `matrixCoeff_injective_of_isSimpleModule` then forces `z j = 0`.

No external-tensor (`GL × GL`) simplicity is needed: the argument lives entirely on the
right `GL`-action / the group algebra.
-/

open scoped TensorProduct
open Module (End)

namespace Etingof

noncomputable section

variable {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G]
variable {ι : Type*} [Fintype ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, Module.Finite k (V i)]
variable (ρ : ∀ i, Representation k G (V i))

omit [IsAlgClosed k] [∀ i, Module.Finite k (V i)] in
/-- The group-element matrix-coefficient hypothesis extends `k`-linearly to the whole
group algebra: `∑ i, contractLeft (id ⊗ ρ i.asAlgebraHom b) (z i) = 0` for every
`b : k[G]`. -/
private theorem crossMatrixCoeff_extend
    (z : ∀ i, Module.Dual k (V i) ⊗[k] V i)
    (hz : ∀ g : G, ∑ i, contractLeft k (V i)
      (TensorProduct.map LinearMap.id (ρ i g) (z i)) = 0)
    (b : MonoidAlgebra k G) :
    ∑ i, contractLeft k (V i)
      (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom b) (z i)) = 0 := by
  induction b using MonoidAlgebra.induction_on with
  | hM g =>
    simp only [Representation.asAlgebraHom_of]
    exact hz g
  | hadd f₁ f₂ h₁ h₂ =>
    have step : ∀ i, contractLeft k (V i)
        (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom (f₁ + f₂)) (z i))
      = contractLeft k (V i) (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom f₁) (z i))
        + contractLeft k (V i) (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom f₂) (z i)) := by
      intro i
      rw [map_add, TensorProduct.map_add_right, LinearMap.add_apply, map_add]
    simp only [step]
    rw [Finset.sum_add_distrib, h₁, h₂, add_zero]
  | hsmul r f h =>
    have step : ∀ i, contractLeft k (V i)
        (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom (r • f)) (z i))
      = r • contractLeft k (V i) (TensorProduct.map LinearMap.id ((ρ i).asAlgebraHom f) (z i)) := by
      intro i
      rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul]
    simp only [step]
    rw [← Finset.smul_sum, h, smul_zero]

/-- **Cross-summand matrix-coefficient independence.** For a finite family of
finite-dimensional representations `ρ i` over an algebraically closed field whose
`asModule`s are simple and pairwise non-isomorphic `k[G]`-modules, a tuple of matrix
coefficients summing to zero is identically zero. -/
theorem crossMatrixCoeff_indep
    (hsimp : ∀ i, IsSimpleModule (MonoidAlgebra k G) (ρ i).asModule)
    (hdist : Pairwise (fun i j =>
      ¬ Nonempty ((ρ i).asModule ≃ₗ[MonoidAlgebra k G] (ρ j).asModule)))
    (z : ∀ i, Module.Dual k (V i) ⊗[k] V i)
    (hz : ∀ g : G, ∑ i, contractLeft k (V i)
      (TensorProduct.map LinearMap.id (ρ i g) (z i)) = 0)
    (j : ι) : z j = 0 := by
  classical
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra k G) (ρ i).asModule := hsimp
  -- Separating element: acts as identity on `(ρ j).asModule`, zero on the others.
  obtain ⟨a, ha⟩ := CharacterIndependence.exists_separating
    (𝕜 := k) (A := MonoidAlgebra k G) (fun i => (ρ i).asModule)
    (fun _ => inferInstance) hsimp hdist j
  -- Transport the separating property to `asAlgebraHom` acting on `V i`.
  have hsep : ∀ i (w : V i),
      (ρ i).asAlgebraHom a w = if i = j then w else (0 : V i) := by
    intro i w
    have hkey := congrArg (ρ i).asModuleEquiv (ha i ((ρ i).asModuleEquiv.symm w))
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply] at hkey
    by_cases hij : i = j
    · subst hij; simpa using hkey
    · rw [if_neg hij] at hkey ⊢; simpa using hkey
  -- `asAlgebraHom a` is the identity on `V j` and zero on `V i` for `i ≠ j`.
  have hAj : (ρ j).asAlgebraHom a = 1 := by
    ext w; rw [hsep j w, if_pos rfl]; rfl
  have hAi : ∀ i, i ≠ j → (ρ i).asAlgebraHom a = 0 := by
    intro i hij; ext w; rw [hsep i w, if_neg hij]; rfl
  -- Single-summand hypothesis for `j`, from the extended hypothesis at `a * of g`.
  have hzj : ∀ g : G, contractLeft k (V j)
      (TensorProduct.map LinearMap.id (ρ j g) (z j)) = 0 := by
    intro g
    have hoff : ∀ i ∈ Finset.univ, i ≠ j → contractLeft k (V i)
        (TensorProduct.map LinearMap.id
          ((ρ i).asAlgebraHom (a * MonoidAlgebra.of k G g)) (z i)) = 0 := by
      intro i _ hij
      rw [map_mul, hAi i hij, zero_mul]
      simp
    have hext := crossMatrixCoeff_extend ρ z hz (a * MonoidAlgebra.of k G g)
    rw [Finset.sum_eq_single j hoff
      (fun h => absurd (Finset.mem_univ j) h)] at hext
    rw [map_mul, Representation.asAlgebraHom_of, hAj, one_mul] at hext
    exact hext
  -- Within-summand engine: the single-summand hypothesis forces `z j = 0`.
  haveI := hsimp j
  exact matrixCoeff_injective_of_isSimpleModule (ρ j) (z j) hzj

/-- **`Finset`-indexed cross-summand independence.** The same statement as
`crossMatrixCoeff_indep`, packaged over a `Finset s` of an arbitrary index type `Λ`
(the family `V`, `ρ` is defined on all of `Λ`, the simplicity/distinctness and the
vanishing hypothesis only over `s`). This is the form consumed by the Peter-Weyl
`iSupIndep` assembly. -/
theorem crossMatrixCoeff_indep_finset {Λ : Type*}
    (V : Λ → Type*) [∀ lam, AddCommGroup (V lam)] [∀ lam, Module k (V lam)]
    [∀ lam, Module.Finite k (V lam)]
    (ρ : ∀ lam, Representation k G (V lam))
    (s : Finset Λ)
    (hsimp : ∀ lam, IsSimpleModule (MonoidAlgebra k G) (ρ lam).asModule)
    (hdist : ∀ lam ∈ s, ∀ mu ∈ s, lam ≠ mu →
      ¬ Nonempty ((ρ lam).asModule ≃ₗ[MonoidAlgebra k G] (ρ mu).asModule))
    (z : ∀ lam, Module.Dual k (V lam) ⊗[k] V lam)
    (hz : ∀ g : G, ∑ lam ∈ s, contractLeft k (V lam)
      (TensorProduct.map LinearMap.id (ρ lam g) (z lam)) = 0)
    (lam : Λ) (hlam : lam ∈ s) : z lam = 0 :=
  crossMatrixCoeff_indep (k := k) (G := G) (ι := {lam // lam ∈ s})
    (fun i => ρ i.1)
    (fun i => hsimp i.1)
    (fun i j hij => hdist i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)))
    (fun i => z i.1)
    (fun g => by
      rw [Finset.sum_coe_sort s (fun lam => contractLeft k (V lam)
        (TensorProduct.map LinearMap.id (ρ lam g) (z lam)))]
      exact hz g)
    ⟨lam, hlam⟩

end

end Etingof
