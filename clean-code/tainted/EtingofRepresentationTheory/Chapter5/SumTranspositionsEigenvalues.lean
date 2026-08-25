import Mathlib
import EtingofRepresentationTheory.Chapter5.Problem5_16_2
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_ClassificationGeneral

/-!
# Sum-of-transpositions eigenvalues on an arbitrary `Sₘ`-representation

This file provides the reusable core of Problem 5.16.3(a): the central element
`C = ∑_{i<j}(ij) = sumTranspositions m` acts diagonalizably (`IsSemisimple`) on any
finite-dimensional representation `V` of `Sₘ`, and all of its eigenvalues are contents
`c(λ)` of partitions `λ ⊢ m` (in particular, integers).

## Strategy

View `V` as a module over the group algebra `A = ℂ[Sₘ]` via `ρ.asModule`; the endomorphism
`T = ρ.asAlgebraHom C` is left multiplication by `C`. Maschke's theorem makes `ρ.asModule`
a semisimple `A`-module. Because `C` is central (`sumTranspositions_central`), left
multiplication by any polynomial `q = p(C)` is `A`-linear, so its kernel is an `A`-submodule.
On each simple summand `S ≅ V_λ` (`Theorem5_12_2_classification_general`), `C` acts by the
scalar `c(λ)` (`sumTranspositions_mul_eq_content_smul`), so `q` acts by `p(c(λ))`. Taking
`p = ∏_{c ∈ contents} (X - c)` makes `p(C)` annihilate every simple summand, hence all of
`V`; `p` is squarefree, giving semisimplicity, and every eigenvalue is a root of `p`, i.e. a
content.
-/

namespace Etingof

open scoped Classical
open Polynomial

/-- Powers of `C = sumTranspositions m` act on the Specht module `V_λ` by the corresponding
power of the content scalar `c(λ)`. -/
private lemma pow_sumTranspositions_mul_specht (m : ℕ) (la : Nat.Partition m) (k : ℕ)
    {y : SymGroupAlgebra m} (hy : y ∈ SpechtModule m la) :
    sumTranspositions m ^ k * y = ((content la : ℂ) ^ k) • y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm,
      sumTranspositions_mul_eq_content_smul m la y hy, smul_smul, ← pow_succ]

/-- A polynomial `p` in `C = sumTranspositions m` acts on the Specht module `V_λ` by the scalar
`p(c(λ))`, since `C` acts by the content `c(λ)`. -/
private lemma aeval_sumTranspositions_mul_specht (m : ℕ) (la : Nat.Partition m) (p : ℂ[X])
    {y : SymGroupAlgebra m} (hy : y ∈ SpechtModule m la) :
    (Polynomial.aeval (sumTranspositions m) p) * y = (p.eval (content la : ℂ)) • y := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [map_add, add_mul, hp, hq, eval_add, add_smul]
  · intro k c
    rw [Polynomial.aeval_monomial, eval_monomial, mul_assoc,
      pow_sumTranspositions_mul_specht m la k hy, ← Algebra.smul_def, smul_smul]

/-- Any polynomial in the central element `C = sumTranspositions m` is again central. -/
private lemma aeval_sumTranspositions_comm (m : ℕ) (p : ℂ[X]) (a : SymGroupAlgebra m) :
    Commute (Polynomial.aeval (sumTranspositions m) p) a := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    simpa only [map_add] using hp.add_left hq
  · intro k c
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_left c a).mul_left
      ((show Commute (sumTranspositions m) a from sumTranspositions_central m a).pow_left k)

/-- **Reusable core of Problem 5.16.3(a).** On any finite-dimensional representation `V` of the
symmetric group `Sₘ`, the central element `C = ∑_{i<j}(ij) = sumTranspositions m` acts
semisimply (diagonalizably), and every eigenvalue of its action is the content `c(λ)` of some
partition `λ ⊢ m` (hence an integer). -/
theorem sumTranspositions_isSemisimple_and_integer_eigenvalues
    (m : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin m)) V) :
    (ρ.asAlgebraHom (sumTranspositions m)).IsSemisimple ∧
    (∀ μ : ℂ, Module.End.HasEigenvalue (ρ.asAlgebraHom (sumTranspositions m)) μ →
       ∃ la : Nat.Partition m, μ = (content la : ℂ)) := by
  classical
  set T : Module.End ℂ V := ρ.asAlgebraHom (sumTranspositions m) with hT
  -- The finite set of contents, and the annihilating polynomial `p = ∏ (X - c(λ))`.
  set S : Finset ℂ := Finset.univ.image (fun la : Nat.Partition m => (content la : ℂ)) with hS
  set p : ℂ[X] := ∏ c ∈ S, (X - C c) with hp
  set q : SymGroupAlgebra m := Polynomial.aeval (sumTranspositions m) p with hq
  -- `p` is squarefree (a product of distinct linear factors).
  have hsep := (Polynomial.separable_prod_X_sub_C_iff' (f := fun c : ℂ => c) (s := S)).mpr
    (fun x _ y _ h => h)
  have hsf : Squarefree p := by rw [hp]; exact hsep.squarefree
  -- Maschke: the group-algebra module is semisimple.
  haveI : IsSemisimpleModule (SymGroupAlgebra m) ρ.asModule := inferInstance
  -- `q = p(C)` annihilates `ρ.asModule`.
  have hqann : ∀ x : ρ.asModule, q • x = (0 : ρ.asModule) := by
    -- centrality of `q`, folded through the `set`.
    have hcomm : ∀ a : SymGroupAlgebra m, q * a = a * q := fun a => by
      rw [hq]; exact (aeval_sumTranspositions_comm m p a).eq
    -- kernel of left-multiplication by `q`, an `A`-submodule since `q` is central.
    let N : Submodule (SymGroupAlgebra m) ρ.asModule :=
      { carrier := {x | q • x = 0}
        zero_mem' := by simp
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at *
          rw [smul_add, hx, hy, add_zero]
        smul_mem' := fun a {x} hx => by
          simp only [Set.mem_setOf_eq] at *
          rw [← mul_smul, hcomm a, mul_smul, hx, smul_zero] }
    have hNtop : N = ⊤ := by
      rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (SymGroupAlgebra m) ρ.asModule]
      refine sSup_le ?_
      intro W hW
      -- `hW : IsSimpleModule A ↥W`
      haveI : IsSimpleModule (SymGroupAlgebra m) W := hW
      intro w hw
      change q • w = 0
      -- classify the simple submodule as a Specht module `V_λ`
      obtain ⟨la, ⟨φ⟩⟩ := Etingof.classification_general_u ℂ m (W : Type _)
      have hmod : SpechtModuleK ℂ m la = SpechtModule m la := by
        unfold SpechtModuleK SpechtModule
        rw [YoungSymmetrizerK_eq_mapRange ℂ m la, YoungSymmetrizer_eq_mapRange m la]
      set z : W := ⟨w, hw⟩ with hz
      have hφz_mem : (↑(φ z) : SymGroupAlgebra m) ∈ SpechtModule m la := hmod ▸ (φ z).2
      -- `q` kills `φ z`, since `p(c(λ)) = 0`.
      have h1 : q * (↑(φ z) : SymGroupAlgebra m) = 0 := by
        rw [hq, aeval_sumTranspositions_mul_specht m la p hφz_mem]
        have hev : p.eval (content la : ℂ) = 0 := by
          rw [hp, eval_prod]
          refine Finset.prod_eq_zero (i := (content la : ℂ)) ?_ ?_
          · rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ la)
          · simp
        rw [hev, zero_smul]
      have h2 : q • φ z = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_smul, smul_eq_mul, h1, Submodule.coe_zero]
      have h3 : q • z = 0 := by
        apply φ.injective
        rw [map_zero, map_smul, h2]
      have h4 : (↑(q • z) : ρ.asModule) = ↑(0 : W) := by rw [h3]
      rwa [Submodule.coe_smul, Submodule.coe_zero, show (↑z : ρ.asModule) = w from rfl] at h4
    intro x
    have hx : x ∈ N := by rw [hNtop]; exact Submodule.mem_top
    exact hx
  -- Hence `p(T) = 0`.
  have hpT : Polynomial.aeval T p = 0 := by
    have heq : Polynomial.aeval T p = ρ.asAlgebraHom q := by
      rw [hT, hq]; exact Polynomial.aeval_algHom_apply ρ.asAlgebraHom (sumTranspositions m) p
    rw [heq]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.zero_apply]
    have key := ρ.asModuleEquiv_map_smul q (ρ.asModuleEquiv.symm v)
    rw [ρ.asModuleEquiv.apply_symm_apply] at key
    rw [← key, hqann (ρ.asModuleEquiv.symm v), map_zero]
  refine ⟨Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsf hpT, ?_⟩
  -- Every eigenvalue is a root of `p`, hence a content.
  intro μ hμ
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have happ := Module.End.aeval_apply_of_hasEigenvector (p := p) hx
  rw [hpT, LinearMap.zero_apply] at happ
  have hpev : p.eval μ = 0 := by
    rcases smul_eq_zero.mp happ.symm with h | h
    · exact h
    · exact absurd h hx.2
  rw [hp, eval_prod] at hpev
  obtain ⟨c, hcS, hc0⟩ := Finset.prod_eq_zero_iff.mp hpev
  have hμc : μ = c := by
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hc0
    exact hc0
  obtain ⟨la, _, hla⟩ := Finset.mem_image.mp (hS ▸ hcS)
  exact ⟨la, hμc.trans hla.symm⟩

end Etingof
