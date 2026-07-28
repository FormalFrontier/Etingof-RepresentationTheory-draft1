import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# Problem 2.3.18: The infinite dimensional Schur lemma (Dixmier)

Let `A` be an algebra over `ℂ` and let `V` be an irreducible representation of `A` with at most
countable basis. Then any homomorphism of representations `φ : V → V` is a scalar operator.

## Proof outline (following Etingof's hint)

Let `D := Module.End A V = V →ₗ[A] V`.

* By Schur's lemma (Proposition 2.3.9), `D` is a division algebra
  (`Module.End.instDivisionRing`).
* `D` is at most countably dimensional over `ℂ`: evaluation at a fixed nonzero vector `v₀`
  gives an injective `ℂ`-linear map `D → V`, so `rank ℂ D ≤ rank ℂ V ≤ ℵ₀`.
* Suppose `φ` is not a scalar. Then `φ` is *transcendental* over `ℂ`: if it were algebraic,
  its minimal polynomial would have degree one (because `ℂ` is algebraically closed and `D` is a
  domain), forcing `φ ∈ ℂ`.
* The field `ℂ(φ)` sits inside `D` as the double centralizer of `φ`
  (`Subalgebra.centralizer ℂ (Set.centralizer {φ})`), which is a commutative division subring,
  hence a field. Since `φ` is transcendental, the family `{(φ - a)⁻¹ : a ∈ ℂ}` is
  `ℂ`-linearly independent (`Transcendental.linearIndependent_sub_inv`).
* An uncountable linearly independent family forces `𝔠 = #ℂ ≤ rank ℂ D ≤ ℵ₀`, contradicting
  `ℵ₀ < 𝔠`.

## Mathlib correspondence

This is not in Mathlib. The finite-dimensional analogue is `Etingof.Corollary_2_3_10`
(`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`).
-/

open Cardinal Polynomial

namespace Etingof

/-- **Dixmier's infinite dimensional Schur lemma** (Etingof Problem 2.3.18).

Let `V` be an irreducible representation of a `ℂ`-algebra `A`, whose underlying `ℂ`-vector space
has at most countable dimension. Then any `A`-endomorphism `φ : V → V` is a scalar operator
`φ = c • id`. -/
theorem Problem_2_3_18
    {A : Type*} [Ring A] [Algebra ℂ A]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [IsSimpleModule A V]
    (hcard : Module.rank ℂ V ≤ Cardinal.aleph0)
    (φ : V →ₗ[A] V) :
    ∃ c : ℂ, ∀ v : V, φ v = c • v := by
  classical
  letI : DecidableEq (Module.End A V) := Classical.decEq _
  -- It suffices to show `φ` is in the range of the algebra map `ℂ → End A V`.
  suffices h : ∃ c : ℂ, algebraMap ℂ (Module.End A V) c = φ by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, fun v => by simp [← hc]⟩
  by_contra hcon
  rw [not_exists] at hcon
  -- `hcon : ∀ c, algebraMap ℂ (Module.End A V) c ≠ φ`, i.e. `φ` is not a scalar.
  have hnt : Nontrivial V := IsSimpleModule.nontrivial A V
  -- ## Step 1: `D = Module.End A V` is at most countably dimensional over `ℂ`.
  have hDrank : Module.rank ℂ (Module.End A V) ≤ Cardinal.aleph0 := by
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    -- Evaluation at `v₀`, as a `ℂ`-linear map.
    let ev : (Module.End A V) →ₗ[ℂ] V :=
      { toFun := fun ψ => ψ v₀
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hev_inj : Function.Injective ev := by
      rw [injective_iff_map_eq_zero]
      intro ψ hψ
      by_contra hne
      have hψv : ψ v₀ = 0 := hψ
      apply hv₀
      calc v₀ = (ψ⁻¹ * ψ) v₀ := by rw [inv_mul_cancel₀ hne]; rfl
        _ = ψ⁻¹ (ψ v₀) := rfl
        _ = ψ⁻¹ 0 := by rw [hψv]
        _ = 0 := map_zero _
    calc Module.rank ℂ (Module.End A V)
        ≤ Module.rank ℂ V := LinearMap.rank_le_of_injective ev hev_inj
      _ ≤ Cardinal.aleph0 := hcard
  -- ## Step 2: `φ` is transcendental over `ℂ`.
  have htr : Transcendental ℂ φ := by
    intro halg
    -- If `φ` is algebraic, its minimal polynomial has degree one, so `φ` is a scalar.
    have hint : IsIntegral ℂ φ := halg.isIntegral
    have hq : (minpoly ℂ φ).leadingCoeff = 1 := minpoly.monic hint
    have h1 : (minpoly ℂ φ).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hint)
    have h2 : aeval φ (minpoly ℂ φ) = 0 := minpoly.aeval ℂ φ
    rw [eq_X_add_C_of_degree_eq_one h1, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
      add_eq_zero_iff_eq_neg] at h2
    exact hcon (-(minpoly ℂ φ).coeff 0) (by rw [map_neg]; exact h2.symm)
  -- ## Step 3: build the field `K = ℂ(φ) ⊆ D` as the double centralizer of `φ`.
  set K : Subalgebra ℂ (Module.End A V) :=
    Subalgebra.centralizer ℂ (Set.centralizer ({φ} : Set (Module.End A V))) with hK
  -- `{φ} ⊆ centralizer {φ}` since `φ` commutes with itself.
  have hφS' : ({φ} : Set (Module.End A V)) ⊆ Set.centralizer {φ} := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    rw [Set.mem_centralizer_iff]
    intro m hm
    rw [Set.mem_singleton_iff] at hm; subst hm; rfl
  -- The double centralizer is contained in the centralizer: `S'' ⊆ S'`.
  have hSS' : Set.centralizer (Set.centralizer ({φ} : Set (Module.End A V)))
      ⊆ Set.centralizer {φ} := Set.centralizer_subset hφS'
  -- `φ ∈ K`.
  have hφK : φ ∈ K := by
    rw [hK, Subalgebra.mem_centralizer_iff]
    intro g hg
    exact (Set.mem_centralizer_iff.mp hg φ rfl).symm
  -- `K` is commutative.
  have hmulcomm : ∀ x y : K, x * y = y * x := by
    intro x y
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    have hxcc : (x : Module.End A V) ∈
        Set.centralizer (Set.centralizer ({φ} : Set (Module.End A V))) := x.2
    have hy : (y : Module.End A V) ∈
        Set.centralizer (Set.centralizer ({φ} : Set (Module.End A V))) := y.2
    have hx : (x : Module.End A V) ∈ Set.centralizer ({φ} : Set (Module.End A V)) := hSS' hxcc
    exact Set.mem_centralizer_iff.mp hy (x : Module.End A V) hx
  -- `K` is a field: it is a commutative division subring of the division ring `D`.
  have hIsField : IsField K := by
    refine { exists_pair_ne := ?_, mul_comm := hmulcomm, mul_inv_cancel := ?_ }
    · exact ⟨0, 1, fun h => zero_ne_one (congrArg (Subtype.val) h)⟩
    · intro a ha
      have haD : (a : Module.End A V) ≠ 0 := fun h => ha (Subtype.ext h)
      have hinv : (a : Module.End A V)⁻¹ ∈ K :=
        Set.inv_mem_centralizer₀ (a.2 : (a : Module.End A V) ∈
          Set.centralizer (Set.centralizer ({φ} : Set (Module.End A V))))
      exact ⟨⟨(a : Module.End A V)⁻¹, hinv⟩, Subtype.ext (by
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
        exact mul_inv_cancel₀ haD)⟩
  letI : Field K := hIsField.toField
  -- ## Step 4: `φ`, viewed in `K`, is transcendental, giving an uncountable independent family.
  have htrK : Transcendental ℂ (⟨φ, hφK⟩ : K) := by
    intro halg
    exact htr (by simpa using halg.algHom K.val)
  have hLIK : LinearIndependent ℂ
      (fun a : ℂ => ((⟨φ, hφK⟩ : K) - algebraMap ℂ K a)⁻¹) :=
    htrK.linearIndependent_sub_inv
  -- Push forward along the injective `ℂ`-linear inclusion `K → D`.
  have hLI : LinearIndependent ℂ
      (fun a : ℂ => ((φ - algebraMap ℂ (Module.End A V) a)⁻¹)) := by
    have hmap := hLIK.map' (K.val.toLinearMap)
      (LinearMap.ker_eq_bot.mpr (by exact Subtype.val_injective))
    have hfun : (K.val.toLinearMap ∘ fun a : ℂ => ((⟨φ, hφK⟩ : K) - algebraMap ℂ K a)⁻¹)
        = fun a : ℂ => ((φ - algebraMap ℂ (Module.End A V) a)⁻¹) := by
      funext a
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, map_inv₀, map_sub,
        AlgHom.commutes, Subalgebra.coe_val]
    rwa [hfun] at hmap
  -- ## Step 5: uncountably many independent vectors contradict countable dimension.
  have hcont : (𝔠 : Cardinal) ≤ Module.rank ℂ (Module.End A V) := by
    rw [← Cardinal.mk_complex]; exact hLI.cardinal_le_rank
  exact absurd (hcont.trans hDrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end Etingof
