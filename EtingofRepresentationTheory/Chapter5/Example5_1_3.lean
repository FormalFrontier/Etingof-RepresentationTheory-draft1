import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_1_1
import EtingofRepresentationTheory.Chapter5.Definition5_1_4
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurRealType
import EtingofRepresentationTheory.Chapter5.FrobeniusSchurTraceIdentity
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_Classification
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_1_5
import EtingofRepresentationTheory.Chapter4.Corollary4_2_2

/-!
# Example 5.1.3: Type Classification for Specific Groups

Examples of the real/complex/quaternionic classification (Definition 5.1.1):

1. ℤ/nℤ: representations of complex type come in conjugate pairs {V, V*}; the only
   real-type ones are the trivial representation and (for `n` even) the sign
   representation `m ↦ (-1)^m`.
2. S₃: all three irreducible representations `ℂ₊, ℂ₋, ℂ²` are of real type.
3. S₄: all five irreducible representations are of real type.
4. A₅: all five irreducible representations are of real type.
5. Q₈: the 1-dimensional representations are of real type and the 2-dimensional
   one is of quaternionic type.

## Mathlib correspondence

Uses `ZMod`, `Equiv.Perm (Fin n)`, `alternatingGroup`, and `QuaternionGroup` from
Mathlib. Irreducibility is expressed as `IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule`,
and the type predicates `Etingof.IsRealType` / `Etingof.IsQuaternionicType` come from
Definition 5.1.1.
-/

/-- For `ℤ/nℤ` (written multiplicatively), a 1-dimensional representation `ρ` on `ℂ`
whose character `g ↦ ρ g 1` takes some value other than `±1` is **not** of real type
— i.e. it is of complex type. The only real-type characters are those landing in
`{1, -1}`, namely the trivial representation and (for `n` even) the sign representation.
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_ZMod
    {n : ℕ} [NeZero n]
    (ρ : Representation ℂ (Multiplicative (ZMod n)) ℂ)
    (h : ∃ g : Multiplicative (ZMod n), ρ g 1 ≠ 1 ∧ ρ g 1 ≠ -1) :
    ¬ Etingof.IsRealType ρ := by
  -- A `G`-invariant bilinear form `B` on a 1-dimensional character `χ` satisfies
  -- `χ(g)² B(v,w) = B(v,w)`, forcing `χ(g)² = 1`, i.e. `χ(g) ∈ {1, -1}`, for all `g`
  -- where `B` is nondegenerate. The hypothesis `h` exhibits a `g` violating this.
  rintro ⟨B, _hsym, hnondeg, hinv⟩
  obtain ⟨g, hg1, hg2⟩ := h
  set χ : ℂ := ρ g 1 with hχ
  -- Every bilinear form on the 1-dimensional space `ℂ` is `B a b = a·b·(B 1 1)`.
  have key : ∀ a b : ℂ, B a b = a * b * B 1 1 := by
    intro a b
    have step : (B a) b = a • (b • B 1 1) := by
      have h1 : (B a) b = (B (a • (1:ℂ))) (b • (1:ℂ)) := by simp
      rw [h1, show B (a • (1:ℂ)) = a • B 1 from map_smul B a 1,
        LinearMap.smul_apply, show (B 1) (b • (1:ℂ)) = b • (B 1) 1 from map_smul (B 1) b 1]
    rw [step, smul_eq_mul, smul_eq_mul, mul_assoc]
  -- Nondegeneracy forces the single coefficient `B 1 1` to be nonzero.
  have hc : B 1 1 ≠ 0 := by
    intro hc0
    have : (1 : ℂ) = 0 := hnondeg 1 (fun w => by rw [key, hc0, mul_zero])
    exact one_ne_zero this
  -- `G`-invariance at `g` (with `v = w = 1`) gives `χ² · (B 1 1) = B 1 1`.
  have hinvg : χ * χ * B 1 1 = B 1 1 := by
    have := hinv g 1 1
    rw [← hχ, key] at this
    exact this
  -- Cancelling the nonzero coefficient yields `χ² = 1`, hence `χ = ±1` — contradiction.
  have hχχ : χ * χ = 1 := by
    have : χ * χ * B 1 1 = 1 * B 1 1 := by rw [one_mul]; exact hinvg
    exact mul_right_cancel₀ hc this
  rcases mul_self_eq_one_iff.mp hχχ with h1 | h1
  · exact hg1 h1
  · exact hg2 h1

namespace Etingof.S3

open Module (finrank)

/-- A 3-cycle generator of `S₃`. -/
def σ : Equiv.Perm (Fin 3) := finRotate 3
/-- A transposition generator of `S₃`. -/
def τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem σ_cube : σ ^ 3 = 1 := by decide
theorem τ_sq : τ * τ = 1 := by decide
theorem braid_rel : σ * τ = τ * σ * σ := by decide
theorem σσσσ : σ * σ * (σ * σ) = σ := by decide
theorem σ_ne : σ ≠ σ * σ := by decide
theorem conj_eq : σ * σ = τ * (σ * τ⁻¹) := by decide
theorem conj_back : σ * τ⁻¹ * τ = σ := by decide

/-- The two generators generate all of `S₃`. -/
theorem hclosure : Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
  apply Equiv.Perm.closure_prime_cycle_swap
  · rw [Fintype.card_fin]; exact Nat.prime_three
  · exact isCycle_finRotate
  · exact support_finRotate
  · exact ⟨0, 1, by decide, rfl⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]

/-- A submodule invariant under both generators `ρ σ` and `ρ τ` is invariant under the
whole representation. -/
theorem gen_inv (ρ : Representation ℂ (Equiv.Perm (Fin 3)) V) (W : Submodule ℂ V)
    (hσ : ∀ x ∈ W, ρ σ x ∈ W) (hτ : ∀ x ∈ W, ρ τ x ∈ W) :
    W ∈ ρ.invtSubmodule := by
  rw [ρ.mem_invtSubmodule]
  intro g
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  have hmem : g ∈ Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin 3))) := by
    rw [hclosure]; trivial
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hmem
  · intro x hx
    rcases hx with hx | hx
    · subst hx; exact hσ
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hτ
  · intro x hx; rw [map_one, Module.End.one_apply]; exact hx
  · intro x y _ _ Px Py z hz
    rw [map_mul, Module.End.mul_apply]; exact Px _ (Py _ hz)
  · intro x _ Px z hz
    have hxinj : Function.Injective (ρ x) := by
      have hli : Function.LeftInverse (ρ x⁻¹) (ρ x) := fun w => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      exact hli.injective
    let fW : W →ₗ[ℂ] W := (ρ x).restrict Px
    have hfWinj : Function.Injective fW := by
      intro a b hab
      apply Subtype.ext
      apply hxinj
      have ha : (fW a : V) = ρ x (a : V) := rfl
      have hb : (fW b : V) = ρ x (b : V) := rfl
      rw [← ha, ← hb, hab]
    have hfWsurj : Function.Surjective fW := LinearMap.injective_iff_surjective.mp hfWinj
    obtain ⟨a, ha⟩ := hfWsurj ⟨z, hz⟩
    have haz : ρ x (a : V) = z := congrArg Subtype.val ha
    have hxz : ρ x⁻¹ z = (a : V) := by
      rw [← haz, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hxz]; exact a.2

end Etingof.S3

/-- All irreducible representations of `S₃` are of real type: any simple
`ℂ[S₃]`-module carries a nondegenerate `S₃`-invariant symmetric bilinear form.

The Frobenius–Schur indicator of any simple `ℂ[S₃]`-module equals `1`, so the bridge
`Etingof.isRealType_of_frobeniusSchurIndicator_eq_one` gives real type. We compute
`FS(ρ) = (1/6) ∑_{g} χ(g²) = (1/6)(4·dim V + χ(c) + χ(c²))` (the squares of the six
elements are `1` four times and the two 3-cycles once each), and show
`4·dim V + χ(c) + χ(c²) = 6` by splitting on whether the 3-cycle `c = σ` acts trivially
(`E₁ = ker(ρσ - 1)` is `⊤`, forcing `dim V = 1` via the transposition's eigenvector) or
not (`E₁ = ⊥`, giving `ρσ² + ρσ + 1 = 0` and `dim V = 2` via a pair of eigenvectors).
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_S3
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin 3)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 3))) ρ.asModule) :
    Etingof.IsRealType ρ := by
  classical
  apply Etingof.isRealType_of_frobeniusSchurIndicator_eq_one ρ hρ
  -- It remains to show `frobeniusSchurIndicator ρ = 1`.
  have hSO : IsSimpleOrder ρ.invtSubmodule :=
    (Representation.mapSubmodule ρ).isSimpleOrder_iff.mpr hρ.toIsSimpleOrder
  haveI := hSO
  haveI : Nontrivial V := (Representation.invtSubmodule.nontrivial_iff ρ).mp inferInstance
  -- The crux character identity.
  have hkey : 4 * (Module.finrank ℂ V : ℂ)
      + LinearMap.trace ℂ V (ρ Etingof.S3.σ)
      + LinearMap.trace ℂ V (ρ (Etingof.S3.σ * Etingof.S3.σ)) = 6 := by
    -- `ρ σ * ρ τ = ρ τ * ρ σ * ρ σ` (the braid relation `στ = τσ²`).
    have hop : ρ Etingof.S3.σ * ρ Etingof.S3.τ
        = ρ Etingof.S3.τ * ρ Etingof.S3.σ * ρ Etingof.S3.σ := by
      rw [← map_mul ρ, ← map_mul ρ, ← map_mul ρ, Etingof.S3.braid_rel]
    -- `χ(σ²) = χ(σ)` since `σ²` is conjugate to `σ`.
    have hconj : LinearMap.trace ℂ V (ρ (Etingof.S3.σ * Etingof.S3.σ))
        = LinearMap.trace ℂ V (ρ Etingof.S3.σ) := by
      rw [Etingof.S3.conj_eq, map_mul, LinearMap.trace_mul_comm, ← map_mul, Etingof.S3.conj_back]
    -- `E₁ = ker(ρσ - 1)` is `ρ`-invariant.
    have hE1inv : LinearMap.ker (ρ Etingof.S3.σ - 1) ∈ ρ.invtSubmodule := by
      apply Etingof.S3.gen_inv
      · intro x hx
        have hx' : ρ Etingof.S3.σ x = x := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
          exact hx
        rw [hx', LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        exact hx'
      · intro x hx
        have hx' : ρ Etingof.S3.σ x = x := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
          exact hx
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        calc ρ Etingof.S3.σ (ρ Etingof.S3.τ x)
            = (ρ Etingof.S3.σ * ρ Etingof.S3.τ) x := by rw [Module.End.mul_apply]
          _ = (ρ Etingof.S3.τ * ρ Etingof.S3.σ * ρ Etingof.S3.σ) x := by rw [hop]
          _ = ρ Etingof.S3.τ (ρ Etingof.S3.σ (ρ Etingof.S3.σ x)) := by
                rw [Module.End.mul_apply, Module.End.mul_apply]
          _ = ρ Etingof.S3.τ x := by rw [hx', hx']
    rcases hSO.eq_bot_or_eq_top (⟨_, hE1inv⟩ : ρ.invtSubmodule) with hb | ht
    · -- `E₁ = ⊥`: `ρσ` has no eigenvalue `1`, so `dim V = 2` and `χ(σ) = -1`.
      have hE : LinearMap.ker (ρ Etingof.S3.σ - 1) = ⊥ := by
        have := congrArg Subtype.val hb
        rwa [Representation.invtSubmodule.coe_bot] at this
      have hsinj : Function.Injective ((ρ Etingof.S3.σ - 1 : Module.End ℂ V)) := by
        rw [← LinearMap.ker_eq_bot]; exact hE
      have hcube : (ρ Etingof.S3.σ) ^ 3 = 1 := by
        rw [← map_pow, Etingof.S3.σ_cube, map_one]
      have hquad : ((ρ Etingof.S3.σ) ^ 2 + ρ Etingof.S3.σ + 1 : Module.End ℂ V) = 0 := by
        have hfactor : (ρ Etingof.S3.σ - 1) * ((ρ Etingof.S3.σ) ^ 2 + ρ Etingof.S3.σ + 1) = 0 := by
          have h : (ρ Etingof.S3.σ - 1) * ((ρ Etingof.S3.σ) ^ 2 + ρ Etingof.S3.σ + 1)
              = (ρ Etingof.S3.σ) ^ 3 - 1 := by noncomm_ring
          rw [h, hcube, sub_self]
        ext x
        simp only [LinearMap.zero_apply]
        apply hsinj
        rw [map_zero, ← Module.End.mul_apply, hfactor, LinearMap.zero_apply]
      have hsq : (ρ Etingof.S3.σ) ^ 2 = ρ (Etingof.S3.σ * Etingof.S3.σ) := by rw [map_mul, sq]
      have htr : LinearMap.trace ℂ V (ρ Etingof.S3.σ)
          + LinearMap.trace ℂ V (ρ Etingof.S3.σ) + (Module.finrank ℂ V : ℂ) = 0 := by
        have h := congrArg (LinearMap.trace ℂ V) hquad
        rw [map_add, map_add, LinearMap.trace_one, map_zero, hsq, hconj] at h
        exact h
      -- An eigenvector `v` of `ρσ`, eigenvalue `μ ≠ 1`, plus `ρτ v` (eigenvalue `μ²`).
      obtain ⟨μ, hμev⟩ := Module.End.exists_eigenvalue (ρ Etingof.S3.σ)
      obtain ⟨v, hv⟩ := hμev.exists_hasEigenvector
      have hv0 : v ≠ 0 := hv.2
      have hσv : ρ Etingof.S3.σ v = μ • v := hv.apply_eq_smul
      have hμ1 : μ ≠ 1 := by
        intro h
        apply hv0
        have hker : v ∈ LinearMap.ker (ρ Etingof.S3.σ - 1) := by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hσv, h, one_smul,
            sub_self]
        rw [hE, Submodule.mem_bot] at hker; exact hker
      have hμ3 : μ ^ 3 = 1 := by
        have h1 : ((ρ Etingof.S3.σ) ^ 3) v = v := by rw [hcube, Module.End.one_apply]
        rw [hv.pow_apply 3] at h1
        have hh : (μ ^ 3 - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
        rcases smul_eq_zero.mp hh with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hv0
      have hμ2 : μ ^ 2 ≠ μ := by
        intro h
        have hμ0 : μ ≠ 0 := fun h0 => by rw [h0] at hμ3; norm_num at hμ3
        apply hμ1
        apply mul_left_cancel₀ hμ0
        rw [mul_one, ← sq, h]
      have hτinj : Function.Injective (ρ Etingof.S3.τ) := by
        have hli : Function.LeftInverse (ρ Etingof.S3.τ⁻¹) (ρ Etingof.S3.τ) := fun w => by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        exact hli.injective
      have hτv0 : ρ Etingof.S3.τ v ≠ 0 := fun h => hv0 (hτinj (by rw [h, map_zero]))
      have hσu : ρ Etingof.S3.σ (ρ Etingof.S3.τ v) = μ ^ 2 • ρ Etingof.S3.τ v := by
        calc ρ Etingof.S3.σ (ρ Etingof.S3.τ v)
            = (ρ Etingof.S3.σ * ρ Etingof.S3.τ) v := by rw [Module.End.mul_apply]
          _ = (ρ Etingof.S3.τ * ρ Etingof.S3.σ * ρ Etingof.S3.σ) v := by rw [hop]
          _ = ρ Etingof.S3.τ (ρ Etingof.S3.σ (ρ Etingof.S3.σ v)) := by
                rw [Module.End.mul_apply, Module.End.mul_apply]
          _ = ρ Etingof.S3.τ (μ ^ 2 • v) := by rw [hσv, map_smul, hσv, smul_smul, ← sq]
          _ = μ ^ 2 • ρ Etingof.S3.τ v := by rw [map_smul]
      have hindep : LinearIndependent ℂ (![v, ρ Etingof.S3.τ v] : Fin 2 → V) := by
        apply Module.End.eigenvectors_linearIndependent' (ρ Etingof.S3.σ)
          (![μ, μ ^ 2] : Fin 2 → ℂ) ?_ (![v, ρ Etingof.S3.τ v])
        · intro i
          fin_cases i
          · exact ⟨Module.End.mem_eigenspace_iff.mpr hσv, hv0⟩
          · exact ⟨Module.End.mem_eigenspace_iff.mpr hσu, hτv0⟩
        · intro i j hij
          fin_cases i <;> fin_cases j <;>
            simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
      have hWinv : (Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V)) ∈ ρ.invtSubmodule := by
        apply Etingof.S3.gen_inv
        · intro x hx
          have hle : Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V)
              ≤ (Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V)).comap (ρ Etingof.S3.σ) := by
            rw [Submodule.span_le]
            rintro y (rfl | hy)
            · rw [SetLike.mem_coe, Submodule.mem_comap, hσv]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
            · rw [Set.mem_singleton_iff] at hy; subst hy
              rw [SetLike.mem_coe, Submodule.mem_comap, hσu]
              exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
          exact hle hx
        · intro x hx
          have hle : Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V)
              ≤ (Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V)).comap (ρ Etingof.S3.τ) := by
            rw [Submodule.span_le]
            rintro y (rfl | hy)
            · rw [SetLike.mem_coe, Submodule.mem_comap]
              exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
            · rw [Set.mem_singleton_iff] at hy; subst hy
              rw [SetLike.mem_coe, Submodule.mem_comap,
                show ρ Etingof.S3.τ (ρ Etingof.S3.τ v) = v by
                  rw [← Module.End.mul_apply, ← map_mul, Etingof.S3.τ_sq, map_one,
                    Module.End.one_apply]]
              exact Submodule.subset_span (Set.mem_insert _ _)
          exact hle hx
      have hWtop : Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V) = ⊤ := by
        rcases hSO.eq_bot_or_eq_top (⟨_, hWinv⟩ : ρ.invtSubmodule) with h | h
        · exfalso
          have hb' : Submodule.span ℂ ({v, ρ Etingof.S3.τ v} : Set V) = ⊥ := by
            have := congrArg Subtype.val h
            rwa [Representation.invtSubmodule.coe_bot] at this
          apply hv0
          have : v ∈ (⊥ : Submodule ℂ V) := by
            rw [← hb']; exact Submodule.subset_span (Set.mem_insert _ _)
          rwa [Submodule.mem_bot] at this
        · have := congrArg Subtype.val h
          rwa [Representation.invtSubmodule.coe_top] at this
      have hrange : Set.range (![v, ρ Etingof.S3.τ v] : Fin 2 → V) = {v, ρ Etingof.S3.τ v} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
      let B : Module.Basis (Fin 2) ℂ V := Module.Basis.mk hindep (le_of_eq (by rw [hrange, hWtop]))
      have hd2 : Module.finrank ℂ V = 2 := by rw [Module.finrank_eq_card_basis B]; simp
      have hcast : (Module.finrank ℂ V : ℂ) = 2 := by rw [hd2]; norm_num
      rw [hconj, hcast]
      rw [hcast] at htr
      linear_combination htr
    · -- `E₁ = ⊤`: `ρσ = 1`, so `dim V = 1` via the transposition's eigenvector.
      have hE : LinearMap.ker (ρ Etingof.S3.σ - 1) = ⊤ := by
        have := congrArg Subtype.val ht
        rwa [Representation.invtSubmodule.coe_top] at this
      have hs1 : ρ Etingof.S3.σ = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp hE)
      obtain ⟨ν, hνev⟩ := Module.End.exists_eigenvalue (ρ Etingof.S3.τ)
      obtain ⟨w, hw⟩ := hνev.exists_hasEigenvector
      have hw0 : w ≠ 0 := hw.2
      have hτw : ρ Etingof.S3.τ w = ν • w := hw.apply_eq_smul
      have hW'inv : (Submodule.span ℂ ({w} : Set V)) ∈ ρ.invtSubmodule := by
        apply Etingof.S3.gen_inv
        · intro x hx; rw [hs1, Module.End.one_apply]; exact hx
        · intro x hx
          have hle : Submodule.span ℂ ({w} : Set V)
              ≤ (Submodule.span ℂ ({w} : Set V)).comap (ρ Etingof.S3.τ) := by
            rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
              Submodule.mem_comap, hτw]
            exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
          exact hle hx
      have hW'top : Submodule.span ℂ ({w} : Set V) = ⊤ := by
        rcases hSO.eq_bot_or_eq_top (⟨_, hW'inv⟩ : ρ.invtSubmodule) with h | h
        · exfalso
          have hb' : Submodule.span ℂ ({w} : Set V) = ⊥ := by
            have := congrArg Subtype.val h
            rwa [Representation.invtSubmodule.coe_bot] at this
          apply hw0
          have : w ∈ (⊥ : Submodule ℂ V) := by
            rw [← hb']; exact Submodule.subset_span rfl
          rwa [Submodule.mem_bot] at this
        · have := congrArg Subtype.val h
          rwa [Representation.invtSubmodule.coe_top] at this
      have hd1 : Module.finrank ℂ V = 1 := by
        have h1 : Module.finrank ℂ V
            = Module.finrank ℂ (Submodule.span ℂ ({w} : Set V)) := by rw [hW'top, finrank_top]
        rw [h1, finrank_span_singleton hw0]
      have hcast : (Module.finrank ℂ V : ℂ) = 1 := by rw [hd1]; norm_num
      have hT : LinearMap.trace ℂ V (ρ Etingof.S3.σ) = 1 := by
        rw [hs1, LinearMap.trace_one, hcast]
      have hT2 : LinearMap.trace ℂ V (ρ (Etingof.S3.σ * Etingof.S3.σ)) = 1 := by
        rw [map_mul, hs1, mul_one, LinearMap.trace_one, hcast]
      rw [hT, hT2, hcast]; norm_num
  -- Assemble: reduce the indicator to the character identity.
  unfold Etingof.frobeniusSchurIndicator
  have hsum : ∑ g : Equiv.Perm (Fin 3), LinearMap.trace ℂ V (ρ (g * g))
      = 4 * LinearMap.trace ℂ V (ρ 1) + LinearMap.trace ℂ V (ρ Etingof.S3.σ)
        + LinearMap.trace ℂ V (ρ (Etingof.S3.σ * Etingof.S3.σ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g => g * g = 1)]
    have e1 : ∑ g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => g * g = 1),
        LinearMap.trace ℂ V (ρ (g * g))
        = ∑ _g ∈ Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => g * g = 1),
          LinearMap.trace ℂ V (ρ 1) :=
      Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.mp hg).2])
    have hc : (Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => g * g = 1)).card = 4 := by decide
    have e2 : (Finset.univ.filter (fun g : Equiv.Perm (Fin 3) => ¬ g * g = 1))
        = {Etingof.S3.σ, Etingof.S3.σ * Etingof.S3.σ} := by decide
    rw [e1, Finset.sum_const, hc, e2, Finset.sum_pair Etingof.S3.σ_ne, Etingof.S3.σσσσ]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have htr1 : LinearMap.trace ℂ V (ρ 1) = (Module.finrank ℂ V : ℂ) := by
    rw [map_one, LinearMap.trace_one]
  have hcard : (Fintype.card (Equiv.Perm (Fin 3)) : ℂ) = 6 := by
    rw [Fintype.card_perm, Fintype.card_fin]; norm_num
  rw [hsum, htr1, hkey, hcard]
  norm_num

/-!
## Group-algebra real form: the coordinate dot-product form

For any finite group `G`, the group algebra `ℂ[G]` carries the symmetric bilinear
form `Φ(x, y) = ∑_g (x g)(y g)` ("make the group basis orthonormal"). Left
multiplication permutes the coordinates, so `Φ` is invariant under the left-regular
action — and `Φ(c, c) = ∑_g (c g)² > 0` whenever `c ≠ 0` has **real** coefficients.

Transporting `Φ` along a `ℂ[G]`-linear embedding `V ↪ ℂ[G]` of a simple
representation onto the left ideal `ℂ[G]·c` (with `c` real and nonzero) produces a
nonzero invariant symmetric form on `V`, hence (by simplicity) a nondegenerate one:
`V` is of real type. This is the engine behind "every irreducible of `Sₙ` is of real
type": the Specht module `V_λ = ℂ[Sₙ]·c_λ` is generated by the Young symmetrizer
`c_λ`, which has **integer** coefficients. -/
section GroupAlgebraRealForm

open scoped MonoidAlgebra
open MonoidAlgebra

variable {G : Type*} [Group G] [Fintype G]

/-- The coordinate dot-product symmetric bilinear form on the group algebra:
`coordForm x y = ∑_g (x g) * (y g)`. -/
noncomputable def coordForm :
    MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G →ₗ[ℂ] ℂ :=
  ∑ g : G, (LinearMap.mul ℂ ℂ).compl₁₂ (Finsupp.lapply g) (Finsupp.lapply g)

lemma coordForm_apply (x y : MonoidAlgebra ℂ G) :
    coordForm x y = ∑ g : G, x g * y g := by
  simp only [coordForm, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
  rfl

lemma coordForm_symm (x y : MonoidAlgebra ℂ G) : coordForm x y = coordForm y x := by
  rw [coordForm_apply, coordForm_apply]
  exact Finset.sum_congr rfl fun g _ => mul_comm _ _

/-- `coordForm` is invariant under left multiplication by a group element. -/
lemma coordForm_of_mul (h : G) (x y : MonoidAlgebra ℂ G) :
    coordForm (of ℂ G h * x) (of ℂ G h * y) = coordForm x y := by
  rw [coordForm_apply, coordForm_apply]
  have hx : ∀ g : G, (of ℂ G h * x) g = x (h⁻¹ * g) := by
    intro g; rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, one_mul]
  have hy : ∀ g : G, (of ℂ G h * y) g = y (h⁻¹ * g) := by
    intro g; rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, one_mul]
  simp only [hx, hy]
  exact Equiv.sum_comp (Equiv.mulLeft h⁻¹) (fun g => x g * y g)

/-- If `c` has real coefficients and is nonzero, `coordForm c c = ∑_g (c g)² ≠ 0`. -/
lemma coordForm_self_ne_zero_of_real (c : MonoidAlgebra ℂ G)
    (hreal : ∀ x, (c x).im = 0) (hc : c ≠ 0) : coordForm c c ≠ 0 := by
  have hre : ∀ g : G, c g * c g = (((c g).re ^ 2 : ℝ) : ℂ) := by
    intro g
    have h := hreal g
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, h, pow_two]
  have key : coordForm c c = (((∑ g : G, (c g).re ^ 2) : ℝ) : ℂ) := by
    rw [coordForm_apply, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun g _ => hre g
  rw [key, Ne, Complex.ofReal_eq_zero]
  intro hsum
  apply hc
  have hzero : ∀ g : G, (c g).re = 0 := by
    intro g
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => sq_nonneg ((c g).re)).mp hsum g
      (Finset.mem_univ g)
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h
  ext g
  apply Complex.ext
  · simpa using hzero g
  · simpa using hreal g

/-- **Group-algebra real-form engine.** A simple representation `ρ` admitting a
`ℂ`-linear map `ψ : V → ℂ[G]` that intertwines the `ρ`-action with left
multiplication, and carrying a real, nonzero element `c = ψ v₀` in its image, is of
real type: pull back the coordinate dot-product form `coordForm`. -/
theorem isRealType_of_coordForm_transport
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule)
    (ψ : V →ₗ[ℂ] MonoidAlgebra ℂ G)
    (hψ : ∀ g v, ψ (ρ g v) = of ℂ G g * ψ v)
    (c : MonoidAlgebra ℂ G) (hreal : ∀ x, (c x).im = 0)
    (v₀ : V) (hv₀ : ψ v₀ = c) (hcne : c ≠ 0) :
    Etingof.IsRealType ρ := by
  set B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ := coordForm.compl₁₂ ψ ψ with hB
  have hBapply : ∀ v w, B v w = coordForm (ψ v) (ψ w) := fun v w => by
    simp [hB, LinearMap.compl₁₂_apply]
  have hsym : ∀ v w, B v w = B w v := fun v w => by
    rw [hBapply, hBapply]; exact coordForm_symm _ _
  have hinv : ∀ g v w, B (ρ g v) (ρ g w) = B v w := fun g v w => by
    rw [hBapply, hBapply, hψ, hψ, coordForm_of_mul]
  have hBne : B ≠ 0 := by
    intro h0
    have hzero : B v₀ v₀ = 0 := by rw [h0]; simp
    rw [hBapply, hv₀] at hzero
    exact coordForm_self_ne_zero_of_real c hreal hcne hzero
  exact ⟨B, hsym, Etingof.nondegenerate_of_invariant_of_simple ρ hρ B hBne hinv, hinv⟩

end GroupAlgebraRealForm

/-- The Young symmetrizer `c_λ` over `ℂ` has real (indeed integer) coefficients,
since it is the base change of the integer Young symmetrizer `YoungSymmetrizerZ`. -/
lemma Etingof.youngSymmetrizer_im_eq_zero (n : ℕ) (la : Nat.Partition n)
    (x : Equiv.Perm (Fin n)) : (Etingof.YoungSymmetrizer n la x).im = 0 := by
  rw [Etingof.YoungSymmetrizer_eq_mapRange, MonoidAlgebra.mapRingHom_apply]
  simp

/-- All irreducible representations of `S₄` are of real type. (Etingof Example 5.1.3)

Every simple `ℂ[S₄]`-module is isomorphic to a Specht module `V_λ` (Theorem 5.12.2),
which is the left ideal `ℂ[S₄]·c_λ` generated by the integer-coefficient Young
symmetrizer `c_λ`. Transporting the coordinate dot-product form along this iso gives
a nondegenerate invariant symmetric form — `V` is of real type. -/
theorem Etingof.Example5_1_3_S4
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin 4)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) ρ.asModule) :
    Etingof.IsRealType ρ := by
  classical
  haveI := hρ
  -- Embed `ρ.asModule` as a left ideal `I ⊆ ℂ[S₄]` (this lands in universe `0`),
  -- then classify `I` as a Specht module via Theorem 5.12.2.
  obtain ⟨I, ⟨φ_M⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
      (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) ρ.asModule
  haveI : IsSimpleModule (MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) I :=
    IsSimpleModule.congr φ_M.symm
  obtain ⟨la, ⟨φ_I⟩⟩ := Etingof.Theorem5_12_2_classification 4 I
  -- `Ψ : ρ.asModule ≃ₗ[ℂ[S₄]] V_λ`.
  set Ψ := φ_M.trans φ_I with hΨ
  set c := Etingof.YoungSymmetrizer 4 la with hc
  have hc_mem : c ∈ Etingof.SpechtModule 4 la := Submodule.subset_span rfl
  -- The intertwiner `ψ : V → ℂ[S₄]`, `v ↦ ↑(Ψ (asModuleEquiv⁻¹ v))`.
  set ψ : V →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin 4)) :=
    ((Etingof.SpechtModule 4 la).subtype.restrictScalars ℂ).comp
      ((Ψ.restrictScalars ℂ).toLinearMap.comp ρ.asModuleEquiv.symm.toLinearMap) with hψdef
  have hψ_apply : ∀ v : V,
      ψ v = (Ψ (ρ.asModuleEquiv.symm v) : MonoidAlgebra ℂ (Equiv.Perm (Fin 4))) := by
    intro v; rfl
  -- `ψ` intertwines the `ρ`-action with left multiplication.
  have hψ : ∀ (g : Equiv.Perm (Fin 4)) (v : V),
      ψ (ρ g v) = MonoidAlgebra.of ℂ (Equiv.Perm (Fin 4)) g * ψ v := by
    intro g v
    rw [hψ_apply, hψ_apply, ρ.asModuleEquiv_symm_map_rho, map_smul]
    simp only [Submodule.coe_smul, smul_eq_mul]
  -- `c` is real and nonzero, and lies in the image of `ψ`.
  have hcne : c ≠ 0 := by
    intro h0
    rw [hc] at h0
    exact Etingof.young_symmetrizer_sq_ne_zero 4 la (by rw [h0, mul_zero])
  set v₀ : V := ρ.asModuleEquiv (Ψ.symm ⟨c, hc_mem⟩) with hv₀def
  have hv₀ : ψ v₀ = c := by
    rw [hψ_apply, hv₀def, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  exact isRealType_of_coordForm_transport ρ hρ ψ hψ c
    (Etingof.youngSymmetrizer_im_eq_zero 4 la) v₀ hv₀ hcne

set_option maxRecDepth 10000 in
/-- **A₅ is ambivalent:** every element is conjugate to its inverse. A finite
check over the 60 elements of `A₅` (`decide`). This is the input to L2 / the
self-dual dichotomy: it makes every `A₅` character self-dual (`χ(g⁻¹) = χ(g)`). -/
theorem Etingof.alternatingGroup_ambivalent (g : alternatingGroup (Fin 5)) :
    IsConj g g⁻¹ := by
  have h : ∀ h : alternatingGroup (Fin 5), ∃ c : alternatingGroup (Fin 5),
      c * h * c⁻¹ = h⁻¹ := by decide
  obtain ⟨c, hc⟩ := h g
  exact isConj_iff.mpr ⟨c, hc⟩

/-- **Arithmetic core of the A₅ real-type argument (the Cauchy-Schwarz endgame).**

`A₅` has five irreducible representations (its number of conjugacy classes), with
positive integer dimensions `d i` and Frobenius-Schur indicators `ε i ∈ {+1, -1}`.
The value `0` is excluded because `A₅` is ambivalent (`alternatingGroup_ambivalent`),
so no irreducible is of complex type. The two global identities

* `∑ᵢ (d i)² = 60 = |A₅|`  (sum of squared dimensions equals the group order), and
* `∑ᵢ (ε i)·(d i) = 16 = #{g ∈ A₅ : g² = 1}`  (the Frobenius-Schur involution count),

together with the Cauchy-Schwarz bound `(∑ᵢ d i)² ≤ 5 · ∑ᵢ (d i)² = 300`
(`sq_sum_le_card_mul_sum_sq`) force **every** indicator to be `+1`. Hence every
`A₅` irreducible is of real type.

This packages the combinatorial heart of the classification with no representation
theory: a single `+1 → −1` sign flip on a dimension `d i ≥ 1` would raise `∑ᵢ d i`
by `2·(d i) ≥ 2` to at least `18`, whose square `324` exceeds the Cauchy-Schwarz
ceiling `300`. So the `{1, 3, 3, 4, 5}` dimension list never has to be exhibited;
only the two sums and the count of `5` irreducibles are needed.

The three inputs (`∑ d² = |G|`, the indicator count `= #{g : g² = 1}`, and
`#irreps = #conjugacy classes = 5`) are the missing-from-Mathlib foundations that
the even-dimensional `A₅` case is blocked on; this lemma is the verified endgame
they feed into. -/
lemma Etingof.A5_frobeniusSchur_all_pos
    (d ε : Fin 5 → ℤ)
    (hd : ∀ i, 1 ≤ d i)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsq : ∑ i, d i ^ 2 = 60)
    (hcount : ∑ i, ε i * d i = 16) :
    ∀ i, ε i = 1 := by
  -- Cauchy-Schwarz: `(∑ d)² ≤ card · ∑ d² = 5 · 60 = 300`.
  have hcheb : (∑ i, d i) ^ 2 ≤ 5 * ∑ i, d i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 5))) (f := d)
    simpa using h
  rw [hsq] at hcheb
  set T := ∑ j, d j with hT
  intro i
  by_contra hi
  have hneg : ε i = -1 := (hε i).resolve_left hi
  -- The "defect" `d j - ε j · d j = (1 - ε j)·d j` is nonnegative everywhere, and is
  -- `≥ 2` at the index `i` where the sign is `-1`.
  have hf_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 5)), (0 : ℤ) ≤ d j - ε j * d j := by
    intro j _
    rcases hε j with hj | hj
    · rw [hj]; simp
    · rw [hj]; nlinarith [hd j]
  have hsum_def : ∑ j, (d j - ε j * d j) = T - 16 := by
    rw [Finset.sum_sub_distrib, hcount, hT]
  have hfi : (2 : ℤ) ≤ d i - ε i * d i := by rw [hneg]; nlinarith [hd i]
  have hsingle : d i - ε i * d i ≤ ∑ j, (d j - ε j * d j) :=
    Finset.single_le_sum hf_nonneg (Finset.mem_univ i)
  have hTge : (18 : ℤ) ≤ T := by rw [hsum_def] at hsingle; linarith
  nlinarith [hcheb, hTge]

section A5EvenAssembly

open CategoryTheory

/-- **General-index Cauchy-Schwarz endgame.** The cardinality-`5`, arbitrary-index
form of `Etingof.A5_frobeniusSchur_all_pos`: for any `5`-element index type `ι` with
positive integer dimensions `d i ≥ 1` and indicators `ε i ∈ {±1}`, the two global
identities `∑ d² = 60` and `∑ ε·d = 16` force every `ε i = 1`. This is the form the
Wedderburn family of `A₅` (indexed by `Fin D.n` with `D.n = 5`) feeds into, sparing a
`Fin D.n ≃ Fin 5` re-indexing. -/
lemma Etingof.frobeniusSchur_all_pos_general {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι = 5) (d ε : ι → ℤ)
    (hd : ∀ i, 1 ≤ d i) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hsq : ∑ i, d i ^ 2 = 60) (hcount : ∑ i, ε i * d i = 16) :
    ∀ i, ε i = 1 := by
  have hcheb : (∑ i, d i) ^ 2 ≤ 5 * ∑ i, d i ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := d)
    rw [Finset.card_univ, hcard] at h
    simpa using h
  rw [hsq] at hcheb
  set T := ∑ j, d j with hT
  intro i
  by_contra hi
  have hneg : ε i = -1 := (hε i).resolve_left hi
  have hf_nonneg : ∀ j ∈ (Finset.univ : Finset ι), (0 : ℤ) ≤ d j - ε j * d j := by
    intro j _
    rcases hε j with hj | hj
    · rw [hj]; simp
    · rw [hj]; nlinarith [hd j]
  have hsum_def : ∑ j, (d j - ε j * d j) = T - 16 := by
    rw [Finset.sum_sub_distrib, hcount, hT]
  have hfi : (2 : ℤ) ≤ d i - ε i * d i := by rw [hneg]; nlinarith [hd i]
  have hsingle : d i - ε i * d i ≤ ∑ j, (d j - ε j * d j) :=
    Finset.single_le_sum hf_nonneg (Finset.mem_univ i)
  have hTge : (18 : ℤ) ≤ T := by rw [hsum_def] at hsingle; linarith
  nlinarith [hcheb, hTge]

/-- The Frobenius-Schur indicator depends only on the character: equal-character
representations have equal indicators (since `FS(ρ) = |G|⁻¹ ∑_g χ_ρ(g²)`). -/
lemma Etingof.frobeniusSchurIndicator_eq_of_character_eq
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (h : ∀ g, Representation.character ρ g = Representation.character σ g) :
    Etingof.frobeniusSchurIndicator ρ = Etingof.frobeniusSchurIndicator σ := by
  simp only [Etingof.frobeniusSchurIndicator]
  congr 1
  exact Finset.sum_congr rfl (fun g _ => h (g * g))

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- A full faithful functor preserving monomorphisms reflects `Simple` objects. -/
private lemma simple_of_full_faithful_preservesMono' {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

/-- Bridge: the module-level simplicity `IsSimpleModule (ℂ[G]) ρ.asModule` upgrades to
categorical `Simple (FDRep.of ρ)`, via the `Rep ≃ Module ℂ[G]` equivalence. -/
private lemma simple_FDRep_of_isSimpleModule [NeZero (Nat.card G : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ G V)
    [IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule] :
    Simple (FDRep.of ρ) := by
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)
  haveI : Simple (E.functor.obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ G) ρ.asModule)
    exact simple_of_isSimpleModule
  haveI : Simple ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of ρ)) :=
    simple_of_full_faithful_preservesMono' E.functor _
  exact simple_of_full_faithful_preservesMono' (forget₂ (FDRep ℂ G) (Rep ℂ G)) _

/-- **Frobenius-Schur type dichotomy.** For a simple complex `FDRep` `W` with a
self-dual character (`χ(g⁻¹) = χ(g)`, supplied by an ambivalent group), the
Frobenius-Schur indicator is `±1`. Equivalently: `W` is of real or quaternionic type,
never complex type. This is the Frobenius-Schur trace identity
`FS = dim(Sym²V)^G − dim(Λ²V)^G` together with self-duality forcing the total
invariant-form dimension to `1`, proved as
`Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple` in
`FrobeniusSchurTraceIdentity.lean`. -/
private lemma frobeniusSchurIndicator_pm_one_of_simple_selfDual
    [NeZero (Nat.card G : ℂ)] [Invertible (Fintype.card G : ℂ)]
    (W : FDRep ℂ G) (hW : IsSimpleModule (MonoidAlgebra ℂ G) (Representation.asModule W.ρ))
    (hsd : ∀ g, Representation.character W.ρ g⁻¹ = Representation.character W.ρ g) :
    Etingof.frobeniusSchurIndicator W.ρ = 1 ∨ Etingof.frobeniusSchurIndicator W.ρ = -1 :=
  Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple W.ρ hW hsd

/-- **The 4-dimensional (standard) irreducible of `A₅` is of real type.** Every
even-dimensional simple `ℂ[A₅]`-module is of real type.

The proof assembles the verified Frobenius-Schur foundations rather than exhibiting the
concrete `{1, 3, 3, 4, 5}` dimension list. Working with the Wedderburn family
`W = D.columnFDRep` of the group algebra `ℂ[A₅]`:

* there are exactly `5` irreducibles (`D.n = #ConjClasses A₅ = 5`,
  `IrrepDecomp.n_eq_card_conjClasses'`);
* `∑ᵢ (dim Wᵢ)² = 60 = |A₅|` (`IrrepDecomp.sum_finrank_sq_eq_card`);
* `∑ᵢ FS(Wᵢ)·dim Wᵢ = #{g : g² = 1} = 16` (`Etingof.frobeniusSchur_involution_count`);
* each `FS(Wᵢ) ∈ {±1}` since `A₅` is ambivalent (`alternatingGroup_ambivalent` gives
  self-dual characters, ruling out complex type).

Feeding these into the Cauchy-Schwarz endgame `frobeniusSchur_all_pos_general` forces
every `FS(Wᵢ) = 1`; the abstract `ρ` is isomorphic to some `Wᵢ` (Schur), so
`FS(ρ) = 1` and `isRealType_of_frobeniusSchurIndicator_eq_one` finishes.

The per-irreducible step `FS(Wᵢ) ∈ {±1}` is `frobeniusSchurIndicator_pm_one_of_simple_selfDual`,
now proved via the Frobenius-Schur trace identity
`Etingof.frobeniusSchurIndicator_eq_pm_one_of_self_dual_simple`
(`FrobeniusSchurTraceIdentity.lean`). The remaining `sorry` in the axiom trace of this
theorem comes only from `isRealType_of_frobeniusSchurIndicator_eq_one`'s dependency on
`exists_nonzero_invariant_symmetric_of_FS_eq_one` (tracked as #5214). -/
theorem Etingof.isRealType_of_A5_even_standard
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (alternatingGroup (Fin 5)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (alternatingGroup (Fin 5))) ρ.asModule)
    (hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g)
    (heven : Even (Module.finrank ℂ V)) :
    Etingof.IsRealType ρ := by
  classical
  -- It suffices to show the Frobenius-Schur indicator of `ρ` is `1`.
  apply Etingof.isRealType_of_frobeniusSchurIndicator_eq_one ρ hρ
  -- Order facts about `A₅`.
  have hcard60 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by native_decide
  haveI hNZ : NeZero (Nat.card (alternatingGroup (Fin 5)) : ℂ) := by
    refine ⟨?_⟩; rw [Nat.card_eq_fintype_card, hcard60]; norm_num
  haveI hInv : Invertible (Fintype.card (alternatingGroup (Fin 5)) : ℂ) :=
    invertibleOfNonzero (by rw [hcard60]; norm_num)
  -- The Wedderburn-Artin family of irreducibles of `ℂ[A₅]`.
  let D : IrrepDecomp ℂ (alternatingGroup (Fin 5)) := IrrepDecomp.mk'
  let W : Fin D.n → FDRep ℂ (alternatingGroup (Fin 5)) := D.columnFDRep
  have hWs : ∀ i, Simple (W i) := D.columnFDRep_simple
  have hWi : ∀ i j, Nonempty ((W i) ≅ (W j)) → i = j := D.columnFDRep_injective
  -- (1) There are exactly five irreducibles.
  have h5 : Fintype.card (Fin D.n) = 5 := by
    rw [Fintype.card_fin, D.n_eq_card_conjClasses']
    native_decide
  -- (2) Sum of squared dimensions equals `|A₅| = 60`.
  have hsqN : ∑ i, (Module.finrank ℂ (W i)) ^ 2 = 60 := by
    rw [D.sum_finrank_sq_eq_card W hWs hWi, hcard60]
  -- (3) Frobenius-Schur involution count: `16 = ∑ FS(Wᵢ)·dim Wᵢ`.
  have hcountC : ((Finset.univ.filter
        (fun g : alternatingGroup (Fin 5) => g * g = 1)).card : ℂ)
      = ∑ i, Etingof.frobeniusSchurIndicator (W i).ρ * (Module.finrank ℂ (W i) : ℂ) :=
    Etingof.frobeniusSchur_involution_count D W hWs hWi
  have hinv16 : (Finset.univ.filter
      (fun g : alternatingGroup (Fin 5) => g * g = 1)).card = 16 := by native_decide
  -- (4) `A₅` is ambivalent, so every `Wᵢ` has a self-dual character.
  have hsdW : ∀ i, ∀ g, Representation.character (W i).ρ g⁻¹
      = Representation.character (W i).ρ g := by
    intro i g
    obtain ⟨c, hc⟩ := isConj_iff.mp (Etingof.alternatingGroup_ambivalent g)
    rw [← hc]; exact Representation.char_conj (W i).ρ g c
  -- Hence each `FS(Wᵢ) ∈ {±1}` (isolated gap).
  have hFSmem : ∀ i, Etingof.frobeniusSchurIndicator (W i).ρ = 1
      ∨ Etingof.frobeniusSchurIndicator (W i).ρ = -1 :=
    fun i => frobeniusSchurIndicator_pm_one_of_simple_selfDual (W i)
      (D.isSimpleModule_columnRep_asModule i) (hsdW i)
  -- Package dimensions and indicators as integers for the endgame.
  set dd : Fin D.n → ℤ := fun i => (Module.finrank ℂ (W i) : ℤ) with hdd
  set ee : Fin D.n → ℤ :=
    fun i => if Etingof.frobeniusSchurIndicator (W i).ρ = 1 then (1 : ℤ) else -1 with hee
  have hεval : ∀ i, Etingof.frobeniusSchurIndicator (W i).ρ = (ee i : ℂ) := by
    intro i
    rcases hFSmem i with h1 | h1
    · rw [hee]; simp only [if_pos h1]; rw [h1]; norm_num
    · have hne : Etingof.frobeniusSchurIndicator (W i).ρ ≠ 1 := by rw [h1]; norm_num
      rw [hee]; simp only [if_neg hne]; rw [h1]; norm_num
  have hd : ∀ i, 1 ≤ dd i := by
    intro i
    have hfpos : 0 < Module.finrank ℂ (W i) := by
      rw [D.finrank_columnFDRep i]; exact Nat.pos_of_ne_zero (D.d_pos i).out
    simp only [hdd]; exact_mod_cast hfpos
  have hε : ∀ i, ee i = 1 ∨ ee i = -1 := by
    intro i
    by_cases h : Etingof.frobeniusSchurIndicator (W i).ρ = 1
    · left; rw [hee]; simp only [if_pos h]
    · right; rw [hee]; simp only [if_neg h]
  have hsq : ∑ i, dd i ^ 2 = 60 := by
    rw [hdd]
    calc ∑ i, ((Module.finrank ℂ (W i) : ℤ)) ^ 2
        = ((∑ i, (Module.finrank ℂ (W i)) ^ 2 : ℕ) : ℤ) := by push_cast; ring
      _ = ((60 : ℕ) : ℤ) := by rw [hsqN]
      _ = 60 := by norm_num
  have hcount : ∑ i, ee i * dd i = 16 := by
    have hC : ((16 : ℕ) : ℂ)
        = ∑ i, Etingof.frobeniusSchurIndicator (W i).ρ * (Module.finrank ℂ (W i) : ℂ) := by
      rw [← hinv16]; exact_mod_cast hcountC
    have hC3 : ((∑ i, ee i * dd i : ℤ) : ℂ) = ((16 : ℤ) : ℂ) := by
      rw [show ((16 : ℤ) : ℂ) = ((16 : ℕ) : ℂ) from by norm_num, hC]
      push_cast [hdd]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hεval i]
    exact_mod_cast hC3
  -- The endgame forces every indicator to be `+1`.
  have hall : ∀ i, ee i = 1 :=
    Etingof.frobeniusSchur_all_pos_general h5 dd ee hd hε hsq hcount
  -- The abstract `ρ` is isomorphic to some `Wᵢ₀`, so `FS(ρ) = FS(Wᵢ₀) = 1`.
  haveI := hρ
  haveI hsimp : Simple (FDRep.of ρ) := simple_FDRep_of_isSimpleModule ρ
  obtain ⟨i₀, ⟨iso⟩⟩ := D.columnFDRep_surjective (FDRep.of ρ) hsimp
  have hchar : ∀ g, Representation.character ρ g = Representation.character (W i₀).ρ g :=
    fun g => congrFun (FDRep.char_iso iso) g
  rw [Etingof.frobeniusSchurIndicator_eq_of_character_eq ρ (W i₀).ρ hchar, hεval i₀, hall i₀]
  norm_num

end A5EvenAssembly

/-- All irreducible representations of `A₅` are of real type. (Etingof Example 5.1.3)

`A₅` is ambivalent (`alternatingGroup_ambivalent`), so every character is self-dual
(`χ(g⁻¹) = χ(g)`). The odd-dimensional irreducibles `ℂ, ℂ³₊, ℂ³₋, ℂ⁵` are then of
real type by the self-dual dichotomy plus L3 (quaternionic ⟹ even-dimensional):
`isRealType_of_self_dual_of_odd_finrank`. The single even-dimensional irreducible —
the 4-dimensional standard representation — is rational, handled by
`isRealType_of_A5_even_standard`. -/
theorem Etingof.Example5_1_3_A5
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (alternatingGroup (Fin 5)) V)
    (hρ : IsSimpleModule (MonoidAlgebra ℂ (alternatingGroup (Fin 5))) ρ.asModule) :
    Etingof.IsRealType ρ := by
  -- Ambivalence ⟹ self-dual character.
  have hsd : ∀ g, Representation.character ρ g⁻¹ = Representation.character ρ g := by
    intro g
    obtain ⟨c, hc⟩ := isConj_iff.mp (Etingof.alternatingGroup_ambivalent g)
    rw [← hc]; exact Representation.char_conj ρ g c
  rcases Nat.even_or_odd (Module.finrank ℂ V) with heven | hodd
  · exact Etingof.isRealType_of_A5_even_standard ρ hρ hsd heven
  · exact Etingof.isRealType_of_self_dual_of_odd_finrank ρ hρ hsd hodd

namespace Etingof.Q8

open Matrix Complex QuaternionGroup

/-- The order-4 generator `a ↦ A`, with `A = diag(√-1, -√-1)`. -/
noncomputable def A : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

/-- The second generator `x ↦ X`, with `X = [[0,1],[-1,0]]`. -/
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

@[simp] lemma det_A : A.det = 1 := by
  simp [A, Matrix.det_fin_two_of, Complex.I_mul_I]

@[simp] lemma det_X : X.det = 1 := by
  simp [X, Matrix.det_fin_two_of]

lemma A_sq : A ^ 2 = -1 := by
  rw [pow_two]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Matrix.one_fin_two]

lemma A_pow_four : A ^ 4 = 1 := by
  have h : A ^ 4 = (A ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h, A_sq, neg_one_sq]

/-- `X² = A² = -1`. -/
lemma X_mul_X : X * X = A ^ 2 := by
  rw [A_sq]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]

/-- The relation `A·X = X·A³` (equivalently `X⁻¹AX = A⁻¹`). -/
lemma A_mul_X : A * X = X * A ^ 3 := by
  have h3 : A ^ 3 = !![(-Complex.I), 0; 0, Complex.I] := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, A_sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  rw [h3]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [A, X, Matrix.mul_apply, Fin.sum_univ_two]

/-- `A^a` depends only on `a` mod 4. -/
lemma A_pow_congr {a b : ℕ} (h : (a : ZMod 4) = (b : ZMod 4)) : A ^ a = A ^ b := by
  have e : a % 4 = b % 4 := (ZMod.natCast_eq_natCast_iff a b 4).mp h
  conv_lhs => rw [← Nat.div_add_mod a 4]
  conv_rhs => rw [← Nat.div_add_mod b 4]
  rw [pow_add, pow_add, pow_mul, pow_mul, A_pow_four, one_pow, one_pow, e]

/-- Move a power of `A` across `X`: `A^m · X = X · A^{3m}`. -/
lemma A_pow_mul_X : ∀ m : ℕ, A ^ m * X = X * A ^ (3 * m)
  | 0 => by simp
  | (m + 1) => by
    rw [pow_succ, mul_assoc, A_mul_X, ← mul_assoc, A_pow_mul_X m, mul_assoc, ← pow_add,
      show 3 * m + 3 = 3 * (m + 1) from by ring]

/-- Conjugating `A^m` by `X`: `X · A^m · X = A^{2 + 3m}`. -/
lemma X_mul_A_pow_mul_X (m : ℕ) : X * A ^ m * X = A ^ (2 + 3 * m) := by
  rw [mul_assoc, A_pow_mul_X, ← mul_assoc, X_mul_X, ← pow_add]

/-- The underlying matrix-valued function of the representation. -/
noncomputable def Mfun : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | .a k => A ^ k.val
  | .xa k => X * A ^ k.val

/-- The representation `Q₈ → GL₂(ℂ)` as a monoid homomorphism into matrices. -/
noncomputable def Mhom : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := Mfun
  map_one' := by
    show Mfun 1 = 1
    rw [QuaternionGroup.one_def]; simp [Mfun]
  map_mul' := by
    rintro (i | i) (j | j)
    · show Mfun (a i * a j) = Mfun (a i) * Mfun (a j)
      rw [QuaternionGroup.a_mul_a]
      simp only [Mfun]
      rw [← pow_add]
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · show Mfun (a i * xa j) = Mfun (a i) * Mfun (xa j)
      rw [QuaternionGroup.a_mul_xa]
      simp only [Mfun]
      rw [← mul_assoc, A_pow_mul_X, mul_assoc, ← pow_add]
      congr 1
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)
    · show Mfun (xa i * a j) = Mfun (xa i) * Mfun (a j)
      rw [QuaternionGroup.xa_mul_a]
      simp only [Mfun]
      rw [mul_assoc, ← pow_add]
      congr 1
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)
    · show Mfun (xa i * xa j) = Mfun (xa i) * Mfun (xa j)
      rw [QuaternionGroup.xa_mul_xa]
      simp only [Mfun]
      rw [← mul_assoc (X * A ^ i.val) X (A ^ j.val), X_mul_A_pow_mul_X, ← pow_add]
      exact A_pow_congr (by push_cast [ZMod.natCast_val, ZMod.cast_id]; revert i j; decide)

/-- The 2-dimensional representation of `Q₈` on `Fin 2 → ℂ`. -/
noncomputable def rho : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ) where
  toFun g := Matrix.toLinAlgEquiv' (Mhom g)
  map_one' := by simp
  map_mul' g h := by simp [map_mul]

lemma rho_apply (g : QuaternionGroup 2) (v : Fin 2 → ℂ) :
    rho g v = (Mhom g).mulVec v := by
  simp [rho, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

end Etingof.Q8

/-- The 2-dimensional irreducible representation of `Q₈ = QuaternionGroup 2` is of
quaternionic type: there is a simple `ℂ[Q₈]`-module structure on `Fin 2 → ℂ`
admitting a nondegenerate `Q₈`-invariant skew-symmetric bilinear form.
(Etingof Example 5.1.3) -/
theorem Etingof.Example5_1_3_Q8 :
    ∃ ρ : Representation ℂ (QuaternionGroup 2) (Fin 2 → ℂ),
      IsSimpleModule (MonoidAlgebra ℂ (QuaternionGroup 2)) ρ.asModule ∧
      Etingof.IsQuaternionicType ρ := by
  -- The 2-dimensional irrep uses the Pauli-type matrices `ρ(i) = [[0,1],[-1,0]]`,
  -- `ρ(j) = [[√-1,0],[0,-√-1]]`, `ρ(k) = [[0,-√-1],[-√-1,0]]`. Its FS indicator is
  -- `-1`, witnessed by the invariant skew form `[[0,1],[-1,0]]`.
  refine ⟨Etingof.Q8.rho, ?_, ?_⟩
  · -- Simplicity: the only `ρ`-invariant subspaces are `⊥` and `⊤`, since the diagonal
    -- generator `A` and the swap `X` share no common eigenline.
    -- Evaluate the two generators on an arbitrary vector.
    have hAv : ∀ v : Fin 2 → ℂ, Etingof.Q8.rho (QuaternionGroup.a 1) v
        = ![Complex.I * v 0, -Complex.I * v 1] := by
      intro v
      rw [Etingof.Q8.rho_apply]
      show (Etingof.Q8.Mfun (QuaternionGroup.a 1)).mulVec v = _
      simp only [Etingof.Q8.Mfun, show (1 : ZMod (2 * 2)).val = 1 from by decide, pow_one]
      funext i; fin_cases i <;>
        simp [Etingof.Q8.A, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hXv : ∀ v : Fin 2 → ℂ, Etingof.Q8.rho (QuaternionGroup.xa 0) v
        = ![v 1, -v 0] := by
      intro v
      rw [Etingof.Q8.rho_apply]
      show (Etingof.Q8.Mfun (QuaternionGroup.xa 0)).mulVec v = _
      simp only [Etingof.Q8.Mfun, show (0 : ZMod (2 * 2)).val = 0 from by decide, pow_zero,
        mul_one]
      funext i; fin_cases i <;>
        simp [Etingof.Q8.X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    -- Reduce `IsSimpleModule` to `IsSimpleOrder` of the invariant-submodule lattice.
    suffices hSO : IsSimpleOrder (Etingof.Q8.rho.invtSubmodule) by
      haveI := (Representation.mapSubmodule Etingof.Q8.rho).isSimpleOrder_iff.mp hSO
      exact ⟨⟩
    refine { eq_bot_or_eq_top := fun a => ?_ }
    have hinv : ∀ g, ∀ x ∈ (a : Submodule ℂ (Fin 2 → ℂ)),
        Etingof.Q8.rho g x ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
      intro g x hx
      have hmem : (a : Submodule ℂ (Fin 2 → ℂ)) ∈ Module.End.invtSubmodule (Etingof.Q8.rho g) :=
        (Representation.mem_invtSubmodule (ρ := Etingof.Q8.rho)).mp a.2 g
      exact ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
        (f := Etingof.Q8.rho g)).mp hmem) x hx
    rcases eq_or_ne (a : Submodule ℂ (Fin 2 → ℂ)) ⊥ with hbot | hbot
    · exact Or.inl (Subtype.ext (by rw [Representation.invtSubmodule.coe_bot]; exact hbot))
    · refine Or.inr (Subtype.ext ?_)
      rw [Representation.invtSubmodule.coe_top]
      -- Extract a nonzero vector and show both basis vectors lie in `a`.
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
      have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) ∧
          (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
        by_cases hv1 : v 1 = 0
        · -- `v = (v₀, 0)` with `v₀ ≠ 0`: scale to `e₀`, then apply `X` for `e₁`.
          have hv0' : v 0 ≠ 0 := by
            intro h; apply hv0; funext i; fin_cases i
            · simpa using h
            · simpa using hv1
          have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have : (v 0)⁻¹ • v = (![1, 0] : Fin 2 → ℂ) := by
              funext i; fin_cases i
              · simpa using inv_mul_cancel₀ hv0'
              · simpa [hv1]
            rw [← this]; exact (a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hv
          have he1 : (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have hx := hinv (QuaternionGroup.xa 0) _ he0
            rw [hXv] at hx
            have : (![(![1, 0] : Fin 2 → ℂ) 1, -(![1, 0] : Fin 2 → ℂ) 0] : Fin 2 → ℂ)
                = -(![0, 1] : Fin 2 → ℂ) := by funext i; fin_cases i <;> simp
            rw [this] at hx
            simpa using (a : Submodule ℂ (Fin 2 → ℂ)).neg_mem hx
          exact ⟨he0, he1⟩
        · -- `v₁ ≠ 0`: form `I•v - A·v = (0, 2I v₁)`, scale to `e₁`, then apply `X` for `e₀`.
          have hmem : (Complex.I • v - Etingof.Q8.rho (QuaternionGroup.a 1) v)
              ∈ (a : Submodule ℂ (Fin 2 → ℂ)) :=
            (a : Submodule ℂ (Fin 2 → ℂ)).sub_mem
              ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hv) (hinv _ _ hv)
          have heq : Complex.I • v - Etingof.Q8.rho (QuaternionGroup.a 1) v
              = ![0, 2 * Complex.I * v 1] := by
            rw [hAv]; funext i; fin_cases i <;> simp [Pi.smul_apply] <;> ring
          rw [heq] at hmem
          have hc : (2 : ℂ) * Complex.I * v 1 ≠ 0 := by
            simp [hv1, Complex.I_ne_zero]
          have he1 : (![0, 1] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have : (2 * Complex.I * v 1)⁻¹ • (![0, 2 * Complex.I * v 1] : Fin 2 → ℂ)
                = (![0, 1] : Fin 2 → ℂ) := by
              funext i; fin_cases i
              · simp
              · simpa using inv_mul_cancel₀ hc
            rw [← this]; exact (a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ hmem
          have he0 : (![1, 0] : Fin 2 → ℂ) ∈ (a : Submodule ℂ (Fin 2 → ℂ)) := by
            have hx := hinv (QuaternionGroup.xa 0) _ he1
            rw [hXv] at hx
            have : (![(![0, 1] : Fin 2 → ℂ) 1, -(![0, 1] : Fin 2 → ℂ) 0] : Fin 2 → ℂ)
                = (![1, 0] : Fin 2 → ℂ) := by funext i; fin_cases i <;> simp
            rwa [this] at hx
          exact ⟨he0, he1⟩
      -- Two basis vectors span everything.
      rw [eq_top_iff]
      intro w _
      have hw : w = w 0 • (![1, 0] : Fin 2 → ℂ) + w 1 • ![0, 1] := by
        funext i; fin_cases i <;> simp
      rw [hw]
      exact (a : Submodule ℂ (Fin 2 → ℂ)).add_mem
        ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ he0.1)
        ((a : Submodule ℂ (Fin 2 → ℂ)).smul_mem _ he0.2)
  · -- Quaternionic type: the wedge form `B v w = v₀w₁ - v₁w₀` is skew, nondegenerate, and
    -- `Q₈`-invariant (every matrix lies in `SL₂`, so it preserves the determinant form).
    set B : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) →ₗ[ℂ] ℂ :=
      LinearMap.mk₂ ℂ (fun v w => v 0 * w 1 - v 1 * w 0)
        (fun v v' w => by simp only [Pi.add_apply]; ring)
        (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
        (fun v w w' => by simp only [Pi.add_apply]; ring)
        (fun c v w => by simp only [Pi.smul_apply, smul_eq_mul]; ring) with hBdef
    have hB : ∀ v w : Fin 2 → ℂ, B v w = v 0 * w 1 - v 1 * w 0 := fun v w => rfl
    refine ⟨B, ?_, ?_, ?_⟩
    · -- skew-symmetric
      intro v w; rw [hB, hB]; ring
    · -- nondegenerate
      intro v hv
      have h0 : v 0 = 0 := by have := hv ![0, 1]; rw [hB] at this; simpa using this
      have h1 : v 1 = 0 := by have := hv ![1, 0]; rw [hB] at this; simpa using this
      funext i; fin_cases i
      · simpa using h0
      · simpa using h1
    · -- Q₈-invariant
      intro g v w
      have key : ∀ (N : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 2 → ℂ),
          B (N.mulVec x) (N.mulVec y) = N.det * B x y := by
        intro N x y
        rw [hB, hB]
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
        ring
      rw [Etingof.Q8.rho_apply, Etingof.Q8.rho_apply, key]
      have hdet : (Etingof.Q8.Mhom g).det = 1 := by
        rcases g with k | k
        · show (Etingof.Q8.Mfun (QuaternionGroup.a k)).det = 1
          simp [Etingof.Q8.Mfun, Matrix.det_pow]
        · show (Etingof.Q8.Mfun (QuaternionGroup.xa k)).det = 1
          simp [Etingof.Q8.Mfun, Matrix.det_mul, Matrix.det_pow]
      rw [hdet, one_mul]
