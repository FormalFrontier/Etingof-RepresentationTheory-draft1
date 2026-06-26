import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Theorem 3.3.1: Irreducible Representations of Direct Sums of Matrix Algebras

Let A = ⊕ᵢ Mat_{dᵢ}(k). Then the irreducible representations of A are
V₁ = k^{d₁}, …, Vᵣ = k^{dᵣ}, and any finite dimensional representation of A is a direct
sum of copies of V₁, …, Vᵣ.

The core of this result is that each matrix algebra Mat_d(k) has a unique
irreducible representation, namely the standard representation k^d. The full
theorem follows because the irreducible representations of a direct sum of
algebras are exactly the irreducible representations of the individual factors.
-/

open Matrix.Module Finset

private theorem matrix_single_smul_vec {k : Type*} [Field k] {d : ℕ}
    (j i : Fin d) (c : k) (v : Fin d → k) :
    (Matrix.single j i c • v) = fun l => if l = j then c * v i else 0 := by
  ext l
  simp only [smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hjl : j = l
  · subst hjl
    simp only [true_and, ite_mul, zero_mul]
    rw [sum_ite_eq univ i]
    simp
  · simp only [show ¬(j = l) from hjl, false_and, ite_false, zero_mul, sum_const_zero,
      show ¬(l = j) from Ne.symm hjl, ite_false]

/-- The standard representation `Fin d → k` is a simple module over `Matrix (Fin d) (Fin d) k`.
Any nonzero vector generates the whole module under the matrix action. -/
private theorem isSimpleModule_matrix_vecModule (k : Type*) [Field k]
    (d : ℕ) [NeZero d] :
    IsSimpleModule (Matrix (Fin d) (Fin d) k) (Fin d → k) where
  eq_bot_or_eq_top s := by
    by_cases hs : s = ⊥
    · exact Or.inl hs
    · right
      obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
      have ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h; push_neg at h
        exact hne (funext fun j => by simpa using h j)
      have basis_mem : ∀ j, Pi.single j (1 : k) ∈ s := by
        intro j
        have h1 := s.smul_mem (Matrix.single j i (v i)⁻¹) hv
        rw [matrix_single_smul_vec] at h1
        convert h1 using 1
        ext l
        simp [Pi.single_apply, inv_mul_cancel₀ hi]
      rw [eq_top_iff]
      intro w _
      -- Write w as a sum of matrix-scaled basis vectors
      suffices w = ∑ j ∈ univ, Matrix.single j j (w j) •
          (Pi.single j (1 : k) : Fin d → k) by
        rw [this]
        exact sum_mem fun j _ => s.smul_mem _ (basis_mem j)
      ext l
      simp only [sum_apply, matrix_single_smul_vec, Pi.single_apply, ite_true, mul_one]
      rw [sum_ite_eq univ l]; simp

/-- The standard representation `k^d` is the unique irreducible representation of `Mat_d(k)`:
any finite-dimensional simple `Mat_d(k)`-module is isomorphic to `Fin d → k`. This is the
single-factor core of Etingof Theorem 3.3.1. -/
private theorem matrix_simpleModule_iso_std (k : Type*) [Field k]
    (d : ℕ) [NeZero d] (V : Type*)
    [AddCommGroup V] [Module k V] [Module (Matrix (Fin d) (Fin d) k) V]
    [IsScalarTower k (Matrix (Fin d) (Fin d) k) V]
    [FiniteDimensional k V] [IsSimpleModule (Matrix (Fin d) (Fin d) k) V] :
    Nonempty (V ≃ₗ[Matrix (Fin d) (Fin d) k] (Fin d → k)) := by
  letI := isSimpleModule_matrix_vecModule k d
  letI : IsSimpleRing (Matrix (Fin d) (Fin d) k) := IsSimpleRing.matrix ..
  letI : IsArtinianRing (Matrix (Fin d) (Fin d) k) := inferInstance
  -- Both V and (Fin d → k) are simple modules over a simple Artinian ring.
  -- By the Wedderburn-Artin theorem, a simple Artinian ring has a unique
  -- simple module up to isomorphism. We show this via isotypicity:
  -- both embed into R as simple left ideals, and all such ideals are isomorphic.
  have ⟨I, ⟨eI⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin d) (Fin d) k) V
  have ⟨I', ⟨eI'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin d) (Fin d) k) (Fin d → k)
  haveI : IsSimpleModule _ I := IsSimpleModule.congr eI.symm
  haveI : IsSimpleModule _ I' := IsSimpleModule.congr eI'.symm
  have hiso := IsSimpleRing.isIsotypic (Matrix (Fin d) (Fin d) k) (Matrix (Fin d) (Fin d) k)
  have ⟨eII'⟩ := hiso I I'
  exact ⟨eI.trans (eII'.symm.trans eI'.symm)⟩

/-! ## The full direct-sum-of-matrix-algebras setting

We now treat `A = ⊕ᵢ Mat_{dᵢ}(k)`, modeled as the finite product ring
`∀ i, Matrix (Fin (dᵢ)) (Fin (dᵢ)) k`. Each standard representation `Vⱼ = k^{dⱼ}` becomes an
`A`-module via the `j`-th projection `A → Mat_{dⱼ}(k)`. -/

/-- The product ring `A = ⊕ᵢ Mat_{dᵢ}(k)`. -/
abbrev MatProd (k : Type*) [Field k] {r : ℕ} (d : Fin r → ℕ) : Type _ :=
  ∀ i, Matrix (Fin (d i)) (Fin (d i)) k

section Product

variable {k : Type*} [Field k] {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]

/-- The standard representation `Vⱼ = k^{dⱼ}` as a module over `A = ⊕ᵢ Mat_{dᵢ}(k)`, with `A`
acting through the `j`-th projection. -/
local instance vModuleProd (j : Fin r) : Module (MatProd k d) (Fin (d j) → k) :=
  Module.compHom _ (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j)

/-- Unfold the `A`-action on the standard representation `Vⱼ`: `a` acts as its `j`-th
component matrix. -/
theorem vModuleProd_smul (j : Fin r) (a : MatProd k d) (v : Fin (d j) → k) :
    a • v = a j • v := rfl

instance (j : Fin r) : IsScalarTower k (MatProd k d) (Fin (d j) → k) where
  smul_assoc c a v := by
    rw [vModuleProd_smul]
    show (c • a) j • v = c • (a j • v)
    rw [Pi.smul_apply, smul_assoc]

/-- **Part 1.** Each standard representation `Vⱼ = k^{dⱼ}` is a simple `A`-module. -/
theorem isSimpleModule_vModuleProd (j : Fin r) :
    IsSimpleModule (MatProd k d) (Fin (d j) → k) := by
  haveI : IsSimpleModule (Matrix (Fin (d j)) (Fin (d j)) k) (Fin (d j) → k) :=
    isSimpleModule_matrix_vecModule k (d j)
  haveI : RingHomSurjective
      (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j) :=
    ⟨Function.surjective_eval j⟩
  let l : (Fin (d j) → k) →ₛₗ[Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j]
      (Fin (d j) → k) :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ => rfl }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance

/-- **Part 3.** Every `A`-module is semisimple, i.e. an (internal) direct sum of simple
submodules. Combined with Part 2 below, every finite-dimensional representation of `A` is a
direct sum of copies of the `Vⱼ`. -/
theorem isSemisimpleModule_of_matrixProd (X : Type*) [AddCommGroup X]
    [Module (MatProd k d) X] : IsSemisimpleModule (MatProd k d) X :=
  inferInstance

/-- **Part 2.** Every finite-dimensional simple `A`-module is isomorphic to one of the
standard representations `Vⱼ = k^{dⱼ}`. -/
theorem exists_iso_vModuleProd (W : Type*) [AddCommGroup W] [Module (MatProd k d) W]
    [Module k W] [IsScalarTower k (MatProd k d) W] [FiniteDimensional k W]
    [IsSimpleModule (MatProd k d) W] :
    ∃ j, Nonempty (W ≃ₗ[MatProd k d] (Fin (d j) → k)) := by
  classical
  -- The central idempotents `eᵢ = Pi.single i 1` of `A`.
  have e_mul_self : ∀ i : Fin r,
      (Pi.single i 1 : MatProd k d) * Pi.single i 1 = Pi.single i 1 := fun i => by
    rw [← Pi.single_mul, mul_one]
  have e_left : ∀ (i : Fin r) (a : MatProd k d),
      (Pi.single i 1 : MatProd k d) * a = Pi.single i (a i) := fun i a => by
    rw [← Pi.single_mul_left, one_mul]
  have e_right : ∀ (i : Fin r) (a : MatProd k d),
      a * (Pi.single i 1 : MatProd k d) = Pi.single i (a i) := fun i a => by
    rw [← Pi.single_mul_right, mul_one]
  -- Since `∑ᵢ eᵢ = 1` and `W ≠ 0`, some `eᵢ` does not kill a chosen nonzero vector.
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MatProd k d) W
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hsum : ∑ i, (Pi.single i 1 : MatProd k d) • w₀ = w₀ := by
    rw [← Finset.sum_smul, show (∑ i, (Pi.single i 1 : MatProd k d)) = 1 by
      simpa using Finset.univ_sum_single (1 : MatProd k d), one_smul]
  obtain ⟨i, hi⟩ : ∃ i, (Pi.single i 1 : MatProd k d) • w₀ ≠ 0 := by
    by_contra h; push_neg at h
    exact hw₀ (by rw [← hsum, Finset.sum_eq_zero (fun i _ => h i)])
  -- `μ : w ↦ eᵢ • w` is an `A`-linear idempotent (as `eᵢ` is central).
  let μ : W →ₗ[MatProd k d] W :=
    { toFun := fun w => (Pi.single i 1 : MatProd k d) • w
      map_add' := fun w w' => smul_add _ _ _
      map_smul' := fun a w => by
        show (Pi.single i 1 : MatProd k d) • (a • w) = a • ((Pi.single i 1 : MatProd k d) • w)
        rw [smul_smul, smul_smul, e_left, e_right] }
  have hμμ : ∀ w, μ (μ w) = μ w := fun w => by
    show (Pi.single i 1 : MatProd k d) • ((Pi.single i 1 : MatProd k d) • w)
        = (Pi.single i 1 : MatProd k d) • w
    rw [smul_smul, e_mul_self]
  -- Simplicity forces `range μ = ⊤`, so the idempotent `μ` is the identity: `eᵢ` acts as `1`.
  have hrange : LinearMap.range μ = ⊤ := by
    refine (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left fun h => hi ?_
    have hmem : μ w₀ ∈ LinearMap.range μ := LinearMap.mem_range_self _ _
    rw [h, Submodule.mem_bot] at hmem
    exact hmem
  have hid : ∀ w : W, (Pi.single i 1 : MatProd k d) • w = w := fun w => by
    obtain ⟨w', hw'⟩ := (by rw [hrange]; exact Submodule.mem_top : w ∈ LinearMap.range μ)
    have h := hμμ w'
    rw [hw'] at h
    exact h
  -- The `A`-action on `W` factors through the `i`-th projection.
  have key : ∀ (a : MatProd k d) (w : W),
      a • w = (Pi.single i (a i) : MatProd k d) • w := fun a w => by
    conv_lhs => rw [← hid w, smul_smul, e_right]
  -- Endow `W` with the `Mat_{dᵢ}(k)`-action `b • w = Pi.single i b • w`.
  letI : Module (Matrix (Fin (d i)) (Fin (d i)) k) W :=
    { smul := fun b w => (Pi.single i b : MatProd k d) • w
      one_smul := fun w => hid w
      mul_smul := fun b b' w => by
        show (Pi.single i (b * b') : MatProd k d) • w
            = (Pi.single i b : MatProd k d) • ((Pi.single i b' : MatProd k d) • w)
        rw [Pi.single_mul, smul_smul]
      smul_zero := fun b => smul_zero _
      smul_add := fun b w w' => smul_add _ _ _
      add_smul := fun b b' w => by
        show (Pi.single i (b + b') : MatProd k d) • w
            = (Pi.single i b : MatProd k d) • w + (Pi.single i b' : MatProd k d) • w
        rw [Pi.single_add, add_smul]
      zero_smul := fun w => by
        show (Pi.single i (0 : Matrix (Fin (d i)) (Fin (d i)) k) : MatProd k d) • w = 0
        rw [Pi.single_zero, zero_smul] }
  haveI : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) k) W :=
    { smul_assoc := fun c b w => by
        show (Pi.single i (c • b) : MatProd k d) • w = c • ((Pi.single i b : MatProd k d) • w)
        rw [Pi.single_smul, smul_assoc] }
  haveI : IsSimpleModule (Matrix (Fin (d i)) (Fin (d i)) k) W := by
    haveI : RingHomSurjective
        (Pi.evalRingHom (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i) :=
      ⟨Function.surjective_eval i⟩
    let l : W →ₛₗ[Pi.evalRingHom (fun j => Matrix (Fin (d j)) (Fin (d j)) k) i] W :=
      { AddMonoidHom.id W with map_smul' := fun a w => key a w }
    exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).mp inferInstance
  -- Apply the single-factor classification and upgrade the iso to `A`-linearity.
  obtain ⟨eW⟩ := matrix_simpleModule_iso_std k (d i) W
  exact ⟨i, ⟨{ eW.toAddEquiv with
    map_smul' := fun a w => by
      show eW (a • w) = a • eW w
      rw [key a w, vModuleProd_smul]
      exact eW.map_smul (a i) w }⟩⟩

/-- **Theorem 3.3.1.** Let `A = ⊕ᵢ Mat_{dᵢ}(k)`. Then the irreducible representations of `A`
are `V₁ = k^{d₁}, …, Vᵣ = k^{dᵣ}`, and any finite-dimensional representation of `A` is a
direct sum of copies of the `Vⱼ`. Concretely:
* (1) each `Vⱼ` is a simple `A`-module (`isSimpleModule_vModuleProd`);
* (2) every finite-dimensional simple `A`-module is isomorphic to some `Vⱼ`
  (`exists_iso_vModuleProd`); and
* (3) every `A`-module is a direct sum of simple submodules (`isSemisimpleModule_of_matrixProd`),
  which by (1)–(2) are copies of the `Vⱼ`. -/
theorem Etingof.irreducible_reps_of_matrix_algebra :
    (∀ j, IsSimpleModule (MatProd k d) (Fin (d j) → k)) ∧
    (∀ (W : Type*) [AddCommGroup W] [Module (MatProd k d) W] [Module k W]
        [IsScalarTower k (MatProd k d) W] [FiniteDimensional k W] [IsSimpleModule (MatProd k d) W],
        ∃ j, Nonempty (W ≃ₗ[MatProd k d] (Fin (d j) → k))) ∧
    (∀ (X : Type*) [AddCommGroup X] [Module (MatProd k d) X], IsSemisimpleModule (MatProd k d) X) :=
  ⟨isSimpleModule_vModuleProd, fun W => exists_iso_vModuleProd W,
    isSemisimpleModule_of_matrixProd⟩

end Product
