import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace
import EtingofRepresentationTheory.Chapter3.Proposition3_1_4

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

open scoped DirectSum

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
        by_contra h; push Not at h
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
abbrev MatProd (k : Type*) {r : ℕ} (d : Fin r → ℕ) : Type _ :=
  ∀ i, Matrix (Fin (d i)) (Fin (d i)) k

section Product

variable {k : Type*} [Field k] {r : ℕ} {d : Fin r → ℕ} [∀ i, NeZero (d i)]

/-- The standard representation `Vⱼ = k^{dⱼ}` as a module over `A = ⊕ᵢ Mat_{dᵢ}(k)`, with `A`
acting through the `j`-th projection. -/
local instance vModuleProd (j : Fin r) : Module (MatProd k d) (Fin (d j) → k) :=
  Module.compHom _ (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j)

omit [∀ i, NeZero (d i)] in
/-- Unfold the `A`-action on the standard representation `Vⱼ`: `a` acts as its `j`-th
component matrix. -/
theorem vModuleProd_smul (j : Fin r) (a : MatProd k d) (v : Fin (d j) → k) :
    a • v = a j • v := rfl

/-- Scalar multiplication by `k` associates with the product-matrix action on `Vⱼ`. -/
instance (j : Fin r) : IsScalarTower k (MatProd k d) (Fin (d j) → k) where
  smul_assoc c a v := by
    rw [vModuleProd_smul]
    change (c • a) j • v = c • (a j • v)
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

omit [∀ i, NeZero (d i)] in
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
    by_contra h; push Not at h
    exact hw₀ (by rw [← hsum, Finset.sum_eq_zero (fun i _ => h i)])
  -- `μ : w ↦ eᵢ • w` is an `A`-linear idempotent (as `eᵢ` is central).
  let μ : W →ₗ[MatProd k d] W :=
    { toFun := fun w => (Pi.single i 1 : MatProd k d) • w
      map_add' := fun w w' => smul_add _ _ _
      map_smul' := fun a w => by
        change (Pi.single i 1 : MatProd k d) • (a • w) =
          a • ((Pi.single i 1 : MatProd k d) • w)
        rw [smul_smul, smul_smul, e_left, e_right] }
  have hμμ : ∀ w, μ (μ w) = μ w := fun w => by
    change (Pi.single i 1 : MatProd k d) • ((Pi.single i 1 : MatProd k d) • w)
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
        change (Pi.single i (b * b') : MatProd k d) • w
            = (Pi.single i b : MatProd k d) • ((Pi.single i b' : MatProd k d) • w)
        rw [Pi.single_mul, smul_smul]
      smul_zero := fun b => smul_zero _
      smul_add := fun b w w' => smul_add _ _ _
      add_smul := fun b b' w => by
        change (Pi.single i (b + b') : MatProd k d) • w
            = (Pi.single i b : MatProd k d) • w + (Pi.single i b' : MatProd k d) • w
        rw [Pi.single_add, add_smul]
      zero_smul := fun w => by
        change (Pi.single i (0 : Matrix (Fin (d i)) (Fin (d i)) k) : MatProd k d) • w = 0
        rw [Pi.single_zero, zero_smul] }
  haveI : IsScalarTower k (Matrix (Fin (d i)) (Fin (d i)) k) W :=
    { smul_assoc := fun c b w => by
        change (Pi.single i (c • b) : MatProd k d) • w =
          c • ((Pi.single i b : MatProd k d) • w)
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
      change eW (a • w) = a • eW w
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

/-- **Pairwise non-isomorphism of the standard representations.** The `Vᵢ = k^{dᵢ}` are
pairwise non-isomorphic as `A`-modules: the central idempotent `eᵢ = Pi.single i 1` acts as
the identity on `Vᵢ` but as zero on `Vⱼ` for `j ≠ i`, so an `A`-linear isomorphism
`Vᵢ ≃ₗ[A] Vⱼ` forces `i = j`. This is the `hd` hypothesis needed to invoke Proposition
3.1.4 in the dual-route proof of Theorem 3.3.1. -/
theorem vModuleProd_iso_imp_eq {i j : Fin r}
    (h : Nonempty ((Fin (d i) → k) ≃ₗ[MatProd k d] (Fin (d j) → k))) : i = j := by
  obtain ⟨φ⟩ := h
  by_contra hij
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin (d i) → k)
  have hVi : (Pi.single i 1 : MatProd k d) • v = v := by
    rw [vModuleProd_smul, Pi.single_eq_same, one_smul]
  have hVj : (Pi.single i 1 : MatProd k d) • φ v = 0 := by
    rw [vModuleProd_smul, Pi.single_eq_of_ne (Ne.symm hij), zero_smul]
  have hz : φ v = 0 := by
    have h1 := map_smul φ (Pi.single i 1 : MatProd k d) v
    rw [hVi, hVj] at h1
    exact h1
  exact hv (φ.injective (by rw [hz, map_zero]))

/-! ## Regular-module decomposition `A ≅ ⊕ᵢ dᵢ Vᵢ`

The book's proof of Theorem 3.3.1 uses the identity `Mat_{dᵢ}(k) = dᵢ Vᵢ`, hence
`A = ⊕ᵢ dᵢ Vᵢ` and `Aⁿ = ⊕ᵢ (n dᵢ) Vᵢ` as representations of `A`. Concretely, viewing the
left regular module `A = ⊕ᵢ Mat_{dᵢ}(k)` over itself, within the `i`-th matrix factor the
`dᵢ` columns each span a copy of the standard representation `Vᵢ = k^{dᵢ}`, and the columns
transform independently under left multiplication. -/

/-- The `A`-linear map extracting the `c`-th column of the `i`-th matrix factor:
`M ↦ (fun j => (M i) j c)`, landing in `Vᵢ = k^{dᵢ}`. This is the single-factor,
single-column building block of the regular decomposition; it is `A`-linear because within
the `i`-th factor, left multiplication acts columnwise by `mulVec`. -/
def colVec (i : Fin r) (c : Fin (d i)) :
    MatProd k d →ₗ[MatProd k d] (Fin (d i) → k) where
  toFun M := fun j => M i j c
  map_add' M N := by funext j; simp
  map_smul' N M := by
    funext j
    rw [RingHom.id_apply, vModuleProd_smul, Matrix.Module.smul_apply, smul_eq_mul, Pi.mul_apply,
      Matrix.mul_apply]
    simp [smul_eq_mul]

/-- The columns of the `i`-th matrix factor, packaged as an `A`-linear map into
`Fin (dᵢ) → Vᵢ`. -/
def colMap (i : Fin r) : MatProd k d →ₗ[MatProd k d] (Fin (d i) → (Fin (d i) → k)) :=
  LinearMap.pi fun c => colVec i c

/-- **Regular-module decomposition** (`A ≅ ⊕ᵢ dᵢ Vᵢ`). As a module over itself,
`A = ⊕ᵢ Mat_{dᵢ}(k)` is isomorphic to `⊕ᵢ dᵢ Vᵢ`, realized as the direct sum
`⨁ i, (Fin (dᵢ) → Vᵢ)` (each `Fin (dᵢ) → Vᵢ` is `dᵢ` copies of `Vᵢ = k^{dᵢ}`, with `A`
acting through its `i`-th projection). The isomorphism sends a tuple of matrices to its
columns, `M ↦ fun i c j => (M i) j c`, packaged in the direct sum.

The direct-sum target (rather than the product `∀ i, …`) is deliberate: it matches the
ambient of `Etingof.subrepresentation_of_semisimple` (Proposition 3.1.4) and avoids the
`Pi.module'` instance (product ring acting factorwise), which would otherwise supply a
different, column-mixing action on `∀ i, Fin (dᵢ) → Fin (dᵢ) → k`. -/
noncomputable def regularDecomp :
    MatProd k d ≃ₗ[MatProd k d] (⨁ i, (Fin (d i) → (Fin (d i) → k))) :=
  (LinearEquiv.ofBijective (LinearMap.pi colMap)
      (Function.bijective_iff_has_inverse.mpr
        ⟨fun w i j c => w i c j, fun _ => rfl, fun _ => rfl⟩)).trans
    (DirectSum.linearEquivFunOnFintype (MatProd k d) (Fin r)
      (fun i => Fin (d i) → (Fin (d i) → k))).symm

omit [∀ i, NeZero (d i)] in
/-- The regular-module equivalence sends a matrix tuple to its factorwise columns. -/
@[simp] theorem regularDecomp_apply (M : MatProd k d) (i : Fin r) (c j : Fin (d i)) :
    regularDecomp M i c j = M i j c := rfl

/-! ### Free-module decomposition `Aⁿ ≅ ⊕ᵢ (n·dᵢ) Vᵢ`

Stacking `n` copies of `A = ⊕ᵢ dᵢ Vᵢ` gives `Aⁿ = ⊕ᵢ (n·dᵢ) Vᵢ`. The `(n·dᵢ)` copies of
`Vᵢ = k^{dᵢ}` are indexed by pairs `(l, c)` with `l : Fin n` (which copy of `A`) and
`c : Fin dᵢ` (which column of the `i`-th matrix factor), packaged into `Fin (n·dᵢ) → Vᵢ`
via `finProdFinEquiv : Fin n × Fin dᵢ ≃ Fin (n·dᵢ)`. This is the `Aⁿ` side of the book's
`Aⁿ = ⊕ᵢ n dᵢ Vᵢ` step in the proof of Theorem 3.3.1. -/

/-- The `i`-th block of the free-module decomposition of `Aⁿ`: the `(n·dᵢ)` columns of the
`n` stacked `i`-th matrix factors, packaged into `Fin (n·dᵢ) → Vᵢ`. `A`-linear as a
composition of the columnwise `colVec` and the coordinate projection `Aⁿ → A`. -/
def freeColMap (n : ℕ) (i : Fin r) :
    (Fin n → MatProd k d) →ₗ[MatProd k d] (Fin (n * d i) → (Fin (d i) → k)) :=
  LinearMap.pi fun m =>
    (colVec i (finProdFinEquiv.symm m).2).comp (LinearMap.proj (finProdFinEquiv.symm m).1)

omit [∀ i, NeZero (d i)] in
/-- The free-column map reads the matrix entry indexed by the corresponding copy and column. -/
@[simp] theorem freeColMap_apply (n : ℕ) (i : Fin r) (M : Fin n → MatProd k d)
    (m : Fin (n * d i)) (j : Fin (d i)) :
    freeColMap n i M m j =
      M (finProdFinEquiv.symm m).1 i j (finProdFinEquiv.symm m).2 := rfl

/-- **Free-module decomposition** (`Aⁿ ≅ ⊕ᵢ (n·dᵢ) Vᵢ`). The free module `Aⁿ = Fin n → A`
over `A = ⊕ᵢ Mat_{dᵢ}(k)` is isomorphic to `⊕ᵢ (n·dᵢ) Vᵢ`, realized as the direct sum
`⨁ i, (Fin (n·dᵢ) → Vᵢ)`. The isomorphism sends `M : Fin n → A` to its columns, grouped by
matrix factor `i` and reindexed by `finProdFinEquiv`. As with `regularDecomp`, the direct-sum
target matches the ambient of `Etingof.subrepresentation_of_semisimple` and avoids the
`Pi.module'` diamond. -/
noncomputable def freeModuleDecomp (n : ℕ) :
    (Fin n → MatProd k d) ≃ₗ[MatProd k d] (⨁ i, (Fin (n * d i) → (Fin (d i) → k))) :=
  (LinearEquiv.ofBijective (LinearMap.pi fun i => freeColMap n i)
      (Function.bijective_iff_has_inverse.mpr
        ⟨fun w l i => Matrix.of fun j c => w i (finProdFinEquiv (l, c)) j,
          fun M => by
            funext l i j c
            simp only [LinearMap.pi_apply, freeColMap_apply, Matrix.of_apply,
              Equiv.symm_apply_apply],
          fun w => by
            funext i m j
            simp only [LinearMap.pi_apply, freeColMap_apply, Matrix.of_apply, Prod.mk.eta,
              Equiv.apply_symm_apply]⟩)).trans
    (DirectSum.linearEquivFunOnFintype (MatProd k d) (Fin r)
       (fun i => Fin (n * d i) → (Fin (d i) → k))).symm

end Product

/-! ## Transpose self-duality and the dual-of-surjection bridge

Two further ingredients of the book's proof of Theorem 3.3.1:

* the matrix transpose realizes `Mat_d(k) ≅ Mat_d(k)ᵒᵖ`, hence `A ≅ Aᵒᵖ`, which is what lets
  the `k`-dual `X*` (a priori an `Aᵒᵖ`-module) be viewed as an `A`-module;
* the `k`-dual of a surjection is an injection, which turns the surjection `Aⁿ ↠ X*` into the
  injection `X ↪ Aⁿ*`.
-/

section Duality

variable {k : Type*} [Field k]

/-- **Transpose self-duality of a matrix algebra.** `Matrix.transpose` realizes
`Mat_d(k) ≅ Mat_d(k)ᵐᵒᵖ` as `k`-algebras (equivalently `Mat_d(k)ᵒᵖ ≅ Mat_d(k)`), since
`(BC)ᵀ = CᵀBᵀ`. This is the isomorphism `A ≅ Aᵒᵖ` used in the proof of Theorem 3.3.1 to
turn the dual `X*` (a priori an `Aᵒᵖ`-module) into an `A`-module. -/
abbrev matrixTransposeSelfDuality (k : Type*) [Field k] (D : ℕ) :
    Matrix (Fin D) (Fin D) k ≃ₐ[k] (Matrix (Fin D) (Fin D) k)ᵐᵒᵖ :=
  Matrix.transposeAlgEquiv (Fin D) k k

/-- The opposite of a finite product of rings is the product of the opposites. -/
def piMulOppositeRingEquiv {ι : Type*} (R : ι → Type*) [∀ i, Semiring (R i)] :
    (∀ i, (R i)ᵐᵒᵖ) ≃+* (∀ i, R i)ᵐᵒᵖ where
  toFun f := MulOpposite.op fun i => (f i).unop
  invFun g := fun i => MulOpposite.op ((MulOpposite.unop g) i)
  left_inv f := by funext i; simp
  right_inv g := by simp
  map_mul' f g := MulOpposite.unop_injective <| funext fun i => by simp [MulOpposite.unop_mul]
  map_add' f g := MulOpposite.unop_injective <| funext fun i => by simp

/-- **Transpose self-duality of `A = ⊕ᵢ Mat_{dᵢ}(k)`**: `A ≅ Aᵐᵒᵖ` as rings, applying the
matrix transpose factorwise. -/
def matProdTransposeSelfDuality {r : ℕ} (d : Fin r → ℕ) :
    MatProd k d ≃+* (MatProd k d)ᵐᵒᵖ :=
  (RingEquiv.piCongrRight fun i => Matrix.transposeRingEquiv (Fin (d i)) k).trans
    (piMulOppositeRingEquiv _)

/-- **Dual of a surjection is an injection.** If `φ : M → N` is a surjective `k`-linear map,
its transpose `φ.dualMap : N* → M*` is injective. This is the step in the proof of Theorem
3.3.1 turning the surjection `Aⁿ ↠ X*` into the injection `X ↪ Aⁿ*`. -/
theorem dualMap_injective_of_surjective {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {φ : M →ₗ[k] N} (hφ : Function.Surjective φ) :
    Function.Injective φ.dualMap :=
  LinearMap.dualMap_injective_of_surjective hφ

end Duality

/-! ## The transpose-twisted dual module

The `k`-dual `X* = X →ₗ[k] k` of a left `A`-module `X` is naturally a *right* `A`-module.
Composing with a ring isomorphism `e : A ≃+* Aᵐᵒᵖ` (for `A = ⊕ᵢ Mat_{dᵢ}(k)` this is the
transpose self-duality `A ≅ Aᵒᵖ`, `matProdTransposeSelfDuality`) turns `X*` into a *left*
`A`-module via `(a • f) x = f (τ a • x)`, where `τ a = (e a).unop` is the induced
anti-automorphism of `A`. This is the structure the book uses to regard `X*` as an
`A`-representation in the proof of Theorem 3.3.1. -/

section TwistedDual

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

/-- Left multiplication by `b : A`, as a `k`-linear endomorphism of a left `A`-module `X`
(finite over the ground field `k`). `k`-linearity is `SMulCommClass k A X`, which holds
because `A` is a `k`-algebra. -/
def lsmulHom (b : A) (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] : X →ₗ[k] X where
  toFun x := b • x
  map_add' := smul_add b
  map_smul' c x := (smul_comm c b x).symm

/-- Left multiplication as a linear map evaluates to the original module action. -/
@[simp] theorem lsmulHom_apply (b : A) (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] (x : X) : lsmulHom (k := k) b X x = b • x := rfl

variable (e : A ≃+* Aᵐᵒᵖ)

/-- The transpose-twisted left `A`-module structure on the `k`-dual `X* = X →ₗ[k] k` of a
left `A`-module `X`: `(a • f) x = f (τ a • x)` with `τ a = (e a).unop`. -/
@[reducible]
def twistedDualModule (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X] : Module A (Module.Dual k X) where
  smul a f := f ∘ₗ lsmulHom (e a).unop X
  one_smul f := by
    ext x
    change f ((e 1).unop • x) = f x
    rw [map_one, MulOpposite.unop_one, one_smul]
  mul_smul a b f := by
    ext x
    change f ((e (a * b)).unop • x) = f ((e b).unop • (e a).unop • x)
    rw [map_mul, MulOpposite.unop_mul, mul_smul]
  smul_zero a := by ext x; rfl
  smul_add a f g := by ext x; rfl
  add_smul a b f := by
    ext x
    change f ((e (a + b)).unop • x) = f ((e a).unop • x) + f ((e b).unop • x)
    rw [map_add, MulOpposite.unop_add, add_smul, map_add]
  zero_smul f := by
    ext x
    change f ((e 0).unop • x) = 0
    rw [map_zero, MulOpposite.unop_zero, zero_smul, map_zero]

/-- The twisted dual action is precomposition by transpose-twisted multiplication. -/
@[simp] theorem twistedDualModule_smul_apply (X : Type*) [AddCommGroup X] [Module k X]
    [Module A X] [IsScalarTower k A X] (a : A) (f : Module.Dual k X) (x : X) :
    letI : Module A (Module.Dual k X) := twistedDualModule e X
    (a • f) x = f ((e a).unop • x) := rfl

/-- With the transpose-twisted action, `X*` is a `k`-`A`-scalar tower, provided `e` is
`k`-linear on underlying elements (`(e (c • a)).unop = c • (e a).unop`). -/
theorem twistedDual_isScalarTower (X : Type*) [AddCommGroup X] [Module k X] [Module A X]
    [IsScalarTower k A X]
    (he : ∀ (c : k) (a : A), (e (c • a)).unop = c • (e a).unop) :
    letI : Module A (Module.Dual k X) := twistedDualModule e X
    IsScalarTower k A (Module.Dual k X) := by
  letI : Module A (Module.Dual k X) := twistedDualModule e X
  refine ⟨fun c a f => ?_⟩
  ext x
  change f ((e (c • a)).unop • x) = c • f ((e a).unop • x)
  rw [he, smul_assoc, map_smul]

end TwistedDual

/-! ## Self-duality of the regular module `A ≅ A*`

For `A = ⊕ᵢ Mat_{dᵢ}(k)` the regular representation is self-dual: `A ≅ A*` as left
`A`-modules, where `A*` carries the transpose-twisted action of the previous section. The
isomorphism is the (twisted) Frobenius pairing `a ↦ (x ↦ ∑ᵢ tr(aᵢᵀ xᵢ))`; it is `A`-linear
because `tr((a'ᵢaᵢ)ᵀ xᵢ) = tr(aᵢᵀ (a'ᵢᵀ xᵢ))`, and bijective because the pairing is
nondegenerate (a dimension count over `k`). Taking `n`-fold sums gives `(Aⁿ)* ≅ Aⁿ`, the
step "`A^{n*} ≅ A^n` (check it!)" in the book's proof. -/

section DualRoute

open Matrix

variable {k : Type*} [Field k] {r : ℕ} {d : Fin r → ℕ}

/-- The transpose anti-automorphism `τ = (matProdTransposeSelfDuality ·).unop` acts
factorwise as the matrix transpose. -/
theorem matProdTransposeSelfDuality_unop (a : MatProd k d) :
    (matProdTransposeSelfDuality d a).unop = fun i => (a i)ᵀ := rfl

/-- `τ` is `k`-linear on underlying elements: the `he` hypothesis of
`twistedDual_isScalarTower` for `e = matProdTransposeSelfDuality`. -/
theorem matProdTransposeSelfDuality_unop_smul (c : k) (a : MatProd k d) :
    (matProdTransposeSelfDuality d (c • a)).unop = c • (matProdTransposeSelfDuality d a).unop := by
  rw [matProdTransposeSelfDuality_unop, matProdTransposeSelfDuality_unop]
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, Matrix.transpose_smul]

variable {X : Type*} [AddCommGroup X] [Module k X] [Module (MatProd k d) X]
  [IsScalarTower k (MatProd k d) X]

/-- The transpose-twisted `A`-module structure on the `k`-dual `X*` of any left `A`-module
`X` (for `A = ⊕ᵢ Mat_{dᵢ}(k)`), via the factorwise transpose anti-automorphism. -/
local instance instTwistedDual : Module (MatProd k d) (Module.Dual k X) :=
  twistedDualModule (matProdTransposeSelfDuality d) X

/-- The transpose-twisted dual action is compatible with the base-field action. -/
local instance instTwistedDualTower : IsScalarTower k (MatProd k d) (Module.Dual k X) := by
  refine ⟨fun c a f => ?_⟩
  refine LinearMap.ext fun x => ?_
  change f ((matProdTransposeSelfDuality d (c • a)).unop • x)
       = c • f ((matProdTransposeSelfDuality d a).unop • x)
  rw [matProdTransposeSelfDuality_unop_smul, smul_assoc, map_smul]

/-- The Frobenius pairing `a ↦ (x ↦ ∑ᵢ tr(aᵢᵀ xᵢ))` as a `k`-linear functional for fixed `a`. -/
def frobPairing (a : MatProd k d) : Module.Dual k (MatProd k d) where
  toFun x := ∑ i, Matrix.trace ((a i)ᵀ * x i)
  map_add' x y := by
    simp only [Pi.add_apply, Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply, mul_smul_comm, Matrix.trace_smul,
      Finset.smul_sum]

/-- The Frobenius pairing evaluates as the sum of factorwise matrix traces. -/
@[simp] theorem frobPairing_apply (a x : MatProd k d) :
    frobPairing a x = ∑ i, Matrix.trace ((a i)ᵀ * x i) := rfl

/-- The Frobenius pairing packaged as an `A`-linear map `A → A*` (twisted action on `A*`). -/
def frobHom : MatProd k d →ₗ[MatProd k d] Module.Dual k (MatProd k d) where
  toFun := frobPairing
  map_add' a b := by
    refine LinearMap.ext fun x => ?_
    simp only [frobPairing_apply, Pi.add_apply, Matrix.transpose_add, Matrix.add_mul,
      Matrix.trace_add, Finset.sum_add_distrib, LinearMap.add_apply]
  map_smul' a' a := by
    refine LinearMap.ext fun x => ?_
    change (∑ i, Matrix.trace (((a' * a) i)ᵀ * x i))
         = ∑ i, Matrix.trace ((a i)ᵀ * ((matProdTransposeSelfDuality d a').unop • x) i)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [smul_eq_mul, Pi.mul_apply, matProdTransposeSelfDuality_unop]
    rw [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The regular-to-dual map evaluates through the Frobenius pairing. -/
@[simp] theorem frobHom_apply (a x : MatProd k d) :
    frobHom a x = ∑ i, Matrix.trace ((a i)ᵀ * x i) := rfl

/-- The Frobenius map from the regular module to its dual is injective. -/
theorem frobHom_injective : Function.Injective (frobHom (k := k) (d := d)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  funext i
  ext p q
  have h0 : frobHom a (Pi.single i (Matrix.single p q 1)) = 0 := by rw [ha]; rfl
  rw [frobHom_apply, Finset.sum_eq_single i] at h0
  · rw [Pi.single_eq_same, Matrix.trace_mul_single] at h0
    simpa [Matrix.transpose_apply] using h0
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, Matrix.mul_zero, Matrix.trace_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The Frobenius map is a bijection for a finite product of matrix algebras. -/
theorem frobHom_bijective : Function.Bijective (frobHom (k := k) (d := d)) := by
  refine ⟨frobHom_injective, ?_⟩
  have hdim : Module.finrank k (MatProd k d)
      = Module.finrank k (Module.Dual k (MatProd k d)) := Subspace.dual_finrank_eq.symm
  have hinj : Function.Injective ((frobHom (k := k) (d := d)).restrictScalars k) := by
    simpa [LinearMap.coe_restrictScalars] using frobHom_injective
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  simpa [LinearMap.coe_restrictScalars] using hsurj

/-- **Self-duality of the regular module** (`A ≅ A*`). The Frobenius pairing gives an
`A`-linear isomorphism from `A = ⊕ᵢ Mat_{dᵢ}(k)` to its transpose-twisted `k`-dual `A*`. -/
noncomputable def matProdSelfDual :
    MatProd k d ≃ₗ[MatProd k d] Module.Dual k (MatProd k d) :=
  LinearEquiv.ofBijective frobHom frobHom_bijective

/-- The free-module map `Aⁿ → X*`, `(a₁,…,aₙ) ↦ ∑ₗ aₗ • yₗ`, associated to a `k`-basis
`{yₗ}` of `X*`. It is `A`-linear for the diagonal `A`-action on `Aⁿ` and the twisted action
on `X*`. -/
noncomputable def toDualHom {n : ℕ} (yb : Module.Basis (Fin n) k (Module.Dual k X)) :
    (Fin n → MatProd k d) →ₗ[MatProd k d] Module.Dual k X where
  toFun a := ∑ l, a l • yb l
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' b a := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- The free-to-dual map evaluates as the basis-weighted sum of its coordinates. -/
@[simp] theorem toDualHom_apply {n : ℕ} (yb : Module.Basis (Fin n) k (Module.Dual k X))
    (a : Fin n → MatProd k d) : toDualHom yb a = ∑ l, a l • yb l := rfl

/-- **The surjection `Aⁿ ↠ X*`** of the book's proof of Theorem 3.3.1: `∑ₗ aₗ • yₗ` hits
every functional because `k ⊆ A` (take `aₗ = c_ℓ · 1` for the `k`-coordinates `c_ℓ` of the
target). Here `{yₗ}` is any `k`-basis of `X*`. -/
theorem toDualHom_surjective {n : ℕ} (yb : Module.Basis (Fin n) k (Module.Dual k X)) :
    Function.Surjective (toDualHom (d := d) yb) := by
  intro f
  refine ⟨fun l => algebraMap k (MatProd k d) (yb.repr f l), ?_⟩
  change ∑ l, algebraMap k (MatProd k d) (yb.repr f l) • yb l = f
  simp only [algebraMap_smul]
  exact yb.sum_repr f

/-- The transpose anti-automorphism `τ` is an involution: `τ (τ a) = a` (double transpose). -/
theorem matProdTransposeSelfDuality_unop_unop (a : MatProd k d) :
    (matProdTransposeSelfDuality d (matProdTransposeSelfDuality d a).unop).unop = a := by
  funext i
  simp only [matProdTransposeSelfDuality_unop, Matrix.transpose_transpose]

section DualMap

variable {M N : Type*}
  [AddCommGroup M] [Module k M] [Module (MatProd k d) M] [IsScalarTower k (MatProd k d) M]
  [AddCommGroup N] [Module k N] [Module (MatProd k d) N] [IsScalarTower k (MatProd k d) N]

/-- **The transpose-twisted dual of an `A`-linear map** `f : M → N`, namely `g ↦ g ∘ f`,
is `A`-linear `N* → M*`. This is the operation `φ ↦ φ*` in the book's proof. -/
noncomputable def twistedDualMap (f : M →ₗ[MatProd k d] N) :
    Module.Dual k N →ₗ[MatProd k d] Module.Dual k M where
  toFun g := (f.restrictScalars k).dualMap g
  map_add' g h := by simp only [map_add]
  map_smul' a g := by
    refine LinearMap.ext fun m => ?_
    change g ((matProdTransposeSelfDuality d a).unop • f m)
         = g (f ((matProdTransposeSelfDuality d a).unop • m))
    rw [map_smul f]

/-- **Dual of a surjection is injective** (`A`-linear form): if `f` is a surjective `A`-linear
map then `twistedDualMap f` is injective. This turns the surjection `Aⁿ ↠ X*` into the
injection `X ↪ Aⁿ*` in the proof of Theorem 3.3.1. -/
theorem twistedDualMap_injective {f : M →ₗ[MatProd k d] N} (hf : Function.Surjective f) :
    Function.Injective (twistedDualMap f) := by
  have hf' : Function.Surjective (f.restrictScalars k) := by
    simpa [LinearMap.coe_restrictScalars] using hf
  exact dualMap_injective_of_surjective hf'

end DualMap

/-- **`X ≅ X**` as `A`-modules** (transpose-twisted double dual), from `Module.evalEquiv` and
the involutivity of `τ`. This realizes the book's identification `X ≅ (X*)*`. -/
noncomputable def twistedEvalEquiv (X : Type*)
    [AddCommGroup X] [Module k X] [Module (MatProd k d) X] [IsScalarTower k (MatProd k d) X]
    [FiniteDimensional k X] :
    X ≃ₗ[MatProd k d] Module.Dual k (Module.Dual k X) :=
  { (Module.evalEquiv k X).toAddEquiv with
    map_smul' := fun a x => by
      refine LinearMap.ext fun g => ?_
      change g (a • x)
           = g ((matProdTransposeSelfDuality d (matProdTransposeSelfDuality d a).unop).unop • x)
      rw [matProdTransposeSelfDuality_unop_unop] }

variable (X) [FiniteDimensional k X]

/-- **The embedding `X ↪ Aⁿ*`** from the book's proof of Theorem 3.3.1 (`n = dim_k X*`):
dualize the surjection `Aⁿ ↠ X*` to `X** → Aⁿ*` and precompose with `X ≅ X**`. -/
noncomputable def toDualEmbedding :
    X →ₗ[MatProd k d]
      Module.Dual k (Fin (Module.finrank k (Module.Dual k X)) → MatProd k d) :=
  (twistedDualMap (toDualHom (Module.finBasis k (Module.Dual k X)))).comp
    (twistedEvalEquiv X).toLinearMap

/-- The canonical map into the dual of a finite free module is injective. -/
theorem toDualEmbedding_injective : Function.Injective (toDualEmbedding (k := k) (d := d) X) := by
  rw [toDualEmbedding, LinearMap.coe_comp]
  exact (twistedDualMap_injective (toDualHom_surjective _)).comp (twistedEvalEquiv X).injective

/-! ## Assembling the dual route: `X ≅ ⊕ᵢ mᵢ Vᵢ`

The remaining ingredients of the book's proof of Theorem 3.3.1. First `(Aⁿ)* ≅ Aⁿ`: the
`k`-dual of the free module `Aⁿ`, with the transpose-twisted action, is `A`-linearly
isomorphic to `Aⁿ` (this is the step "`A^{n*} ≅ A^n` (check it!)"). Then, transporting the
injection `X ↪ (Aⁿ)*` across `(Aⁿ)* ≅ Aⁿ ≅ ⊕ᵢ (n·dᵢ) Vᵢ` and applying Proposition 3.1.4,
`X ≅ ⊕ᵢ mᵢ Vᵢ`. -/

/-- **`(Aⁿ)* ≅ ∏ⁿ A*` as `A`-modules.** The `k`-dual of the free module `Aⁿ = Fin n → A`,
with the transpose-twisted `A`-action, is `A`-linearly isomorphic to the product of `n`
copies of the twisted dual `A*`, via `f ↦ (l ↦ f ∘ singleₗ)` (the diagonal `A`-action on
`Aⁿ` restricts to each `singleₗ` copy of `A`). -/
noncomputable def dualPiEquiv (n : ℕ) :
    Module.Dual k (Fin n → MatProd k d) ≃ₗ[MatProd k d]
      (Fin n → Module.Dual k (MatProd k d)) where
  toFun f l := f ∘ₗ LinearMap.single k (fun _ : Fin n => MatProd k d) l
  map_add' f g := by funext l; ext b; simp
  map_smul' a f := by
    funext l
    refine LinearMap.ext fun b => ?_
    change f ((matProdTransposeSelfDuality d a).unop
              • LinearMap.single k (fun _ : Fin n => MatProd k d) l b)
       = f (LinearMap.single k (fun _ : Fin n => MatProd k d) l
              ((matProdTransposeSelfDuality d a).unop • b))
    congr 1
    funext l'
    simp only [LinearMap.single_apply, Pi.single_apply, Pi.smul_apply]
    by_cases h : l' = l <;> simp [h]
  invFun g := ∑ l, (g l) ∘ₗ LinearMap.proj l
  left_inv f := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.single_apply]
    rw [← map_sum]
    congr 1
    exact Finset.univ_sum_single x
  right_inv g := by
    funext l
    refine LinearMap.ext fun b => ?_
    simp only [LinearMap.comp_apply, LinearMap.single_apply, LinearMap.coe_sum,
      Finset.sum_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single l]
    · simp
    · intro l' _ hl'; simp [Ne.symm hl']
    · intro h; exact absurd (Finset.mem_univ l) h

/-- **`(Aⁿ)* ≅ Aⁿ` as `A`-modules** — the step "`A^{n*} ≅ A^n` (check it!)" of the book's
proof of Theorem 3.3.1. Split the dual of the free module into `n` copies of `A*`
(`dualPiEquiv`), then apply the regular self-duality `A* ≅ A` (`matProdSelfDual`) on each. -/
noncomputable def dualPowSelfDual (n : ℕ) :
    Module.Dual k (Fin n → MatProd k d) ≃ₗ[MatProd k d] (Fin n → MatProd k d) :=
  (dualPiEquiv n).trans
    (LinearEquiv.piCongrRight fun _ : Fin n => (matProdSelfDual (k := k) (d := d)).symm)

variable [∀ i, NeZero (d i)]

/-- The standard representation `Vⱼ = k^{dⱼ}` as an `A`-module, needed to phrase the
conclusion of the dual route in the `DualRoute` section (the `Product`-section instance
`vModuleProd` is out of scope here). Definitionally equal to it. -/
local instance vModuleProdDual (j : Fin r) : Module (MatProd k d) (Fin (d j) → k) :=
  Module.compHom _ (Pi.evalRingHom (fun i => Matrix (Fin (d i)) (Fin (d i)) k) j)

/-- **Theorem 3.3.1, dual route: `X ≅ ⊕ᵢ mᵢ Vᵢ`.** Any finite-dimensional representation
`X` of `A = ⊕ᵢ Mat_{dᵢ}(k)` is a direct sum of copies of the standard representations
`Vᵢ = k^{dᵢ}`. This is the end-to-end conclusion of the book's dual-route proof: dualize the
surjection `Aⁿ ↠ X*` (`n = dim_k X*`) to the injection `X ↪ (Aⁿ)*`, transport across
`(Aⁿ)* ≅ Aⁿ ≅ ⊕ᵢ (n·dᵢ) Vᵢ`, and apply Proposition 3.1.4 to the image subrepresentation. -/
theorem exists_iso_directSum_of_matrixProd :
    ∃ m : Fin r → ℕ,
      Nonempty (X ≃ₗ[MatProd k d] ⨁ i, (Fin (m i) → (Fin (d i) → k))) := by
  haveI : ∀ i, IsSimpleModule (MatProd k d) (Fin (d i) → k) := isSimpleModule_vModuleProd
  -- `(Aⁿ)* ≅ Aⁿ ≅ ⊕ᵢ (n·dᵢ) Vᵢ`, with `n = dim_k X*`.
  let e := (dualPowSelfDual (k := k) (d := d) (Module.finrank k (Module.Dual k X))).trans
    (freeModuleDecomp (Module.finrank k (Module.Dual k X)))
  -- The injection `X ↪ ⊕ᵢ (n·dᵢ) Vᵢ`.
  let F := e.toLinearMap.comp (toDualEmbedding X)
  have hF : Function.Injective F := e.injective.comp (toDualEmbedding_injective X)
  -- Its image is a subrepresentation of `⊕ᵢ (n·dᵢ) Vᵢ`; apply Proposition 3.1.4.
  obtain ⟨m, -, ⟨φ⟩⟩ := Etingof.subrepresentation_of_semisimple
    (V := fun i => Fin (d i) → k)
    (fun i => Module.finrank k (Module.Dual k X) * d i)
    (fun ⦃i j⦄ h => vModuleProd_iso_imp_eq h) (LinearMap.range F)
  exact ⟨m, ⟨(LinearEquiv.ofInjective F hF).trans φ⟩⟩

end DualRoute
