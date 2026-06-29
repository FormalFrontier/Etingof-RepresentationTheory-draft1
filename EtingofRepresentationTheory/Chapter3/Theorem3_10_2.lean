import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Artinian.Module
import EtingofRepresentationTheory.Chapter3.Theorem3_2_2

/-!
# Theorem 3.10.2: Irreducible Representations of Tensor Products of Algebras

(i) Let V be an irreducible finite dimensional representation of A and let W be an
    irreducible finite dimensional representation of B. Then V ⊗ W is an irreducible
    representation of A ⊗ B.

(ii) Any irreducible finite dimensional representation M of A ⊗ B has the form (i) for
     unique V and W.

The (A ⊗_k B)-module structure on V ⊗_k W is given by (a ⊗ b) • (v ⊗ w) = (a • v) ⊗ (b • w).
Irreducibility is stated as: the only k-submodules of V ⊗ W invariant under all such
actions are {0} and the whole space.

Note: These results require k to be algebraically closed (as assumed throughout Etingof's
textbook). Without algebraic closure, the tensor product of irreducible representations
need not be irreducible (e.g., ℂ ⊗_ℝ ℂ ≅ ℂ × ℂ as ℂ ⊗ ℂ-modules).
-/

section Part1

open scoped TensorProduct

variable {k : Type*} {V W : Type*}
  [Field k]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

omit [FiniteDimensional k V] [FiniteDimensional k W] in
/-- For linear functionals φ : V →ₗ k, ψ : W →ₗ k and vectors v₀ : V, w₀ : W,
applying TensorProduct.map (φ.smulRight v₀) (ψ.smulRight w₀) to t yields
(bilinear contraction of t by φ,ψ) • (v₀ ⊗ w₀). -/
private theorem map_smulRight_smulRight_eq
    (φ : V →ₗ[k] k) (ψ : W →ₗ[k] k) (v₀ : V) (w₀ : W) (t : V ⊗[k] W) :
    TensorProduct.map (φ.smulRight v₀) (ψ.smulRight w₀) t =
      TensorProduct.lid k k (TensorProduct.map φ ψ t) • (v₀ ⊗ₜ[k] w₀) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.smulRight_apply, TensorProduct.lid_tmul,
      smul_eq_mul, TensorProduct.smul_tmul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_smul]

/-- If U is a nonzero k-submodule of V ⊗ W stable under all TensorProduct.map f g,
then every pure tensor v ⊗ w is in U. -/
private theorem pure_tensors_mem_of_stable
    (U : Submodule k (V ⊗[k] W))
    (hU_end : ∀ (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W),
        x ∈ U → TensorProduct.map f g x ∈ U)
    {u : V ⊗[k] W} (hu : u ∈ U) (hu_ne : u ≠ 0)
    (v : V) (w : W) : v ⊗ₜ[k] w ∈ U := by
  classical
  -- Decompose u using a basis of V to find φ, ψ with nonzero contraction.
  let bV := Module.finBasis k V
  let coeffs := TensorProduct.equivFinsuppOfBasisLeft bV u
  -- u ≠ 0 implies the decomposition has a nonzero W-coefficient
  have hcoeffs_ne : coeffs ≠ 0 := by
    intro h
    apply hu_ne
    have : u = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply u).symm
    rw [this, h, map_zero]
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hcoeffs_ne
  simp only [Finsupp.zero_apply] at hi₀
  -- w₀ is the nonzero W-coefficient at index i₀
  set w₀ := coeffs i₀ with hw₀_def
  -- Choose φ = bV.coord i₀ and find ψ with ψ(w₀) ≠ 0
  let bW := Module.finBasis k W
  have hw₀_ne : w₀ ≠ 0 := hi₀
  have hrepr_ne : bW.repr w₀ ≠ 0 :=
    fun h => hw₀_ne (bW.repr.injective (show _ = _ by simp [h]))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hrepr_ne
  simp only [Finsupp.zero_apply] at hj₀
  -- The bilinear contraction c = ψ(w₀) ≠ 0
  -- where φ = bV.coord i₀, ψ = bW.coord j₀
  -- Use the general formula: map (φ.smulRight v) (ψ.smulRight w) u = c • (v ⊗ w)
  have h_mem : TensorProduct.map ((bV.coord i₀).smulRight v) ((bW.coord j₀).smulRight w) u ∈ U :=
    hU_end _ _ u hu
  rw [map_smulRight_smulRight_eq] at h_mem
  -- The contraction TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u)
  -- equals ψ(w₀) ≠ 0
  set c := TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u)
  -- Show c ≠ 0
  have hc_ne : c ≠ 0 := by
    -- Show c = (bW.coord j₀)(w₀) = (bW.repr w₀) j₀ ≠ 0
    suffices hc_eq : c = (bW.repr w₀) j₀ by rw [hc_eq]; exact hj₀
    -- Rewrite u via the basis decomposition
    have hu_decomp : u = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply u).symm
    -- c is defined as lid (map φ ψ u); compute by rewriting u
    show TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) u) = _
    rw [hu_decomp, TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    -- Distribute linear maps over the Finsupp sum
    rw [Finsupp.sum]
    simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    -- The sum collapses to the i₀ term
    rw [Finset.sum_eq_single i₀]
    · simp [hw₀_def]
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finsupp.mem_support_iff.mpr hi₀) h
  -- Since c ≠ 0 and c • (v ⊗ w) ∈ U, deduce v ⊗ w ∈ U
  have := U.smul_mem c⁻¹ h_mem
  rwa [inv_smul_smul₀ hc_ne] at this

end Part1

open TensorProduct in
/-- The tensor product of irreducible representations is irreducible over the tensor
product of algebras: the only k-submodules of V ⊗ W closed under the action
(a ⊗ b) • (v ⊗ w) = (a • v) ⊗ (b • w) for all a ∈ A, b ∈ B are {0} and V ⊗ W.
Etingof Theorem 3.10.2(i).

Proof: By the density theorem, A → End_k(V) and B → End_k(W) are surjective.
So U is stable under TensorProduct.map f g for all f ∈ End(V), g ∈ End(W).
Pick nonzero u ∈ U, decompose using a basis of V, and use a rank-1 projection
to extract a nonzero pure tensor. Then the A- and B-actions generate all of V ⊗ W. -/
theorem Etingof.tensor_product_irreducible (k : Type*) (A B V W : Type*)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W]
    [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSimpleModule A V] [IsSimpleModule B W] :
    ∀ (U : Submodule k (V ⊗[k] W)),
      (∀ (a : A) (b : B) (x : V ⊗[k] W), x ∈ U →
        TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a)
          ((Algebra.lsmul k k W : B →ₐ[k] Module.End k W) b) x ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨u, hu, hu_ne⟩ := U.ne_bot_iff.mp hbot
    -- Density theorem: A → End(V) and B → End(W) are surjective
    have hdens_A := Etingof.density_theorem_part1 k A V
    have hdens_B := Etingof.density_theorem_part1 k B W
    -- U is stable under TensorProduct.map f g for all f : End V, g : End W
    have hU_end : ∀ (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W),
        x ∈ U → TensorProduct.map f g x ∈ U := by
      intro f g x hx
      obtain ⟨a, ha⟩ := hdens_A f
      obtain ⟨b, hb⟩ := hdens_B g
      rw [← ha, ← hb]
      exact hU a b x hx
    -- Every element is in U (since every pure tensor is)
    rw [eq_top_iff]
    intro x _
    -- x is in the span of pure tensors
    have := span_tmul_eq_top k V W
    rw [eq_top_iff] at this
    have hx := this (Submodule.mem_top : x ∈ ⊤)
    -- It suffices to show every pure tensor is in U
    refine Submodule.span_le.mpr ?_ hx
    intro t ht
    obtain ⟨v, w, rfl⟩ := ht
    exact pure_tensors_mem_of_stable U hU_end hu hu_ne v w

/-! ## Part 2: Classification of irreducible representations of tensor products

The proof proceeds as follows:
1. Find a simple A-submodule V₀ of M (using finite-dimensionality → Artinian → atomic)
2. Define W₀ = Hom_A(V₀, M) with B-module structure via (b • f)(v) = b • f(v)
3. Build the evaluation map ev: V₀ ⊗ W₀ → M, ev(v ⊗ f) = f(v)
4. Show ev is surjective (image is A-B-invariant, nonzero, so = M)
5. Show ev is injective (using density theorem: A → End_k(V₀) surjective)
6. Show W₀ is simple as B-module (dimension argument from bijectivity of ev)
-/

section Part2Helpers

open scoped TensorProduct

variable {k : Type*} {A B : Type*} [Field k] [IsAlgClosed k]
  [Ring A] [Algebra k A] [FiniteDimensional k A]
  [Ring B] [Algebra k B] [FiniteDimensional k B]

variable {M : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
  [Module A M] [IsScalarTower k A M]
  [Module B M] [IsScalarTower k B M]
  [SMulCommClass A B M]

variable (V₀ : Submodule A M)

/-- B-scalar multiplication on Hom_A(V₀, M): (b • f)(v) = b • f(v).
This is A-linear since A and B commute on M. -/
noncomputable def homBSMul (b : B) (f : V₀ →ₗ[A] M) : V₀ →ₗ[A] M where
  toFun v := b • f v
  map_add' x y := by simp [smul_add]
  map_smul' a v := by
    simp only [RingHom.id_apply]
    rw [f.map_smul, smul_comm a b]

/-- The B-module instance on Hom_A(V₀, M). -/
noncomputable instance homBModule : Module B (V₀ →ₗ[A] M) where
  smul := homBSMul V₀
  one_smul f := by ext v; exact one_smul B (f v)
  mul_smul b₁ b₂ f := by ext v; exact mul_smul b₁ b₂ (f v)
  smul_zero b := by ext v; exact smul_zero b
  smul_add b f g := by ext v; exact smul_add b (f v) (g v)
  add_smul b₁ b₂ f := by ext v; exact add_smul b₁ b₂ (f v)
  zero_smul f := by ext v; exact zero_smul B (f v)

instance homIsScalarTowerKB : IsScalarTower k B (V₀ →ₗ[A] M) where
  smul_assoc c b f := by
    ext v; show (c • b) • f v = c • (b • f v)
    exact smul_assoc c b (f v)

/-- The evaluation map V₀ ⊗_k Hom_A(V₀, M) →ₗ[k] M sending v ⊗ f to f(v). -/
noncomputable def evalMap : V₀ ⊗[k] (V₀ →ₗ[A] M) →ₗ[k] M :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun f => f v
          map_add' := fun _ _ => rfl
          map_smul' := fun c f => by
            change (c • f) v = c • f v
            rfl }
      map_add' := fun v₁ v₂ => by ext f; exact f.map_add v₁ v₂
      map_smul' := fun c v => by
        ext f; simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        show f (c • v) = c • f v
        -- f is A-linear; c acts via algebraMap k A
        have h1 : f ((algebraMap k A c) • v) = (algebraMap k A c) • f v := f.map_smul _ _
        rwa [algebraMap_smul, algebraMap_smul] at h1 }

omit [IsAlgClosed k] [FiniteDimensional k A] [FiniteDimensional k M] in
@[simp]
theorem evalMap_tmul (v : V₀) (f : V₀ →ₗ[A] M) :
    evalMap V₀ (v ⊗ₜ[k] f) = f v := by
  simp [evalMap]

end Part2Helpers

open TensorProduct in
/-- Every irreducible representation of A ⊗ B arises as V ⊗ W for unique irreducible
representations V of A and W of B. Specifically, given any finite-dimensional
k-vector space M with commuting A and B actions that is irreducible (no proper nonzero
invariant k-submodules), M ≅ V ⊗ W for some irreducible V of A and W of B.
Etingof Theorem 3.10.2(ii). -/
theorem Etingof.tensor_product_irreducible_classification.{u}
    (k : Type*) (A B : Type*)
    (M : Type u)
    [Field k] [IsAlgClosed k]
    [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Ring B] [Algebra k B] [FiniteDimensional k B]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module A M] [IsScalarTower k A M]
    [Module B M] [IsScalarTower k B M]
    [SMulCommClass A B M]
    [Nontrivial M]
    (hM : ∀ (U : Submodule k M),
      (∀ (a : A) (x : M), x ∈ U → a • x ∈ U) →
      (∀ (b : B) (x : M), x ∈ U → b • x ∈ U) →
      U = ⊥ ∨ U = ⊤) :
    ∃ (V : Type u) (W : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Module A V)
      (_ : IsScalarTower k A V) (_ : FiniteDimensional k V) (_ : IsSimpleModule A V)
      (_ : AddCommGroup W) (_ : Module k W) (_ : Module B W)
      (_ : IsScalarTower k B W) (_ : FiniteDimensional k W) (_ : IsSimpleModule B W)
      (e : M ≃ₗ[k] V ⊗[k] W),
      (∀ (a : A) (m : M),
        e (a • m) = TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id (e m)) ∧
      (∀ (b : B) (m : M),
        e (b • m) = TensorProduct.map LinearMap.id ((Algebra.lsmul k k W : B →ₐ[k] _) b) (e m)) := by
  -- Step 1: M is Artinian as A-module, hence atomic; extract a simple A-submodule V₀
  haveI : IsArtinian A M := isArtinian_of_tower k (inferInstance : IsArtinian k M)
  have hM_ne : (⊤ : Submodule A M) ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx (congr_arg (x ∈ ·) h |>.mp Submodule.mem_top)
  haveI hatomic : IsAtomic (Submodule A M) :=
    isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨V₀, hV₀_atom, _⟩ :=
    (hatomic.eq_bot_or_exists_atom_le (⊤ : Submodule A M)).resolve_left hM_ne
  haveI : IsSimpleModule A V₀ := isSimpleModule_iff_isAtom.mpr hV₀_atom
  haveI : FiniteDimensional k V₀ := by
    have : Module.Finite k (V₀.restrictScalars k) := inferInstance
    exact this
  -- Step 2: W₀ = Hom_A(V₀, M) with B-module structure (from Part2Helpers)
  set W₀ := V₀ →ₗ[A] M
  -- The inclusion V₀ ↪ M gives a nonzero element of W₀
  have hι_ne : (V₀.subtype.restrictScalars A : W₀) ≠ 0 := by
    intro h
    have hzero : ∀ v : V₀, (v : M) = 0 := fun v => LinearMap.congr_fun h v
    exact hV₀_atom.1 (eq_bot_iff.mpr fun x hx => hzero ⟨x, hx⟩)
  -- Step 3: Surjectivity of evalMap
  have hev_surj : Function.Surjective (evalMap V₀ : V₀ ⊗[k] W₀ →ₗ[k] M) := by
    rw [← LinearMap.range_eq_top]
    set evR := LinearMap.range (evalMap V₀ : V₀ ⊗[k] W₀ →ₗ[k] M)
    have hA_inv : ∀ (a : A) (x : M), x ∈ evR → a • x ∈ evR := by
      rintro a _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v f =>
        exact ⟨(a • v) ⊗ₜ[k] f, by simp [evalMap_tmul, f.map_smul]⟩
      | add _ _ hx hy =>
        rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
    have hB_inv : ∀ (b : B) (x : M), x ∈ evR → b • x ∈ evR := by
      rintro b _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul v f => exact ⟨v ⊗ₜ[k] homBSMul V₀ b f, by simp [evalMap_tmul, homBSMul]⟩
      | add _ _ hx hy =>
        rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
    have hne : evR ≠ ⊥ := by
      intro h
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₀_atom.1
      have : (v : M) ∈ evR :=
        ⟨⟨v, hv_mem⟩ ⊗ₜ[k] V₀.subtype.restrictScalars A, by simp [evalMap_tmul]⟩
      rw [h, Submodule.mem_bot] at this; exact hv_ne this
    exact (hM evR hA_inv hB_inv).resolve_left hne
  -- Step 4: Injectivity via density theorem
  have hev_inj : Function.Injective (evalMap V₀ : V₀ ⊗[k] W₀ →ₗ[k] M) := by
    -- A-equivariance: ev ∘ (ρ(a) ⊗ id) = a • ev
    have hequi : ∀ (a : A) (s : V₀ ⊗[k] W₀),
        evalMap V₀ (TensorProduct.map ((Algebra.lsmul k k V₀ : A →ₐ[k] _) a)
          LinearMap.id s) = a • evalMap V₀ s := by
      intro a s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul v f =>
        rw [TensorProduct.map_tmul, LinearMap.id_apply, evalMap_tmul, evalMap_tmul]
        simp only [Algebra.lsmul_coe]
        exact f.map_smul a v
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
    -- ker(ev) is stable under map(φ, id) for all φ ∈ End_k(V₀)
    have hstable : ∀ (φ : Module.End k V₀) (s : V₀ ⊗[k] W₀),
        evalMap V₀ s = 0 → evalMap V₀ (TensorProduct.map φ LinearMap.id s) = 0 := by
      intro φ s hs
      obtain ⟨a, ha⟩ := Etingof.density_theorem_part1 k A V₀ φ
      rw [← ha, hequi, hs, smul_zero]
    -- Proof by contradiction
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    obtain ⟨t, ht_mem, ht_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker] at ht_mem
    -- Decompose t using a basis of V₀
    let bV := Module.finBasis k V₀
    have ht_ne' : TensorProduct.equivFinsuppOfBasisLeft bV t ≠ 0 := by
      intro h; exact ht_ne ((TensorProduct.equivFinsuppOfBasisLeft bV).injective
        (show _ = _ by rw [h, map_zero]))
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp ht_ne'
    simp only [Finsupp.zero_apply] at hj
    -- wⱼ ≠ 0, so ∃ v with wⱼ(v) ≠ 0
    obtain ⟨v, hv⟩ : ∃ v, (TensorProduct.equivFinsuppOfBasisLeft bV t) j v ≠ 0 := by
      by_contra h; push_neg at h
      exact hj (LinearMap.ext fun v => by simpa using h v)
    -- Build φ : V₀ → V₀ with φ(bV i) = δᵢⱼ v using Basis.constr
    let φ : Module.End k V₀ := bV.constr k (fun i => if i = j then v else 0)
    have hφ : ∀ i, φ (bV i) = if i = j then v else 0 :=
      fun i => bV.constr_basis k _ i
    -- ev(map(φ, id)(t)) = 0 by stability
    have hzero := hstable φ t ht_mem
    -- But ev(map(φ, id)(t)) = wⱼ(v) ≠ 0
    -- Rewrite t using basis decomposition
    have ht_eq : t = Finsupp.sum (TensorProduct.equivFinsuppOfBasisLeft bV t)
        (fun i w => bV i ⊗ₜ[k] w) := by
      rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
          LinearEquiv.symm_apply_apply]
    rw [ht_eq] at hzero
    simp only [Finsupp.sum, map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
      evalMap_tmul] at hzero
    -- φ(bV i) = δᵢⱼ v, so the sum simplifies
    simp only [hφ] at hzero
    rw [Finset.sum_eq_single j] at hzero
    · simp at hzero; exact hv hzero
    · intro i _ hi; simp [hi]
    · intro hj_mem
      exfalso; exact hj_mem (Finsupp.mem_support_iff.mpr (by intro h; exact hj h))
  set ev_equiv : V₀ ⊗[k] W₀ ≃ₗ[k] M :=
    LinearEquiv.ofBijective (evalMap V₀) ⟨hev_inj, hev_surj⟩ with hev_def
  have ev_apply : ∀ x, ev_equiv x = evalMap V₀ x := by
    intro x; rw [hev_def, LinearEquiv.ofBijective_apply]
  -- The evaluation map is equivariant for both the A- and B-actions.
  have hAeq : ∀ (a : A) (s : V₀ ⊗[k] W₀),
      evalMap V₀ (TensorProduct.map ((Algebra.lsmul k k V₀ : A →ₐ[k] _) a) LinearMap.id s)
        = a • evalMap V₀ s := by
    intro a s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, evalMap_tmul, evalMap_tmul]
      simp only [Algebra.lsmul_coe]
      exact f.map_smul a v
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  have hBeq : ∀ (b : B) (s : V₀ ⊗[k] W₀),
      evalMap V₀ (TensorProduct.map LinearMap.id ((Algebra.lsmul k k W₀ : B →ₐ[k] _) b) s)
        = b • evalMap V₀ s := by
    intro b s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, evalMap_tmul, evalMap_tmul]
      simp only [Algebra.lsmul_coe]
      rfl
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  -- W₀ is finite-dimensional: V₀ ⊗ W₀ ≃ M is f.d., and V₀ is nonzero
  haveI : FiniteDimensional k W₀ := by
    -- Build injective k-linear map W₀ → (V₀ →ₗ[k] M)
    let ι : W₀ →ₗ[k] (V₀ →ₗ[k] M) :=
      { toFun := fun f => f.restrictScalars k
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => by
          ext v; show (c • f) v = c • f v; rfl }
    exact Module.Finite.of_injective ι (fun f g h => by
      ext v; exact LinearMap.congr_fun h v)
  -- W₀ is simple as B-module
  haveI : IsSimpleModule B W₀ := by
    haveI : Nontrivial W₀ :=
      ⟨⟨0, V₀.subtype.restrictScalars A, hι_ne.symm⟩⟩
    have hsimple : ∀ S : Submodule B W₀, S = ⊥ ∨ S = ⊤ := by
      intro S
      by_contra hS
      push_neg at hS
      obtain ⟨hS_ne_bot, hS_ne_top⟩ := hS
      -- S ≠ ⊥: ∃ nonzero f ∈ S
      obtain ⟨f, hf_mem, hf_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS_ne_bot
      -- f ≠ 0: ∃ v with f(v) ≠ 0
      obtain ⟨v, hv⟩ : ∃ v, (f : W₀) v ≠ 0 := by
        by_contra h; push_neg at h
        exact hf_ne (LinearMap.ext fun v => by simpa using h v)
      -- Image of ev|_{V₀ ⊗ S} is A-B-invariant and nonzero → = M
      -- Build restricted eval: V₀ ⊗ S → M
      -- For s : S, the map (s : W₀) : V₀ →ₗ[A] M
      -- evS(v ⊗ s) = (s : W₀)(v)
      let incl : S →ₗ[k] W₀ := S.subtype.restrictScalars k
      set evS : V₀ ⊗[k] S →ₗ[k] M :=
        (evalMap V₀).comp (TensorProduct.map LinearMap.id incl) with hevS_def
      have hevS_tmul : ∀ (v' : V₀) (g : S), evS (v' ⊗ₜ[k] g) = (g : W₀) v' := by
        intro v' g; simp only [hevS_def, LinearMap.comp_apply, TensorProduct.map_tmul,
          LinearMap.id_apply, evalMap_tmul]; rfl
      have hevS_surj : Function.Surjective evS := by
        rw [← LinearMap.range_eq_top]
        set R := LinearMap.range evS
        have hR_A : ∀ (a : A) (x : M), x ∈ R → a • x ∈ R := by
          rintro a _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul v' g =>
            rw [hevS_tmul]; exact ⟨(a • v') ⊗ₜ[k] g, by rw [hevS_tmul, (g : W₀).map_smul]⟩
          | add _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
        have hR_B : ∀ (b : B) (x : M), x ∈ R → b • x ∈ R := by
          rintro b _ ⟨t, rfl⟩
          induction t using TensorProduct.induction_on with
          | zero => simp
          | tmul v' g =>
            rw [hevS_tmul]
            refine ⟨v' ⊗ₜ[k] ⟨b • (g : W₀), S.smul_mem b g.2⟩, ?_⟩
            rw [hevS_tmul]; rfl
          | add _ _ hx hy => rw [map_add, smul_add]; exact Submodule.add_mem _ hx hy
        have hR_ne : R ≠ ⊥ := by
          intro h
          have : evS (v ⊗ₜ[k] ⟨f, hf_mem⟩) ∈ R := LinearMap.mem_range_self evS _
          rw [h, Submodule.mem_bot] at this
          rw [hevS_tmul] at this
          exact hv this
        exact (hM R hR_A hR_B).resolve_left hR_ne
      -- S is finite-dimensional (submodule of f.d. W₀)
      haveI : FiniteDimensional k S :=
        Module.Finite.of_injective incl Subtype.val_injective
      -- Dimension argument
      have h1 : Module.finrank k M ≤ Module.finrank k V₀ * Module.finrank k S := by
        rw [← Module.finrank_tensorProduct]
        calc Module.finrank k M
            = Module.finrank k (LinearMap.range evS) + 0 := by
              rw [LinearMap.range_eq_top.mpr hevS_surj]; simp
          _ ≤ Module.finrank k (LinearMap.range evS) +
              Module.finrank k (LinearMap.ker evS) := by omega
          _ = _ := evS.finrank_range_add_finrank_ker
      have h2 : Module.finrank k M = Module.finrank k V₀ * Module.finrank k W₀ := by
        rw [← Module.finrank_tensorProduct, ev_equiv.finrank_eq]
      haveI : Nontrivial V₀ := by
        obtain ⟨x, hx, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₀_atom.1
        exact ⟨⟨⟨x, hx⟩, 0, fun h => hx_ne (congr_arg Subtype.val h)⟩⟩
      have hV₀_pos : 0 < Module.finrank k V₀ := Module.finrank_pos
      have h3 : Module.finrank k W₀ ≤ Module.finrank k S := by
        exact Nat.le_of_mul_le_mul_left (h2 ▸ h1) hV₀_pos
      have h4 : Module.finrank k S ≤ Module.finrank k W₀ :=
        Submodule.finrank_le (S.restrictScalars k)
      have hS_k_top : S.restrictScalars k = ⊤ :=
        Submodule.eq_top_of_finrank_eq
          (show Module.finrank k (S.restrictScalars k) = _ from le_antisymm h4 h3)
      exact hS_ne_top (eq_top_iff.mpr fun x _ => by
        have : x ∈ (S.restrictScalars k : Set W₀) := by rw [hS_k_top]; trivial
        exact this)
    exact { toIsSimpleOrder := { eq_bot_or_eq_top := hsimple } }
  refine ⟨↥V₀, W₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ev_equiv.symm, ?_, ?_⟩
  · -- A-equivariance of `ev_equiv.symm`.
    intro a m
    apply ev_equiv.injective
    rw [LinearEquiv.apply_symm_apply, ev_apply, hAeq]
    have hsm : evalMap V₀ (ev_equiv.symm m) = m := by
      rw [← ev_apply]; exact ev_equiv.apply_symm_apply m
    rw [hsm]
  · -- B-equivariance of `ev_equiv.symm`.
    intro b m
    apply ev_equiv.injective
    rw [LinearEquiv.apply_symm_apply, ev_apply, hBeq]
    have hsm : evalMap V₀ (ev_equiv.symm m) = m := by
      rw [← ev_apply]; exact ev_equiv.apply_symm_apply m
    rw [hsm]

/-! ## Part 3: Uniqueness of the factors

Theorem 3.10.2(ii) of Etingof asserts not merely that an irreducible representation `M`
of `A ⊗ B` has the form `V ⊗ W`, but that `V` and `W` are **unique** (up to isomorphism).
We record this as a companion theorem: any two `A`-`B`-equivariant factorizations of the
same module agree up to isomorphism of the factors.

The proof is Schur's lemma applied to the `A`-action. An `A`-`B`-equivariant equivalence
`e : V ⊗ W ≃ V' ⊗ W'` is in particular `A`-linear (with `A` acting on the left factors).
Fixing `0 ≠ w₀ ∈ W` and a functional `ψ : W' → k`, the map
`v ↦ rid (map id ψ (e (v ⊗ w₀)))` is an `A`-linear map `V → V'`; for a suitable `ψ` it is
nonzero, hence an isomorphism by Schur's lemma. Uniqueness of `W` follows by symmetry,
applying the same lemma to the factor-swapped equivalence `W ⊗ V ≃ W' ⊗ V'`. -/

section Part3Helpers

open scoped TensorProduct

/-- A nonzero vector in a finite-dimensional space is detected by some linear functional. -/
private theorem exists_functional_ne_zero {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {v : V} (hv : v ≠ 0) :
    ∃ φ : V →ₗ[k] k, φ v ≠ 0 := by
  classical
  let bV := Module.finBasis k V
  have hrepr : bV.repr v ≠ 0 := fun h => hv (bV.repr.injective (by simp [h]))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr
  simp only [Finsupp.zero_apply] at hi
  exact ⟨bV.coord i, by simpa [Module.Basis.coord_apply] using hi⟩

/-- A nonzero pure tensor of two nonzero vectors over a field. -/
private theorem tmul_ne_zero {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[k] w ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_functional_ne_zero (k := k) hv
  obtain ⟨ψ, hψ⟩ := exists_functional_ne_zero (k := k) hw
  intro h
  apply mul_ne_zero hφ hψ
  have := congrArg (fun z => TensorProduct.lid k k (TensorProduct.map φ ψ z)) h
  simpa [TensorProduct.map_tmul, TensorProduct.lid_tmul] using this

/-- For a nonzero element of `V ⊗ W` (both finite-dimensional over a field) there exist
functionals `φ`, `ψ` whose contraction is nonzero. -/
private theorem exists_contraction_ne_zero {k V W : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {t : V ⊗[k] W} (ht : t ≠ 0) :
    ∃ (φ : V →ₗ[k] k) (ψ : W →ₗ[k] k),
      TensorProduct.lid k k (TensorProduct.map φ ψ t) ≠ 0 := by
  classical
  let bV := Module.finBasis k V
  let coeffs := TensorProduct.equivFinsuppOfBasisLeft bV t
  have hcoeffs_ne : coeffs ≠ 0 := by
    intro h
    apply ht
    have : t = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
      ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply t).symm
    rw [this, h, map_zero]
  obtain ⟨i₀, hi₀⟩ := Finsupp.ne_iff.mp hcoeffs_ne
  simp only [Finsupp.zero_apply] at hi₀
  set w₀ := coeffs i₀ with hw₀_def
  let bW := Module.finBasis k W
  have hrepr_ne : bW.repr w₀ ≠ 0 :=
    fun h => hi₀ (bW.repr.injective (by simp [h]))
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hrepr_ne
  simp only [Finsupp.zero_apply] at hj₀
  refine ⟨bV.coord i₀, bW.coord j₀, ?_⟩
  suffices hc : TensorProduct.lid k k (TensorProduct.map (bV.coord i₀) (bW.coord j₀) t)
      = (bW.repr w₀) j₀ by rw [hc]; exact hj₀
  have hu_decomp : t = (TensorProduct.equivFinsuppOfBasisLeft bV).symm coeffs :=
    ((TensorProduct.equivFinsuppOfBasisLeft bV).symm_apply_apply t).symm
  conv_lhs => rw [hu_decomp]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum]
  simp only [map_sum, TensorProduct.map_tmul, TensorProduct.lid_tmul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i₀]
  · simp [hw₀_def]
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finsupp.mem_support_iff.mpr hi₀) h

/-- Contraction by `φ` of a right-partial contraction by `ψ` equals the full contraction. -/
private theorem lid_map_eq_apply_rid {k V' W' : Type*} [Field k]
    [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']
    (φ : V' →ₗ[k] k) (ψ : W' →ₗ[k] k) (z : V' ⊗[k] W') :
    φ ((TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ z))
      = TensorProduct.lid k k (TensorProduct.map φ ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v' w' =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul,
      map_smul, smul_eq_mul, TensorProduct.lid_tmul]
    ring
  | add x y hx hy => simp [map_add, hx, hy]

/-- The right-partial contraction `rid ∘ map id ψ` intertwines the left `A`-action
`map (lsmul a) id` with the `A`-action on `V'`. -/
private theorem rid_mapψ_lsmul {k A V' W' : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V']
    [AddCommGroup W'] [Module k W']
    (ψ : W' →ₗ[k] k) (a : A) (z : V' ⊗[k] W') :
    (TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ
        (TensorProduct.map ((Algebra.lsmul k k V' : A →ₐ[k] _) a) LinearMap.id z))
      = a • (TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v' w' =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, Algebra.lsmul_coe,
      TensorProduct.rid_tmul]
    exact smul_comm (ψ w') a v'
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end Part3Helpers

open scoped TensorProduct in
/-- Uniqueness of the left factor in `V ⊗ W ≃ V' ⊗ W'`. If `V` and `V'` are simple
`A`-modules and `e` is an `A`-equivariant equivalence (with `A` acting on the left factors)
and the right factor `W` is nontrivial, then `V ≅ V'` as `A`-modules. This is Schur's lemma:
a suitable contraction of `e` provides a nonzero, hence bijective, `A`-linear map `V → V'`. -/
theorem Etingof.tensor_left_factor_unique
    {k A V W V' W' : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
    [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V'] [FiniteDimensional k V']
    [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    [IsSimpleModule A V] [IsSimpleModule A V']
    (e : V ⊗[k] W ≃ₗ[k] V' ⊗[k] W')
    (hA : ∀ (a : A) (x : V ⊗[k] W),
        e (TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id x)
          = TensorProduct.map ((Algebra.lsmul k k V' : A →ₐ[k] _) a) LinearMap.id (e x)) :
    Nonempty (V ≃ₗ[A] V') := by
  classical
  haveI := IsSimpleModule.nontrivial A V
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  -- For each `ψ : W' → k`, the contraction is a genuine `A`-linear map `V → V'`.
  let T : (W' →ₗ[k] k) → (V →ₗ[A] V') := fun ψ =>
    { toFun := fun v =>
        (TensorProduct.rid k V') (TensorProduct.map LinearMap.id ψ (e (v ⊗ₜ[k] w₀)))
      map_add' := fun x y => by simp only [TensorProduct.add_tmul, map_add]
      map_smul' := fun a v => by
        simp only [RingHom.id_apply]
        have hsmul : (a • v) ⊗ₜ[k] w₀
            = TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id (v ⊗ₜ[k] w₀) := by
          rw [TensorProduct.map_tmul]; simp [Algebra.lsmul_coe]
        rw [hsmul, hA, rid_mapψ_lsmul] }
  -- Some `ψ` makes `T ψ` nonzero.
  have hex : ∃ ψ : W' →ₗ[k] k, T ψ ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
    have ht : e (v₁ ⊗ₜ[k] w₀) ≠ 0 :=
      fun hz => tmul_ne_zero hv₁ hw₀ (e.injective (hz.trans (map_zero e).symm))
    obtain ⟨φ, ψ, hφψ⟩ := exists_contraction_ne_zero ht
    apply hφψ
    have hTψ : (TensorProduct.rid k V')
        (TensorProduct.map LinearMap.id ψ (e (v₁ ⊗ₜ[k] w₀))) = 0 := by
      calc (TensorProduct.rid k V')
              (TensorProduct.map LinearMap.id ψ (e (v₁ ⊗ₜ[k] w₀)))
          = T ψ v₁ := rfl
        _ = (0 : V →ₗ[A] V') v₁ := by rw [h ψ]
        _ = 0 := rfl
    calc TensorProduct.lid k k (TensorProduct.map φ ψ (e (v₁ ⊗ₜ[k] w₀)))
        = φ ((TensorProduct.rid k V')
            (TensorProduct.map LinearMap.id ψ (e (v₁ ⊗ₜ[k] w₀)))) :=
          (lid_map_eq_apply_rid φ ψ _).symm
      _ = φ 0 := by rw [hTψ]
      _ = 0 := map_zero φ
  obtain ⟨ψ, hψ⟩ := hex
  exact ⟨LinearEquiv.ofBijective (T ψ) (LinearMap.bijective_of_ne_zero hψ)⟩

open scoped TensorProduct in
/-- The factor-swap equivalence `comm` intertwines `map f g` with `map g f`. -/
private theorem comm_map_apply {k M N M' N' : Type*} [CommSemiring k]
    [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]
    [AddCommMonoid M'] [Module k M'] [AddCommMonoid N'] [Module k N']
    (f : M →ₗ[k] M') (g : N →ₗ[k] N') (x : M ⊗[k] N) :
    (TensorProduct.comm k M' N') (TensorProduct.map f g x)
      = TensorProduct.map g f ((TensorProduct.comm k M N) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.map_tmul, TensorProduct.comm_tmul]
  | add p q hp hq => simp [map_add, hp, hq]

open scoped TensorProduct in
/-- Uniqueness in Etingof Theorem 3.10.2(ii): the factors `V` and `W` of an irreducible
representation `M ≅ V ⊗ W` of `A ⊗ B` are unique up to isomorphism. Concretely, any
`A`-`B`-equivariant equivalence `e : V ⊗ W ≃ V' ⊗ W'` between two factorizations into
simple modules forces `V ≅ V'` as `A`-modules and `W ≅ W'` as `B`-modules.

Together with `Etingof.tensor_product_irreducible_classification` (existence), this is the
full content of the book's "for **unique** `V` and `W`": two factorizations of the same `M`
yield such an `e` by composing the two equivalences. -/
theorem Etingof.tensor_product_irreducible_classification_unique
    {k A B V W V' W' : Type*} [Field k]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [Module B W] [IsScalarTower k B W] [FiniteDimensional k W]
    [AddCommGroup V'] [Module k V'] [Module A V'] [IsScalarTower k A V'] [FiniteDimensional k V']
    [AddCommGroup W'] [Module k W'] [Module B W'] [IsScalarTower k B W'] [FiniteDimensional k W']
    [IsSimpleModule A V] [IsSimpleModule A V'] [IsSimpleModule B W] [IsSimpleModule B W']
    (e : V ⊗[k] W ≃ₗ[k] V' ⊗[k] W')
    (hA : ∀ (a : A) (x : V ⊗[k] W),
        e (TensorProduct.map ((Algebra.lsmul k k V : A →ₐ[k] _) a) LinearMap.id x)
          = TensorProduct.map ((Algebra.lsmul k k V' : A →ₐ[k] _) a) LinearMap.id (e x))
    (hB : ∀ (b : B) (x : V ⊗[k] W),
        e (TensorProduct.map LinearMap.id ((Algebra.lsmul k k W : B →ₐ[k] _) b) x)
          = TensorProduct.map LinearMap.id ((Algebra.lsmul k k W' : B →ₐ[k] _) b) (e x)) :
    Nonempty (V ≃ₗ[A] V') ∧ Nonempty (W ≃ₗ[B] W') := by
  haveI := IsSimpleModule.nontrivial A V
  haveI := IsSimpleModule.nontrivial B W
  refine ⟨Etingof.tensor_left_factor_unique e hA, ?_⟩
  -- Swap the tensor factors: `ê : W ⊗ V ≃ W' ⊗ V'` is `B`-equivariant on the left.
  let ê : W ⊗[k] V ≃ₗ[k] W' ⊗[k] V' :=
    (TensorProduct.comm k W V).trans (e.trans (TensorProduct.comm k V' W'))
  refine Etingof.tensor_left_factor_unique (A := B) (V := W) (W := V) (V' := W') (W' := V') ê ?_
  intro b x
  change (TensorProduct.comm k V' W') (e ((TensorProduct.comm k W V)
        (TensorProduct.map ((Algebra.lsmul k k W : B →ₐ[k] _) b) LinearMap.id x)))
      = TensorProduct.map ((Algebra.lsmul k k W' : B →ₐ[k] _) b) LinearMap.id
          ((TensorProduct.comm k V' W') (e ((TensorProduct.comm k W V) x)))
  rw [comm_map_apply, hB, comm_map_apply]
