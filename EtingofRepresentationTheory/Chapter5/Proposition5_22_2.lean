import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.GLRepAlgebraic
import EtingofRepresentationTheory.Chapter5.SchurWeylFormalCharacterIso
import EtingofRepresentationTheory.Chapter5.SchurPolyShift

/-!
# Proposition 5.22.2: Twisting by Determinant

`L_{λ + 1^N} ≅ L_λ ⊗ ∧^N V`, where `1^N = (1, 1, …, 1)`.

The top exterior power `∧^N V` is the one-dimensional determinant representation
of `GL_N(k)`. Tensoring by it shifts every part of the highest weight by 1.
This follows from the inclusion `L_λ ⊗ ∧^N V ⊂ V^{⊗(n+N)}` and the
uniqueness of the component with the given character.

## Mathlib correspondence

Uses the Schur module from `Theorem5_22_1`. The tensor product of `FDRep` objects
uses the monoidal category structure on `FDRep k G`.
-/

open CategoryTheory MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Etingof

variable (k : Type) [Field k] [IsAlgClosed k] [CharZero k]

noncomputable local instance (priority := high) proposition522SchurModuleAddCommGroup
    (N : ℕ) (lam : Fin N → ℕ) : AddCommGroup (SchurModuleSubmodule k N lam) :=
  { Module.addCommMonoidToAddCommGroup k with
    toAddCommMonoid := (SchurModuleSubmodule k N lam).addCommMonoid }

/-- The determinant representation of `GL_N(k)`: the one-dimensional representation
given by `g ↦ det(g)`. It is equivariantly isomorphic to the top exterior power
`∧^N(k^N)` (see `topExteriorPowerRep_iso_detRep`). -/
noncomputable def detRep (N : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
    Matrix.GeneralLinearGroup.det)

/-! ### The top exterior power representation `∧^N (kᴺ)`

Etingof's Proposition 5.22.2 features the honest top exterior power `∧^N V`.
Here we construct the standard `GL_N(k)`-action on `⋀^N (kᴺ)`, prove it is
equivariantly isomorphic to the one-dimensional determinant character `detRep`,
and use it to state Proposition 5.22.2 with the actual exterior-power object.
The key classical fact is that the functorial action of a matrix `A` on the
top exterior power scales the canonical top form by `det A`. -/

/-- The standard `GL_N(k)`-action on the top exterior power `⋀^N (kᴺ)`: a group
element `g` acts by the functorially induced map `exteriorPower.map` of `g`
regarded as a linear endomorphism of `kᴺ` (via `Matrix.mulVecLin`). This is the
honest `∧^N V` appearing in Etingof's Proposition 5.22.2. -/
def topExtPowerRep (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k) (⋀[k]^N (Fin N → k)) where
  toFun g := exteriorPower.map N (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) k))
  map_one' := by
    simp only [Units.val_one, Matrix.mulVecLin_one, exteriorPower.map_id]
    rfl
  map_mul' g h := by
    simp only [Units.val_mul, Matrix.mulVecLin_mul, exteriorPower.map_comp]
    rfl

/-- The top exterior power representation `∧^N (kᴺ)` as an object of `FDRep k GL_N(k)`. -/
noncomputable def topExteriorPowerRep (N : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  FDRep.of (topExtPowerRep k N)

omit [IsAlgClosed k] [CharZero k] in
/-- **Determinant scaling of the top form.** The functorial action `exteriorPower.map`
of a matrix `A` on `⋀^N (kᴺ)` scales the canonical determinant form
`φ := alternatingMapLinearEquiv (Pi.basisFun k (Fin N)).det` by `det A`:
`φ (map N (mulVecLin A) x) = det A • φ x`. -/
private lemma topForm_map_mulVecLin (N : ℕ) (A : Matrix (Fin N) (Fin N) k)
    (x : ⋀[k]^N (Fin N → k)) :
    exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det
        (exteriorPower.map N (Matrix.mulVecLin A) x) =
      A.det • exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det x := by
  set b := Pi.basisFun k (Fin N) with hb
  have hdetlin : LinearMap.det (Matrix.mulVecLin A) = A.det := by
    rw [show Matrix.mulVecLin A = Matrix.toLin' A from (Matrix.toLin'_apply' A).symm,
      LinearMap.det_toLin']
  have key : (exteriorPower.alternatingMapLinearEquiv (n := N) b.det) ∘ₗ
      exteriorPower.map N (Matrix.mulVecLin A) =
      A.det • (exteriorPower.alternatingMapLinearEquiv (n := N) b.det) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, LinearMap.smul_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [b.det_comp, hdetlin, smul_eq_mul]
  exact LinearMap.congr_fun key x

/-- The canonical linear isomorphism `⋀^N (kᴺ) ≅ k` given by the determinant top
form `(Pi.basisFun k (Fin N)).det`. It sends the wedge `e₁ ∧ … ∧ e_N` of the
standard basis to `1`. -/
noncomputable def topFormEquiv (N : ℕ) : (⋀[k]^N (Fin N → k)) ≃ₗ[k] k := by
  have hω : exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det
      (exteriorPower.ιMulti k N (⇑(Pi.basisFun k (Fin N)))) = 1 := by
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact (Pi.basisFun k (Fin N)).det_self
  have hsurj : Function.Surjective
      (exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det) := by
    intro c
    refine ⟨c • exteriorPower.ιMulti k N (⇑(Pi.basisFun k (Fin N))), ?_⟩
    rw [map_smul, hω, smul_eq_mul, mul_one]
  have hdim : Module.finrank k (⋀[k]^N (Fin N → k)) = Module.finrank k k := by
    rw [exteriorPower.finrank_eq, Module.finrank_fin_fun, Module.finrank_self, Nat.choose_self]
  exact LinearEquiv.ofBijective _
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj, hsurj⟩

omit [CharZero k] in
@[simp]
lemma topFormEquiv_apply (N : ℕ) (x : ⋀[k]^N (Fin N → k)) :
    topFormEquiv k N x =
      exteriorPower.alternatingMapLinearEquiv (n := N) (Pi.basisFun k (Fin N)).det x := rfl

omit [CharZero k] in
/-- **The top exterior power action is multiplication by the determinant.**
On the one-dimensional space `⋀^N (kᴺ)`, a group element `g ∈ GL_N(k)` acts by the
scalar `det g`: `∧^N g = det(g) • id`. -/
lemma topExtPowerRep_eq_det_smul (N : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    topExtPowerRep k N g = (↑(Matrix.GeneralLinearGroup.det g) : k) • LinearMap.id := by
  refine LinearMap.ext fun x => (topFormEquiv k N).injective ?_
  simp only [topFormEquiv_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, map_smul]
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact topForm_map_mulVecLin k N _ x

omit [CharZero k] in
/-- The determinant top form `topFormEquiv` intertwines the top exterior power action
`g ↦ ∧^N g` with the determinant character `g ↦ det(g) • ·`. -/
theorem topFormEquiv_comm_detRep (N : ℕ) (g : Matrix.GeneralLinearGroup (Fin N) k) :
    (topFormEquiv k N).toLinearMap ∘ₗ (topExtPowerRep k N g) =
      ((((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
        Matrix.GeneralLinearGroup.det) g) ∘ₗ (topFormEquiv k N).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  have hL : topFormEquiv k N (topExtPowerRep k N g x) =
      (g : Matrix (Fin N) (Fin N) k).det • topFormEquiv k N x := by
    rw [topFormEquiv_apply, topFormEquiv_apply]
    exact topForm_map_mulVecLin k N _ x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, hL]
  -- RHS is `Algebra.lsmul k k k ↑(det g) (topFormEquiv x) = ↑(det g) • topFormEquiv x`
  -- definitionally; convert and match scalars via `val_det_apply`.
  change (g : Matrix (Fin N) (Fin N) k).det • topFormEquiv k N x
    = (↑(Matrix.GeneralLinearGroup.det g) : k) • topFormEquiv k N x
  rw [Matrix.GeneralLinearGroup.val_det_apply]

/-- **The top exterior power representation is the determinant character.**
`∧^N (kᴺ) ≅ detRep k N` as `GL_N(k)`-representations. Both are one-dimensional and
`g` acts by the scalar `det g`; the intertwiner is the determinant top form
`topFormEquiv`. This is the identification asserted (previously unproved) in the
documentation of `detRep`. -/
noncomputable def topExteriorPowerRep_iso_detRep (N : ℕ) :
    topExteriorPowerRep k N ≅ detRep k N :=
  Action.mkIso (topFormEquiv k N).toFGModuleCatIso (fun g => by
    ext : 1
    exact topFormEquiv_comm_detRep k N g)

-- rc2: slower instance search; bump synthInstance budget for the `det • End` smul synthesis
set_option synthInstance.maxHeartbeats 80000 in
/-- The determinant-twisted Schur module representation: `g ↦ det(g) • schurModuleRep(g)`.
This is the representation on the same underlying vector space as `L_λ`, but with the
GL_N action twisted by the determinant character. -/
def detTwistedSchurModuleRep (N : ℕ) (lam : Fin N → ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (SchurModuleSubmodule k N lam) where
  toFun g := (Matrix.GeneralLinearGroup.det g : k) • schurModuleRep k N lam g
  map_one' := by simp [map_one]
  map_mul' g₁ g₂ := by
    have hdet : (Matrix.GeneralLinearGroup.det (g₁ * g₂) : k) =
      (Matrix.GeneralLinearGroup.det g₁ : k) * (Matrix.GeneralLinearGroup.det g₂ : k) := by
      simp [map_mul]
    have hmul : (schurModuleRep k N lam) (g₁ * g₂) = (schurModuleRep k N lam) g₁ *
      (schurModuleRep k N lam) g₂ := map_mul _ _ _
    ext v
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, hdet, hmul]
    rw [mul_smul]
    simp only [map_smul, Submodule.coe_smul_of_tower]

/-- The formal character of `L_{λ+(1,…,1)}` equals `(∏ Xᵢ) · char(L_λ)`.
This follows from Theorem 5.22.1 (Weyl character formula) and schurPoly_shift. -/
theorem formalCharacter_schurModule_shift (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    formalCharacter k N (SchurModule k N (fun i => lam i + 1)) =
      (∏ i : Fin N, MvPolynomial.X i) * formalCharacter k N (SchurModule k N lam) := by
  have hlam' : Antitone (fun i => lam i + 1) := fun i j hij => Nat.add_le_add_right (hlam hij) 1
  rw [Theorem5_22_1 k N _ hlam', Theorem5_22_1 k N lam hlam, schurPoly_shift]

omit [IsAlgClosed k] in
/-- The determinant of `diagUnit k N i t` is `t`. -/
private lemma det_diagUnit (N : ℕ) (i : Fin N) (t : kˣ) :
    Matrix.GeneralLinearGroup.det (diagUnit k N i t) = t := by
  ext
  change Matrix.det (diagUnit k N i t).val = (t : k)
  simp only [diagUnit, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i),
    Pi.one_apply]
  simp [Finset.prod_eq_one (fun j _ => rfl)]

omit [IsAlgClosed k] in
private lemma det_diagUnit_val (N : ℕ) (i : Fin N) (t : kˣ) :
    (Matrix.GeneralLinearGroup.det (diagUnit k N i t) : k) = (t : k) :=
  congr_arg Units.val (det_diagUnit k N i t)


-- The initial `simp only [glWeightSpace, ...]` unfold is expensive.
-- rc2: slower instance search; bump synthInstance budget for the `t • End` smul synthesis
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- The weight space of the det-twisted module at weight `μ + 1` equals
the weight space of the original Schur module at weight `μ`. -/
lemma glWeightSpace_detTwist_shift (N : ℕ) (lam : Fin N → ℕ) (μ : Fin N → ℕ) :
    glWeightSpace k N (FDRep.of (detTwistedSchurModuleRep k N lam)) (fun j => μ j + 1) =
      glWeightSpace k N (SchurModule k N lam) μ := by
  -- Unfold definitions to iInf over kernels
  simp only [glWeightSpace, SchurModule, FDRep.of_ρ']
  -- detTwisted(g) = t • orig(g), so the linear maps factor:
  -- detTwisted(g) - t^(μ+1)•id = t•(orig(g) - t^μ•id)
  -- Hence ker(detTwisted(g) - t^(μ+1)•id) = ker(orig(g) - t^μ•id)
  apply iInf_congr; intro i; apply iInf_congr; intro t
  have hdt : (detTwistedSchurModuleRep k N lam (diagUnit k N i t)) =
      (t : k) • (schurModuleRep k N lam (diagUnit k N i t)) := by
    change (Matrix.GeneralLinearGroup.det (diagUnit k N i t) : k) •
      (schurModuleRep k N lam) (diagUnit k N i t) = _
    rw [det_diagUnit_val]
  have factored : (detTwistedSchurModuleRep k N lam (diagUnit k N i t)) -
      ((↑t : k) ^ (μ i + 1)) • LinearMap.id =
    (↑t : k) • ((schurModuleRep k N lam (diagUnit k N i t)) -
      ((↑t : k) ^ μ i) • LinearMap.id) := by
    rw [hdt, smul_sub, pow_succ, mul_comm, mul_smul]
  calc LinearMap.ker ((detTwistedSchurModuleRep k N lam (diagUnit k N i t)) -
        ((↑t : k) ^ (μ i + 1)) • LinearMap.id)
      = LinearMap.ker ((↑t : k) • ((schurModuleRep k N lam (diagUnit k N i t)) -
          ((↑t : k) ^ μ i) • LinearMap.id)) := congr_arg LinearMap.ker factored
    _ = LinearMap.ker ((schurModuleRep k N lam (diagUnit k N i t)) -
          ((↑t : k) ^ μ i) • LinearMap.id) := LinearMap.ker_smul _ _ (Units.ne_zero t)

/-- The formal character of the det-twisted Schur module equals that of the shifted
Schur module `L_{λ+(1,…,1)}`. Both equal `(∏ Xᵢ) · char(L_λ)`. -/
private lemma finrank_submodule_congr {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {S₁ S₂ : Submodule R M} (h : S₁ = S₂) :
    Module.finrank R S₁ = Module.finrank R S₂ := by subst h; rfl

/-- The standard tensor basis for `(k^N)^{⊗n}`, indexed by `Fin n → Fin N`. -/
private noncomputable abbrev tBasis (N n : ℕ) :=
  (_root_.Basis.piTensorProduct (R := k) (fun _ : Fin n => Pi.basisFun k (Fin N)))

omit [IsAlgClosed k] in
/-- `diagUnit(i, t)` acts on the tensor basis by scalar `t^(count of i in f)`. -/
private lemma glTensorRep_diagUnit_tBasis (N n : ℕ) (i : Fin N) (t : kˣ)
    (f : Fin n → Fin N) :
    (glTensorRep k N n (diagUnit k N i t)) (tBasis (k := k) N n f) =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
        tBasis (k := k) N n f := by
  change PiTensorProduct.map (fun _ => Matrix.mulVecLin (diagUnit k N i t).val)
      (tBasis (k := k) N n f) =
    ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) •
      tBasis (k := k) N n f
  simp only [tBasis, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod]
  -- Matrix.mulVecLin(diagUnit) on basis vector = scalar • basis vector
  have haction : ∀ (m : Fin n),
      Matrix.mulVecLin (R := k) (diagUnit k N i t).val (Pi.basisFun k (Fin N) (f m)) =
        (Function.update (1 : Fin N → k) i (t : k)) (f m) •
          Pi.basisFun k (Fin N) (f m) := by
    intro m
    simp only [diagUnit, Matrix.mulVecLin_apply, Pi.basisFun_apply]
    rw [Matrix.mulVec_single]
    ext x
    simp only [Pi.smul_apply, smul_eq_mul,
      Function.update_apply, Pi.single_apply, Pi.one_apply]
    by_cases hm : f m = i <;> by_cases hx : x = f m <;> simp_all
  simp_rw [haction]
  rw [(PiTensorProduct.tprod k).map_smul_univ
    (fun j => (Function.update (1 : Fin N → k) i (t : k)) (f j))
    (fun j => Pi.basisFun k (Fin N) (f j))]
  congr 1
  simp only [Function.update_apply, Pi.one_apply]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

omit [IsAlgClosed k] in
/-- The f-th basis coordinate of `glTensorRep(diagUnit(i,t))` applied to `v` equals
`t^(count f i) * (f-th coordinate of v)`. Local copy specialised to `tBasis`; the
`tensorStdBasis`-version is exposed publicly in `Theorem5_22_1.lean`. -/
private lemma repr_glTensorRep_diagUnit_local (N n : ℕ) (i : Fin N) (t : kˣ)
    (v : TensorPower k (Fin N → k) n) (f : Fin n → Fin N) :
    (tBasis (k := k) N n).repr ((glTensorRep k N n (diagUnit k N i t)) v) f =
      ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card) *
        (tBasis (k := k) N n).repr v f := by
  set b := tBasis (k := k) N n
  set c := ((t : k) ^ (Finset.univ.filter (fun j => f j = i)).card)
  -- Both sides are linear in v; reduce to basis elements via LinearMap equality
  have h_eq : (Finsupp.lapply f).comp (b.repr.toLinearMap.comp
      (glTensorRep k N n (diagUnit k N i t))) =
      c • ((Finsupp.lapply f).comp b.repr.toLinearMap) := by
    apply b.ext; intro g
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.smul_apply,
      smul_eq_mul, Finsupp.lapply_apply]
    rw [glTensorRep_diagUnit_tBasis, map_smul, Finsupp.smul_apply, smul_eq_mul,
      b.repr_self_apply]
    by_cases hgf : g = f <;> simp [hgf, c]
  exact LinearMap.congr_fun h_eq v

-- v4.30: synthesizing `Module.Free k (glWeightSpace …)` is slower; raise the limit.
set_option synthInstance.maxHeartbeats 80000 in
private theorem formalCharacter_detTwist_eq_shift (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) :
    formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      formalCharacter k N (SchurModule k N (fun i => lam i + 1)) := by
  rw [formalCharacter_schurModule_shift k N lam hlam]
  exact formalCharacter_shift_of_weightSpace_finrank k N _ _
    (fun ν => finrank_submodule_congr (glWeightSpace_detTwist_shift k N lam ν))
    (fun μ hμ => by
      -- The det-twisted Schur module has no weight spaces at zero-component weights.
      obtain ⟨i₀, hi₀⟩ := hμ
      suffices h : glWeightSpace k N (FDRep.of (detTwistedSchurModuleRep k N lam)) μ = ⊥ by
        simp [h]
      rw [Submodule.eq_bot_iff]
      intro v hv
      simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv
      -- For all t: ρ(diagUnit(i₀, t)) v = t^(μ i₀) • v = v  (since μ i₀ = 0)
      have hv_fix : ∀ t : kˣ,
          (FDRep.of (detTwistedSchurModuleRep k N lam)).ρ (diagUnit k N i₀ t) v = v := by
        intro t; have := hv i₀ t; rw [hi₀, pow_zero, one_smul] at this
        exact eq_of_sub_eq_zero this
      -- v is in SchurModuleSubmodule, a subtype of the tensor power
      -- Show (v : TensorPower) = 0 using the tensor basis diagonal action
      set n := ∑ i, lam i
      set b := tBasis (k := k) N n
      -- Extract the underlying tensor power element
      set vt : TensorPower k (Fin N → k) n :=
        (v : SchurModuleSubmodule k N lam).val with hvt_def
      -- It suffices to show all basis coordinates of v (in the tensor power) are zero
      suffices hv_val : vt = 0 by
        exact SetCoe.ext hv_val
      rw [← b.repr.map_eq_zero_iff]
      ext f
      simp only [Finsupp.zero_apply]
      by_contra hcf
      -- The f-th basis coefficient is nonzero; derive contradiction
      set m := (Finset.univ.filter (fun j => f j = i₀)).card
      -- Pick t₀ with t₀^(m+1) ≠ 1 (exists since k is algebraically closed, hence infinite)
      obtain ⟨t₀, ht₀⟩ := exists_unit_pow_ne_one k (m + 1) (by omega)
      -- From weight space condition at (i₀, t₀):
      -- detTwistedRep(g) v = det(g) • schurModuleRep(g) v
      -- On the tensor power level: t₀ • glTensorRep(diagUnit(i₀, t₀)) vt = vt
      have hfix_val : (t₀ : k) • (glTensorRep k N n (diagUnit k N i₀ t₀)) vt = vt := by
        have h := congr_arg Subtype.val (hv_fix t₀)
        -- h : ↑(ρ(g) v) = ↑v at the FDRep level
        -- Unfold through: FDRep.of_ρ' → detTwistedSchurModuleRep → smul + restrict → glTensorRep
        simp only [FDRep.of_ρ'] at h
        -- The coercions (smul_apply, restrict_coe_apply, coe_smul) are all rfl,
        -- so h is definitionally: det(g) • glTensorRep(g) vt = vt
        have h2 : (Matrix.GeneralLinearGroup.det (diagUnit k N i₀ t₀) : k) •
            (glTensorRep k N n (diagUnit k N i₀ t₀)) vt = vt := h
        rw [det_diagUnit_val] at h2
        exact h2
      -- Extract f-th basis coordinate: t₀^(m+1) * c_f = c_f
      have hcoord : (t₀ : k) ^ (m + 1) * b.repr vt f = b.repr vt f := by
        have h1 := congr_arg (fun w => b.repr w f) hfix_val
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
        rw [repr_glTensorRep_diagUnit_local, ← mul_assoc, ← pow_succ'] at h1
        exact h1
      -- (t₀^(m+1) - 1) * c_f = 0, contradicting both ≠ 0
      have h_zero : ((t₀ : k) ^ (m + 1) - 1) * b.repr vt f = 0 := by
        rw [sub_mul, one_mul, hcoord, sub_self]
      exact (mul_eq_zero.mp h_zero).elim (sub_ne_zero.mpr ht₀) hcf)

/-! ### Weight decomposition for Schur modules

The weight spaces of a Schur module form a direct internal decomposition.
This is used to show `finrank(L_λ) = ∑_μ finrank(L_λ)_μ = eval₁(schurPoly)`,
which gives the dimension equality `finrank(L_λ) = finrank(L_{λ+(1,...,1)})`.

The Schur-module weight-saturation `glWeightSpace_schurModule_iSup_eq_top` lives upstream in
`SchurWeylFormalCharacterIso` (it is the equivariant image of the tensor power), and is used
unqualified below. -/

/-- Weight spaces for distinct weights are disjoint: if `μ ≠ ν`, then
`glWeightSpace(L, μ) ⊓ glWeightSpace(L, ν) = ⊥`. -/
private theorem glWeightSpace_disjoint (N : ℕ)
    (M : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    {μ ν : Fin N → ℕ} (hne : μ ≠ ν) :
    Disjoint (glWeightSpace k N M μ) (glWeightSpace k N M ν) := by
  rw [Function.ne_iff] at hne; obtain ⟨i₀, hi₀⟩ := hne
  rw [Submodule.disjoint_def]
  intro v hv_μ hv_ν
  simp only [glWeightSpace, Submodule.mem_iInf, LinearMap.mem_ker] at hv_μ hv_ν
  obtain ⟨t₀, ht₀⟩ := exists_unit_pow_ne k hi₀
  have h1 : M.ρ (diagUnit k N i₀ t₀) v = ((t₀ : k) ^ μ i₀) • v :=
    sub_eq_zero.mp (hv_μ i₀ t₀)
  have h2 : M.ρ (diagUnit k N i₀ t₀) v = ((t₀ : k) ^ ν i₀) • v :=
    sub_eq_zero.mp (hv_ν i₀ t₀)
  have h3 : (((t₀ : k) ^ μ i₀) - ((t₀ : k) ^ ν i₀)) • v = 0 := by
    rw [sub_smul]; exact sub_eq_zero.mpr (h1.symm.trans h2)
  rw [smul_eq_zero, sub_eq_zero] at h3
  exact h3.resolve_left ht₀

/-- Key isomorphism: the Schur module `L_{λ+(1,…,1)}` is isomorphic (as a GL_N-representation)
to the determinant-twisted Schur module `det ⊗ L_λ`.

Mathematically: `L_λ ⊗ ∧^N V ⊂ V^{⊗n} ⊗ ∧^N V ⊂ V^{⊗(n+N)}`, and the unique
component of `V^{⊗(n+N)}` with the same character as `L_λ ⊗ ∧^N V` is `L_{λ+(1,…,1)}`.
This is the core mathematical content of Proposition 5.22.2. -/
theorem schurModule_shift_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (FDRep.of (schurModuleRep k N (fun i => lam i + 1)) ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  have hlam' : Antitone (fun i => lam i + 1) :=
    fun i j hij => Nat.add_le_add_right (hlam hij) 1
  -- The det-twisted Schur module has the same formal character as the shifted Schur module
  have h_char : formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      schurPoly N (fun i => lam i + 1) := by
    rw [formalCharacter_detTwist_eq_shift k N lam hlam,
        Theorem5_22_1 k N _ hlam']
  -- The det-twisted rep has the same dimension as the shifted Schur module.
  -- Both are polynomial GL_N reps (ℕ-valued weight spaces span everything),
  -- so their dimensions equal the total mass of the Schur polynomial.
  -- Since S_{λ+(1,...,1)} = (∏ Xᵢ) · S_λ and ∏ Xᵢ preserves total mass,
  -- dim L_λ = dim L_{λ+(1,...,1)}.
  -- The det-twisted rep is polynomial: its ℕ-valued weight spaces span everything. Its
  -- weight spaces at (μ+1) match the SchurModule's at μ (`glWeightSpace_detTwist_shift`),
  -- and the SchurModule is polynomial. (Hoisted out so it is in scope as `h_span` below.)
  have h₁_top : ⨆ (μ : Fin N →₀ ℕ),
      glWeightSpace k N (FDRep.of (detTwistedSchurModuleRep k N lam))
        (fun i => μ i) = ⊤ := by
    rw [eq_top_iff, ← glWeightSpace_schurModule_iSup_eq_top k N lam]
    apply iSup_le
    intro μ
    -- Map μ to its shift (i ↦ μ i + 1) as a Fin N →₀ ℕ
    set μ_shift : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => μ i + 1) with hμs
    refine le_trans ?_ (le_iSup _ μ_shift)
    -- glWeightSpace_detTwist_shift gives equality (M₁ at μ+1) = (SchurModule at μ)
    have h_shift := glWeightSpace_detTwist_shift k N lam (fun i => μ i)
    have h_apply : (fun i => μ_shift i) = (fun i => μ i + 1) := by
      ext i; simp [μ_shift]
    rw [h_apply, h_shift]
  -- The det-twisted Schur module representation is algebraic (assembled from the general
  -- algebraicity infrastructure in `GLRepAlgebraic`; the concrete packaging is
  -- `detTwistedSchurModuleRep_isAlgebraic`, which lives downstream and so is inlined here).
  have halg : Etingof.IsAlgebraicCoefficientFamily N
      (FDRep.of (detTwistedSchurModuleRep k N lam)).ρ := by
    rw [FDRep.of_ρ']
    exact ((Etingof.glTensorRep_isAlgebraic k N (∑ i, lam i)).restrict
      (SchurModuleSubmodule k N lam)
      (fun g v hv => glTensorRep_mem_range k N lam g v hv)).detTwist
  have h_dim : Module.finrank k (FDRep.of (detTwistedSchurModuleRep k N lam)) =
      Module.finrank k (SchurModule k N (fun i => lam i + 1)) := by
    -- The SchurModule for λ+1 is polynomial (ℕ-valued weight spaces span).
    have h₂_top : ⨆ (μ : Fin N →₀ ℕ),
        glWeightSpace k N (SchurModule k N (fun i => lam i + 1)) (fun i => μ i) = ⊤ :=
      glWeightSpace_schurModule_iSup_eq_top k N (fun i => lam i + 1)
    -- Formal characters agree (the det-twist shifts the character by the product of Xᵢ)
    have h_char_eq : formalCharacter k N (FDRep.of (detTwistedSchurModuleRep k N lam)) =
        formalCharacter k N (SchurModule k N (fun i => lam i + 1)) :=
      formalCharacter_detTwist_eq_shift k N lam hlam
    exact finrank_eq_of_formalCharacter_eq k N _ _ h₁_top h₂_top h_char_eq
  -- By iso_of_formalCharacter_eq_schurPoly, the det-twisted rep ≅ SchurModule k N (λ+1)
  obtain ⟨iso⟩ := iso_of_formalCharacter_eq_schurPoly k N (fun i => lam i + 1) hlam'
    _ halg h₁_top h_char h_dim
  exact ⟨iso.symm⟩

omit [IsAlgClosed k] [CharZero k] in
/-- The `TensorProduct.rid` intertwines the tensor action `rep(g) ⊗ det(g)·id` with
the determinant-twisted action `det(g) · rep(g)`. -/
theorem tensorRid_comm_detTwist (N : ℕ) (lam : Fin N → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    (TensorProduct.rid k (SchurModuleSubmodule k N lam)).toLinearMap ∘ₗ
      TensorProduct.map (schurModuleRep k N lam g)
        (((Algebra.lsmul k k k).toMonoidHom.comp (Units.coeHom k)).comp
          Matrix.GeneralLinearGroup.det g) =
    (detTwistedSchurModuleRep k N lam g) ∘ₗ
      (TensorProduct.rid k (SchurModuleSubmodule k N lam)).toLinearMap := by
  apply TensorProduct.ext'
  intro v c
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_toLinearMap, TensorProduct.rid_tmul, detTwistedSchurModuleRep]
  -- LHS: (det(g)·c) • rep(g) v   RHS: det(g) • rep(g) (c • v)
  -- LHS: (↑(lsmul).toRingHom ↑(det g)) c • rep(g) v  = (↑(det g) * c) • rep(g) v
  -- RHS: det(g) • rep(g) (c • v) = det(g) • c • rep(g) v
  change ((↑(Matrix.GeneralLinearGroup.det g) : k) * c) • ((schurModuleRep k N lam) g) v =
    (↑(Matrix.GeneralLinearGroup.det g) : k) • ((schurModuleRep k N lam) g) (c • v)
  rw [map_smul, mul_smul, smul_comm]

/-- The FDRep tensor product `L_λ ⊗ det` is isomorphic to the determinant-twisted
representation. For any 1-dimensional representation `χ`, `M ⊗ χ` is isomorphic
to `M` with the action twisted by `χ`. -/
theorem schurModule_tensor_det_iso_detTwist (N : ℕ) (lam : Fin N → ℕ) :
    Nonempty (SchurModule k N lam ⊗ detRep k N ≅
      FDRep.of (detTwistedSchurModuleRep k N lam)) := by
  -- The underlying linear iso is TensorProduct.rid: M ⊗ k ≅ M
  refine ⟨Action.mkIso
    ((TensorProduct.rid k (SchurModuleSubmodule k N lam)).toFGModuleCatIso) (fun g => ?_)⟩
  ext : 1
  exact tensorRid_comm_detTwist k N lam g

/-- **Determinant twist** (determinant-character model): `L_{λ+(1,…,1)} ≅ L_λ ⊗ detRep`
as `GL_N(k)`-representations, where `detRep` is the one-dimensional determinant character.
This is the implementation core of Proposition 5.22.2; the public statement
`Proposition5_22_2` below replaces `detRep` with the honest top exterior power `∧^N V`
via `topExteriorPowerRep_iso_detRep`.
(Etingof Proposition 5.22.2) -/
theorem Proposition5_22_2_detRep
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (SchurModule k N (fun i => lam i + 1) ≅
      SchurModule k N lam ⊗ detRep k N) := by
  -- Decompose into two steps:
  -- (1) L_{λ+1^N} ≅ det-twisted L_λ  (character argument)
  -- (2) det-twisted L_λ ≅ L_λ ⊗ det  (categorical tensor/twist equivalence)
  obtain ⟨iso₁⟩ := schurModule_shift_iso_detTwist k N lam hlam
  obtain ⟨iso₂⟩ := schurModule_tensor_det_iso_detTwist k N lam
  exact ⟨iso₁ ≪≫ iso₂.symm⟩

/-- **Determinant twist**: `L_{λ+(1,…,1)} ≅ L_λ ⊗ ∧^N V` as `GL_N(k)`-representations,
where `∧^N V = topExteriorPowerRep k N` is the honest top exterior power of `V = kᴺ`.

Tensoring with the top exterior power shifts every part of the highest weight by 1.
This is Etingof's Proposition 5.22.2 with the actual `∧^N V` object (rather than the
determinant-character model `detRep`): the two are equivariantly identified in
`topExteriorPowerRep_iso_detRep`.
(Etingof Proposition 5.22.2) -/
theorem Proposition5_22_2
    (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam) :
    Nonempty (SchurModule k N (fun i => lam i + 1) ≅
      SchurModule k N lam ⊗ topExteriorPowerRep k N) := by
  obtain ⟨iso⟩ := Proposition5_22_2_detRep k N lam hlam
  -- Replace `detRep` by the top exterior power in the tensor factor.
  exact ⟨iso ≪≫ (whiskerLeftIso (SchurModule k N lam)
    (topExteriorPowerRep_iso_detRep k N)).symm⟩

end Etingof
