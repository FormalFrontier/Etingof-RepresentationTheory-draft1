import Mathlib
import EtingofRepresentationTheory.Chapter5.PolynomialGLBiAction
import EtingofRepresentationTheory.Chapter5.LocalizationGLRightAction

/-!
# The `GL_N × GL_N` bi-action on the coordinate ring `O = A[det⁻¹]`

`LocalizationGLRightAction.lean` extended the right-translation representation
`polyRightRep` from `A = k[Xᵢⱼ]` to the determinant localization
`O = A[det⁻¹] = Localization.Away (detPoly k N)`, giving `localRightRep`. This
file does the same for the **left** translation `polyLeftRep`
(`PolynomialGLBiAction.lean`), producing `localLeftRep`, and then combines the two
commuting one-sided actions into a single genuine **`GL_N × GL_N`-representation**
`localBiRep` on `O`.

`O` is Etingof's coordinate ring `R` of regular functions on `GL_N(k)`: every
regular function is a polynomial in the matrix entries `gᵢⱼ` divided by a power of
`det(g)`. The bi-action is left/right translation, `(g,h)·φ = L_g R_h φ`, the
`GL_N × GL_N`-structure whose Peter-Weyl decomposition is Theorem 5.23.2(ii).

## Construction

The left translation `lTransAlgHom (g : Matrix)` carries `detPoly` to
`det g · detPoly` (`lTransAlgHom_det`); since `det g` is a unit, it sends the
powers of `detPoly` to units of `O`, so `IsLocalization.liftAlgHom` extends it to
`localLeftAlgHom g : O →ₐ[k] O`. Multiplicativity is inherited from
`lTransAlgHom_mul`, giving `localLeftRep`. The two one-sided actions commute on
`O` (`localLeftAlgHom_comm_localRightAlgHom`, lifting
`lTransAlgHom_comp_rTransAlgHom` across the localization), so
`Representation.ofCommutingPair` packages them as `localBiRep`.
-/

namespace Etingof.LocalizationGLAction

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
open scoped Matrix

variable {k : Type*} [Field k] {N : ℕ}

/-! ## A representation of a product group from two commuting actions -/

/-- Two commuting representations of `G` and `H` on the **same** module `V`
assemble into a representation of `G × H`: `(g, h) ↦ ρ g ∘ σ h`. The commutation
hypothesis is exactly what makes this a monoid homomorphism. -/
noncomputable def _root_.Representation.ofCommutingPair
    {k G H V : Type*} [CommSemiring k] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (σ : Representation k H V)
    (hcomm : ∀ (g : G) (h : H), ρ g * σ h = σ h * ρ g) :
    Representation k (G × H) V where
  toFun gh := ρ gh.1 * σ gh.2
  map_one' := by simp
  map_mul' x y := by
    change ρ (x * y).1 * σ (x * y).2 = (ρ x.1 * σ x.2) * (ρ y.1 * σ y.2)
    -- (ρx₁ ρy₁)(σx₂ σy₂) = (ρx₁ σx₂)(ρy₁ σy₂); swap the middle ρy₁ σx₂.
    rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul,
      mul_assoc (ρ x.1) (ρ y.1), ← mul_assoc (ρ y.1) (σ x.2) (σ y.2),
      hcomm y.1 x.2, mul_assoc (σ x.2) (ρ y.1) (σ y.2),
      ← mul_assoc (ρ x.1) (σ x.2)]

@[simp] theorem _root_.Representation.ofCommutingPair_apply
    {k G H V : Type*} [CommSemiring k] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (σ : Representation k H V)
    (hcomm : ∀ (g : G) (h : H), ρ g * σ h = σ h * ρ g) (g : G) (h : H) (v : V) :
    Representation.ofCommutingPair ρ σ hcomm (g, h) v = ρ g (σ h v) :=
  rfl

/-! ## The left-translation action on the localization `O = A[det⁻¹]` -/

/-- For a matrix `M`, the `k`-algebra hom `A →ₐ[k] O` obtained by composing the
left translation `lTransAlgHom M` with the structure map `A → O`. -/
noncomputable def lTransToAway (M : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] Localization.Away (detPoly k N) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (detPoly k N))).comp (lTransAlgHom M)

@[simp] theorem lTransToAway_apply (M : Matrix (Fin N) (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    lTransToAway M a = algebraMap _ (Localization.Away (detPoly k N)) (lTransAlgHom M a) :=
  rfl

/-- Determinant semi-invariance phrased with `detPoly` (a restatement of
`lTransAlgHom_det`). -/
theorem lTransAlgHom_detPoly (M : Matrix (Fin N) (Fin N) k) :
    lTransAlgHom M (detPoly k N) = MvPolynomial.C M.det * detPoly k N :=
  lTransAlgHom_det M

/-- For `g ∈ GL_N`, the powers of `detPoly` map to units of `O` under
`lTransToAway (g : Matrix)`. -/
theorem isUnit_lTransToAway_detPoly_pow (g : Matrix.GeneralLinearGroup (Fin N) k)
    (y : Submonoid.powers (detPoly k N)) :
    IsUnit (lTransToAway (g : Matrix (Fin N) (Fin N) k) (y : MvPolynomial (Fin N × Fin N) k)) := by
  obtain ⟨n, hn⟩ := y.2
  rw [← hn]
  change IsUnit (lTransToAway (g : Matrix (Fin N) (Fin N) k) (detPoly k N ^ n))
  rw [lTransToAway_apply, map_pow, map_pow]
  refine IsUnit.pow n ?_
  rw [lTransAlgHom_detPoly, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hdet : IsUnit ((g : Matrix (Fin N) (Fin N) k).det) :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)
    exact (hdet.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)).map
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)))
  · exact IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away (detPoly k N)) (detPoly k N)

/-- The inverse-transpose of `g ∈ GL_N` as an element of `GL_N`: the matrix
`(g⁻¹)ᵀ`, with inverse `gᵀ`. -/
noncomputable def glInvTransposeFun (g : Matrix.GeneralLinearGroup (Fin N) k) :
    Matrix.GeneralLinearGroup (Fin N) k :=
  ⟨((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)ᵀ,
   ((g : Matrix (Fin N) (Fin N) k))ᵀ,
   by rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one],
   by rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one]⟩

@[simp] theorem glInvTransposeFun_coe (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ((glInvTransposeFun g : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)ᵀ :=
  rfl

/-- The inverse-transpose monoid hom `GL_N → GL_N`, `g ↦ (g⁻¹)ᵀ`. This is the
`GL_N`-automorphism that converts Etingof's left action `φ ↦ φ(g⁻¹ ·)` into the
transpose substitution that `lTransAlgHom` realizes: `lTransAlgHom M` implements
`Mᵀ`-multiplication, and we want `Mᵀ = g⁻¹`, i.e. `M = (g⁻¹)ᵀ`. -/
noncomputable def glInvTranspose :
    Matrix.GeneralLinearGroup (Fin N) k →* Matrix.GeneralLinearGroup (Fin N) k where
  toFun := glInvTransposeFun
  map_one' := by
    apply Units.ext
    rw [glInvTransposeFun_coe, inv_one, Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one]
  map_mul' g₁ g₂ := by
    apply Units.ext
    rw [Units.val_mul, glInvTransposeFun_coe, glInvTransposeFun_coe, glInvTransposeFun_coe,
      mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul]

@[simp] theorem glInvTranspose_coe (g : Matrix.GeneralLinearGroup (Fin N) k) :
    ((glInvTranspose g : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)
      = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)ᵀ :=
  rfl

/-- The left-translation `k`-algebra endomorphism of `O = A[det⁻¹]` attached to
`g ∈ GL_N`, implementing Etingof's action `φ ↦ φ(g⁻¹ ·)`: the localization
extension of `lTransAlgHom ((g⁻¹)ᵀ)`. Since `lTransAlgHom M` realizes the
substitution `X_{ij} ↦ (Mᵀ X)_{ij}`, taking `M = (g⁻¹)ᵀ` gives `X ↦ g⁻¹ X`. -/
noncomputable def localLeftAlgHom (g : Matrix.GeneralLinearGroup (Fin N) k) :
    Localization.Away (detPoly k N) →ₐ[k] Localization.Away (detPoly k N) :=
  IsLocalization.liftAlgHom
    (f := lTransToAway ((glInvTranspose g : Matrix.GeneralLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k))
    (isUnit_lTransToAway_detPoly_pow (glInvTranspose g))

/-- `localLeftAlgHom g` extends the inverse-transpose left translation on `A`: on
the image of `a ∈ A` it is `algebraMap (lTransAlgHom ((g⁻¹)ᵀ) a)`. -/
@[simp] theorem localLeftAlgHom_algebraMap (g : Matrix.GeneralLinearGroup (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    localLeftAlgHom g (algebraMap _ (Localization.Away (detPoly k N)) a)
      = algebraMap _ _ (lTransAlgHom
          ((glInvTranspose g : Matrix.GeneralLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) a) := by
  simp only [localLeftAlgHom, IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
  rfl

/-- `localLeftAlgHom 1 = id`. -/
theorem localLeftAlgHom_one :
    localLeftAlgHom (1 : Matrix.GeneralLinearGroup (Fin N) k)
      = AlgHom.id k (Localization.Away (detPoly k N)) := by
  apply IsLocalization.algHom_ext (R := k) (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (detPoly k N)) (B := Localization.Away (detPoly k N))
    (Submonoid.powers (detPoly k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change localLeftAlgHom (1 : Matrix.GeneralLinearGroup (Fin N) k)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
    = AlgHom.id k (Localization.Away (detPoly k N))
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
  rw [localLeftAlgHom_algebraMap, AlgHom.id_apply, map_one, Units.val_one, lTransAlgHom_one,
    AlgHom.id_apply]

/-- Multiplicativity: `localLeftAlgHom (g₁ g₂) = localLeftAlgHom g₁ ∘ localLeftAlgHom g₂`. -/
theorem localLeftAlgHom_mul (g₁ g₂ : Matrix.GeneralLinearGroup (Fin N) k) :
    localLeftAlgHom (g₁ * g₂)
      = (localLeftAlgHom g₁).comp (localLeftAlgHom g₂) := by
  apply IsLocalization.algHom_ext (R := k) (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (detPoly k N)) (B := Localization.Away (detPoly k N))
    (Submonoid.powers (detPoly k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change localLeftAlgHom (g₁ * g₂)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
    = (localLeftAlgHom g₁).comp (localLeftAlgHom g₂)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
  rw [localLeftAlgHom_algebraMap, AlgHom.comp_apply, localLeftAlgHom_algebraMap,
    localLeftAlgHom_algebraMap, map_mul, Units.val_mul, lTransAlgHom_mul, AlgHom.comp_apply]

/-- The **left-translation representation of `GL_N` on `O = A[det⁻¹]`**:
`g ↦ localLeftAlgHom g`. -/
noncomputable def localLeftRep (k : Type*) [Field k] (N : ℕ) :
    Representation k (Matrix.GeneralLinearGroup (Fin N) k)
      (Localization.Away (detPoly k N)) where
  toFun g := (localLeftAlgHom g).toLinearMap
  map_one' := by
    change (localLeftAlgHom (1 : Matrix.GeneralLinearGroup (Fin N) k)).toLinearMap = _
    rw [localLeftAlgHom_one]; rfl
  map_mul' g₁ g₂ := by
    change (localLeftAlgHom (g₁ * g₂)).toLinearMap = _
    rw [localLeftAlgHom_mul]; rfl

@[simp] theorem localLeftRep_apply (g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (detPoly k N)) :
    localLeftRep k N g x = localLeftAlgHom g x :=
  rfl

/-- **The structure map `A → O` is left-`GL_N`-equivariant**, where `A` carries
the inverse-transposed left translation `polyLeftRep (glInvTranspose g)` (so the
substitution is `X ↦ g⁻¹ X`, matching Etingof's localization action). -/
theorem localLeftRep_algebraMap (g : Matrix.GeneralLinearGroup (Fin N) k)
    (a : MvPolynomial (Fin N × Fin N) k) :
    localLeftRep k N g (algebraMap _ (Localization.Away (detPoly k N)) a)
      = algebraMap _ _ (polyLeftRep k N (glInvTranspose g) a) := by
  rw [polyLeftRep_apply]
  exact localLeftAlgHom_algebraMap g a

/-! ## The two one-sided actions commute -/

/-- **Left and right translations commute on `O = A[det⁻¹]`.** The two algebra
endomorphisms commute on the polynomial subring `A`
(`lTransAlgHom_comp_rTransAlgHom`); by the universal property of the localization
the commutation lifts to all of `O`. -/
theorem localLeftAlgHom_comp_localRightAlgHom
    (g h : Matrix.GeneralLinearGroup (Fin N) k) :
    (localLeftAlgHom g).comp (localRightAlgHom h)
      = (localRightAlgHom h).comp (localLeftAlgHom g) := by
  apply IsLocalization.algHom_ext (R := k) (A := MvPolynomial (Fin N × Fin N) k)
    (L := Localization.Away (detPoly k N)) (B := Localization.Away (detPoly k N))
    (Submonoid.powers (detPoly k N))
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  change (localLeftAlgHom g).comp (localRightAlgHom h)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
    = (localRightAlgHom h).comp (localLeftAlgHom g)
      (algebraMap (MvPolynomial (Fin N × Fin N) k) (Localization.Away (detPoly k N)) a)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, localRightAlgHom_algebraMap,
    localLeftAlgHom_algebraMap, localLeftAlgHom_algebraMap, localRightAlgHom_algebraMap]
  -- reduce to commutation on `A` and apply `lTransAlgHom_comp_rTransAlgHom`
  have hcomm := AlgHom.congr_fun (lTransAlgHom_comp_rTransAlgHom
    ((glInvTranspose g : Matrix.GeneralLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k)
    (h : Matrix (Fin N) (Fin N) k)) a
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at hcomm
  rw [hcomm]

/-- The left and right `GL_N`-actions on `O` commute as linear endomorphisms. -/
theorem localLeftRep_commute_localRightRep
    (g h : Matrix.GeneralLinearGroup (Fin N) k) :
    localLeftRep k N g * localRightRep k N h
      = localRightRep k N h * localLeftRep k N g := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, Module.End.mul_apply, localLeftRep_apply,
    localRightRep_apply, localRightRep_apply, localLeftRep_apply]
  exact AlgHom.congr_fun (localLeftAlgHom_comp_localRightAlgHom g h) x

/-! ## The `GL_N × GL_N` bi-representation -/

/-- **The `GL_N × GL_N` bi-action on the coordinate ring `O = A[det⁻¹]`.** For
`(g, h) ∈ GL_N × GL_N`, `(g, h)` acts by `L_g R_h` (left translation by `g`
composed with right translation by `h`). This is the genuine
`GL_N × GL_N`-representation on Etingof's coordinate ring `R` whose Peter-Weyl
decomposition is Theorem 5.23.2(ii). -/
noncomputable def localBiRep (k : Type*) [Field k] (N : ℕ) :
    Representation k
      (Matrix.GeneralLinearGroup (Fin N) k × Matrix.GeneralLinearGroup (Fin N) k)
      (Localization.Away (detPoly k N)) :=
  Representation.ofCommutingPair (localLeftRep k N) (localRightRep k N)
    localLeftRep_commute_localRightRep

@[simp] theorem localBiRep_apply (g h : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (detPoly k N)) :
    localBiRep k N (g, h) x = localLeftAlgHom g (localRightAlgHom h x) :=
  rfl

/-! ## Left-translation intertwining for `evalGLAway` -/

/-- Evaluating `lTransAlgHom M p` at `g` coincides with evaluating `p` at the
product matrix `Mᵀ · g`: the substitution `X_{ij} ↦ ∑_l M_{li} X_{lj}`
(`lTransAlgHom_X`) followed by `X ↦ g` gives `(Mᵀ·g)_{ij}`. This is the left
analogue of `eval_rTransAlgHom`. -/
lemma eval_lTransAlgHom (M g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2) (lTransAlgHom M p)
      = MvPolynomial.eval (fun ij : Fin N × Fin N => (Mᵀ * g) ij.1 ij.2) p := by
  classical
  suffices halgs :
      (MvPolynomial.aeval (fun ij : Fin N × Fin N => g ij.1 ij.2)).comp
          (lTransAlgHom M) =
        (MvPolynomial.aeval (fun ij : Fin N × Fin N => (Mᵀ * g) ij.1 ij.2) :
          MvPolynomial (Fin N × Fin N) k →ₐ[k] k) by
    have := AlgHom.congr_fun halgs p
    simpa [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using this
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  rw [AlgHom.comp_apply, lTransAlgHom_X, map_sum, MvPolynomial.aeval_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, MvPolynomial.aeval_X, smul_eq_mul, Matrix.transpose_apply]

/-- **Left-translation intertwining for `evalGLAway`.** Etingof's left translation
of the localization element `x ∈ O = A[det⁻¹]` by `g₀ ∈ GL_N`, evaluated at `g`,
is `x` evaluated at `g₀⁻¹ · g`: `evalGLAway (localLeftRep g₀ x) g = evalGLAway x (g₀⁻¹ · g)`.
This is the left analogue of `evalGLAway_localRightRep`. -/
lemma evalGLAway_localLeftRep (g₀ g : Matrix.GeneralLinearGroup (Fin N) k)
    (x : Localization.Away (detPoly k N)) :
    evalGLAway (localLeftRep k N g₀ x) g = evalGLAway x (g₀⁻¹ * g) := by
  -- both sides are ring homs `O →+* k` in `x`; check on `algebraMap A O`.
  have key : ∀ a : MvPolynomial (Fin N × Fin N) k,
      evalGLAway (localLeftRep k N g₀
          (algebraMap (MvPolynomial (Fin N × Fin N) k) _ a)) g
        = evalGLAway (algebraMap _ _ a) (g₀⁻¹ * g) := by
    intro a
    rw [localLeftRep_apply, localLeftAlgHom_algebraMap, evalGLAway_algebraMap,
      evalGLAway_algebraMap, evalGLHom_apply, evalGLHom_apply]
    show MvPolynomial.eval (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (lTransAlgHom
          ((glInvTranspose g₀ : Matrix.GeneralLinearGroup (Fin N) k) :
            Matrix (Fin N) (Fin N) k) a) = _
    rw [eval_lTransAlgHom]
    -- `((g₀⁻¹)ᵀ)ᵀ · g = g₀⁻¹ · g = ↑(g₀⁻¹ * g)`, definitionally.
    rfl
  -- package as ring homs and use the localization extension principle.
  let F : Localization.Away (detPoly k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) g).comp
      (evalGLAway.comp (localLeftAlgHom g₀).toRingHom)
  let G : Localization.Away (detPoly k N) →+* k :=
    (Pi.evalRingHom (fun _ : Matrix.GeneralLinearGroup (Fin N) k => k) (g₀⁻¹ * g)).comp evalGLAway
  have hFG : F = G := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (detPoly k N))
    apply RingHom.ext
    intro a
    simp only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom]
    rw [← localLeftRep_apply]
    exact key a
  have hx := RingHom.congr_fun hFG x
  simpa only [F, G, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, ← localLeftRep_apply] using hx

end Etingof.LocalizationGLAction
