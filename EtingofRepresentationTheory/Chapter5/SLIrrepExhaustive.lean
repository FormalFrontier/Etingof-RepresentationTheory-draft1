import EtingofRepresentationTheory.Chapter5.Remark5_23_3
import EtingofRepresentationTheory.Chapter5.AlgIrrepGLExhaustive

/-!
# Exhaustiveness bridge for algebraic `SL_N` representations

This file supplies the formal bridge from the landed `GL_N` highest-weight classification to
`SL_N`.  It defines intrinsic regularity of matrix coefficients on `SL_N`, proves that restriction
of an algebraic `GL_N` representation is algebraic, and classifies every simple `SL_N`
representation equipped with an algebraic `GL_N` extension.

The remaining genuinely `SL_N`-specific input for unconditional exhaustiveness is precisely that
every intrinsically algebraic simple `SL_N` representation admits such an *algebraic* extension.
The abstract group-representation extension is constructed below; its regularity is isolated as
the sole remaining coordinate-ring normalization step.
-/

noncomputable section

namespace Etingof

/-- Matrix-coefficient regularity for a family of endomorphisms indexed by `SL_n(k)`.  The
coefficients are restrictions of polynomials in the standard `GL_n` coordinate variables; on
`SL_n`, the inverse-determinant coordinate evaluates to `1`. -/
def IsAlgebraicSLCoefficientFamily
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Matrix.SpecialLinearGroup (Fin n) k → Y →ₗ[k] Y) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) k Y)
    (P : Fin m → Fin m → MvPolynomial (GLCoordVars n) k),
    ∀ (g : Matrix.SpecialLinearGroup (Fin n) k) (a c : Fin m),
      b.repr (σ g (b c)) a = evalAtGL (Matrix.SpecialLinearGroup.toGL g) (P a c)

/-- A bundled `SL_n` representation is algebraic when its coefficient family is algebraic. -/
def IsAlgebraicSLRepresentation
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  IsAlgebraicSLCoefficientFamily n σ

/-- Restricting an algebraic `GL_n` coefficient family to `SL_n` preserves algebraicity. -/
theorem IsAlgebraicCoefficientFamily.slRestrict
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y}
    (hρ : IsAlgebraicCoefficientFamily n ρ) :
    IsAlgebraicSLCoefficientFamily n (slRestrict ρ) := by
  obtain ⟨m, b, P, hP⟩ := hρ
  exact ⟨m, b, P, fun g a c => hP (Matrix.SpecialLinearGroup.toGL g) a c⟩

/-- An `SL_n` representation has an algebraic `GL_n` extension if its action is obtained by
restriction from an algebraic `GL_n` representation on the same vector space. -/
def HasAlgebraicGLExtension
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y,
    IsAlgebraicCoefficientFamily n ρ ∧ slRestrict ρ = σ

/-- An abstract `GL_n` extension, without yet asserting regularity of its matrix coefficients. -/
def HasGLExtension
    {k : Type*} [Field k] (n : ℕ)
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) : Prop :=
  ∃ ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y, slRestrict ρ = σ

/-- A central group element acts by a scalar in a finite-dimensional simple representation over
an algebraically closed field.  This is the form of Schur's lemma used for the scalar roots of
unity in `SL_n`. -/
private theorem exists_scalar_action_of_central
    {k G Y : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (σ : Representation k G Y)
    [hsimp : IsSimpleModule (MonoidAlgebra k G) σ.asModule]
    (z : G) (hz : ∀ g : G, z * g = g * z) :
    ∃ c : k, σ z = c • LinearMap.id := by
  letI : Nontrivial Y := IsSimpleModule.nontrivial (MonoidAlgebra k G) σ.asModule
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (σ z)
  let S : Subrepresentation σ :=
    { toSubmodule := Module.End.eigenspace (σ z) c
      apply_mem_toSubmodule := fun g v hv => by
        rw [Module.End.mem_eigenspace_iff] at hv ⊢
        calc
          σ z (σ g v) = σ (z * g) v := by rw [map_mul, Module.End.mul_apply]
          _ = σ (g * z) v := by rw [hz]
          _ = σ g (σ z v) := by rw [map_mul, Module.End.mul_apply]
          _ = σ g (c • v) := by rw [hv]
          _ = c • σ g v := by rw [map_smul] }
  have hS_ne : S ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
    intro hbot
    have : v ∈ (⊥ : Subrepresentation σ) := hbot ▸ hv
    change v ∈ (⊥ : Submodule k Y) at this
    exact hv0 ((Submodule.mem_bot k).mp this)
  have hirr : Representation.IsIrreducible σ :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).2 hsimp
  have hS : S = ⊤ := (hirr.eq_bot_or_eq_top S).resolve_left hS_ne
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv : v ∈ S := by rw [hS]; trivial
  change v ∈ Module.End.eigenspace (σ z) c at hv
  rw [Module.End.mem_eigenspace_iff] at hv
  simpa only [LinearMap.smul_apply, LinearMap.id_coe, id_eq] using hv

/-- Scalar matrices, bundled as a homomorphism.  `Remark5_23_3.scalarGL` is deliberately
defined elementwise there, so we package the elementary multiplicativity needed for descent. -/
private def scalarGLHom {k : Type*} [Field k] (n : ℕ) :
    kˣ →* Matrix.GeneralLinearGroup (Fin n) k where
  toFun := scalarGL k n
  map_one' := by
    apply Units.ext
    simp [scalarGL]
  map_mul' s t := by
    apply Units.ext
    simp [scalarGL, smul_smul, mul_comm]

@[simp] private theorem scalarGLHom_apply
    {k : Type*} [Field k] {n : ℕ} (s : kˣ) :
    scalarGLHom n s = scalarGL k n s := rfl

private theorem scalarGL_comm
    {k : Type*} [Field k] {n : ℕ} (s : kˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    scalarGL k n s * g = g * scalarGL k n s := by
  apply Units.ext
  change ((s : k) • 1) * (g : Matrix (Fin n) (Fin n) k) =
    (g : Matrix (Fin n) (Fin n) k) * ((s : k) • 1)
  simp

/-- The central-product map `kˣ × SL_n(k) → GL_n(k)`. -/
private def scalarSpecialMul {k : Type*} [Field k] (n : ℕ) :
    kˣ × Matrix.SpecialLinearGroup (Fin n) k →*
      Matrix.GeneralLinearGroup (Fin n) k where
  toFun p := scalarGL k n p.1 * Matrix.SpecialLinearGroup.toGL p.2
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    change scalarGL k n 1 * 1 = 1
    rw [show scalarGL k n 1 = 1 by exact (scalarGLHom n).map_one, one_mul]
  map_mul' p q := by
    change scalarGL k n (p.1 * q.1) * Matrix.SpecialLinearGroup.toGL (p.2 * q.2) =
      (scalarGL k n p.1 * Matrix.SpecialLinearGroup.toGL p.2) *
        (scalarGL k n q.1 * Matrix.SpecialLinearGroup.toGL q.2)
    rw [show scalarGL k n (p.1 * q.1) = scalarGL k n p.1 * scalarGL k n q.1 by
      exact (scalarGLHom n).map_mul p.1 q.1]
    rw [map_mul]
    calc
      (scalarGL k n p.1 * scalarGL k n q.1) *
          (Matrix.SpecialLinearGroup.toGL p.2 * Matrix.SpecialLinearGroup.toGL q.2) =
        scalarGL k n p.1 *
          (scalarGL k n q.1 * Matrix.SpecialLinearGroup.toGL p.2) *
            Matrix.SpecialLinearGroup.toGL q.2 := by simp only [mul_assoc]
      _ = scalarGL k n p.1 *
          (Matrix.SpecialLinearGroup.toGL p.2 * scalarGL k n q.1) *
            Matrix.SpecialLinearGroup.toGL q.2 := by
        rw [scalarGL_comm q.1 (Matrix.SpecialLinearGroup.toGL p.2)]
      _ = (scalarGL k n p.1 * Matrix.SpecialLinearGroup.toGL p.2) *
          (scalarGL k n q.1 * Matrix.SpecialLinearGroup.toGL q.2) := by
        simp only [mul_assoc]

private theorem scalarSpecialMul_surjective
    {k : Type*} [Field k] [IsAlgClosed k] {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (scalarSpecialMul (k := k) n) := by
  intro g
  obtain ⟨s, h, rfl⟩ := specialLinearFactor hn g
  exact ⟨(s, h), rfl⟩

/-- In a simple `SL_n` representation, scalar `n`-th roots of unity act through one power
character.  This is the compatibility needed to descend from the central product. -/
private theorem exists_scalar_weight
    {k Y : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (hn : n ≠ 0)
    [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    ∃ d : ℕ, ∀ (s : kˣ) (hs : (s : k) ^ n = 1),
      sigma (scalarSL s hs) = ((s : k) ^ d) • LinearMap.id := by
  letI : NeZero n := ⟨hn⟩
  obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k n
  let u : kˣ := (hzeta.isUnit hn).unit
  have hu : (u : k) = zeta := IsUnit.unit_spec _
  have hun : (u : k) ^ n = 1 := by rw [hu]; exact hzeta.pow_eq_one
  let z : Matrix.SpecialLinearGroup (Fin n) k := scalarSL u hun
  have hzcentral : ∀ g : Matrix.SpecialLinearGroup (Fin n) k, z * g = g * z := by
    intro g
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, show Matrix.SpecialLinearGroup.toGL z = scalarGL k n u by
      simp [z]]
    exact scalarGL_comm u _
  obtain ⟨c, hc⟩ := exists_scalar_action_of_central sigma z hzcentral
  have hupow : u ^ n = 1 := Units.ext hun
  have hzpow : z ^ n = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, show Matrix.SpecialLinearGroup.toGL z = scalarGL k n u by simp [z]]
    change (scalarGLHom n u) ^ n = _
    rw [← map_pow, hupow, map_one, map_one]
  have hpow_smul_id (a : k) (m : ℕ) :
      (a • LinearMap.id : Module.End k Y) ^ m = (a ^ m) • LinearMap.id := by
    induction m with
    | zero => ext v; simp
    | succ m ih =>
      rw [pow_succ, ih]
      ext v
      simp [pow_succ, mul_smul, mul_comm]
  have hcpowEnd : (c ^ n) • LinearMap.id =
      (1 : Module.End k Y) := by
    calc
      (c ^ n) • LinearMap.id = (c • LinearMap.id) ^ n := (hpow_smul_id c n).symm
      _ = (sigma z) ^ n := congrArg (fun T : Module.End k Y => T ^ n) hc.symm
      _ = sigma (z ^ n) := by rw [map_pow]
      _ = 1 := by rw [hzpow, map_one]
  letI : Nontrivial Y :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hcpow : c ^ n = 1 := by
    apply smul_left_injective k hv
    have h := LinearMap.congr_fun hcpowEnd v
    simpa using h
  obtain ⟨d, hdlt, hcd⟩ := hzeta.eq_pow_of_pow_eq_one hcpow
  refine ⟨d, fun s hs => ?_⟩
  obtain ⟨m, hmlt, hsm⟩ := hzeta.eq_pow_of_pow_eq_one hs
  have hsu : s = u ^ m := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, hsm]
  have hscalarSL : scalarSL s hs = z ^ m := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, toGL_scalarSL]
    rw [show Matrix.SpecialLinearGroup.toGL z = scalarGL k n u by simp [z]]
    change scalarGL k n s = (scalarGLHom n u) ^ m
    rw [← map_pow, hsu]
    rfl
  rw [hscalarSL, map_pow, hc]
  rw [hpow_smul_id]
  ext v
  simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  rw [← hcd, ← hu]
  have hsval : (s : k) = (u : k) ^ m := congrArg Units.val hsu
  rw [hsval]
  rw [← pow_mul, mul_comm d m, pow_mul]

/-- The product action before descent: the scalar factor acts by the chosen power character and
the special-linear factor acts through `sigma`. -/
private def scalarSpecialAction
    {k Y : Type*} [Field k] {n : ℕ}
    [AddCommGroup Y] [Module k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) (d : ℕ) :
    kˣ × Matrix.SpecialLinearGroup (Fin n) k →* Module.End k Y where
  toFun p := ((p.1 : k) ^ d) • sigma p.2
  map_one' := by ext v; simp
  map_mul' p q := by
    ext v
    simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, mul_pow, map_mul,
      Module.End.mul_apply, LinearMap.smul_apply, map_smul]
    rw [mul_comm, mul_smul]

private theorem scalarSpecialAction_ker_le
    {k Y : Type*} [Field k] {n : ℕ}
    [AddCommGroup Y] [Module k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y) (d : ℕ)
    (hscalar : ∀ (s : kˣ) (hs : (s : k) ^ n = 1),
      sigma (scalarSL s hs) = ((s : k) ^ d) • LinearMap.id) :
    (scalarSpecialMul (k := k) n).ker ≤ (scalarSpecialAction sigma d).toHomUnits.ker := by
  rintro ⟨s, h⟩ hx
  rw [MonoidHom.mem_ker] at hx ⊢
  change scalarGL k n s * Matrix.SpecialLinearGroup.toGL h = 1 at hx
  have hdet := congrArg (KernelLemmaKPrime.detChar k n) hx
  have hsunit : s ^ n = 1 := by
    simpa [map_mul, detChar_toGL, detChar_scalarGL] using hdet
  have hs : (s : k) ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hsunit
  have hsinv : ((s⁻¹ : kˣ) : k) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hsunit, inv_one]
    rfl
  have hh : h = scalarSL s⁻¹ hsinv := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hto : Matrix.SpecialLinearGroup.toGL h = (scalarGL k n s)⁻¹ :=
      eq_inv_of_mul_eq_one_right hx
    rw [hto, toGL_scalarSL]
    exact ((scalarGLHom n).map_inv s).symm
  apply Units.ext
  change ((s : k) ^ d) • sigma h = (1 : Module.End k Y)
  rw [hh, hscalar]
  ext v
  simp [← Units.val_pow_eq_pow_val]

/-- Every finite-dimensional simple abstract representation of `SL_n` over an algebraically
closed field of characteristic zero extends to `GL_n`.  No regularity is asserted here.  The
construction descends the compatible action of the central product `kˣ × SL_n`. -/
theorem hasGLExtension_of_isSimple
    (n : ℕ) (k : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type*} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
    (sigma : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    [hsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) sigma.asModule] :
    HasGLExtension n sigma := by
  rcases eq_or_ne n 0 with rfl | hn
  · let rho : Representation k (Matrix.GeneralLinearGroup (Fin 0) k) Y :=
      Representation.trivial k _ _
    refine ⟨rho, ?_⟩
    ext h v
    change v = sigma h v
    have hh : h = 1 := by
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    rw [hh, map_one]
    rfl
  · obtain ⟨d, hscalar⟩ := exists_scalar_weight hn sigma
    let phi := scalarSpecialMul (k := k) n
    let psi := scalarSpecialAction sigma d
    have hphi : Function.Surjective phi := scalarSpecialMul_surjective hn
    have hker : phi.ker ≤ psi.toHomUnits.ker :=
      scalarSpecialAction_ker_le sigma d hscalar
    let lift : Matrix.GeneralLinearGroup (Fin n) k →* (Module.End k Y)ˣ :=
      phi.liftOfSurjective hphi ⟨psi.toHomUnits, hker⟩
    let rho : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y :=
      (Units.coeHom (Module.End k Y)).comp lift
    refine ⟨rho, ?_⟩
    ext h v
    have hphi1 : phi (1, h) = Matrix.SpecialLinearGroup.toGL h := by
      change scalarGL k n 1 * Matrix.SpecialLinearGroup.toGL h =
        Matrix.SpecialLinearGroup.toGL h
      rw [show scalarGL k n 1 = 1 by exact (scalarGLHom n).map_one, one_mul]
    have hlift : lift (Matrix.SpecialLinearGroup.toGL h) = psi.toHomUnits (1, h) := by
      rw [← hphi1]
      simp [lift]
    change ((lift (Matrix.SpecialLinearGroup.toGL h) : (Module.End k Y)ˣ) :
      Module.End k Y) v = sigma h v
    rw [hlift]
    change (((1 : kˣ) : k) ^ d • sigma h) v = sigma h v
    simp

/-- Liftable algebraicity implies intrinsic algebraicity on `SL_n`. -/
theorem HasAlgebraicGLExtension.isAlgebraic
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y}
    (hσ : HasAlgebraicGLExtension n σ) : IsAlgebraicSLRepresentation n σ := by
  obtain ⟨ρ, hρ, rfl⟩ := hσ
  exact hρ.slRestrict

/-- A representation whose restriction to `SL_n` is simple is itself simple as a `GL_n`
representation: every `GL_n`-stable subspace is in particular `SL_n`-stable. -/
theorem isSimpleModule_of_slRestrict_isSimple
    {k : Type*} [Field k] {n : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) Y)
    [hsl : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k))
      (slRestrict ρ).asModule] :
    IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have hsl' : Representation.IsIrreducible (slRestrict ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).2 hsl
  letI : Nontrivial Y :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) (slRestrict ρ).asModule
  refine
    { exists_pair_ne := ⟨⊥, ⊤, by
        intro h
        have h' := congrArg Subrepresentation.toSubmodule h
        change (⊥ : Submodule k Y) = ⊤ at h'
        exact bot_ne_top h'⟩
      eq_bot_or_eq_top := fun S => ?_ }
  let T : Subrepresentation (slRestrict ρ) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv =>
        S.apply_mem_toSubmodule (Matrix.SpecialLinearGroup.toGL g) hv }
  rcases hsl'.eq_bot_or_eq_top T with hT | hT
  · left
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊥
    have hT' := congrArg Subrepresentation.toSubmodule hT
    change T.toSubmodule = (⊥ : Submodule k Y) at hT'
    exact hT'
  · right
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    have hT' := congrArg Subrepresentation.toSubmodule hT
    change T.toSubmodule = (⊤ : Submodule k Y) at hT'
    exact hT'

/-- **Conditional exhaustiveness for `SL_n`.** Every simple `SL_n` representation that admits an
algebraic `GL_n` extension is isomorphic to the restriction of `L_λ` for some dominant weight
`λ`.  The only extra input needed for unconditional #7808 is that intrinsic algebraicity implies
the existence of such an extension. -/
theorem exists_dominantWeight_slEquiv_of_hasAlgebraicGLExtension
    (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Type} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (σ : Representation k (Matrix.SpecialLinearGroup (Fin n) k) Y)
    (hσ : HasAlgebraicGLExtension n σ)
    [hsimp : IsSimpleModule (MonoidAlgebra k (Matrix.SpecialLinearGroup (Fin n) k)) σ.asModule] :
    ∃ lam : DominantWeight n,
      Nonempty (Representation.Equiv σ (slRestrict (algIrrepGLRepρ n lam k))) := by
  obtain ⟨ρ, hρ, hres⟩ := hσ
  subst σ
  letI : IsSimpleModule (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin n) k)) ρ.asModule :=
    isSimpleModule_of_slRestrict_isSimple ρ
  obtain ⟨lam, ⟨e⟩⟩ :=
    exists_dominantWeight_asModuleEquiv_of_isSimpleModule n k ρ hρ
  let E : Representation.Equiv ρ (algIrrepGLRepρ n lam k) :=
    Representation.Equiv.mk (Representation.kEquivOfAsModuleEquiv e) (fun g => by
      ext v
      exact Representation.kEquivOfAsModuleEquiv_intertwines e g v)
  exact ⟨lam, ⟨slRestrictEquiv E⟩⟩

end Etingof
