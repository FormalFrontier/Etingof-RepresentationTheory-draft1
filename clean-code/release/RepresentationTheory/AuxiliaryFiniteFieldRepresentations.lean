import Mathlib
import RepresentationTheory.FDRep.GroupAlgebraDecomposition
import RepresentationTheory.Group.CharacterAuxiliary
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.AuxiliaryFiniteFieldRepresentations


open CategoryTheory CategoryTheory.Limits Classical

noncomputable section

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ)

private abbrev GL2 (p n : ℕ) [Fact (Nat.Prime p)] :=
  Matrix.GeneralLinearGroup (Fin 2) (GaloisField p n)

/-- An auxiliary finite enumeration structure for the displayed Galois field. -/
instance auxiliaryFintypeGaloisField : Fintype (GaloisField p n) := Fintype.ofFinite _

/-- An auxiliary subgroup of the displayed group. -/
def auxiliarySubgroup :
    Subgroup (GL2 p n) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at *
    simp [ha, hb]
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    have hmul : (g.val * (g⁻¹).val) 1 0 = (1 : Matrix (Fin 2) (Fin 2) _) 1 0 := by
      have : g.val * (g⁻¹).val = 1 := by exact_mod_cast g.mul_inv
      rw [this]
    simp only [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at hmul
    rw [hg, zero_mul, zero_add] at hmul
    have hdet : IsUnit (g.val.det) := g.isUnit.map Matrix.detMonoidHom
    rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hdet
    exact (mul_eq_zero.mp hmul).resolve_left
      (IsUnit.ne_zero (isUnit_of_mul_isUnit_right hdet))

/-- The indicated evaluation at two zero indices is nonzero. -/
lemma auxiliary_eval_zero_zero_ne_zero
    (b : ↥(auxiliarySubgroup p n)) :
    (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 ≠ 0 := by
  intro h
  have hdet : IsUnit (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)).det :=
    b.val.isUnit.map Matrix.detMonoidHom
  rw [Matrix.det_fin_two, b.prop, mul_zero, sub_zero, h, zero_mul] at hdet
  exact not_isUnit_zero hdet

/-- The indicated evaluation at two one indices is nonzero. -/
lemma auxiliary_eval_one_one_ne_zero
    (b : ↥(auxiliarySubgroup p n)) :
    (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 ≠ 0 := by
  intro h
  have hdet : IsUnit (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)).det :=
    b.val.isUnit.map Matrix.detMonoidHom
  rw [Matrix.det_fin_two, b.prop, mul_zero, sub_zero, h, mul_zero] at hdet
  exact not_isUnit_zero hdet

/-- An auxiliary complex-valued function of two monoid homomorphisms and a subgroup element. -/
def auxiliaryComplexFunction
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b : ↥(auxiliarySubgroup p n)) : ℂ :=
  let bmat := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  (chi1 (Units.mk0 (bmat 0 0) (auxiliary_eval_zero_zero_ne_zero p n b)) : ℂ) *
  (chi2 (Units.mk0 (bmat 1 1) (auxiliary_eval_one_one_ne_zero p n b)) : ℂ)

/-- An auxiliary submodule of complex-valued functions on the displayed group. -/
def auxiliarySubmodule
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Submodule ℂ (GL2 p n → ℂ) where
  carrier := {f | ∀ (b : ↥(auxiliarySubgroup p n)) (g : GL2 p n),
    f (b.val * g) = auxiliaryComplexFunction p n chi1 chi2 b * f g}
  add_mem' {f g} hf hg := by
    intro b x; simp only [Pi.add_apply]; rw [hf b x, hg b x, mul_add]
  zero_mem' := by intro b g; simp
  smul_mem' c f hf := by
    intro b g; simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf b g, mul_left_comm]

/-- A representation whose carrier is the displayed auxiliary submodule. -/
def auxiliarySubmoduleRepresentation
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Representation ℂ (GL2 p n)
      (auxiliarySubmodule p n chi1 chi2) where
  toFun h := {
    toFun := fun ⟨f, hf⟩ => ⟨fun g => f (g * h), fun b g => by
      change f (↑b * g * h) = auxiliaryComplexFunction p n chi1 chi2 b * f (g * h)
      rw [mul_assoc]; exact hf b (g * h)⟩
    map_add' := fun ⟨_, _⟩ ⟨_, _⟩ => Subtype.ext rfl
    map_smul' := fun _ ⟨_, _⟩ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_assoc g a b).symm)

private def augmentation
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (GL2 p n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ g : GL2 p n,
    f g * ((mu (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ)
  map_add' f g := by simp [Finset.sum_add_distrib, add_mul]
  map_smul' c f := by
    simp only [smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]

private def complementWSubmodule
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Submodule ℂ (GL2 p n → ℂ) :=
  auxiliarySubmodule p n mu mu ⊓
    LinearMap.ker (augmentation p n mu)

private lemma complementW_mem_of_mul
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : GL2 p n → ℂ)
    (hf : f ∈ complementWSubmodule p n mu)
    (h : GL2 p n) :
    (fun g => f (g * h)) ∈ complementWSubmodule p n mu := by
  constructor
  · -- Covariance preserved
    intro b g
    change f (↑b * g * h) = auxiliaryComplexFunction p n mu mu b * f (g * h)
    rw [mul_assoc]; exact hf.1 b (g * h)
  · -- Augmentation = 0: ∑_g f(gh) · μ(det g)⁻¹ = 0
    have hker : ∑ g : GL2 p n, f g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 0 := by
      have := hf.2; simp only [augmentation,
        LinearMap.coe_mk] at this; exact this
    change (fun g => f (g * h)) ∈ LinearMap.ker (augmentation p n mu)
    rw [LinearMap.mem_ker]
    change ∑ g : GL2 p n,
      f (g * h) * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 0
    rw [Fintype.sum_equiv (Equiv.mulRight h)
        (fun g => f (g * h) * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹)
        (fun g => f g * ↑(mu (Matrix.GeneralLinearGroup.det (g * h⁻¹)))⁻¹)
        (fun g => by simp [Equiv.coe_mulRight])]
    simp_rw [map_mul, mul_inv_rev, Units.val_mul]
    simp_rw [show ∀ g : GL2 p n,
        f g * (↑(mu (Matrix.GeneralLinearGroup.det h⁻¹))⁻¹ *
        ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹) =
        f g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ *
        ↑(mu (Matrix.GeneralLinearGroup.det h⁻¹))⁻¹ from fun g => by ring]
    rw [← Finset.sum_mul, hker, zero_mul]

private def complementWRep
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Representation ℂ (GL2 p n) (complementWSubmodule p n mu) where
  toFun h := {
    toFun := fun ⟨f, hf⟩ => ⟨fun g => f (g * h),
      complementW_mem_of_mul p n mu f hf h⟩
    map_add' := fun ⟨_, _⟩ ⟨_, _⟩ => Subtype.ext rfl
    map_smul' := fun _ ⟨_, _⟩ => Subtype.ext rfl }
  map_one' := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_one g))
  map_mul' a b := by
    apply LinearMap.ext; intro ⟨f, _⟩
    exact Subtype.ext (funext fun g => congr_arg f (mul_assoc g a b).symm)

/-- An auxiliary finite-dimensional representation associated with a pair of monoid homomorphisms. -/
@[source_ref "Chapter5/Discussion_5.25.3" (role := supporting)]
def auxiliaryPairedRepresentation
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    FDRep ℂ (GL2 p n) :=
  FDRep.of (auxiliarySubmoduleRepresentation p n chi1 chi2)

/-- A second auxiliary finite-dimensional representation associated with a monoid homomorphism. -/
def auxiliaryOtherRepresentation
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    FDRep ℂ (GL2 p n) :=
  FDRep.of
    ({ toFun := fun g => ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.id
       map_one' := by
         ext; simp
       map_mul' := fun a b => by
         apply LinearMap.ext; intro x
         change ((mu (Matrix.GeneralLinearGroup.det (a * b)) : ℂˣ) : ℂ) * x =
           ((mu (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ) *
           (((mu (Matrix.GeneralLinearGroup.det b) : ℂˣ) : ℂ) * x)
         rw [map_mul, map_mul, Units.val_mul, mul_assoc]
    } : Representation ℂ _ ℂ)

/-- An auxiliary finite-dimensional representation associated with a monoid homomorphism. -/
def auxiliaryRepresentation
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    FDRep ℂ (GL2 p n) :=
  FDRep.of (complementWRep p n mu)

private lemma sum_monoidHom_units_eq_zero
    {F : Type*} [CommGroup F] [Fintype F]
    (φ : F →* ℂˣ) (hφ : φ ≠ 1) :
    ∑ x : F, (φ x : ℂ) = 0 := by
  have ⟨b, hb⟩ : ∃ b, φ b ≠ 1 := by
    by_contra h; push Not at h
    exact hφ (MonoidHom.ext fun x => h x)
  have hreindex : ∑ x : F, (φ (b * x) : ℂ) = ∑ x : F, (φ x : ℂ) :=
    Fintype.sum_equiv (Equiv.mulLeft b) _ _ (fun _ => rfl)
  simp_rw [map_mul, Units.val_mul] at hreindex
  rw [← Finset.mul_sum] at hreindex
  have hsub : ((φ b : ℂ) - 1) * ∑ x : F, (φ x : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact hreindex
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (Units.val_injective ((sub_eq_zero.mp h).trans Units.val_one.symm)) hb
  · exact h

private lemma simple_of_full_faithful_preservesMono' {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesMonomorphisms] (X : C)
    [Simple (F.obj X)] : Simple X where
  mono_isIso_iff_nonzero {Y} f := by
    intro
    constructor
    · intro hiso
      haveI : IsIso (F.map f) := Functor.map_isIso F f
      exact fun h => (Simple.mono_isIso_iff_nonzero (F.map f)).mp inferInstance
        (by rw [h]; simp)
    · intro hne
      haveI : Mono (F.map f) := inferInstance
      haveI : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr
        (fun h => hne (F.map_injective (by rwa [F.map_zero])))
      exact isIso_of_fully_faithful F f

private lemma simple_of_isSimpleModule_FDRep
    {G : Type} [Group G] [Fintype G]
    [NeZero (Nat.card G : ℂ)]
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

section AuxiliarySetup

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ) (hn : 0 < n)

end AuxiliarySetup

/-- Builds an auxiliary group element from an optional finite-field value. -/
noncomputable def auxiliaryElement
    (i : Option (GaloisField p n)) : GL2 p n :=
  match i with
  | none => 1
  | some t => Matrix.GeneralLinearGroup.mkOfDetNeZero
      (n := Fin 2) (K := GaloisField p n) !![0, -1; 1, t]
      (by simp [Matrix.det_fin_two])

/-- Maps each displayed group element to an optional finite-field value. -/
noncomputable def auxiliaryOptionMap
    (g : GL2 p n) : Option (GaloisField p n) :=
  if h : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 then none
  else some ((g.val : Matrix _ _ _) 1 1 / (g.val : Matrix _ _ _) 1 0)

/-- Maps each displayed group element to an auxiliary subgroup element. -/
noncomputable def auxiliarySubgroupMap
    (g : GL2 p n) : ↥(auxiliarySubgroup p n) :=
  if h : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 then
    ⟨g, h⟩
  else
    let gm := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    let bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
      !![gm.det / gm 1 0, gm 0 0; (0 : _), gm 1 0]
    have hdet : gm.det ≠ 0 := IsUnit.ne_zero ((Units.isUnit g).map Matrix.detMonoidHom)
    have hbdet : bmat.det ≠ 0 := by
      have h10 : gm 1 0 ≠ 0 := h
      have : bmat.det = gm.det := by
        simp [Matrix.det_fin_two, bmat]; field_simp
      rw [this]; exact hdet
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet, by
      change ((Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet).val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible, bmat]⟩

/-- Each displayed group element has the indicated decomposition using the auxiliary subgroup map. -/
lemma auxiliarySubgroupMap_decomposition
    (g : GL2 p n) :
    g = (auxiliarySubgroupMap p n g).val * auxiliaryElement p n (auxiliaryOptionMap p n g) := by
  unfold auxiliarySubgroupMap auxiliaryOptionMap auxiliaryElement
  split_ifs with h10
  · simp
  · apply Matrix.GeneralLinearGroup.ext; intro i j
    set gm := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.det_fin_two] <;> field_simp ; ring

/-- Every displayed group element has an auxiliary factor decomposition. -/
lemma auxiliary_exists_factor_decomposition
    (g : GL2 p n) :
    ∃ (b : ↥(auxiliarySubgroup p n)),
      g = b.val * auxiliaryElement p n (auxiliaryOptionMap p n g) := by
  unfold auxiliaryOptionMap auxiliaryElement
  split_ifs with h10
  · exact ⟨⟨g, h10⟩, by simp⟩
  · set gm := (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) with hgm_def
    have hdet : gm.det ≠ 0 := IsUnit.ne_zero ((Units.isUnit g).map Matrix.detMonoidHom)
    set bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
      !![gm.det / gm 1 0, gm 0 0; (0 : _), gm 1 0] with hbmat_def
    have hbdet : bmat.det ≠ 0 := by
      have : bmat.det = gm.det := by
        simp [hbmat_def, Matrix.det_fin_two]
        field_simp
      rw [this]; exact hdet
    refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet, ?_⟩, ?_⟩
    · -- b ∈ B: b₁₀ = 0
      change ((Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet).val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible, bmat]
    · -- g = b * rep(t): verify entry by entry
      apply Matrix.GeneralLinearGroup.ext; intro i j
      simp only [Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [bmat, Matrix.det_fin_two] <;>
        (try ring) <;> (field_simp; ring)

/-- The auxiliary optional value is unchanged after multiplication by an auxiliary subgroup factor. -/
lemma auxiliaryOptionMap_mul
    (b : ↥(auxiliarySubgroup p n)) (g : GL2 p n) :
    auxiliaryOptionMap p n (b.val * g) = auxiliaryOptionMap p n g := by
  simp only [auxiliaryOptionMap]
  have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
  have hbg10 : ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 =
    (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 0 := by
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb10]
  have hb11 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 ≠ 0 :=
    auxiliary_eval_one_one_ne_zero p n b
  by_cases hg10 : (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
  · have : ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
      rw [hbg10]; simp [hg10]
    simp [hg10, this]
  · have hbg10_ne : ¬ ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
      rw [hbg10]; exact mul_ne_zero hb11 hg10
    have hbg11 : ((b.val * g).val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 =
      (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 1 := by
      simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hb10]
    simp only [hg10, hbg10_ne, ↓reduceDIte]
    congr 1
    rw [show ((b.val * g).val : Matrix _ _ _) 1 1 =
        (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 1 from hbg11,
      show ((b.val * g).val : Matrix _ _ _) 1 0 =
        (b.val.val : Matrix _ _ _) 1 1 * (g.val : Matrix _ _ _) 1 0 from hbg10]
    rw [mul_div_mul_left _ _ hb11]

/-- The auxiliary complex-valued function is multiplicative on subgroup elements. -/
lemma auxiliaryComplexFunction_mul
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (b1 b2 : ↥(auxiliarySubgroup p n)) :
    auxiliaryComplexFunction p n chi1 chi2
      ⟨b1.val * b2.val, (auxiliarySubgroup p n).mul_mem b1.prop b2.prop⟩ =
    auxiliaryComplexFunction p n chi1 chi2 b1 *
    auxiliaryComplexFunction p n chi1 chi2 b2 := by
  unfold auxiliaryComplexFunction
  have hb1_10 := b1.prop
  have hb2_10 := b2.prop
  have hb2_10' : (b2.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b2.prop
  have hb1_10' : (b1.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b1.prop
  have h00 : Units.mk0 _ (auxiliary_eval_zero_zero_ne_zero p n
      ⟨b1.val * b2.val, (auxiliarySubgroup p n).mul_mem b1.prop b2.prop⟩) =
    Units.mk0 _ (auxiliary_eval_zero_zero_ne_zero p n b1) *
    Units.mk0 _ (auxiliary_eval_zero_zero_ne_zero p n b2) := by
    ext
    change ((b1.val * b2.val).val : Matrix _ _ _) 0 0 =
      (b1.val.val : Matrix _ _ _) 0 0 * (b2.val.val : Matrix _ _ _) 0 0
    change ((b1.val.val * b2.val.val) 0 0 : _) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb2_10']
  have h11 : Units.mk0 _ (auxiliary_eval_one_one_ne_zero p n
      ⟨b1.val * b2.val, (auxiliarySubgroup p n).mul_mem b1.prop b2.prop⟩) =
    Units.mk0 _ (auxiliary_eval_one_one_ne_zero p n b1) *
    Units.mk0 _ (auxiliary_eval_one_one_ne_zero p n b2) := by
    ext
    change ((b1.val * b2.val).val : Matrix _ _ _) 1 1 =
      (b1.val.val : Matrix _ _ _) 1 1 * (b2.val.val : Matrix _ _ _) 1 1
    change ((b1.val.val * b2.val.val) 1 1 : _) = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb1_10']
  simp only [auxiliaryComplexFunction]
  rw [show Units.mk0 ((b1.val * b2.val).val 0 0 : _) _ = _ from h00,
      show Units.mk0 ((b1.val * b2.val).val 1 1 : _) _ = _ from h11,
      map_mul, map_mul, Units.val_mul, Units.val_mul]
  ring

/-- The auxiliary subgroup map is compatible with the displayed multiplication. -/
lemma auxiliarySubgroupMap_mul
    (b : ↥(auxiliarySubgroup p n)) (g : GL2 p n) :
    auxiliarySubgroupMap p n (b.val * g) =
      ⟨b.val * (auxiliarySubgroupMap p n g).val,
       (auxiliarySubgroup p n).mul_mem b.prop (auxiliarySubgroupMap p n g).prop⟩ := by
  apply Subtype.ext
  have h1 := auxiliarySubgroupMap_decomposition p n (b.val * g)
  have h2 := auxiliarySubgroupMap_decomposition p n g
  have hidx := auxiliaryOptionMap_mul p n b g
  have key : (auxiliarySubgroupMap p n (b.val * g)).val *
      auxiliaryElement p n (auxiliaryOptionMap p n (b.val * g)) =
    (b.val * (auxiliarySubgroupMap p n g).val) *
      auxiliaryElement p n (auxiliaryOptionMap p n (b.val * g)) := by
    rw [← h1, mul_assoc, hidx, ← h2]
  exact mul_right_cancel key

/-- An auxiliary complex-valued function on the displayed group from the given input data. -/
noncomputable def auxiliaryFunctionOnGroup
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    GL2 p n → ℂ :=
  fun g => auxiliaryComplexFunction p n chi1 chi2
    (auxiliarySubgroupMap p n g) * c (auxiliaryOptionMap p n g)

/-- The auxiliary function on the group belongs to the displayed submodule. -/
lemma auxiliaryFunctionOnGroup_mem
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    auxiliaryFunctionOnGroup p n chi1 chi2 c ∈
      auxiliarySubmodule p n chi1 chi2 := by
  intro b g
  simp only [auxiliaryFunctionOnGroup]
  rw [auxiliaryOptionMap_mul, auxiliarySubgroupMap_mul]
  rw [auxiliaryComplexFunction_mul]
  ring

/-- Applying the auxiliary option map to the auxiliary element recovers its input. -/
lemma auxiliaryOptionMap_auxiliaryElement
    (i : Option (GaloisField p n)) :
    auxiliaryOptionMap p n (auxiliaryElement p n i) = i := by
  cases i with
  | none =>
    simp [auxiliaryOptionMap, auxiliaryElement]
  | some t =>
    simp only [auxiliaryOptionMap, auxiliaryElement,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
    have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero
        (n := Fin 2) (K := GaloisField p n) !![0, -1; 1, t]
        (by simp [Matrix.det_fin_two])).val 1 0 ≠ 0 := by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible]
    simp [

          Matrix.unitOfDetInvertible]

/-- The auxiliary complex-valued function takes value one at the identity. -/
lemma auxiliaryComplexFunction_one
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryComplexFunction p n chi1 chi2
      ⟨1, by simp [auxiliarySubgroup]⟩ = 1 := by
  unfold auxiliaryComplexFunction
  simp

/-- The auxiliary subgroup map sends the displayed auxiliary element to the identity. -/
lemma auxiliarySubgroupMap_auxiliaryElement
    (i : Option (GaloisField p n)) :
    auxiliarySubgroupMap p n (auxiliaryElement p n i) =
      ⟨1, by simp [auxiliarySubgroup]⟩ := by
  cases i with
  | none =>
    simp [auxiliarySubgroupMap, auxiliaryElement, auxiliarySubgroup]
  | some t =>
    simp only [auxiliarySubgroupMap, auxiliaryElement]
    have h10 : ¬ ((Matrix.GeneralLinearGroup.mkOfDetNeZero
        (n := Fin 2) (K := GaloisField p n) !![0, -1; 1, t]
        (by simp [Matrix.det_fin_two])).val :
          Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
            Matrix.unitOfDetInvertible]
    rw [dif_neg h10]
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    fin_cases i <;> fin_cases j <;> simp

/-- The auxiliary function on the group agrees with its input function on the displayed auxiliary elements. -/
lemma auxiliaryFunctionOnGroup_auxiliaryElement
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ)
    (i : Option (GaloisField p n)) :
    auxiliaryFunctionOnGroup p n chi1 chi2 c
      (auxiliaryElement p n i) = c i := by
  simp [auxiliaryFunctionOnGroup,
    auxiliaryOptionMap_auxiliaryElement,
    auxiliarySubgroupMap_auxiliaryElement,
    auxiliaryComplexFunction_one]

/-- A member of the auxiliary submodule vanishing on all auxiliary elements is zero. -/
lemma auxiliarySubmodule_ext
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (hf : ∀ i : Option (GaloisField p n),
      (f : GL2 p n → ℂ) (auxiliaryElement p n i) = 0) :
    f = 0 := by
  ext g
  obtain ⟨b, hbg⟩ := auxiliary_exists_factor_decomposition p n g
  have hcov := f.prop b (auxiliaryElement p n (auxiliaryOptionMap p n g))
  rw [← hbg] at hcov
  rw [show (f : GL2 p n → ℂ) g = (f.val g) from rfl, hcov,
      hf (auxiliaryOptionMap p n g), mul_zero]
  simp

private noncomputable def translationElt
    (s : GaloisField p n) : GL2 p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, s; 0, 1] (by simp [Matrix.det_fin_two])

private noncomputable def diagElt
    (c : (GaloisField p n)ˣ) : GL2 p n :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(c : GaloisField p n), 0; 0, 1]
    (by simp [Matrix.det_fin_two, Units.ne_zero])

private lemma cosetRep_mul_translation_some
    (t s : GaloisField p n) :
    auxiliaryElement p n (some t) * translationElt p n s =
    auxiliaryElement p n (some (t + s)) := by
  apply Matrix.GeneralLinearGroup.ext; intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul,
    auxiliaryElement, translationElt,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp ; ring

private lemma action_translation_some
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (s t : GaloisField p n) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (translationElt p n s) f).val
      (auxiliaryElement p n (some t)) =
    f.val (auxiliaryElement p n (some (t + s))) := by
  change f.val (auxiliaryElement p n (some t) * translationElt p n s) = _
  rw [cosetRep_mul_translation_some]

private lemma action_translation_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (s : GaloisField p n) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (translationElt p n s) f).val
      (auxiliaryElement p n none) =
    f.val (auxiliaryElement p n none) := by
  change f.val (auxiliaryElement p n none * translationElt p n s) = _
  simp only [auxiliaryElement, one_mul]
  have hb_mem : (translationElt p n s).val 1 0 = 0 := by
    simp [translationElt, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]
  have hcov := f.prop ⟨translationElt p n s, hb_mem⟩ 1
  simp only [mul_one] at hcov
  rw [hcov]
  simp [auxiliaryComplexFunction, translationElt,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

private lemma action_diagonal_some
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (c : (GaloisField p n)ˣ) (t : GaloisField p n) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (diagElt p n c) f).val
      (auxiliaryElement p n (some t)) =
    (chi2 c : ℂ) * f.val (auxiliaryElement p n (some (t * ↑c⁻¹))) := by
  change f.val (auxiliaryElement p n (some t) * diagElt p n c) = _
  set bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
    !![1, 0; 0, (c : GaloisField p n)]
  have hbdet : bmat.det ≠ 0 := by
    simp [bmat, Matrix.det_fin_two, Units.ne_zero]
  set b := Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet
  have hb_mem : b.val 1 0 = 0 := by
    simp [b, bmat, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
  have hprod : auxiliaryElement p n (some t) * diagElt p n c =
      b * auxiliaryElement p n (some (t * ↑c⁻¹)) := by
    apply Matrix.GeneralLinearGroup.ext; intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      auxiliaryElement, diagElt, b, bmat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
    have hc_ne : (c : GaloisField p n) ≠ 0 := Units.ne_zero c
    fin_cases i <;> fin_cases j <;> simp
    · -- (1,1) entry: t = ↑c * (t * (↑c)⁻¹)
      field_simp
  rw [hprod]
  have hcov := f.prop ⟨b, hb_mem⟩ (auxiliaryElement p n (some (t * ↑c⁻¹)))
  rw [hcov]
  congr 1
  simp [auxiliaryComplexFunction, b, bmat,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

private lemma action_diagonal_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (c : (GaloisField p n)ˣ) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (diagElt p n c) f).val
      (auxiliaryElement p n none) =
    (chi1 c : ℂ) * f.val (auxiliaryElement p n none) := by
  change f.val (auxiliaryElement p n none * diagElt p n c) = _
  simp only [auxiliaryElement, one_mul]
  have hb_mem : (diagElt p n c).val 1 0 = 0 := by
    simp [diagElt, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]
  have hcov := f.prop ⟨diagElt p n c, hb_mem⟩ 1
  simp only [mul_one] at hcov
  rw [hcov]
  congr 1
  simp [auxiliaryComplexFunction, diagElt,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

private lemma action_weyl_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2)) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (auxiliaryElement p n (some 0)) f).val
      (auxiliaryElement p n none) =
    f.val (auxiliaryElement p n (some 0)) := by
  change f.val (auxiliaryElement p n none * auxiliaryElement p n (some 0)) = _
  simp [auxiliaryElement]

private lemma principalSeries_nontrivial
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Nontrivial (Subrepresentation (auxiliarySubmoduleRepresentation p n chi1 chi2)) := by
  set f : ↥(auxiliarySubmodule p n chi1 chi2) :=
    ⟨auxiliaryFunctionOnGroup p n chi1 chi2 (fun _ => 1),
     auxiliaryFunctionOnGroup_mem p n chi1 chi2 (fun _ => 1)⟩
  have hfne : f ≠ 0 := by
    intro h
    have heval := auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 (fun _ => 1) none
    simp only [f] at h
    have : (0 : ↥(auxiliarySubmodule p n chi1 chi2)).val
        (auxiliaryElement p n none) = 1 := by rw [← h]; exact heval
    simp at this
  exact nontrivial_of_ne ⊥ ⊤ (by
    intro heq
    apply hfne
    have hmem : f ∈ (⊥ : Subrepresentation
      (auxiliarySubmoduleRepresentation p n chi1 chi2)).toSubmodule := by
      rw [heq]; exact Submodule.mem_top
    exact (Submodule.mem_bot ℂ).mp hmem)

private lemma principalSeries_construct_delta_none
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2)
    (S : Subrepresentation (auxiliarySubmoduleRepresentation p n chi1 chi2))
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (hfS : f ∈ S.toSubmodule) (hfne : f ≠ 0) :
    ∃ g : ↥(auxiliarySubmodule p n chi1 chi2),
      g ∈ S.toSubmodule ∧
      g.val (auxiliaryElement p n none) ≠ 0 ∧
      ∀ t : GaloisField p n, g.val (auxiliaryElement p n (some t)) = 0 := by
  have hf'exists : ∃ f' ∈ S.toSubmodule,
      f'.val (auxiliaryElement p n none) ≠ 0 := by
    by_cases hfnone : f.val (auxiliaryElement p n none) ≠ 0
    · exact ⟨f, hfS, hfnone⟩
    · push Not at hfnone
      have hsome : ∃ t₀, f.val (auxiliaryElement p n (some t₀)) ≠ 0 := by
        by_contra hall; push Not at hall
        exact hfne (auxiliarySubmodule_ext p n chi1 chi2 f
          (fun i => match i with | none => hfnone | some t => hall t))
      obtain ⟨t₀, ht₀⟩ := hsome
      set f' := (auxiliarySubmoduleRepresentation p n chi1 chi2) (auxiliaryElement p n (some 0))
        ((auxiliarySubmoduleRepresentation p n chi1 chi2) (translationElt p n t₀) f)
      refine ⟨f', ?_, ?_⟩
      · -- f' ∈ S: S is G-stable
        exact S.apply_mem_toSubmodule _ (S.apply_mem_toSubmodule _ hfS)
      · -- f'(rep(none)) ≠ 0
        rw [show f'.val = (auxiliarySubmoduleRepresentation p n chi1 chi2
          (auxiliaryElement p n (some 0))
          (auxiliarySubmoduleRepresentation p n chi1 chi2
            (translationElt p n t₀) f)).val from rfl]
        rw [action_weyl_none p n chi1 chi2
          (auxiliarySubmoduleRepresentation p n chi1 chi2 (translationElt p n t₀) f)]
        rw [action_translation_some p n chi1 chi2 f t₀ 0, zero_add]
        exact ht₀
  obtain ⟨f', hf'S, hf'none⟩ := hf'exists
  let ρ := auxiliarySubmoduleRepresentation p n chi1 chi2
  set avg := ∑ s : GaloisField p n, ρ (translationElt p n s) f' with avg_def
  have havgS : avg ∈ S.toSubmodule :=
    S.toSubmodule.sum_mem (fun s _ => S.apply_mem_toSubmodule _ hf'S)
  have hval : ∀ x, avg.val x =
      ∑ s : GaloisField p n, (ρ (translationElt p n s) f').val x := by
    intro x
    have : (Submodule.subtype _ avg) x =
        ∑ s, (Submodule.subtype _ (ρ (translationElt p n s) f')) x := by
      rw [show Submodule.subtype _ avg = Submodule.subtype _
        (∑ s, ρ (translationElt p n s) f') from rfl, map_sum]
      simp [Finset.sum_apply]
    exact this
  have havg_none : avg.val (auxiliaryElement p n none) =
      (Fintype.card (GaloisField p n) : ℂ) * f'.val (auxiliaryElement p n none) := by
    rw [hval]
    conv_lhs => arg 2; ext s
                rw [action_translation_none p n chi1 chi2 f' s]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have havg_some_const : ∀ t : GaloisField p n,
      avg.val (auxiliaryElement p n (some t)) =
      ∑ u : GaloisField p n, f'.val (auxiliaryElement p n (some u)) := by
    intro t; rw [hval]
    conv_lhs => arg 2; ext s
                rw [action_translation_some p n chi1 chi2 f' s t]
    exact Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun s => rfl)
  have ⟨c, hc⟩ : ∃ c : (GaloisField p n)ˣ, chi1 c ≠ chi2 c := by
    by_contra h; push Not at h; exact hne (MonoidHom.ext h)
  set g := ρ (diagElt p n c) avg - (chi2 c : ℂ) • avg
  refine ⟨g, ?_, ?_, ?_⟩
  · -- g ∈ S
    exact S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ havgS)
      (S.toSubmodule.smul_mem _ havgS)
  · -- g(rep(none)) ≠ 0: g(rep(none)) = (χ₁(c) - χ₂(c)) · q · f'(rep(none))
    intro heq
    have hgval : g.val (auxiliaryElement p n none) =
        ((chi1 c : ℂ) - (chi2 c : ℂ)) * ((Fintype.card (GaloisField p n) : ℂ) *
          f'.val (auxiliaryElement p n none)) := by
      change (ρ (diagElt p n c) avg - (chi2 c : ℂ) • avg).val
        (auxiliaryElement p n none) = _
      simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [action_diagonal_none p n chi1 chi2 avg c, havg_none]
      ring
    rw [hgval] at heq
    rcases mul_eq_zero.mp heq with hsub | hprod
    · exact hc (Units.val_injective (sub_eq_zero.mp hsub))
    · rcases mul_eq_zero.mp hprod with hq | hf
      · exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hq
      · exact hf'none hf
  · -- g(rep(some t)) = 0: diagonal and averaging cancel
    intro t
    change (ρ (diagElt p n c) avg - (chi2 c : ℂ) • avg).val
      (auxiliaryElement p n (some t)) = 0
    simp only [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [action_diagonal_some p n chi1 chi2 avg c t,
      havg_some_const (t * ↑c⁻¹), havg_some_const t]
    ring

private lemma action_weyl_some_zero
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2)) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (auxiliaryElement p n (some 0)) f).val
      (auxiliaryElement p n (some 0)) =
    f.val (auxiliaryElement p n (some 0) * auxiliaryElement p n (some 0)) := rfl

private lemma cosetRep_some_mul_weyl_not_borel
    (t : GaloisField p n) (ht : t ≠ 0) :
    ((auxiliaryElement p n (some t) *
      auxiliaryElement p n (some 0)).val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 := by
  simp only [auxiliaryElement, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
  simp [ht]

private lemma action_weyl_some_ne_zero
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (hfsome : ∀ s, f.val (auxiliaryElement p n (some s)) = 0)
    (t : GaloisField p n) (ht : t ≠ 0) :
    (auxiliarySubmoduleRepresentation p n chi1 chi2
      (auxiliaryElement p n (some 0)) f).val
      (auxiliaryElement p n (some t)) = 0 := by
  change f.val (auxiliaryElement p n (some t) * auxiliaryElement p n (some 0)) = 0
  set M := auxiliaryElement p n (some t) * auxiliaryElement p n (some 0)
  obtain ⟨b, hbM⟩ := auxiliary_exists_factor_decomposition p n M
  have hcov := f.prop b (auxiliaryElement p n (auxiliaryOptionMap p n M))
  rw [← hbM] at hcov
  rw [hcov]
  have hidx : ∃ s, auxiliaryOptionMap p n M = some s := by
    unfold auxiliaryOptionMap
    simp only [M]
    have h10 := cosetRep_some_mul_weyl_not_borel p n t ht
    rw [show (M : Matrix (Fin 2) (Fin 2) (GaloisField p n)) =
      (auxiliaryElement p n (some t)).val *
        (auxiliaryElement p n (some 0)).val from
      Units.val_mul _ _] at h10
    simp [h10]
  obtain ⟨s, hs⟩ := hidx
  rw [hs, hfsome, mul_zero]

private lemma principalSeries_delta_spans_top
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (S : Subrepresentation (auxiliarySubmoduleRepresentation p n chi1 chi2))
    (g : ↥(auxiliarySubmodule p n chi1 chi2))
    (hgS : g ∈ S.toSubmodule)
    (hgnone : g.val (auxiliaryElement p n none) ≠ 0)
    (hgsome : ∀ t, g.val (auxiliaryElement p n (some t)) = 0) :
    S = ⊤ := by
  rw [eq_top_iff]
  intro f _
  set c₀ := g.val (auxiliaryElement p n none)
  set g' := c₀⁻¹ • g with g'_def
  have hg'S : g' ∈ S.toSubmodule := S.toSubmodule.smul_mem _ hgS
  have hg'_none : g'.val (auxiliaryElement p n none) = 1 := by
    simp only [g'_def, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hgnone
  have hg'_some : ∀ t, g'.val (auxiliaryElement p n (some t)) = 0 := by
    intro t
    simp [g'_def, Pi.smul_apply, smul_eq_mul, hgsome]
  set wg' := auxiliarySubmoduleRepresentation p n chi1 chi2
    (auxiliaryElement p n (some 0)) g' with wg'_def
  have hwg'S : wg' ∈ S.toSubmodule := S.apply_mem_toSubmodule _ hg'S
  have hwg'_none : wg'.val (auxiliaryElement p n none) = 0 := by
    rw [action_weyl_none]; exact hg'_some 0
  have hwg'_some_ne : ∀ t, t ≠ 0 →
      wg'.val (auxiliaryElement p n (some t)) = 0 :=
    fun t ht => action_weyl_some_ne_zero p n chi1 chi2 g'
      hg'_some t ht
  set α := wg'.val (auxiliaryElement p n (some 0))
  have hα_ne : α ≠ 0 := by
    change wg'.val (auxiliaryElement p n (some 0)) ≠ 0
    rw [show wg'.val (auxiliaryElement p n (some 0)) =
      g'.val (auxiliaryElement p n (some 0) *
        auxiliaryElement p n (some 0)) from rfl]
    obtain ⟨b, hbM⟩ := auxiliary_exists_factor_decomposition p n
      (auxiliaryElement p n (some 0) *
        auxiliaryElement p n (some 0))
    have hcov := g'.prop b (auxiliaryElement p n
      (auxiliaryOptionMap p n
        (auxiliaryElement p n (some 0) *
          auxiliaryElement p n (some 0))))
    rw [← hbM] at hcov; rw [hcov]
    have hidx : auxiliaryOptionMap p n
        (auxiliaryElement p n (some 0) *
          auxiliaryElement p n (some 0)) = none := by
      simp [auxiliaryOptionMap, auxiliaryElement,
        Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible,

        Matrix.mul_apply, Fin.sum_univ_two]
    rw [hidx, hg'_none]
    simp [auxiliaryComplexFunction]
  set rhs := f.val (auxiliaryElement p n none) • g' +
    ∑ t : GaloisField p n,
      f.val (auxiliaryElement p n (some t)) •
        (α⁻¹ • auxiliarySubmoduleRepresentation p n chi1 chi2
          (translationElt p n (-t)) wg')
  have hrhs_S : rhs ∈ S.toSubmodule := by
    apply S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ hg'S)
    apply S.toSubmodule.sum_mem; intro t _
    exact S.toSubmodule.smul_mem _
      (S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hwg'S))
  suffices heq : f = rhs by rwa [heq]
  have := auxiliarySubmodule_ext p n chi1 chi2 (f - rhs)
  rw [sub_eq_zero] at this; apply this
  intro i
  change f.val (auxiliaryElement p n i) -
    (f.val (auxiliaryElement p n none) • g' +
      ∑ t : GaloisField p n,
        f.val (auxiliaryElement p n (some t)) •
          (α⁻¹ • auxiliarySubmoduleRepresentation p n chi1 chi2
            (translationElt p n (-t)) wg')).val
      (auxiliaryElement p n i) = 0
  simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum,
    Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  cases i with
  | none =>
    rw [hg'_none, mul_one]
    simp_rw [action_translation_none p n chi1 chi2 wg']
    simp [hwg'_none]
  | some s =>
    rw [hg'_some, mul_zero, zero_add]
    simp_rw [action_translation_some p n chi1 chi2
      wg' (-_) s]
    conv_lhs =>
      arg 2; arg 2; ext t; rw [show s + -t = s - t from by ring]
    rw [show (∑ t : GaloisField p n,
        f.val (auxiliaryElement p n (some t)) *
          (α⁻¹ * wg'.val
            (auxiliaryElement p n (some (s - t))))) =
      f.val (auxiliaryElement p n (some s)) *
        (α⁻¹ * wg'.val (auxiliaryElement p n (some 0))) from by
      rw [← Finset.sum_subset (Finset.subset_univ {s})
        (fun t _ ht => by
          simp at ht
          rw [hwg'_some_ne (s - t)
            (sub_ne_zero.mpr (Ne.symm ht)), mul_zero, mul_zero])]
      simp [sub_self]]
    rw [inv_mul_cancel₀ hα_ne, mul_one, sub_self]

private lemma principalSeries_simple_of_ne
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (auxiliaryPairedRepresentation p n chi1 chi2) := by
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set ρ := auxiliarySubmoduleRepresentation p n chi1 chi2
  suffices IsSimpleModule (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule by
    haveI := this; exact simple_of_isSimpleModule_FDRep ρ
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  haveI : Nontrivial (Subrepresentation ρ) :=
    principalSeries_nontrivial p n chi1 chi2
  exact IsSimpleOrder.mk fun S => by
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · right
      have hSne : S.toSubmodule ≠ ⊥ := by
        intro heq; apply hS
        exact Subrepresentation.toSubmodule_injective heq
      rw [ne_eq, Submodule.eq_bot_iff] at hSne; push Not at hSne
      obtain ⟨f, hfS, hfne⟩ := hSne
      obtain ⟨g, hgS, hgnone, hgsome⟩ :=
        principalSeries_construct_delta_none p n chi1 chi2 hne S f hfS hfne
      exact principalSeries_delta_spans_top p n chi1 chi2 S g hgS hgnone hgsome

/-- The auxiliary paired representation is simple when its two monoid homomorphisms differ. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := primary)]
theorem auxiliaryPairedRepresentation_simple_of_ne
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) (hne : chi1 ≠ chi2) :
    Simple (auxiliaryPairedRepresentation p n chi1 chi2) :=
  principalSeries_simple_of_ne p n chi1 chi2 hne

private lemma principalSeries_eval_surjective
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : Option (GaloisField p n) → ℂ) :
    ∃ f : ↥(auxiliarySubmodule p n chi1 chi2),
      ∀ i, (f : GL2 p n → ℂ) (auxiliaryElement p n i) = c i :=
  ⟨⟨auxiliaryFunctionOnGroup p n chi1 chi2 c,
    auxiliaryFunctionOnGroup_mem p n chi1 chi2 c⟩,
   auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 c⟩

private lemma complementW_eval_injective
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(complementWSubmodule p n mu))
    (hf : ∀ t : GaloisField p n,
      (f : GL2 p n → ℂ) (auxiliaryElement p n (some t)) = 0) :
    f = 0 := by
  have hcov := f.prop.1  -- covariance
  have hker := f.prop.2  -- ker(augmentation)
  suffices h : ∀ i : Option (GaloisField p n),
      (f.val : GL2 p n → ℂ) (auxiliaryElement p n i) = 0 by
    have hinj := auxiliarySubmodule_ext p n mu mu
      ⟨f.val, hcov⟩ h
    exact Subtype.ext (show f.val = 0 from congr_arg Subtype.val hinj)
  intro i
  cases i with
  | some t => exact hf t
  | none =>
    have hf_zero_outside_B : ∀ g : GL2 p n,
        (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 →
        f.val g = 0 := by
      intro g hg10
      obtain ⟨b, hbg⟩ := auxiliary_exists_factor_decomposition p n g
      have hcov_g := hcov b (auxiliaryElement p n (auxiliaryOptionMap p n g))
      rw [← hbg] at hcov_g
      rw [hcov_g]
      have : auxiliaryOptionMap p n g =
          some ((g.val : Matrix _ _ _) 1 1 / (g.val : Matrix _ _ _) 1 0) := by
        simp [auxiliaryOptionMap, hg10]
      rw [this]
      rw [hf _, mul_zero]
    have hf_B_term : ∀ g : GL2 p n,
        (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 →
        f.val g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = f.val 1 := by
      intro g hg10
      have hcov_g := hcov ⟨g, hg10⟩ 1
      simp only [mul_one] at hcov_g ⊢
      rw [hcov_g]
      unfold auxiliaryComplexFunction
      have hdet_g : Matrix.GeneralLinearGroup.det g =
        Units.mk0 _ (auxiliary_eval_zero_zero_ne_zero p n ⟨g, hg10⟩) *
        Units.mk0 _ (auxiliary_eval_one_one_ne_zero p n ⟨g, hg10⟩) := by
        ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hg10]
      rw [hdet_g, map_mul, mul_inv_rev, Units.val_mul]
      simp only [Units.val_inv_eq_inv_val]
      have h1 : ((mu (Units.mk0 _
          (auxiliary_eval_one_one_ne_zero p n ⟨g, hg10⟩)) : ℂˣ) : ℂ) ≠ 0 :=
        Units.ne_zero _
      have h0 : ((mu (Units.mk0 _
          (auxiliary_eval_zero_zero_ne_zero p n ⟨g, hg10⟩)) : ℂˣ) : ℂ) ≠ 0 :=
        Units.ne_zero _
      field_simp
    have hker_val : ∑ g : GL2 p n,
        f.val g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 0 := by
      have := hker
      simp only [augmentation,
        LinearMap.coe_mk] at this
      exact this
    have hterm : ∀ g : GL2 p n,
        f.val g * ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ =
        if (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0
        then f.val 1
        else 0 := by
      intro g
      split_ifs with h10
      · exact hf_B_term g h10
      · rw [hf_zero_outside_B g h10, zero_mul]
    simp_rw [hterm] at hker_val
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul] at hker_val
    have hB_ne : ((Finset.univ.filter
        (fun g : GL2 p n =>
          (g.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0)).card : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact Finset.card_ne_zero.mpr ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
    exact (mul_eq_zero.mp hker_val).resolve_left hB_ne

private lemma complementW_eval_surjective
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (c : GaloisField p n → ℂ) :
    ∃ f : ↥(complementWSubmodule p n mu),
      ∀ t, (f : GL2 p n → ℂ) (auxiliaryElement p n (some t)) = c t := by
  let v : Option (GaloisField p n) → ℂ := fun i =>
    match i with
    | some t => c t
    | none => -∑ t, c t
  have hf_mem := auxiliaryFunctionOnGroup_mem p n mu mu v
  have hf_eval := auxiliaryFunctionOnGroup_auxiliaryElement p n mu mu v
  have hf_aug : auxiliaryFunctionOnGroup p n mu mu v ∈
      LinearMap.ker (augmentation p n mu) := by
    simp only [LinearMap.mem_ker, augmentation, LinearMap.coe_mk, AddHom.coe_mk]
    have hdet_rep : ∀ i : Option (GaloisField p n),
        Matrix.GeneralLinearGroup.det (auxiliaryElement p n i) = 1 := by
      intro i
      cases i with
      | none =>
        ext
        simp [auxiliaryElement, Matrix.GeneralLinearGroup.det]
      | some t =>
        ext
        simp [auxiliaryElement, Matrix.GeneralLinearGroup.det,
          Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
          Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    have hborel_cancel : ∀ b : ↥(auxiliarySubgroup p n),
        auxiliaryComplexFunction p n mu mu b *
        ((mu (Matrix.GeneralLinearGroup.det b.val))⁻¹ : ℂˣ) = 1 := by
      intro b
      have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
      have hdet_b : Matrix.GeneralLinearGroup.det b.val =
        Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
          (auxiliary_eval_zero_zero_ne_zero p n b) *
        Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
          (auxiliary_eval_one_one_ne_zero p n b) := by
        ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hb10]
      rw [hdet_b, map_mul]
      rw [Units.val_inv_eq_inv_val, Units.val_mul]
      simp only [auxiliaryComplexFunction]
      rw [mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))]
    have hterm : ∀ g : GL2 p n,
        auxiliaryFunctionOnGroup p n mu mu v g *
        ((mu (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) =
        v (auxiliaryOptionMap p n g) := by
      intro g
      simp only [auxiliaryFunctionOnGroup]
      have hdecomp := auxiliarySubgroupMap_decomposition p n g
      have hdet_g : Matrix.GeneralLinearGroup.det g =
          Matrix.GeneralLinearGroup.det (auxiliarySubgroupMap p n g).val *
          Matrix.GeneralLinearGroup.det
            (auxiliaryElement p n (auxiliaryOptionMap p n g)) := by
        conv_lhs => rw [hdecomp]
        exact map_mul _ _ _
      rw [hdet_g, hdet_rep, mul_one]
      rw [show auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n g) *
            v (auxiliaryOptionMap p n g) *
            ((mu (Matrix.GeneralLinearGroup.det
              (auxiliarySubgroupMap p n g).val))⁻¹ : ℂˣ) =
          (auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n g) *
            ((mu (Matrix.GeneralLinearGroup.det
              (auxiliarySubgroupMap p n g).val))⁻¹ : ℂˣ)) *
          v (auxiliaryOptionMap p n g) from by ring]
      rw [hborel_cancel, one_mul]
    simp_rw [hterm]
    have hv_sum : ∑ i : Option (GaloisField p n), v i = 0 := by
      simp only [Fintype.sum_option, v]
      simp [add_comm]
    let e : GL2 p n ≃ ↥(auxiliarySubgroup p n) × Option (GaloisField p n) :=
      { toFun := fun g => (auxiliarySubgroupMap p n g, auxiliaryOptionMap p n g)
        invFun := fun bi => bi.1.val * auxiliaryElement p n bi.2
        left_inv := fun g => by
          simp only
          exact (auxiliarySubgroupMap_decomposition p n g).symm
        right_inv := fun ⟨b, i⟩ => by
          simp only
          ext
          · -- cosetBorel(b * rep(i)) = b
            have := auxiliarySubgroupMap_mul p n b
                      (auxiliaryElement p n i)
            rw [this, auxiliarySubgroupMap_auxiliaryElement]
            simp
          · -- cosetIndex(b * rep(i)) = i
            rw [auxiliaryOptionMap_mul,
                auxiliaryOptionMap_auxiliaryElement] }
    rw [show (∑ g : GL2 p n, v (auxiliaryOptionMap p n g)) =
        ∑ bi : ↥(auxiliarySubgroup p n) × Option (GaloisField p n), v bi.2 from
      Fintype.sum_equiv e _ _ (fun g => by simp [e])]
    rw [Fintype.sum_prod_type]
    simp [hv_sum]
  exact ⟨⟨auxiliaryFunctionOnGroup p n mu mu v, ⟨hf_mem, hf_aug⟩⟩,
    fun t => hf_eval (some t)⟩

private lemma principalSeriesSubmodule_finrank [NeZero n]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ ↥(auxiliarySubmodule p n chi1 chi2) = p ^ n + 1 := by
  let evalMap : ↥(auxiliarySubmodule p n chi1 chi2) →ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) :=
    { toFun := fun f i => (f : GL2 p n → ℂ) (auxiliaryElement p n i)
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  have hinj : Function.Injective evalMap := by
    intro f g hfg
    have h : f - g = 0 := auxiliarySubmodule_ext p n chi1 chi2 (f - g)
      (fun i => by
        have := congr_fun hfg i
        simp [evalMap] at this
        simp [this])
    exact sub_eq_zero.mp h
  have hsurj : Function.Surjective evalMap := fun c =>
    ⟨⟨auxiliaryFunctionOnGroup p n chi1 chi2 c,
      auxiliaryFunctionOnGroup_mem p n chi1 chi2 c⟩,
     funext fun i => auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 c i⟩
  have heq := (LinearEquiv.ofBijective evalMap ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_pi_fintype] at heq
  simp only [Module.finrank_self] at heq
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at heq
  rw [heq, Fintype.card_option]
  congr 1
  rw [← Nat.card_eq_fintype_card, GaloisField.card p n (NeZero.ne n)]

/-- The auxiliary paired representation has the displayed finite dimension. -/
@[source_ref "Chapter5/Discussion_5.25.3" (role := primary),
  source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem auxiliaryPairedRepresentation_finrank [NeZero n]
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ (auxiliaryPairedRepresentation p n chi1 chi2).V = p ^ n + 1 := by
  change Module.finrank ℂ ↥(auxiliarySubmodule p n chi1 chi2) = p ^ n + 1
  exact principalSeriesSubmodule_finrank p n chi1 chi2

private lemma detFun_mem_principalSeries
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (fun g : GL2 p n => (mu (Matrix.GeneralLinearGroup.det g) : ℂ)) ∈
      auxiliarySubmodule p n mu mu := by
  intro b g
  simp only [auxiliaryComplexFunction]
  rw [show Matrix.GeneralLinearGroup.det (b.val * g) =
    Matrix.GeneralLinearGroup.det b.val * Matrix.GeneralLinearGroup.det g from map_mul _ _ _,
    map_mul, Units.val_mul]
  congr 1
  have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
  have hdet_eq : (Matrix.GeneralLinearGroup.det b.val : GaloisField p n) =
      (b.val.val : Matrix _ _ _) 0 0 * (b.val.val : Matrix _ _ _) 1 1 := by
    change (b.val.val : Matrix _ _ _).det = _
    rw [Matrix.det_fin_two, hb10, mul_zero, sub_zero]
  have : Matrix.GeneralLinearGroup.det b.val =
      Units.mk0 ((b.val.val : Matrix _ _ _) 0 0) (auxiliary_eval_zero_zero_ne_zero p n b) *
      Units.mk0 ((b.val.val : Matrix _ _ _) 1 1) (auxiliary_eval_one_one_ne_zero p n b) := by
    ext; simp [hdet_eq]
  rw [this, map_mul, Units.val_mul]

private lemma augmentation_detFun_ne_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    augmentation p n mu
      (fun g : GL2 p n => (mu (Matrix.GeneralLinearGroup.det g) : ℂ)) ≠ 0 := by
  simp only [augmentation, LinearMap.coe_mk, AddHom.coe_mk]
  have hone : ∀ g : GL2 p n,
      (mu (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = 1 := fun g => by
    rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _)]
  simp_rw [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

private noncomputable def augOnPrincipalSeries
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(auxiliarySubmodule p n mu mu) →ₗ[ℂ] ℂ :=
  (augmentation p n mu).comp (Submodule.subtype _)

private lemma ker_augOnPrincipalSeries_eq
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    LinearMap.ker (augOnPrincipalSeries p n mu) =
      (complementWSubmodule p n mu).comap
        (Submodule.subtype (auxiliarySubmodule p n mu mu)) := by
  ext ⟨f, hf⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap,
    augOnPrincipalSeries, LinearMap.comp_apply,
    complementWSubmodule, Submodule.mem_inf, LinearMap.mem_ker]
  exact ⟨fun h => ⟨hf, h⟩, fun ⟨_, h⟩ => h⟩

private lemma augOnPrincipalSeries_surjective
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Function.Surjective (augOnPrincipalSeries p n mu) := by
  intro c
  have hdetMem := detFun_mem_principalSeries p n mu
  set detFn : ↥(auxiliarySubmodule p n mu mu) :=
    ⟨fun g => (mu (Matrix.GeneralLinearGroup.det g) : ℂ), hdetMem⟩
  have haugNe := augmentation_detFun_ne_zero p n mu
  set a := augOnPrincipalSeries p n mu detFn with ha_def
  refine ⟨(c / a) • detFn, ?_⟩
  simp only [map_smul, smul_eq_mul]
  have ha_ne : a ≠ 0 := haugNe
  exact div_mul_cancel₀ c ha_ne

private lemma augOnPrincipalSeries_equivariant
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (g : GL2 p n)
    (f : ↥(auxiliarySubmodule p n mu mu)) :
    augOnPrincipalSeries p n mu
      (auxiliarySubmoduleRepresentation p n mu mu g f) =
    ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      augOnPrincipalSeries p n mu f := by
  simp only [augOnPrincipalSeries, LinearMap.comp_apply,
    augmentation, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_subtype]
  change ∑ x : GL2 p n, f.val (x * g) * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹ =
    ↑(mu (Matrix.GeneralLinearGroup.det g)) *
    (∑ x : GL2 p n, f.val x * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹)
  conv_lhs =>
    rw [Fintype.sum_equiv (Equiv.mulRight g)
        (fun x => f.val (x * g) * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹)
        (fun x => f.val x * ↑(mu (Matrix.GeneralLinearGroup.det (x * g⁻¹)))⁻¹)
        (fun x => by simp [Equiv.mulRight])]
  simp_rw [map_mul, mul_inv_rev, Units.val_mul]
  simp_rw [show ∀ x : GL2 p n,
      f.val x * (↑(mu (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ *
      ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹) =
      f.val x * ↑(mu (Matrix.GeneralLinearGroup.det x))⁻¹ *
      ↑(mu (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ from fun x => by ring]
  rw [← Finset.sum_mul, mul_comm]
  congr 1
  rw [map_inv, map_inv, inv_inv]

private noncomputable def augMorphism
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryPairedRepresentation p n mu mu ⟶ auxiliaryOtherRepresentation p n mu where
  hom := FGModuleCat.ofHom (augOnPrincipalSeries p n mu)
  comm g := by
    apply FGModuleCat.hom_ext
    ext ⟨f, hf⟩
    change augOnPrincipalSeries p n mu
      (auxiliarySubmoduleRepresentation p n mu mu g ⟨f, hf⟩) =
      ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        augOnPrincipalSeries p n mu ⟨f, hf⟩
    exact augOnPrincipalSeries_equivariant p n mu g ⟨f, hf⟩

private noncomputable def complementWInclusion
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryRepresentation p n mu ⟶ auxiliaryPairedRepresentation p n mu mu where
  hom := FGModuleCat.ofHom
    { toFun := fun ⟨f, hf⟩ => ⟨f, hf.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  comm g := by
    ext ⟨f, hf⟩; rfl

private noncomputable def detCharEmbedding
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryOtherRepresentation p n mu ⟶ auxiliaryPairedRepresentation p n mu mu where
  hom := FGModuleCat.ofHom
    { toFun := fun c =>
        ⟨fun g => c * (mu (Matrix.GeneralLinearGroup.det g) : ℂ),
         fun b g => by
           have := detFun_mem_principalSeries p n mu b g
           simp only [auxiliaryComplexFunction] at this ⊢; rw [this]; ring⟩
      map_add' := fun _ _ => Subtype.ext (funext fun _ => by simp [add_mul])
      map_smul' := fun _ _ => Subtype.ext (funext fun _ => by simp [mul_assoc]) }
  comm g := by
    apply FGModuleCat.hom_ext; ext1
    apply Subtype.ext; funext x
    change ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (1 : ℂ) *
      ↑(mu (Matrix.GeneralLinearGroup.det x)) =
      1 * ↑(mu (Matrix.GeneralLinearGroup.det (x * g)))
    simp only [smul_eq_mul, mul_one, one_mul, map_mul, Units.val_mul]; ring

private def detCharRep
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Representation ℂ (GL2 p n) ℂ where
  toFun g := ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((mu (Matrix.GeneralLinearGroup.det (a * b)) : ℂˣ) : ℂ) * x =
      ((mu (Matrix.GeneralLinearGroup.det a) : ℂˣ) : ℂ) *
      (((mu (Matrix.GeneralLinearGroup.det b) : ℂˣ) : ℂ) * x)
    rw [map_mul, map_mul, Units.val_mul, mul_assoc]

private lemma detChar_eq_of
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryOtherRepresentation p n mu = FDRep.of (detCharRep p n mu) := rfl

/-- The second auxiliary representation is simple. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := supporting)]
theorem auxiliaryOtherRepresentation_simple
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Simple (auxiliaryOtherRepresentation p n mu) := by
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  rw [detChar_eq_of]
  let ρ := detCharRep p n mu
  haveI : IsSimpleModule (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule := by
    rw [isSimpleModule_iff]
    refine is_simple_module_of_finrank_eq_one (K := ℂ) (A := MonoidAlgebra ℂ (GL2 p n))
      (V := ρ.asModule) ?_
    rw [ρ.asModuleEquiv.finrank_eq, Module.finrank_self]
  haveI : Simple (ModuleCat.of (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule) :=
    simple_of_isSimpleModule
  let E := Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := GL2 p n)
  haveI : Simple
      (E.functor.obj ((forget₂ (FDRep ℂ (GL2 p n)) (Rep ℂ (GL2 p n))).obj
        (FDRep.of ρ))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule)
    infer_instance
  haveI : Simple ((forget₂ (FDRep ℂ (GL2 p n)) (Rep ℂ (GL2 p n))).obj (FDRep.of ρ)) :=
    simple_of_full_faithful_preservesMono' E.functor _
  exact simple_of_full_faithful_preservesMono'
    (forget₂ (FDRep ℂ (GL2 p n)) (Rep ℂ (GL2 p n))) _

private def detCharEmbedding_linearMap
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    ℂ →ₗ[ℂ] ↥(auxiliarySubmodule p n mu mu) where
  toFun c := ⟨fun g => c * (mu (Matrix.GeneralLinearGroup.det g) : ℂ),
    fun b g => by
      have := detFun_mem_principalSeries p n mu b g
      simp only [auxiliaryComplexFunction] at this ⊢; rw [this]; ring⟩
  map_add' a b := Subtype.ext (funext fun _ => by simp [add_mul])
  map_smul' r c := Subtype.ext (funext fun _ => by simp [mul_assoc])

private lemma aug_comp_emb_eq
    (mu : (GaloisField p n)ˣ →* ℂˣ) (c : ℂ) :
    augOnPrincipalSeries p n mu
      (detCharEmbedding_linearMap p n mu c) =
    c * (Fintype.card (GL2 p n) : ℂ) := by
  simp only [augOnPrincipalSeries, LinearMap.comp_apply,
    augmentation, detCharEmbedding_linearMap,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype]
  simp_rw [show ∀ g : GL2 p n,
      c * ↑(mu (Matrix.GeneralLinearGroup.det g)) *
      ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ = c from fun g => by
    rw [mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), mul_one]]
  simp [Finset.sum_const, Finset.card_univ, mul_comm]

private lemma detCharEmbedding_ne_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    detCharEmbedding p n mu ≠ 0 := by
  intro h
  have h1 : (detCharEmbedding_linearMap p n mu 1).val (1 : GL2 p n) = 0 := by
    have hlin : detCharEmbedding_linearMap p n mu = 0 := by
      have hh : (detCharEmbedding p n mu).hom = 0 := by
        rw [h]; exact Action.zero_hom
      ext x
      have key : ∀ (c : ℂ) (g : GL2 p n),
          (detCharEmbedding_linearMap p n mu c).val g =
          (ConcreteCategory.hom
            (detCharEmbedding p n mu).hom.hom c :
            ↥(auxiliarySubmodule p n mu mu)).val g := by
        intro c g; rfl
      rw [key 1 x, hh]
      rfl
    simp [hlin]
  simp [detCharEmbedding_linearMap] at h1

private lemma detCharEmbedding_mono
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Mono (detCharEmbedding p n mu) := by
  haveI := auxiliaryOtherRepresentation_simple p n mu
  exact mono_of_nonzero_from_simple (detCharEmbedding_ne_zero p n mu)

private noncomputable def complementWProjection_toAmbient
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliarySubmodule p n mu mu →ₗ[ℂ] (GL2 p n → ℂ) where
  toFun := fun ⟨f, hf⟩ g =>
    f g - ((Fintype.card (GL2 p n) : ℂ)⁻¹ *
      augOnPrincipalSeries p n mu ⟨f, hf⟩) *
      (mu (Matrix.GeneralLinearGroup.det g) : ℂ)
  map_add' := fun ⟨a, ha⟩ ⟨b, hb⟩ => by
    funext g
    simp only [augOnPrincipalSeries, LinearMap.comp_apply,
      Submodule.coe_subtype, Pi.add_apply, LinearMap.map_add]
    ring
  map_smul' := fun r ⟨a, ha⟩ => by
    funext g
    simp only [smul_eq_mul, augOnPrincipalSeries, LinearMap.comp_apply,
      Submodule.coe_subtype, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
      LinearMap.map_smul]
    ring

private lemma complementWProjection_mem
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : auxiliarySubmodule p n mu mu) :
    complementWProjection_toAmbient p n mu f ∈
      complementWSubmodule p n mu := by
  obtain ⟨f, hf⟩ := f
  rw [complementWSubmodule, Submodule.mem_inf]
  simp only [complementWProjection_toAmbient, LinearMap.coe_mk, AddHom.coe_mk]
  refine ⟨?_, ?_⟩
  · -- Covariance: the projected function is still B-covariant with character λ.
    intro b g'
    have hcov := hf b g'
    have hdet := detFun_mem_principalSeries p n mu b g'
    simp only [auxiliaryComplexFunction] at hcov hdet ⊢
    rw [hcov, hdet]; ring
  · -- Zero augmentation.
    rw [LinearMap.mem_ker]
    simp only [augmentation, LinearMap.coe_mk, AddHom.coe_mk]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    simp_rw [show ∀ g : GL2 p n,
      (Fintype.card (GL2 p n) : ℂ)⁻¹ *
        augOnPrincipalSeries p n mu ⟨f, hf⟩ *
        ↑(mu (Matrix.GeneralLinearGroup.det g)) *
        ↑(mu (Matrix.GeneralLinearGroup.det g))⁻¹ =
      (Fintype.card (GL2 p n) : ℂ)⁻¹ *
        augOnPrincipalSeries p n mu ⟨f, hf⟩ from fun g => by
      rw [mul_assoc, mul_assoc, Units.val_inv_eq_inv_val,
        mul_inv_cancel₀ (Units.ne_zero _), mul_one]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
      one_mul]
    simp only [augOnPrincipalSeries, augmentation,
      LinearMap.comp_apply, Submodule.coe_subtype,
      LinearMap.coe_mk, AddHom.coe_mk, sub_self]

private noncomputable def complementWProjection_linearMap
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliarySubmodule p n mu mu →ₗ[ℂ]
      complementWSubmodule p n mu :=
  (complementWProjection_toAmbient p n mu).codRestrict _
    (complementWProjection_mem p n mu)

private lemma complementWProjection_comm
    (mu : (GaloisField p n)ˣ →* ℂˣ) (g : GL2 p n) :
    (complementWProjection_linearMap p n mu).comp
        ((auxiliarySubmoduleRepresentation p n mu mu g)) =
      (complementWRep p n mu g).comp
        (complementWProjection_linearMap p n mu) := by
  apply LinearMap.ext; intro ⟨f, hf⟩
  apply Subtype.ext; funext x
  change f (x * g) -
      (Fintype.card (GL2 p n) : ℂ)⁻¹ *
        augOnPrincipalSeries p n mu
          (auxiliarySubmoduleRepresentation p n mu mu g ⟨f, hf⟩) *
        ↑(mu (Matrix.GeneralLinearGroup.det x)) =
    f (x * g) -
      (Fintype.card (GL2 p n) : ℂ)⁻¹ *
        augOnPrincipalSeries p n mu ⟨f, hf⟩ *
        ↑(mu (Matrix.GeneralLinearGroup.det (x * g)))
  rw [augOnPrincipalSeries_equivariant]
  simp only [map_mul, Units.val_mul]
  ring

private noncomputable def complementWProjection
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryPairedRepresentation p n mu mu ⟶ auxiliaryRepresentation p n mu where
  hom := FGModuleCat.ofHom (complementWProjection_linearMap p n mu)
  comm g := by
    apply FGModuleCat.hom_ext
    exact complementWProjection_comm p n mu g

private noncomputable def scaledAugMorphism
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    auxiliaryPairedRepresentation p n mu mu ⟶ auxiliaryOtherRepresentation p n mu where
  hom := FGModuleCat.ofHom
    ((Fintype.card (GL2 p n) : ℂ)⁻¹ • augOnPrincipalSeries p n mu)
  comm g := by
    apply FGModuleCat.hom_ext; ext ⟨f, hf⟩
    change (Fintype.card (GL2 p n) : ℂ)⁻¹ *
      augOnPrincipalSeries p n mu
        (auxiliarySubmoduleRepresentation p n mu mu g ⟨f, hf⟩) =
      ((mu (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((Fintype.card (GL2 p n) : ℂ)⁻¹ *
          augOnPrincipalSeries p n mu ⟨f, hf⟩)
    rw [augOnPrincipalSeries_equivariant]; ring

private lemma emb_comp_scaledAug_eq_id
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    detCharEmbedding p n mu ≫
      scaledAugMorphism p n mu = 𝟙 _ := by
  refine Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun c => ?_)))
  change (Fintype.card (GL2 p n) : ℂ)⁻¹ *
    augOnPrincipalSeries p n mu
      (detCharEmbedding_linearMap p n mu c) = c
  rw [aug_comp_emb_eq]
  field_simp

private lemma total_condition
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    scaledAugMorphism p n mu ≫ detCharEmbedding p n mu +
      complementWProjection p n mu ≫ complementWInclusion p n mu =
      𝟙 _ := by
  refine Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun ⟨f, hf⟩ => ?_)))
  apply Subtype.ext; funext g
  change ((Fintype.card (GL2 p n) : ℂ)⁻¹ *
    augOnPrincipalSeries p n mu ⟨f, hf⟩) *
    ↑(mu (Matrix.GeneralLinearGroup.det g)) +
    (f g - (Fintype.card (GL2 p n) : ℂ)⁻¹ *
      augOnPrincipalSeries p n mu ⟨f, hf⟩ *
      ↑(mu (Matrix.GeneralLinearGroup.det g))) = f g
  ring

private lemma emb_comp_proj_eq_zero
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    detCharEmbedding p n mu ≫ complementWProjection p n mu = 0 := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, Action.zero_hom]
  apply FGModuleCat.hom_ext
  ext c
  apply Subtype.ext; funext g
  change (1 : ℂ) * ↑(mu (Matrix.GeneralLinearGroup.det g)) -
    (Fintype.card (GL2 p n) : ℂ)⁻¹ *
      augOnPrincipalSeries p n mu
        (detCharEmbedding_linearMap p n mu (1 : ℂ)) *
      ↑(mu (Matrix.GeneralLinearGroup.det g)) = 0
  rw [aug_comp_emb_eq, one_mul, one_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul, sub_self]

private lemma incl_comp_proj_eq_id
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    complementWInclusion p n mu ≫
      complementWProjection p n mu = 𝟙 _ := by
  refine Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun ⟨f, hf⟩ => ?_)))
  apply Subtype.ext; funext g
  change f g - (Fintype.card (GL2 p n) : ℂ)⁻¹ *
    augOnPrincipalSeries p n mu ⟨f, hf.1⟩ *
    ↑(mu (Matrix.GeneralLinearGroup.det g)) = f g
  have hker : augOnPrincipalSeries p n mu ⟨f, hf.1⟩ = 0 := by
    simp only [augOnPrincipalSeries, LinearMap.comp_apply, Submodule.coe_subtype]
    exact hf.2
  rw [hker, mul_zero, zero_mul, sub_zero]

/-- The diagonal auxiliary paired representation is isomorphic to a biproduct of two auxiliary representations. -/
lemma auxiliaryPairedRepresentation_iso_biprod
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (auxiliaryPairedRepresentation p n mu mu ≅
      auxiliaryOtherRepresentation p n mu ⊞ auxiliaryRepresentation p n mu) := by
  haveI : Simple (auxiliaryOtherRepresentation p n mu) := auxiliaryOtherRepresentation_simple p n mu
  have hne := detCharEmbedding_ne_zero p n mu
  set emb := detCharEmbedding p n mu
  set incl := complementWInclusion p n mu
  set proj := complementWProjection p n mu
  haveI : Mono emb := detCharEmbedding_mono p n mu
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  haveI : CategoryTheory.Injective (auxiliaryOtherRepresentation p n mu) := inferInstance
  haveI : IsSplitMono emb := IsSplitMono.mk'
    ⟨CategoryTheory.Injective.factorThru (𝟙 _) emb,
     CategoryTheory.Injective.comp_factorThru (𝟙 _) emb⟩
  have hcok := cokernelIsCokernel emb
  let bc := binaryBiconeOfIsSplitMonoOfCokernel hcok
  have hbl := isBilimitBinaryBiconeOfIsSplitMonoOfCokernel hcok
  haveI : HasBinaryBiproduct (auxiliaryOtherRepresentation p n mu) (cokernel emb) :=
    HasBinaryBiproduct.mk ⟨bc, hbl⟩
  have iso1 : auxiliaryPairedRepresentation p n mu mu ≅
    auxiliaryOtherRepresentation p n mu ⊞ cokernel emb :=
    biprod.uniqueUpToIso _ _ hbl
  let ψ : cokernel emb ⟶ auxiliaryRepresentation p n mu :=
    cokernel.desc emb proj (emb_comp_proj_eq_zero p n mu)
  let φ : auxiliaryRepresentation p n mu ⟶ cokernel emb := incl ≫ cokernel.π emb
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    simp only [φ, ψ, Category.assoc, cokernel.π_desc]
    exact incl_comp_proj_eq_id p n mu
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    set sAug := scaledAugMorphism p n mu
    have htotal := total_condition p n mu
    have hpi : proj ≫ incl = 𝟙 _ - sAug ≫ emb := by
      rw [eq_sub_iff_add_eq, add_comm]; exact htotal
    have hkey : proj ≫ (incl ≫ cokernel.π emb) = cokernel.π emb := by
      rw [← Category.assoc, hpi, Preadditive.sub_comp, Category.id_comp,
        Category.assoc, cokernel.condition, comp_zero, sub_zero]
    haveI : Epi (cokernel.π emb) := inferInstance
    apply (cancel_epi (cokernel.π emb)).mp
    rw [Category.comp_id]
    conv_lhs => rw [← Category.assoc (cokernel.π emb) ψ φ]
    show (cokernel.π emb ≫ ψ) ≫ φ = cokernel.π emb
    rw [cokernel.π_desc]
    exact hkey
  let cokIso : cokernel emb ≅ auxiliaryRepresentation p n mu :=
    ⟨ψ, φ, hψφ, hφψ⟩
  exact ⟨iso1.trans (biprod.mapIso (Iso.refl _) cokIso)⟩

private lemma complementW_none_eq_neg_sum
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(complementWSubmodule p n mu)) :
    f.val (auxiliaryElement p n none) =
    -(∑ t : GaloisField p n, f.val (auxiliaryElement p n (some t))) := by
  have hcov := f.prop.1  -- covariance
  have hker : f.val ∈ LinearMap.ker (augmentation p n mu) := f.prop.2
  rw [LinearMap.mem_ker] at hker
  simp only [augmentation, LinearMap.coe_mk, AddHom.coe_mk] at hker
  have hdet_rep : ∀ i : Option (GaloisField p n),
      Matrix.GeneralLinearGroup.det (auxiliaryElement p n i) = 1 := by
    intro i; cases i with
    | none => ext; simp [auxiliaryElement, Matrix.GeneralLinearGroup.det]
    | some t => ext; simp [auxiliaryElement, Matrix.GeneralLinearGroup.det,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.det_fin_two]
  have hborel_cancel : ∀ b : ↥(auxiliarySubgroup p n),
      auxiliaryComplexFunction p n mu mu b *
      ((mu (Matrix.GeneralLinearGroup.det b.val))⁻¹ : ℂˣ) = 1 := by
    intro b
    have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
    have hdet_b : Matrix.GeneralLinearGroup.det b.val =
      Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
        (auxiliary_eval_zero_zero_ne_zero p n b) *
      Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
        (auxiliary_eval_one_one_ne_zero p n b) := by
      ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hb10]
    rw [hdet_b, map_mul]
    rw [Units.val_inv_eq_inv_val, Units.val_mul]
    simp only [auxiliaryComplexFunction]
    rw [mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))]
  have hterm : ∀ g : GL2 p n,
      f.val g * ((mu (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) =
      f.val (auxiliaryElement p n (auxiliaryOptionMap p n g)) := by
    intro g
    have hdecomp := auxiliarySubgroupMap_decomposition p n g
    have hdet_g : Matrix.GeneralLinearGroup.det g =
        Matrix.GeneralLinearGroup.det (auxiliarySubgroupMap p n g).val *
        Matrix.GeneralLinearGroup.det
          (auxiliaryElement p n (auxiliaryOptionMap p n g)) := by
      conv_lhs => rw [hdecomp]; exact map_mul _ _ _
    rw [hdet_g, hdet_rep, mul_one]
    have hcov_g := hcov (auxiliarySubgroupMap p n g)
      (auxiliaryElement p n (auxiliaryOptionMap p n g))
    rw [← hdecomp] at hcov_g
    rw [hcov_g]
    rw [show auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n g) *
          f.val (auxiliaryElement p n (auxiliaryOptionMap p n g)) *
          ((mu (Matrix.GeneralLinearGroup.det
            (auxiliarySubgroupMap p n g).val))⁻¹ : ℂˣ) =
        (auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n g) *
          ((mu (Matrix.GeneralLinearGroup.det
            (auxiliarySubgroupMap p n g).val))⁻¹ : ℂˣ)) *
        f.val (auxiliaryElement p n (auxiliaryOptionMap p n g)) from by ring]
    rw [hborel_cancel, one_mul]
  simp_rw [hterm] at hker
  let e : GL2 p n ≃ ↥(auxiliarySubgroup p n) × Option (GaloisField p n) :=
    { toFun := fun g => (auxiliarySubgroupMap p n g, auxiliaryOptionMap p n g)
      invFun := fun bi => bi.1.val * auxiliaryElement p n bi.2
      left_inv := fun g => by
        simp only
        exact (auxiliarySubgroupMap_decomposition p n g).symm
      right_inv := fun ⟨b, i⟩ => by
        simp only
        ext
        · have := auxiliarySubgroupMap_mul p n b (auxiliaryElement p n i)
          rw [this, auxiliarySubgroupMap_auxiliaryElement]; simp
        · rw [auxiliaryOptionMap_mul, auxiliaryOptionMap_auxiliaryElement] }
  rw [show (∑ g : GL2 p n, f.val (auxiliaryElement p n
      (auxiliaryOptionMap p n g))) =
    ∑ bi : ↥(auxiliarySubgroup p n) × Option (GaloisField p n),
      f.val (auxiliaryElement p n bi.2) from
    Fintype.sum_equiv e _ _ (fun g => by simp [e])] at hker
  rw [Fintype.sum_prod_type] at hker
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hker
  have hB_ne : (Fintype.card ↥(auxiliarySubgroup p n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hsum_zero : ∑ i : Option (GaloisField p n),
      f.val (auxiliaryElement p n i) = 0 := by
    rcases mul_eq_zero.mp hker with h | h
    · exact absurd h hB_ne
    · exact h
  rw [Fintype.sum_option] at hsum_zero
  linear_combination hsum_zero

private lemma complementW_weyl_const_ne
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(complementWSubmodule p n mu))
    (σ : ℂ)
    (hconst : ∀ t : GaloisField p n,
      f.val (auxiliaryElement p n (some t)) = σ)
    (t : GaloisField p n) (ht : t ≠ 0) :
    (complementWRep p n mu (auxiliaryElement p n (some 0)) f).val
      (auxiliaryElement p n (some t)) = σ := by
  change f.val (auxiliaryElement p n (some t) *
    auxiliaryElement p n (some 0)) = σ
  set M := auxiliaryElement p n (some t) * auxiliaryElement p n (some 0)
  have h10 := cosetRep_some_mul_weyl_not_borel p n t ht
  have hM10 : (M.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 ≠ 0 := by
    change ((auxiliaryElement p n (some t)).val *
      (auxiliaryElement p n (some 0)).val : Matrix _ _ _) 1 0 ≠ 0
    exact h10
  have hidx : ∃ s, auxiliaryOptionMap p n M = some s := by
    unfold auxiliaryOptionMap
    simp [hM10]
  obtain ⟨s, hs⟩ := hidx
  have hcov_f := f.prop.1
  have hcov_app := hcov_f (auxiliarySubgroupMap p n M)
    (auxiliaryElement p n (auxiliaryOptionMap p n M))
  rw [← auxiliarySubgroupMap_decomposition p n M] at hcov_app
  rw [hcov_app, hs, hconst s]
  suffices auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n M) = 1 by
    rw [this, one_mul]
  set b := auxiliarySubgroupMap p n M
  have hb10 : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := b.prop
  have hdet_b : Matrix.GeneralLinearGroup.det b.val =
    Units.mk0 ((b.val.val : Matrix _ _ _) 0 0) (auxiliary_eval_zero_zero_ne_zero p n b) *
    Units.mk0 ((b.val.val : Matrix _ _ _) 1 1) (auxiliary_eval_one_one_ne_zero p n b) := by
    ext; simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_two, hb10]
  have hdet_M : Matrix.GeneralLinearGroup.det M = 1 := by
    simp only [M]
    rw [map_mul]
    have h1 : Matrix.GeneralLinearGroup.det (auxiliaryElement p n (some t)) = 1 := by
      ext; simp [auxiliaryElement, Matrix.GeneralLinearGroup.det,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    have h2 : Matrix.GeneralLinearGroup.det (auxiliaryElement p n (some 0)) = 1 := by
      ext; simp [auxiliaryElement, Matrix.GeneralLinearGroup.det,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
        Matrix.unitOfDetInvertible, Matrix.det_fin_two]
    rw [h1, h2, mul_one]
  have hdet_rep_s : Matrix.GeneralLinearGroup.det (auxiliaryElement p n (some s)) = 1 := by
    ext; simp [auxiliaryElement, Matrix.GeneralLinearGroup.det,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.det_fin_two]
  have hdet_b_one : Matrix.GeneralLinearGroup.det b.val = 1 := by
    have hdecomp := auxiliarySubgroupMap_decomposition p n M
    rw [hs] at hdecomp
    have : Matrix.GeneralLinearGroup.det M =
      Matrix.GeneralLinearGroup.det b.val *
      Matrix.GeneralLinearGroup.det (auxiliaryElement p n (some s)) := by
      conv_lhs => rw [hdecomp]; rw [map_mul]
    rw [hdet_M, hdet_rep_s, mul_one] at this
    exact this.symm
  unfold auxiliaryComplexFunction
  rw [hdet_b] at hdet_b_one
  have hprod : Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
      (auxiliary_eval_zero_zero_ne_zero p n b) *
    Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
      (auxiliary_eval_one_one_ne_zero p n b) = 1 := hdet_b_one
  have hmu : (mu (Units.mk0 ((b.val.val : Matrix _ _ _) 0 0)
      (auxiliary_eval_zero_zero_ne_zero p n b)) : ℂˣ) *
    (mu (Units.mk0 ((b.val.val : Matrix _ _ _) 1 1)
      (auxiliary_eval_one_one_ne_zero p n b)) : ℂˣ) = 1 := by
    rw [← map_mul, hprod, map_one]
  have := congr_arg Units.val hmu
  simp only [Units.val_mul, Units.val_one] at this
  convert this using 1

private lemma complementW_weyl_zero_eval
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(complementWSubmodule p n mu)) :
    (complementWRep p n mu (auxiliaryElement p n (some 0)) f).val
      (auxiliaryElement p n (some 0)) =
    f.val (auxiliaryElement p n none) := by
  change f.val (auxiliaryElement p n (some 0) *
    auxiliaryElement p n (some 0)) = f.val (auxiliaryElement p n none)
  set w2 := auxiliaryElement p n (some 0) * auxiliaryElement p n (some 0)
  have hw2_borel : (w2.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
    simp [w2, auxiliaryElement, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.mul_apply, Fin.sum_univ_two]
  have hcov_f := f.prop.1  -- f.val ∈ principalSeriesSubmodule = covariant
  have hidx : auxiliaryOptionMap p n w2 = none := by
    unfold auxiliaryOptionMap; simp [hw2_borel]
  have hcb : (auxiliarySubgroupMap p n w2).val = w2 := by
    have := auxiliarySubgroupMap_decomposition p n w2
    rw [hidx] at this; simp [auxiliaryElement] at this; exact this.symm
  have hcov_app := hcov_f (auxiliarySubgroupMap p n w2)
    (auxiliaryElement p n none)
  rw [show (auxiliarySubgroupMap p n w2).val * auxiliaryElement p n none = w2 from by
    rw [hcb]; simp [auxiliaryElement]] at hcov_app
  rw [hcov_app]
  have h00 : ((auxiliarySubgroupMap p n w2).val.val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 = -1 := by
    rw [show (auxiliarySubgroupMap p n w2).val = w2 from hcb]
    simp [w2, auxiliaryElement, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((auxiliarySubgroupMap p n w2).val.val :
      Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 = -1 := by
    rw [show (auxiliarySubgroupMap p n w2).val = w2 from hcb]
    simp [w2, auxiliaryElement, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,
      Matrix.mul_apply, Fin.sum_univ_two]
  change auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n w2) *
    f.val (auxiliaryElement p n none) = f.val (auxiliaryElement p n none)
  have hbcv : auxiliaryComplexFunction p n mu mu (auxiliarySubgroupMap p n w2) = 1 := by
    unfold auxiliaryComplexFunction
    have h00' : Units.mk0 (((auxiliarySubgroupMap p n w2).val.val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0)
        (auxiliary_eval_zero_zero_ne_zero p n _) = -1 := by
      ext; simp [h00]
    have h11' : Units.mk0 (((auxiliarySubgroupMap p n w2).val.val :
        Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1)
        (auxiliary_eval_one_one_ne_zero p n _) = -1 := by
      ext; simp [h11]
    simp only [h00', h11']
    simp [← Units.val_mul, ← map_mul]
  rw [hbcv, one_mul]

private lemma complementW_simple
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Simple (auxiliaryRepresentation p n mu) := by
  haveI : NeZero (Nat.card (GL2 p n) : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  set ρ := complementWRep p n mu
  suffices IsSimpleModule (MonoidAlgebra ℂ (GL2 p n)) ρ.asModule by
    haveI := this; exact simple_of_isSimpleModule_FDRep ρ
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  haveI : Nontrivial (Subrepresentation ρ) := by
    obtain ⟨f, hf⟩ := complementW_eval_surjective p n mu
      (fun t => if t = (0 : GaloisField p n) then 1 else 0)
    have hfne : f ≠ 0 := by
      intro h; rw [h] at hf; simp at hf
    exact nontrivial_of_ne ⊥ ⊤ (by
      intro heq; apply hfne
      have : f ∈ (⊥ : Subrepresentation ρ).toSubmodule := heq ▸ Submodule.mem_top
      exact (Submodule.mem_bot ℂ).mp this)
  exact IsSimpleOrder.mk fun S => by
    by_cases hS : S = ⊥
    · exact Or.inl hS
    · right
      have hSne : S.toSubmodule ≠ ⊥ := by
        intro heq; exact hS (Subrepresentation.toSubmodule_injective heq)
      rw [ne_eq, Submodule.eq_bot_iff] at hSne; push Not at hSne
      obtain ⟨f, hfS, hfne⟩ := hSne
      have hsome : ∃ t₀, f.val (auxiliaryElement p n (some t₀)) ≠ 0 := by
        by_contra hall; push Not at hall
        exact hfne (complementW_eval_injective p n mu f hall)
      obtain ⟨t₀, ht₀⟩ := hsome
      set f' := ρ (translationElt p n t₀) f
      have hf'S : f' ∈ S.toSubmodule := S.apply_mem_toSubmodule _ hfS
      have hf'_eval0 : f'.val (auxiliaryElement p n (some 0)) ≠ 0 := by
        change f.val (auxiliaryElement p n (some 0) *
          translationElt p n t₀) ≠ 0
        rw [cosetRep_mul_translation_some, zero_add]
        exact ht₀
      set σ₀ := ∑ t : GaloisField p n, f'.val (auxiliaryElement p n (some t))
      obtain ⟨g, hgS, hg_sum_ne⟩ : ∃ g ∈ S.toSubmodule,
          ∑ t : GaloisField p n, g.val (auxiliaryElement p n (some t)) ≠ 0 := by
        by_cases hσ : σ₀ ≠ 0
        · exact ⟨f', hf'S, hσ⟩
        · push Not at hσ
          have hf'_none : f'.val (auxiliaryElement p n none) = 0 := by
            rw [complementW_none_eq_neg_sum]
            change -σ₀ = 0
            rw [hσ, neg_zero]
          set g := ρ (auxiliaryElement p n (some 0)) f'
          refine ⟨g, S.apply_mem_toSubmodule _ hf'S, ?_⟩
          rw [show ∑ t, g.val (auxiliaryElement p n (some t)) =
            -(g.val (auxiliaryElement p n none)) from by
            rw [complementW_none_eq_neg_sum]; ring]
          change -(f'.val (auxiliaryElement p n none *
            auxiliaryElement p n (some 0))) ≠ 0
          rw [show auxiliaryElement p n none * auxiliaryElement p n (some 0) =
            auxiliaryElement p n (some 0) from by simp [auxiliaryElement]]
          exact neg_ne_zero.mpr hf'_eval0
      set σ := ∑ t : GaloisField p n, g.val (auxiliaryElement p n (some t))
      set A := ∑ s : GaloisField p n, ρ (translationElt p n s) g
      have hAS : A ∈ S.toSubmodule :=
        S.toSubmodule.sum_mem (fun s _ => S.apply_mem_toSubmodule _ hgS)
      have hA_const : ∀ t : GaloisField p n,
          A.val (auxiliaryElement p n (some t)) = σ := by
        intro t
        simp only [A, Submodule.coe_sum, Finset.sum_apply]
        simp_rw [show ∀ s, (ρ (translationElt p n s) g).val
          (auxiliaryElement p n (some t)) =
          g.val (auxiliaryElement p n (some (t + s))) from
          fun s => by change g.val (auxiliaryElement p n (some t) *
            translationElt p n s) = _; rw [cosetRep_mul_translation_some]]
        exact Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun s => rfl)
      have hσ_ne : σ ≠ 0 := hg_sum_ne
      have hA_none : A.val (auxiliaryElement p n none) =
          -(Fintype.card (GaloisField p n) : ℂ) * σ := by
        rw [complementW_none_eq_neg_sum]
        simp_rw [hA_const]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, neg_mul]
      set w := auxiliaryElement p n (some 0)
      set wA := ρ w A
      have hwAS : wA ∈ S.toSubmodule := S.apply_mem_toSubmodule _ hAS
      have hwA_ne : ∀ t : GaloisField p n, t ≠ 0 →
          wA.val (auxiliaryElement p n (some t)) = σ :=
        fun t ht => complementW_weyl_const_ne p n mu A σ hA_const t ht
      have hwA_zero : wA.val (auxiliaryElement p n (some 0)) =
          -(Fintype.card (GaloisField p n) : ℂ) * σ := by
        rw [complementW_weyl_zero_eval]; exact hA_none
      set h := wA - A
      have hhS : h ∈ S.toSubmodule := S.toSubmodule.sub_mem hwAS hAS
      have hh_ne : ∀ t : GaloisField p n, t ≠ 0 →
          h.val (auxiliaryElement p n (some t)) = 0 := by
        intro t ht
        change wA.val (auxiliaryElement p n (some t)) -
          A.val (auxiliaryElement p n (some t)) = 0
        rw [hwA_ne t ht, hA_const t, sub_self]
      have hh_zero_ne : h.val (auxiliaryElement p n (some 0)) ≠ 0 := by
        change wA.val (auxiliaryElement p n (some 0)) -
          A.val (auxiliaryElement p n (some 0)) ≠ 0
        rw [hwA_zero, hA_const]
        intro heq
        apply hσ_ne
        have h1 : -(Fintype.card (GaloisField p n) : ℂ) * σ - σ = 0 := heq
        have h2 : -((Fintype.card (GaloisField p n) : ℂ) + 1) * σ = 0 := by
          have : -((Fintype.card (GaloisField p n) : ℂ) + 1) * σ =
              -(Fintype.card (GaloisField p n) : ℂ) * σ - σ := by ring
          rw [this]; exact h1
        have hqp1 : ((Fintype.card (GaloisField p n) : ℂ) + 1) ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        rcases mul_eq_zero.mp h2 with hq | hσ
        · exact absurd (neg_eq_zero.mp hq) hqp1
        · exact hσ
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm le_top
      intro x _
      set α := h.val (auxiliaryElement p n (some 0))
      have hα_ne : α ≠ 0 := hh_zero_ne
      set rhs := ∑ u : GaloisField p n,
        (α⁻¹ * x.val (auxiliaryElement p n (some u))) •
          ρ (translationElt p n (-u)) h
      have hrhs_S : rhs ∈ S.toSubmodule := by
        apply S.toSubmodule.sum_mem; intro u _
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hhS)
      suffices heq : x = rhs by rw [heq]; exact hrhs_S
      have hxrhs := complementW_eval_injective p n mu (x - rhs)
      rw [sub_eq_zero] at hxrhs; apply hxrhs; intro t
      change x.val (auxiliaryElement p n (some t)) -
        (∑ u : GaloisField p n,
          (α⁻¹ * x.val (auxiliaryElement p n (some u))) •
            ρ (translationElt p n (-u)) h).val
          (auxiliaryElement p n (some t)) = 0
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      simp_rw [show ∀ u, (ρ (translationElt p n (-u)) h).val
        (auxiliaryElement p n (some t)) =
        h.val (auxiliaryElement p n (some (t + (-u)))) from fun u => by
        change h.val (auxiliaryElement p n (some t) *
          translationElt p n (-u)) = _
        rw [cosetRep_mul_translation_some]]
      conv_lhs => arg 2; arg 2; ext u; rw [show t + -u = t - u from by ring]
      rw [show (∑ u : GaloisField p n,
          α⁻¹ * x.val (auxiliaryElement p n (some u)) *
          h.val (auxiliaryElement p n (some (t - u)))) =
        α⁻¹ * x.val (auxiliaryElement p n (some t)) *
          h.val (auxiliaryElement p n (some 0)) from by
        rw [← Finset.sum_subset (Finset.subset_univ {t}) (fun u _ hu => by
          simp only [Finset.mem_singleton] at hu
          rw [hh_ne (t - u) (sub_ne_zero.mpr (Ne.symm hu)), mul_zero])]
        simp [sub_self]]
      rw [show h.val (auxiliaryElement p n (some 0)) = α from rfl]
      rw [mul_comm (α⁻¹) _, mul_assoc, inv_mul_cancel₀ hα_ne, mul_one, sub_self]

private noncomputable def complementW_evalMap
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    ↥(complementWSubmodule p n mu) →ₗ[ℂ] (GaloisField p n → ℂ) where
  toFun f t := (f : GL2 p n → ℂ) (auxiliaryElement p n (some t))
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp [smul_eq_mul]

private lemma complementW_finrank
    (hn : 0 < n)
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    Module.finrank ℂ (auxiliaryRepresentation p n mu).V = p ^ n := by
  have hinj : Function.Injective (complementW_evalMap p n mu) := by
    intro f g heq
    have : f - g = 0 := by
      apply complementW_eval_injective
      intro t
      have := congr_fun heq t
      simp [complementW_evalMap] at this
      simp [this]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (complementW_evalMap p n mu) := by
    intro c
    obtain ⟨f, hf⟩ := complementW_eval_surjective p n mu c
    exact ⟨f, funext hf⟩
  have hequiv : ↥(complementWSubmodule p n mu) ≃ₗ[ℂ] (GaloisField p n → ℂ) :=
    LinearEquiv.ofBijective (complementW_evalMap p n mu) ⟨hinj, hsurj⟩
  change Module.finrank ℂ ↥(complementWSubmodule p n mu) = p ^ n
  rw [hequiv.finrank_eq, Module.finrank_pi_fintype, Module.finrank_self]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_univ, Fintype.card_eq_nat_card, GaloisField.card p n (Nat.pos_iff_ne_zero.mp hn)]

/-- A positive index gives the displayed decomposition, simplicity, and dimension properties for auxiliary representations. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := primary)]
theorem auxiliary_representation_summary_of_pos
    (hn : 0 < n)
    (mu : (GaloisField p n)ˣ →* ℂˣ) :
    (Nonempty (auxiliaryPairedRepresentation p n mu mu ≅
      auxiliaryOtherRepresentation p n mu ⊞ auxiliaryRepresentation p n mu)) ∧
    Simple (auxiliaryRepresentation p n mu) ∧
    Module.finrank ℂ (auxiliaryRepresentation p n mu).V = p ^ n :=
  ⟨auxiliaryPairedRepresentation_iso_biprod p n mu,
   complementW_simple p n mu,
   complementW_finrank p n hn mu⟩

private lemma complementW_action_diagonal_some
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(complementWSubmodule p n mu))
    (c : (GaloisField p n)ˣ) (t : GaloisField p n) :
    (complementWRep p n mu (diagElt p n c) f).val
      (auxiliaryElement p n (some t)) =
    (mu c : ℂ) * f.val (auxiliaryElement p n (some (t * ↑c⁻¹))) := by
  change f.val (auxiliaryElement p n (some t) * diagElt p n c) = _
  set bmat : Matrix (Fin 2) (Fin 2) (GaloisField p n) :=
    !![1, 0; 0, (c : GaloisField p n)]
  have hbdet : bmat.det ≠ 0 := by
    simp [bmat, Matrix.det_fin_two, Units.ne_zero]
  set b := Matrix.GeneralLinearGroup.mkOfDetNeZero bmat hbdet
  have hb_mem : b.val 1 0 = 0 := by
    simp [b, bmat, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible]
  have hprod : auxiliaryElement p n (some t) * diagElt p n c =
      b * auxiliaryElement p n (some (t * ↑c⁻¹)) := by
    apply Matrix.GeneralLinearGroup.ext; intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      auxiliaryElement, diagElt, b, bmat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two]
    have hc_ne : (c : GaloisField p n) ≠ 0 := Units.ne_zero c
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
  rw [hprod]
  have hcov := f.prop.1 ⟨b, hb_mem⟩ (auxiliaryElement p n (some (t * ↑c⁻¹)))
  rw [hcov]
  congr 1
  simp [auxiliaryComplexFunction, b, bmat,
    Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
    Matrix.unitOfDetInvertible]

private noncomputable def permAction
    (c : (GaloisField p n)ˣ) :
    (GaloisField p n → ℂ) →ₗ[ℂ] (GaloisField p n → ℂ) where
  toFun f t := f (t * ↑c⁻¹)
  map_add' f g := by ext t; simp [Pi.add_apply]
  map_smul' r f := by ext t; simp [Pi.smul_apply, smul_eq_mul]

set_option maxHeartbeats 800000 in
private lemma trace_permAction
    (c : (GaloisField p n)ˣ) (hc : c ≠ 1) :
    LinearMap.trace ℂ (GaloisField p n → ℂ) (permAction p n c) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (GaloisField p n))]
  simp only [Matrix.trace, Matrix.diag]
  have hcinv_ne_one : (↑c⁻¹ : GaloisField p n) ≠ 1 := by
    intro h
    apply hc
    have : c⁻¹ = 1 := Units.val_eq_one.mp h
    rw [inv_eq_one] at this
    exact this
  have hfixed : ∀ i : GaloisField p n, i * ↑c⁻¹ = i ↔ i = 0 := by
    intro i
    constructor
    · intro h
      by_contra hi
      apply hcinv_ne_one
      have : i * ↑c⁻¹ = i * 1 := by rw [mul_one]; exact h
      exact mul_left_cancel₀ hi this
    · intro h; rw [h, zero_mul]
  have hentry : ∀ i : GaloisField p n,
      (Pi.basisFun ℂ (GaloisField p n)).repr
        (permAction p n c ((Pi.basisFun ℂ (GaloisField p n)) i)) i =
      if i = 0 then (1 : ℂ) else 0 := by
    intro i
    simp only [Pi.basisFun_apply, Pi.basisFun_repr, permAction,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, hfixed]
  simp_rw [LinearMap.toMatrix_apply, hentry]
  simp [Finset.sum_ite_eq', Finset.mem_univ]

set_option maxHeartbeats 800000 in
private lemma complementW_char_diagElt
    (mu : (GaloisField p n)ˣ →* ℂˣ)
    (c : (GaloisField p n)ˣ) (hc : c ≠ 1) :
    FDRep.character (auxiliaryRepresentation p n mu)
      (diagElt p n c) = (mu c : ℂ) := by
  simp only [FDRep.character]
  have hinj : Function.Injective (complementW_evalMap p n mu) := by
    intro f g heq
    have : f - g = 0 := by
      apply complementW_eval_injective
      intro t
      have := congr_fun heq t
      simp [complementW_evalMap] at this
      simp [this]
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (complementW_evalMap p n mu) := by
    intro c
    obtain ⟨f, hf⟩ := complementW_eval_surjective p n mu c
    exact ⟨f, funext hf⟩
  set e := LinearEquiv.ofBijective (complementW_evalMap p n mu) ⟨hinj, hsurj⟩
  rw [show (LinearMap.trace ℂ _)
      ((auxiliaryRepresentation p n mu).ρ (diagElt p n c)) =
    (LinearMap.trace ℂ _) (e.conj
      ((auxiliaryRepresentation p n mu).ρ (diagElt p n c))) from
    (LinearMap.trace_conj' _ e).symm]
  have hconj : e.conj ((auxiliaryRepresentation p n mu).ρ (diagElt p n c)) =
      (mu c : ℂ) • permAction p n c := by
    apply LinearMap.ext; intro g
    apply funext; intro t
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      permAction, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul,
      Pi.smul_apply]
    have hact := complementW_action_diagonal_some p n mu (e.symm g) c t
    change (complementWRep p n mu (diagElt p n c) (e.symm g)).val
      (auxiliaryElement p n (some t)) = _
    rw [hact]
    congr 1
    exact congr_fun (e.apply_symm_apply g) (t * ↑c⁻¹)
  rw [hconj, map_smul, trace_permAction p n c hc, smul_eq_mul, mul_one]

private lemma complementW_iso_implies_eq
    (mu nu : (GaloisField p n)ˣ →* ℂˣ)
    (iso : auxiliaryRepresentation p n mu ≅ auxiliaryRepresentation p n nu) :
    mu = nu := by
  have hchar : FDRep.character (auxiliaryRepresentation p n mu) =
    FDRep.character (auxiliaryRepresentation p n nu) := FDRep.char_iso iso
  ext c
  by_cases hc : c = 1
  · subst hc; simp
  · have h1 := complementW_char_diagElt p n mu c hc
    have h2 := complementW_char_diagElt p n nu c hc
    have h3 := congr_fun hchar (diagElt p n c)
    rw [h1, h2] at h3
    exact_mod_cast h3

/-- Two auxiliary representations are isomorphic exactly when their associated monoid homomorphisms agree. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := primary)]
theorem auxiliaryRepresentation_iso_iff
    (mu nu : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (auxiliaryRepresentation p n mu ≅ auxiliaryRepresentation p n nu) ↔
    mu = nu := by
  constructor
  · rintro ⟨iso⟩
    exact complementW_iso_implies_eq p n mu nu iso
  · rintro rfl
    exact ⟨Iso.refl _⟩

private lemma sum_nontrivial_char_eq_zero
    {G : Type*} [CommGroup G] [Fintype G]
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  have ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h; push Not at h; exact absurd (MonoidHom.ext h) hχ
  have hne : (χ g₀ : ℂ) ≠ 1 := fun h => hg₀ (Units.val_injective h)
  have key : (χ g₀ : ℂ) * ∑ g, (χ g : ℂ) = ∑ g, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (fun g => g₀ * g)
    · intro g _; exact Finset.mem_univ _
    · intro g₁ _ g₂ _ h; exact mul_left_cancel h
    · intro g _; exact ⟨g₀⁻¹ * g, Finset.mem_univ _, by group⟩
    · intro g _; simp only [map_mul, Units.val_mul]
  have h1 : ((χ g₀ : ℂ) - 1) * ∑ g, (χ g : ℂ) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hne)

private lemma cosetRep_some_mul_borel_factor
    (u : GaloisField p n) (b : ↥(auxiliarySubgroup p n)) :
    let bm := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
    let a := bm 0 0
    let d := bm 1 1
    let c := bm 0 1
    let v := (c + u * d) / a
    ∃ b' : ↥(auxiliarySubgroup p n),
      auxiliaryElement p n (some u) * b.val = b'.val *
        auxiliaryElement p n (some v) ∧
      (b'.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 = d ∧
      (b'.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 1 = a := by
  set bm := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set a := bm 0 0
  set d := bm 1 1
  set c := bm 0 1
  set v := (c + u * d) / a
  have ha : a ≠ 0 := auxiliary_eval_zero_zero_ne_zero p n b
  have hd : d ≠ 0 := auxiliary_eval_one_one_ne_zero p n b
  set b'mat : Matrix (Fin 2) (Fin 2) (GaloisField p n) := !![d, 0; 0, a]
  have hb'det : b'mat.det ≠ 0 := by
    simp only [b'mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_one,
      mul_zero, sub_zero]
    exact mul_ne_zero hd ha
  set b'gl := Matrix.GeneralLinearGroup.mkOfDetNeZero b'mat hb'det
  have hb'mem : (b'gl.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 1 0 = 0 := by
    simp [b'gl, b'mat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible]
  refine ⟨⟨b'gl, hb'mem⟩, ?_, ?_, ?_⟩
  · -- Matrix identity: r_u * b = b' * r_v
    apply Matrix.GeneralLinearGroup.ext; intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul,
      auxiliaryElement,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk',
      Matrix.unitOfDetInvertible, Matrix.mul_apply, Fin.sum_univ_two,
      b'mat, b'gl]
    have hb10 : bm 1 0 = 0 := b.prop
    have ha' : (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n)) 0 0 ≠ 0 := ha
    fin_cases i <;> fin_cases j <;>
      simp [hb10, a, d, bm, b'mat,



        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
        Matrix.cons_val_one] ;
      (try field_simp [ha', ha, hd]) <;> ring
  · -- (0,0) entry of b' is d
    simp only [b'gl, b'mat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,

      Matrix.cons_val_one]; rfl
  · -- (1,1) entry of b' is a
    simp only [b'gl, b'mat, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible,

      Matrix.cons_val_one]; rfl

private lemma intertwining_sum_covariant
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (f : ↥(auxiliarySubmodule p n chi1 chi2))
    (b : ↥(auxiliarySubgroup p n)) (g : GL2 p n) :
    ∑ u : GaloisField p n,
      f.val (auxiliaryElement p n (some u) * (b.val * g)) =
    auxiliaryComplexFunction p n chi2 chi1 b *
      ∑ u : GaloisField p n,
        f.val (auxiliaryElement p n (some u) * g) := by
  set bm := (b.val.val : Matrix (Fin 2) (Fin 2) (GaloisField p n))
  set a := bm 0 0
  set d := bm 1 1
  set c := bm 0 1
  have ha : a ≠ 0 := auxiliary_eval_zero_zero_ne_zero p n b
  have hd : d ≠ 0 := auxiliary_eval_one_one_ne_zero p n b
  have hterm : ∀ u : GaloisField p n,
      f.val (auxiliaryElement p n (some u) * (b.val * g)) =
      auxiliaryComplexFunction p n chi2 chi1 b *
        f.val (auxiliaryElement p n (some ((c + u * d) / a)) * g) := by
    intro u
    obtain ⟨b', hfact, hb'00, hb'11⟩ :=
      cosetRep_some_mul_borel_factor p n u b
    rw [← mul_assoc, hfact, mul_assoc]
    have hcov := f.prop b' (auxiliaryElement p n (some ((c + u * d) / a)) * g)
    rw [hcov]
    unfold auxiliaryComplexFunction
    simp only [hb'00, hb'11]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  congr 1
  apply Fintype.sum_equiv
    (show GaloisField p n ≃ GaloisField p n from
      { toFun := fun u => (c + u * d) / a
        invFun := fun v => (v * a - c) / d
        left_inv := fun u => by field_simp; ring
        right_inv := fun v => by field_simp; ring })
  intro u; rfl

private lemma principalSeries_iso_swap
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ) :
    Nonempty (auxiliaryPairedRepresentation p n chi1 chi2 ≅
      auxiliaryPairedRepresentation p n chi2 chi1) := by
  by_cases heq : chi1 = chi2
  · subst heq; exact ⟨Iso.refl _⟩
  · -- Both representations are simple
    have hSimple₁ := principalSeries_simple_of_ne p n chi1 chi2 heq
    have hSimple₂ := principalSeries_simple_of_ne p n chi2 chi1 (Ne.symm heq)
    let evalMap₂ : ↥(auxiliarySubmodule p n chi2 chi1) →ₗ[ℂ]
        (Option (GaloisField p n) → ℂ) :=
      { toFun := fun f i => (f : GL2 p n → ℂ) (auxiliaryElement p n i)
        map_add' := fun _ _ => funext fun _ => rfl
        map_smul' := fun _ _ => funext fun _ => rfl }
    have hinj₂ : Function.Injective evalMap₂ := by
      intro f g hfg
      have h := auxiliarySubmodule_ext p n chi2 chi1 (f - g)
        (fun i => by have := congr_fun hfg i; simp [evalMap₂] at this; simp [this])
      exact sub_eq_zero.mp h
    have hsurj₂ : Function.Surjective evalMap₂ := fun c =>
      ⟨⟨auxiliaryFunctionOnGroup p n chi2 chi1 c,
        auxiliaryFunctionOnGroup_mem p n chi2 chi1 c⟩,
       funext fun i => auxiliaryFunctionOnGroup_auxiliaryElement p n chi2 chi1 c i⟩
    set e₂ := LinearEquiv.ofBijective evalMap₂ ⟨hinj₂, hsurj₂⟩
    set T : ↥(auxiliarySubmodule p n chi1 chi2) →ₗ[ℂ]
        ↥(auxiliarySubmodule p n chi2 chi1) :=
      { toFun := fun f => e₂.symm (fun j => ∑ u : GaloisField p n,
          f.val (auxiliaryElement p n (some u) * auxiliaryElement p n j))
        map_add' := fun f₁ f₂ => by
          apply e₂.injective; simp [LinearEquiv.apply_symm_apply]
          ext j; simp [Finset.sum_add_distrib]
        map_smul' := fun c f => by
          apply e₂.injective; simp [LinearEquiv.apply_symm_apply]
          ext j; simp [Finset.mul_sum] }
    have hT_equiv : ∀ (h : GL2 p n)
        (f : ↥(auxiliarySubmodule p n chi1 chi2)),
        T (auxiliarySubmoduleRepresentation p n chi1 chi2 h f) =
        auxiliarySubmoduleRepresentation p n chi2 chi1 h (T f) := by
      intro h f
      apply e₂.injective
      have hLHS : e₂ (T (auxiliarySubmoduleRepresentation p n chi1 chi2 h f)) =
          fun j => ∑ u : GaloisField p n,
            f.val (auxiliaryElement p n (some u) *
              auxiliaryElement p n j * h) := by
        change e₂ (e₂.symm (fun j => ∑ u : GaloisField p n,
          (auxiliarySubmoduleRepresentation p n chi1 chi2 h f).val
            (auxiliaryElement p n (some u) * auxiliaryElement p n j))) = _
        rw [LinearEquiv.apply_symm_apply]; rfl
      have hRHS : e₂ (auxiliarySubmoduleRepresentation p n chi2 chi1 h (T f)) =
          fun j => (T f).val (auxiliaryElement p n j * h) := by
        ext j; rfl
      rw [hLHS, hRHS]; ext j
      set b := auxiliarySubgroupMap p n (auxiliaryElement p n j * h)
      set k := auxiliaryOptionMap p n (auxiliaryElement p n j * h)
      have hdecomp := auxiliarySubgroupMap_decomposition p n
        (auxiliaryElement p n j * h)
      have hTf_cov : (T f).val (auxiliaryElement p n j * h) =
          auxiliaryComplexFunction p n chi2 chi1 b *
            (T f).val (auxiliaryElement p n k) := by
        conv_lhs => rw [hdecomp]; exact (T f).prop b (auxiliaryElement p n k)
      have hTf_eval : (T f).val (auxiliaryElement p n k) =
          ∑ u, f.val (auxiliaryElement p n (some u) *
            auxiliaryElement p n k) := by
        exact congr_fun (e₂.apply_symm_apply (fun j => ∑ u : GaloisField p n,
          f.val (auxiliaryElement p n (some u) * auxiliaryElement p n j))) k
      rw [hTf_cov, hTf_eval]
      have hreassoc : ∀ u : GaloisField p n,
          f.val (auxiliaryElement p n (some u) *
            auxiliaryElement p n j * h) =
          f.val (auxiliaryElement p n (some u) *
            (b.val * auxiliaryElement p n k)) := by
        intro u; rw [mul_assoc, hdecomp]
      simp_rw [hreassoc]
      exact intertwining_sum_covariant p n chi1 chi2 f b
        (auxiliaryElement p n k)
    have hT_ne : T ≠ 0 := by
      intro hT0
      obtain ⟨f₀, hf₀⟩ := hsurj₂ (Pi.single (some (0 : GaloisField p n)) 1)
      let evalMap₁ : ↥(auxiliarySubmodule p n chi1 chi2) →ₗ[ℂ]
          (Option (GaloisField p n) → ℂ) :=
        { toFun := fun f i => (f : GL2 p n → ℂ) (auxiliaryElement p n i)
          map_add' := fun _ _ => funext fun _ => rfl
          map_smul' := fun _ _ => funext fun _ => rfl }
      have hsurj₁ : Function.Surjective evalMap₁ := fun c =>
        ⟨⟨auxiliaryFunctionOnGroup p n chi1 chi2 c,
          auxiliaryFunctionOnGroup_mem p n chi1 chi2 c⟩,
         funext fun i => auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 c i⟩
      obtain ⟨g₀, hg₀⟩ := hsurj₁ (Pi.single (some (0 : GaloisField p n)) 1)
      have hTg₀ : T g₀ = 0 := by rw [hT0]; simp
      have heval_none : (e₂ (T g₀)) none = ∑ u : GaloisField p n,
          g₀.val (auxiliaryElement p n (some u) *
            auxiliaryElement p n none) := by
        simp [T, LinearEquiv.apply_symm_apply]
      rw [hTg₀] at heval_none; simp at heval_none
      have : ∑ u : GaloisField p n,
          g₀.val (auxiliaryElement p n (some u) *
            auxiliaryElement p n none) =
        ∑ u : GaloisField p n,
          g₀.val (auxiliaryElement p n (some u)) := by
        congr 1; ext u; simp [auxiliaryElement]
      rw [this] at heval_none
      have hg₀_eval : ∀ u : GaloisField p n,
          g₀.val (auxiliaryElement p n (some u)) =
          if u = 0 then 1 else 0 := by
        intro u; have := congr_fun hg₀ (some u)
        simp [evalMap₁, Pi.single_apply] at this; exact this
      simp_rw [hg₀_eval] at heval_none; simp at heval_none
    let Thom : auxiliaryPairedRepresentation p n chi1 chi2 ⟶
        auxiliaryPairedRepresentation p n chi2 chi1 :=
      { hom := FGModuleCat.ofHom T
        comm := fun g => by
          ext f
          change T (auxiliarySubmoduleRepresentation p n chi1 chi2 g f) =
            auxiliarySubmoduleRepresentation p n chi2 chi1 g (T f)
          exact hT_equiv g f }
    have hThom_ne : Thom ≠ 0 := by
      intro h
      apply hT_ne
      have : Thom.hom.hom.hom = (0 : _ →ₗ[ℂ] _) := by
        have h1 := congr_arg Action.Hom.hom h; rw [h1]; rfl
      exact this
    haveI := isIso_of_hom_simple hThom_ne
    exact ⟨asIso Thom⟩

set_option maxHeartbeats 1600000 in
private lemma principalSeries_char_diagElt
    (chi1 chi2 : (GaloisField p n)ˣ →* ℂˣ)
    (c : (GaloisField p n)ˣ) (hc : c ≠ 1) :
    FDRep.character (auxiliaryPairedRepresentation p n chi1 chi2)
      (diagElt p n c) = (chi1 c : ℂ) + (chi2 c : ℂ) := by
  simp only [FDRep.character]
  let evalMap : ↥(auxiliarySubmodule p n chi1 chi2) →ₗ[ℂ]
      (Option (GaloisField p n) → ℂ) :=
    { toFun := fun f i => (f : GL2 p n → ℂ) (auxiliaryElement p n i)
      map_add' := fun _ _ => funext fun _ => rfl
      map_smul' := fun _ _ => funext fun _ => rfl }
  have hinj : Function.Injective evalMap := by
    intro f g hfg
    have h : f - g = 0 := auxiliarySubmodule_ext p n chi1 chi2 (f - g)
      (fun i => by have := congr_fun hfg i; simp [evalMap] at this; simp [this])
    exact sub_eq_zero.mp h
  have hsurj : Function.Surjective evalMap := fun c =>
    ⟨⟨auxiliaryFunctionOnGroup p n chi1 chi2 c,
      auxiliaryFunctionOnGroup_mem p n chi1 chi2 c⟩,
     funext fun i => auxiliaryFunctionOnGroup_auxiliaryElement p n chi1 chi2 c i⟩
  set e := LinearEquiv.ofBijective evalMap ⟨hinj, hsurj⟩
  rw [show (LinearMap.trace ℂ _)
      ((auxiliaryPairedRepresentation p n chi1 chi2).ρ (diagElt p n c)) =
    (LinearMap.trace ℂ _) (e.conj
      ((auxiliaryPairedRepresentation p n chi1 chi2).ρ (diagElt p n c))) from
    (LinearMap.trace_conj' _ e).symm]
  have hcinv_ne_one : (↑c⁻¹ : GaloisField p n) ≠ 1 := by
    intro h; apply hc; exact inv_eq_one.mp (Units.val_eq_one.mp h)
  have hfixed : ∀ t : GaloisField p n, t * ↑c⁻¹ = t ↔ t = 0 := by
    intro t; constructor
    · intro h; by_contra ht; apply hcinv_ne_one
      exact mul_left_cancel₀ ht (by rw [mul_one]; exact h)
    · intro h; rw [h, zero_mul]
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Option (GaloisField p n)))]
  simp only [Matrix.trace, Matrix.diag]
  have hentry : ∀ i : Option (GaloisField p n),
      (Pi.basisFun ℂ (Option (GaloisField p n))).repr
        (e.conj ((auxiliaryPairedRepresentation p n chi1 chi2).ρ
          (diagElt p n c))
          ((Pi.basisFun ℂ (Option (GaloisField p n))) i)) i =
      match i with
      | none => (chi1 c : ℂ)
      | some t => if t = 0 then (chi2 c : ℂ) else 0 := by
    intro i
    simp only [Pi.basisFun_apply, Pi.basisFun_repr, LinearEquiv.conj_apply,
      LinearMap.comp_apply]
    cases i with
    | none =>
      change (evalMap (auxiliarySubmoduleRepresentation p n chi1 chi2
        (diagElt p n c) (e.symm (Pi.single none 1)))) none = (chi1 c : ℂ)
      change (auxiliarySubmoduleRepresentation p n chi1 chi2
        (diagElt p n c) (e.symm (Pi.single none 1))).val
        (auxiliaryElement p n none) = (chi1 c : ℂ)
      rw [action_diagonal_none]
      have h1 : (↑(e.symm (Pi.single none 1)) : GL2 p n → ℂ)
          (auxiliaryElement p n none) = 1 :=
        (congr_fun (e.apply_symm_apply (Pi.single none 1)) none).trans
          (Pi.single_eq_same _ _)
      rw [h1, mul_one]
    | some t =>
      change (evalMap (auxiliarySubmoduleRepresentation p n chi1 chi2
        (diagElt p n c) (e.symm (Pi.single (some t) 1)))) (some t) =
        if t = 0 then (chi2 c : ℂ) else 0
      change (auxiliarySubmoduleRepresentation p n chi1 chi2
        (diagElt p n c) (e.symm (Pi.single (some t) 1))).val
        (auxiliaryElement p n (some t)) = if t = 0 then (chi2 c : ℂ) else 0
      rw [action_diagonal_some]
      have heval : (↑(e.symm (Pi.single (some t) 1)) : GL2 p n → ℂ)
          (auxiliaryElement p n (some (t * ↑c⁻¹))) =
          if t = 0 then 1 else 0 := by
        have h := congr_fun (e.apply_symm_apply (Pi.single (some t) 1)) (some (t * ↑c⁻¹))
        rw [show e (e.symm (Pi.single (some t) 1)) (some (t * ↑c⁻¹)) =
            (↑(e.symm (Pi.single (some t) 1)) : GL2 p n → ℂ)
            (auxiliaryElement p n (some (t * ↑c⁻¹))) from rfl] at h
        rw [h]; simp only [Pi.single_apply, Option.some.injEq]
        simp only [hfixed]
      rw [heval]; split_ifs <;> simp
  simp_rw [LinearMap.toMatrix_apply, hentry]
  rw [Fintype.sum_option]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private lemma pair_eq_of_sum_eq
    (chi1 chi2 chi1' chi2' : (GaloisField p n)ˣ →* ℂˣ)
    (_hne : chi1 ≠ chi2) (hne' : chi1' ≠ chi2')
    (hsum : ∀ c : (GaloisField p n)ˣ, (chi1 c : ℂ) + (chi2 c : ℂ) =
      (chi1' c : ℂ) + (chi2' c : ℂ)) :
    ({chi1, chi2} : Set ((GaloisField p n)ˣ →* ℂˣ)) = {chi1', chi2'} := by
  by_cases h : chi1 = chi1'
  · -- χ₁ = χ₁': from sum equality, χ₂ = χ₂'
    have h2 : chi2 = chi2' := by
      ext c; have := hsum c; rw [show (chi1 c : ℂ) = (chi1' c : ℂ) from by rw [h]] at this
      exact_mod_cast add_left_cancel this
    rw [h, h2]
  · by_cases h2 : chi2 = chi1'
    · -- χ₂ = χ₁': from sum equality, χ₁ = χ₂'
      have h3 : chi1 = chi2' := by
        ext c; have hsm := hsum c
        rw [show (chi2 c : ℂ) = (chi1' c : ℂ) from by rw [h2]] at hsm
        rw [add_comm (chi1 c : ℂ) (chi1' c : ℂ)] at hsm
        exact_mod_cast (add_left_cancel hsm : (chi1 c : ℂ) = (chi2' c : ℂ))
      rw [Set.pair_eq_pair_iff]; right; exact ⟨h3, h2⟩
    · -- Neither: get contradiction from orthogonality
      exfalso
      have hcard_ne : (Fintype.card (GaloisField p n)ˣ : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      set μ₁ : (GaloisField p n)ˣ →* ℂˣ := chi1 * chi1'⁻¹
      set μ₂ : (GaloisField p n)ˣ →* ℂˣ := chi2 * chi1'⁻¹
      set μ₂' : (GaloisField p n)ˣ →* ℂˣ := chi2' * chi1'⁻¹
      have hμ₁_ne : μ₁ ≠ 1 := by
        intro heq; apply h
        have : ∀ c, μ₁ c = 1 := fun c => by
          have := congr_arg (· c) heq; simpa using this
        ext c; have := mul_inv_eq_one.mp (this c)
        exact congr_arg Units.val this
      have hμ₂_ne : μ₂ ≠ 1 := by
        intro heq; apply h2
        have : ∀ c, μ₂ c = 1 := fun c => by
          have := congr_arg (· c) heq; simpa using this
        ext c; have := mul_inv_eq_one.mp (this c)
        exact congr_arg Units.val this
      have hμ₂'_ne : μ₂' ≠ 1 := by
        intro heq; apply hne'
        have : ∀ c, μ₂' c = 1 := fun c => by
          have := congr_arg (· c) heq; simpa using this
        ext c; have := (mul_inv_eq_one.mp (this c)).symm
        exact congr_arg Units.val this
      have lhs_eq : ∑ c : (GaloisField p n)ˣ,
          ((chi1 c : ℂ) + (chi2 c : ℂ)) * ((chi1' c)⁻¹ : ℂˣ) =
        ∑ c, ((chi1' c : ℂ) + (chi2' c : ℂ)) * ((chi1' c)⁻¹ : ℂˣ) := by
        congr 1; ext c; rw [hsum c]
      have hval_eq : ∀ (χ ψ : (GaloisField p n)ˣ →* ℂˣ) (c : (GaloisField p n)ˣ),
          (χ c : ℂ) * (↑(ψ c)⁻¹ : ℂ) = ((χ * ψ⁻¹) c : ℂ) := by
        intro χ ψ c; simp [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      have hlhs : ∑ c : (GaloisField p n)ˣ,
          ((chi1 c : ℂ) + (chi2 c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) = 0 := by
        simp_rw [add_mul, hval_eq]
        rw [Finset.sum_add_distrib,
            sum_nontrivial_char_eq_zero μ₁ hμ₁_ne,
            sum_nontrivial_char_eq_zero μ₂ hμ₂_ne, add_zero]
      have hrhs : ∑ c : (GaloisField p n)ˣ,
          ((chi1' c : ℂ) + (chi2' c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) =
          (Fintype.card (GaloisField p n)ˣ : ℂ) := by
        simp_rw [add_mul, hval_eq]
        rw [Finset.sum_add_distrib]
        have h1 : ∑ c : (GaloisField p n)ˣ, ((chi1' * chi1'⁻¹) c : ℂ) =
            Fintype.card (GaloisField p n)ˣ := by
          simp [mul_inv_cancel, Finset.card_univ]
        rw [h1, sum_nontrivial_char_eq_zero μ₂' hμ₂'_ne, add_zero]
      have lhs_eq : ∑ c : (GaloisField p n)ˣ,
          ((chi1 c : ℂ) + (chi2 c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) =
        ∑ c, ((chi1' c : ℂ) + (chi2' c : ℂ)) * (↑(chi1' c)⁻¹ : ℂ) :=
        Finset.sum_congr rfl (fun c _ => by rw [hsum c])
      exact hcard_ne (hrhs.symm.trans (lhs_eq.symm.trans hlhs))

/-- Under the stated inequalities, two auxiliary paired representations are isomorphic exactly when their unordered monoid-homomorphism pairs agree. -/
@[source_ref "Chapter5/Theorem5.25.2" (role := primary)]
theorem auxiliaryPairedRepresentation_iso_iff [NeZero n]
    (chi1 chi2 chi1' chi2' : (GaloisField p n)ˣ →* ℂˣ)
    (hne : chi1 ≠ chi2) (hne' : chi1' ≠ chi2') :
    Nonempty (auxiliaryPairedRepresentation p n chi1 chi2 ≅
      auxiliaryPairedRepresentation p n chi1' chi2') ↔
    ({chi1, chi2} : Set ((GaloisField p n)ˣ →* ℂˣ)) = {chi1', chi2'} := by
  constructor
  · -- Forward: iso → equal characters → sum equality → set equality
    rintro ⟨iso⟩
    have hchar := FDRep.char_iso iso
    have hsum : ∀ c : (GaloisField p n)ˣ, c ≠ 1 →
        (chi1 c : ℂ) + (chi2 c : ℂ) = (chi1' c : ℂ) + (chi2' c : ℂ) := by
      intro c hc
      have h1 := principalSeries_char_diagElt p n chi1 chi2 c hc
      have h2 := principalSeries_char_diagElt p n chi1' chi2' c hc
      rw [← h1, ← h2, congr_fun hchar]
    have hsum_all : ∀ c : (GaloisField p n)ˣ,
        (chi1 c : ℂ) + (chi2 c : ℂ) = (chi1' c : ℂ) + (chi2' c : ℂ) := by
      intro c
      by_cases hc : c = 1
      · subst hc; simp
      · exact hsum c hc
    exact pair_eq_of_sum_eq p n chi1 chi2 chi1' chi2' hne hne' hsum_all
  · -- Backward: set equality → iso
    intro heq
    rw [Set.pair_eq_pair_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact ⟨Iso.refl _⟩
    · rw [h1, h2]
      exact principalSeries_iso_swap p n chi2' chi1'

end

end RepresentationTheory.AuxiliaryFiniteFieldRepresentations
