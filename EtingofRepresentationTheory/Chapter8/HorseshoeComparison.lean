import EtingofRepresentationTheory.Chapter8.Horseshoe

/-!
# Comparison maps between horseshoe resolutions

A morphism of short exact sequences does not make the choices in the explicit horseshoe
construction definitionally functorial.  Nevertheless, after choosing the usual comparison maps
on the two outer projective resolutions, there is a strict morphism between the two horseshoe
short complexes.  Degreewise its middle component is the upper-triangular matrix

`[[lift φ₁, r], [0, lift φ₃]]`.

The off-diagonal term `r` is constructed recursively.  Its degree-zero seed is chosen so that the
middle augmentation square commutes; exactness of the target left-hand resolution then constructs
all higher components.  This is the horseshoe comparison theorem needed to make the connecting
map of a left derived functor natural in a short exact sequence.
-/

universe v u

open CategoryTheory CategoryTheory.Limits Category

namespace Etingof

variable {C : Type u} [Category.{v} C] [Abelian C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (Q₁ : ProjectiveResolution T.X₁) (Q₃ : ProjectiveResolution T.X₃)

include hS hT φ P₁ P₃ Q₁ Q₃

/-- The comparison map on the left-hand projective resolutions. -/
noncomputable abbrev horseshoeComparison₁ : P₁.complex ⟶ Q₁.complex :=
  ProjectiveResolution.lift φ.τ₁ P₁ Q₁

/-- The comparison map on the right-hand projective resolutions. -/
noncomputable abbrev horseshoeComparison₃ : P₃.complex ⟶ Q₃.complex :=
  ProjectiveResolution.lift φ.τ₃ P₃ Q₃

/-- The defect, on the right summand in degree zero, of the evident diagonal comparison between
the two middle horseshoe augmentations. -/
noncomputable def horseshoeComparisonDefect : P₃.complex.X 0 ⟶ T.X₂ :=
  @Projective.factorThru C _ (P₃.complex.X 0) S.X₃ S.X₂ (P₃.projective 0)
      (P₃.π.f 0) S.g hS.epi_g ≫ φ.τ₂ -
    (horseshoeComparison₃ φ P₃ Q₃).f 0 ≫
      @Projective.factorThru C _ (Q₃.complex.X 0) T.X₃ T.X₂ (Q₃.projective 0)
        (Q₃.π.f 0) T.g hT.epi_g

lemma horseshoeComparisonDefect_comp_g :
    horseshoeComparisonDefect (hS := hS) (hT := hT) (φ := φ) (P₃ := P₃) (Q₃ := Q₃) ≫
      T.g = 0 := by
  rw [horseshoeComparisonDefect, Preadditive.sub_comp]
  simp only [Category.assoc]
  rw [φ.comm₂₃]
  simp only [Projective.factorThru_comp_assoc, Projective.factorThru_comp]
  rw [ProjectiveResolution.lift_commutes_zero]
  simp

/-- The factorisation of the degree-zero defect through the left object of the target short exact
sequence. -/
noncomputable def horseshoeComparisonDefectLift : P₃.complex.X 0 ⟶ T.X₁ := by
  letI : Mono T.f := hT.mono_f
  exact hT.exact.lift
    (horseshoeComparisonDefect (hS := hS) (hT := hT) (φ := φ) (P₃ := P₃) (Q₃ := Q₃))
    (horseshoeComparisonDefect_comp_g (hS := hS) (hT := hT) (φ := φ)
      (P₁ := P₁) (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃))

@[reassoc]
lemma horseshoeComparisonDefectLift_comp_f :
    horseshoeComparisonDefectLift (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₃ := Q₃) ≫ T.f =
      horseshoeComparisonDefect (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₃ := Q₃) := by
  letI : Mono T.f := hT.mono_f
  exact hT.exact.lift_f _ _

/-- The degree-zero off-diagonal comparison, chosen to make the middle augmentation square
commute. -/
noncomputable def horseshoeComparisonZero : P₃.complex.X 0 ⟶ Q₁.complex.X 0 := by
  exact @Projective.factorThru C _ (P₃.complex.X 0) T.X₁ (Q₁.complex.X 0)
    (P₃.projective 0) (horseshoeComparisonDefectLift (hS := hS) (hT := hT) (φ := φ)
      (P₃ := P₃) (Q₃ := Q₃))
    (Q₁.π.f 0) (epi_of_isColimit_cofork Q₁.isColimitCokernelCofork)

@[reassoc]
lemma horseshoeComparisonZero_comp_π :
    horseshoeComparisonZero (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃) ≫ Q₁.π.f 0 =
      horseshoeComparisonDefectLift (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₃ := Q₃) :=
  Projective.factorThru_comp _ _

/-- The expression which the next off-diagonal comparison component must lift. -/
noncomputable def horseshoeComparisonStep (n : ℕ)
    (r : P₃.complex.X n ⟶ Q₁.complex.X n) :
    P₃.complex.X (n + 1) ⟶ Q₁.complex.X n :=
  P₃.complex.d (n + 1) n ≫ r +
    horseshoeTwist hS P₁ P₃ n ≫ (horseshoeComparison₁ φ P₁ Q₁).f n -
    (horseshoeComparison₃ φ P₃ Q₃).f (n + 1) ≫ horseshoeTwist hT Q₁ Q₃ n

lemma horseshoeComparisonStep_zero_comp_π :
    horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ 0
      (horseshoeComparisonZero (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃)) ≫ Q₁.π.f 0 = 0 := by
  letI : Mono T.f := hT.mono_f
  rw [horseshoeComparisonStep, Preadditive.sub_comp, Preadditive.add_comp]
  simp only [Category.assoc, horseshoeComparisonZero_comp_π,
    ProjectiveResolution.lift_commutes_zero]
  apply (cancel_mono T.f).1
  simp only [zero_comp]
  rw [horseshoeComparisonDefectLift_comp_f]
  rw [horseshoeComparisonDefect]
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc]
  rw [φ.comm₁₂]
  simp only [← Category.assoc]
  rw [horseshoeTwist_zero_comp_f, horseshoeTwist_zero_comp_f]
  simp only [Category.assoc]
  rw [← ProjectiveResolution.lift_commutes_zero_assoc]
  abel

/-- Auxiliary recursion producing two consecutive off-diagonal comparison components and their
chain-map relation. -/
noncomputable def horseshoeComparisonAux :
    ∀ n, Σ' (r : P₃.complex.X n ⟶ Q₁.complex.X n)
      (_r' : P₃.complex.X (n + 1) ⟶ Q₁.complex.X (n + 1)),
        _r' ≫ Q₁.complex.d (n + 1) n =
          horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ n r
  | 0 =>
      let r := horseshoeComparisonZero (hS := hS) (hT := hT) (φ := φ)
        (P₃ := P₃) (Q₁ := Q₁) (Q₃ := Q₃)
      let r' := Q₁.exact₀.liftFromProjective
        (horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ 0 r)
        (horseshoeComparisonStep_zero_comp_π hS hT φ P₁ P₃ Q₁ Q₃)
      ⟨r, r', Q₁.exact₀.liftFromProjective_comp _ _⟩
  | n + 1 => by
      let r := (horseshoeComparisonAux n).1
      let r' := (horseshoeComparisonAux n).2.1
      have hr' : r' ≫ Q₁.complex.d (n + 1) n =
          horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ n r :=
        (horseshoeComparisonAux n).2.2
      have hz : horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) r' ≫
          Q₁.complex.d (n + 1) n = 0 := by
        simp only [horseshoeComparisonStep, Preadditive.sub_comp, Preadditive.add_comp,
          Category.assoc]
        rw [hr']
        simp only [horseshoeComparisonStep, Preadditive.comp_sub, Preadditive.comp_add,
          Category.assoc, P₃.complex.d_comp_d_assoc, zero_comp, zero_add]
        rw [HomologicalComplex.Hom.comm]
        rw [horseshoeTwist_comp_assoc]
        rw [← HomologicalComplex.Hom.comm_assoc]
        rw [horseshoeTwist_comp]
        abel_nf
      let r'' := (Q₁.exact_succ n).liftFromProjective
        (horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) r') hz
      exact ⟨r', r'', (Q₁.exact_succ n).liftFromProjective_comp _ _⟩

/-- The off-diagonal component of the strict horseshoe comparison. -/
noncomputable def horseshoeComparisonOffDiag (n : ℕ) :
    P₃.complex.X n ⟶ Q₁.complex.X n :=
  (horseshoeComparisonAux hS hT φ P₁ P₃ Q₁ Q₃ n).1

lemma horseshoeComparisonOffDiag_succ (n : ℕ) :
    horseshoeComparisonOffDiag hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) =
      (horseshoeComparisonAux hS hT φ P₁ P₃ Q₁ Q₃ n).2.1 := rfl

lemma horseshoeComparisonOffDiag_comm (n : ℕ) :
    horseshoeComparisonOffDiag hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) ≫
        Q₁.complex.d (n + 1) n =
      horseshoeComparisonStep hS hT φ P₁ P₃ Q₁ Q₃ n
        (horseshoeComparisonOffDiag hS hT φ P₁ P₃ Q₁ Q₃ n) := by
  rw [horseshoeComparisonOffDiag_succ]
  exact (horseshoeComparisonAux hS hT φ P₁ P₃ Q₁ Q₃ n).2.2

/-- The degreewise upper-triangular middle comparison map. -/
noncomputable def horseshoeComparisonMiddleF (n : ℕ) :
    (horseshoeComplex hS P₁ P₃).X n ⟶ (horseshoeComplex hT Q₁ Q₃).X n :=
  biprod.map ((horseshoeComparison₁ φ P₁ Q₁).f n)
      ((horseshoeComparison₃ φ P₃ Q₃).f n) +
    biprod.snd ≫ horseshoeComparisonOffDiag hS hT φ P₁ P₃ Q₁ Q₃ n ≫ biprod.inl

lemma horseshoeComparisonMiddleF_comm (n : ℕ) :
    horseshoeComparisonMiddleF hS hT φ P₁ P₃ Q₁ Q₃ (n + 1) ≫
        (horseshoeComplex hT Q₁ Q₃).d (n + 1) n =
      (horseshoeComplex hS P₁ P₃).d (n + 1) n ≫
        horseshoeComparisonMiddleF hS hT φ P₁ P₃ Q₁ Q₃ n := by
  simp only [horseshoeComplex, ChainComplex.of_d]
  apply biprod.hom_ext <;> apply biprod.hom_ext'
  all_goals
    simp [horseshoeComparisonMiddleF, horseshoeComparisonOffDiag_comm,
      horseshoeComparisonStep, HomologicalComplex.Hom.comm, Category.assoc,
      Preadditive.add_comp, Preadditive.comp_add]

/-- The strict middle chain map between the two horseshoe complexes. -/
noncomputable def horseshoeComparisonMiddle :
    horseshoeComplex hS P₁ P₃ ⟶ horseshoeComplex hT Q₁ Q₃ :=
  ChainComplex.ofHom
    (horseshoeComparisonMiddleF hS hT φ P₁ P₃ Q₁ Q₃)
    (horseshoeComparisonMiddleF_comm hS hT φ P₁ P₃ Q₁ Q₃)

/-- The strict comparison of horseshoe short complexes induced by a morphism of short exact
sequences. -/
noncomputable def horseshoeComparison :
    horseshoeShortComplex hS P₁ P₃ ⟶ horseshoeShortComplex hT Q₁ Q₃ :=
  ShortComplex.homMk
    (horseshoeComparison₁ φ P₁ Q₁)
    (horseshoeComparisonMiddle hS hT φ P₁ P₃ Q₁ Q₃)
    (horseshoeComparison₃ φ P₃ Q₃)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      apply biprod.hom_ext
      all_goals
        simp [horseshoeShortComplex, horseshoeComparisonMiddle,
          horseshoeComparisonMiddleF, horseshoeα, Category.assoc,
          Preadditive.add_comp, Preadditive.comp_add])
    (by
      apply HomologicalComplex.hom_ext
      intro n
      apply biprod.hom_ext'
      all_goals
        simp [horseshoeShortComplex, horseshoeComparisonMiddle,
          horseshoeComparisonMiddleF, horseshoeβ, Category.assoc,
          Preadditive.add_comp, Preadditive.comp_add])

end Etingof
