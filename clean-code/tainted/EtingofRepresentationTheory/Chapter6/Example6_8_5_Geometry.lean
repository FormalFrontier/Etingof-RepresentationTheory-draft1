import EtingofRepresentationTheory.Chapter6.Example6_8_5_Actual

/-!
# The geometric endpoint of the D₄ reflection computation

This file identifies the endpoint of the actual reflection-functor chain with the
inclusion of three lines into a plane.
-/

namespace Etingof.Example6_8_5

def finalArmArrow₁ : @Quiver.Hom (Fin 4) Q₀ 0 3 := ⟨⟨by decide, by decide⟩⟩
def finalArmArrow₂ : @Quiver.Hom (Fin 4) Q₀ 1 3 := ⟨⟨by decide, by decide⟩⟩
def finalArmArrow₃ : @Quiver.Hom (Fin 4) Q₀ 2 3 := ⟨⟨by decide, by decide⟩⟩

noncomputable abbrev finalArmMap₁ :=
  @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
    0 3 finalArmArrow₁
noncomputable abbrev finalArmMap₂ :=
  @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
    1 3 finalArmArrow₂
noncomputable abbrev finalArmMap₃ :=
  @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
    2 3 finalArmArrow₃

theorem Q₀_arrow_cases {a b : Fin 4} (e : @Quiver.Hom (Fin 4) Q₀ a b) :
    (a = 0 ∧ b = 3 ∧ HEq e finalArmArrow₁) ∨
    (a = 1 ∧ b = 3 ∧ HEq e finalArmArrow₂) ∨
    (a = 2 ∧ b = 3 ∧ HEq e finalArmArrow₃) := by
  rcases e with ⟨⟨hadj, hlt⟩⟩
  have hclass : ∀ a b : Fin 4, Etingof.D₄_adj a b = 1 → a < b →
      (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 3) ∨ (a = 2 ∧ b = 3) := by
    decide
  rcases hclass a b hadj hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)

noncomputable local instance final_addCommGroup (v : Fin 4) : AddCommGroup
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
  Etingof.addCommGroupOfRing (k := ℂ)

private theorem centre_finrank : Module.finrank ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 3) = 2 := by
  have h := finalRepresentation_dimensionVector 3
  have h' : (Module.finrank ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 3) : ℤ) = 2 := by
    simpa using h
  exact_mod_cast h'

private theorem arm_finrank (i : Fin 4) (hi : i ≠ 3) : Module.finrank ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation i) = 1 := by
  have h := finalRepresentation_dimensionVector i
  fin_cases i <;> simp_all

private theorem armMap_injective {i : Fin 4} (hi : i ≠ 3)
    (e : @Quiver.Hom (Fin 4) Q₀ i 3) : Function.Injective
      (@Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
        i 3 e) := by
  let A := @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀
    finalRepresentation i 3 e
  obtain ⟨S, hKS⟩ := Submodule.exists_isCompl (LinearMap.ker A)
  let P : ∀ v, Submodule ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
    fun v => if h : v = i then h ▸ LinearMap.ker A else ⊥
  let R : ∀ v, Submodule ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
    fun v => if h : v = i then h ▸ S else ⊤
  have h3i : (3 : Fin 4) ≠ i := Ne.symm hi
  have hP : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) Q₀ a b), ∀ x ∈ P a,
      @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
        a b f x ∈ P b := by
    intro a b f x hx
    by_cases ha : a = i
    · subst a
      rcases Q₀_arrow_cases f with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
      all_goals
        have hf : f = e := Subsingleton.elim _ _
        subst f
        have hxker : x ∈ LinearMap.ker A := by
          simpa only [P, dif_pos rfl] using hx
        have hzero : A x = 0 := LinearMap.mem_ker.mp hxker
        simp [P, A, hzero]
    · have hxzero : x = 0 := by
        have : x ∈ (⊥ : Submodule ℂ
            (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation a)) := by
          simpa [P, ha] using hx
        exact (Submodule.mem_bot (R := ℂ)).mp this
      subst x
      simp [P]
  have hR : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) Q₀ a b), ∀ x ∈ R a,
      @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
        a b f x ∈ R b := by
    intro a b f x hx
    rcases Q₀_arrow_cases f with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;>
      simp [R, h3i]
  have hcompl : ∀ v, IsCompl (P v) (R v) := by
    intro v
    by_cases hv : v = i
    · subst v
      simpa [P, R] using hKS
    · simpa [P, R, hv] using isCompl_bot_top
  rcases finalRepresentation_indecomposable.2 P R hP hR hcompl with hbot | hbot
  · exact LinearMap.ker_eq_bot.mp (by simpa [P] using hbot i)
  · exfalso
    have htop : (⊤ : Submodule ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 3)) = ⊥ := by
      simpa [R, h3i] using hbot 3
    have hrank := congrArg (fun T : Submodule ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 3) =>
          Module.finrank ℂ T) htop
    simp [centre_finrank] at hrank

/-- The three actual arrow maps embed the one-dimensional arms into the centre. -/
theorem final_arrow_maps_injective :
    Function.Injective finalArmMap₁ ∧
    Function.Injective finalArmMap₂ ∧
    Function.Injective finalArmMap₃ :=
  ⟨armMap_injective (by decide) finalArmArrow₁,
    armMap_injective (by decide) finalArmArrow₂,
    armMap_injective (by decide) finalArmArrow₃⟩

/-- The images of the three actual arm maps span the two-dimensional centre. -/
theorem final_arm_ranges_span :
    LinearMap.range finalArmMap₁ ⊔ LinearMap.range finalArmMap₂ ⊔
      LinearMap.range finalArmMap₃ = ⊤ := by
  let A₁ := @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀
    finalRepresentation 0 3 finalArmArrow₁
  let A₂ := @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀
    finalRepresentation 1 3 finalArmArrow₂
  let A₃ := @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀
    finalRepresentation 2 3 finalArmArrow₃
  let T := LinearMap.range A₁ ⊔ LinearMap.range A₂ ⊔ LinearMap.range A₃
  obtain ⟨S, hTS⟩ := Submodule.exists_isCompl T
  let P : ∀ v, Submodule ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
    fun v => if h : v = 3 then h ▸ T else ⊤
  let R : ∀ v, Submodule ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
    fun v => if h : v = 3 then h ▸ S else ⊥
  have hP : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) Q₀ a b), ∀ x ∈ P a,
      @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
        a b f x ∈ P b := by
    intro a b f x hx
    rcases Q₀_arrow_cases f with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
    · cases he
      exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (LinearMap.mem_range.mpr ⟨x, rfl⟩))
    · cases he
      exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (LinearMap.mem_range.mpr ⟨x, rfl⟩))
    · cases he
      exact Submodule.mem_sup_right (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  have hR : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) Q₀ a b), ∀ x ∈ R a,
      @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₀ finalRepresentation
        a b f x ∈ R b := by
    intro a b f x hx
    rcases Q₀_arrow_cases f with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    all_goals
      have hxzero : x = 0 := by simpa [R] using hx
      subst x
      simp [R]
  have hcompl : ∀ v, IsCompl (P v) (R v) := by
    intro v
    by_cases hv : v = 3
    · subst v
      simpa [P, R] using hTS
    · simpa [P, R, hv] using isCompl_top_bot
  rcases finalRepresentation_indecomposable.2 P R hP hR hcompl with hbot | hbot
  · have htop : (⊤ : Submodule ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 0)) = ⊥ := by
      simpa [P] using hbot 0
    have hrank := congrArg (fun U : Submodule ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 0) =>
          Module.finrank ℂ U) htop
    simp [arm_finrank 0 (by decide)] at hrank
  · have hS : S = ⊥ := by simpa [R] using hbot 3
    have htop := hTS.sup_eq_top
    rw [hS, sup_bot_eq] at htop
    simpa [T, A₁, A₂, A₃] using htop

/-- An isomorphism from the actual final representation to its image-line presentation.
The target arrows are literally the subtype inclusions of the three ranges. -/
structure ThreeLinesInPlaneIso where
  centre : (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀
    finalRepresentation 3) ≃ₗ[ℂ]
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation 3)
  arm₁ : (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀
    finalRepresentation 0) ≃ₗ[ℂ] LinearMap.range finalArmMap₁
  arm₂ : (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀
    finalRepresentation 1) ≃ₗ[ℂ] LinearMap.range finalArmMap₂
  arm₃ : (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀
    finalRepresentation 2) ≃ₗ[ℂ] LinearMap.range finalArmMap₃
  comm₁ : ∀ x, centre (finalArmMap₁ x) = (LinearMap.range finalArmMap₁).subtype (arm₁ x)
  comm₂ : ∀ x, centre (finalArmMap₂ x) = (LinearMap.range finalArmMap₂).subtype (arm₂ x)
  comm₃ : ∀ x, centre (finalArmMap₃ x) = (LinearMap.range finalArmMap₃).subtype (arm₃ x)

/-- The actual endpoint is isomorphic to the representation whose arrows are the
inclusions of its three image lines into the centre. -/
theorem final_isomorphic_to_threeLinesInPlane : Nonempty ThreeLinesInPlaneIso := by
  obtain ⟨h₁, h₂, h₃⟩ := final_arrow_maps_injective
  refine ⟨{
    centre := LinearEquiv.refl ℂ _
    arm₁ := LinearEquiv.ofInjective finalArmMap₁ h₁
    arm₂ := LinearEquiv.ofInjective finalArmMap₂ h₂
    arm₃ := LinearEquiv.ofInjective finalArmMap₃ h₃
    comm₁ := fun _ => rfl
    comm₂ := fun _ => rfl
    comm₃ := fun _ => rfl }⟩

/-- Each image is a line, and together the three lines span the plane. -/
theorem final_three_lines_geometry :
    Module.finrank ℂ (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀
      finalRepresentation 3) = 2 ∧
    Module.finrank ℂ (LinearMap.range finalArmMap₁) = 1 ∧
    Module.finrank ℂ (LinearMap.range finalArmMap₂) = 1 ∧
    Module.finrank ℂ (LinearMap.range finalArmMap₃) = 1 ∧
    LinearMap.range finalArmMap₁ ⊔ LinearMap.range finalArmMap₂ ⊔
      LinearMap.range finalArmMap₃ = ⊤ := by
  obtain ⟨h₁, h₂, h₃⟩ := final_arrow_maps_injective
  refine ⟨centre_finrank, ?_, ?_, ?_, final_arm_ranges_span⟩
  · rw [LinearMap.finrank_range_of_inj h₁]
    exact arm_finrank 0 (by decide)
  · rw [LinearMap.finrank_range_of_inj h₂]
    exact arm_finrank 1 (by decide)
  · rw [LinearMap.finrank_range_of_inj h₃]
    exact arm_finrank 2 (by decide)

end Etingof.Example6_8_5
