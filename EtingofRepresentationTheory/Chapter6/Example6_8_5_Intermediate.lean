import EtingofRepresentationTheory.Chapter6.Example6_8_5_Actual

/-!
# The intermediate D₄ reflection representation

The first three actual reflections produce the outward D₄ representation with a
one-dimensional space at every vertex and invertible maps along all three arrows.
-/

namespace Etingof.Example6_8_5

noncomputable def intermediateArrow₁ : @Quiver.Hom (Fin 4) Q₃ 3 0 :=
  Classical.choice ((orient₃.2.1 3 0 (by decide)).resolve_right
    (fun h => (source₃ 0).false (Classical.choice h)))

noncomputable def intermediateArrow₂ : @Quiver.Hom (Fin 4) Q₃ 3 1 :=
  Classical.choice ((orient₃.2.1 3 1 (by decide)).resolve_right
    (fun h => (source₃ 1).false (Classical.choice h)))

noncomputable def intermediateArrow₃ : @Quiver.Hom (Fin 4) Q₃ 3 2 :=
  Classical.choice ((orient₃.2.1 3 2 (by decide)).resolve_right
    (fun h => (source₃ 2).false (Classical.choice h)))

noncomputable abbrev intermediateMap₁ :=
  @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ 3 0 intermediateArrow₁
noncomputable abbrev intermediateMap₂ :=
  @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ 3 1 intermediateArrow₂
noncomputable abbrev intermediateMap₃ :=
  @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ 3 2 intermediateArrow₃

private theorem Q₃_arrow_cases {a b : Fin 4} (e : @Quiver.Hom (Fin 4) Q₃ a b) :
    (a = 3 ∧ b = 0 ∧ HEq e intermediateArrow₁) ∨
    (a = 3 ∧ b = 1 ∧ HEq e intermediateArrow₂) ∨
    (a = 3 ∧ b = 2 ∧ HEq e intermediateArrow₃) := by
  have hadj : Etingof.D₄_adj a b = 1 := by
    by_contra h
    exact (orient₃.1 a b h).false e
  have hb : b ≠ 3 := by
    intro h
    subst b
    exact (source₃ a).false e
  have hclass : ∀ a b : Fin 4, Etingof.D₄_adj a b = 1 → b ≠ 3 →
      (a = 3 ∧ b = 0) ∨ (a = 3 ∧ b = 1) ∨ (a = 3 ∧ b = 2) := by
    decide
  rcases hclass a b hadj hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, heq_of_eq (Subsingleton.elim _ _)⟩)

noncomputable local instance V₃_addCommGroup (v : Fin 4) : AddCommGroup
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ v) :=
  Etingof.addCommGroupOfRing (k := ℂ)

private theorem V₃_finrank (v : Fin 4) : Module.finrank ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ v) = 1 := by
  have h := V₃_dimensionVector v
  unfold Etingof.QuiverRepresentation.finrankAt' at h
  fin_cases v <;> simp_all

private theorem intermediateMap_surjective {j : Fin 4} (hj : j ≠ 3)
    (e : @Quiver.Hom (Fin 4) Q₃ 3 j) : Function.Surjective
      (@Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ 3 j e) := by
  let A := @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ 3 j e
  obtain ⟨S, hRS⟩ := Submodule.exists_isCompl (LinearMap.range A)
  let P : ∀ v, Submodule ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ v) :=
    fun v => if h : v = j then h ▸ LinearMap.range A else ⊤
  let R : ∀ v, Submodule ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ v) :=
    fun v => if h : v = j then h ▸ S else ⊥
  have hP : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) Q₃ a b), ∀ x ∈ P a,
      @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ a b f x ∈ P b := by
    intro a b f x hx
    by_cases hb : b = j
    · subst b
      rcases Q₃_arrow_cases f with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
      · cases he
        have hf : intermediateArrow₁ = e := Subsingleton.elim _ _
        subst e
        simpa only [P, dif_pos rfl, A] using
          (LinearMap.mem_range.mpr ⟨x, rfl⟩ :
            intermediateMap₁ x ∈ LinearMap.range intermediateMap₁)
      · cases he
        have hf : intermediateArrow₂ = e := Subsingleton.elim _ _
        subst e
        simpa only [P, dif_pos rfl, A] using
          (LinearMap.mem_range.mpr ⟨x, rfl⟩ :
            intermediateMap₂ x ∈ LinearMap.range intermediateMap₂)
      · cases he
        have hf : intermediateArrow₃ = e := Subsingleton.elim _ _
        subst e
        simpa only [P, dif_pos rfl, A] using
          (LinearMap.mem_range.mpr ⟨x, rfl⟩ :
            intermediateMap₃ x ∈ LinearMap.range intermediateMap₃)
    · simp [P, hb]
  have hR : ∀ {a b : Fin 4} (f : @Quiver.Hom (Fin 4) Q₃ a b), ∀ x ∈ R a,
      @Etingof.QuiverRepresentation.mapLinear ℂ (Fin 4) _ Q₃ V₃ a b f x ∈ R b := by
    intro a b f x hx
    rcases Q₃_arrow_cases f with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    all_goals
      have h3j : (3 : Fin 4) ≠ j := Ne.symm hj
      have hxzero : x = 0 := by simpa [R, h3j] using hx
      subst x
      simp [R]
  have hcompl : ∀ v, IsCompl (P v) (R v) := by
    intro v
    by_cases hv : v = j
    · subst v
      simpa [P, R] using hRS
    · simpa [P, R, hv] using isCompl_top_bot
  rcases V₃_indecomposable.2 P R hP hR hcompl with hbot | hbot
  · exfalso
    have h3j : (3 : Fin 4) ≠ j := Ne.symm hj
    have htop : (⊤ : Submodule ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3)) = ⊥ := by
      simpa [P, h3j] using hbot 3
    have hrank := congrArg (fun U : Submodule ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3) =>
          Module.finrank ℂ U) htop
    simp [V₃_finrank 3] at hrank
  · have hS : S = ⊥ := by simpa [R] using hbot j
    have htop := hRS.sup_eq_top
    rw [hS, sup_bot_eq] at htop
    exact LinearMap.range_eq_top.mp htop

/-- All three maps of the actual intermediate `(1,1,1,1)` representation are
linear equivalences. -/
theorem intermediate_maps_bijective :
    Function.Bijective intermediateMap₁ ∧ Function.Bijective intermediateMap₂ ∧
      Function.Bijective intermediateMap₃ := by
  have hs₁ := intermediateMap_surjective (by decide) intermediateArrow₁
  have hs₂ := intermediateMap_surjective (by decide) intermediateArrow₂
  have hs₃ := intermediateMap_surjective (by decide) intermediateArrow₃
  have hi₁ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [V₃_finrank 3, V₃_finrank 0])).mpr hs₁
  have hi₂ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [V₃_finrank 3, V₃_finrank 1])).mpr hs₂
  have hi₃ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [V₃_finrank 3, V₃_finrank 2])).mpr hs₃
  exact ⟨⟨hi₁, hs₁⟩, ⟨hi₂, hs₂⟩, ⟨hi₃, hs₃⟩⟩

/-- The canonical `(1,1,1,1)` outward representation: one fixed line at every vertex,
with identity along every arrow. -/
noncomputable def canonicalIntermediateRepresentation :
    @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₃ :=
  @Etingof.QuiverRepresentation.mk ℂ (Fin 4) _ Q₃
    (fun _ => @Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun {_ _} (_ : @Quiver.Hom (Fin 4) Q₃ _ _) => LinearMap.id)

/-- The actual result of the first three reflection functors is isomorphic to the canonical
`(1,1,1,1)` representation. -/
noncomputable def V₃_iso_canonicalIntermediate :
    @Etingof.QuiverRepresentation.Iso ℂ _ (Fin 4) Q₃
      V₃ canonicalIntermediateRepresentation := by
  obtain ⟨hb₁, hb₂, hb₃⟩ := intermediate_maps_bijective
  let e₁ := LinearEquiv.ofBijective intermediateMap₁ hb₁
  let e₂ := LinearEquiv.ofBijective intermediateMap₂ hb₂
  let e₃ := LinearEquiv.ofBijective intermediateMap₃ hb₃
  refine @Etingof.QuiverRepresentation.Iso.mk ℂ _ (Fin 4) Q₃ V₃
    canonicalIntermediateRepresentation (fun v => match v with
      | 0 => e₁.symm
      | 1 => e₂.symm
      | 2 => e₃.symm
      | 3 => LinearEquiv.refl ℂ _) ?_
  intro a b e x
  rcases Q₃_arrow_cases e with ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
  · cases he
    exact e₁.symm_apply_apply x
  · cases he
    exact e₂.symm_apply_apply x
  · cases he
    exact e₃.symm_apply_apply x

end Etingof.Example6_8_5
