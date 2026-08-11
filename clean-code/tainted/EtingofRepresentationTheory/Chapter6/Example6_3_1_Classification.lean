import EtingofRepresentationTheory.Chapter6.Example6_3_1
import EtingofRepresentationTheory.Chapter6.Example6_8_5_Geometry
import EtingofRepresentationTheory.Chapter6.Theorem6_5_2
import EtingofRepresentationTheory.Chapter6.DynkinTypes

/-!
# The twelve isomorphism classes of indecomposable D₄ representations

This file bridges the concrete three-subspaces model of Example 6.3.1 to the
quiver-representation model used by Gabriel's theorem.  It then upgrades the
existing dimension-vector bound to an actual classification up to isomorphism.
-/

namespace D₄Rep

open Etingof.Example6_8_5

/-- The vertex-space family underlying a concrete three-subspaces representation.
The outer vertices are `0`, `1`, and `2`; the centre is `3`. -/
abbrev vertexSpace {k : Type*} [Field k] (rho : D₄Rep k) : Fin 4 → Type _
  | 0 => rho.V₁
  | 1 => rho.V₂
  | 2 => rho.V₃
  | 3 => rho.V

private theorem falseOfImpossibleArrow {a b : Fin 4}
    (e : @Quiver.Hom (Fin 4) Q₀ a b)
    (h : Etingof.D₄_adj a b ≠ 1 ∨ ¬ a < b) : False := by
    rcases e with ⟨⟨hadj, hlt⟩⟩
    exact h.elim (fun hn => hn hadj) (fun hn => hn hlt)

/-- A concrete `D₄Rep` regarded as a representation of the standard inward D₄
quiver used by the reflection-functor development. -/
noncomputable abbrev toQuiverRepresentation {k : Type*} [Field k] (rho : D₄Rep k) :
    @Etingof.QuiverRepresentation k (Fin 4) _ Q₀ :=
  @Etingof.QuiverRepresentation.mk k (Fin 4) _ Q₀ (vertexSpace rho)
    (fun v => match v with
      | 0 => rho.addCommGroup₁.toAddCommMonoid
      | 1 => rho.addCommGroup₂.toAddCommMonoid
      | 2 => rho.addCommGroup₃.toAddCommMonoid
      | 3 => rho.addCommGroupV.toAddCommMonoid)
    (fun v => match v with
      | 0 => rho.module₁
      | 1 => rho.module₂
      | 2 => rho.module₃
      | 3 => rho.moduleV)
    (fun {a b} e => match a, b with
      | 0, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 0, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 0, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 0, 3 => rho.A₁
      | 1, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 1, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 1, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 1, 3 => rho.A₂
      | 2, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 2, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 2, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 2, 3 => rho.A₃
      | 3, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 3, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 3, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 3, 3 => False.elim (falseOfImpossibleArrow e (by decide)))

noncomputable instance toQuiverRepresentation_addCommMonoid {k : Type*} [Field k]
    (rho : D₄Rep k) (v : Fin 4) : AddCommMonoid
      (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀
        rho.toQuiverRepresentation v) :=
  @Etingof.QuiverRepresentation.instAddCommMonoid k (Fin 4) _ Q₀
    rho.toQuiverRepresentation v

noncomputable instance toQuiverRepresentation_module {k : Type*} [Field k]
    (rho : D₄Rep k) (v : Fin 4) : Module k
      (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀
        rho.toQuiverRepresentation v) :=
  @Etingof.QuiverRepresentation.instModule k (Fin 4) _ Q₀
    rho.toQuiverRepresentation v

noncomputable instance toQuiverRepresentation_free {k : Type*} [Field k]
    (rho : D₄Rep k) (v : Fin 4) : Module.Free k
      (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀
        rho.toQuiverRepresentation v) := by
  fin_cases v <;> infer_instance

noncomputable instance toQuiverRepresentation_finite {k : Type*} [Field k]
    (rho : D₄Rep k) (v : Fin 4) : Module.Finite k
      (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀
        rho.toQuiverRepresentation v) := by
  fin_cases v <;> infer_instance

/-- Isomorphisms in the concrete three-subspaces model. -/
structure Iso {k : Type*} [Field k] (rho sigma : D₄Rep k) where
  centre : rho.V ≃ₗ[k] sigma.V
  arm₁ : rho.V₁ ≃ₗ[k] sigma.V₁
  arm₂ : rho.V₂ ≃ₗ[k] sigma.V₂
  arm₃ : rho.V₃ ≃ₗ[k] sigma.V₃
  comm₁ : ∀ x, centre (rho.A₁ x) = sigma.A₁ (arm₁ x)
  comm₂ : ∀ x, centre (rho.A₂ x) = sigma.A₂ (arm₂ x)
  comm₃ : ∀ x, centre (rho.A₃ x) = sigma.A₃ (arm₃ x)

/-- A quiver-representation isomorphism restricts to an isomorphism of concrete
three-subspaces representations. -/
noncomputable def isoOfQuiverIso {k : Type*} [Field k] {rho sigma : D₄Rep k}
    (f : @Etingof.QuiverRepresentation.Iso k _ (Fin 4) Q₀
      rho.toQuiverRepresentation sigma.toQuiverRepresentation) : Iso rho sigma where
  centre := @Etingof.QuiverRepresentation.Iso.equivAt k _ (Fin 4) Q₀ _ _ f 3
  arm₁ := @Etingof.QuiverRepresentation.Iso.equivAt k _ (Fin 4) Q₀ _ _ f 0
  arm₂ := @Etingof.QuiverRepresentation.Iso.equivAt k _ (Fin 4) Q₀ _ _ f 1
  arm₃ := @Etingof.QuiverRepresentation.Iso.equivAt k _ (Fin 4) Q₀ _ _ f 2
  comm₁ := fun x => @Etingof.QuiverRepresentation.Iso.naturality k _ (Fin 4)
    Q₀ _ _ f 0 3 finalArmArrow₁ x
  comm₂ := fun x => @Etingof.QuiverRepresentation.Iso.naturality k _ (Fin 4)
    Q₀ _ _ f 1 3 finalArmArrow₂ x
  comm₃ := fun x => @Etingof.QuiverRepresentation.Iso.naturality k _ (Fin 4)
    Q₀ _ _ f 2 3 finalArmArrow₃ x

/-- The concrete and quiver-theoretic notions of indecomposability agree in the
forward direction. -/
theorem toQuiverRepresentation_indecomposable {k : Type*} [Field k]
    {rho : D₄Rep k} (h : rho.Indecomposable) :
    @Etingof.QuiverRepresentation.IsIndecomposable k _ (Fin 4) Q₀
      rho.toQuiverRepresentation := by
  constructor
  · rcases h.1 with hV | h₁ | h₂ | h₃
    · exact ⟨3, Module.finrank_pos_iff.mp hV⟩
    · exact ⟨0, Module.finrank_pos_iff.mp h₁⟩
    · exact ⟨1, Module.finrank_pos_iff.mp h₂⟩
    · exact ⟨2, Module.finrank_pos_iff.mp h₃⟩
  · intro W₁ W₂ hW₁ hW₂ hcompl
    have hd := h.2 (W₁ 3) (W₂ 3) (W₁ 0) (W₂ 0)
      (W₁ 1) (W₂ 1) (W₁ 2) (W₂ 2)
      (hcompl 3) (hcompl 0) (hcompl 1) (hcompl 2)
      (fun x hx => hW₁ finalArmArrow₁ x hx)
      (fun x hx => hW₂ finalArmArrow₁ x hx)
      (fun x hx => hW₁ finalArmArrow₂ x hx)
      (fun x hx => hW₂ finalArmArrow₂ x hx)
      (fun x hx => hW₁ finalArmArrow₃ x hx)
      (fun x hx => hW₂ finalArmArrow₃ x hx)
    rcases hd with ⟨hV, h₁, h₂, h₃⟩ | ⟨hV, h₁, h₂, h₃⟩
    · left
      intro v
      fin_cases v
      · exact h₁
      · exact h₂
      · exact h₃
      · exact hV
    · right
      intro v
      fin_cases v
      · exact h₁
      · exact h₂
      · exact h₃
      · exact hV

/-- The concrete and quiver-theoretic notions of indecomposability agree in the
reverse direction. -/
theorem indecomposable_of_toQuiverRepresentation {k : Type*} [Field k]
    {rho : D₄Rep k}
    (h : @Etingof.QuiverRepresentation.IsIndecomposable k _ (Fin 4) Q₀
      rho.toQuiverRepresentation) : rho.Indecomposable := by
  constructor
  · obtain ⟨v, hv⟩ := h.1
    fin_cases v
    · exact Or.inr (Or.inl (Module.finrank_pos_iff.mpr hv))
    · exact Or.inr (Or.inr (Or.inl (Module.finrank_pos_iff.mpr hv)))
    · exact Or.inr (Or.inr (Or.inr (Module.finrank_pos_iff.mpr hv)))
    · exact Or.inl (Module.finrank_pos_iff.mpr hv)
  · intro p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hpq₁ hpq₂ hpq₃
      hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
    let W₁ : ∀ v, Submodule k
        (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀
          rho.toQuiverRepresentation v) := fun v => match v with
      | 0 => p₁
      | 1 => p₂
      | 2 => p₃
      | 3 => p
    let W₂ : ∀ v, Submodule k
        (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀
          rho.toQuiverRepresentation v) := fun v => match v with
      | 0 => q₁
      | 1 => q₂
      | 2 => q₃
      | 3 => q
    have hW₁ : ∀ {a b : Fin 4} (e : @Quiver.Hom (Fin 4) Q₀ a b), ∀ x ∈ W₁ a,
        @Etingof.QuiverRepresentation.mapLinear k (Fin 4) _ Q₀
          rho.toQuiverRepresentation a b e x ∈ W₁ b := by
      intro a b e x hx
      rcases Q₀_arrow_cases e with
        ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
      · cases he
        exact hp₁ x hx
      · cases he
        exact hp₂ x hx
      · cases he
        exact hp₃ x hx
    have hW₂ : ∀ {a b : Fin 4} (e : @Quiver.Hom (Fin 4) Q₀ a b), ∀ x ∈ W₂ a,
        @Etingof.QuiverRepresentation.mapLinear k (Fin 4) _ Q₀
          rho.toQuiverRepresentation a b e x ∈ W₂ b := by
      intro a b e x hx
      rcases Q₀_arrow_cases e with
        ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
      · cases he
        exact hq₁ x hx
      · cases he
        exact hq₂ x hx
      · cases he
        exact hq₃ x hx
    have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
      intro v
      fin_cases v
      · exact hpq₁
      · exact hpq₂
      · exact hpq₃
      · exact hpq
    rcases h.2 W₁ W₂ hW₁ hW₂ hcompl with hbot | hbot
    · left
      exact ⟨hbot 3, hbot 0, hbot 1, hbot 2⟩
    · right
      exact ⟨hbot 3, hbot 0, hbot 1, hbot 2⟩

/-- The finite indexing type of the twelve candidate dimension vectors. -/
abbrev ClassIndex := {d // d ∈ D₄_indecomposable_dimVectors}

/-- Convert the concrete dimension-vector convention `(centre, arm₁, arm₂, arm₃)`
to the vertex ordering `(arm₁, arm₂, arm₃, centre)` used by `Q₀`. -/
def rootOf (d : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℤ
  | 0 => d.2.1
  | 1 => d.2.2.1
  | 2 => d.2.2.2
  | 3 => d.1

theorem rootOf_injective : Function.Injective rootOf := by
  intro d e h
  rcases d with ⟨d, d₁, d₂, d₃⟩
  rcases e with ⟨e, e₁, e₂, e₃⟩
  have h₀ := congr_fun h 0
  have h₁ := congr_fun h 1
  have h₂ := congr_fun h 2
  have h₃ := congr_fun h 3
  simp only [rootOf, Int.ofNat_inj] at h₀ h₁ h₂ h₃
  subst e
  subst e₁
  subst e₂
  subst e₃
  rfl

/-- Our concrete D₄ adjacency is the standard Dynkin diagram, with the standard
type-D centre relabelled from vertex `1` to vertex `3`. -/
theorem d₄_isDynkinDiagram : Etingof.IsDynkinDiagram 4 Etingof.D₄_adj := by
  let sigma : Fin 4 ≃ Fin 4 := Equiv.swap 1 3
  apply Etingof.isDynkinDiagram_of_graph_iso sigma
    (adj := Etingof.DynkinType.adj (.D 4 (by omega)))
  · decide
  · exact Etingof.isDynkinDiagram_of_type (.D 4 (by omega))

theorem Q₀_isOrientation : Etingof.IsOrientationOf Q₀ Etingof.D₄_adj :=
  Etingof.standardOrientation_isOrientationOf Etingof.D₄_adj (by decide) (by decide)

instance Q₀_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) Q₀ a b) :=
  Etingof.standardOrientation_subsingleton Etingof.D₄_adj a b

theorem classIndex_isPositiveRoot (d : ClassIndex) :
    Etingof.IsPositiveRoot 4 Etingof.D₄_adj (rootOf d.1) := by
  rcases d with ⟨d, hd⟩
  change Etingof.IsPositiveRoot 4 Etingof.D₄_adj (rootOf d)
  simp only [D₄_indecomposable_dimVectors, Finset.mem_insert,
    Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · constructor
      · intro hzero
        have hsum := congr_arg (fun x : Fin 4 → ℤ => x 0 + x 1 + x 2 + x 3) hzero
        norm_num [rootOf] at hsum
      · decide
    · intro i
      fin_cases i <;> norm_num [rootOf]

universe u

abbrev FreeAt {k : Type u} [Field k]
    (rho : @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin 4) _ Q₀)
    (v : Fin 4) : Prop :=
  @Module.Free k (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀ rho v) _
    (@Etingof.QuiverRepresentation.instAddCommMonoid k (Fin 4) _ Q₀ rho v)
    (@Etingof.QuiverRepresentation.instModule k (Fin 4) _ Q₀ rho v)

abbrev FiniteAt {k : Type u} [Field k]
    (rho : @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin 4) _ Q₀)
    (v : Fin 4) : Prop :=
  @Module.Finite k (@Etingof.QuiverRepresentation.obj k (Fin 4) _ Q₀ rho v) _
    (@Etingof.QuiverRepresentation.instAddCommMonoid k (Fin 4) _ Q₀ rho v)
    (@Etingof.QuiverRepresentation.instModule k (Fin 4) _ Q₀ rho v)

/-- The data of one chosen indecomposable representative of a D₄ positive root. -/
structure CanonicalData (k : Type u) [Field k] (d : ClassIndex) where
  representation : @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin 4) _ Q₀
  [free : ∀ v, FreeAt representation v]
  [finite : ∀ v, FiniteAt representation v]
  indecomposable : @Etingof.QuiverRepresentation.IsIndecomposable k _ (Fin 4) Q₀
    representation
  dimension : ∀ v, rootOf d.1 v =
    ((@Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀ representation v : ℕ) : ℤ)

attribute [instance] CanonicalData.free CanonicalData.finite

private theorem canonicalData_nonempty (k : Type u) [Field k] (d : ClassIndex) :
    Nonempty (CanonicalData k d) := by
  rcases (Etingof.Theorem_6_5_2c_bijection d₄_isDynkinDiagram k Q₀_isOrientation
    (rootOf d.1) (classIndex_isPositiveRoot d)).1 with
    ⟨rho, hfree, hfinite, hind, hdim⟩
  exact ⟨{
    representation := rho
    free := hfree
    finite := hfinite
    indecomposable := hind
    dimension := by
      intro v
      simpa [Etingof.QuiverRepresentation.finrankAt'] using hdim v }⟩

/-- A canonical representative for each of the twelve roots, chosen from the
existence half of Gabriel's theorem. -/
noncomputable def canonicalData (k : Type u) [Field k] (d : ClassIndex) :
    CanonicalData k d :=
  Classical.choice (canonicalData_nonempty k d)

noncomputable abbrev canonicalRepresentation (k : Type u) [Field k] (d : ClassIndex) :
    @Etingof.QuiverRepresentation.{u, 0, u, 0} k (Fin 4) _ Q₀ :=
  (canonicalData k d).representation

noncomputable instance canonicalRepresentation_free (k : Type u) [Field k]
    (d : ClassIndex) (v : Fin 4) : FreeAt (canonicalRepresentation k d) v :=
  (canonicalData k d).free v

noncomputable instance canonicalRepresentation_finite (k : Type u) [Field k]
    (d : ClassIndex) (v : Fin 4) : FiniteAt (canonicalRepresentation k d) v :=
  (canonicalData k d).finite v

theorem canonicalRepresentation_indecomposable (k : Type u) [Field k]
    (d : ClassIndex) : @Etingof.QuiverRepresentation.IsIndecomposable k _ (Fin 4) Q₀
      (canonicalRepresentation k d) :=
  (canonicalData k d).indecomposable

theorem canonicalRepresentation_dimension (k : Type u) [Field k]
    (d : ClassIndex) (v : Fin 4) :
    rootOf d.1 v =
      ((@Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀
        (canonicalRepresentation k d) v : ℕ) : ℤ) :=
  (canonicalData k d).dimension v

theorem rootOf_dimVector {k : Type} [Field k]
    (rho : D₄Rep.{0, 0, 0, 0, 0} k) (v : Fin 4) :
    rootOf rho.dimVector v =
      ((@Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀
        rho.toQuiverRepresentation v : ℕ) : ℤ) := by
  fin_cases v <;>
    simp [rootOf, D₄Rep.dimVector, Etingof.QuiverRepresentation.finrankAt']

/-- The canonical index attached to a concrete indecomposable representation. -/
noncomputable def classIndexOf {k : Type} [Field k]
    (rho : D₄Rep.{0, 0, 0, 0, 0} k) (h : rho.Indecomposable) : ClassIndex :=
  ⟨rho.dimVector, Etingof.Example_6_3_1 k rho h⟩

/-- Every concrete indecomposable D₄ representation is isomorphic to the canonical
representative indexed by its dimension vector. -/
theorem iso_canonical {k : Type} [Field k]
    (rho : D₄Rep.{0, 0, 0, 0, 0} k) (h : rho.Indecomposable) :
    Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin 4) Q₀
      rho.toQuiverRepresentation (canonicalRepresentation k (classIndexOf rho h))) := by
  let d := classIndexOf rho h
  apply (Etingof.Theorem_6_5_2c_bijection d₄_isDynkinDiagram k Q₀_isOrientation
    (rootOf d.1) (classIndex_isPositiveRoot d)).2
  · exact toQuiverRepresentation_indecomposable h
  · exact canonicalRepresentation_indecomposable k d
  · intro v
    exact rootOf_dimVector rho v
  · intro v
    exact canonicalRepresentation_dimension k d v

private theorem canonical_index_eq_of_iso {k : Type} [Field k]
    {d e : ClassIndex}
    (f : @Etingof.QuiverRepresentation.Iso k _ (Fin 4) Q₀
      (canonicalRepresentation k d) (canonicalRepresentation k e)) : d = e := by
  apply Subtype.ext
  apply rootOf_injective
  funext v
  have hfin :
      @Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀
          (canonicalRepresentation k d) v =
        @Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀
          (canonicalRepresentation k e) v := by
    unfold Etingof.QuiverRepresentation.finrankAt'
    exact LinearEquiv.finrank_eq
      (@Etingof.QuiverRepresentation.Iso.equivAt k _ (Fin 4) Q₀ _ _ f v)
  exact (canonicalRepresentation_dimension k d v).trans
    ((congr_arg (fun n : ℕ => (n : ℤ)) hfin).trans
      (canonicalRepresentation_dimension k e v).symm)

/-- Distinct listed roots give pairwise nonisomorphic canonical representatives. -/
theorem canonical_pairwise_nonisomorphic {k : Type} [Field k]
    {d e : ClassIndex} (hde : d ≠ e) :
    ¬ Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin 4) Q₀
      (canonicalRepresentation k d) (canonicalRepresentation k e)) := by
  rintro ⟨f⟩
  exact hde (canonical_index_eq_of_iso f)

/-- Full source-level classification: every concrete indecomposable belongs to one
and only one of the twelve canonical isomorphism classes. -/
theorem classification {k : Type} [Field k]
    (rho : D₄Rep.{0, 0, 0, 0, 0} k) (h : rho.Indecomposable) :
    ∃! d : ClassIndex,
      Nonempty (@Etingof.QuiverRepresentation.Iso k _ (Fin 4) Q₀
        rho.toQuiverRepresentation (canonicalRepresentation k d)) := by
  refine ⟨classIndexOf rho h, iso_canonical rho h, ?_⟩
  intro e he
  obtain ⟨f⟩ := he
  apply Subtype.ext
  apply rootOf_injective
  funext v
  have hfin :
      @Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀
          rho.toQuiverRepresentation v =
        @Etingof.QuiverRepresentation.finrankAt' k _ (Fin 4) Q₀
          (canonicalRepresentation k e) v := by
    unfold Etingof.QuiverRepresentation.finrankAt'
    exact LinearEquiv.finrank_eq
      (@Etingof.QuiverRepresentation.Iso.equivAt k _ (Fin 4) Q₀ _ _ f v)
  exact (canonicalRepresentation_dimension k e v).trans
    ((congr_arg (fun n : ℕ => (n : ℤ)) hfin).symm.trans
      (rootOf_dimVector rho v).symm)

/-- There are exactly twelve canonical isomorphism classes. -/
theorem classIndex_card : Fintype.card ClassIndex = 12 := by
  rw [Fintype.card_coe]
  exact D₄_indecomposable_dimVectors_card

end D₄Rep
