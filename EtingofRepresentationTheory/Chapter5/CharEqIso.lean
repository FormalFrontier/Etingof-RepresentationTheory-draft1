import Mathlib

/-!
# Equal characters imply isomorphism (`charEq_iso`)

For finite-dimensional representations of a finite group over `ℂ`, equality of
characters is not just a *consequence* of isomorphism (`FDRep.char_iso`) but is
*equivalent* to it. This file proves the converse, the keystone lemma needed to
turn character computations into genuine isomorphisms of representations:

  `charEq_iso : V.character = W.character → Nonempty (V ≅ W)`.

## Proof outline

We argue entirely inside the semisimple `ℂ`-linear category `FDRep ℂ G`, reusing
Mathlib's categorical Schur's lemma (`finrank_hom_simple_simple`) and the
scalar-product/character bridge (`scalar_product_char_eq_finrank_equivariant`).

* `finrank_hom_eq_of_character_eq`: equal characters force
  `finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)` for *every* test object `S`, directly
  from `scalar_product_char_eq_finrank_equivariant`.
* The main work is purely categorical: in a semisimple, `ℂ`-linear, finite
  category with Schur's lemma, two objects with the same `finrank ℂ (S ⟶ -)` for
  every simple `S` are isomorphic (`iso_of_forall_finrank_hom_eq`). This is proved
  by strong induction on `finrank ℂ V`: peel a simple subobject `S₀ ↪ V`, which
  splits off (every `FDRep` is injective, by Maschke), and match the complement.
* To peel a simple subobject we use `CategoryTheory.exists_simple_subobject`,
  which needs `IsArtinianObject V`. We establish that instance for every
  `FDRep ℂ G` via the strictly-monotone length function `finrank ℂ` on the
  subobject lattice (`Etingof.instIsArtinianObjectFDRep`).

This is reusable across the project: any character-based decomposition argument
can now upgrade a character identity to an honest isomorphism.
-/

open CategoryTheory CategoryTheory.Limits Module

namespace Etingof

variable {G : Type} [Group G] [Finite G]

/-- The forgetful functor from `FDRep ℂ G` to `ℂ`-vector spaces (as `ModuleCat ℂ`).
It is additive, preserves and reflects monomorphisms and isomorphisms, and its
value on an object has the same underlying type as that object. -/
noncomputable abbrev forgetToModuleCat : FDRep ℂ G ⥤ ModuleCat ℂ :=
  Action.forget (FGModuleCat ℂ) G ⋙ forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)

omit [Finite G] in
/-- A monomorphism of finite-dimensional representations is underlyingly injective. -/
theorem injective_of_mono {A B : FDRep ℂ G} (g : A ⟶ B) [Mono g] :
    Function.Injective (forgetToModuleCat.map g).hom := by
  haveI : Mono (forgetToModuleCat.map g) := inferInstance
  rw [← ModuleCat.mono_iff_injective]; infer_instance

/-- Every finite-dimensional representation is an Artinian object: the subobject
lattice satisfies the descending chain condition because `finrank ℂ` is a strictly
monotone `ℕ`-valued length function on it. -/
instance instIsArtinianObjectFDRep (V : FDRep ℂ G) : IsArtinianObject V := by
  set len : Subobject V → ℕ := fun s => finrank ℂ ((s : FDRep ℂ G) : Type) with hlen
  have hlt : ∀ a b : Subobject V, a < b → len a < len b := by
    intro a b hab
    have hle : a ≤ b := le_of_lt hab
    let g : (a : FDRep ℂ G) ⟶ (b : FDRep ℂ G) := Subobject.ofLE a b hle
    haveI : FiniteDimensional ℂ ↥(forgetToModuleCat.obj (a : FDRep ℂ G)) :=
      (inferInstance : FiniteDimensional ℂ ((a : FDRep ℂ G) : Type))
    haveI : FiniteDimensional ℂ ↥(forgetToModuleCat.obj (b : FDRep ℂ G)) :=
      (inferInstance : FiniteDimensional ℂ ((b : FDRep ℂ G) : Type))
    have hginj : Function.Injective (forgetToModuleCat.map g).hom := injective_of_mono g
    have hfle : len a ≤ len b :=
      (forgetToModuleCat.map g).hom.finrank_le_finrank_of_injective hginj
    rcases lt_or_eq_of_le hfle with h | h
    · exact h
    · exfalso
      -- Equal dimensions + injective ⟹ surjective ⟹ underlying iso ⟹ `g` iso ⟹ `a = b`.
      have hsurj : Function.Surjective (forgetToModuleCat.map g).hom := by
        have hrk := (forgetToModuleCat.map g).hom.finrank_range_add_finrank_ker
        rw [LinearMap.ker_eq_bot.mpr hginj, finrank_bot, add_zero] at hrk
        rw [← LinearMap.range_eq_top]
        exact Submodule.eq_top_of_finrank_eq (by rw [hrk]; exact h)
      haveI : Epi (forgetToModuleCat.map g) := by
        rw [ModuleCat.epi_iff_surjective]; exact hsurj
      haveI : IsIso (forgetToModuleCat.map g) := isIso_of_mono_of_epi (forgetToModuleCat.map g)
      haveI : IsIso g := isIso_of_reflects_iso g forgetToModuleCat
      have hba : b ≤ a := Subobject.le_of_comm (inv g) (by
        rw [← Subobject.ofLE_arrow hle]
        change inv g ≫ g ≫ b.arrow = b.arrow
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp])
      exact absurd (le_antisymm hle hba) (ne_of_lt hab)
  have wf : WellFounded ((· < ·) : Subobject V → Subobject V → Prop) :=
    Subrelation.wf (fun {a b} hab => hlt a b hab) (InvImage.wf len wellFounded_lt)
  exact (isArtinianObject_iff_not_strictAnti V).mpr (fun f hf => by
    haveI : WellFoundedLT (Subobject V) := ⟨wf⟩
    exact not_strictAnti_of_wellFoundedLT f hf)

omit [Finite G] in
/-- An object with `finrank ℂ = 0` is a zero object. -/
theorem isZero_of_finrank_eq_zero {V : FDRep ℂ G} (h : finrank ℂ (V : Type) = 0) :
    IsZero V := by
  haveI : Subsingleton (V : Type) := finrank_zero_iff.mp h
  haveI : Subsingleton ↥(forgetToModuleCat.obj V) := (inferInstance : Subsingleton (V : Type))
  haveI : Subsingleton (V ⟶ V) := ⟨fun f g => by
    apply forgetToModuleCat.map_injective
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => Subsingleton.elim _ _⟩
  exact (IsZero.iff_id_eq_zero V).2 (Subsingleton.elim _ _)

omit [Finite G] in
/-- A nonzero object has nonzero `finrank ℂ`. -/
theorem finrank_pos_of_not_isZero {V : FDRep ℂ G} (h : ¬ IsZero V) :
    0 < finrank ℂ (V : Type) :=
  Nat.pos_of_ne_zero fun h0 => h (isZero_of_finrank_eq_zero h0)

omit [Finite G] in
/-- The space of maps from `S` into a zero object is zero-dimensional. -/
theorem finrank_hom_isZero {S V : FDRep ℂ G} (h : IsZero V) : finrank ℂ (S ⟶ V) = 0 := by
  haveI : Subsingleton (S ⟶ V) := ⟨fun f g => h.eq_of_tgt f g⟩
  exact finrank_zero_of_subsingleton

/-- Post-composition with an isomorphism is a `ℂ`-linear equivalence of hom-spaces. -/
noncomputable def homCongrRight (S : FDRep ℂ G) {A B : FDRep ℂ G} (e : A ≅ B) :
    (S ⟶ A) ≃ₗ[ℂ] (S ⟶ B) where
  toFun f := f ≫ e.hom
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' c f := by simp [Linear.smul_comp]
  invFun f := f ≫ e.inv
  left_inv f := by simp
  right_inv f := by simp

omit [Finite G] in
theorem finrank_hom_congr_right (S : FDRep ℂ G) {A B : FDRep ℂ G} (e : A ≅ B) :
    finrank ℂ (S ⟶ A) = finrank ℂ (S ⟶ B) :=
  (homCongrRight S e).finrank_eq

/-- Maps into a binary biproduct split as a product, as `ℂ`-vector spaces. -/
noncomputable def homBiprodEquiv (S A B : FDRep ℂ G) :
    (S ⟶ A ⊞ B) ≃ₗ[ℂ] (S ⟶ A) × (S ⟶ B) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  map_add' f g := by simp [Preadditive.add_comp]
  map_smul' c f := by simp [Linear.smul_comp]
  invFun p := biprod.lift p.1 p.2
  left_inv f := by apply biprod.hom_ext <;> simp
  right_inv p := by ext <;> simp

omit [Finite G] in
/-- `finrank ℂ (S ⟶ -)` is additive on binary biproducts. -/
theorem finrank_hom_biprod (S A B : FDRep ℂ G) :
    finrank ℂ (S ⟶ A ⊞ B) = finrank ℂ (S ⟶ A) + finrank ℂ (S ⟶ B) := by
  rw [(homBiprodEquiv S A B).finrank_eq, Module.finrank_prod]

omit [Finite G] in
/-- `finrank ℂ` is additive on binary biproducts of objects. -/
theorem finrank_biprod_obj (A B : FDRep ℂ G) :
    finrank ℂ (A ⊞ B : FDRep ℂ G) = finrank ℂ (A : Type) + finrank ℂ (B : Type) := by
  haveI : PreservesBinaryBiproduct A B (forgetToModuleCat (G := G)) :=
    preservesBinaryBiproduct_of_preservesBinaryProduct _
  haveI : Module.Finite ℂ ↥(forgetToModuleCat.obj A) :=
    (inferInstance : Module.Finite ℂ (A : Type))
  haveI : Module.Finite ℂ ↥(forgetToModuleCat.obj B) :=
    (inferInstance : Module.Finite ℂ (B : Type))
  have e := (((forgetToModuleCat.mapBiprod A B) ≪≫
    ModuleCat.biprodIsoProd (forgetToModuleCat.obj A) (forgetToModuleCat.obj B)).toLinearEquiv)
  have key : finrank ℂ ↥(forgetToModuleCat.obj (A ⊞ B))
      = finrank ℂ ↥(forgetToModuleCat.obj A) + finrank ℂ ↥(forgetToModuleCat.obj B) := by
    rw [e.finrank_eq, Module.finrank_prod]
  exact key

/-- A split monomorphism splits off its image as a biproduct summand. -/
noncomputable def splitSummand {X Y : FDRep ℂ G} (f : X ⟶ Y) [IsSplitMono f] :
    Σ' Z : FDRep ℂ G, (Y ≅ X ⊞ Z) :=
  ⟨cokernel f, (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel
    (cokernelIsCokernel f)).isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X (cokernel f))⟩

omit [Finite G] in
/-- A monomorphism out of a simple object is nonzero. -/
theorem hom_ne_zero_of_mono_of_simple {S V : FDRep ℂ G} (f : S ⟶ V) [Mono f] [Simple S] :
    f ≠ 0 :=
  fun h0 => (Simple.not_isZero S) ((IsZero.iff_id_eq_zero S).2
    ((cancel_mono f).mp (by rw [h0]; simp)))

section CharField

variable [Fintype G] [Invertible (Fintype.card G : ℂ)]

omit [Finite G] in
/-- Equal characters force equal hom-dimensions out of every object `S`. This is the
character-side input to the isomorphism argument: it follows immediately from
`scalar_product_char_eq_finrank_equivariant`. -/
theorem finrank_hom_eq_of_character_eq (S V W : FDRep ℂ G) (h : V.character = W.character) :
    finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W) := by
  have hV := FDRep.scalar_product_char_eq_finrank_equivariant S V
  have hW := FDRep.scalar_product_char_eq_finrank_equivariant S W
  rw [h] at hV
  have : (finrank ℂ (S ⟶ V) : ℂ) = (finrank ℂ (S ⟶ W) : ℂ) := by rw [← hV, ← hW]
  exact_mod_cast this

end CharField

/-- **Hom-multiplicity classification.** In `FDRep ℂ G`, two objects with the same
`finrank ℂ (S ⟶ -)` for every simple `S` are isomorphic.

Proved by strong induction on `finrank ℂ V`. -/
theorem iso_of_forall_finrank_hom_eq :
    ∀ (n : ℕ) (V W : FDRep ℂ G), finrank ℂ (V : Type) = n →
      (∀ S : FDRep ℂ G, Simple S → finrank ℂ (S ⟶ V) = finrank ℂ (S ⟶ W)) →
      Nonempty (V ≅ W) := by
  haveI : NeZero (Nat.card G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V W hVn hhom
    by_cases hVz : IsZero V
    · -- `V` is a zero object; show `W` is too, then both are isomorphic to `0`.
      refine ⟨hVz.iso ?_⟩
      by_contra hWz
      -- A nonzero `W` has a simple subobject, giving a nonzero map into `W`.
      set S₀ := simpleSubobject hWz with hS₀
      have hιne : simpleSubobjectArrow hWz ≠ 0 := hom_ne_zero_of_mono_of_simple _
      have hpos : 0 < finrank ℂ (S₀ ⟶ W) :=
        finrank_pos_iff_exists_ne_zero.mpr ⟨simpleSubobjectArrow hWz, hιne⟩
      have := hhom S₀ inferInstance
      rw [finrank_hom_isZero hVz] at this
      omega
    · -- `V` is nonzero: peel a simple subobject and induct on the complement.
      set S₀ := simpleSubobject hVz with hS₀
      haveI : Simple S₀ := inferInstance
      -- `ι : S₀ ↪ V` is a split monomorphism since `S₀` is injective (Maschke).
      set ι : S₀ ⟶ V := simpleSubobjectArrow hVz with hι
      haveI : Mono ι := inferInstance
      haveI : IsSplitMono ι :=
        ⟨⟨Injective.factorThru (𝟙 S₀) ι, Injective.comp_factorThru (𝟙 S₀) ι⟩⟩
      obtain ⟨Q, eV⟩ := splitSummand ι
      have hS₀pos : 0 < finrank ℂ (S₀ : Type) := finrank_pos_of_not_isZero (Simple.not_isZero S₀)
      have hVeq : finrank ℂ (V : Type) = finrank ℂ (S₀ : Type) + finrank ℂ (Q : Type) := by
        rw [(FDRep.isoToLinearEquiv eV).finrank_eq, finrank_biprod_obj]
      have hQlt : finrank ℂ (Q : Type) < n := by rw [← hVn, hVeq]; omega
      -- `finrank (S₀ ⟶ W) > 0`, so there is a nonzero map `S₀ → W`; peel it off `W` too.
      have hendo : finrank ℂ (S₀ ⟶ S₀) = 1 := finrank_endomorphism_simple_eq_one ℂ S₀
      have hWpos : 0 < finrank ℂ (S₀ ⟶ W) := by
        have h1 := hhom S₀ inferInstance
        rw [finrank_hom_congr_right S₀ eV, finrank_hom_biprod, hendo] at h1
        omega
      obtain ⟨j, hj⟩ := finrank_pos_iff_exists_ne_zero.mp hWpos
      haveI : Mono j := mono_of_nonzero_from_simple hj
      haveI : IsSplitMono j :=
        ⟨⟨Injective.factorThru (𝟙 S₀) j, Injective.comp_factorThru (𝟙 S₀) j⟩⟩
      obtain ⟨Q', eW⟩ := splitSummand j
      -- The complements have matching hom-dimensions, so they are isomorphic by induction.
      have hQhom : ∀ S : FDRep ℂ G, Simple S →
          finrank ℂ (S ⟶ Q) = finrank ℂ (S ⟶ Q') := by
        intro S hS
        have hSV := hhom S hS
        rw [finrank_hom_congr_right S eV, finrank_hom_biprod,
          finrank_hom_congr_right S eW, finrank_hom_biprod] at hSV
        omega
      obtain ⟨eQ⟩ := ih (finrank ℂ (Q : Type)) hQlt Q Q' rfl hQhom
      exact ⟨eV ≪≫ biprod.mapIso (Iso.refl S₀) eQ ≪≫ eW.symm⟩

/-- **Equal characters imply isomorphism.** For finite-dimensional complex
representations of a finite group, two representations with the same character are
isomorphic. This is the converse of `FDRep.char_iso`, and the keystone lemma for
turning character computations into genuine isomorphisms. -/
theorem charEq_iso {G : Type} [Group G] [Finite G] (V W : FDRep ℂ G)
    (h : V.character = W.character) : Nonempty (V ≅ W) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact iso_of_forall_finrank_hom_eq (finrank ℂ (V : Type)) V W rfl
    (fun S _ => finrank_hom_eq_of_character_eq S V W h)

end Etingof
