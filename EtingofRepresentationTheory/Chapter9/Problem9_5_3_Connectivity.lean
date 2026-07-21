import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_CompositionFactor
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_Devissage
import EtingofRepresentationTheory.Chapter9.Problem9_5_3_Splitting

/-!
# Problem 9.5.3(ii), steps 4–5: block-connectivity of an indecomposable module

This file assembles the finite-length dévissage (`Problem9_5_3_Devissage.lean`, step 2) and the
`Ext¹`-vanishing splitting (`Problem9_5_3_Splitting.lean`, step 3) into the mathematical core of
Problem 9.5.3(ii): the composition factors of an indecomposable finite-length module all lie in a
single linkage class.

## Proof outline

Fix a simple `S`. For a finite-length module `X` and the linkage class `𝒮 = {U | AreLinked S U}`,
`exists_isCompl_split` produces complementary submodules `P ⊞ Q = X` with every composition
factor of `P` linked to `S` and every factor of `Q` unlinked to `S`. The construction is an
induction on the finite length: at each layer `0 → N → X → S₀ → 0` the simple top `S₀` is sorted
into the `𝒮`- or `𝒮'`-part, and the complementary part is split off using step 3 (whose `Ext¹`
hypothesis is discharged by step 2, since factors across the partition are unlinked).

Applied to an indecomposable `M`, one of the two summands must vanish; the surviving summand
carries every composition factor, forcing `S` and `T` into the same class
(`compositionFactors_areLinked_aux`).
-/

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {R : Type u} [Ring R] [Small.{v} R]

omit [Small.{v} R] in
/-- Finite length passes to submodules. -/
theorem isFiniteLength_submodule {X : Type v} [AddCommGroup X] [Module R X]
    (hX : IsFiniteLength R X) (P : Submodule R X) : IsFiniteLength R P := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hX ⊢
  obtain ⟨hN, hA⟩ := hX
  haveI := hN; haveI := hA
  exact ⟨inferInstance, inferInstance⟩

omit [Small.{v} R] in
/-- Finite length passes to quotients. -/
theorem isFiniteLength_quotient {X : Type v} [AddCommGroup X] [Module R X]
    (hX : IsFiniteLength R X) (P : Submodule R X) : IsFiniteLength R (X ⧸ P) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hX ⊢
  obtain ⟨hN, hA⟩ := hX
  haveI := hN; haveI := hA
  exact ⟨inferInstance, inferInstance⟩

/-- **Complement from `Ext¹`-vanishing.** If `Q ≤ X` and `Ext¹(X ⧸ Q, Q)` is subsingleton, then
`Q` has a complementary submodule `P` (so `X = P ⊕ Q` internally) with `P ≅ X ⧸ Q`. This is the
internal-submodule form of the splitting lemma `shortExact_splits_of_ext_subsingleton`. -/
theorem exists_isCompl_of_ext_subsingleton {X : Type v} [AddCommGroup X] [Module R X]
    (Q : Submodule R X)
    (hExt : Subsingleton (Abelian.Ext (ModuleCat.of R (X ⧸ Q)) (ModuleCat.of R Q) 1)) :
    ∃ P : Submodule R X, IsCompl P Q ∧ Nonempty (↥P ≃ₗ[R] (X ⧸ Q)) := by
  -- The short exact sequence `0 → ↥Q → X → X ⧸ Q → 0`.
  set f : ModuleCat.of R Q ⟶ ModuleCat.of R X := ModuleCat.ofHom Q.subtype with hf
  set g : ModuleCat.of R X ⟶ ModuleCat.of R (X ⧸ Q) := ModuleCat.ofHom Q.mkQ with hg
  have hw : f ≫ g = 0 := by ext x; simp [hf, hg]
  have hSES : (ShortComplex.mk f g hw).ShortExact :=
    ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ Q) Q.subtype_injective
      Q.mkQ_surjective
  -- A retraction `r : X ⟶ ↥Q` of `f`, obtained as in `shortExact_splits_of_ext_subsingleton`.
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSES (ModuleCat.of R Q)
    (Abelian.Ext.mk₀ (𝟙 (ModuleCat.of R Q))) (show (1 : ℕ) + 0 = 1 from rfl)
    (Subsingleton.elim _ 0)
  have hfr : f ≫ Abelian.Ext.homEquiv₀ x₂ = 𝟙 (ModuleCat.of R Q) := by
    apply (Abelian.Ext.mk₀_bijective (ModuleCat.of R Q) (ModuleCat.of R Q)).injective
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_homEquiv₀_apply]
    exact hx₂
  set r : X →ₗ[R] ↥Q := (Abelian.Ext.homEquiv₀ x₂).hom with hr
  have hcomp : r ∘ₗ Q.subtype = LinearMap.id := by
    have := congrArg ModuleCat.Hom.hom hfr
    simpa [hf, hr, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_id] using this
  have hrf : ∀ q : ↥Q, r (q : X) = q := fun q => by
    have := LinearMap.congr_fun hcomp q; simpa using this
  -- `proj = Q.subtype ∘ r` is a projection onto `Q`; its kernel is the desired complement.
  set proj : X →ₗ[R] X := Q.subtype ∘ₗ r with hproj
  have hisproj : LinearMap.IsProj Q proj :=
    ⟨fun x => (r x).2, fun x hx => by
      simp only [hproj, LinearMap.comp_apply]
      exact congrArg Subtype.val (hrf ⟨x, hx⟩)⟩
  refine ⟨LinearMap.ker proj, hisproj.isCompl.symm,
    ⟨(Submodule.quotientEquivOfIsCompl Q (LinearMap.ker proj) hisproj.isCompl).symm⟩⟩

omit [Small.{v} R] in
/-- **Sorting composition factors of a quotient across a complemented submodule.** Let `N ≤ X`,
let `A, B` be complementary submodules of `↥N`, and let `Q = B.map N.subtype ≤ N` be the image of
`B` in `X`. Then every composition factor of `X ⧸ Q` is a composition factor of `A` (the
complementary summand inside `N`) or of the top quotient `X ⧸ N`. -/
theorem factor_quot_of_isCompl {X : Type v} [AddCommGroup X] [Module R X] (N : Submodule R X)
    {A B : Submodule R N} (hAB : IsCompl A B) {U : ModuleCat.{v} R}
    (h : IsCompositionFactor R (ModuleCat.of R (X ⧸ B.map N.subtype)) U) :
    IsCompositionFactor R (ModuleCat.of R A) U ∨
      IsCompositionFactor R (ModuleCat.of R (X ⧸ N)) U := by
  set Q : Submodule R X := B.map N.subtype with hQ
  have hle : Q ≤ N := Submodule.map_subtype_le _ _
  -- Subadditivity along the submodule `N ⧸ Q ≤ X ⧸ Q`.
  rcases IsCompositionFactor.of_submodule_or_quotient (K := N.map Q.mkQ) h with hsub | hquot
  · -- Submodule branch: the image of `N` in `X ⧸ Q` is `≅ ↥N ⧸ B ≅ ↥A`.
    left
    set κ : N →ₗ[R] (X ⧸ Q) := Q.mkQ ∘ₗ N.subtype with hκ
    have hrangeκ : LinearMap.range κ = N.map Q.mkQ := by
      rw [hκ, LinearMap.range_comp, Submodule.range_subtype]
    have hkerκ : LinearMap.ker κ = B := by
      ext n
      simp only [LinearMap.mem_ker, hκ, LinearMap.comp_apply, Submodule.subtype_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hQ, Submodule.mem_map]
      constructor
      · rintro ⟨b, hb, hbeq⟩
        rwa [← N.subtype_injective hbeq]
      · intro hn
        exact ⟨n, hn, rfl⟩
    -- `↥(N.map Q.mkQ) ≅ ↥N ⧸ B ≅ ↥A`.
    have e1 : (N ⧸ B) ≃ₗ[R] ↥(N.map Q.mkQ) :=
      (Submodule.quotEquivOfEq B (LinearMap.ker κ) hkerκ.symm).trans
        ((LinearMap.quotKerEquivRange κ).trans (LinearEquiv.ofEq _ _ hrangeκ))
    have e2 : (N ⧸ B) ≃ₗ[R] ↥A := Submodule.quotientEquivOfIsCompl B A hAB.symm
    exact IsCompositionFactor.of_linearEquiv (e2.symm.trans e1) hsub
  · -- Quotient branch: `(X ⧸ Q) ⧸ (N ⧸ Q) ≅ X ⧸ N`.
    right
    exact IsCompositionFactor.of_linearEquiv
      (Submodule.quotientQuotientEquivQuotient Q N hle).symm hquot

/-- **Trace-submodule decomposition (Problem 9.5.3(ii), step 4).** For a finite-length module `X`
and a fixed simple `S`, there are complementary submodules `P, Q` such that every composition
factor of `P` is linked to `S` and every composition factor of `Q` is unlinked to `S`. -/
theorem exists_isCompl_split {S : ModuleCat.{v} R} :
    ∀ {X : Type v} [AddCommGroup X] [Module R X], IsFiniteLength R X →
      ∃ P Q : Submodule R X, IsCompl P Q ∧
        (∀ U : ModuleCat.{v} R, IsCompositionFactor R (ModuleCat.of R P) U → AreLinked R S U) ∧
        (∀ V : ModuleCat.{v} R, IsCompositionFactor R (ModuleCat.of R Q) V →
          ¬ AreLinked R S V) := by
  intro X _ _ hX
  induction hX with
  | @of_subsingleton X _ _ _ =>
      have hns : ∀ (P : Submodule R X) (U : ModuleCat.{v} R),
          IsCompositionFactor R (ModuleCat.of R P) U → False := fun P U hU =>
        absurd (inferInstanceAs (Subsingleton (ModuleCat.of R P)))
          (not_subsingleton_iff_nontrivial.mpr hU.nontrivial)
      exact ⟨⊤, ⊥, isCompl_top_bot, fun U hU => absurd (hns ⊤ U hU) not_false,
        fun V hV => absurd (hns ⊥ V hV) not_false⟩
  | @of_simple_quotient X _ _ N _ hNfl ih =>
      obtain ⟨P₀, Q₀, hcompl₀, hgood₀, hbad₀⟩ := ih
      have hXfl : IsFiniteLength R X := IsFiniteLength.of_simple_quotient hNfl
      set P₁ : Submodule R X := P₀.map N.subtype with hP₁
      set Q₁ : Submodule R X := Q₀.map N.subtype with hQ₁
      -- Transport composition factors between `↥B₀` and its image `↥(B₀.map N.subtype)`.
      have hmapfac : ∀ (B₀ : Submodule R N) (W : ModuleCat.{v} R),
          IsCompositionFactor R (ModuleCat.of R (B₀.map N.subtype)) W →
            IsCompositionFactor R (ModuleCat.of R B₀) W := fun B₀ W h =>
        IsCompositionFactor.of_linearEquiv
          (Submodule.equivMapOfInjective N.subtype N.subtype_injective B₀) h
      -- The image `Q₁` is unlinked-to-`S` on the nose; `P₁` is linked-to-`S`.
      have hQ₁bad : ∀ V : ModuleCat.{v} R,
          IsCompositionFactor R (ModuleCat.of R Q₁) V → ¬ AreLinked R S V := fun V hV =>
        hbad₀ V (hmapfac Q₀ V hV)
      have hP₁good : ∀ U : ModuleCat.{v} R,
          IsCompositionFactor R (ModuleCat.of R P₁) U → AreLinked R S U := fun U hU =>
        hgood₀ U (hmapfac P₀ U hU)
      by_cases hlink : AreLinked R S (ModuleCat.of R (X ⧸ N))
      · -- `S₀ = X ⧸ N` is linked to `S`: split off the unlinked summand `Q₁`.
        have hquotgood : ∀ (W : ModuleCat.{v} R),
            IsCompositionFactor R (ModuleCat.of R (X ⧸ Q₁)) W → AreLinked R S W := by
          intro W hW
          rcases factor_quot_of_isCompl N hcompl₀ hW with hWP | hWN
          · exact hgood₀ W hWP
          · obtain ⟨e⟩ := IsCompositionFactor.of_simple ‹IsSimpleModule R (X ⧸ N)› hWN
            refine (areLinked_equivalence R).trans hlink ?_
            exact areLinked_of_iso R ‹IsSimpleModule R (X ⧸ N)› hWN.1 e.symm.toModuleIso
        have hExt : Subsingleton
            (Abelian.Ext (ModuleCat.of R (X ⧸ Q₁)) (ModuleCat.of R Q₁) 1) := by
          apply ext_subsingleton_of_compositionFactors_unlinked
            (isFiniteLength_quotient hXfl Q₁) (isFiniteLength_submodule hXfl Q₁)
          intro U V hU hV hUV
          exact hQ₁bad V hV ((areLinked_equivalence R).trans (hquotgood U hU) hUV)
        obtain ⟨P, hPcompl, ⟨ePQ⟩⟩ := exists_isCompl_of_ext_subsingleton Q₁ hExt
        refine ⟨P, Q₁, hPcompl, fun U hU => ?_, hQ₁bad⟩
        exact hquotgood U (IsCompositionFactor.of_linearEquiv ePQ.symm hU)
      · -- `S₀` is unlinked to `S`: split off the linked summand `P₁`.
        have hquotbad : ∀ (W : ModuleCat.{v} R),
            IsCompositionFactor R (ModuleCat.of R (X ⧸ P₁)) W → ¬ AreLinked R S W := by
          intro W hW
          rcases factor_quot_of_isCompl N hcompl₀.symm hW with hWQ | hWN
          · exact hbad₀ W hWQ
          · obtain ⟨e⟩ := IsCompositionFactor.of_simple ‹IsSimpleModule R (X ⧸ N)› hWN
            intro hSW
            exact hlink ((areLinked_equivalence R).trans hSW
              (areLinked_of_iso R hWN.1 ‹IsSimpleModule R (X ⧸ N)› e.toModuleIso))
        have hExt : Subsingleton
            (Abelian.Ext (ModuleCat.of R (X ⧸ P₁)) (ModuleCat.of R P₁) 1) := by
          apply ext_subsingleton_of_compositionFactors_unlinked
            (isFiniteLength_quotient hXfl P₁) (isFiniteLength_submodule hXfl P₁)
          intro U V hU hV hUV
          exact hquotbad U hU ((areLinked_equivalence R).trans (hP₁good V hV)
            ((areLinked_equivalence R).symm hUV))
        obtain ⟨Q, hQcompl, ⟨eQP⟩⟩ := exists_isCompl_of_ext_subsingleton P₁ hExt
        refine ⟨P₁, Q, hQcompl.symm, hP₁good, fun V hV => ?_⟩
        exact hquotbad V (IsCompositionFactor.of_linearEquiv eQP.symm hV)

/-- **Block-connectivity (Problem 9.5.3(ii), core).** The composition factors of an indecomposable
finite-length module all lie in a single linkage class. -/
theorem compositionFactors_areLinked_aux {M : ModuleCat.{v} R} (hM : Indecomposable M)
    (hfl : IsFiniteLength R M) {S T : ModuleCat.{v} R}
    (hS : IsCompositionFactor R M S) (hT : IsCompositionFactor R M T) :
    AreLinked R S T := by
  obtain ⟨P, Q, hcompl, hgood, hbad⟩ := exists_isCompl_split (S := S) hfl
  -- Internal direct sum `M = P ⊕ Q` gives a biproduct decomposition `M ≅ ↥P ⊞ ↥Q`.
  have iso : M ≅ (ModuleCat.of R P) ⊞ (ModuleCat.of R Q) :=
    (LinearEquiv.toModuleIso (Submodule.prodEquivOfIsCompl P Q hcompl)).symm ≪≫
      (ModuleCat.biprodIsoProd (ModuleCat.of R P) (ModuleCat.of R Q)).symm
  rcases hM.2 (ModuleCat.of R P) (ModuleCat.of R Q) iso with hZ | hZ
  · -- `↥P = 0`: then `S`, a factor of `M ≅ ↥Q`, would be an unlinked factor, a contradiction.
    exfalso
    have hPbot : P = ⊥ := by
      have hsub : Subsingleton (P : Type v) := ModuleCat.isZero_iff_subsingleton.mp hZ
      rw [Submodule.eq_bot_iff]
      exact fun x hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : P) 0)
    have hQtop : Q = ⊤ := by rw [← hcompl.sup_eq_top, hPbot, bot_sup_eq]
    have eQ : (Q : Type v) ≃ₗ[R] M :=
      (LinearEquiv.ofEq Q ⊤ hQtop).trans Submodule.topEquiv
    exact hbad S (IsCompositionFactor.of_linearEquiv eQ hS) ((areLinked_equivalence R).refl S)
  · -- `↥Q = 0`: then `T`, a factor of `M ≅ ↥P`, is linked to `S`.
    have hQbot : Q = ⊥ := by
      have hsub : Subsingleton (Q : Type v) := ModuleCat.isZero_iff_subsingleton.mp hZ
      rw [Submodule.eq_bot_iff]
      exact fun x hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : Q) 0)
    have hPtop : P = ⊤ := by rw [← hcompl.sup_eq_top, hQbot, sup_bot_eq]
    have eP : (P : Type v) ≃ₗ[R] M :=
      (LinearEquiv.ofEq P ⊤ hPtop).trans Submodule.topEquiv
    exact hgood T (IsCompositionFactor.of_linearEquiv eP hT)

end Etingof
