import EtingofRepresentationTheory.Chapter8.RearrangeHomBifunctorNatIso
import EtingofRepresentationTheory.Chapter8.ExternalTensorComplexLeft
import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
import EtingofRepresentationTheory.Chapter7.KunnethCochainComplexNat

/-!
# The degreewise object iso for the `Ext` Künneth cochain construction

Part of the `Ext` half of Problem 8.2.8. This file constructs, for each degree `i`, the
`ModuleCat k` isomorphism

    Hom_{A₁⊗A₂}(⊕_{j+m=i} extTensorFunctorLeftObj (P₁ⱼ) (P₂ₘ), N₁⊗N₂)
      ≅ ⊕_{j+m=i} Hom_{A₁}(P₁ⱼ, N₁) ⊗ₖ Hom_{A₂}(P₂ₘ, N₂),

identifying the degree-`i` object of the source cochain complex
`(extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁⊗N₂)` with that of the target
`HomologicalComplex.tensorObj (P₁.complex.linearYonedaObj k N₁) (P₂.complex.linearYonedaObj k N₂)`.

Because the source is `Hom(mapBifunctor …, N)`, a product over the finite fiber via the op/unop
`linearYonedaObj` rather than a `mapBifunctor` bicomplex, the `Tor`-side `total.mapIso` shortcut is
unavailable, and the complex iso has to be assembled degreewise from this object iso.

## The per-summand isomorphism

The essential ingredient is `summandIso`: on a single summand `(j, m)`,
`Hom(extTensorFunctorLeftObj (P₁ⱼ)(P₂ₘ), N₁⊗N₂) ≅ Hom(P₁ⱼ,N₁) ⊗ₖ Hom(P₂ₘ,N₂)`, obtained by
converting the categorical `Hom`s (`ModuleCat.homLinearEquiv`) to `→ₗ`-maps and applying the
component iso `Etingof.rearrangeHomComponentIso`.
-/

open CategoryTheory Limits MonoidalCategory TensorProduct HomologicalComplex

namespace Etingof

universe u

variable (k : Type u) [Field k]
variable (A₁ A₂ : Type u) [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
variable (N₁ N₂ : Type u)
  [AddCommGroup N₁] [Module k N₁] [Module A₁ N₁] [IsScalarTower k A₁ N₁]
  [AddCommGroup N₂] [Module k N₂] [Module A₂ N₂] [IsScalarTower k A₂ N₂]
variable [instN : Module (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
  [IsScalarTower k (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)]
variable
  (hN : ∀ (a₁ : A₁) (a₂ : A₂) (n₁ : N₁) (n₂ : N₂),
    (a₁ ⊗ₜ[k] a₂ : A₁ ⊗[k] A₂) • (n₁ ⊗ₜ[k] n₂ : N₁ ⊗[k] N₂)
      = (a₁ • n₁) ⊗ₜ[k] (a₂ • n₂))

/-- The `A₁ ⊗ A₂`-module `N₁ ⊗ₖ N₂` as an object of `ModuleCat (A₁ ⊗ A₂)`. -/
noncomputable abbrev NNobj : ModuleCat.{u} (A₁ ⊗[k] A₂) := ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂)

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

section Summand

variable {A₁ A₂}

include hN in
/-- The per-summand isomorphism: on the `(X₁, X₂)` summand,
`Hom_{A₁⊗A₂}(extTensorFunctorLeftObj X₁ X₂, N₁⊗N₂) ≅ Hom_{A₁}(X₁, N₁) ⊗ₖ Hom_{A₂}(X₂, N₂)`, phrased
between the categorical `Hom` objects (as they appear in `linearYonedaObj`/`tensorObj`). Converts the
categorical `Hom`s to `→ₗ`-maps via `ModuleCat.homLinearEquiv` and applies the component iso
`rearrangeHomComponentIso`. -/
noncomputable def summandIso (X₁ : ModuleCat.{u} A₁) (X₂ : ModuleCat.{u} A₂)
    [Module.Finite A₁ X₁] [Module.Projective A₁ X₁]
    [Module.Finite A₂ X₂] [Module.Projective A₂ X₂] :
    ModuleCat.of k (extTensorFunctorLeftObj k A₁ A₂ X₁ X₂ ⟶ NNobj k A₁ A₂ N₁ N₂) ≅
      (ModuleCat.of k (X₁ ⟶ ModuleCat.of A₁ N₁)) ⊗ (ModuleCat.of k (X₂ ⟶ ModuleCat.of A₂ N₂)) :=
  ModuleCat.homLinearEquiv.toModuleIso ≪≫
    rearrangeHomComponentIso k N₁ N₂ hN X₁ X₂ ≪≫
    (tensorIso
      (ModuleCat.homLinearEquiv (M := X₁) (N := ModuleCat.of A₁ N₁) (S := k)).toModuleIso
      (ModuleCat.homLinearEquiv (M := X₂) (N := ModuleCat.of A₂ N₂) (S := k)).toModuleIso).symm

end Summand

/-! ## Reconciling the two `k`-module structures

The degreewise objects of the source/target cochain complexes appear in `linearYoneda` form
(`((linearYoneda k _).obj Y).obj (op Z)`), whose `k`-module structure comes through the categorical
`Linear.homModule`. The per-summand `summandIso` and the target tensor factors, by contrast, are
spelled `ModuleCat.of k (Z ⟶ Y)`, whose `k`-module structure is `ModuleCat.Hom.instModule`, picking
the external `Module k` on the codomain `N` (`TensorProduct` on `N₁ ⊗ N₂`, and the ambient one on
each `Nᵢ`). These two `k`-module structures are not definitionally equal; they agree only
through the scalar tower (`algebraMap_smul`). The two lemmas below record the resulting object
equalities so that `eqToIso` can relate the two spellings. -/

/-- Reconciliation lemma for a single Hom factor: the degree-`j` object of `Hom_A(C, of A N)` (as
it appears in `linearYonedaObj`) equals `ModuleCat.of k (C.X j ⟶ of A N)`. The two `k`-module
structures on the hom (categorical `Linear.homModule` vs `ModuleCat.Hom.instModule` picking the
external `Module k N`) agree by the scalar tower `IsScalarTower k A N`. -/
theorem linYonedaXEq (A : Type u) [Ring A] [Algebra k A] (N : Type u)
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (C : ChainComplex (ModuleCat.{u} A) ℕ) (j : ℕ) :
    (C.linearYonedaObj k (ModuleCat.of A N)).X j = ModuleCat.of k (C.X j ⟶ ModuleCat.of A N) := by
  rw [ChainComplex.linearYonedaObj_X]
  dsimp only [linearYoneda]
  congr 1
  refine Module.ext' _ _ (fun r f => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact algebraMap_smul A r ((ModuleCat.Hom.hom f) z)

section Assembly

variable {A₁ A₂}
variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}
variable (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
variable [∀ j, Module.Finite A₁ (P₁.complex.X j)] [∀ j, Module.Projective A₁ (P₁.complex.X j)]
variable [∀ m, Module.Finite A₂ (P₂.complex.X m)] [∀ m, Module.Projective A₂ (P₂.complex.X m)]

include hN in
/-- Reconciliation lemma for an external-tensor summand: `Hom_{A₁⊗A₂}((P₁ⱼ) ⊗ₖ (P₂ₘ), N₁⊗N₂)` in
`linearYoneda` form equals `ModuleCat.of k (extTensorFunctorLeftObj … ⟶ NN)`, the domain of
`summandIso`. -/
theorem srcSummandEq (j m : ℕ) :
    ((linearYoneda k (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj (NNobj k A₁ A₂ N₁ N₂)).obj (Opposite.op
        (((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m))) =
      ModuleCat.of k (extTensorFunctorLeftObj k A₁ A₂ (P₁.complex.X j) (P₂.complex.X m) ⟶
        NNobj k A₁ A₂ N₁ N₂) := by
  dsimp only [linearYoneda]
  congr 1
  refine Module.ext' _ _ (fun r f => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact algebraMap_smul (A₁ ⊗[k] A₂) r ((ModuleCat.Hom.hom f) z)

include hN in
/-- The full per-summand iso between the actual degreewise summands: on the fiber element
`(j, m)`, `Hom_{A₁⊗A₂}((P₁ⱼ) ⊗ₖ (P₂ₘ), N₁⊗N₂)` (as it appears in the source `linearYonedaObj`) is
isomorphic to `Hom_{A₁}(P₁ⱼ, N₁) ⊗ₖ Hom_{A₂}(P₂ₘ, N₂)` (the target `mapBifunctor` summand). Obtained
from `summandIso` by reconciling the two `k`-module spellings via `srcSummandEq` and
`linYonedaXEq`. -/
noncomputable def fullSummandIso (j m : ℕ) :
    ((linearYoneda k (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj (NNobj k A₁ A₂ N₁ N₂)).obj (Opposite.op
        (((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m))) ≅
      ((curriedTensor (ModuleCat.{u} k)).obj
          ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j)).obj
        ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m) :=
  eqToIso (srcSummandEq k N₁ N₂ hN P₁ P₂ j m) ≪≫
    summandIso k N₁ N₂ hN (P₁.complex.X j) (P₂.complex.X m) ≪≫
    tensorIso (eqToIso (linYonedaXEq k A₁ N₁ P₁.complex j).symm)
      (eqToIso (linYonedaXEq k A₂ N₂ P₂.complex m).symm)

/-- The contravariant `Hom(-, N₁⊗N₂)` functor, whose value on the source complex objects is the
source cochain complex `.X`. Being an additive functor it preserves the finite (bi)products used to
assemble the degreewise iso. -/
noncomputable abbrev homYoneda : (ModuleCat.{u} (A₁ ⊗[k] A₂))ᵒᵖ ⥤ ModuleCat.{u} k :=
  (linearYoneda k (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj (NNobj k A₁ A₂ N₁ N₂)

/-- Inclusion of the `(j, m)` summand into `(extTensorComplexLeft P₁ P₂).X i`. -/
noncomputable abbrev srcInc (i j m : ℕ) (h : j + m = i) :
    ((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m) ⟶
      (extTensorComplexLeft P₁ P₂).X i :=
  ιMapBifunctor P₁.complex P₂.complex (extTensorFunctorLeft k A₁ A₂) (ComplexShape.down ℕ) j m i h

/-- Projection of `(extTensorComplexLeft P₁ P₂).X i` onto the `(j, m)` summand (Kronecker delta on
the finite fiber). Together with `srcInc` this exhibits the finite biproduct structure of the
degree-`i` object of the external tensor complex. -/
noncomputable def srcProj (i j m : ℕ) (_h : j + m = i) :
    (extTensorComplexLeft P₁ P₂).X i ⟶
      ((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X j)).obj (P₂.complex.X m) :=
  mapBifunctorDesc (j := i) (fun a b _ =>
    if hjm : a = j ∧ b = m then eqToHom (by rw [hjm.1, hjm.2]) else 0)

/-- **Source `ι`/`π` reduction** (`srcInc ≫ srcProj = δ`). Composing the `(j, m)` inclusion with the
`(j', m')` projection of the external tensor complex is the Kronecker delta. This is the source-side
biproduct relation the assembler reads off; the mirror of `ιN_invNat`/`ιZ_fwdNat`. -/
@[reassoc]
theorem srcInc_srcProj (i j m j' m' : ℕ) (h : j + m = i) (h' : j' + m' = i) :
    srcInc k P₁ P₂ i j m h ≫ srcProj k P₁ P₂ i j' m' h' =
      if hjm : j = j' ∧ m = m' then eqToHom (by rw [hjm.1, hjm.2]) else 0 := by
  rw [srcInc, srcProj, ι_mapBifunctorDesc]

/-- The finite fiber `{(j, m) : j + m = i}` is a `Fintype` (it embeds in `Fin (i+1)` via the first
coordinate). -/
noncomputable instance fibFintype (i : ℕ) : Fintype {p : ℕ × ℕ // p.1 + p.2 = i} := by
  apply Fintype.ofInjective (β := Fin (i + 1)) (fun q => ⟨q.1.1, by have := q.2; omega⟩)
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ hh
  simp only [Fin.mk.injEq] at hh
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨hh, by omega⟩

/-- **Biproduct completeness** for the degree-`i` object of the external tensor complex:
`∑_{(j,m)} srcProj ≫ srcInc = 𝟙`. -/
theorem sum_srcProj_srcInc (i : ℕ) :
    (∑ p : {p : ℕ × ℕ // p.1 + p.2 = i},
      srcProj k P₁ P₂ i p.1.1 p.1.2 p.2 ≫ srcInc k P₁ P₂ i p.1.1 p.1.2 p.2) =
      𝟙 ((extTensorComplexLeft P₁ P₂).X i) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  rw [Preadditive.comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single (⟨(a, b), hab⟩ : {p : ℕ × ℕ // p.1 + p.2 = i})]
  · change srcInc k P₁ P₂ i a b hab ≫ srcProj k P₁ P₂ i a b hab ≫
        srcInc k P₁ P₂ i a b hab = _
    rw [← Category.assoc, srcInc_srcProj]
    simp
  · intro q _ hq
    rw [← Category.assoc]
    change (srcInc k P₁ P₂ i a b hab ≫ srcProj k P₁ P₂ i q.1.1 q.1.2 q.2) ≫ _ = 0
    rw [srcInc_srcProj, dif_neg (by rintro ⟨rfl, rfl⟩; exact hq (Subtype.ext (by simp))), zero_comp]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- The target degree-`i` cochain object `⊕_{j+m=i} Hom_{A₁}(P₁ⱼ, N₁) ⊗ₖ Hom_{A₂}(P₂ₘ, N₂)`. -/
noncomputable abbrev homTarget : CochainComplex (ModuleCat.{u} k) ℕ :=
  HomologicalComplex.tensorObj
    (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
    (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))

/-- Inclusion of the `(j, m)` summand into the target degree-`i` object `homTarget.X i`. -/
noncomputable abbrev tgtInc (i j m : ℕ) (h : j + m = i) :
    ((curriedTensor (ModuleCat.{u} k)).obj
        ((P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁)).X j)).obj
      ((P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)).X m) ⟶
      (homTarget k N₁ N₂ P₁ P₂).X i :=
  ιMapBifunctor (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
    (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) (curriedTensor (ModuleCat.{u} k))
    (ComplexShape.up ℕ) j m i h

include hN in
/-- The forward degreewise map `Hom(⊕Sⱼₘ, N) ⟶ ⊕Tⱼₘ`, a finite sum over the fiber of
`(restrict to summand) ≫ (per-summand iso) ≫ (target inclusion)`. -/
noncomputable def coreFwd (i : ℕ) :
    (homYoneda k N₁ N₂).obj (Opposite.op ((extTensorComplexLeft P₁ P₂).X i)) ⟶
      (homTarget k N₁ N₂ P₁ P₂).X i :=
  ∑ p : {p : ℕ × ℕ // p.1 + p.2 = i},
    (homYoneda k N₁ N₂).map (srcInc k P₁ P₂ i p.1.1 p.1.2 p.2).op ≫
      (fullSummandIso k N₁ N₂ hN P₁ P₂ p.1.1 p.1.2).hom ≫
        tgtInc k N₁ N₂ P₁ P₂ i p.1.1 p.1.2 p.2

include hN in
/-- The inverse degreewise map `⊕Tⱼₘ ⟶ Hom(⊕Sⱼₘ, N)`, the coproduct desc of
`(per-summand iso)⁻¹ ≫ (extend along projection)`. -/
noncomputable def coreInv (i : ℕ) :
    (homTarget k N₁ N₂ P₁ P₂).X i ⟶
      (homYoneda k N₁ N₂).obj (Opposite.op ((extTensorComplexLeft P₁ P₂).X i)) :=
  mapBifunctorDesc (j := i) (fun j m _ =>
    (fullSummandIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
      (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ i j m (by assumption)).op)

include hN in
/-- The degreewise iso, phrased between `Hom((extTensorComplexLeft).X i, N₁⊗N₂)` (in `linearYoneda`
form) and the target coproduct `homTarget.X i`. `coreFwd`/`coreInv` are mutually inverse because
`Hom(-, N₁⊗N₂)` (additive) sends the finite biproduct `⊕Sⱼₘ` to the biproduct `⊕Hom(Sⱼₘ, N)`, whose
`ι`/`π` relations are `srcInc_srcProj` and `sum_srcProj_srcInc`. -/
noncomputable def coreIso (i : ℕ) :
    (homYoneda k N₁ N₂).obj (Opposite.op ((extTensorComplexLeft P₁ P₂).X i)) ≅
      (homTarget k N₁ N₂ P₁ P₂).X i where
  hom := coreFwd k N₁ N₂ hN P₁ P₂ i
  inv := coreInv k N₁ N₂ hN P₁ P₂ i
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    rw [coreInv, ← Category.assoc, ι_mapBifunctorDesc, Category.comp_id, coreFwd,
      Preadditive.comp_sum]
    rw [Finset.sum_eq_single (⟨(a, b), hab⟩ : {p : ℕ × ℕ // p.1 + p.2 = i})]
    · simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, ← op_comp, srcInc_srcProj, dif_pos ⟨rfl, rfl⟩]
      simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc]
    · intro q _ hq
      simp only [Category.assoc]
      rw [← Functor.map_comp_assoc, ← op_comp, srcInc_srcProj,
        dif_neg (by rintro ⟨rfl, rfl⟩; exact hq (Subtype.ext (by simp)))]
      simp only [op_zero, Functor.map_zero, zero_comp, comp_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  hom_inv_id := by
    rw [coreFwd, coreInv, Preadditive.sum_comp]
    have h1 : ∀ p : {p : ℕ × ℕ // p.1 + p.2 = i},
        ((homYoneda k N₁ N₂).map (srcInc k P₁ P₂ i p.1.1 p.1.2 p.2).op ≫
          (fullSummandIso k N₁ N₂ hN P₁ P₂ p.1.1 p.1.2).hom ≫
            tgtInc k N₁ N₂ P₁ P₂ i p.1.1 p.1.2 p.2) ≫
              mapBifunctorDesc (j := i) (fun j m _ =>
                (fullSummandIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
                  (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ i j m (by assumption)).op) =
          (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ i p.1.1 p.1.2 p.2 ≫
            srcInc k P₁ P₂ i p.1.1 p.1.2 p.2).op := by
      intro p
      simp only [Category.assoc, tgtInc, ι_mapBifunctorDesc]
      rw [Iso.hom_inv_id_assoc, ← Functor.map_comp, ← op_comp]
    rw [Finset.sum_congr rfl (fun p _ => h1 p), ← Functor.map_sum (homYoneda k N₁ N₂),
      ← CategoryTheory.op_sum, sum_srcProj_srcInc, op_id, CategoryTheory.Functor.map_id]

include hN in
/-- **The degreewise object iso for the `Ext` Künneth cochain construction.** For each degree `i`,
`Hom_{A₁⊗A₂}(⊕_{j+m=i} (P₁ⱼ) ⊗ₖ (P₂ₘ), N₁⊗N₂) ≅ ⊕_{j+m=i} Hom_{A₁}(P₁ⱼ, N₁) ⊗ₖ Hom_{A₂}(P₂ₘ, N₂)`,
i.e. the degree-`i` object of the source cochain complex
`(extTensorComplexLeft P₁ P₂).linearYonedaObj k (N₁⊗N₂)` is identified with that of the target
`tensorObj (P₁.linearYonedaObj k N₁) (P₂.linearYonedaObj k N₂)`. Assembled from `coreIso` after
transporting the source degree object along `ChainComplex.linearYonedaObj_X`. -/
noncomputable def rearrangeHomComplexXIso (i : ℕ) :
    ((extTensorComplexLeft P₁ P₂).linearYonedaObj k
        (ModuleCat.of (A₁ ⊗[k] A₂) (N₁ ⊗[k] N₂))).X i ≅
      (HomologicalComplex.tensorObj
        (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂))).X i :=
  eqToIso (ChainComplex.linearYonedaObj_X _ _ _ _) ≪≫ coreIso k N₁ N₂ hN P₁ P₂ i

include hN in
/-- **Target `ι`/inv reduction.** Composing the `(j, m)` target-summand inclusion with the inverse
of the degreewise iso is the per-summand inverse `fullSummandIso⁻¹` followed by the source
projection (transported to the `linearYoneda` degree object). The mirror of `ιN_invNat`; consumed
by the assembler. -/
@[reassoc]
theorem ιMapBifunctor_rearrangeHomComplexXIso_inv (i j m : ℕ) (h : j + m = i) :
    ιMapBifunctor (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ) j m i h ≫ (rearrangeHomComplexXIso k N₁ N₂ hN P₁ P₂ i).inv =
      (fullSummandIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
        (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ i j m h).op ≫
          eqToHom (ChainComplex.linearYonedaObj_X _ _ _ _).symm := by
  have h1 : ιMapBifunctor (P₁.complex.linearYonedaObj k (ModuleCat.of A₁ N₁))
        (P₂.complex.linearYonedaObj k (ModuleCat.of A₂ N₂)) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℕ) j m i h ≫ (coreIso k N₁ N₂ hN P₁ P₂ i).inv =
      (fullSummandIso k N₁ N₂ hN P₁ P₂ j m).inv ≫
        (homYoneda k N₁ N₂).map (srcProj k P₁ P₂ i j m h).op := by
    change _ ≫ coreInv k N₁ N₂ hN P₁ P₂ i = _
    simp only [coreInv, ι_mapBifunctorDesc]
  rw [rearrangeHomComplexXIso, Iso.trans_inv, eqToIso.inv, ← Category.assoc, h1, Category.assoc]

end Assembly

end Etingof
