import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.ExtCohomologyHomK
/-!
# Problem 8.2.5: `Tor` and `Ext` are independent of the projective resolution

Let `P_•`, `Q_•` be two projective resolutions of `M`.

* (i) There exists `f₀ : P₀ → Q₀` with `d^Q₀ ∘ f₀ = d^P₀`.
* (ii) Inductively there exist `f_j : P_j → Q_j` with `d^Q_j ∘ f_j = f_{j-1} ∘ d^P_j`; the
  collection `f : P_• → Q_•` is a **morphism of resolutions**.
* (iii) `f` induces maps `ψ_i(P, Q, f) : Tor_i^P(M, N) → Tor_i^Q(M, N)` independent of `f`.
* (iv) The `ψ_i(P, Q)` are isomorphisms.
* (v) Similarly for `Ext`: `ξ_i(Q, P, f) : Ext^i_P(M, N) → Ext^i_Q(M, N)` are independent of
  `f` and are isomorphisms.

The upshot is that the groups `Tor_i` and `Ext^i` do not depend on the chosen resolution, which
justifies suppressing `P_•` from the notation.

## Formalization notes

Parts (i) and (ii) are exactly the existence of a lift of the identity `𝟙 M` to a chain map
between the two resolutions, compatible with the augmentations `π`. This is captured by the
first statement: a morphism `f : P.complex ⟶ Q.complex` with `f ≫ Q.π = P.π`.

For parts (iii) and (iv), `torLiftMap` is the map on homology induced by a chosen compatible
lift. `torLiftMap_eq_comparison` identifies it with the canonical derived-functor comparison
`torComparison`, so `torLiftMap_independent` proves literal independence of the lift and
`torComparison_refl`/`torComparison_trans` give the identity and composition laws.

Part (v) is contravariant in the resolution. `extCochainMap` performs the required reindexing
after applying the cochain-Hom functor, `extLiftMap_independent` proves independence, and
`extComparison` packages the resulting map as an actual isomorphism. Thus the public API
records the source's induced maps and isomorphisms themselves, rather than relying only on the
neighboring fact that resolutions are homotopy equivalent.
-/

namespace Etingof

open CategoryTheory

universe u

variable {A : Type u} [Ring A] {M : ModuleCat.{u} A}

/-- **Problem 8.2.5(i)–(ii).** Any two projective resolutions of `M` admit a *morphism of
resolutions*: a chain map `f : P_• → Q_•` compatible with the augmentations to `M`. -/
theorem Problem_8_2_5_morphism_of_resolutions
    (P Q : ProjectiveResolution M) :
    ∃ f : P.complex ⟶ Q.complex, f ≫ Q.π = P.π :=
  ⟨ProjectiveResolution.lift (𝟙 M) P Q, by simp⟩

/-- **Problem 8.2.5(iii)–(v).** Any two projective resolutions of `M` are homotopy equivalent.
Applying an additive functor and taking homology, this shows the induced maps on `Tor_i` and
`Ext^i` are isomorphisms independent of the chosen morphism of resolutions, so `Tor_i` and
`Ext^i` do not depend on the resolution. -/
theorem Problem_8_2_5_independence
    (P Q : ProjectiveResolution M) :
    Nonempty (HomotopyEquiv P.complex Q.complex) :=
  ⟨ProjectiveResolution.homotopyEquiv P Q⟩

/-! ## The source-level comparison maps -/

namespace Problem825

open Limits

universe v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type*} [Category* D] [Abelian D]

/-- The canonical comparison between the homologies obtained by applying an additive functor
to two projective resolutions of the same object. -/
noncomputable def resolutionComparison (F : C ⥤ D) [F.Additive] {X : C}
    (P Q : ProjectiveResolution X) (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex).homology n :=
  (P.isoLeftDerivedObj F n).symm ≪≫ Q.isoLeftDerivedObj F n

/-- A compatible morphism of resolutions induces the canonical comparison map on homology. -/
theorem homologyMap_eq_resolutionComparison (F : C ⥤ D) [F.Additive] {X : C}
    (P Q : ProjectiveResolution X) (φ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n =
      (resolutionComparison F P Q n).hom := by
  change _ = (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom
  rw [← cancel_epi (P.isoLeftDerivedObj F n).hom, Iso.hom_inv_id_assoc]
  simpa using (ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (𝟙 X) P Q φ (by simpa using hφ) F n).symm

/-- In particular, arbitrary compatible lifts induce the same map on homology. -/
theorem homologyMap_independent_of_lift (F : C ⥤ D) [F.Additive] {X : C}
    (P Q : ProjectiveResolution X) (φ ψ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0)
    (hψ : ψ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ) n := by
  rw [homologyMap_eq_resolutionComparison F P Q φ hφ n,
    homologyMap_eq_resolutionComparison F P Q ψ hψ n]

/-- The comparison from a resolution to itself is the identity. -/
theorem resolutionComparison_refl (F : C ⥤ D) [F.Additive] {X : C}
    (P : ProjectiveResolution X) (n : ℕ) :
    (resolutionComparison F P P n).hom = 𝟙 _ := by
  simp [resolutionComparison]

/-- Resolution comparisons compose transitively. -/
theorem resolutionComparison_trans (F : C ⥤ D) [F.Additive] {X : C}
    (P Q R : ProjectiveResolution X) (n : ℕ) :
    (resolutionComparison F P Q n).hom ≫ (resolutionComparison F Q R n).hom =
      (resolutionComparison F P R n).hom := by
  simp [resolutionComparison, Category.assoc]

/-- Passing a homotopy equivalence in an opposite category through `unop` reverses its
direction, as required by a contravariant Hom complex. -/
def unopHomotopyEquiv {ι V : Type*} [Category* V] [Preadditive V]
    {c : ComplexShape ι} {K L : HomologicalComplex Vᵒᵖ c} (h : HomotopyEquiv K L) :
    HomotopyEquiv
      ((HomologicalComplex.unopFunctor V c).obj (Opposite.op L))
      ((HomologicalComplex.unopFunctor V c).obj (Opposite.op K)) where
  hom := (HomologicalComplex.unopFunctor V c).map h.hom.op
  inv := (HomologicalComplex.unopFunctor V c).map h.inv.op
  homotopyHomInvId := by
    let F := HomologicalComplex.unopFunctor V c
    have h₁ : Homotopy (F.map h.hom.op ≫ F.map h.inv.op) (F.map (𝟙 (Opposite.op L))) := by
      simpa only [op_comp, op_id, Functor.map_comp] using
        Homotopy.unop h.homotopyInvHomId
    exact h₁.trans (Homotopy.ofEq (F.map_id (Opposite.op L)))
  homotopyInvHomId := by
    let F := HomologicalComplex.unopFunctor V c
    have h₁ : Homotopy (F.map h.inv.op ≫ F.map h.hom.op) (F.map (𝟙 (Opposite.op K))) := by
      simpa only [op_comp, op_id, Functor.map_comp] using
        Homotopy.unop h.homotopyHomInvId
    exact h₁.trans (Homotopy.ofEq (F.map_id (Opposite.op K)))

section Tor

variable {A : Type u} [Ring A] (N : ModuleCat.{u} A)
variable {M : ModuleCat.{u} Aᵐᵒᵖ}

/-- `Tor` computed from the chosen projective resolution `P`. -/
noncomputable abbrev TorByResolution (P : ProjectiveResolution M) (n : ℕ) : AddCommGrpCat.{u} :=
  (((tensorRightFunctor A N).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n

/-- **Problem 8.2.5(iv).** The canonical isomorphism between the `Tor` groups computed from
two projective resolutions. -/
noncomputable def torComparison (P Q : ProjectiveResolution M) (n : ℕ) :
    TorByResolution N P n ≅ TorByResolution N Q n :=
  resolutionComparison (tensorRightFunctor A N) P Q n

/-- The map `ψᵢ(P,Q,f)` induced on resolution-computed `Tor` by a resolution morphism. -/
noncomputable def torLiftMap (P Q : ProjectiveResolution M)
    (φ : P.complex ⟶ Q.complex) (n : ℕ) : TorByResolution N P n ⟶ TorByResolution N Q n :=
  HomologicalComplex.homologyMap
    (((tensorRightFunctor A N).mapHomologicalComplex (ComplexShape.down ℕ)).map φ) n

/-- **Problem 8.2.5(iii).** `ψᵢ(P,Q,f)` is independent of the compatible lift `f` and is the
canonical comparison isomorphism. -/
theorem torLiftMap_eq_comparison (P Q : ProjectiveResolution M)
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    torLiftMap N P Q φ n = (torComparison N P Q n).hom :=
  homologyMap_eq_resolutionComparison (tensorRightFunctor A N) P Q φ hφ n

/-- Any two compatible resolution morphisms induce exactly the same map on `Tor`. -/
theorem torLiftMap_independent (P Q : ProjectiveResolution M)
    (φ ψ : P.complex ⟶ Q.complex)
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0)
    (hψ : ψ.f 0 ≫ Q.π.f 0 = P.π.f 0) (n : ℕ) :
    torLiftMap N P Q φ n = torLiftMap N P Q ψ n := by
  rw [torLiftMap_eq_comparison N P Q φ hφ n,
    torLiftMap_eq_comparison N P Q ψ hψ n]

/-- The canonical `Tor` comparison from a resolution to itself is the identity. -/
theorem torComparison_refl (P : ProjectiveResolution M) (n : ℕ) :
    (torComparison N P P n).hom = 𝟙 _ :=
  resolutionComparison_refl (tensorRightFunctor A N) P n

/-- The canonical `Tor` comparisons satisfy the source's composition law. -/
theorem torComparison_trans (P Q R : ProjectiveResolution M) (n : ℕ) :
    (torComparison N P Q n).hom ≫ (torComparison N Q R n).hom =
      (torComparison N P R n).hom :=
  resolutionComparison_trans (tensorRightFunctor A N) P Q R n

end Tor

section Ext


variable (k : Type u) [Field k] {A : Type u} [Ring A] [Algebra k A]
variable (N : ModuleCat.{u} A) {M : ModuleCat.{u} A}

/-- `Ext` computed as the cohomology of `Hom_A(P,-)` for the chosen resolution `P`. -/
noncomputable abbrev ExtByResolution (P : ProjectiveResolution M) (n : ℕ) : ModuleCat.{u} k :=
  (P.complex.linearYonedaObj k N).homology n

/-- A map `Q ⟶ P` of resolutions induces the contravariant cochain map
`Hom_A(P,N) ⟶ Hom_A(Q,N)`. -/
noncomputable def extCochainMap (P Q : ProjectiveResolution M)
    (φ : Q.complex ⟶ P.complex) :
    P.complex.linearYonedaObj k N ⟶ Q.complex.linearYonedaObj k N := by
  let F := ((linearYoneda k (ModuleCat.{u} A)).obj N).rightOp
  exact (HomologicalComplex.unopFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ)).map
    (Quiver.Hom.op ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ))

/-- The map `ξᵢ(Q,P,f)` induced on resolution-computed `Ext` by a resolution morphism
`f : Q ⟶ P`. -/
noncomputable def extLiftMap (P Q : ProjectiveResolution M)
    (φ : Q.complex ⟶ P.complex) (n : ℕ) : ExtByResolution k N P n ⟶ ExtByResolution k N Q n :=
  HomologicalComplex.homologyMap (extCochainMap k N P Q φ) n

/-- Compatible choices of a resolution map induce the same map on `Ext` cohomology. -/
theorem extLiftMap_independent (P Q : ProjectiveResolution M)
    (φ ψ : Q.complex ⟶ P.complex)
    (hφ : φ ≫ P.π = Q.π)
    (hψ : ψ ≫ P.π = Q.π) (n : ℕ) :
    extLiftMap k N P Q φ n = extLiftMap k N P Q ψ n := by
  let F := ((linearYoneda k (ModuleCat.{u} A)).obj N).rightOp
  have h : Homotopy φ ψ := ProjectiveResolution.liftHomotopy (𝟙 M) φ ψ
    (by simpa using hφ) (by simpa using hψ)
  have hF := F.mapHomotopy h
  exact (Homotopy.unop hF).homologyMap_eq n

/-- The homotopy equivalence between the two contravariant Hom complexes, obtained from the
homotopy equivalence of projective resolutions. -/
noncomputable def extResolutionHomotopyEquiv (P Q : ProjectiveResolution M) :
    HomotopyEquiv (P.complex.linearYonedaObj k N) (Q.complex.linearYonedaObj k N) := by
  let F := ((linearYoneda k (ModuleCat.{u} A)).obj N).rightOp
  exact unopHomotopyEquiv (F.mapHomotopyEquiv (ProjectiveResolution.homotopyEquiv Q P))

/-- **Problem 8.2.5(v).** The canonical isomorphism between the `Ext` groups computed from
two projective resolutions. Its forward map is induced by the canonical lift `Q ⟶ P`. -/
noncomputable def extComparison (P Q : ProjectiveResolution M) (n : ℕ) :
    ExtByResolution k N P n ≅ ExtByResolution k N Q n :=
  (extResolutionHomotopyEquiv k N P Q).toHomologyIso n

/-- Every compatible resolution morphism induces the canonical `Ext` comparison isomorphism. -/
theorem extLiftMap_eq_comparison (P Q : ProjectiveResolution M)
    (φ : Q.complex ⟶ P.complex) (hφ : φ ≫ P.π = Q.π) (n : ℕ) :
    extLiftMap k N P Q φ n = (extComparison k N P Q n).hom := by
  rw [extLiftMap_independent k N P Q φ
    (ProjectiveResolution.homotopyEquiv Q P).hom hφ (by simp) n]
  rfl

end Ext

end Problem825

end Etingof
