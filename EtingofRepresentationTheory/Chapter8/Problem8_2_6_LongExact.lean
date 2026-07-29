import EtingofRepresentationTheory.Chapter8.Problem8_2_6

set_option backward.isDefEq.respectTransparency false

/-!
# Coherent long exact sequences for Problem 8.2.6

The local six-term windows in `Problem8_2_6.lean` are assembled here into globally indexed
cohomological and homological long exact sequence data.  In particular, a single indexed
connecting family is used in every adjacent window.  The degree-zero endpoints are also made
explicit: the first `Ext⁰` map is mono and the last `Tor₀` map is epi, after comparison with
`Hom` and tensor product respectively.  The `Tor` connecting maps are the explicit left-derived
maps from `LeftDerivedSequence.lean`.  Both are natural in the other module parameter, and the
varying-functor construction is also natural under morphisms of short exact sequences.
-/

namespace Etingof

open CategoryTheory

universe u

/-- A cohomological long exact sequence, encoded by one globally indexed connecting family and
an exact six-object window in every pair of adjacent degrees. -/
structure CohomologicalLongExactSequence
    (T1 T2 T3 : ℕ → AddCommGrpCat.{u}) where
  map12 : ∀ n, T1 n ⟶ T2 n
  map23 : ∀ n, T2 n ⟶ T3 n
  connecting : ∀ n, T3 n ⟶ T1 (n + 1)
  window_exact : ∀ n,
    (ComposableArrows.mk₅ (map12 n) (map23 n) (connecting n)
      (map12 (n + 1)) (map23 (n + 1))).Exact

/-- A homological long exact sequence, encoded by one globally indexed connecting family and
an exact six-object window in every pair of adjacent degrees. -/
structure HomologicalLongExactSequence
    (T1 T2 T3 : ℕ → AddCommGrpCat.{u}) where
  map12 : ∀ n, T1 n ⟶ T2 n
  map23 : ∀ n, T2 n ⟶ T3 n
  connecting : ∀ n, T3 (n + 1) ⟶ T1 n
  window_exact : ∀ n,
    (ComposableArrows.mk₅ (map12 (n + 1)) (map23 (n + 1)) (connecting n)
      (map12 n) (map23 n)).Exact

/-! ## Ext in the second argument -/

/-- The globally indexed connecting family in the covariant `Ext` sequence.  It is Yoneda
composition with the extension class of the short exact sequence. -/
noncomputable def Problem_8_2_6_iii_extConnecting
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    AddCommGrpCat.of (Etingof.Ext M S.X₃ n) ⟶
      AddCommGrpCat.of (Etingof.Ext M S.X₁ (n + 1)) :=
  AddCommGrpCat.ofHom (hS.extClass.postcomp M rfl)

/-- **Problem 8.2.6(iii), coherent `Ext` sequence.** The local windows are assembled using the
single family `Problem_8_2_6_iii_extConnecting`. -/
noncomputable def Problem_8_2_6_iii_extLongExact
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    CohomologicalLongExactSequence
      (fun n => AddCommGrpCat.of (Etingof.Ext M S.X₁ n))
      (fun n => AddCommGrpCat.of (Etingof.Ext M S.X₂ n))
      (fun n => AddCommGrpCat.of (Etingof.Ext M S.X₃ n)) where
  map12 n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.f).postcomp M (add_zero n))
  map23 n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.g).postcomp M (add_zero n))
  connecting := Problem_8_2_6_iii_extConnecting A M hS
  window_exact n := by
    simpa [Abelian.Ext.covariantSequence, Problem_8_2_6_iii_extConnecting] using
      Abelian.Ext.covariantSequence_exact M hS n (n + 1) rfl

/-- The zero-ended first map in the covariant `Ext` sequence is mono. -/
theorem Problem_8_2_6_iii_ext_zero_mono
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Mono (AddCommGrpCat.ofHom
      ((Abelian.Ext.mk₀ S.f).postcomp M (add_zero 0))) := by
  letI : Mono S.f := hS.mono_f
  exact Abelian.Ext.mono_postcomp_mk₀_of_mono M S.f

/-- Under `Ext⁰(M,-) ≃ Hom(M,-)`, the first map is ordinary postcomposition by the inclusion. -/
theorem Problem_8_2_6_iii_ext_zero_apply
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (φ : M ⟶ S.X₁) :
    Abelian.Ext.addEquiv₀
      (((Abelian.Ext.mk₀ S.f).postcomp M (add_zero 0))
        (Abelian.Ext.addEquiv₀.symm φ)) = φ ≫ S.f := by
  simp only [Abelian.Ext.addEquiv₀_symm_apply, AddMonoidHom.flip_apply,
    Abelian.Ext.bilinearComp_apply_apply, Abelian.Ext.mk₀_comp_mk₀]
  change Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm (φ ≫ S.f)) = _
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

/-- The displayed covariant `Ext` sequence starts with an exact `0 → Ext⁰(M,X₁) → Ext⁰(M,X₂)`
endpoint. -/
theorem Problem_8_2_6_iii_ext_zero_exact
    (A : Type u) [Ring A] (M : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (ShortComplex.mk
      (0 : AddCommGrpCat.of PUnit ⟶ AddCommGrpCat.of (Etingof.Ext M S.X₁ 0))
      (AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.f).postcomp M (add_zero 0)))
      (by simp)).Exact := by
  letI := Problem_8_2_6_iii_ext_zero_mono A M hS
  apply (ShortComplex.exact_iff_mono _ rfl).2
  infer_instance

/-! ## Ext in the first argument -/

/-- The globally indexed connecting family in the contravariant `Ext` sequence. -/
noncomputable def Problem_8_2_6_v_extConnecting
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    AddCommGrpCat.of (Etingof.Ext S.X₁ N n) ⟶
      AddCommGrpCat.of (Etingof.Ext S.X₃ N (n + 1)) :=
  AddCommGrpCat.ofHom (hS.extClass.precomp N (Nat.one_add n))

/-- **Problem 8.2.6(v), coherent `Ext` sequence.** -/
noncomputable def Problem_8_2_6_v_extLongExact
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    CohomologicalLongExactSequence
      (fun n => AddCommGrpCat.of (Etingof.Ext S.X₃ N n))
      (fun n => AddCommGrpCat.of (Etingof.Ext S.X₂ N n))
      (fun n => AddCommGrpCat.of (Etingof.Ext S.X₁ N n)) where
  map12 n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.g).precomp N (zero_add n))
  map23 n := AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.f).precomp N (zero_add n))
  connecting := Problem_8_2_6_v_extConnecting A N hS
  window_exact n := by
    simpa [Abelian.Ext.contravariantSequence, Problem_8_2_6_v_extConnecting] using
      Abelian.Ext.contravariantSequence_exact hS N n (n + 1) (Nat.one_add n)

/-- The zero-ended first map in the contravariant `Ext` sequence is mono. -/
theorem Problem_8_2_6_v_ext_zero_mono
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Mono (AddCommGrpCat.ofHom
      ((Abelian.Ext.mk₀ S.g).precomp N (zero_add 0))) := by
  letI : Epi S.g := hS.epi_g
  exact Abelian.Ext.mono_precomp_mk₀_of_epi N S.g

/-- Under `Ext⁰(-,N) ≃ Hom(-,N)`, the first map is ordinary precomposition by the quotient. -/
theorem Problem_8_2_6_v_ext_zero_apply
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (φ : S.X₃ ⟶ N) :
    Abelian.Ext.addEquiv₀
      (((Abelian.Ext.mk₀ S.g).precomp N (zero_add 0))
        (Abelian.Ext.addEquiv₀.symm φ)) = S.g ≫ φ := by
  simp only [Abelian.Ext.addEquiv₀_symm_apply, Abelian.Ext.bilinearComp_apply_apply,
    Abelian.Ext.mk₀_comp_mk₀]
  change Abelian.Ext.addEquiv₀ (Abelian.Ext.addEquiv₀.symm (S.g ≫ φ)) = _
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

/-- The displayed contravariant `Ext` sequence starts with an exact
`0 → Ext⁰(X₃,N) → Ext⁰(X₂,N)` endpoint. -/
theorem Problem_8_2_6_v_ext_zero_exact
    (A : Type u) [Ring A] (N : ModuleCat.{u} A)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (ShortComplex.mk
      (0 : AddCommGrpCat.of PUnit ⟶ AddCommGrpCat.of (Etingof.Ext S.X₃ N 0))
      (AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ S.g).precomp N (zero_add 0)))
      (by simp)).Exact := by
  letI := Problem_8_2_6_v_ext_zero_mono A N hS
  apply (ShortComplex.exact_iff_mono _ rfl).2
  infer_instance

/-! ## Tor in the second argument -/

/-- The explicit left-derived connecting map for the second-argument `Tor` sequence. -/
noncomputable def torSndδ
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    Etingof.Tor A S.X₃ M (n + 1) ⟶ Etingof.Tor A S.X₁ M n :=
  NatTrans.leftDerivedδ
    (tensorRightNatTrans A S.f.hom) (tensorRightNatTrans A S.g.hom)
    (tensorRightNatTrans_comp_zero A)
    (fun Y _ => tensorLeftFunctor_map_shortExact A Y hS) M n (n + 1) rfl

/-- Naturality of the second-argument connecting map in the right module. -/
theorem torSndδ_naturality
    (A : Type u) [Ring A] {M M' : ModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ M')
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    torSndδ A M hS n ≫ (TorFunctor A S.X₁ n).map f =
      (TorFunctor A S.X₃ (n + 1)).map f ≫ torSndδ A M' hS n := by
  simpa [torSndδ, TorFunctor] using
    NatTrans.leftDerivedδ_naturality
      (tensorRightNatTrans A S.f.hom) (tensorRightNatTrans A S.g.hom)
      (tensorRightNatTrans_comp_zero A)
      (fun Y _ => tensorLeftFunctor_map_shortExact A Y hS) f n (n + 1) rfl

/-- Naturality of the second-argument connecting map under a morphism of short exact
sequences. -/
theorem torSndδ_naturality_shortComplex
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S T : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    torSndMap A φ.τ₃.hom (n + 1) M ≫ torSndδ A M hT n =
      torSndδ A M hS n ≫ torSndMap A φ.τ₁.hom n M := by
  have comm₁₂ :
      tensorRightNatTrans A φ.τ₁.hom ≫ tensorRightNatTrans A T.f.hom =
        tensorRightNatTrans A S.f.hom ≫ tensorRightNatTrans A φ.τ₂.hom := by
    change (tensorRightBifunctor A).map φ.τ₁ ≫
        (tensorRightBifunctor A).map T.f =
      (tensorRightBifunctor A).map S.f ≫ (tensorRightBifunctor A).map φ.τ₂
    rw [← Functor.map_comp, φ.comm₁₂, Functor.map_comp]
  have comm₂₃ :
      tensorRightNatTrans A φ.τ₂.hom ≫ tensorRightNatTrans A T.g.hom =
        tensorRightNatTrans A S.g.hom ≫ tensorRightNatTrans A φ.τ₃.hom := by
    change (tensorRightBifunctor A).map φ.τ₂ ≫
        (tensorRightBifunctor A).map T.g =
      (tensorRightBifunctor A).map S.g ≫ (tensorRightBifunctor A).map φ.τ₃
    rw [← Functor.map_comp, φ.comm₂₃, Functor.map_comp]
  simpa [torSndδ, torSndMap] using
    NatTrans.leftDerivedδ_naturality_sequence
      (tensorRightNatTrans A S.f.hom) (tensorRightNatTrans A S.g.hom)
      (tensorRightNatTrans_comp_zero A)
      (fun Y _ => tensorLeftFunctor_map_shortExact A Y hS)
      (tensorRightNatTrans A T.f.hom) (tensorRightNatTrans A T.g.hom)
      (tensorRightNatTrans_comp_zero A)
      (fun Y _ => tensorLeftFunctor_map_shortExact A Y hT)
      (tensorRightNatTrans A φ.τ₁.hom) (tensorRightNatTrans A φ.τ₂.hom)
      (tensorRightNatTrans A φ.τ₃.hom) comm₁₂ comm₂₃ M n (n + 1) rfl

/-- A single globally indexed family of connecting maps for the second-argument `Tor` sequence. -/
noncomputable def Problem_8_2_6_iii_torConnecting
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    Etingof.Tor A S.X₃ M (n + 1) ⟶ Etingof.Tor A S.X₁ M n :=
  torSndδ A M hS n

/-- Exactness of every adjacent window for the global second-argument connecting family. -/
theorem Problem_8_2_6_iii_torConnecting_window_exact
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      (torSndMap A S.f.hom (n + 1) M) (torSndMap A S.g.hom (n + 1) M)
      (Problem_8_2_6_iii_torConnecting A M hS n)
      (torSndMap A S.f.hom n M) (torSndMap A S.g.hom n M)).Exact := by
  simpa [Problem_8_2_6_iii_torConnecting, torSndδ, torSndMap] using
    NatTrans.leftDerivedδ_sixTerm_exact
      (tensorRightNatTrans A S.f.hom) (tensorRightNatTrans A S.g.hom)
      (tensorRightNatTrans_comp_zero A)
      (fun Y _ => tensorLeftFunctor_map_shortExact A Y hS) M n (n + 1) rfl

/-- **Problem 8.2.6(iii), coherent `Tor` sequence.** -/
noncomputable def Problem_8_2_6_iii_torLongExact
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    HomologicalLongExactSequence
      (fun n => Etingof.Tor A S.X₁ M n)
      (fun n => Etingof.Tor A S.X₂ M n)
      (fun n => Etingof.Tor A S.X₃ M n) where
  map12 n := torSndMap A S.f.hom n M
  map23 n := torSndMap A S.g.hom n M
  connecting := Problem_8_2_6_iii_torConnecting A M hS
  window_exact := Problem_8_2_6_iii_torConnecting_window_exact A M hS

/-- The degree-zero comparison square identifies `torSndMap` with the ordinary tensor map. -/
theorem Problem_8_2_6_iii_tor_zero_naturality
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} :
    torSndMap A S.g.hom 0 M ≫
        ((tensorRightFunctor A S.X₃).leftDerivedZeroIsoSelf.app M).hom =
      ((tensorRightFunctor A S.X₂).leftDerivedZeroIsoSelf.app M).hom ≫
        (tensorLeftFunctor A M).map S.g := by
  let F1 := tensorRightFunctor A S.X₂
  let F2 := tensorRightFunctor A S.X₃
  let α := tensorRightNatTrans A S.g.hom
  have hα : α.app M = (tensorLeftFunctor A M).map S.g := rfl
  simpa [F1, F2, α, hα, torSndMap] using
    fromLeftDerivedZero_natTrans_app (tensorRightNatTrans A S.g.hom) M

/-- The terminal `Tor₀` map in the second-argument long exact sequence is epi. -/
theorem Problem_8_2_6_iii_tor_zero_epi
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    Epi (torSndMap A S.g.hom 0 M) := by
  let F1 := tensorRightFunctor A S.X₂
  let F2 := tensorRightFunctor A S.X₃
  haveI : Epi S.g := hS.epi_g
  haveI : Epi ((tensorLeftFunctor A M).map S.g) :=
    Functor.map_epi (tensorLeftFunctor A M) S.g
  have hnat := Problem_8_2_6_iii_tor_zero_naturality A M (S := S)
  apply (epi_comp_iff_of_isIso (torSndMap A S.g.hom 0 M)
    (F2.leftDerivedZeroIsoSelf.app M).hom).mp
  rw [hnat]
  infer_instance

/-- The second-argument `Tor` sequence ends in an exact `Tor₀(M,X₂) → Tor₀(M,X₃) → 0`. -/
theorem Problem_8_2_6_iii_tor_zero_exact
    (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (ShortComplex.mk (torSndMap A S.g.hom 0 M)
      (0 : Etingof.Tor A S.X₃ M 0 ⟶ AddCommGrpCat.of PUnit) (by simp)).Exact := by
  letI := Problem_8_2_6_iii_tor_zero_epi A M hS
  apply (ShortComplex.exact_iff_epi _ rfl).2
  infer_instance

/-! ## Tor in the first argument -/

/-- The explicit left-derived connecting map for the first-argument `Tor` sequence. -/
noncomputable def torFstδ
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (n : ℕ) :
    (Etingof.TorFunctor A N (n + 1)).obj S.X₃ ⟶
      (Etingof.TorFunctor A N n).obj S.X₁ :=
  Functor.leftDerivedδ (tensorRightFunctor A N) hS n (n + 1) rfl

/-- Naturality of the first-argument connecting map in the left module. -/
theorem torFstδ_naturality
    (A : Type u) [Ring A]
    {N N' : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (f : N →ₗ[A] N') {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)}
    (hS : S.ShortExact) (n : ℕ) :
    torSndMap A f (n + 1) S.X₃ ≫ torFstδ A N' hS n =
      torFstδ A N hS n ≫ torSndMap A f n S.X₁ := by
  simpa [torFstδ, torSndMap] using
    Functor.leftDerivedδ_naturality_natTrans (tensorRightNatTrans A f) hS n (n + 1) rfl

/-- Naturality of the first-argument connecting map under a morphism of short exact
sequences. -/
theorem torFstδ_naturality_shortComplex
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S T : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) :
    (TorFunctor A N (n + 1)).map φ.τ₃ ≫ torFstδ A N hT n =
      torFstδ A N hS n ≫ (TorFunctor A N n).map φ.τ₁ := by
  simpa [torFstδ, TorFunctor] using
    Functor.leftDerivedδ_naturality_sequence
      (tensorRightFunctor A N) hS hT φ n (n + 1) rfl

/-- A single globally indexed family of connecting maps for the first-argument `Tor` sequence. -/
noncomputable def Problem_8_2_6_v_torConnecting
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (n : ℕ) :
    (Etingof.TorFunctor A N (n + 1)).obj S.X₃ ⟶
      (Etingof.TorFunctor A N n).obj S.X₁ :=
  torFstδ A N hS n

/-- Exactness of every adjacent window for the global first-argument connecting family. -/
theorem Problem_8_2_6_v_torConnecting_window_exact
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) (n : ℕ) :
    (ComposableArrows.mk₅
      ((TorFunctor A N (n + 1)).map S.f) ((TorFunctor A N (n + 1)).map S.g)
      (Problem_8_2_6_v_torConnecting A N hS n)
      ((TorFunctor A N n).map S.f) ((TorFunctor A N n).map S.g)).Exact := by
  simpa [Problem_8_2_6_v_torConnecting, torFstδ, TorFunctor] using
    Functor.leftDerivedδ_sixTerm_exact (tensorRightFunctor A N) hS n (n + 1) rfl

/-- **Problem 8.2.6(v), coherent `Tor` sequence.** -/
noncomputable def Problem_8_2_6_v_torLongExact
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    HomologicalLongExactSequence
      (fun n => (TorFunctor A N n).obj S.X₁)
      (fun n => (TorFunctor A N n).obj S.X₂)
      (fun n => (TorFunctor A N n).obj S.X₃) where
  map12 n := (TorFunctor A N n).map S.f
  map23 n := (TorFunctor A N n).map S.g
  connecting := Problem_8_2_6_v_torConnecting A N hS
  window_exact := Problem_8_2_6_v_torConnecting_window_exact A N hS

/-- The degree-zero comparison square identifies the derived map with the ordinary tensor map. -/
theorem Problem_8_2_6_v_tor_zero_naturality
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} :
    (TorFunctor A N 0).map S.g ≫
        ((tensorRightFunctor A N).leftDerivedZeroIsoSelf.app S.X₃).hom =
      ((tensorRightFunctor A N).leftDerivedZeroIsoSelf.app S.X₂).hom ≫
        (tensorRightFunctor A N).map S.g :=
  (tensorRightFunctor A N).leftDerivedZeroIsoSelf.hom.naturality S.g

/-- The terminal `Tor₀` map in the first-argument long exact sequence is epi. -/
theorem Problem_8_2_6_v_tor_zero_epi
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    Epi ((Etingof.TorFunctor A N 0).map S.g) := by
  change Epi (((Etingof.tensorRightFunctor A N).leftDerived 0).map S.g)
  let F := Etingof.tensorRightFunctor A N
  haveI : Epi S.g := hS.epi_g
  haveI : Epi (F.map S.g) := Functor.map_epi F S.g
  change Epi ((F.leftDerived 0).map S.g)
  apply (epi_comp_iff_of_isIso ((F.leftDerived 0).map S.g)
    (F.leftDerivedZeroIsoSelf.app S.X₃).hom).mp
  change Epi ((F.leftDerived 0).map S.g ≫ F.leftDerivedZeroIsoSelf.hom.app S.X₃)
  rw [F.leftDerivedZeroIsoSelf.hom.naturality S.g]
  infer_instance

/-- The first-argument `Tor` sequence ends in an exact `Tor₀(X₂,N) → Tor₀(X₃,N) → 0`. -/
theorem Problem_8_2_6_v_tor_zero_exact
    (A : Type u) [Ring A] (N : Type u) [AddCommGroup N] [Module A N]
    {S : ShortComplex (ModuleCat.{u} Aᵐᵒᵖ)} (hS : S.ShortExact) :
    (ShortComplex.mk ((TorFunctor A N 0).map S.g)
      (0 : (TorFunctor A N 0).obj S.X₃ ⟶ AddCommGrpCat.of PUnit) (by simp)).Exact := by
  letI := Problem_8_2_6_v_tor_zero_epi A N hS
  apply (ShortComplex.exact_iff_epi _ rfl).2
  infer_instance

end Etingof
