import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_3_RightExact

set_option backward.isDefEq.respectTransparency false

/-!
# Second-argument functoriality of `⊗_A` and `Tor` (core for Problem 8.2.6)

This is the upstream core of `Problem8_2_6.lean`, split out to break an import cycle: the
flatness lemma `Etingof.tensorLeftFunctor_map_shortExact` (needed to prove the second-argument
`Tor` long exact sequence, Problem 8.2.6(iii)) lives in `TensorProjectiveExact.lean`, which is
built on top of `tensorLeftFunctor`/`tensorSndMap`.  Those definitions therefore live here, so
that `TensorProjectiveExact.lean` can import this file, and `Problem8_2_6.lean` can in turn
import both this file and `TensorProjectiveExact.lean` without a cycle.

A left `A`-module map `g : N → N'` induces a natural transformation
`tensorRightFunctor A N ⟶ tensorRightFunctor A N'` (apply `id ⊗ g` to the second tensor factor),
and `NatTrans.leftDerived` turns it into a map `Torᵢᴬ(M, N) ⟶ Torᵢᴬ(M, N')` natural in `M`.
We also build `tensorLeftFunctor A M : ModuleCat A ⥤ AddCommGrpCat`, `N ↦ M ⊗_A N`, used to state
the balancing theorem Problem 8.2.6(iv) and to feed the flatness lemma.
-/

namespace Etingof

open CategoryTheory TensorProduct

universe u

noncomputable def tensorSndMap
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Etingof.tensorOver A N M →+ Etingof.tensorOver A N' M :=
  QuotientAddGroup.map (Etingof.balancedSubgroup A N M) (Etingof.balancedSubgroup A N' M)
    (TensorProduct.map (LinearMap.id) g.toAddMonoidHom.toIntLinearMap).toAddMonoidHom
    (by
      -- the induced map sends the balancing relation of `N` into that of `N'`
      refine AddSubgroup.closure_le _ |>.mpr ?_
      rintro x ⟨a, m, n, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨a, m, g n, ?_⟩
      simp only [map_sub, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
        LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_toIntLinearMap, map_smul])

@[simp]
lemma tensorSndMap_mk
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (M : ModuleCat.{u} Aᵐᵒᵖ)
    (m : M) (n : N) :
    tensorSndMap A g M (TensorProduct.tmul ℤ m n : Etingof.tensorOver A N M)
      = (TensorProduct.tmul ℤ m (g n) : Etingof.tensorOver A N' M) :=
  rfl

/-- The natural transformation `- ⊗_A N ⟶ - ⊗_A N'` induced by a left `A`-module map
`g : N → N'`; its components are `tensorSndMap`. -/
noncomputable def tensorRightNatTrans
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') :
    Etingof.tensorRightFunctor A N ⟶ Etingof.tensorRightFunctor A N' where
  app M := AddCommGrpCat.ofHom (tensorSndMap A g M)
  naturality {M M'} f := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb =>
      rw [show ((a + b : TensorProduct ℤ M N) : Etingof.tensorOver A N M)
            = (a : Etingof.tensorOver A N M) + b from
          map_add (QuotientAddGroup.mk' (Etingof.balancedSubgroup A N M)) a b,
        map_add, map_add, ha, hb]

/-- **Second-argument functoriality of `Tor`.** A left `A`-module map `g : N → N'` induces
`Torᵢᴬ(M, N) ⟶ Torᵢᴬ(M, N')`, natural in the right module `M`. Defined as the `n`-th left
derived natural transformation of `tensorRightNatTrans A g`. -/
noncomputable def torSndMap
    (A : Type u) [Ring A] {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (g : N →ₗ[A] N') (n : ℕ) (M : ModuleCat.{u} Aᵐᵒᵖ) :
    Etingof.Tor A N M n ⟶ Etingof.Tor A N' M n :=
  (NatTrans.leftDerived (tensorRightNatTrans A g) n).app M

/-- The functor `N ↦ M ⊗_A N` from left `A`-modules to abelian groups, with the right `A`-module
`M` held fixed. This is the functor whose left derived functors compute `Tor` "the other way"
(from a projective resolution of `N` tensored with `M`), used to state the balancing theorem
Problem 8.2.6(iv). Its action on morphisms is `tensorSndMap`. -/
noncomputable def tensorLeftFunctor (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ) :
    ModuleCat.{u} A ⥤ AddCommGrpCat.{u} where
  obj N := AddCommGrpCat.of (Etingof.tensorOver A N M)
  map {N N'} g := AddCommGrpCat.ofHom (tensorSndMap A g.hom M)
  map_id N := by
    ext x
    induction x with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  map_comp {N N' N''} g g' := by
    ext x
    induction x with
    | zero => simp
    | tmul m n => rfl
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The functor `N ↦ M ⊗_A N` is additive in `N`, so it can be left-derived (Problem 8.2.6(iv)). -/
instance (A : Type u) [Ring A] (M : ModuleCat.{u} Aᵐᵒᵖ) :
    (tensorLeftFunctor A M).Additive where
  map_add {N N' f g} := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    induction y with
    | zero => simp
    | tmul m n =>
      simp only [tensorLeftFunctor, AddCommGrpCat.hom_ofHom, AddCommGrpCat.hom_add,
        AddMonoidHom.add_apply, tensorSndMap_mk, ModuleCat.hom_add, LinearMap.add_apply,
        tmul_add]
      exact map_add (QuotientAddGroup.mk' (Etingof.balancedSubgroup A N' M)) _ _
    | add a b ha hb =>
      rw [show ((a + b : TensorProduct ℤ M N) : Etingof.tensorOver A N M)
            = (a : Etingof.tensorOver A N M) + b from
          map_add (QuotientAddGroup.mk' (Etingof.balancedSubgroup A N M)) a b,
        map_add, map_add, ha, hb]


end Etingof
