import EtingofRepresentationTheory.Chapter7.Example7_9_2

/-!
# Downstream import/`#check` test for Example 7.9.2

This file imports `Chapter7/Example7_9_2.lean` and pins the public API asserting that the
functors `Ind_K^G`, `Res_K^G`, and `Hom_G(V, ?)` on `Rep k G` are additive and `k`-linear.
Its purpose is to catch a regression in the source even when cached oleans would otherwise
hide it from the aggregate build: because this file `import`s the item file and
re-elaborates the endpoints, it forces a fresh check of their public signatures.

The regression this test guards against is the linear companion `left_adjoint_linear`
(and hence `indFunctor_linear`) failing to elaborate against the current categorical
linearity API (issue #7526).

See issue #7526 (restore k-linearity of induction in Example 7.9.2).
-/

open CategoryTheory Opposite

-- The `k`-linearity of induction rests on the linear companion of
-- `Adjunction.left_adjoint_additive`; pin it and the three functor endpoints.
#check @Etingof.left_adjoint_linear
#check @Etingof.resFunctor_additive
#check @Etingof.resFunctor_linear
#check @Etingof.indFunctor_additive
#check @Etingof.indFunctor_linear
#check @Etingof.homGFunctor_additive
#check @Etingof.homGFunctor_linear

section
universe u
variable {k G H : Type u} [Field k] [Group G] [Group H] (φ : G →* H)

-- Clients must be able to recover additivity and `k`-linearity of restriction and
-- induction from the public API.
example : (Rep.resFunctor (k := k) φ).Additive := Etingof.resFunctor_additive φ
example : (Rep.resFunctor (k := k) φ).Linear k := Etingof.resFunctor_linear φ
example : (Rep.indFunctor.{u} k φ).Additive := Etingof.indFunctor_additive φ
example : (Rep.indFunctor.{u} k φ).Linear k := Etingof.indFunctor_linear φ

-- The covariant hom-functor `Hom_G(V, ?)` is additive and `k`-linear.
example (V : Rep k G) : ((linearCoyoneda k (Rep k G)).obj (op V)).Additive :=
  Etingof.homGFunctor_additive V
example (V : Rep k G) : ((linearCoyoneda k (Rep k G)).obj (op V)).Linear k :=
  Etingof.homGFunctor_linear V

-- The linear companion transfers `k`-linearity across any adjunction, not just induction.
example {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear k C] [Linear k D] {F : C ⥤ D} {J : D ⥤ C} (adj : F ⊣ J)
    [J.Additive] [J.Linear k] : F.Linear k :=
  Etingof.left_adjoint_linear k adj

end
