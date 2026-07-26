import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Example 7.3.2: Examples of Natural Transformations

1. On the category of finite dimensional vector spaces FVect_k, the functors id and **
   are isomorphic via the standard maps a_V : V → V**. But on Vect_k they are not
   isomorphic (infinite dimensional V is not isomorphic to V**).
2. On FVect_k' (morphisms = isomorphisms), V ↦ V* is a functor where V ≅ F(V) for
   all V, but it is not isomorphic to the identity functor.
3. If F : A-mod → Vect_k is the forgetful functor, then End(F) = A.
4. The endomorphisms of the identity functor on A-mod is the center of A.

## Mathlib correspondence

The double dual natural isomorphism is captured by `Module.evalEquiv` (for reflexive
modules) and its naturality by `Module.Dual.eval_naturality`. Finite-dimensional
modules over a field are automatically reflexive (`IsReflexive.of_finite_of_free`).
-/

universe u v

/-- The canonical evaluation map gives a linear equivalence `V ≃ₗ[k] V**` for any
finite-dimensional vector space V over a field k. (Etingof Example 7.3.2(1))

The key point is that this isomorphism is natural: for any linear map `f : V →ₗ[k] W`,
the diagram `V → V** → W**` commutes with `V → W → W**`, which is captured by
`Module.Dual.eval_naturality`. -/
noncomputable def Etingof.double_dual_iso
    (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Module.Free k V] :
    V ≃ₗ[k] Module.Dual k (Module.Dual k V) :=
  Module.evalEquiv k V

/-- The double dual evaluation map is natural: for any linear map `f : V →ₗ[k] W`,
we have `f.dualMap.dualMap ∘ eval k V = eval k W ∘ f`. This is the naturality
condition for Example 7.3.2(1), showing the evaluation maps form a natural
transformation from the identity functor to the double dual functor. -/
theorem Etingof.double_dual_naturality
    (k : Type*) [CommSemiring k] (V W : Type*) [AddCommMonoid V] [AddCommMonoid W]
    [Module k V] [Module k W] (f : V →ₗ[k] W) :
    f.dualMap.dualMap ∘ₗ Module.Dual.eval k V = Module.Dual.eval k W ∘ₗ f :=
  Module.Dual.eval_naturality f

/-- **Example 7.3.2(1), second half.** On the category `Vect_k` of all vector
spaces the identity and double-dual functors are not isomorphic. Concretely, `V` is
linearly isomorphic to its double dual `V**` if and only if `V` is finite-dimensional:
in infinite dimension the double dual is strictly larger
(`Module.rank k V < Module.rank k V** `, an Erdős–Kaplansky consequence), so no
isomorphism, let alone a natural one, can exist. Contrast with `double_dual_iso`,
which supplies the isomorphism in the finite-dimensional case. -/
theorem Etingof.linearEquiv_dualDual_iff_finiteDimensional (k V : Type u)
    [Field k] [AddCommGroup V] [Module k V] :
    Nonempty (V ≃ₗ[k] Module.Dual k (Module.Dual k V)) ↔ FiniteDimensional k V := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
    by_contra! contra
    have h₁ : Module.rank k V < Module.rank k (Module.Dual k V) := by
      simpa using lift_rank_lt_rank_dual (K := k) (V := V) contra
    have hℵ : Cardinal.aleph0 ≤ Module.rank k (Module.Dual k V) := le_trans contra h₁.le
    have h₂ : Module.rank k (Module.Dual k V)
        < Module.rank k (Module.Dual k (Module.Dual k V)) := by
      simpa using lift_rank_lt_rank_dual (K := k) (V := Module.Dual k V) hℵ
    have heq : Module.rank k V = Module.rank k (Module.Dual k (Module.Dual k V)) := by
      simpa using e.lift_rank_eq
    exact absurd heq (lt_trans h₁ h₂).ne
  · haveI := h
    exact ⟨Module.evalEquiv k V⟩

/-!
## Example 7.3.2(1), categorical form: the natural isomorphism `𝟭 ≅ (·)**`

The pointwise iso (`double_dual_iso`) and its naturality square (`double_dual_naturality`)
together say that the identity and double-dual *functors* on the category of
finite-dimensional vector spaces are naturally isomorphic. We package this as an
actual `CategoryTheory.NatIso` on `FGModuleCat k`, the category Etingof calls
`FVect_k`. The double-dual functor sends `V ↦ V**` and `f ↦ f.dualMap.dualMap`; the
natural isomorphism to the identity has components the evaluation equivalences
`a_V : V ≃ V**`, `a_V(u)(g) = g(u)` (Mathlib's `Module.evalEquiv`), whose naturality is
`Module.Dual.eval_naturality`.
-/

open CategoryTheory in
/-- The double-dual endofunctor `V ↦ V**` on the category `FGModuleCat k` of
finite-dimensional `k`-vector spaces (`FVect_k`). It acts on a morphism `f` by
`f ↦ f.dualMap.dualMap`; functoriality is definitional
(`LinearMap.dualMap_comp_dualMap`). (Etingof Example 7.3.2(1)) -/
noncomputable def Etingof.doubleDualFunctor (k : Type u) [Field k] :
    FGModuleCat.{u} k ⥤ FGModuleCat.{u} k where
  obj V := FGModuleCat.of k (Module.Dual k (Module.Dual k V))
  map {V W} f := FGModuleCat.ofHom f.hom.hom.dualMap.dualMap
  map_id V := by ext x; rfl
  map_comp f g := by ext x; rfl

open CategoryTheory in
/-- **Example 7.3.2(1), categorical form.** On the category `FGModuleCat k` of
finite-dimensional vector spaces (Etingof's `FVect_k`), the identity functor is
naturally isomorphic to the double-dual functor `(·)**`. The isomorphism has
components the standard evaluation maps `a_V : V → V**`, `a_V(u)(g) = g(u)`; naturality
is `Module.Dual.eval_naturality`. Contrast `linearEquiv_dualDual_iff_finiteDimensional`:
on all of `Vect_k` no such isomorphism exists. -/
noncomputable def Etingof.doubleDualNatIso (k : Type u) [Field k] :
    𝟭 (FGModuleCat.{u} k) ≅ Etingof.doubleDualFunctor k :=
  NatIso.ofComponents
    (fun V => (Module.evalEquiv k (V : Type u)).toFGModuleCatIso)
    (fun {V W} f => by
      ext x
      exact (LinearMap.congr_fun (Module.Dual.eval_naturality f.hom.hom) x).symm)

/-!
## Example 7.3.2(2): the functor `V ↦ V*` on `FVect'_k`

Let `FVect'_k` be the groupoid of finite-dimensional `k`-vector spaces with *isomorphisms*
as morphisms, and `F : FVect'_k → FVect'_k` the functor `V ↦ V*`, `a ↦ (a*)⁻¹`. Etingof's
point is that `F` is pointwise isomorphic to the identity (`V ≅ V*` for every `V`) yet is
not naturally isomorphic to it: a natural iso would give, for every `V`, an isomorphism
`V ≅ V*` compatible with the `GL(V)`-action, which is impossible because `V` and `V*` are
inequivalent as `GL(V)`-representations.

The positive half, `V ≅ V*` exactly when `V` is finite-dimensional, is
`linearEquiv_dual_iff_finiteDimensional` (Mathlib's
`Basis.linearEquiv_dual_iff_finiteDimensional`, an Erdős–Kaplansky consequence, the same
dichotomy `linearEquiv_dualDual_iff_finiteDimensional` gives for the double dual).

The deeper content, non-naturality, is `dual_gl_natural_eq_zero` and its corollary
`not_bijective_of_gl_natural_dual` below. The naturality of a putative isomorphism `η : Id ≅ F`
at the object `V`, tested against the automorphisms `a ∈ GL(V) = V ≃ₗ[k] V`, is exactly the
`GL(V)`-equivariance square `a* ∘ η_V ∘ a = η_V`; a `k`-bilinear reading of this square,
`B(a u, a w) = B(u, w)` for `B(u, w) := η_V u w`, says `B` is a `GL(V)`-invariant bilinear
form. Over any field with a scalar `l ≠ 0`, `l² ≠ 1` (e.g. any field with more than three
elements) the scalar automorphisms `a = l • 𝟙` already force `l² · B = B`, hence `B = 0` and
`η_V = 0`. So no natural family can consist of isomorphisms once `V ≠ 0`: `F` is not naturally
isomorphic to the identity, precisely because `V ≇ V*` as `GL(V)`-representations.

We also package this categorically: `contragredientFunctor k` is `F` itself, built as an
endofunctor of the groupoid `Core (FGModuleCat k)` (Etingof's `FVect'_k`), and
`not_natIso_id_contragredientFunctor` proves `𝟭 ≇ F` there, deriving it from the obstruction
by extracting the component and the scalar-naturality square at the line `k`.
-/

/-- **Example 7.3.2(2), positive part.** A vector space `V` over a field `k` is linearly
isomorphic to its dual `V*` if and only if it is finite-dimensional. This is why the functor
`F : V ↦ V*` of Etingof's Example 7.3.2(2) is pointwise isomorphic to the identity on the
category `FVect'_k` of finite-dimensional spaces. -/
theorem Etingof.linearEquiv_dual_iff_finiteDimensional (k V : Type u)
    [Field k] [AddCommGroup V] [Module k V] :
    Nonempty (V ≃ₗ[k] Module.Dual k V) ↔ FiniteDimensional k V :=
  Basis.linearEquiv_dual_iff_finiteDimensional

/-- **Example 7.3.2(2), non-naturality obstruction.** Let `k` be a field containing a scalar
`l ≠ 0` with `l² ≠ 1` (any field with more than three elements). If `η : V →ₗ[k] V*` is
natural with respect to `GL(V)`, meaning for every linear automorphism `a : V ≃ₗ[k] V` the
square `a* ∘ η ∘ a = η` commutes (equivalently, the bilinear form `B(u, w) = η u w` is
`GL(V)`-invariant: `B(a u, a w) = B(u, w)`), then `η = 0`.

This is the `GL(V)`-representation obstruction behind Etingof's remark that the functor
`F : V ↦ V*` on `FVect'_k` is not naturally isomorphic to the identity: only the scalar
automorphisms `a = l • 𝟙` are used, and they already force `l² · B = B`, hence `B = 0`. -/
theorem Etingof.dual_gl_natural_eq_zero
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (η : V →ₗ[k] Module.Dual k V)
    (hnat : ∀ a : V ≃ₗ[k] V, (a : V →ₗ[k] V).dualMap ∘ₗ η ∘ₗ (a : V →ₗ[k] V) = η)
    (hk : ∃ l : k, l ≠ 0 ∧ l ^ 2 ≠ 1) :
    η = 0 := by
  obtain ⟨l, hl0, hl1⟩ := hk
  -- The scalar automorphism `a = l • 𝟙` of `V`.
  set a : V ≃ₗ[k] V := LinearEquiv.smulOfNeZero k V l hl0 with ha
  ext u w
  -- Evaluate the `GL(V)`-invariance square for `a` at `(u, w)`.
  have h := LinearMap.congr_fun (LinearMap.congr_fun (hnat a) u) w
  simp only [ha, LinearMap.comp_apply, LinearMap.dualMap_apply,
    LinearEquiv.coe_coe, LinearEquiv.smulOfNeZero_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  -- `h : l * (l * η u w) = η u w`, i.e. `l² · (η u w) = η u w`.
  have hzero : (l * l - 1) * η u w = 0 := by
    rw [sub_mul, one_mul, mul_assoc, h, sub_self]
  rcases mul_eq_zero.mp hzero with hcoeff | hval
  · exact absurd (by rw [sq]; exact sub_eq_zero.mp hcoeff) hl1
  · simpa using hval

/-- **Example 7.3.2(2), non-naturality corollary.** Over a field with a scalar `l ≠ 0`,
`l² ≠ 1` (any field with more than three elements), no `GL(V)`-natural family can consist of
isomorphisms when `V ≠ 0`. Concretely, a `GL(V)`-natural `η : V →ₗ[k] V*` is forced to be `0`
(`dual_gl_natural_eq_zero`), hence not bijective. This is why the functor `F : V ↦ V*` on
`FVect'_k` (pointwise isomorphic to the identity by `linearEquiv_dual_iff_finiteDimensional`)
is nonetheless not naturally isomorphic to the identity functor. -/
theorem Etingof.not_bijective_of_gl_natural_dual
    {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]
    (η : V →ₗ[k] Module.Dual k V)
    (hnat : ∀ a : V ≃ₗ[k] V, (a : V →ₗ[k] V).dualMap ∘ₗ η ∘ₗ (a : V →ₗ[k] V) = η)
    (hk : ∃ l : k, l ≠ 0 ∧ l ^ 2 ≠ 1) :
    ¬ Function.Bijective η := by
  intro hbij
  have hη0 : η = 0 := Etingof.dual_gl_natural_eq_zero η hnat hk
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (hbij.injective (by rw [hη0]; simp))

open CategoryTheory in
/-- **Example 7.3.2(2), categorical form: the contragredient functor `F` on `FVect'_k`.**
Etingof's `FVect'_k` is the groupoid of finite-dimensional `k`-vector spaces with
isomorphisms as morphisms; we model it as `Core (FGModuleCat k)`. The contragredient
functor `F` sends `V ↦ V*` and an isomorphism `a : V ≅ W` to `(a*)⁻¹ = (a⁻¹)* : V* ≅ W*`
(the inverse of the transpose; this is why `F` is only functorial on the groupoid, not on
the whole category, where dualization is contravariant). -/
noncomputable def Etingof.contragredientFunctor (k : Type u) [Field k] :
    Core (FGModuleCat.{u} k) ⥤ Core (FGModuleCat.{u} k) where
  obj X := Core.mk (FGModuleCat.of k (Module.Dual k (X.of : Type u)))
  map {X Y} f := ⟨(FGModuleCat.isoToLinearEquiv f.iso).symm.dualMap.toFGModuleCatIso⟩

open CategoryTheory in
/-- **Example 7.3.2(2), categorical form: `𝟭 ≇ F`.** On the groupoid `FVect'_k`
(`Core (FGModuleCat k)`) the identity functor is not naturally isomorphic to the
contragredient functor `F : V ↦ V*`, over any field `k` with a scalar `l ≠ 0`, `l² ≠ 1`
(any field with more than three elements). This is Etingof's statement that `F`, though
pointwise isomorphic to the identity (`linearEquiv_dual_iff_finiteDimensional`), is not
naturally isomorphic to it. The proof extracts, from a putative natural isomorphism, its
component `η : k → k*` at the line `k` and the `GL(k)`-naturality square for scalar
automorphisms, then invokes the obstruction `not_bijective_of_gl_natural_dual`: naturality
forces `η = 0`, contradicting that a component of a natural isomorphism is an isomorphism. -/
theorem Etingof.not_natIso_id_contragredientFunctor (k : Type u) [Field k]
    (hk : ∃ l : k, l ≠ 0 ∧ l ^ 2 ≠ 1) :
    IsEmpty (𝟭 (Core (FGModuleCat.{u} k)) ≅ Etingof.contragredientFunctor k) := by
  refine ⟨fun ε => ?_⟩
  set X₀ : Core (FGModuleCat.{u} k) := Core.mk (FGModuleCat.of k k) with hX
  -- The underlying linear map `η : k →ₗ[k] k*` of the component at the line `k`.
  set η : (k : Type u) →ₗ[k] Module.Dual k k := (ε.hom.app X₀).iso.hom.hom.hom with hη
  -- A component of a natural isomorphism is an isomorphism, so `η` is bijective.
  have hbij : Function.Bijective η :=
    (FGModuleCat.isoToLinearEquiv (ε.hom.app X₀).iso).bijective
  -- The obstruction: no bijective `GL(k)`-natural map `k →ₗ[k] k*` exists.
  refine Etingof.not_bijective_of_gl_natural_dual η (fun a => ?_) hk hbij
  -- Naturality of `ε` against the automorphism `a` of the line `k`.
  have hn := ε.hom.naturality (X := X₀) (Y := X₀) (⟨a.toFGModuleCatIso⟩)
  have hn' := congrArg
    (fun p => (p.iso.hom.hom.hom : (k : Type u) →ₗ[k] Module.Dual k k)) hn
  have rt : FGModuleCat.isoToLinearEquiv a.toFGModuleCatIso = a := by
    ext x; rfl
  have Fmap : ((Etingof.contragredientFunctor k).map (⟨a.toFGModuleCatIso⟩ : X₀ ⟶ X₀)).iso
      = (FGModuleCat.isoToLinearEquiv a.toFGModuleCatIso).symm.dualMap.toFGModuleCatIso := rfl
  simp only [Functor.id_map, coreCategory_comp_iso, Iso.trans_hom, FGModuleCat.hom_hom_comp,
    LinearEquiv.toFGModuleCatIso_hom, Fmap, rt, ← hη] at hn'
  -- The naturality square, read pointwise, is `η (a x) (a w) = η x (a⁻¹ (a w))`.
  refine LinearMap.ext fun x => LinearMap.ext fun w => ?_
  have hx := LinearMap.congr_fun (LinearMap.congr_fun hn' x) (a w)
  have hx2 : (η ((a : k →ₗ[k] k) x)) (a w) = (η x) (a.symm (a w)) := hx
  rw [LinearEquiv.symm_apply_apply] at hx2
  exact hx2

/-!
## Example 7.3.2(3): `End(F) = A` for the forgetful functor `F : A-mod → Vect_k`

Let `A` be a `k`-algebra and `F : A-mod → Vect_k` the forgetful functor. A natural
endomorphism of `F` is a family of `k`-linear maps `η_M : M → M`, one for every
`A`-module `M`, natural with respect to all `A`-linear maps: for every `A`-linear
`f : M → N` (a morphism of `A-mod`, mapped by `F` to the same underlying `k`-linear
map) we have `η_N ∘ f = f ∘ η_M`. The book states, quoting Problem 2.3.17, that the
ring of such natural endomorphisms is `A` itself.

The heart of the statement is that any such family is determined by a single
element `a := η_A 1 ∈ A`, and equals scalar multiplication by that element on every
module. The proof is exactly the Problem 2.3.17 idea specialised across all modules:
for `m ∈ M`, right multiplication `r_m : A → M`, `x ↦ x • m`, is `A`-linear
(`LinearMap.toSpanSingleton`), so naturality applied to `r_m` and evaluated at
`1 ∈ A` gives `η_M m = η_M (r_m 1) = r_m (η_A 1) = (η_A 1) • m`.

The correspondence `a ↦ (m ↦ a • m)` is a ring isomorphism (composition of the
families multiplies the elements in the same order: `a • (b • m) = (a*b) • m`), so
`End(F) ≅ A`, not `Aᵒᵖ`. The opposite appears in Problem 2.3.17 only because there
one composes `A`-linear self-maps of the single module `A`; here the elements act
uniformly on all modules by left multiplication.
-/

/-- **Example 7.3.2(3).** A natural endomorphism `η` of the forgetful functor
`F : A-mod → Vect_k`, a `k`-linear map `η M : M →ₗ[k] M` for every `A`-module `M`,
natural in `M`, acts on every module as scalar multiplication by the single element
`η A 1 ∈ A`. Consequently the natural endomorphisms of `F` are in bijection with `A`
(each is determined by its value `η A 1`), which is the content of `End(F) = A`. The
argument specialises Problem 2.3.17: naturality against right multiplication
`r_m : A → M`, `x ↦ x • m`, forces `η M m = (η A 1) • m`. -/
theorem Etingof.forgetful_natEnd_eq_smul
    {k : Type v} {A : Type u} [CommRing k] [Ring A] [Algebra k A]
    (η : ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M],
          M →ₗ[k] M)
    (hnat : ∀ {M N : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
              [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
              (f : M →ₗ[A] N),
              (f.restrictScalars k).comp (η M) = (η N).comp (f.restrictScalars k))
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] (m : M) :
    η M m = η A 1 • m := by
  -- Right multiplication `r_m : A → M`, `x ↦ x • m`, is `A`-linear.
  have h := hnat (M := A) (N := M) (LinearMap.toSpanSingleton A M m)
  -- Evaluate the naturality square at `1 ∈ A`.
  have h1 := LinearMap.congr_fun h 1
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.toSpanSingleton_apply, one_smul] using h1.symm

/-- The scalar families of Example 7.3.2(3) compose in the same order: acting by `a`
after acting by `b` is acting by `a * b`. This is why the endomorphism ring of the
forgetful functor is `A` itself (not `Aᵒᵖ`). -/
theorem Etingof.forgetful_smul_comp
    {k : Type v} {A : Type u} [CommRing k] [Ring A] [Algebra k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (a b : A) (m : M) :
    a • b • m = (a * b) • m :=
  (mul_smul a b m).symm

/-!
## Example 7.3.2(4): `End(Id_{A-mod}) = Z(A)`

A natural endomorphism of the identity functor on `A-mod` is a family of `A`-linear
maps `η_M : M → M`, one per `A`-module `M`, natural in `M`. As in sub-item (3) the
family is determined by `c := η_A 1`: naturality against right multiplication
`r_m : A → M`, `x ↦ x • m`, forces `η_M m = c • m`. But now the maps are `A`-linear,
and `A`-linearity of `η_A` itself pins `c` down further: it must be central. Indeed
`η_A a = c • a` (determination) while `η_A a = η_A (a • 1) = a • c` (`A`-linearity), so
`c * a = a * c` for every `a ∈ A`. Thus the natural endomorphisms of the identity
functor are exactly the central elements: `End(Id_{A-mod}) = Z(A)`.
-/

/-- **Example 7.3.2(4).** A natural endomorphism `η` of the identity functor on
`A-mod`, an `A`-linear map `η M : M →ₗ[A] M` for every `A`-module `M`, natural in
`M`, acts on every module as scalar multiplication by the single element
`η A 1 ∈ A`. This is the exact analogue of `forgetful_natEnd_eq_smul`, now with
`A`-linear (rather than merely `k`-linear) components. -/
theorem Etingof.idFunctor_natEnd_eq_smul
    {A : Type u} [Ring A]
    (η : ∀ (M : Type u) [AddCommGroup M] [Module A M], M →ₗ[A] M)
    (hnat : ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
              (f : M →ₗ[A] N), f.comp (η M) = (η N).comp f)
    {M : Type u} [AddCommGroup M] [Module A M] (m : M) :
    η M m = η A 1 • m := by
  -- Right multiplication `r_m : A → M`, `x ↦ x • m`, is `A`-linear.
  have h := hnat (M := A) (N := M) (LinearMap.toSpanSingleton A M m)
  -- Evaluate the naturality square at `1 ∈ A`.
  have h1 := LinearMap.congr_fun h 1
  simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul] using h1.symm

/-- **Example 7.3.2(4).** The element `η A 1` determining a natural endomorphism of the
identity functor on `A-mod` lies in the center of `A`: `A`-linearity of `η A`, combined
with the determination `Etingof.idFunctor_natEnd_eq_smul`, forces `η A 1` to commute
with every element of `A`. Together with the determination this is the statement
`End(Id_{A-mod}) = Z(A)`. -/
theorem Etingof.idFunctor_natEnd_central
    {A : Type u} [Ring A]
    (η : ∀ (M : Type u) [AddCommGroup M] [Module A M], M →ₗ[A] M)
    (hnat : ∀ {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
              (f : M →ₗ[A] N), f.comp (η M) = (η N).comp f)
    (b : A) : η A 1 * b = b * η A 1 := by
  -- Determination applied to the regular module `A` at the element `b`.
  have hdet := Etingof.idFunctor_natEnd_eq_smul η hnat (M := A) b
  -- `A`-linearity of `η A` evaluated at `b • 1`.
  have hlin : η A (b • (1 : A)) = b • η A 1 := (η A).map_smul b 1
  rw [smul_eq_mul, mul_one] at hlin
  rw [hlin] at hdet
  simpa only [smul_eq_mul] using hdet.symm

/-!
## Example 7.3.2(3)-(4), bundled form: the ring isomorphisms `End F ≃+* A` and
`End 𝟭 ≃+* Z(A)`

The determination lemmas above say the map `η ↦ η_A 1` from natural endomorphisms to `A` is
injective. That is only half of the book's `End F = A` and `End(id) = Z(A)`: the other half is
that *every* `a ∈ A` (resp. every central `c`) actually arises from a natural family, and that
the correspondence respects the ring structure. This section supplies both halves as genuine
`RingEquiv`s, on Mathlib's real categorical `End`.

The category `A-mod` is `ModuleCat A`; the forgetful functor to `Vect_k` is restriction of
scalars along `algebraMap k A`. `End` of an object in a preadditive category is a ring, and a
functor category into a preadditive category is preadditive, so `End F` is a ring on the nose,
with multiplication `η * θ = θ ≫ η` (`CategoryTheory.End.mul`, in `Function.comp` order).
That order is what makes the answer `A` rather than `Aᵒᵖ`: `(η * θ)_A 1 = η_A (θ_A 1)`, and
determination turns the right-hand side into `(η_A 1) * (θ_A 1)`.
-/

open CategoryTheory in
/-- The forgetful functor `F : A-mod ⥤ Vect_k` of Example 7.3.2(3), realised as restriction of
scalars along `algebraMap k A`. -/
noncomputable abbrev Etingof.forgetfulFunctor (k : Type v) (A : Type u)
    [CommRing k] [Ring A] [Algebra k A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A)

open CategoryTheory in
/-- **Example 7.3.2(3), the reverse direction.** Every `a : A` gives a natural endomorphism of
the forgetful functor `F : A-mod ⥤ Vect_k`, namely the family `m ↦ a • m`. Each component is
`k`-linear because the image of `algebraMap k A` is central (`Algebra.commutes`), and the
family is natural because `A`-linear maps commute with the action of `a`. -/
noncomputable def Etingof.forgetfulSmul {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (a : A) :
    End (Etingof.forgetfulFunctor k A) where
  app M :=
    ModuleCat.ofHom (X := (Etingof.forgetfulFunctor k A).obj M)
      (Y := (Etingof.forgetfulFunctor k A).obj M)
      { toFun := fun m => a • (m : M)
        map_add' := fun x y => smul_add a x y
        map_smul' := fun c m => by
          simp only [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
          rw [← mul_smul, ← mul_smul, Algebra.commutes] }
  naturality M N f := by
    ext m
    exact (f.hom.map_smul a m).symm

open CategoryTheory in
/-- The element of `A` attached to a natural endomorphism of the forgetful functor: the value
of its component at the regular module `A` on `1`. This is the forward map of
`Etingof.forgetfulEndRingEquiv`. -/
noncomputable def Etingof.forgetfulEndElt {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (η : End (Etingof.forgetfulFunctor k A)) : A :=
  (η.app (ModuleCat.of A A)).hom (1 : A)

open CategoryTheory in
/-- **Example 7.3.2(3), determination.** A natural endomorphism of the forgetful functor
`F : A-mod ⥤ Vect_k` acts on every `A`-module as multiplication by the single element
`Etingof.forgetfulEndElt η = η_A 1`. This is `Etingof.forgetful_natEnd_eq_smul` transported to
Mathlib's categorical `End`; the proof is the same Problem 2.3.17 argument, naturality against
the `A`-linear map `r_m : A → M`, `x ↦ x • m`, evaluated at `1`. -/
theorem Etingof.forgetful_natEnd_app_eq_smul {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (η : End (Etingof.forgetfulFunctor k A))
    (M : ModuleCat.{u} A) (m : M) :
    (η.app M).hom m = Etingof.forgetfulEndElt η • m := by
  have h := η.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))
  have h1 := congrArg (fun g => (ModuleCat.Hom.hom g) (1 : A)) h
  -- The two sides of `h1` are definitionally those of the goal, up to `1 • m = m`.
  have h2 : (η.app M).hom ((1 : A) • m) = Etingof.forgetfulEndElt η • m := h1
  rwa [one_smul] at h2

open CategoryTheory in
/-- The scalar family of `a` recovers `a`: the two maps of `Etingof.forgetfulEndRingEquiv` are
inverse on the `A` side. -/
theorem Etingof.forgetfulEndElt_forgetfulSmul {k : Type v} {A : Type u}
    [CommRing k] [Ring A] [Algebra k A] (a : A) :
    Etingof.forgetfulEndElt (Etingof.forgetfulSmul (k := k) a) = a :=
  -- definitionally `a • (1 : A) = a * 1`
  mul_one a

open CategoryTheory in
/-- **Example 7.3.2(3), the book's `End F = A`.** For a `k`-algebra `A`, the endomorphism ring
of the forgetful functor `F : A-mod ⥤ Vect_k` is isomorphic to `A` itself, by `η ↦ η_A 1` with
inverse `a ↦ (m ↦ a • m)`. Injectivity is `Etingof.forgetful_natEnd_app_eq_smul`, surjectivity
is `Etingof.forgetfulSmul`, and multiplicativity is where the answer comes out as `A` and not
`Aᵒᵖ` (see the section docstring). -/
noncomputable def Etingof.forgetfulEndRingEquiv (k : Type v) (A : Type u)
    [CommRing k] [Ring A] [Algebra k A] :
    End (Etingof.forgetfulFunctor k A) ≃+* A where
  toFun := Etingof.forgetfulEndElt
  invFun := Etingof.forgetfulSmul
  left_inv η :=
    NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun m =>
      (Etingof.forgetful_natEnd_app_eq_smul η M m).symm))
  right_inv a := Etingof.forgetfulEndElt_forgetfulSmul a
  map_add' _ _ := rfl
  map_mul' η θ :=
    -- `η * θ = θ ≫ η` (`End.mul` is in `Function.comp` order), so the left-hand side is
    -- definitionally `η_A (θ_A 1)`; determination rewrites it as `(η_A 1) * (θ_A 1)`.
    Etingof.forgetful_natEnd_app_eq_smul η (ModuleCat.of A A)
      ((θ.app (ModuleCat.of A A)).hom (1 : A))

/-!
### Example 7.3.2(4): `End 𝟭 ≃+* Z(A)`
-/

open CategoryTheory in
/-- **Example 7.3.2(4), the reverse direction.** Every central `c : A` gives a natural
endomorphism of the identity functor on `A-mod`, namely `m ↦ c • m`. Centrality is exactly what
makes each component `A`-linear. -/
def Etingof.idSmul {A : Type u} [Ring A] (c : Subring.center A) :
    End (𝟭 (ModuleCat.{u} A)) where
  app M :=
    ModuleCat.ofHom
      { toFun := fun m => (c : A) • (m : M)
        map_add' := fun x y => smul_add (c : A) x y
        map_smul' := fun b m => by
          simp only [RingHom.id_apply, ← mul_smul]
          rw [Subring.mem_center_iff.mp c.2 b] }
  naturality M N f := by
    ext m
    exact (f.hom.map_smul (c : A) m).symm

open CategoryTheory in
/-- The element of `A` attached to a natural endomorphism of the identity functor on `A-mod`:
the value of its component at the regular module on `1`. -/
def Etingof.idEndElt {A : Type u} [Ring A] (η : End (𝟭 (ModuleCat.{u} A))) : A :=
  (η.app (ModuleCat.of A A)).hom (1 : A)

open CategoryTheory in
/-- **Example 7.3.2(4), determination.** A natural endomorphism of the identity functor on
`A-mod` acts on every module as multiplication by `Etingof.idEndElt η = η_A 1`. Same argument as
`Etingof.forgetful_natEnd_app_eq_smul`, now with `A`-linear components. -/
theorem Etingof.idFunctor_natEnd_app_eq_smul {A : Type u} [Ring A]
    (η : End (𝟭 (ModuleCat.{u} A))) (M : ModuleCat.{u} A) (m : M) :
    (η.app M).hom m = Etingof.idEndElt η • m := by
  have h := η.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))
  have h1 := congrArg (fun g => (ModuleCat.Hom.hom g) (1 : A)) h
  have h2 : (η.app M).hom ((1 : A) • m) = Etingof.idEndElt η • m := h1
  rwa [one_smul] at h2

open CategoryTheory in
/-- **Example 7.3.2(4), centrality.** The element determining a natural endomorphism of the
identity functor on `A-mod` lies in the center of `A`: this is `Etingof.idFunctor_natEnd_central`
on Mathlib's categorical `End`. -/
theorem Etingof.idEndElt_mem_center {A : Type u} [Ring A] (η : End (𝟭 (ModuleCat.{u} A))) :
    Etingof.idEndElt η ∈ Subring.center A := by
  refine Subring.mem_center_iff.mpr fun b => ?_
  -- Determination applied to the regular module at the element `b`.
  have hdet : ((η.app (ModuleCat.of A A)).hom (b : A) : A) = Etingof.idEndElt η * b :=
    Etingof.idFunctor_natEnd_app_eq_smul η (ModuleCat.of A A) b
  -- `A`-linearity of the component at `A`, evaluated at `b • 1`.
  have hlin : ((η.app (ModuleCat.of A A)).hom (b * (1 : A)) : A) = b * Etingof.idEndElt η :=
    (η.app (ModuleCat.of A A)).hom.map_smul b (1 : A)
  rw [mul_one] at hlin
  exact hlin.symm.trans hdet

open CategoryTheory in
/-- The natural family of a central `c` recovers `c`. -/
theorem Etingof.idEndElt_idSmul {A : Type u} [Ring A] (c : Subring.center A) :
    Etingof.idEndElt (Etingof.idSmul c) = (c : A) :=
  -- definitionally `(c : A) • (1 : A) = (c : A) * 1`
  mul_one (c : A)

open CategoryTheory in
/-- **Example 7.3.2(4), the book's `End(id_{A-mod}) = Z(A)`.** The endomorphism ring of the
identity functor on `A-mod` is isomorphic to the center of `A`, by `η ↦ η_A 1` with inverse
`c ↦ (m ↦ c • m)`. Well-definedness of the forward map is `Etingof.idEndElt_mem_center`,
injectivity is `Etingof.idFunctor_natEnd_app_eq_smul`, and surjectivity is `Etingof.idSmul`. -/
def Etingof.idFunctorEndRingEquiv (A : Type u) [Ring A] :
    End (𝟭 (ModuleCat.{u} A)) ≃+* Subring.center A where
  toFun η := ⟨Etingof.idEndElt η, Etingof.idEndElt_mem_center η⟩
  invFun c := Etingof.idSmul c
  left_inv η :=
    NatTrans.ext (funext fun M => ModuleCat.hom_ext (LinearMap.ext fun m =>
      (Etingof.idFunctor_natEnd_app_eq_smul η M m).symm))
  right_inv c := Subtype.ext (Etingof.idEndElt_idSmul c)
  map_add' _ _ := rfl
  map_mul' η θ :=
    Subtype.ext (Etingof.idFunctor_natEnd_app_eq_smul η (ModuleCat.of A A)
      ((θ.app (ModuleCat.of A A)).hom (1 : A)))
