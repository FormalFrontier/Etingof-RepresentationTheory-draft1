import Mathlib

/-!
# Example 7.5.3: Representable Forgetful Functor

Let `A` be an algebra. Then the forgetful functor from the category of left `A`-modules
to the category of vector spaces is representable, and the representing object is
the free rank 1 module (= the regular representation) `M = A`.

But if `A` is infinite dimensional and we restrict attention to the category of
finite dimensional modules, then the forgetful functor is, in general, not
representable. Etingof's witness is `A = c₀₀(ℤ)`, the algebra of complex functions on
`ℤ` that vanish at all but finitely many points.

## Mathlib correspondence

### Claim (1): representability of the forgetful functor on all modules

Section 7.5 of the book defines a functor `F : C ⥤ Sets` to be *representable* when it is
isomorphic *as a functor* to `Hom(X, ?)`; an object-indexed family of bijections is not
enough, the family has to be natural. So the endpoint here is a natural isomorphism

`coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat R)`,

built from two mutually inverse natural transformations: evaluation at `1`
(`Etingof.Example753.evalOne`) and multiplication into a chosen element
(`Etingof.Example753.smulOne`, `m ↦ (r ↦ r • m)`). Objectwise this is the core equivalence
`Hom_R(R, M) ≃ M`, which is `LinearMap.ringLmapEquivSelf` in Mathlib
(`Etingof.forgetful_representable`); `Etingof.Example753.forgetCorepresentableBy_homEquiv_eq`
records that the natural isomorphism's components are exactly that equivalence.

Lemma 7.5.1 then pins the representing object down: `Etingof.Example753.uniqueUpToIso` turns
any other corepresenting module into an isomorphism with the regular module `R`.

The book's `F ≅ Hom(X, ?)` is *covariant* in the argument, so the Mathlib API it lands in is
`CategoryTheory.Functor.CorepresentableBy` (representability of a `C ⥤ Type` functor by an
object of `C`), not `RepresentableBy` (which is for `Cᵒᵖ ⥤ Type`).

The enriched (`k`-linear, vector-space-valued) refinement of representability is Remark 7.5.2
rather than this example, and is tracked separately.

### Claim (2): non-representability on finite dimensional modules

Etingof's algebra `A = c₀₀(ℤ)` is non-unital (there is no finitely supported
function equal to `1` everywhere), so its modules fall outside Mathlib's unital `Module`
framework. We formalize the same obstruction over the polynomial algebra `A = k[x]`, an
*equivalent* infinite dimensional algebra: it has infinitely many one dimensional simple
modules (one `ℂ_μ` for each scalar `μ`, where `x` acts as `μ`), yet any finite dimensional
module only "sees" finitely many of them through `Hom`. This is the identical phenomenon
that makes `c₀₀(ℤ)` fail: infinitely many one dimensional simples, each finite dimensional
module reaching only finitely many.

Concretely, a finite dimensional `k[x]`-module is a finite dimensional vector space `V`
together with the endomorphism `S : End k V` giving the action of `x`. The one dimensional
module `ℂ_μ` is `k` with `x` acting by the scalar `μ`. An `A`-module homomorphism
`φ : V → ℂ_μ` is a `k`-linear functional with `φ ∘ S = μ • φ`; these form the space
`forgetfulHom S μ`. It is nonzero exactly when `μ` is an eigenvalue of `S`, and a finite
dimensional `S` has only finitely many eigenvalues. Over an infinite field there is
therefore always a `μ` with `forgetfulHom S μ = 0`, even though `ℂ_μ` is one dimensional.
A representing object `M` would force `dim_k Hom_A(M, ℂ_μ) = dim_k ℂ_μ = 1` for *every*
`μ`, which is impossible: `forgetful_not_representable`.
-/

open Module

universe u

/-- The forgetful functor from `R`-mod to `Type` is representable by the free module `R`.
(Etingof Example 7.5.3, first claim.)

The representing object is `R` itself (the regular representation): the map `f ↦ f(1)`
gives an equivalence `Hom_R(R, M) ≃ M` for any `R`-module `M`. -/
noncomputable def Etingof.forgetful_representable
    (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
    (R →ₗ[R] M) ≃ₗ[ℕ] M :=
  LinearMap.ringLmapEquivSelf R ℕ M

namespace Etingof.Example753

open CategoryTheory Opposite

section Corepresentable

variable (R : Type u) [Ring R]

/-- The objectwise bijection `Hom_R(R, M) ≃ M` of Example 7.5.3, in the category `ModuleCat R`:
evaluation at `1` one way, `m ↦ (r ↦ r • m)` the other.

This is `Etingof.forgetful_representable` transported across `ModuleCat.homEquiv`; see
`forgetCorepresentableBy_homEquiv_eq`. -/
def homEquivOne (M : ModuleCat.{u} R) : (ModuleCat.of R R ⟶ M) ≃ M :=
  ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R ℕ M).toEquiv

@[simp]
theorem homEquivOne_apply (M : ModuleCat.{u} R) (f : ModuleCat.of R R ⟶ M) :
    homEquivOne R M f = ModuleCat.Hom.hom f 1 := rfl

@[simp]
theorem homEquivOne_symm_apply (M : ModuleCat.{u} R) (m : M) :
    (homEquivOne R M).symm m =
      ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ M).symm m) := rfl

/-- **The forgetful functor on all left `R`-modules is representable, by the regular module
`R`** (Etingof Example 7.5.3, first claim), in the categorical sense of Section 7.5: this is
the `Functor.CorepresentableBy` witness, i.e. the natural bijection

`Hom_R(R, M) ≃ M`,

together with its compatibility with postcomposition, which is exactly the naturality the
book's "isomorphism of functors" asks for. -/
def forgetCorepresentableBy :
    (forget (ModuleCat.{u} R)).CorepresentableBy (ModuleCat.of R R) where
  homEquiv {M} := homEquivOne R M
  homEquiv_comp _ _ := rfl

@[simp]
theorem forgetCorepresentableBy_homEquiv (M : ModuleCat.{u} R) :
    (forgetCorepresentableBy R).homEquiv (Y := M) = homEquivOne R M := rfl

instance : (forget (ModuleCat.{u} R)).IsCorepresentable :=
  (forgetCorepresentableBy R).isCorepresentable

/-- **The forgetful functor is isomorphic as a functor to `Hom_R(R, ?)`**
(Etingof Example 7.5.3, first claim, in the form the book states it in Section 7.5: an
isomorphism of functors, not merely an objectwise family of bijections).

Its two halves are `evalOne` and `smulOne` below, and the naturality squares come with the
`Iso` in the functor category. -/
def forgetNatIso : coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat.{u} R) :=
  Functor.corepresentableByEquiv (forgetCorepresentableBy R)

/-- **Evaluation at `1`**: the natural transformation `Hom_R(R, ?) ⟶ forget` sending an
`R`-module map `f : R → M` to `f 1`.

This is the forward half of the book's isomorphism of functors in Example 7.5.3; its
naturality square is `(f ≫ g) 1 = g (f 1)` (`evalOne_naturality`). -/
def evalOne : coyoneda.obj (op (ModuleCat.of R R)) ⟶ forget (ModuleCat.{u} R) :=
  (forgetNatIso R).hom

/-- **Multiplication into a chosen element**: the natural transformation
`forget ⟶ Hom_R(R, ?)` sending `m : M` to the `R`-module map `r ↦ r • m`.

This is the backward half of the book's isomorphism of functors in Example 7.5.3; its
naturality square is `R`-linearity of the module maps (`smulOne_naturality`). -/
def smulOne : forget (ModuleCat.{u} R) ⟶ coyoneda.obj (op (ModuleCat.of R R)) :=
  (forgetNatIso R).inv

@[simp]
theorem forgetNatIso_hom : (forgetNatIso R).hom = evalOne R := rfl

@[simp]
theorem forgetNatIso_inv : (forgetNatIso R).inv = smulOne R := rfl

@[simp]
theorem evalOne_app_apply (M : ModuleCat.{u} R) (f : ModuleCat.of R R ⟶ M) :
    (evalOne R).app M f = ModuleCat.Hom.hom f 1 := rfl

@[simp]
theorem smulOne_app_apply (M : ModuleCat.{u} R) (m : M) :
    (smulOne R).app M m = ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ M).symm m) := rfl

/-- The two natural transformations are mutually inverse, componentwise (one direction). -/
theorem smulOne_app_evalOne_app (M : ModuleCat.{u} R) (f : ModuleCat.of R R ⟶ M) :
    (smulOne R).app M ((evalOne R).app M f) = f :=
  (homEquivOne R M).symm_apply_apply f

/-- The two natural transformations are mutually inverse, componentwise (other direction). -/
theorem evalOne_app_smulOne_app (M : ModuleCat.{u} R) (m : M) :
    (evalOne R).app M ((smulOne R).app M m) = m :=
  (homEquivOne R M).apply_symm_apply m

theorem evalOne_comp_smulOne : evalOne R ≫ smulOne R = 𝟙 _ := (forgetNatIso R).hom_inv_id

theorem smulOne_comp_evalOne : smulOne R ≫ evalOne R = 𝟙 _ := (forgetNatIso R).inv_hom_id

/-- **The naturality square of `evalOne`**, in the form Example 7.5.3 uses it: for every
`R`-module map `g : M ⟶ N`, evaluating at `1` commutes with pushing forward along `g`. -/
theorem evalOne_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (f : ModuleCat.of R R ⟶ M) :
    ModuleCat.Hom.hom (f ≫ g) 1 = g (ModuleCat.Hom.hom f 1) := rfl

/-- **The naturality square of `smulOne`**: pushing `m` forward along `g` and then multiplying
agrees with multiplying and then postcomposing with `g`. -/
theorem smulOne_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N) (m : M) :
    ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ N).symm (g m)) =
      ModuleCat.ofHom ((LinearMap.ringLmapEquivSelf R ℕ M).symm m) ≫ g := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun r => ?_
  simp

/-- **The components of the natural isomorphism agree with the objectwise linear equivalence**
`Etingof.forgetful_representable`, i.e. the categorical statement above really does refine the
previously recorded `Hom_R(R, M) ≃ₗ[ℕ] M`. -/
theorem forgetCorepresentableBy_homEquiv_eq (M : ModuleCat.{u} R) :
    (forgetCorepresentableBy R).homEquiv (Y := M) =
      ModuleCat.homEquiv.trans (Etingof.forgetful_representable R M).toEquiv :=
  rfl

/-- **Uniqueness of the representing object** (Lemma 7.5.1 applied to Example 7.5.3): any
other module corepresenting the forgetful functor is canonically isomorphic to the regular
module `R`. -/
def uniqueUpToIso {X : ModuleCat.{u} R}
    (e : (forget (ModuleCat.{u} R)).CorepresentableBy X) : ModuleCat.of R R ≅ X :=
  (forgetCorepresentableBy R).uniqueUpToIso e

end Corepresentable

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The underlying space of `Hom_A(M, ℂ_μ)` for `A = k[x]`, where `M = (V, S)` is the
finite dimensional module with `x` acting by `S`, and `ℂ_μ` is the one dimensional module
with `x` acting by the scalar `μ`.

An `A`-module map `φ : V → ℂ_μ` is a `k`-linear functional intertwining the two actions,
i.e. `φ ∘ S = μ • φ`. Equivalently `φ` lies in the kernel of `ψ ↦ ψ ∘ S - μ • ψ`. -/
def forgetfulHom (S : Module.End k V) (μ : k) : Submodule k (V →ₗ[k] k) :=
  LinearMap.ker (LinearMap.lcomp k k S - μ • LinearMap.id)

theorem mem_forgetfulHom_iff (S : Module.End k V) (μ : k) (φ : V →ₗ[k] k) :
    φ ∈ forgetfulHom S μ ↔ φ ∘ₗ S = μ • φ := by
  simp only [forgetfulHom, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.lcomp_apply', sub_eq_zero]

/-- If `μ` is not an eigenvalue of the action `S`, then there are no nonzero module maps
`M = (V, S) → ℂ_μ`: the Hom space is trivial.

Intertwining `φ ∘ S = μ • φ` says `φ ∘ (S - μ • 1) = 0`, and when `μ` is not an eigenvalue
`S - μ • 1` is bijective (a finite dimensional injective endomorphism is surjective), so
precomposition with it is injective and forces `φ = 0`. -/
theorem forgetfulHom_eq_bot_of_not_hasEigenvalue [FiniteDimensional k V]
    (S : Module.End k V) (μ : k) (hμ : ¬ S.HasEigenvalue μ) :
    forgetfulHom S μ = ⊥ := by
  -- `S - μ • 1` is injective, hence (finite dimensional) surjective.
  have hker : LinearMap.ker (S - μ • (1 : Module.End k V)) = ⊥ := by
    have h : S.eigenspace μ = ⊥ := not_ne_iff.mp hμ
    rwa [Module.End.eigenspace_def] at h
  have hsurj : Function.Surjective (S - μ • (1 : Module.End k V)) :=
    LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)
  -- Precomposition with a surjection is injective on functionals.
  have hlcomp : Function.Injective
      (LinearMap.lcomp k k (S - μ • (1 : Module.End k V))) :=
    LinearMap.lcomp_injective_of_surjective _ hsurj
  rw [Submodule.eq_bot_iff]
  intro φ hφ
  rw [mem_forgetfulHom_iff] at hφ
  -- `φ ∘ (S - μ • 1) = 0`, so `φ = 0`.
  have hcomp : φ ∘ₗ (S - μ • (1 : Module.End k V)) = 0 := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_smul, LinearMap.zero_apply]
    have hv := LinearMap.congr_fun hφ v
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hv
    rw [hv]; ring
  have h0 : LinearMap.lcomp k k (S - μ • (1 : Module.End k V)) φ
      = LinearMap.lcomp k k (S - μ • (1 : Module.End k V)) 0 := by
    rw [map_zero, LinearMap.lcomp_apply', hcomp]
  exact hlcomp h0

/-- Over an infinite field, **every** finite dimensional module `M = (V, S)` admits a
scalar `μ` for which the Hom space `Hom_A(M, ℂ_μ)` is zero, even though the target module
`ℂ_μ` is one dimensional.

This is the reason for the non-representability: an endomorphism of a finite dimensional
space has finitely many eigenvalues, so over an infinite field some `μ` is not an
eigenvalue, and then `forgetfulHom S μ = ⊥`. -/
theorem exists_forgetfulHom_eq_bot [Infinite k] [FiniteDimensional k V]
    (S : Module.End k V) : ∃ μ : k, forgetfulHom S μ = ⊥ := by
  -- The eigenvalues of `S` form a finite set, so their complement is nonempty.
  have hfin : Set.Finite S.HasEigenvalue := S.finite_hasEigenvalue
  obtain ⟨μ, hμ⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff] at hμ
  exact ⟨μ, forgetfulHom_eq_bot_of_not_hasEigenvalue S μ hμ⟩

/-- **Non-representability of the forgetful functor on finite dimensional modules**
(Etingof Example 7.5.3, second claim).

Take `A = k[x]` with `k` an infinite field, and restrict to finite dimensional modules.
The forgetful functor `A`-mod → Vect_k is not representable: no finite dimensional module
`M = (V, S)` can represent it. Indeed, a representing object would give a natural
isomorphism `Hom_A(M, N) ≅ N` (underlying space) for every finite dimensional `N`, hence
in particular `dim_k Hom_A(M, ℂ_μ) = dim_k ℂ_μ = 1` for every scalar `μ`. But for every
finite dimensional `(V, S)` there is a `μ` with `Hom_A(M, ℂ_μ) = 0` (dimension `0 ≠ 1`).

We record this as the impossibility of the necessary dimension condition
`∀ μ, dim_k (forgetfulHom S μ) = 1`. -/
theorem forgetful_not_representable [Infinite k] [FiniteDimensional k V]
    (S : Module.End k V) :
    ¬ (∀ μ : k, finrank k (forgetfulHom S μ) = 1) := by
  intro h
  obtain ⟨μ, hμ⟩ := exists_forgetfulHom_eq_bot S
  have : finrank k (forgetfulHom S μ) = 0 := by rw [hμ]; exact finrank_bot k (V →ₗ[k] k)
  rw [h μ] at this
  exact one_ne_zero this

end Etingof.Example753
