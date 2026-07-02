import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Algebra.Tower

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

The key point is that this isomorphism is *natural*: for any linear map `f : V →ₗ[k] W`,
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

/-- **Example 7.3.2(1), second half.** On the category `Vect_k` of *all* vector
spaces the identity and double-dual functors are *not* isomorphic. Concretely, `V` is
linearly isomorphic to its double dual `V**` if and only if `V` is finite-dimensional:
in infinite dimension the double dual is strictly larger
(`Module.rank k V < Module.rank k V** `, an Erdős–Kaplansky consequence), so no
isomorphism — let alone a natural one — can exist. Contrast with `double_dual_iso`,
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
## Example 7.3.2(3): `End(F) = A` for the forgetful functor `F : A-mod → Vect_k`

Let `A` be a `k`-algebra and `F : A-mod → Vect_k` the forgetful functor. A natural
endomorphism of `F` is a family of `k`-linear maps `η_M : M → M`, one for every
`A`-module `M`, natural with respect to all `A`-linear maps: for every `A`-linear
`f : M → N` (a morphism of `A-mod`, mapped by `F` to the same underlying `k`-linear
map) we have `η_N ∘ f = f ∘ η_M`. The book states, quoting Problem 2.3.17, that the
ring of such natural endomorphisms is `A` itself.

The heart of the statement is that any such family is *determined* by a single
element `a := η_A 1 ∈ A`, and equals scalar multiplication by that element on every
module. The proof is exactly the Problem 2.3.17 idea specialised across all modules:
for `m ∈ M`, right multiplication `r_m : A → M`, `x ↦ x • m`, is `A`-linear
(`LinearMap.toSpanSingleton`), so naturality applied to `r_m` and evaluated at
`1 ∈ A` gives `η_M m = η_M (r_m 1) = r_m (η_A 1) = (η_A 1) • m`.

The correspondence `a ↦ (m ↦ a • m)` is a *ring* isomorphism (composition of the
families multiplies the elements in the same order: `a • (b • m) = (a*b) • m`), so
`End(F) ≅ A` — not `Aᵒᵖ`. The opposite appears in Problem 2.3.17 only because there
one composes `A`-linear self-maps of the *single* module `A`; here the elements act
uniformly on all modules by left multiplication.
-/

/-- **Example 7.3.2(3).** A natural endomorphism `η` of the forgetful functor
`F : A-mod → Vect_k` — a `k`-linear map `η M : M →ₗ[k] M` for every `A`-module `M`,
natural in `M` — acts on every module as scalar multiplication by the single element
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

A natural endomorphism of the *identity* functor on `A-mod` is a family of *`A`-linear*
maps `η_M : M → M`, one per `A`-module `M`, natural in `M`. As in sub-item (3) the
family is determined by `c := η_A 1`: naturality against right multiplication
`r_m : A → M`, `x ↦ x • m`, forces `η_M m = c • m`. But now the maps are `A`-linear,
and `A`-linearity of `η_A` itself pins `c` down further — it must be *central*. Indeed
`η_A a = c • a` (determination) while `η_A a = η_A (a • 1) = a • c` (`A`-linearity), so
`c * a = a * c` for every `a ∈ A`. Thus the natural endomorphisms of the identity
functor are exactly the central elements: `End(Id_{A-mod}) = Z(A)`.
-/

/-- **Example 7.3.2(4).** A natural endomorphism `η` of the identity functor on
`A-mod` — an `A`-linear map `η M : M →ₗ[A] M` for every `A`-module `M`, natural in
`M` — acts on every module as scalar multiplication by the single element
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
