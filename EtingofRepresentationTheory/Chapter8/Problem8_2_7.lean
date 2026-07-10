import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Module.Opposite
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_4

/-!
# Problem 8.2.7: Tor and Ext for `ℤ` and `k[x]`

* (i) `A = ℤ`, `M`, `N` finitely generated abelian groups: compute `Torᵢ(M, N)` and
  `Extⁱ(M, N)`. (Hint: reduce to cyclic groups via the classification theorem.)
* (ii) `A = k[x]`, `M`, `N` finitely generated modules: the same computation.

## What is formalized here

A finitely generated module over the PID `ℤ` (resp. `k[x]`) is a direct sum of a free module
and cyclic torsion modules, and `Tor`/`Ext` are additive in each argument, so the whole
computation reduces to two cases: a **free** generator and a pair of **cyclic** modules. We
formalize exactly these building blocks — the content the book's "reduce to cyclic groups" hint
points at:

* **Cyclic pair.** For `a, b ≠ 0` (finite cyclic groups `ℤ/a`, `ℤ/b`):
  `Tor₀ ≅ Tor₁ ≅ ℤ/gcd(a,b)` and `Extⁿ⁺² = Ext¹ ≅ Ext⁰ ≅ ℤ/gcd(a,b)`, with `Torᵢ = Extⁱ = 0`
  for `i ≥ 2`. Over `k[x]` the same holds with `ℤ/a ↝ k[x]/(f)` and `gcd(a,b) ↝ gcd(f,g)`.
* **Free generator.** `ℤ` (resp. `k[x]`) is projective, so `Torᵢ₊₁(free, N) = 0` and
  `Extⁱ⁺¹(free, N) = 0`; the degree-`0` values are `free ⊗ N` and `Hom(free, N)` by
  Problem 8.2.6(i).

The right-module argument of `Etingof.Tor` lives in `ModuleCat Aᵐᵒᵖ`; since `ℤ` and `k[x]` are
commutative we equip each cyclic module with its `Aᵐᵒᵖ`-action pulled back along the opposite
ring hom (`local instance`s below).

These are statement-level formalizations (spec-first): the proofs are deferred (`sorry`).
-/

namespace Etingof

open CategoryTheory

universe u

/-! ### Projectivity of the right regular module

The free-generator vanishing theorems need that the first argument `A` (as a **right**
`A`-module, i.e. an `Aᵐᵒᵖ`-module via `op a • x = x * a`) is projective. It is free of rank one:
the map `op : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ` identifies the right regular module with the free rank-one module
`Aᵐᵒᵖ`. -/

/-- The right regular module `A` (over `Aᵐᵒᵖ` via `op a • x = x * a`) is linearly isomorphic,
over `Aᵐᵒᵖ`, to the free rank-one module `Aᵐᵒᵖ`, via `MulOpposite.op`. -/
private def opRegularEquiv (A : Type*) [Ring A] : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ where
  toFun := MulOpposite.op
  map_add' _ _ := rfl
  map_smul' c x := by
    change MulOpposite.op (x * MulOpposite.unop c) = c * MulOpposite.op x
    rw [MulOpposite.op_mul, MulOpposite.op_unop]
  invFun := MulOpposite.unop
  left_inv _ := rfl
  right_inv _ := rfl

/-- The right regular module `A` is projective over `Aᵐᵒᵖ` (it is free of rank one). -/
private instance opRegularProjective (A : Type*) [Ring A] : Module.Projective Aᵐᵒᵖ A :=
  have : Module.Free Aᵐᵒᵖ A := Module.Free.of_equiv (opRegularEquiv A).symm
  Module.Projective.of_free

/-! ### Projective dimension `< 2` from a length-`1` resolution

The cyclic-module higher-vanishing content is: a cyclic module over a PID has projective
dimension `≤ 1`, so `Extⁱ` vanishes for `i ≥ 2`. Categorically, a module `Q` fitting in a short
exact sequence `0 → P₁ → P₀ → Q → 0` with `P₀`, `P₁` projective has
`HasProjectiveDimensionLT Q 2`, and then `HasProjectiveDimensionLT.subsingleton` kills the higher
`Ext`. -/

open Limits in
/-- If `Q = S.X₃` fits in a short exact sequence `0 → S.X₁ → S.X₂ → Q → 0` with `S.X₁`, `S.X₂`
projective, then `Q` has projective dimension `< 2`. (Categorical form of "a length-`1` projective
resolution bounds the projective dimension by `1`".) -/
private lemma hasProjectiveDimensionLT_two_of_shortExact
    {R : Type u} [Ring R] [Small.{u} R] {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (h₁ : Projective S.X₁) (h₂ : Projective S.X₂) :
    HasProjectiveDimensionLT S.X₃ 2 := by
  haveI : HasProjectiveDimensionLT S.X₁ 1 := projective_iff_hasProjectiveDimensionLT_one.mp h₁
  haveI : HasProjectiveDimensionLT S.X₂ 1 := projective_iff_hasProjectiveDimensionLT_one.mp h₂
  haveI : HasProjectiveDimensionLT S.X₂ 2 := hasProjectiveDimensionLT_of_ge S.X₂ 1 2 (by omega)
  exact hS.hasProjectiveDimensionLT_X₃ 1 ‹_› ‹_›

/-! ### Part (i): `A = ℤ` -/

/-- Right `ℤ`-action on `ZMod a` (pulled back from the left action along `ℤᵐᵒᵖ ≃+* ℤ`; the two
coincide because `ℤ` is commutative). Needed to feed `ZMod a` as a right module to
`Etingof.Tor`. -/
noncomputable local instance mopZMod (a : ℕ) : Module ℤᵐᵒᵖ (ZMod a) :=
  Module.compHom (ZMod a) ((RingHom.id ℤ).fromOpposite fun x y => mul_comm x y)

/-- **Problem 8.2.7(i), `Tor₀`.** For finite cyclic groups `ℤ/a`, `ℤ/b` (`a, b ≠ 0`),
`Tor₀(ℤ/a, ℤ/b) ≅ ℤ/gcd(a,b)`. (This is `ℤ/a ⊗_ℤ ℤ/b`, Problem 8.2.6(i).) -/
theorem Problem_8_2_7_i_tor_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (Etingof.Tor ℤ (ZMod b) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) 0
      ≅ AddCommGrpCat.of (ZMod (Nat.gcd a b))) := by
  sorry

/-- **Problem 8.2.7(i), `Tor₁`.** For finite cyclic groups `ℤ/a`, `ℤ/b` (`a, b ≠ 0`),
`Tor₁(ℤ/a, ℤ/b) ≅ ℤ/gcd(a,b)`. -/
theorem Problem_8_2_7_i_tor_one (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (Etingof.Tor ℤ (ZMod b) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) 1
      ≅ AddCommGrpCat.of (ZMod (Nat.gcd a b))) := by
  sorry

/-- **Problem 8.2.7(i), higher `Tor` vanishes.** `Torᵢ(ℤ/a, ℤ/b) = 0` for `i ≥ 2`, because
`ℤ/a` has a length-1 free resolution over the PID `ℤ`. -/
theorem Problem_8_2_7_i_tor_vanish (a b : ℕ) (n : ℕ) :
    Limits.IsZero (Etingof.Tor ℤ (ZMod b) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) (n + 2)) := by
  sorry

/-- **Problem 8.2.7(i), free generator.** `ℤ` is projective as a `ℤ`-module, so
`Torᵢ₊₁(ℤ, N) = 0` for every abelian group `N`. -/
theorem Problem_8_2_7_i_tor_free_vanish (N : Type) [AddCommGroup N] [Module ℤ N] (n : ℕ) :
    Limits.IsZero (Etingof.Tor ℤ N (ModuleCat.of ℤᵐᵒᵖ ℤ) (n + 1)) :=
  Functor.isZero_leftDerived_obj_projective_succ (tensorRightFunctor ℤ N) n
    (ModuleCat.of ℤᵐᵒᵖ ℤ)

/-- **Problem 8.2.7(i), `Ext⁰`.** `Ext⁰(ℤ/a, ℤ/b) = Hom(ℤ/a, ℤ/b) ≅ ℤ/gcd(a,b)` for
`a, b ≠ 0`. -/
theorem Problem_8_2_7_i_ext_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod b)) 0
      ≃+ ZMod (Nat.gcd a b)) := by
  sorry

/-- **Problem 8.2.7(i), `Ext¹`.** `Ext¹(ℤ/a, ℤ/b) ≅ ℤ/gcd(a,b)` for `a, b ≠ 0`. -/
theorem Problem_8_2_7_i_ext_one (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod b)) 1
      ≃+ ZMod (Nat.gcd a b)) := by
  sorry

/-- `ℤ/a` has projective dimension `< 2` as a `ℤ`-module. For `a ≠ 0` the length-`1` free
resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0` exhibits this; for `a = 0`, `ℤ/0 = ℤ` is projective. -/
private lemma zmod_hasProjectiveDimensionLT_two (a : ℕ) :
    HasProjectiveDimensionLT (ModuleCat.of ℤ (ZMod a)) 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · -- `ZMod 0 = ℤ` definitionally, so `ℤ/0` is the projective free module `ℤ`
    haveI : HasProjectiveDimensionLT (ModuleCat.of ℤ ℤ) 1 :=
      projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
    exact hasProjectiveDimensionLT_of_ge (ModuleCat.of ℤ ℤ) 1 2 (by omega)
  · -- the length-`1` free resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0`
    have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha
    let f : ℤ →ₗ[ℤ] ℤ := (a : ℤ) • LinearMap.id
    let g : ℤ →ₗ[ℤ] ZMod a := Algebra.linearMap ℤ (ZMod a)
    have hf : ∀ x : ℤ, f x = (a : ℤ) * x := fun x => by simp [f]
    have hg : ∀ x : ℤ, g x = ((x : ℤ) : ZMod a) := fun x => by
      simp [g, Algebra.linearMap_apply, algebraMap_int_eq, eq_intCast]
    have hgf : ∀ x : ℤ, g (f x) = 0 := by
      intro x
      rw [hf, hg, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact dvd_mul_right _ _
    have eq0 : g.comp f = 0 :=
      LinearMap.ext fun x => by rw [LinearMap.comp_apply, hgf x, LinearMap.zero_apply]
    let S := ModuleCat.shortComplexOfCompEqZero f g eq0
    have hexact : Function.Exact f g := by
      rw [LinearMap.exact_iff]
      ext y
      simp only [LinearMap.mem_ker, hg, ZMod.intCast_zmod_eq_zero_iff_dvd, LinearMap.mem_range, hf]
      constructor
      · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩; exact dvd_mul_right _ _
    have hinj : Function.Injective f := fun x y hxy =>
      mul_left_cancel₀ ha' (by rw [← hf, ← hf, hxy])
    have hsurj : Function.Surjective g := by
      intro z
      obtain ⟨y, rfl⟩ := ZMod.intCast_surjective z
      exact ⟨y, hg y⟩
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexact hinj hsurj
    exact hasProjectiveDimensionLT_two_of_shortExact hS inferInstance inferInstance

/-- **Problem 8.2.7(i), higher `Ext` vanishes.** `Extⁱ(ℤ/a, ℤ/b) = 0` for `i ≥ 2`, because
`ℤ/a` has a length-`1` free resolution over the PID `ℤ`, hence projective dimension `≤ 1`. -/
theorem Problem_8_2_7_i_ext_vanish (a b : ℕ) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod b)) (n + 2)) := by
  haveI := zmod_hasProjectiveDimensionLT_two a
  exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of ℤ (ZMod a)) 2 (n + 2) (by omega) _

/-- **Problem 8.2.7(i), free generator.** `ℤ` is projective, so `Extⁱ⁺¹(ℤ, N) = 0` for every
abelian group `N`. -/
theorem Problem_8_2_7_i_ext_free_vanish (N : ModuleCat.{0} ℤ) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of ℤ ℤ) N (n + 1)) :=
  Abelian.Ext.subsingleton_of_projective (ModuleCat.of ℤ ℤ) N n

/-! ### Part (ii): `A = k[x]` -/

open Polynomial

/-- Right `k[x]`-action on the cyclic module `k[x]/(f)` (pulled back along `k[x]ᵐᵒᵖ ≃+* k[x]`;
the two coincide because `k[x]` is commutative). -/
noncomputable local instance mopPolyQuot (k : Type*) [Field k] (f : k[X]) :
    Module (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f}) :=
  Module.compHom _ ((RingHom.id k[X]).fromOpposite fun x y => mul_comm x y)

/-- **Problem 8.2.7(ii), `Tor₀`.** For cyclic `k[x]`-modules `k[x]/(f)`, `k[x]/(g)`,
`Tor₀(k[x]/(f), k[x]/(g)) ≅ k[x]/(gcd(f,g))`. -/
theorem Problem_8_2_7_ii_tor_zero (k : Type*) [Field k] (f g : k[X]) :
    Nonempty (Etingof.Tor k[X] (k[X] ⧸ Ideal.span {g})
        (ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f})) 0
      ≅ AddCommGrpCat.of (k[X] ⧸ Ideal.span {f, g})) := by
  sorry

/-- **Problem 8.2.7(ii), `Tor₁`.** `Tor₁(k[x]/(f), k[x]/(g)) ≅ k[x]/(gcd(f,g))`. -/
theorem Problem_8_2_7_ii_tor_one (k : Type*) [Field k] (f g : k[X]) :
    Nonempty (Etingof.Tor k[X] (k[X] ⧸ Ideal.span {g})
        (ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f})) 1
      ≅ AddCommGrpCat.of (k[X] ⧸ Ideal.span {f, g})) := by
  sorry

/-- **Problem 8.2.7(ii), higher `Tor` vanishes.** `Torᵢ(k[x]/(f), k[x]/(g)) = 0` for `i ≥ 2`. -/
theorem Problem_8_2_7_ii_tor_vanish (k : Type*) [Field k] (f g : k[X]) (n : ℕ) :
    Limits.IsZero (Etingof.Tor k[X] (k[X] ⧸ Ideal.span {g})
      (ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f})) (n + 2)) := by
  sorry

/-- **Problem 8.2.7(ii), free generator.** `k[x]` is projective, so `Torᵢ₊₁(k[x], N) = 0` for
every `k[x]`-module `N`. -/
theorem Problem_8_2_7_ii_tor_free_vanish (k : Type u) [Field k]
    (N : Type u) [AddCommGroup N] [Module k[X] N] (n : ℕ) :
    Limits.IsZero (Etingof.Tor k[X] N (ModuleCat.of (k[X])ᵐᵒᵖ k[X]) (n + 1)) :=
  Functor.isZero_leftDerived_obj_projective_succ (tensorRightFunctor k[X] N) n
    (ModuleCat.of (k[X])ᵐᵒᵖ k[X])

/-- **Problem 8.2.7(ii), `Ext⁰`.** `Ext⁰(k[x]/(f), k[x]/(g)) = Hom(k[x]/(f), k[x]/(g))
≅ k[x]/(gcd(f,g))`. -/
theorem Problem_8_2_7_ii_ext_zero (k : Type*) [Field k] (f g : k[X]) :
    Nonempty (Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f}))
        (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {g})) 0
      ≃+ (k[X] ⧸ Ideal.span {f, g})) := by
  sorry

/-- **Problem 8.2.7(ii), `Ext¹`.** `Ext¹(k[x]/(f), k[x]/(g)) ≅ k[x]/(gcd(f,g))`. -/
theorem Problem_8_2_7_ii_ext_one (k : Type*) [Field k] (f g : k[X]) :
    Nonempty (Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f}))
        (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {g})) 1
      ≃+ (k[X] ⧸ Ideal.span {f, g})) := by
  sorry

/-- **Problem 8.2.7(ii), higher `Ext` vanishes.** `Extⁱ(k[x]/(f), k[x]/(g)) = 0` for `i ≥ 2`. -/
theorem Problem_8_2_7_ii_ext_vanish (k : Type*) [Field k] (f g : k[X]) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f}))
      (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {g})) (n + 2)) := by
  sorry

/-- **Problem 8.2.7(ii), free generator.** `k[x]` is projective, so `Extⁱ⁺¹(k[x], N) = 0` for
every `k[x]`-module `N`. -/
theorem Problem_8_2_7_ii_ext_free_vanish (k : Type u) [Field k]
    (N : ModuleCat.{u} k[X]) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] k[X]) N (n + 1)) :=
  Abelian.Ext.subsingleton_of_projective (ModuleCat.of k[X] k[X]) N n

end Etingof
