import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
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
    Limits.IsZero (Etingof.Tor ℤ N (ModuleCat.of ℤᵐᵒᵖ ℤ) (n + 1)) := by
  sorry

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

/-- **Problem 8.2.7(i), higher `Ext` vanishes.** `Extⁱ(ℤ/a, ℤ/b) = 0` for `i ≥ 2`. -/
theorem Problem_8_2_7_i_ext_vanish (a b : ℕ) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod b)) (n + 2)) := by
  sorry

/-- **Problem 8.2.7(i), free generator.** `ℤ` is projective, so `Extⁱ⁺¹(ℤ, N) = 0` for every
abelian group `N`. -/
theorem Problem_8_2_7_i_ext_free_vanish (N : ModuleCat.{0} ℤ) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of ℤ ℤ) N (n + 1)) := by
  sorry

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
    Limits.IsZero (Etingof.Tor k[X] N (ModuleCat.of (k[X])ᵐᵒᵖ k[X]) (n + 1)) := by
  sorry

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
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] k[X]) N (n + 1)) := by
  sorry

end Etingof
