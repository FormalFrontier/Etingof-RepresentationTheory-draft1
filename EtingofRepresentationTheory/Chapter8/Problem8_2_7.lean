import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Module.Opposite
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Operations
import EtingofRepresentationTheory.Chapter8.Definition8_2_3
import EtingofRepresentationTheory.Chapter8.Definition8_2_4
import EtingofRepresentationTheory.Chapter8.LeftDerivedSequence
import EtingofRepresentationTheory.Chapter8.Problem8_2_6

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

The reusable number theory is packaged in the `ZModGcd` namespace below: the kernel and
cokernel of multiplication by `a` on `ZMod b` are both `ZMod (gcd a b)`, giving the tensor and
Hom bridges `ZMod a ⊗_ℤ ZMod b ≅ ZMod (gcd a b)` and `Hom_ℤ(ZMod a, ZMod b) ≅ ZMod (gcd a b)`.

Status: part (i) is complete — the degree-`0` identifications (`Tor₀`, `Ext⁰`), the degree-`1`
identifications (`Tor₁`, `Ext¹`), and all higher-degree vanishing are proved. The degree-`1`
groups are read off the length-`1` free resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0` via the derived
six-term sequence: `Tor₁` is the kernel and `Ext¹` the cokernel of multiplication by `a` on
`ℤ/b`. Part (ii) (`k[x]`) is stated but its degree-`0`/`1` proofs are deferred (`sorry`).
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

open Limits in
/-- In a six-term exact window `W₀ → W₁ → W₂ → W₃ → W₄ → W₅`, if the neighbours `W₁` and `W₃` of
`W₂` are both zero then `W₂` is zero. (Used to squeeze a higher `Tor` between two vanishing `Tor`
of the free terms of a length-`1` resolution.) -/
private lemma isZero_obj_two_of_sixTerm_exact
    {D : Type*} [Category D] [Abelian D] {W : ComposableArrows D 5}
    (hW : W.Exact) (h1 : IsZero (W.obj 1)) (h3 : IsZero (W.obj 3)) :
    IsZero (W.obj 2) := by
  have e : (W.sc' hW.toIsComplex 1 2 3).Exact := hW.exact' 1 2 3
  exact e.isZero_X₂ (h1.eq_of_src _ _) (h3.eq_of_tgt _ _)

/-! ### Reusable `ZMod`-gcd isomorphisms

The four degree-0 / degree-1 identifications all reduce to two group isomorphisms about
`ZMod`: the kernel and cokernel of multiplication by `a` on `ZMod b` are both
`ZMod (gcd a b)`. These are not in Mathlib, so we prove them here (over the PID `ℤ`),
together with the tensor and Hom bridges `ZMod a ⊗_ℤ ZMod b ≅ ZMod (gcd a b)` and
`Hom_ℤ(ZMod a, ZMod b) ≅ ZMod (gcd a b)`. -/

namespace ZModGcd

open scoped TensorProduct

noncomputable section

/-- The ℤ-linear cast `ZMod b →ₗ[ℤ] ZMod (gcd a b)` (well-defined since `gcd a b ∣ b`). -/
def castLin (a b : ℕ) : ZMod b →ₗ[ℤ] ZMod (Nat.gcd a b) :=
  (ZMod.castHom (Nat.gcd_dvd_right a b) (ZMod (Nat.gcd a b))).toAddMonoidHom.toIntLinearMap

@[simp] lemma castLin_apply (a b : ℕ) (x : ZMod b) :
    castLin a b x = ZMod.castHom (Nat.gcd_dvd_right a b) (ZMod (Nat.gcd a b)) x := rfl

/-- The image `a • ZMod b` equals the kernel of the cast to `ZMod (gcd a b)`. -/
lemma span_smul_top_eq_ker (a b : ℕ) [NeZero b] :
    Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ (ZMod b)) = LinearMap.ker (castLin a b) := by
  set g := Nat.gcd a b with hg
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr n _
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    rw [LinearMap.mem_ker, map_smul]
    -- (a * c) • (castLin a b n) = 0 in ZMod g
    have hga : (a : ZMod g) = 0 := (ZMod.natCast_eq_zero_iff a g).mpr (Nat.gcd_dvd_left a b)
    rw [zsmul_eq_mul]
    push_cast
    rw [hga]
    ring
  · intro x hx
    rw [LinearMap.mem_ker, castLin_apply, ZMod.castHom_apply, ← ZMod.natCast_val x,
      ZMod.natCast_eq_zero_iff] at hx
    -- g ∣ x.val, so x.val = g * t, and g ∈ (a) in ZMod b by Bezout
    obtain ⟨t, ht⟩ := hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    -- Bezout: (g:ℤ) = a * u + b * v
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (g : ℤ) = a * u + b * v :=
      ⟨Nat.gcdA a b, Nat.gcdB a b, by rw [hg]; exact_mod_cast Nat.gcd_eq_gcd_ab a b⟩
    refine ⟨(u : ZMod b) * (t : ZMod b), Submodule.mem_top, ?_⟩
    -- (a:ℤ) • (u * t) = x
    rw [zsmul_eq_mul]
    have hx' : x = (x.val : ZMod b) := (ZMod.natCast_zmod_val x).symm
    rw [hx', ht]
    have hbz : (b : ZMod b) = 0 := ZMod.natCast_self b
    have : (g : ZMod b) = (a : ZMod b) * (u : ZMod b) := by
      have := congrArg (fun z : ℤ => (z : ZMod b)) huv
      push_cast at this ⊢
      rw [this, hbz]; ring
    push_cast
    rw [this]
    ring

/-- **Cokernel of multiplication by `a` on `ZMod b` is `ZMod (gcd a b)`.** -/
def zmodCokerEquiv (a b : ℕ) [NeZero b] :
    (ZMod b ⧸ (Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ (ZMod b)))) ≃ₗ[ℤ] ZMod (Nat.gcd a b) :=
  (Submodule.quotEquivOfEq _ _ (span_smul_top_eq_ker a b)).trans
    ((castLin a b).quotKerEquivOfSurjective (by
      intro y
      obtain ⟨x, rfl⟩ := ZMod.castHom_surjective (Nat.gcd_dvd_right a b) y
      exact ⟨x, rfl⟩))

/-! ### Kernel of multiplication by `a` on `ZMod b` -/

/-- Multiplication-by-`a` endomorphism of `ZMod b`, as a ℤ-linear map. -/
def mulByCast (a b : ℕ) : ZMod b →ₗ[ℤ] ZMod b := (a : ℤ) • LinearMap.id

@[simp] lemma mulByCast_apply (a b : ℕ) (x : ZMod b) : mulByCast a b x = (a : ℤ) • x := rfl

/-- `ZMod (gcd a b) → ZMod b`, `k ↦ k • (b / gcd a b)`; its image is the `a`-torsion of `ZMod b`. -/
def kerGen (a b : ℕ) [NeZero b] : ZMod (Nat.gcd a b) →ₗ[ℤ] ZMod b :=
  (ZMod.lift (Nat.gcd a b)
    ⟨zmultiplesHom (ZMod b) ((b / Nat.gcd a b : ℕ) : ZMod b), by
      simp only [zmultiplesHom_apply, zsmul_eq_mul]
      rw [Int.cast_natCast, ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b),
        ZMod.natCast_self]⟩).toIntLinearMap

lemma kerGen_intCast (a b : ℕ) [NeZero b] (m : ℤ) :
    kerGen a b (m : ZMod (Nat.gcd a b)) = m • ((b / Nat.gcd a b : ℕ) : ZMod b) := by
  simp only [kerGen, AddMonoidHom.coe_toIntLinearMap, ZMod.lift_coe, zmultiplesHom_apply]

lemma kerGen_apply (a b : ℕ) [NeZero b] (y : ZMod (Nat.gcd a b)) :
    kerGen a b y = (y.val : ℤ) • ((b / Nat.gcd a b : ℕ) : ZMod b) := by
  haveI : NeZero (Nat.gcd a b) := ⟨Nat.gcd_ne_zero_right (NeZero.ne b)⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val y]
  rw [show ((y.val : ℕ) : ZMod (Nat.gcd a b)) = (((y.val : ℕ) : ℤ) : ZMod (Nat.gcd a b)) by
      push_cast; rfl, kerGen_intCast]

/-- **Kernel of multiplication by `a` on `ZMod b` is `ZMod (gcd a b)`** (the `a`-torsion). -/
def zmodKerEquiv (a b : ℕ) [NeZero b] :
    (LinearMap.ker (mulByCast a b)) ≃ₗ[ℤ] ZMod (Nat.gcd a b) := by
  haveI : NeZero (Nat.gcd a b) := ⟨Nat.gcd_ne_zero_right (NeZero.ne b)⟩
  set g := Nat.gcd a b with hg
  have hgpos : 0 < g := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_right (NeZero.ne b))
  have hb'pos : 0 < b / g :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne b)) (Nat.gcd_dvd_right a b)) hgpos
  have hinj : Function.Injective (kerGen a b) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, kerGen_apply, zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at hx
    -- hx : b ∣ x.val * (b/g); goal : x = 0
    rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
    refine (Nat.mul_dvd_mul_iff_right hb'pos).mp ?_
    rwa [Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
  have hz : (a : ℤ) • ((b / g : ℕ) : ZMod b) = 0 := by
    rw [zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    conv_lhs => rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
    exact mul_dvd_mul_right (Nat.gcd_dvd_left a b) _
  have hrange : LinearMap.range (kerGen a b) = LinearMap.ker (mulByCast a b) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, mulByCast_apply, kerGen_apply,
        smul_smul, mul_comm, ← smul_smul, hz, smul_zero]
    · intro x hx
      rw [LinearMap.mem_ker, mulByCast_apply] at hx
      have h1 : b ∣ a * x.val := by
        rwa [← ZMod.natCast_zmod_val x, zsmul_eq_mul, Int.cast_natCast, ← Nat.cast_mul,
          ZMod.natCast_eq_zero_iff] at hx
      have haga' : a = g * (a / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
      have hcop : Nat.Coprime (b / g) (a / g) := (Nat.coprime_div_gcd_div_gcd hgpos).symm
      have hb'dvd : (b / g) ∣ x.val := by
        have hstep : (b / g) ∣ (a / g) * x.val := by
          apply Nat.dvd_of_mul_dvd_mul_left hgpos
          calc g * (b / g) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
            _ ∣ a * x.val := h1
            _ = g * ((a / g) * x.val) := by rw [← mul_assoc, ← haga']
        exact hcop.dvd_of_dvd_mul_left hstep
      obtain ⟨s, hs⟩ := hb'dvd
      refine ⟨((s : ℤ) : ZMod g), ?_⟩
      rw [kerGen_intCast, zsmul_eq_mul, Int.cast_natCast, ← ZMod.natCast_zmod_val x, hs,
        Nat.cast_mul]
      ring
  exact ((LinearEquiv.ofInjective (kerGen a b) hinj).trans
    (LinearEquiv.ofEq _ _ hrange)).symm

/-! ### Tensor and Hom bridges -/

/-- **`ZMod a ⊗_ℤ ZMod b ≃ ZMod (gcd a b)`.** -/
def tensorEquiv (a b : ℕ) [NeZero b] :
    TensorProduct ℤ (ZMod a) (ZMod b) ≃ₗ[ℤ] ZMod (Nat.gcd a b) :=
  let e_a : ZMod a ≃ₗ[ℤ] (ℤ ⧸ Ideal.span {(a : ℤ)}) :=
    ((Int.quotientSpanNatEquivZMod a).symm.toAddEquiv).toIntLinearEquiv
  (TensorProduct.congr e_a (LinearEquiv.refl ℤ (ZMod b))) ≪≫ₗ
    (TensorProduct.quotTensorEquivQuotSMul (ZMod b) (Ideal.span {(a : ℤ)})) ≪≫ₗ
    zmodCokerEquiv a b

/-- The `a`-torsion element `f 1` of a ℤ-linear map `ZMod a → ZMod b`, packaged as an
additive isomorphism `Hom(ZMod a, ZMod b) ≃+ ker(·a)`. -/
def homToKer (a b : ℕ) [NeZero a] :
    (ZMod a →ₗ[ℤ] ZMod b) ≃+ LinearMap.ker (mulByCast a b) where
  toFun f := ⟨f 1, by
    rw [LinearMap.mem_ker, mulByCast_apply, ← map_smul]
    have h1 : (a : ℤ) • (1 : ZMod a) = 0 := by
      rw [zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_self]
    rw [h1, map_zero]⟩
  invFun x := (ZMod.lift a ⟨zmultiplesHom (ZMod b) (x : ZMod b), by
    have hx := LinearMap.mem_ker.mp x.2
    rw [mulByCast_apply] at hx
    simpa only [zmultiplesHom_apply] using hx⟩).toIntLinearMap
  left_inv f := by
    ext z
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, (n : ZMod a) = z :=
      ⟨(z.val : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val]⟩
    rw [AddMonoidHom.coe_toIntLinearMap, ZMod.lift_coe]
    simp only [zmultiplesHom_apply]
    rw [← zsmul_one n, map_zsmul]
  right_inv x := by
    apply Subtype.ext
    change (ZMod.lift a ⟨zmultiplesHom (ZMod b) (x : ZMod b), _⟩).toIntLinearMap 1 = (x : ZMod b)
    rw [AddMonoidHom.coe_toIntLinearMap,
      show (1 : ZMod a) = ((1 : ℤ) : ZMod a) by push_cast; rfl, ZMod.lift_coe]
    simp only [zmultiplesHom_apply, one_zsmul]
  map_add' f g := rfl

/-- **`Hom_ℤ(ZMod a, ZMod b) ≃ ZMod (gcd a b)`.** -/
def homEquiv (a b : ℕ) [NeZero a] [NeZero b] :
    (ZMod a →ₗ[ℤ] ZMod b) ≃+ ZMod (Nat.gcd a b) :=
  (homToKer a b).trans (zmodKerEquiv a b).toAddEquiv

end

end ZModGcd


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
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  -- `Tor₀ ≅ ZMod a ⊗_ℤ ZMod b`, and the latter is `ZMod (gcd a b)`.
  obtain ⟨e₀⟩ := Problem_8_2_6_i_tor ℤ (ZMod b) (ModuleCat.of ℤᵐᵒᵖ (ZMod a))
  refine ⟨e₀ ≪≫ AddEquiv.toAddCommGrpIso ?_⟩
  -- the balancing subgroup is trivial over the commutative base `ℤ`
  have hbot : balancedSubgroup ℤ (ZMod b) (ZMod a) = ⊥ := by
    rw [balancedSubgroup]
    apply le_antisymm _ bot_le
    rw [AddSubgroup.closure_le]
    rintro x ⟨r, m, n, rfl⟩
    simp only [SetLike.mem_coe, AddSubgroup.mem_bot]
    have hop : (MulOpposite.op r • m : ZMod a) = r • m := rfl
    rw [hop, sub_eq_zero]
    exact TensorProduct.smul_tmul r m n
  exact ((QuotientAddGroup.quotientAddEquivOfEq hbot).trans QuotientAddGroup.quotientBot).trans
    (ZModGcd.tensorEquiv a b).toAddEquiv

/-! ### The degree-`0` tensor `ℤ ⊗_ℤ N ≅ N`, for the `Tor₁` connecting-map identification

The `Tor₁` proof reads the degree-`1` group off the length-`1` resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0`
via the six-term sequence, which identifies `Tor₁` with the kernel of the induced map on
`Tor₀(ℤ, N) = ℤ ⊗_ℤ N`. Over the commutative base `ℤ` the module `M = ℤ` has trivial balancing
subgroup, so `tensorOver ℤ N ℤ ≅ N` and the induced map `·a` becomes `mulByCast a b`. -/

open scoped TensorProduct in
/-- For `M = ℤ` over the commutative base `ℤ`, the balancing subgroup of `ℤ ⊗_ℤ N` is trivial. -/
private lemma balancedSubgroup_int_eq_bot (N : Type) [AddCommGroup N] :
    balancedSubgroup ℤ N ℤ = ⊥ := by
  apply le_antisymm _ bot_le
  rw [balancedSubgroup, AddSubgroup.closure_le]
  rintro x ⟨c, m, n, rfl⟩
  simp only [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hop : (MulOpposite.op c • m : ℤ) = c • m := by
    change m * MulOpposite.unop (MulOpposite.op c) = c • m
    rw [MulOpposite.unop_op, smul_eq_mul, mul_comm]
  rw [hop, sub_eq_zero, TensorProduct.smul_tmul]

open scoped TensorProduct in
/-- `ℤ ⊗_ℤ N ≅ N` (the ring tensor product `tensorOver ℤ N ℤ` with `M = ℤ`). -/
private noncomputable def intTensorOverEquiv (N : Type) [AddCommGroup N] :
    tensorOver ℤ N ℤ ≃+ N :=
  (QuotientAddGroup.quotientAddEquivOfEq (balancedSubgroup_int_eq_bot N)).trans
    (QuotientAddGroup.quotientBot.trans (TensorProduct.lid ℤ N).toAddEquiv)

open scoped TensorProduct in
@[simp] private lemma intTensorOverEquiv_mk (N : Type) [AddCommGroup N]
    (m : ℤ) (n : N) :
    intTensorOverEquiv N (TensorProduct.tmul ℤ m n : tensorOver ℤ N ℤ) = m • n := by
  simp only [intTensorOverEquiv, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  rfl

open scoped TensorProduct in
/-- **Problem 8.2.7(i), `Tor₁`.** For finite cyclic groups `ℤ/a`, `ℤ/b` (`a, b ≠ 0`),
`Tor₁(ℤ/a, ℤ/b) ≅ ℤ/gcd(a,b)`. -/
theorem Problem_8_2_7_i_tor_one (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (Etingof.Tor ℤ (ZMod b) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) 1
      ≅ AddCommGrpCat.of (ZMod (Nat.gcd a b))) := by
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  -- Length-`1` resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0` over `ℤᵐᵒᵖ`, inline for access to `S.f`.
  let f : ℤ →ₗ[ℤᵐᵒᵖ] ℤ :=
    { toFun := fun x => (a : ℤ) * x
      map_add' := fun x y => by ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, MulOpposite.smul_eq_mul_unop]; ring }
  let g : ℤ →ₗ[ℤᵐᵒᵖ] ZMod a :=
    { toFun := fun x => (x : ZMod a)
      map_add' := fun x y => by push_cast; ring
      map_smul' := fun r x => by
        have hsmul : (r • (x : ZMod a)) = MulOpposite.unop r • (x : ZMod a) := rfl
        simp only [RingHom.id_apply, MulOpposite.smul_eq_mul_unop, hsmul, zsmul_eq_mul]
        push_cast; ring }
  have hgf : ∀ x : ℤ, g (f x) = 0 := by
    intro x
    change (((a : ℤ) * x : ℤ) : ZMod a) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact dvd_mul_right _ _
  have eq0 : g.comp f = 0 :=
    LinearMap.ext fun x => by rw [LinearMap.comp_apply, hgf x, LinearMap.zero_apply]
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff]; ext y
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    change (((y : ℤ) : ZMod a) = 0) ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact dvd_mul_right _ _
  have hinjf : Function.Injective f := fun x y hxy =>
    mul_left_cancel₀ ha' (by simpa only [f, LinearMap.coe_mk, AddHom.coe_mk] using hxy)
  have hsurjg : Function.Surjective g := by
    intro z; obtain ⟨y, rfl⟩ := ZMod.intCast_surjective z; exact ⟨y, rfl⟩
  set S := ModuleCat.shortComplexOfCompEqZero f g eq0 with hSdef
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexact hinjf hsurjg
  set F := tensorRightFunctor ℤ (ZMod b) with hF
  -- Six-term window `0 = L₁X₁ → 0 = L₁X₂ → Tor₁ →[δ] Tor₀ℤ →[φ] Tor₀ℤ → …`.
  obtain ⟨δ, hExact⟩ := Etingof.Functor.leftDerived_sixTerm_exact F hS 0 1 rfl
  let φ : (F.leftDerived 0).obj S.X₁ ⟶ (F.leftDerived 0).obj S.X₂ := (F.leftDerived 0).map S.f
  -- `L₁X₂ = 0` (`S.X₂ = ℤ` projective), so `δ` is mono.
  have h1 : Limits.IsZero ((F.leftDerived 1).obj S.X₂) :=
    Functor.isZero_leftDerived_obj_projective_succ F 0 S.X₂
  have hmono : Mono δ := by
    have e123 := hExact.exact' 1 2 3
    rwa [ShortComplex.exact_iff_mono _ (h1.eq_zero_of_src _)] at e123
  have hinjδ : Function.Injective δ.hom := (AddCommGrpCat.mono_iff_injective δ).mp hmono
  -- Exactness at `Tor₀ℤ`: `range δ = ker φ`.
  have hrk : δ.hom.range = φ.hom.ker := (hExact.exact' 2 3 4).ab_range_eq_ker
  have hcompl : δ ≫ φ = 0 := hExact.toIsComplex.zero' 2 3 4
  -- `Tor₀(ℤ) = ℤ ⊗_ℤ (ZMod b) ≅ ZMod b`, natural in the argument (`leftDerivedZeroIsoSelf`).
  let ζ := F.leftDerivedZeroIsoSelf
  let τ₁ : ((F.leftDerived 0).obj S.X₁) ≃+ ZMod b :=
    (ζ.app S.X₁).addCommGroupIsoToAddEquiv.trans (intTensorOverEquiv (ZMod b))
  let τ₂ : ((F.leftDerived 0).obj S.X₂) ≃+ ZMod b :=
    (ζ.app S.X₂).addCommGroupIsoToAddEquiv.trans (intTensorOverEquiv (ZMod b))
  -- The induced map `φ` on `Tor₀(ℤ)` is multiplication by `a`.
  have key : ∀ w : tensorOver ℤ (ZMod b) S.X₁,
      intTensorOverEquiv (ZMod b) (tensorRightMap ℤ (ZMod b) S.f w)
        = ZModGcd.mulByCast a b (intTensorOverEquiv (ZMod b) w) := by
    intro w
    induction w using QuotientAddGroup.induction_on with
    | _ y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul m n =>
        change intTensorOverEquiv (ZMod b)
            (tensorRightMap ℤ (ZMod b) S.f (TensorProduct.tmul ℤ m n : tensorOver ℤ (ZMod b) S.X₁))
          = ZModGcd.mulByCast a b
            (intTensorOverEquiv (ZMod b) (TensorProduct.tmul ℤ m n : tensorOver ℤ (ZMod b) S.X₁))
        rw [show tensorRightMap ℤ (ZMod b) S.f
              (TensorProduct.tmul ℤ m n : tensorOver ℤ (ZMod b) S.X₁)
            = (TensorProduct.tmul ℤ (S.f.hom m) n : tensorOver ℤ (ZMod b) S.X₂) from rfl,
          intTensorOverEquiv_mk, intTensorOverEquiv_mk, ZModGcd.mulByCast_apply, smul_smul]
        rfl
      | add p q hp hq =>
        rw [show ((p + q : TensorProduct ℤ S.X₁ (ZMod b)) : tensorOver ℤ (ZMod b) S.X₁)
              = ((p : tensorOver ℤ (ZMod b) S.X₁) + (q : tensorOver ℤ (ZMod b) S.X₁))
            from map_add (QuotientAddGroup.mk' _) p q,
          map_add, map_add, map_add, map_add, hp, hq]
  have hconj : ∀ x, τ₂ (φ.hom x) = ZModGcd.mulByCast a b (τ₁ x) := by
    intro x
    have hn := congrArg (fun (m : (F.leftDerived 0).obj S.X₁ ⟶ F.obj S.X₂) => m.hom x)
      (ζ.hom.naturality S.f)
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hn
    simp only [τ₁, τ₂, AddEquiv.trans_apply, Iso.addCommGroupIsoToAddEquiv_apply]
    calc intTensorOverEquiv (ZMod b) ((ζ.app S.X₂).hom (φ.hom x))
        = intTensorOverEquiv (ZMod b)
            (tensorRightMap ℤ (ZMod b) S.f ((ζ.app S.X₁).hom x)) :=
          congrArg (intTensorOverEquiv (ZMod b)) hn
      _ = ZModGcd.mulByCast a b (intTensorOverEquiv (ZMod b) ((ζ.app S.X₁).hom x)) :=
          key _
  -- Assemble: `Tor₁ = W.obj 2 ≃+ ker(mulByCast) ≃+ ZMod (gcd a b)`.
  have mem : ∀ x, τ₁ (δ.hom x) ∈ LinearMap.ker (ZModGcd.mulByCast a b) := by
    intro x
    rw [LinearMap.mem_ker, ← hconj (δ.hom x)]
    have : φ.hom (δ.hom x) = 0 := by
      have := congrArg
        (fun (m : (F.leftDerived 1).obj S.X₃ ⟶ (F.leftDerived 0).obj S.X₂) => m.hom x) hcompl
      simpa only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply] using this
    rw [this, map_zero]
  let κ : ((F.leftDerived 1).obj S.X₃) →+ LinearMap.ker (ZModGcd.mulByCast a b) :=
    { toFun := fun x => ⟨τ₁ (δ.hom x), mem x⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun x y => by apply Subtype.ext; simp }
  have hκbij : Function.Bijective κ := by
    constructor
    · intro x y hxy
      apply hinjδ
      apply τ₁.injective
      exact congrArg Subtype.val hxy
    · rintro ⟨z, hz⟩
      have hwker : (τ₁.symm z) ∈ φ.hom.ker := by
        rw [AddMonoidHom.mem_ker]
        apply τ₂.injective
        rw [hconj, map_zero, τ₁.apply_symm_apply]
        exact (LinearMap.mem_ker.mp hz)
      rw [← hrk] at hwker
      obtain ⟨x, hx⟩ := hwker
      exact ⟨x, Subtype.ext (by rw [show ((κ x : _) : ZMod b) = τ₁ (δ.hom x) from rfl, hx,
        τ₁.apply_symm_apply])⟩
  exact ⟨((AddEquiv.ofBijective κ hκbij).trans
    (ZModGcd.zmodKerEquiv a b).toAddEquiv).toAddCommGrpIso⟩

/-- The right-module length-`1` free resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0` over `ℤᵐᵒᵖ`
(`a ≠ 0`): `ℤ` and `ℤ/a` as right `ℤ`-modules, with `·a` and the quotient map made `ℤᵐᵒᵖ`-linear.
The underlying functions match the left-module resolution used for the `Ext` side. -/
private noncomputable def zmodMopResolution (a : ℕ) (ha : a ≠ 0) :
    {S : ShortComplex (ModuleCat.{0} ℤᵐᵒᵖ) //
      S.ShortExact ∧ S.X₁ = ModuleCat.of ℤᵐᵒᵖ ℤ ∧ S.X₂ = ModuleCat.of ℤᵐᵒᵖ ℤ ∧
      S.X₃ = ModuleCat.of ℤᵐᵒᵖ (ZMod a)} :=
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  let f : ℤ →ₗ[ℤᵐᵒᵖ] ℤ :=
    { toFun := fun x => (a : ℤ) * x
      map_add' := fun x y => by ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, MulOpposite.smul_eq_mul_unop]; ring }
  let g : ℤ →ₗ[ℤᵐᵒᵖ] ZMod a :=
    { toFun := fun x => (x : ZMod a)
      map_add' := fun x y => by push_cast; ring
      map_smul' := fun r x => by
        have hsmul : (r • (x : ZMod a)) = MulOpposite.unop r • (x : ZMod a) := rfl
        simp only [RingHom.id_apply, MulOpposite.smul_eq_mul_unop, hsmul, zsmul_eq_mul]
        push_cast; ring }
  have hf : ∀ x : ℤ, f x = (a : ℤ) * x := fun _ => rfl
  have hg : ∀ x : ℤ, g x = ((x : ℤ) : ZMod a) := fun _ => rfl
  have hgf : ∀ x : ℤ, g (f x) = 0 := by
    intro x; rw [hf, hg, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact dvd_mul_right _ _
  have eq0 : g.comp f = 0 :=
    LinearMap.ext fun x => by rw [LinearMap.comp_apply, hgf x, LinearMap.zero_apply]
  let S := ModuleCat.shortComplexOfCompEqZero f g eq0
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff]; ext y
    simp only [LinearMap.mem_ker, hg, ZMod.intCast_zmod_eq_zero_iff_dvd, LinearMap.mem_range, hf]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact dvd_mul_right _ _
  have hinj : Function.Injective f := fun x y hxy => mul_left_cancel₀ ha' (by rw [← hf, ← hf, hxy])
  have hsurj : Function.Surjective g := by
    intro z; obtain ⟨y, rfl⟩ := ZMod.intCast_surjective z; exact ⟨y, hg y⟩
  ⟨S, ModuleCat.shortComplex_shortExact S hexact hinj hsurj, rfl, rfl, rfl⟩

/-- `ZMod 0 = ℤ` as a right `ℤ`-module (via `mopZMod`) is `ℤᵐᵒᵖ`-linearly the free rank-one
module `ℤ` (via `Semiring.toOppositeModule`); the two `ℤᵐᵒᵖ`-actions agree by commutativity. -/
private noncomputable def zmodZeroOpEquiv : ℤ ≃ₗ[ℤᵐᵒᵖ] (ZMod 0) :=
  { (AddEquiv.refl ℤ) with
    map_smul' := fun r x => by
      rw [MulOpposite.smul_eq_mul_unop]
      show x * MulOpposite.unop r = MulOpposite.unop r • x
      rw [smul_eq_mul, mul_comm] }

open Limits in
/-- **Problem 8.2.7(i), higher `Tor` vanishes.** `Torᵢ(ℤ/a, ℤ/b) = 0` for `i ≥ 2`, because
`ℤ/a` has a length-`1` free resolution over the PID `ℤ`. For `i ≥ 2` the `Tor` is squeezed
between the vanishing `Tor` of the two free terms in the six-term long exact sequence. -/
theorem Problem_8_2_7_i_tor_vanish (a b : ℕ) (n : ℕ) :
    Limits.IsZero (Etingof.Tor ℤ (ZMod b) (ModuleCat.of ℤᵐᵒᵖ (ZMod a)) (n + 2)) := by
  rcases eq_or_ne a 0 with rfl | ha
  · -- `ZMod 0 = ℤ` is a projective (free rank-one) right module
    have hz := Functor.isZero_leftDerived_obj_projective_succ
      (tensorRightFunctor ℤ (ZMod b)) (n + 1) (ModuleCat.of ℤᵐᵒᵖ ℤ)
    exact hz.of_iso
      (((tensorRightFunctor ℤ (ZMod b)).leftDerived (n + 2)).mapIso
        zmodZeroOpEquiv.symm.toModuleIso)
  · obtain ⟨S, hS, hX₁, hX₂, hX₃⟩ := zmodMopResolution a ha
    set F := tensorRightFunctor ℤ (ZMod b) with hF
    obtain ⟨δ, hExact⟩ := Etingof.Functor.leftDerived_sixTerm_exact F hS (n + 1) (n + 2) rfl
    have h1 : IsZero ((F.leftDerived (n + 2)).obj S.X₂) := by
      rw [hX₂]; exact Functor.isZero_leftDerived_obj_projective_succ F (n + 1) _
    have h3 : IsZero ((F.leftDerived (n + 1)).obj S.X₁) := by
      rw [hX₁]; exact Functor.isZero_leftDerived_obj_projective_succ F n _
    have hgoal : IsZero ((F.leftDerived (n + 2)).obj S.X₃) :=
      isZero_obj_two_of_sixTerm_exact hExact h1 h3
    rw [hX₃] at hgoal
    exact hgoal

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
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  -- `Ext⁰ ≃+ Hom_ℤ(ZMod a, ZMod b)`, and the latter is `ZMod (gcd a b)`.
  obtain ⟨e₀⟩ := Problem_8_2_6_i_ext ℤ (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod b))
  exact ⟨e₀.trans (ModuleCat.homAddEquiv.trans (ZModGcd.homEquiv a b))⟩

/-- **Problem 8.2.7(i), `Ext¹`.** `Ext¹(ℤ/a, ℤ/b) ≅ ℤ/gcd(a,b)` for `a, b ≠ 0`. -/
theorem Problem_8_2_7_i_ext_one (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (Etingof.Ext (ModuleCat.of ℤ (ZMod a)) (ModuleCat.of ℤ (ZMod b)) 1
      ≃+ ZMod (Nat.gcd a b)) := by
  haveI : NeZero a := ⟨ha⟩
  haveI : NeZero b := ⟨hb⟩
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  -- Length-`1` resolution `0 → ℤ →(·a) ℤ → ℤ/a → 0` over `ModuleCat ℤ`, inline for access to `S.f`.
  let f : ℤ →ₗ[ℤ] ℤ := (a : ℤ) • LinearMap.id
  let g : ℤ →ₗ[ℤ] ZMod a := Algebra.linearMap ℤ (ZMod a)
  have hf : ∀ x : ℤ, f x = (a : ℤ) * x := fun x => by simp [f]
  have hg : ∀ x : ℤ, g x = ((x : ℤ) : ZMod a) := fun x => by
    simp [g, Algebra.linearMap_apply, algebraMap_int_eq, eq_intCast]
  have hgf : ∀ x : ℤ, g (f x) = 0 := by
    intro x; rw [hf, hg, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact dvd_mul_right _ _
  have eq0 : g.comp f = 0 :=
    LinearMap.ext fun x => by rw [LinearMap.comp_apply, hgf x, LinearMap.zero_apply]
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff]; ext y
    simp only [LinearMap.mem_ker, hg, ZMod.intCast_zmod_eq_zero_iff_dvd, LinearMap.mem_range, hf]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact dvd_mul_right _ _
  have hinjf : Function.Injective f :=
    fun x y hxy => mul_left_cancel₀ ha' (by rw [← hf, ← hf, hxy])
  have hsurjg : Function.Surjective g := by
    intro z; obtain ⟨y, rfl⟩ := ZMod.intCast_surjective z; exact ⟨y, hg y⟩
  set S := ModuleCat.shortComplexOfCompEqZero f g eq0 with hSdef
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexact hinjf hsurjg
  set Y := ModuleCat.of ℤ (ZMod b) with hY
  -- Contravariant six-term window `Ext⁰(ℤ/a) → Ext⁰(ℤ) →[·a] Ext⁰(ℤ) →[δ] Ext¹(ℤ/a) → 0 → 0`.
  have hExactCS := Abelian.Ext.contravariantSequence_exact hS Y 0 1 (by norm_num)
  -- Connecting map `δ : Ext⁰(ℤ, ℤ/b) → Ext¹(ℤ/a, ℤ/b)`, and precomposition-by-`·a` map.
  let dhom : Etingof.Ext S.X₁ Y 0 →+ Etingof.Ext S.X₃ Y 1 := hS.extClass.precomp Y (by norm_num)
  let m12 : Etingof.Ext S.X₂ Y 0 →+ Etingof.Ext S.X₁ Y 0 :=
    (Abelian.Ext.mk₀ S.f).precomp Y (zero_add 0)
  -- `Ext¹(ℤ, ℤ/b) = 0`, so `δ` is surjective; and `ker δ = range(·a)`.
  have hsurjδ : Function.Surjective dhom := by
    rw [← AddMonoidHom.range_eq_top,
      show dhom.range = _ from (hExactCS.exact' 2 3 4).ab_range_eq_ker]
    ext x
    simp only [AddSubgroup.mem_top, iff_true, AddMonoidHom.mem_ker]
    exact (Abelian.Ext.subsingleton_of_projective S.X₂ Y 0).elim _ _
  have hkerδ : dhom.ker = m12.range := ((hExactCS.exact' 1 2 3).ab_range_eq_ker).symm
  -- `Ext⁰(ℤ, ℤ/b) ≅ Hom_ℤ(ℤ, ℤ/b) ≅ ℤ/b`, sending `α ↦ (addEquiv₀ α)(1)`.
  let e0 : (Etingof.Ext S.X₁ Y 0) ≃+ ZMod b :=
    (Abelian.Ext.addEquiv₀).trans (ModuleCat.homAddEquiv.trans
      (LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod b)).toAddEquiv)
  -- The precomposition map `·a` on `Ext⁰(ℤ)` is multiplication by `a` on `ℤ/b`.
  have hconj : ∀ β, e0 (m12 β) = ZModGcd.mulByCast a b (e0 β) := by
    intro β
    have hred : m12 β = (Abelian.Ext.mk₀ S.f).comp β (zero_add 0) := rfl
    have step1 : Abelian.Ext.addEquiv₀ (m12 β) = S.f ≫ Abelian.Ext.addEquiv₀ β := by
      rw [hred]
      apply Abelian.Ext.addEquiv₀.symm.injective
      rw [AddEquiv.symm_apply_apply, Abelian.Ext.addEquiv₀_symm_apply, ← Abelian.Ext.mk₀_comp_mk₀,
        Abelian.Ext.mk₀_addEquiv₀_apply]
    change (LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod b))
        (ModuleCat.homAddEquiv (Abelian.Ext.addEquiv₀ (m12 β)))
      = ZModGcd.mulByCast a b ((LinearMap.ringLmapEquivSelf ℤ ℤ (ZMod b))
        (ModuleCat.homAddEquiv (Abelian.Ext.addEquiv₀ β)))
    rw [step1]
    simp only [ModuleCat.homAddEquiv_apply, ModuleCat.hom_comp,
      LinearMap.ringLmapEquivSelf_apply, ZModGcd.mulByCast_apply]
    change (Abelian.Ext.addEquiv₀ β).hom (S.f.hom 1) = (a : ℤ) • (Abelian.Ext.addEquiv₀ β).hom 1
    rw [show S.f.hom (1 : ℤ) = (a : ℤ) • (1 : ℤ) from rfl, map_smul]
  -- `range(mulByCast) = (a) • ⊤`, matching the domain of `zmodCokerEquiv`.
  have hrange : LinearMap.range (ZModGcd.mulByCast a b)
      = Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ (ZMod b)) := by
    rw [Submodule.ideal_span_singleton_smul]
    ext x
    simp only [LinearMap.mem_range, ZModGcd.mulByCast_apply,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩
    · rintro ⟨y, _, rfl⟩; exact ⟨y, rfl⟩
  -- Assemble: `Ext¹ ≃ Ext⁰(ℤ)/ker δ ≃ ℤ/b / (a)•⊤ ≃ ℤ/gcd`.
  let δL := dhom.toIntLinearMap
  have hsurjδL : Function.Surjective δL := hsurjδ
  let e0L : (Etingof.Ext S.X₁ Y 0) ≃ₗ[ℤ] ZMod b := e0.toIntLinearEquiv
  have he0L : ∀ x, (e0L : (Etingof.Ext S.X₁ Y 0) →ₗ[ℤ] ZMod b) x = e0 x := fun _ => rfl
  have hmap : Submodule.map (e0L : (Etingof.Ext S.X₁ Y 0) →ₗ[ℤ] ZMod b) (LinearMap.ker δL)
      = Ideal.span {(a : ℤ)} • (⊤ : Submodule ℤ (ZMod b)) := by
    rw [← hrange]
    ext z
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.mem_range, he0L]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ dhom.ker := AddMonoidHom.mem_ker.mpr hy
      rw [hkerδ] at hy'
      obtain ⟨u, hu⟩ := hy'
      exact ⟨e0 u, by rw [← hconj, hu]⟩
    · rintro ⟨w, rfl⟩
      refine ⟨m12 (e0.symm w), ?_, ?_⟩
      · have : m12 (e0.symm w) ∈ dhom.ker :=
          hkerδ.symm ▸ AddMonoidHom.mem_range.mpr ⟨e0.symm w, rfl⟩
        exact AddMonoidHom.mem_ker.mp this
      · rw [hconj, e0.apply_symm_apply]
  exact ⟨(((LinearMap.quotKerEquivOfSurjective δL hsurjδL).symm.trans
    (Submodule.Quotient.equiv (LinearMap.ker δL) _ e0L hmap)).trans
    (ZModGcd.zmodCokerEquiv a b)).toAddEquiv⟩

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

/-- The right-module length-`1` free resolution `0 → k[x] →(·p) k[x] → k[x]/(p) → 0` over
`k[x]ᵐᵒᵖ` (`p ≠ 0`), the `k[x]` analogue of `zmodMopResolution`. -/
private noncomputable def polyMopResolution (k : Type u) [Field k] (p : k[X]) (hp : p ≠ 0) :
    {S : ShortComplex (ModuleCat.{u} (k[X])ᵐᵒᵖ) //
      S.ShortExact ∧ S.X₁ = ModuleCat.of (k[X])ᵐᵒᵖ k[X] ∧ S.X₂ = ModuleCat.of (k[X])ᵐᵒᵖ k[X] ∧
      S.X₃ = ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {p})} :=
  let f : k[X] →ₗ[(k[X])ᵐᵒᵖ] k[X] :=
    { toFun := fun x => p * x
      map_add' := fun x y => by ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, MulOpposite.smul_eq_mul_unop]; ring }
  let g : k[X] →ₗ[(k[X])ᵐᵒᵖ] (k[X] ⧸ Ideal.span {p}) :=
    { toFun := fun x => (Ideal.span {p}).mkQ x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        rw [MulOpposite.smul_eq_mul_unop, RingHom.id_apply]
        change (Ideal.span {p}).mkQ (x * MulOpposite.unop r)
            = MulOpposite.unop r • (Ideal.span {p}).mkQ x
        rw [← map_smul]; congr 1; rw [smul_eq_mul, mul_comm] }
  have hf : ∀ x : k[X], f x = p * x := fun _ => rfl
  have hg : ∀ x : k[X], g x = (Ideal.span {p}).mkQ x := fun _ => rfl
  have hgf : ∀ x : k[X], g (f x) = 0 := by
    intro x
    rw [hf, hg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
    exact dvd_mul_right p x
  have eq0 : g.comp f = 0 :=
    LinearMap.ext fun x => by rw [LinearMap.comp_apply, hgf x, LinearMap.zero_apply]
  let S := ModuleCat.shortComplexOfCompEqZero f g eq0
  have hexact : Function.Exact f g := by
    rw [LinearMap.exact_iff]; ext y
    simp only [LinearMap.mem_ker, hg, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Ideal.mem_span_singleton, LinearMap.mem_range, hf]
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact dvd_mul_right p c
  have hinj : Function.Injective f := fun x y hxy => mul_left_cancel₀ hp (by rw [← hf, ← hf, hxy])
  have hsurj : Function.Surjective g := Submodule.Quotient.mk_surjective _
  ⟨S, ModuleCat.shortComplex_shortExact S hexact hinj hsurj, rfl, rfl, rfl⟩

/-- `k[x]/(0) = k[x]/⊥` is `k[x]ᵐᵒᵖ`-linearly the free rank-one module `k[x]`; the two
`k[x]ᵐᵒᵖ`-actions agree by commutativity. -/
private noncomputable def polyZeroOpEquiv (k : Type u) [Field k] :
    (k[X] ⧸ Ideal.span {(0 : k[X])}) ≃ₗ[(k[X])ᵐᵒᵖ] k[X] :=
  let e0 : (k[X] ⧸ Ideal.span {(0 : k[X])}) ≃ₗ[k[X]] k[X] :=
    Submodule.quotEquivOfEqBot _ (by simp)
  { e0.toAddEquiv with
    map_smul' := fun r z => by
      change e0 (MulOpposite.unop r • z) = e0 z * MulOpposite.unop r
      rw [map_smul, smul_eq_mul, mul_comm] }

open Limits in
/-- **Problem 8.2.7(ii), higher `Tor` vanishes.** `Torᵢ(k[x]/(f), k[x]/(g)) = 0` for `i ≥ 2`,
by the same six-term long-exact-sequence squeeze as part (i), over the PID `k[x]`. -/
theorem Problem_8_2_7_ii_tor_vanish (k : Type*) [Field k] (f g : k[X]) (n : ℕ) :
    Limits.IsZero (Etingof.Tor k[X] (k[X] ⧸ Ideal.span {g})
      (ModuleCat.of (k[X])ᵐᵒᵖ (k[X] ⧸ Ideal.span {f})) (n + 2)) := by
  rcases eq_or_ne f 0 with rfl | hf
  · -- `k[x]/(0) ≅ k[x]` is a projective (free rank-one) right module
    have hz := Functor.isZero_leftDerived_obj_projective_succ
      (tensorRightFunctor k[X] (k[X] ⧸ Ideal.span {g})) (n + 1) (ModuleCat.of (k[X])ᵐᵒᵖ k[X])
    exact hz.of_iso
      (((tensorRightFunctor k[X] (k[X] ⧸ Ideal.span {g})).leftDerived (n + 2)).mapIso
        (polyZeroOpEquiv k).toModuleIso)
  · obtain ⟨S, hS, hX₁, hX₂, hX₃⟩ := polyMopResolution k f hf
    set F := tensorRightFunctor k[X] (k[X] ⧸ Ideal.span {g}) with hF
    obtain ⟨δ, hExact⟩ := Etingof.Functor.leftDerived_sixTerm_exact F hS (n + 1) (n + 2) rfl
    have h1 : IsZero ((F.leftDerived (n + 2)).obj S.X₂) := by
      rw [hX₂]; exact Functor.isZero_leftDerived_obj_projective_succ F (n + 1) _
    have h3 : IsZero ((F.leftDerived (n + 1)).obj S.X₁) := by
      rw [hX₁]; exact Functor.isZero_leftDerived_obj_projective_succ F n _
    have hgoal : IsZero ((F.leftDerived (n + 2)).obj S.X₃) :=
      isZero_obj_two_of_sixTerm_exact hExact h1 h3
    rw [hX₃] at hgoal
    exact hgoal

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

/-- `k[x]/(p)` has projective dimension `< 2` as a `k[x]`-module. For `p ≠ 0` the length-`1`
free resolution `0 → k[x] →(·p) k[x] → k[x]/(p) → 0` exhibits this; for `p = 0`,
`k[x]/(0) ≅ k[x]` is projective. -/
private lemma polyQuot_hasProjectiveDimensionLT_two (k : Type u) [Field k] (p : k[X]) :
    HasProjectiveDimensionLT (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {p})) 2 := by
  rcases eq_or_ne p 0 with rfl | hp
  · -- `span {0} = ⊥`, so `k[x]/(0) ≅ k[x]` is projective
    have e : (k[X] ⧸ Ideal.span {(0 : k[X])}) ≃ₗ[k[X]] k[X] :=
      Submodule.quotEquivOfEqBot _ (by simp)
    haveI : HasProjectiveDimensionLT (ModuleCat.of k[X] k[X]) 1 :=
      projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
    haveI : HasProjectiveDimensionLT (ModuleCat.of k[X] k[X]) 2 :=
      hasProjectiveDimensionLT_of_ge (ModuleCat.of k[X] k[X]) 1 2 (by omega)
    exact hasProjectiveDimensionLT_of_iso
      (e.toModuleIso.symm : ModuleCat.of k[X] k[X] ≅ ModuleCat.of k[X] _) 2
  · -- the length-`1` free resolution `0 → k[x] →(·p) k[x] → k[x]/(p) → 0`
    let f : k[X] →ₗ[k[X]] k[X] := p • LinearMap.id
    let g : k[X] →ₗ[k[X]] (k[X] ⧸ Ideal.span {p}) := (Ideal.span {p}).mkQ
    have hf : ∀ x : k[X], f x = p * x := fun x => by simp [f]
    have eq0 : g.comp f = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, hf, g, Submodule.mkQ_apply, LinearMap.zero_apply,
        Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact dvd_mul_right p x
    let S := ModuleCat.shortComplexOfCompEqZero f g eq0
    have hexact : Function.Exact f g := by
      rw [LinearMap.exact_iff]
      ext y
      simp only [g, LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton, LinearMap.mem_range, hf]
      constructor
      · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩; exact dvd_mul_right p c
    have hinj : Function.Injective f := fun x y hxy =>
      mul_left_cancel₀ hp (by rw [← hf, ← hf, hxy])
    have hsurj : Function.Surjective g := (Ideal.span {p}).mkQ_surjective
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexact hinj hsurj
    exact hasProjectiveDimensionLT_two_of_shortExact hS inferInstance inferInstance

/-- **Problem 8.2.7(ii), higher `Ext` vanishes.** `Extⁱ(k[x]/(f), k[x]/(g)) = 0` for `i ≥ 2`,
because `k[x]/(f)` has a length-`1` free resolution over the PID `k[x]`, hence projective
dimension `≤ 1`. -/
theorem Problem_8_2_7_ii_ext_vanish (k : Type*) [Field k] (f g : k[X]) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f}))
      (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {g})) (n + 2)) := by
  haveI := polyQuot_hasProjectiveDimensionLT_two k f
  exact HasProjectiveDimensionLT.subsingleton
    (ModuleCat.of k[X] (k[X] ⧸ Ideal.span {f})) 2 (n + 2) (by omega) _

/-- **Problem 8.2.7(ii), free generator.** `k[x]` is projective, so `Extⁱ⁺¹(k[x], N) = 0` for
every `k[x]`-module `N`. -/
theorem Problem_8_2_7_ii_ext_free_vanish (k : Type u) [Field k]
    (N : ModuleCat.{u} k[X]) (n : ℕ) :
    Subsingleton (Etingof.Ext (ModuleCat.of k[X] k[X]) N (n + 1)) :=
  Abelian.Ext.subsingleton_of_projective (ModuleCat.of k[X] k[X]) N n

end Etingof
