import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.ULift

/-!
# Exercise 8.2.9: (non)existence of enough projectives

* (i) The category of finite abelian groups, and the category of finite dimensional
  `k[x]`-modules, do **not** contain nonzero projective objects (so they do not have
  enough projectives).
* (ii) If `A` is a finitely generated commutative ring, then the category of finitely
  generated `A`-modules **has** enough projectives.

## Formalization notes

There is no ready-made Mathlib category of *finite* abelian groups or *finite dimensional*
`k[x]`-modules, so we express "is a projective object of that category" directly via the
defining lifting property: `P` is projective iff every epimorphism `f : Q₁ ↠ Q₂` (between
objects of the subcategory) and every map `g : P → Q₂` admit a lift `h : P → Q₁` with
`f ∘ h = g`. Part (i) is then the statement that such a `P` must be zero (`Subsingleton P`).

For part (ii), "enough projectives" for the category of finitely generated `A`-modules means
every finitely generated module is a quotient of a projective object of the category. A finite
free module `Fin n → A` is finitely generated and projective, so the content is that every
finitely generated `A`-module admits a surjection from a finite free module. The finite
generation hypothesis on the commutative ring `A` (a finitely generated `ℤ`-algebra) makes the
category abelian via the Hilbert basis theorem (`A` is Noetherian, so submodules of finitely
generated modules are finitely generated); this is what is needed for the categorical notion of
"enough projectives" to make sense.

These are statement-level formalizations (spec-first): the proofs are deferred (`sorry`).
-/

namespace Etingof

universe u

/-- **Exercise 8.2.9(i), finite abelian groups.** A finite abelian group that is a projective
object of the category of finite abelian groups — i.e. has the lifting property against
surjections of finite abelian groups — is zero. Hence that category has no nonzero projective
objects. -/
theorem Exercise_8_2_9_i_finAb
    (P : Type u) [AddCommGroup P] [Finite P]
    (hP : ∀ (Q₁ Q₂ : Type u) [AddCommGroup Q₁] [Finite Q₁] [AddCommGroup Q₂] [Finite Q₂]
      (f : Q₁ →+ Q₂) (g : P →+ Q₂), Function.Surjective f →
        ∃ h : P →+ Q₁, ∀ x, f (h x) = g x) :
    Subsingleton P := by
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · exact hsub
  exfalso
  haveI : Fintype P := Fintype.ofFinite P
  -- Pick a prime `q` dividing `|P|` and, by Cauchy, an element `x` of additive order `q`.
  have hcard1 : Nat.card P ≠ 1 := by
    have := Finite.one_lt_card (α := P); omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard1
  haveI : Fact q.Prime := ⟨hq⟩
  have hqdvd' : q ∣ Fintype.card P := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hxord⟩ := exists_prime_addOrderOf_dvd_card q hqdvd'
  have hx0 : q • x = 0 := by rw [← hxord]; exact addOrderOf_nsmul_eq_zero x
  have hxne : x ≠ 0 := by
    rintro rfl; rw [addOrderOf_zero] at hxord; exact hq.one_lt.ne hxord
  -- Multiplication by `q` on `P`, and the subgroup `H = qP`.
  let μ : P →+ P := AddMonoidHom.mk' (fun y => q • y) (fun a b => smul_add q a b)
  have μapp : ∀ y, μ y = q • y := fun _ => rfl
  let H : AddSubgroup P := μ.range
  have hHmem : ∀ y, q • y ∈ H := fun y => ⟨y, rfl⟩
  -- `μ` is not injective (kills `x ≠ 0`), hence (P finite) not surjective, so `H ≠ ⊤`.
  have hμ_ninj : ¬ Function.Injective μ := by
    intro hinj
    exact hxne (hinj (by rw [μapp, hx0, map_zero]))
  have hμ_nsurj : ¬ Function.Surjective μ := fun hsurj =>
    hμ_ninj ((Finite.injective_iff_surjective).2 hsurj)
  obtain ⟨y₀, hy₀⟩ := not_forall.mp hμ_nsurj
  have hy₀H : y₀ ∉ H := fun hmem => hy₀ (AddMonoidHom.mem_range.mp hmem)
  -- The quotient `P/qP` is a nonzero `ZMod q`-vector space.
  letI : Module (ZMod q) (P ⧸ H) := QuotientAddGroup.zmodModule (n := q) hHmem
  set ybar : P ⧸ H := QuotientAddGroup.mk' H y₀ with hybar
  have hybarne : ybar ≠ 0 := by
    rw [hybar, QuotientAddGroup.mk'_apply, Ne, QuotientAddGroup.eq_zero_iff]
    exact hy₀H
  -- Choose a basis of `P/qP` as a `ZMod q`-vector space; some coordinate functional is
  -- nonzero on `ybar`, giving a nonzero additive character `φ : P →+ ZMod q`.
  let b := Module.Basis.ofVectorSpace (ZMod q) (P ⧸ H)
  obtain ⟨i, hi⟩ :
      ∃ i, ((b.coord i).toAddMonoidHom.comp (QuotientAddGroup.mk' H)) y₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hybarne
    apply b.forall_coord_eq_zero_iff.mp
    intro j
    simpa [hybar] using hcon j
  let φ : P →+ ZMod q := (b.coord i).toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  have hφy₀ : φ y₀ ≠ 0 := hi
  -- Now lift `φ` through the reduction `ZMod (q^N) ↠ ZMod q` with `N = |P|`.  The finite
  -- `ZMod` groups live in `Type 0`, so transport them into `Type u` via `ULift`.
  set N := Nat.card P with hNdef
  have hN0 : N ≠ 0 := by rw [hNdef]; exact Nat.card_pos.ne'
  haveI : NeZero (q ^ N) := ⟨pow_ne_zero N hq.ne_zero⟩
  have hdvd : q ∣ q ^ N := dvd_pow_self q hN0
  let f0 : ZMod (q ^ N) →+ ZMod q := (ZMod.castHom hdvd (ZMod q)).toAddMonoidHom
  have hf0surj : Function.Surjective f0 := ZMod.castHom_surjective hdvd
  let e1 : ULift.{u} (ZMod (q ^ N)) ≃+ ZMod (q ^ N) := AddEquiv.ulift
  let e2 : ULift.{u} (ZMod q) ≃+ ZMod q := AddEquiv.ulift
  let f0' : ULift.{u} (ZMod (q ^ N)) →+ ULift.{u} (ZMod q) :=
    (e2.symm.toAddMonoidHom).comp (f0.comp e1.toAddMonoidHom)
  have hf0'surj : Function.Surjective f0' := by
    intro y
    obtain ⟨z, hz⟩ := hf0surj (e2 y)
    refine ⟨e1.symm z, ?_⟩
    change e2.symm (f0 (e1 (e1.symm z))) = y
    rw [e1.apply_symm_apply, hz, e2.symm_apply_apply]
  let φ' : P →+ ULift.{u} (ZMod q) := (e2.symm.toAddMonoidHom).comp φ
  obtain ⟨h', hh'⟩ := hP (ULift.{u} (ZMod (q ^ N))) (ULift.{u} (ZMod q)) f0' φ' hf0'surj
  let h : P →+ ZMod (q ^ N) := e1.toAddMonoidHom.comp h'
  have key : ∀ z, f0 (h z) = φ z := fun z => e2.symm.injective (hh' z)
  have hne0 : f0 (h y₀) ≠ 0 := by rw [key y₀]; exact hφy₀
  -- The lift `h y₀` reduces to a nonzero residue mod `q`, so it is a unit of `ZMod (q^N)`:
  -- its additive order is `q^N`.
  have hcast : f0 (h y₀) = (((h y₀).val : ℕ) : ZMod q) := by
    change ZMod.castHom hdvd (ZMod q) (h y₀) = _
    rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  have hnotdvd : ¬ (q ∣ (h y₀).val) := by
    intro hd
    apply hne0
    rw [hcast, ZMod.natCast_eq_zero_iff]
    exact hd
  have hcop : Nat.Coprime (q ^ N) (h y₀).val :=
    ((hq.coprime_iff_not_dvd).mpr hnotdvd).pow_left N
  have hord : addOrderOf (h y₀) = q ^ N := by
    have h1 := ZMod.addOrderOf_coe (h y₀).val (pow_ne_zero N hq.ne_zero)
    rw [ZMod.natCast_rightInverse (h y₀)] at h1
    rw [h1, hcop, Nat.div_one]
  -- But the additive order divides `|P|`, giving `q^N ≤ N < q^N`.
  have hdvd1 : addOrderOf (h y₀) ∣ addOrderOf y₀ := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
  have hdvd2 : addOrderOf y₀ ∣ Nat.card P := addOrderOf_dvd_natCard y₀
  have hle : addOrderOf (h y₀) ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (hdvd1.trans hdvd2)
  rw [hord] at hle
  have hlt : Nat.card P < q ^ Nat.card P :=
    calc Nat.card P < 2 ^ Nat.card P := Nat.lt_two_pow_self
      _ ≤ q ^ Nat.card P := Nat.pow_le_pow_left hq.two_le _
  exact absurd hle (not_le.mpr hlt)

/-- **Exercise 8.2.9(i), finite dimensional `k[x]`-modules.** A finite dimensional `k[x]`-module
that is a projective object of the category of finite dimensional `k[x]`-modules — i.e. has the
lifting property against surjections of finite dimensional `k[x]`-modules — is zero. Hence that
category has no nonzero projective objects. -/
theorem Exercise_8_2_9_i_polynomial
    (k : Type u) [Field k]
    (P : Type u) [AddCommGroup P] [Module (Polynomial k) P] [Module k P]
      [IsScalarTower k (Polynomial k) P] [FiniteDimensional k P]
    (hP : ∀ (Q₁ Q₂ : Type u) [AddCommGroup Q₁] [Module (Polynomial k) Q₁] [Module k Q₁]
        [IsScalarTower k (Polynomial k) Q₁] [FiniteDimensional k Q₁]
        [AddCommGroup Q₂] [Module (Polynomial k) Q₂] [Module k Q₂]
        [IsScalarTower k (Polynomial k) Q₂] [FiniteDimensional k Q₂]
        (f : Q₁ →ₗ[Polynomial k] Q₂) (g : P →ₗ[Polynomial k] Q₂), Function.Surjective f →
          ∃ h : P →ₗ[Polynomial k] Q₁, ∀ x, f (h x) = g x) :
    Subsingleton P := by
  sorry

/-- **Exercise 8.2.9(ii).** If `A` is a finitely generated commutative ring (a finitely
generated `ℤ`-algebra), then the category of finitely generated `A`-modules has enough
projectives: every finitely generated `A`-module is a quotient of a finite free module
`Fin n → A`, which is a finitely generated projective object. -/
theorem Exercise_8_2_9_ii
    (A : Type u) [CommRing A] [Algebra.FiniteType ℤ A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ (n : ℕ) (f : (Fin n → A) →ₗ[A] M), Function.Surjective f :=
  Module.Finite.exists_fin' A M

end Etingof
