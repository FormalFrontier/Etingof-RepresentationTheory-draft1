import EtingofRepresentationTheory.Chapter8.PIDDecomposition

/-!
# Problem 8.2.7: `Ext` for arbitrary finitely generated modules over a PID

`Problem8_2_7.lean` computes `Extⁱ` for the two *building blocks* of the structure theorem over a
PID — a free generator and a pair of cyclic modules — and `PIDDecomposition.lean` packages the
structure theorem as a biproduct decomposition. This file performs the reduction the book's hint
asks for ("reduce to the case of cyclic groups using the classification theorem") and supplies the
base-ring-independent half of the computation of `Extⁱ(M, N)` for **arbitrary** finitely generated
`M`, `N`.

## Main results

* `Etingof.extCongr`: `Ext` transported along isomorphisms in both variables.
* `Etingof.extPIDDecompositionAddEquiv`: **the reduction.** Given decompositions `D` of `M` and
  `E` of `N`,
  `Extⁱ(M, N) ≃+ Π (j : D.index) (l : E.index), Extⁱ(D.summand j, E.summand l)`,
  i.e. `Ext` of a pair of finitely generated modules is the product of the `Ext` groups of the
  pairs of free/cyclic summands. This is Mathlib's additivity of `Ext` in both variables
  (`Abelian.Ext.biproductAddEquiv`, `Abelian.Ext.addEquivBiproduct`) applied to
  `PIDDecomposition.biproductIso`.
* `Etingof.hasProjectiveDimensionLT_biproduct`: a finite biproduct of objects of projective
  dimension `< n` has projective dimension `< n` (Mathlib has only the binary case).
* `Etingof.cyclic_hasProjectiveDimensionLT_two`: over a domain, `A ⧸ (d)` has projective
  dimension `< 2` — from `0 → A →(·d) A → A ⧸ (d) → 0` when `d ≠ 0`, and from projectivity of
  `A ⧸ (0) ≅ A` when `d = 0`.
* `Etingof.fg_hasProjectiveDimensionLT_two`: **every** finitely generated module over a PID has
  projective dimension `< 2`, hence `Extⁱ(M, N) = 0` for `i ≥ 2` and *arbitrary* `N`.

Everything here is proved for an arbitrary PID; the `ℤ` and `k[X]` statements of Problem 8.2.7 are
instances. The degree-`0` and degree-`1` computations, which depend on the base ring through the
`ZModGcd` / `PolyGcd` isomorphisms of `Problem8_2_7.lean`, are assembled in
`Problem8_2_7_ExtInt.lean` and `Problem8_2_7_ExtPoly.lean`.
-/

universe w v u

namespace Etingof

open CategoryTheory Limits

/-! ### Transporting `Ext` along isomorphisms -/

section ExtCongr

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **`Ext` is invariant under isomorphism in both variables.** `Extⁿ(X, Y) ≃+ Extⁿ(X', Y')` for
`e : X ≅ X'` and `f : Y ≅ Y'`, by pre-composing with `e.inv` and post-composing with `f.hom`. -/
noncomputable def extCongr {X X' Y Y' : C} (e : X ≅ X') (f : Y ≅ Y') (n : ℕ) :
    Abelian.Ext.{w} X Y n ≃+ Abelian.Ext.{w} X' Y' n where
  toFun α :=
    (Abelian.Ext.mk₀ e.inv).comp (α.comp (Abelian.Ext.mk₀ f.hom) (add_zero n)) (zero_add n)
  invFun β :=
    (Abelian.Ext.mk₀ e.hom).comp (β.comp (Abelian.Ext.mk₀ f.inv) (add_zero n)) (zero_add n)
  left_inv α := by
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero, Iso.hom_inv_id, Abelian.Ext.comp_mk₀_id,
      Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_id_comp]
  right_inv β := by
    simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.comp_assoc_of_third_deg_zero, Iso.inv_hom_id, Abelian.Ext.comp_mk₀_id,
      Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_id_comp]
  map_add' α₁ α₂ := by
    simp only [Abelian.Ext.add_comp, Abelian.Ext.comp_add]

end ExtCongr

/-! ### Projective dimension of a finite biproduct -/

section ProjectiveDimension

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **A finite biproduct of objects of projective dimension `< n` has projective dimension `< n`.**
Mathlib has the binary case as an instance; the finite-family case follows from additivity of `Ext`
in its first variable, `Abelian.Ext.biproductAddEquiv`. -/
lemma hasProjectiveDimensionLT_biproduct {ι : Type*} [Finite ι] (X : ι → C) [HasBiproduct X]
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (X i) n) :
    HasProjectiveDimensionLT (⨁ X) n :=
  HasProjectiveDimensionLT.mk fun i hi Y e => by
    haveI := Fintype.ofFinite ι
    haveI : ∀ j, Subsingleton (Abelian.Ext.{w} (X j) Y i) := fun j =>
      have := h j
      HasProjectiveDimensionLT.subsingleton (X j) n i hi Y
    haveI : Subsingleton (∀ j, Abelian.Ext.{w} (X j) Y i) :=
      ⟨fun _ _ => funext fun _ => Subsingleton.elim _ _⟩
    exact (Abelian.Ext.biproductAddEquiv (biproduct.isBilimit X) Y i).subsingleton.elim _ _

end ProjectiveDimension

/-! ### The reduction to summand pairs -/

section Reduction

variable {A : Type u} [CommRing A] {M N : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- **The reduction of Problem 8.2.7 to the free and cyclic building blocks.** For decompositions
`D` of `M` and `E` of `N` into a free part and cyclic parts, `Extⁿ(M, N)` is the product, over
pairs of summands, of the `Extⁿ` groups of those summands. Together with the summand-level
computations of `Problem8_2_7.lean` this *is* the book's "reduce to the case of cyclic groups". -/
noncomputable def extPIDDecompositionAddEquiv (D : PIDDecomposition A M) (E : PIDDecomposition A N)
    (n : ℕ) :
    Etingof.Ext (ModuleCat.of A M) (ModuleCat.of A N) n ≃+
      ∀ (j : D.index) (l : E.index), Etingof.Ext (D.summand j) (E.summand l) n :=
  (extCongr D.biproductIso E.biproductIso n).trans
    ((Abelian.Ext.biproductAddEquiv (biproduct.isBilimit D.summand) _ n).trans
      (AddEquiv.piCongrRight fun _ =>
        Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit E.summand) n))

end Reduction

/-! ### Projective dimension `< 2` for finitely generated modules over a PID -/

section PIDProjectiveDimension

variable (A : Type u) [CommRing A]

/-- The multiplication-by-`d` endomorphism of `A`, as an `A`-linear map. -/
private noncomputable def mulByGen (d : A) : A →ₗ[A] A := d • LinearMap.id

private lemma mulByGen_apply (d x : A) : mulByGen A d x = d * x := by
  simp [mulByGen]

private lemma range_mulByGen (d : A) :
    LinearMap.range (mulByGen A d) = Ideal.span {d} := by
  ext x
  simp only [LinearMap.mem_range, mulByGen_apply, Ideal.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

/-- **A cyclic module over a domain has projective dimension `< 2`.** For `d ≠ 0` this is the
length-`1` free resolution `0 → A →(·d) A → A ⧸ (d) → 0`; for `d = 0` the module `A ⧸ (0)` is
isomorphic to the projective module `A`. -/
lemma cyclic_hasProjectiveDimensionLT_two [IsDomain A] (d : A) :
    HasProjectiveDimensionLT (ModuleCat.of A (A ⧸ Ideal.span {d})) 2 := by
  haveI : HasProjectiveDimensionLT (ModuleCat.of A A) 2 :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of A A) 1 2 (by omega)
  rcases eq_or_ne d 0 with rfl | hd
  · -- `A ⧸ (0) ≅ A` is projective
    have hbot : (Ideal.span {(0 : A)} : Ideal A) = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
    exact hasProjectiveDimensionLT_of_iso
      (LinearEquiv.toModuleIso (Submodule.quotEquivOfEqBot _ hbot).symm) 2
  · -- the length-`1` free resolution `0 → A →(·d) A → A ⧸ (d) → 0`
    let f : A →ₗ[A] A := mulByGen A d
    let g : A →ₗ[A] (A ⧸ Ideal.span {d}) := (Ideal.span {d} : Ideal A).mkQ
    have eq0 : g.comp f = 0 := LinearMap.ext fun x => by
      simpa only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        LinearMap.zero_apply, mulByGen_apply, f, g] using Ideal.mem_span_singleton.mpr ⟨x, rfl⟩
    have hexact : Function.Exact f g := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ]
      exact (range_mulByGen A d).symm
    have hinj : Function.Injective f := fun x y hxy =>
      mul_left_cancel₀ hd (by rw [← mulByGen_apply A d x, ← mulByGen_apply A d y]; exact hxy)
    have hsurj : Function.Surjective g := Submodule.mkQ_surjective _
    let S := ModuleCat.shortComplexOfCompEqZero f g eq0
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hexact hinj hsurj
    exact hasProjectiveDimensionLT_two_of_shortExact hS inferInstance inferInstance

/-- **A module with a PID decomposition has projective dimension `< 2`.** Its summands are free or
cyclic, and both have projective dimension `< 2`
(`Etingof.cyclic_hasProjectiveDimensionLT_two`); projective dimension is additive over finite
biproducts (`Etingof.hasProjectiveDimensionLT_biproduct`). -/
lemma hasProjectiveDimensionLT_two_of_pidDecomposition [IsDomain A] {M : Type u} [AddCommGroup M]
    [Module A M] (D : PIDDecomposition A M) :
    HasProjectiveDimensionLT (ModuleCat.of A M) 2 := by
  haveI : HasProjectiveDimensionLT (ModuleCat.of A A) 2 :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of A A) 1 2 (by omega)
  haveI : HasProjectiveDimensionLT (⨁ D.summand) 2 :=
    hasProjectiveDimensionLT_biproduct D.summand 2 fun j => by
      cases j with
      | inl i => exact ‹HasProjectiveDimensionLT (ModuleCat.of A A) 2›
      | inr i => exact cyclic_hasProjectiveDimensionLT_two A (D.gen i)
  exact hasProjectiveDimensionLT_of_iso D.biproductIso.symm 2

/-- **Every finitely generated module over a PID has projective dimension `< 2`**, hence
`Extⁱ(M, N) = 0` for `i ≥ 2` and *arbitrary* `N` (`HasProjectiveDimensionLT.subsingleton`). -/
lemma fg_hasProjectiveDimensionLT_two [IsDomain A] [IsPrincipalIdealRing A] (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    HasProjectiveDimensionLT (ModuleCat.of A M) 2 :=
  (exists_pidDecomposition A M).elim (hasProjectiveDimensionLT_two_of_pidDecomposition A)

end PIDProjectiveDimension

end Etingof
