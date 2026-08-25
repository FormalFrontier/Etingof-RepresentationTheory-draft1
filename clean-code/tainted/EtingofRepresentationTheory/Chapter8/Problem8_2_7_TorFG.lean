import EtingofRepresentationTheory.Chapter8.Problem8_2_7_ExtFG
import EtingofRepresentationTheory.Chapter8.Additivity

/-!
# Problem 8.2.7: `Tor` for arbitrary finitely generated modules over a PID

`Problem8_2_7.lean` computes `Torᵢ` for the two *building blocks* of the structure theorem over a
PID — a free generator and a pair of cyclic modules — `PIDDecomposition.lean` packages the
structure theorem as a biproduct decomposition, and `Additivity.lean` proves that `Tor` commutes
with finite direct sums in each argument. This file performs the reduction the book's hint asks for
("reduce to the case of cyclic groups using the classification theorem") on the `Tor` side, and
supplies the base-ring-independent half of the computation of `Torᵢ(M, N)` for **arbitrary**
finitely generated `M`, `N`. It is the exact counterpart of `Problem8_2_7_ExtFG.lean`.

## Main results

* `Etingof.torSndCongr`: `Tor` transported along a linear isomorphism in its second variable
  (in the first variable this is just `(TorFunctor A N n).mapIso`).
* `Etingof.PIDDecomposition.equivPi`, `Etingof.PIDDecomposition.mopSummandIso`: a decomposition as
  an isomorphism onto the *product* of its summands, and the identification of each summand, as a
  **right** module, with the cyclic right module `A ⧸ (genOf j)`.
* `Etingof.torFstDecompositionAddEquiv`, `Etingof.torSndDecompositionAddEquiv`,
  `Etingof.torPIDDecompositionAddEquiv`: **the reduction.** Given decompositions `D` of `M` and `E`
  of `N`,
  `Torₙ(M, N) ≃+ Π (j : D.index) (l : E.index), Torₙ(D.summand j, E.summand l)`,
  together with the two one-variable forms that leave the other argument arbitrary.

## Two asymmetries with the `Ext` side

**The first argument has to be transported into `ModuleCat Aᵐᵒᵖ`.** `Etingof.Tor` takes its first
argument as a *right* `A`-module, so the reduction uses `PIDDecomposition.mopBiproductIso` rather
than `PIDDecomposition.biproductIso`. Over the commutative rings `ℤ` and `k[X]` the two carry the
same information, via the ring isomorphism `Aᵐᵒᵖ ≃+* A` of `Etingof.mopRingEquiv`.

**Everything here lives in `Type 0`.** `Etingof.torBiproductIso` and `Etingof.torPiIso` are stated
for an index type in `Type 0` (Mathlib's `PreservesBiproduct` instances for additive functors, and
`AddCommGrpCat.biproductIsoPi`, are `Type 0`-indexed), and a `PIDDecomposition A M` for
`A M : Type u` has its summands indexed by a `Type u`. So the finitely-generated `Tor` statements
are for `A M N : Type`, which is automatic over `ℤ` and amounts to taking `k : Type` over `k[X]`.
The `Ext` side has no such restriction, since Mathlib's `Abelian.Ext.biproductAddEquiv` is
universe-polymorphic in the index.
-/

universe u

namespace Etingof

open CategoryTheory Limits

/-! ### Biproducts of abelian groups as products -/

/-- `⨁ f ≃+ Π j, f j` for a finite family of abelian groups: the additive form of
`AddCommGrpCat.biproductIsoPi`. The `Tor` additivity lemmas produce categorical biproducts; the
answers of Problem 8.2.7 are more readable as products, which is also the shape the `Ext` side
uses. -/
noncomputable def biproductPiAddEquiv {J : Type} [Finite J] (f : J → AddCommGrpCat.{u}) :
    (⨁ f : AddCommGrpCat.{u}) ≃+ ∀ j, f j :=
  (AddCommGrpCat.biproductIsoPi f).addCommGroupIsoToAddEquiv

/-! ### Transporting `Tor` along isomorphisms -/

section TorCongr

variable {A : Type u} [Ring A]

/-- **`Tor` is invariant under isomorphism in its first variable**, since `Torₙ(-, N)` is a
functor. -/
noncomputable abbrev torFstCongr (N : Type u) [AddCommGroup N] [Module A N]
    {M₁ M₂ : ModuleCat.{u} Aᵐᵒᵖ} (e : M₁ ≅ M₂) (n : ℕ) :
    Tor.{u} A N M₁ n ≅ Tor.{u} A N M₂ n :=
  (TorFunctor.{u} A N n).mapIso e

/-- **`Tor` is invariant under isomorphism in its second variable.** The second argument is not a
functor argument in the present set-up, so this is assembled from the functoriality `torSndMap` of
Problem 8.2.6 and its identity/composition laws. -/
noncomputable def torSndCongr {N₁ N₂ : Type u} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] (e : N₁ ≃ₗ[A] N₂) (M : ModuleCat.{u} Aᵐᵒᵖ) (n : ℕ) :
    Tor.{u} A N₁ M n ≅ Tor.{u} A N₂ M n where
  hom := torSndMap A (e : N₁ →ₗ[A] N₂) n M
  inv := torSndMap A (e.symm : N₂ →ₗ[A] N₁) n M
  hom_inv_id := by
    rw [← torSndMap_comp M (e : N₁ →ₗ[A] N₂) (e.symm : N₂ →ₗ[A] N₁) n,
      show (e.symm : N₂ →ₗ[A] N₁).comp (e : N₁ →ₗ[A] N₂) = LinearMap.id from
        LinearMap.ext fun x => e.symm_apply_apply x]
    exact torSndMap_id A N₁ n M
  inv_hom_id := by
    rw [← torSndMap_comp M (e.symm : N₂ →ₗ[A] N₁) (e : N₁ →ₗ[A] N₂) n,
      show (e : N₁ →ₗ[A] N₂).comp (e.symm : N₂ →ₗ[A] N₁) = LinearMap.id from
        LinearMap.ext fun x => e.apply_symm_apply x]
    exact torSndMap_id A N₂ n M

end TorCongr

/-! ### The reduction to summand pairs

Everything below is in `Type 0`; see the module docstring. -/

section Reduction

variable {A : Type} [CommRing A] {M N : Type} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- A decomposition as a linear isomorphism onto the **product** of its summands. This is the
`Pi`-shaped form of `Etingof.PIDDecomposition.equivDirectSum`, which is what
`Etingof.torPiIso` — additivity of `Tor` in its second argument — is stated for. -/
noncomputable def PIDDecomposition.equivPi (D : PIDDecomposition A M) :
    M ≃ₗ[A] ∀ j : D.index, (D.summand j : Type) :=
  D.equivProd ≪≫ₗ
    (LinearEquiv.sumPiEquivProdPi A (Fin D.freeRank) D.torsionIndex
      (fun j => (D.summand j : Type))).symm

/-- **Every summand of a decomposition, viewed as a right module, is the cyclic right module
`A ⧸ (genOf j)`**, the free ones being `A ⧸ (0) ≅ A`. This is `PIDDecomposition.summandIso`
transported along the equivalence `mopFunctor A : ModuleCat A ≌ ModuleCat Aᵐᵒᵖ`. -/
noncomputable def PIDDecomposition.mopSummandIso (D : PIDDecomposition A M) (j : D.index) :
    D.mopSummand j ≅ mopOf A (A ⧸ Ideal.span {D.genOf j}) :=
  (mopFunctor A).mapIso (D.summandIso j)

/-- **Additivity of `Tor` in the first variable, along a decomposition.**
`Torₙ(M, Y) ≃+ Π j, Torₙ(D.summand j, Y)` for an arbitrary second argument `Y`. -/
noncomputable def torFstDecompositionAddEquiv (D : PIDDecomposition A M) (Y : Type)
    [AddCommGroup Y] [Module A Y] (n : ℕ) :
    Tor A Y (mopOf A M) n ≃+ ∀ j : D.index, Tor A Y (D.mopSummand j) n :=
  (torFstCongr Y D.mopBiproductIso n).addCommGroupIsoToAddEquiv.trans
    (((torBiproductIso A Y n D.mopSummand).addCommGroupIsoToAddEquiv).trans
      (biproductPiAddEquiv _))

/-- **Additivity of `Tor` in the second variable, along a decomposition.**
`Torₙ(X, N) ≃+ Π l, Torₙ(X, E.summand l)` for an arbitrary first argument `X`. -/
noncomputable def torSndDecompositionAddEquiv (E : PIDDecomposition A N)
    (X : ModuleCat.{0} Aᵐᵒᵖ) (n : ℕ) :
    Tor A N X n ≃+ ∀ l : E.index, Tor A (E.summand l) X n :=
  (torSndCongr E.equivPi X n).addCommGroupIsoToAddEquiv.trans
    (((torPiIso A (fun l : E.index => (E.summand l : Type)) X n).addCommGroupIsoToAddEquiv).trans
      (biproductPiAddEquiv _))

/-- **The reduction of the `Tor` half of Problem 8.2.7 to the free and cyclic building blocks.**
For decompositions `D` of `M` and `E` of `N` into a free part and cyclic parts, `Torₙ(M, N)` is the
product, over pairs of summands, of the `Torₙ` groups of those summands. Together with the
summand-level computations of `Problem8_2_7.lean` this *is* the book's "reduce to the case of
cyclic groups". -/
noncomputable def torPIDDecompositionAddEquiv (D : PIDDecomposition A M) (E : PIDDecomposition A N)
    (n : ℕ) :
    Tor A N (mopOf A M) n ≃+
      ∀ (j : D.index) (l : E.index), Tor A (E.summand l) (D.mopSummand j) n :=
  (torFstDecompositionAddEquiv D N n).trans
    (AddEquiv.piCongrRight fun j => torSndDecompositionAddEquiv E (D.mopSummand j) n)

/-- **`Tor` vanishes on a decomposed module as soon as it vanishes on every summand.** The form in
which the higher-degree vanishing of Problem 8.2.7 is assembled: each summand is cyclic, and higher
`Tor` out of a cyclic module over a PID vanishes for an arbitrary second argument. -/
lemma subsingleton_tor_of_summands (D : PIDDecomposition A M) (Y : Type) [AddCommGroup Y]
    [Module A Y] (n : ℕ) (h : ∀ j, Subsingleton (Tor A Y (D.mopSummand j) n)) :
    Subsingleton (Tor A Y (mopOf A M) n) :=
  haveI := subsingleton_pi fun j : D.index => (Tor A Y (D.mopSummand j) n : Type)
  (torFstDecompositionAddEquiv D Y n).toEquiv.subsingleton

end Reduction

end Etingof
