import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1
import EtingofRepresentationTheory.Chapter5.Theorem5_10_1
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Problem 5.10.2: concrete induction and restriction models

This file supplies the five concrete endpoints requested in Problem 5.10.2.

Mathlib models the noncommutative relative tensor product
`k[G] ⊗_{k[H]} W` canonically as `Rep.ind H.subtype W`: it is the coinvariant
quotient of `k[G] ⊗_k W` by the balancing relation.  Thus induction along the
identity is the expression `k[G] ⊗_{k[G]} V` in part (a).  Coinduction along
the identity is the equivariant-function model of `Hom_{k[G]}(k[G], V)` in
part (c).  These models avoid introducing a second, standalone noncommutative
tensor-product API while retaining the requested concrete maps on the nose.

The declarations corresponding to the five parts are:

* `Problem5_10_2_a`: `k[G] ⊗_{k[G]} V ≅ Res V`, whose inverse is
  `v ↦ 1 ⊗ v` (`Problem5_10_2_a_inv_apply`);
* `Problem5_10_2_c`: `Hom_{k[G]}(k[G], V) ≅ Res V`, by evaluation at `1`
  (`Problem5_10_2_c_hom_apply`);
* `Problem5_10_2_d`: the book's function-space induction is isomorphic to the
  balanced tensor/coinvariant model.  `Problem5_10_2_d_formula` gives the
  quotient-indexed coset sum, with representative-independence built into
  `Problem5_10_2_d_cosetTerm`;
* `Problem5_10_2_e`: the natural adjunction `Ind ⊣ Res`, together with the
  pointwise linear equivalence `Problem5_10_2_e_homEquiv`;
* `Problem5_10_2_f`: `Ind(V⁺) ≅ (Ind V)⁺` for finite complex representations.

Part (b) is already supplied directly, and at stronger naturality, by
`Theorem5_10_1`; it intentionally does not depend on the omitted standalone
Problem 2.11.6 tensor-Hom API.
-/

open CategoryTheory

universe u

namespace Etingof

variable (k G : Type u) [Field k] [Group G]

/-! ## (a): `k[G] ⊗_{k[G]} V ≅ Res V` -/

/-- Induction along the identity, Mathlib's canonical coinvariant model of
`k[G] ⊗_{k[G]} V`, is isomorphic to `V`.  The inverse is the requested map
`v ↦ 1 ⊗ v`; see `Problem5_10_2_indIdIso_inv_apply`. -/
noncomputable def Problem5_10_2_indIdIso (V : Rep k G) :
    Rep.ind (MonoidHom.id G) V ≅ V := by
  let forward :=
    ((Rep.indResHomEquiv (MonoidHom.id G) V V).symm (𝟙 V)).hom.toLinearMap
  let backward := Representation.IndV.mk (MonoidHom.id G) V.ρ 1
  let e : (Rep.ind (MonoidHom.id G) V).V ≃ₗ[k] V.V :=
    LinearEquiv.ofLinear forward backward (by ext v; simp [forward, backward])
      (by ext g v; simp [forward, backward])
  exact Rep.mkIso (Representation.Equiv.mk e fun g => by
    ext v
    simp [e, forward])

@[simp]
lemma Problem5_10_2_indIdIso_inv_apply (V : Rep k G) (v : V) :
    (Problem5_10_2_indIdIso k G V).inv.hom v =
      Representation.IndV.mk (MonoidHom.id G) V.ρ 1 v :=
  rfl

variable (H : Subgroup G)

/-- **Problem 5.10.2(a).** After restriction to `H`, induction along the identity
is `Res_H^G V`.  Its source is the canonical coinvariant realization of
`k[G]₁ ⊗_{k[G]} V`. -/
noncomputable def Problem5_10_2_a (V : Rep k G) :
    (Rep.resFunctor H.subtype).obj (Rep.ind (MonoidHom.id G) V) ≅
      (Rep.resFunctor H.subtype).obj V :=
  (Rep.resFunctor H.subtype).mapIso (Problem5_10_2_indIdIso k G V)

/-- The inverse in part (a) is exactly `v ↦ 1 ⊗ v`. -/
@[simp]
lemma Problem5_10_2_a_inv_apply (V : Rep k G) (v : V) :
    (Problem5_10_2_a k G H V).inv.hom v =
      Representation.IndV.mk (MonoidHom.id G) V.ρ 1 v :=
  rfl

/-! ## (c): `Hom_{k[G]}(k[G], V) ≅ Res V` -/

/-- Coinduction along the identity is the equivariant-function (equivalently,
left-regular intertwiner) model of `Hom_{k[G]}(k[G], V)`.  Evaluation at `1`
is an isomorphism to `V`. -/
noncomputable def Problem5_10_2_coindIdIso (V : Rep k G) :
    Rep.coind (MonoidHom.id G) V ≅ V := by
  let forward : (Rep.coind (MonoidHom.id G) V).V →ₗ[k] V.V :=
    LinearMap.proj 1 ∘ₗ Submodule.subtype _
  let backward :=
    ((Rep.resCoindHomEquiv (MonoidHom.id G) V V) (𝟙 V)).hom.toLinearMap
  let e : (Rep.coind (MonoidHom.id G) V).V ≃ₗ[k] V.V :=
    LinearEquiv.ofLinear forward backward (by
      apply LinearMap.ext
      intro v
      simp [forward, backward, Rep.resCoindHomEquiv, Rep.resCoindToHom]
      rfl) (by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      change (backward (forward f)).1 g = f.1 g
      rw [show ((backward (forward f)).1 g) = V.ρ g (f.1 1) by
        simp [backward, forward, Rep.resCoindHomEquiv, Rep.resCoindToHom]
        rfl]
      simpa using (f.2 g 1).symm)
  exact Rep.mkIso (Representation.Equiv.mk e fun g => by
    apply LinearMap.ext
    intro f
    change f.1 (1 * g) = V.ρ g (f.1 1)
    simpa using f.2 g 1)

@[simp]
lemma Problem5_10_2_coindIdIso_hom_apply (V : Rep k G)
    (f : (Rep.coind (MonoidHom.id G) V).V) :
    (Problem5_10_2_coindIdIso k G V).hom.hom f = f.1 1 :=
  rfl

/-- **Problem 5.10.2(c).** The regular-Hom model restricts to `Res_H^G V`.
The displayed isomorphism evaluates an equivariant function (or the associated
left-regular intertwiner) at the identity. -/
noncomputable def Problem5_10_2_c (V : Rep k G) :
    (Rep.resFunctor H.subtype).obj (Rep.coind (MonoidHom.id G) V) ≅
      (Rep.resFunctor H.subtype).obj V :=
  (Rep.resFunctor H.subtype).mapIso (Problem5_10_2_coindIdIso k G V)

/-- The isomorphism in part (c) is exactly evaluation at `1`. -/
@[simp]
lemma Problem5_10_2_c_hom_apply (V : Rep k G)
    (f : (Rep.coind (MonoidHom.id G) V).V) :
    (Problem5_10_2_c k G H V).hom.hom f = f.1 1 :=
  rfl

/-! ## (d): the function and balanced-tensor induction models -/

variable [Finite G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **Problem 5.10.2(d).** The book's function-space induction (`Rep.coind`) is
isomorphic to Mathlib's balanced tensor/coinvariant induction (`Rep.ind`). -/
noncomputable def Problem5_10_2_d (W : Rep k H) :
    Rep.coind H.subtype W ≅ Rep.ind H.subtype W :=
  open scoped Classical in (Rep.indCoindIso W).symm

/-- One summand in the quotient-indexed right-coset formula of part (d).

Using `Quotient.liftOn` is the formal representative-independence proof: the
third argument proves that replacing `g` by another representative of the same
right `H`-coset gives the same class in the balanced tensor quotient. -/
noncomputable def Problem5_10_2_d_cosetTerm (W : Rep k H)
    (f : (Rep.coind H.subtype W).V)
    (q : Quotient (QuotientGroup.rightRel H)) : (Rep.ind H.subtype W).V :=
  Quotient.liftOn q
    (fun g => Representation.IndV.mk H.subtype W.ρ g (f.1 g))
    (fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
      (Submodule.Quotient.eq _).2 <|
        Representation.Coinvariants.mem_ker_of_eq s
          (MonoidAlgebra.single g₂ (1 : k) ⊗ₜ[k] f.1 g₂) _ (by
            have := f.2 s g₂
            simp_all))

/-- The coset formula from Problem 5.10.2(d), canonically indexed by right
cosets.  A chosen transversal turns this into the book's
`∑ g ∈ P, g⁻¹ ⊗ f(g)` formula (the apparent inverse is accounted for by
Mathlib's right-action convention in `Representation.ind`). -/
theorem Problem5_10_2_d_formula (W : Rep k H)
    (f : (Rep.coind H.subtype W).V) :
    (Problem5_10_2_d k G H W).hom.hom f =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        Problem5_10_2_d_cosetTerm k G H W f q := by
  classical
  rw [Problem5_10_2_d]
  change W.coindToInd f = _
  simpa [Problem5_10_2_d_cosetTerm] using Rep.coindToInd_apply W f

/-! ## (e): natural Frobenius reciprocity in the other orientation -/

/-- **Problem 5.10.2(e).** Induction is left adjoint to restriction.  An
adjunction records naturality simultaneously in `W` and `V`. -/
noncomputable def Problem5_10_2_e :
    Rep.indFunctor k H.subtype ⊣ Rep.resFunctor H.subtype :=
  Rep.indResAdjunction k H.subtype

/-- The pointwise `k`-linear equivalence underlying part (e). -/
noncomputable def Problem5_10_2_e_homEquiv (W : Rep k H) (V : Rep k G) :
    (Rep.ind H.subtype W ⟶ V) ≃ₗ[k]
      (W ⟶ Rep.res H.subtype V) :=
  Rep.indResHomEquiv H.subtype W V

/-! ## (f): induction commutes with duality -/

variable {G₀ : Type} [Group G₀] [Fintype G₀] (H₀ : Subgroup G₀)

/-- Finite-dimensional complex induction in the canonical balanced-tensor
model. -/
noncomputable def Problem5_10_2_indFDRep (W : FDRep ℂ H₀) : FDRep ℂ G₀ :=
  FDRep.of (Representation.ind H₀.subtype W.ρ)

/-- Character identity used to construct the genuine representation
isomorphism in part (f).  It follows by applying the Frobenius character formula
to `g` and `g⁻¹`; subgroup membership is preserved by inversion. -/
theorem Problem5_10_2_f_character (V : FDRep ℂ H₀) :
    (Problem5_10_2_indFDRep H₀
      (FDRep.of (Representation.dual V.ρ))).character =
      (FDRep.of (Representation.dual
        (Problem5_10_2_indFDRep H₀ V).ρ)).character := by
  classical
  funext g
  rw [FDRep.char_dual]
  change LinearMap.trace ℂ _
      (Definition5_8_1 H₀ (Representation.dual V.ρ) g) =
    LinearMap.trace ℂ _ (Definition5_8_1 H₀ V.ρ g⁻¹)
  rw [Theorem5_9_1 H₀ (Representation.dual V.ρ) g,
    Theorem5_9_1 H₀ V.ρ g⁻¹]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hinv : (x * g * x⁻¹)⁻¹ = x * g⁻¹ * x⁻¹ := by
    simp [mul_assoc]
  by_cases hx : x * g * x⁻¹ ∈ H₀
  · have hx' : x * g⁻¹ * x⁻¹ ∈ H₀ := by
      rw [← hinv]
      exact H₀.inv_mem hx
    simp only [dif_pos hx, dif_pos hx']
    rw [show LinearMap.trace ℂ _
        (Representation.dual V.ρ ⟨x * g * x⁻¹, hx⟩) =
        (FDRep.of (Representation.dual V.ρ)).character
          ⟨x * g * x⁻¹, hx⟩ from rfl,
      FDRep.char_dual]
    congr 2
    apply Subtype.ext
    exact hinv
  · have hx' : x * g⁻¹ * x⁻¹ ∉ H₀ := by
      intro h
      apply hx
      rw [← show (x * g⁻¹ * x⁻¹)⁻¹ = x * g * x⁻¹ by simp [mul_assoc]]
      exact H₀.inv_mem h
    simp [hx, hx']

/-- **Problem 5.10.2(f).** Induction commutes with contragredient duality for
finite-dimensional complex representations.  This is a genuine `G`-equivariant
isomorphism, obtained from the proved character identity rather than merely a
dimension equality. -/
noncomputable def Problem5_10_2_f (V : FDRep ℂ H₀) :
    Problem5_10_2_indFDRep H₀ (FDRep.of (Representation.dual V.ρ)) ≅
      FDRep.of (Representation.dual (Problem5_10_2_indFDRep H₀ V).ρ) :=
  (Etingof.charEq_iso _ _ (Problem5_10_2_f_character H₀ V)).some

end Etingof
