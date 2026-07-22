import Mathlib
import EtingofRepresentationTheory.Chapter4.Example4_3_S4
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_10_1
import EtingofRepresentationTheory.Chapter5.Discussion5_11_examples
import EtingofRepresentationTheory.Infrastructure.IrreducibleEnumeration

/-!
# Discussion 5.11(3): the `S₄ / S₃` induced representations

Etingof's §5.11(3) records the decompositions, obtained via Frobenius reciprocity, of the
representations of `S₄` induced from the three irreducibles of the point-stabiliser
subgroup `S₃ ≤ S₄`:

* `Ind_{S₃}^{S₄} ℂ₊ ≅ ℂ₊ ⊕ ℂ³₋`,
* `Ind_{S₃}^{S₄} ℂ₋ ≅ ℂ₋ ⊕ ℂ³₊`,
* `Ind_{S₃}^{S₄} ℂ² ≅ ℂ² ⊕ ℂ³₋ ⊕ ℂ³₊`,

where `{ℂ₊, ℂ₋, ℂ², ℂ³₋, ℂ³₊}` are the five irreducibles of `S₄` built in
`Etingof.Example4_3_S4` (`trivRep`, `signRep`, `twoDimRep`, `stdRep`, `rotRep`).

Just as the `S₃` decompositions in `Discussion5_11_examples.lean` rest on the
completeness of the `S₃` catalogue (`S3_simple_iso`), the `S₄` decompositions rest on
the completeness of the `S₄` catalogue: **every simple `FDRep ℂ S₄` is isomorphic to one
of the five listed irreducibles**. This file establishes that catalogue-completeness
theorem `S4_simple_iso`, the reusable prerequisite for the induction computations. It
follows from the Artin–Wedderburn squared-dimension count `1² + 1² + 2² + 3² + 3² = 24 =
|S₄|` (`Etingof.Example4_3_S4.irreps_dim_sum_of_squares`): the five listed irreducibles
are simple, pairwise non-isomorphic, and exhaust the squared-dimension budget, so no sixth
simple can exist.

The three induction decompositions (`indH_triv_decomp`, `indH_sign_decomp`,
`indH_twoDim_decomp`) are then proved. `S₃` is realised as the point-stabiliser subgroup
`H ≤ S₄` (permutations fixing `3`) via `Equiv.Perm.extendDomainHom`, and the three `S₃`
irreducibles are transported to `H`. A group-generic form of the Frobenius-reciprocity
dimension lemma (`frobenius_finrank_gen` / `ind_finrank_eq_scalar_gen`) reduces the
multiplicity of each `S₄`-irreducible in the induced representation to a character scalar
product over `H` (order `6`); these fifteen products are evaluated by `decide` after
transporting the sum to `S₃`, and matched against the biproduct multiplicities read off by
Schur's lemma.

## Mathlib correspondence

* `Equiv.Perm (Fin 4)` — the group `S₄`.
* `Etingof.Example4_3_S4` — the five irreducible representations and their characters.
* `Etingof.exists_simples_sum_finrank_sq_eq_card` — the Artin–Wedderburn family used to
  pin down the catalogue.
-/

open CategoryTheory Module

noncomputable section

namespace Etingof.Example4_3_S4

/-! ### Pairwise non-isomorphism of the five irreducibles

Of the ten pairs, eight are separated by dimension (`1, 1, 2, 3, 3`); the two same-dimension
pairs `ℂ₊ / ℂ₋` and `ℂ³₋ / ℂ³₊` are separated by character values (the sign character is
`-1` on a transposition, and `stdRep_character_ne_rotRep_character` already records the
`ℂ³₋ / ℂ³₊` separation). -/

/-- Two `S₄`-representations of different dimension cannot be isomorphic. -/
private lemma not_iso_of_finrank_ne {V W : FDRep ℂ S4}
    (h : finrank ℂ (V : Type) ≠ finrank ℂ (W : Type)) : ¬ Nonempty (V ≅ W) := by
  rintro ⟨e⟩
  exact h (FDRep.isoToLinearEquiv e).finrank_eq

lemma trivRep_not_iso_signRep : ¬ Nonempty (trivRep ≅ signRep) := by
  rintro ⟨e⟩
  have h := congrFun (FDRep.char_iso e) (Equiv.swap (0 : Fin 4) 1)
  rw [show trivRep = FDRep.of (charRep (1 : S4 →* ℂˣ)) from rfl,
      show signRep = FDRep.of (charRep signHom) from rfl,
      charRep_character, charRep_character] at h
  simp only [MonoidHom.one_apply, Units.val_one, signHom_coe] at h
  rw [show Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 from by decide] at h
  norm_num at h

lemma trivRep_not_iso_twoDimRep : ¬ Nonempty (trivRep ≅ twoDimRep) :=
  not_iso_of_finrank_ne (by rw [trivRep_finrank, twoDimRep_finrank]; norm_num)

lemma trivRep_not_iso_stdRep : ¬ Nonempty (trivRep ≅ stdRep) :=
  not_iso_of_finrank_ne (by rw [trivRep_finrank, stdRep_finrank]; norm_num)

lemma trivRep_not_iso_rotRep : ¬ Nonempty (trivRep ≅ rotRep) :=
  not_iso_of_finrank_ne (by rw [trivRep_finrank, rotRep_finrank]; norm_num)

lemma signRep_not_iso_twoDimRep : ¬ Nonempty (signRep ≅ twoDimRep) :=
  not_iso_of_finrank_ne (by rw [signRep_finrank, twoDimRep_finrank]; norm_num)

lemma signRep_not_iso_stdRep : ¬ Nonempty (signRep ≅ stdRep) :=
  not_iso_of_finrank_ne (by rw [signRep_finrank, stdRep_finrank]; norm_num)

lemma signRep_not_iso_rotRep : ¬ Nonempty (signRep ≅ rotRep) :=
  not_iso_of_finrank_ne (by rw [signRep_finrank, rotRep_finrank]; norm_num)

lemma twoDimRep_not_iso_stdRep : ¬ Nonempty (twoDimRep ≅ stdRep) :=
  not_iso_of_finrank_ne (by rw [twoDimRep_finrank, stdRep_finrank]; norm_num)

lemma twoDimRep_not_iso_rotRep : ¬ Nonempty (twoDimRep ≅ rotRep) :=
  not_iso_of_finrank_ne (by rw [twoDimRep_finrank, rotRep_finrank]; norm_num)

lemma stdRep_not_iso_rotRep : ¬ Nonempty (stdRep ≅ rotRep) := by
  rintro ⟨e⟩
  exact stdRep_character_ne_rotRep_character (congrFun (FDRep.char_iso e) (Equiv.swap 0 1))

/-! ### Completeness of the `S₄` catalogue -/

instance : NeZero (Nat.card S4 : ℂ) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

instance : Simple trivRep := trivRep_simple
instance : Simple signRep := signRep_simple
instance : Simple twoDimRep := twoDimRep_simple
instance : Simple stdRep := stdRep_simple
instance : Simple rotRep := rotRep_simple

/-- Every simple representation of `S₄` is isomorphic to one of the five irreducibles
`trivRep` (`ℂ₊`), `signRep` (`ℂ₋`), `twoDimRep` (`ℂ²`), `stdRep` (`ℂ³₋`), or `rotRep`
(`ℂ³₊`).

This follows from the Artin–Wedderburn dimension count `1² + 1² + 2² + 3² + 3² = 24 = |S₄|`
(`irreps_dim_sum_of_squares`): the five listed irreducibles are simple, pairwise
non-isomorphic, and exhaust the squared-dimension budget, so no sixth simple can exist.
It is the `S₄` analogue of `Etingof.Discussion5_11.S3_simple_iso` and the catalogue-
completeness input for the `Ind_{S₃}^{S₄}` decompositions of Discussion 5.11(3). -/
theorem S4_simple_iso (S : FDRep ℂ S4) [Simple S] :
    Nonempty (S ≅ trivRep) ∨ Nonempty (S ≅ signRep) ∨ Nonempty (S ≅ twoDimRep) ∨
      Nonempty (S ≅ stdRep) ∨ Nonempty (S ≅ rotRep) := by
  classical
  obtain ⟨n, V, hsimple, hinj, hsurj, hsum⟩ := exists_simples_sum_finrank_sq_eq_card ℂ S4
  obtain ⟨a, ⟨ea⟩⟩ := hsurj trivRep trivRep_simple
  obtain ⟨b, ⟨eb⟩⟩ := hsurj signRep signRep_simple
  obtain ⟨c, ⟨ec⟩⟩ := hsurj twoDimRep twoDimRep_simple
  obtain ⟨d, ⟨ed⟩⟩ := hsurj stdRep stdRep_simple
  obtain ⟨f, ⟨ef⟩⟩ := hsurj rotRep rotRep_simple
  obtain ⟨s, ⟨es⟩⟩ := hsurj S inferInstance
  -- dimensions of the five distinguished indices
  have hda : finrank ℂ (V a : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv ea).finrank_eq, trivRep_finrank]
  have hdb : finrank ℂ (V b : Type) = 1 := by
    rw [← (FDRep.isoToLinearEquiv eb).finrank_eq, signRep_finrank]
  have hdc : finrank ℂ (V c : Type) = 2 := by
    rw [← (FDRep.isoToLinearEquiv ec).finrank_eq, twoDimRep_finrank]
  have hdd : finrank ℂ (V d : Type) = 3 := by
    rw [← (FDRep.isoToLinearEquiv ed).finrank_eq, stdRep_finrank]
  have hdf : finrank ℂ (V f : Type) = 3 := by
    rw [← (FDRep.isoToLinearEquiv ef).finrank_eq, rotRep_finrank]
  -- a, b, c, d, f are pairwise distinct
  have hab : a ≠ b := by rintro rfl; exact trivRep_not_iso_signRep ⟨ea ≪≫ eb.symm⟩
  have hac : a ≠ c := by rintro rfl; exact trivRep_not_iso_twoDimRep ⟨ea ≪≫ ec.symm⟩
  have had : a ≠ d := by rintro rfl; exact trivRep_not_iso_stdRep ⟨ea ≪≫ ed.symm⟩
  have haf : a ≠ f := by rintro rfl; exact trivRep_not_iso_rotRep ⟨ea ≪≫ ef.symm⟩
  have hbc : b ≠ c := by rintro rfl; exact signRep_not_iso_twoDimRep ⟨eb ≪≫ ec.symm⟩
  have hbd : b ≠ d := by rintro rfl; exact signRep_not_iso_stdRep ⟨eb ≪≫ ed.symm⟩
  have hbf : b ≠ f := by rintro rfl; exact signRep_not_iso_rotRep ⟨eb ≪≫ ef.symm⟩
  have hcd : c ≠ d := by rintro rfl; exact twoDimRep_not_iso_stdRep ⟨ec ≪≫ ed.symm⟩
  have hcf : c ≠ f := by rintro rfl; exact twoDimRep_not_iso_rotRep ⟨ec ≪≫ ef.symm⟩
  have hdf' : d ≠ f := by rintro rfl; exact stdRep_not_iso_rotRep ⟨ed ≪≫ ef.symm⟩
  -- s is one of a, b, c, d, f
  have hs : s = a ∨ s = b ∨ s = c ∨ s = d ∨ s = f := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hsa, hsb, hsc, hsd, hsf⟩ := hcon
    -- {a,b,c,d,f,s} are six distinct indices; their squared dims sum to ≥ 25 > 24
    have hsub : ({a, b, c, d, f, s} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hpos : 0 < finrank ℂ (V s : Type) := by
      haveI := hsimple s
      exact Etingof.finrank_pos_of_not_isZero (Simple.not_isZero (V s))
    have hle : ∑ i ∈ ({a, b, c, d, f, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 ≤
        ∑ i, finrank ℂ (V i : Type) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    have hcard : ∑ i ∈ ({a, b, c, d, f, s} : Finset (Fin n)), finrank ℂ (V i : Type) ^ 2 =
        finrank ℂ (V a : Type) ^ 2 + finrank ℂ (V b : Type) ^ 2 + finrank ℂ (V c : Type) ^ 2 +
          finrank ℂ (V d : Type) ^ 2 + finrank ℂ (V f : Type) ^ 2 + finrank ℂ (V s : Type) ^ 2 := by
      rw [Finset.sum_insert (by simp [hab, hac, had, haf, hsa.symm]),
        Finset.sum_insert (by simp [hbc, hbd, hbf, hsb.symm]),
        Finset.sum_insert (by simp [hcd, hcf, hsc.symm]),
        Finset.sum_insert (by simp [hdf', hsd.symm]),
        Finset.sum_insert (by simp [hsf.symm]), Finset.sum_singleton]
      ring
    have hcard24 : Fintype.card S4 = 24 := by decide
    rw [hsum, hcard24] at hle
    rw [hcard, hda, hdb, hdc, hdd, hdf] at hle
    -- 1 + 1 + 4 + 9 + 9 + (≥1) ≤ 24 is impossible
    have hsq : 1 ≤ finrank ℂ (V s : Type) ^ 2 := Nat.one_le_pow 2 _ hpos
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨es ≪≫ ea.symm⟩
  · exact Or.inr (Or.inl ⟨es ≪≫ eb.symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨es ≪≫ ec.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨es ≪≫ ed.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨es ≪≫ ef.symm⟩)))

/-! ### Group-generic Frobenius reciprocity at the dimension level

The `S₃`-decomposition file (`Discussion5_11_examples.lean`) states Frobenius reciprocity only
for `Subgroup S₃`; the proofs are group-generic, so we restate them for an arbitrary finite group
`G` here. These are the induction inputs for the `S₄ / S₃` computations below. -/

section GenericFrobenius

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
/-- The character of the restriction `Res_H S` reads `S`'s character at the underlying element. -/
lemma resObj_character' (H : Subgroup G) (S : FDRep ℂ G) (h : ↥H) :
    FDRep.character ((Action.res (FGModuleCat ℂ) H.subtype).obj S) h = S.character (h : G) := rfl

/-- **Frobenius reciprocity (dimension form), group-generic.** For a subgroup `H ≤ G`, a
finite-dimensional `H`-representation `ρ`, and any `G`-representation `S`:
`dim Hom_G(Ind_H ρ, S) = dim Hom_H(ρ, Res_H S)`. -/
theorem frobenius_finrank_gen (H : Subgroup G) {V : Type}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ G) :
    finrank ℂ (FDRep.of (Etingof.Definition5_8_1 H ρ) ⟶ S)
      = finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S) := by
  rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of (Etingof.Definition5_8_1 H ρ)) S).finrank_eq]
  have hG : (forget₂ (FDRep ℂ G) (Rep ℂ G)).obj (FDRep.of (Etingof.Definition5_8_1 H ρ))
      = Rep.ind H.subtype (Rep.of ρ) := rfl
  rw [hG, (Rep.indResHomEquiv H.subtype (Rep.of ρ)
      ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj S)).finrank_eq]
  have hWρ : Rep.of ρ = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj (FDRep.of ρ) := rfl
  have hRes : (Rep.resFunctor H.subtype).obj ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj S)
      = (forget₂ (FDRep ℂ ↥H) (Rep ℂ ↥H)).obj
          ((Action.res (FGModuleCat ℂ) H.subtype).obj S) := rfl
  have key : finrank ℂ (FDRep.of ρ ⟶ (Action.res (FGModuleCat ℂ) H.subtype).obj S)
      = finrank ℂ (Rep.of ρ ⟶ (Rep.resFunctor H.subtype).obj
          ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj S)) := by
    rw [← (FDRep.forget₂HomLinearEquiv (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)).finrank_eq, ← hWρ, ← hRes]
  rw [key]

/-- The multiplicity of a simple `S` in `Ind_H ρ`, as a scalar product of characters over `H`,
group-generic version. -/
lemma ind_finrank_eq_scalar_gen (H : Subgroup G) [Fintype ↥H] [Invertible (Fintype.card ↥H : ℂ)]
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ ↥H V) (S : FDRep ℂ G) :
    (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H ρ)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ h : ↥H, S.character (h : G) * (FDRep.of ρ).character h⁻¹ := by
  rw [Etingof.Discussion5_11.finrank_hom_symm, frobenius_finrank_gen,
    ← FDRep.scalar_product_char_eq_finrank_equivariant (FDRep.of ρ)
      ((Action.res (FGModuleCat ℂ) H.subtype).obj S)]
  simp only [resObj_character']

omit [Finite G] in
/-- The character of a representation obtained by pre-composing `τ` with a group hom `π` reads
`τ`'s character at the image. -/
lemma character_comp {K : Type} [Group K] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ K V) (π : G →* K) (g : G) :
    (FDRep.of (τ.comp π)).character g = (FDRep.of τ).character (π g) := by
  change LinearMap.trace ℂ V ((FDRep.of (τ.comp π)).ρ g)
    = LinearMap.trace ℂ V ((FDRep.of τ).ρ (π g))
  rw [FDRep.of_ρ', FDRep.of_ρ']
  rfl

end GenericFrobenius

/-! ### Realising `S₃` as the point-stabiliser subgroup `H ≤ S₄`

`S₃ = Perm (Fin 3)` embeds into `S₄ = Perm (Fin 4)` as the stabiliser of the point `3`, via
`Equiv.Perm.extendDomainHom`. We take `H` to be the range of this embedding and record the
group isomorphism `S₃ ≃* H`. -/

/-- The three points `{0, 1, 2}` that `S₃` permutes, as the subtype `{x : Fin 4 // x ≠ 3}`. -/
def e3 : Fin 3 ≃ {x : Fin 4 // x ≠ 3} where
  toFun i := ⟨i.castSucc, by fin_cases i <;> decide⟩
  invFun x := if h : (x : Fin 4).val < 3 then ⟨(x : Fin 4).val, h⟩ else 0
  left_inv := by decide
  right_inv := by decide

/-- The embedding `S₃ = Perm (Fin 3) ↪ S₄`, extending a permutation of `{0,1,2}` by fixing `3`. -/
def ιHom : Equiv.Perm (Fin 3) →* S4 := Equiv.Perm.extendDomainHom e3

lemma ιHom_injective : Function.Injective ιHom := Equiv.Perm.extendDomainHom_injective e3

/-- The sign of `ιHom σ` in `S₄` equals the sign of `σ` in `S₃`. -/
@[simp] lemma sign_ιHom (σ : Equiv.Perm (Fin 3)) :
    Equiv.Perm.sign (ιHom σ) = Equiv.Perm.sign σ :=
  Equiv.Perm.sign_extendDomain σ e3

/-- The point-stabiliser subgroup `S₃ ≤ S₄` (permutations fixing `3`), as the range of `ιHom`. -/
def H : Subgroup S4 := ιHom.range

noncomputable instance : Fintype ↥H := Fintype.ofFinite _

/-- The group isomorphism `S₃ ≃* H`. -/
noncomputable def φ : Equiv.Perm (Fin 3) ≃* ↥H := MonoidHom.ofInjective ιHom_injective

@[simp] lemma coe_φ (σ : Equiv.Perm (Fin 3)) : ((φ σ : ↥H) : S4) = ιHom σ :=
  MonoidHom.ofInjective_apply ιHom_injective

lemma H_card : Fintype.card ↥H = 6 := by
  rw [← Fintype.card_congr φ.toEquiv]; decide

noncomputable instance : Invertible (Fintype.card ↥H : ℂ) :=
  invertibleOfNonzero (by rw [H_card]; norm_num)

/-- Transport a sum over `H` to a sum over `S₃` along `φ`. -/
lemma sum_over_H (f : ↥H → ℂ) :
    ∑ h : ↥H, f h = ∑ σ : Equiv.Perm (Fin 3), f (φ σ) :=
  (Equiv.sum_comp φ.toEquiv f).symm

/-! ### The three inducing representations of `H` -/

/-- `ℂ₊` on `H`: the trivial character. -/
noncomputable def indTriv : Representation ℂ ↥H ℂ := charRep (1 : ↥H →* ℂˣ)

/-- `ℂ₋` on `H`: the restriction of the `S₄` sign character. -/
noncomputable def indSign : Representation ℂ ↥H ℂ := charRep (signHom.comp H.subtype)

/-- `ℂ²` on `H`: the `S₃` standard representation transported along `φ⁻¹`. -/
noncomputable def indStd : Representation ℂ ↥H ↥(Etingof.Discussion5_11.stdSub.toSubmodule) :=
  (Etingof.Discussion5_11.stdSub.toRepresentation).comp (φ.symm : ↥H →* Equiv.Perm (Fin 3))

lemma indTriv_character (h : ↥H) : (FDRep.of indTriv).character h = 1 := by
  rw [indTriv, charRep_character]; simp

lemma indSign_character (h : ↥H) :
    (FDRep.of indSign).character h = ((Equiv.Perm.sign (h : S4) : ℤ) : ℂ) := by
  rw [indSign, charRep_character]
  simp [MonoidHom.comp_apply, signHom_coe]

lemma indStd_character (h : ↥H) :
    (FDRep.of indStd).character h = Etingof.Discussion5_11.stdRep.character (φ.symm h) := by
  rw [indStd, character_comp]
  rfl

/-! ### The three induced multiplicity formulas -/

/-- Multiplicity of a simple `S` in `Ind_H ℂ₊`, as a sum of `S`-characters over `S₃`. -/
lemma ind_mult_triv (S : FDRep ℂ S4) :
    (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indTriv)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ σ : Equiv.Perm (Fin 3), S.character (ιHom σ) := by
  rw [ind_finrank_eq_scalar_gen, sum_over_H]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coe_φ, indTriv_character, mul_one]

/-- Multiplicity of a simple `S` in `Ind_H ℂ₋`. -/
lemma ind_mult_sign (S : FDRep ℂ S4) :
    (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indSign)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ σ : Equiv.Perm (Fin 3),
          S.character (ιHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  rw [ind_finrank_eq_scalar_gen, sum_over_H]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [indSign_character]
  simp only [coe_φ, Subgroup.coe_inv, Equiv.Perm.sign_inv, sign_ιHom]

/-- Multiplicity of a simple `S` in `Ind_H ℂ²`. -/
lemma ind_mult_std (S : FDRep ℂ S4) :
    (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indStd)) : ℂ)
      = ⅟(Fintype.card ↥H : ℂ) • ∑ σ : Equiv.Perm (Fin 3),
          S.character (ιHom σ) * ((Etingof.Discussion5_11.fixCard σ : ℂ) - 1) := by
  rw [ind_finrank_eq_scalar_gen, sum_over_H]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coe_φ, indStd_character, map_inv, φ.symm_apply_apply,
    Etingof.Discussion5_11.stdRep_character, Etingof.Discussion5_11.fixCard_inv]

/-! ### Character closed forms along the embedding, and the sum bridge -/

lemma trivChar_ιHom (σ : Equiv.Perm (Fin 3)) : trivRep.character (ιHom σ) = 1 := by
  rw [trivRep, charRep_character]; simp

lemma signChar_ιHom (σ : Equiv.Perm (Fin 3)) :
    signRep.character (ιHom σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
  rw [signRep, charRep_character, signHom_coe, sign_ιHom]

lemma stdChar_ιHom (σ : Equiv.Perm (Fin 3)) :
    stdRep.character (ιHom σ) = (fixCard (ιHom σ) : ℂ) - 1 :=
  stdRep_character (ιHom σ)

lemma rotChar_ιHom (σ : Equiv.Perm (Fin 3)) :
    rotRep.character (ιHom σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((fixCard (ιHom σ) : ℂ) - 1) := by
  rw [rotRep_character, sign_ιHom]

lemma twoDimChar_ιHom (σ : Equiv.Perm (Fin 3)) :
    twoDimRep.character (ιHom σ) = (fix3Card (ιHom σ) : ℂ) - 1 :=
  twoDimRep_character (ιHom σ)

/-- Bridge from a complex sum over `S₃` to an integer sum evaluable by `decide`. -/
lemma csum (F : Equiv.Perm (Fin 3) → ℂ) (g : Equiv.Perm (Fin 3) → ℤ) (N : ℤ)
    (hF : ∀ σ, F σ = (g σ : ℂ)) (hN : (∑ σ, g σ) = N) :
    (∑ σ : Equiv.Perm (Fin 3), F σ) = (N : ℂ) := by
  rw [Finset.sum_congr rfl fun σ _ => hF σ, ← Int.cast_sum, hN]

/-! ## The three `Ind_{S₃}^{S₄}` decompositions (Etingof Discussion 5.11(3))

Each is proved via Frobenius reciprocity: for every simple `S`, the multiplicity of `S` in the
induced representation (`ind_mult_*`) is a character scalar product over `H ≅ S₃`, evaluated by
`decide`; the right-hand multiplicity is read off `finrank_hom_biprod` + Schur; the two match on
each of the five `S₄`-irreducibles, so the objects are isomorphic. -/

/-- `Ind_{S₃}^{S₄} ℂ₊ ≅ ℂ₊ ⊕ ℂ³₋`  (`trivRep ⊞ stdRep`). -/
theorem indH_triv_decomp :
    Nonempty (FDRep.of (Etingof.Definition5_8_1 H indTriv) ≅ trivRep ⊞ stdRep) := by
  refine iso_of_forall_finrank_hom_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases S4_simple_iso S with h | h | h | h | h
  · -- S ≅ trivRep : 1 = 1 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indTriv)) : ℂ) = 1 := by
      rw [ind_mult_triv S, hc,
        csum (fun σ => trivRep.character (ιHom σ)) (fun _ => 1) 6
          (fun σ => by rw [trivChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ trivRep ⊞ stdRep) = 1 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S trivRep,
        FDRep.finrank_hom_simple_simple S stdRep, if_pos ⟨e⟩,
        if_neg (fun hh => trivRep_not_iso_stdRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ signRep : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indTriv)) : ℂ) = 0 := by
      rw [ind_mult_triv S, hc,
        csum (fun σ => signRep.character (ιHom σ)) (fun σ => (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [signChar_ιHom σ]) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ trivRep ⊞ stdRep) = 0 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S trivRep,
        FDRep.finrank_hom_simple_simple S stdRep,
        if_neg (fun hh => trivRep_not_iso_signRep ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => signRep_not_iso_stdRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ twoDimRep : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indTriv)) : ℂ) = 0 := by
      rw [ind_mult_triv S, hc,
        csum (fun σ => twoDimRep.character (ιHom σ)) (fun σ => (fix3Card (ιHom σ) : ℤ) - 1) 0
          (fun σ => by rw [twoDimChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ trivRep ⊞ stdRep) = 0 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S trivRep,
        FDRep.finrank_hom_simple_simple S stdRep,
        if_neg (fun hh => trivRep_not_iso_twoDimRep ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => twoDimRep_not_iso_stdRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ stdRep : 1 = 0 + 1
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indTriv)) : ℂ) = 1 := by
      rw [ind_mult_triv S, hc,
        csum (fun σ => stdRep.character (ιHom σ)) (fun σ => (fixCard (ιHom σ) : ℤ) - 1) 6
          (fun σ => by rw [stdChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ trivRep ⊞ stdRep) = 1 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S trivRep,
        FDRep.finrank_hom_simple_simple S stdRep,
        if_neg (fun hh => trivRep_not_iso_stdRep ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ rotRep : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indTriv)) : ℂ) = 0 := by
      rw [ind_mult_triv S, hc,
        csum (fun σ => rotRep.character (ιHom σ))
          (fun σ => (Equiv.Perm.sign σ : ℤ) * ((fixCard (ιHom σ) : ℤ) - 1)) 0
          (fun σ => by rw [rotChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ trivRep ⊞ stdRep) = 0 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S trivRep,
        FDRep.finrank_hom_simple_simple S stdRep,
        if_neg (fun hh => trivRep_not_iso_rotRep ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => stdRep_not_iso_rotRep ⟨hh.some.symm ≪≫ e⟩)]
    rw [hR]; exact_mod_cast hL

/-- `Ind_{S₃}^{S₄} ℂ₋ ≅ ℂ₋ ⊕ ℂ³₊`  (`signRep ⊞ rotRep`). -/
theorem indH_sign_decomp :
    Nonempty (FDRep.of (Etingof.Definition5_8_1 H indSign) ≅ signRep ⊞ rotRep) := by
  refine iso_of_forall_finrank_hom_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases S4_simple_iso S with h | h | h | h | h
  · -- S ≅ trivRep : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indSign)) : ℂ) = 0 := by
      rw [ind_mult_sign S, hc,
        csum (fun σ => trivRep.character (ιHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [trivChar_ιHom σ]; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ signRep ⊞ rotRep) = 0 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S signRep,
        FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => trivRep_not_iso_signRep ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => trivRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ signRep : 1 = 1 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indSign)) : ℂ) = 1 := by
      rw [ind_mult_sign S, hc,
        csum (fun σ => signRep.character (ιHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) 6
          (fun σ => by rw [signChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ signRep ⊞ rotRep) = 1 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S signRep,
        FDRep.finrank_hom_simple_simple S rotRep, if_pos ⟨e⟩,
        if_neg (fun hh => signRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ twoDimRep : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indSign)) : ℂ) = 0 := by
      rw [ind_mult_sign S, hc,
        csum (fun σ => twoDimRep.character (ιHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => ((fix3Card (ιHom σ) : ℤ) - 1) * (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [twoDimChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ signRep ⊞ rotRep) = 0 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S signRep,
        FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => signRep_not_iso_twoDimRep ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => twoDimRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ stdRep : 0 = 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indSign)) : ℂ) = 0 := by
      rw [ind_mult_sign S, hc,
        csum (fun σ => stdRep.character (ιHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => ((fixCard (ιHom σ) : ℤ) - 1) * (Equiv.Perm.sign σ : ℤ)) 0
          (fun σ => by rw [stdChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ signRep ⊞ rotRep) = 0 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S signRep,
        FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => signRep_not_iso_stdRep ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => stdRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ rotRep : 1 = 0 + 1
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indSign)) : ℂ) = 1 := by
      rw [ind_mult_sign S, hc,
        csum (fun σ => rotRep.character (ιHom σ) * ((Equiv.Perm.sign σ : ℤ) : ℂ))
          (fun σ => ((Equiv.Perm.sign σ : ℤ) * ((fixCard (ιHom σ) : ℤ) - 1)) *
            (Equiv.Perm.sign σ : ℤ)) 6
          (fun σ => by rw [rotChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ signRep ⊞ rotRep) = 1 := by
      rw [finrank_hom_biprod, FDRep.finrank_hom_simple_simple S signRep,
        FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => signRep_not_iso_rotRep ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL

/-- `Ind_{S₃}^{S₄} ℂ² ≅ ℂ² ⊕ ℂ³₋ ⊕ ℂ³₊`  (`twoDimRep ⊞ stdRep ⊞ rotRep`). -/
theorem indH_twoDim_decomp :
    Nonempty
      (FDRep.of (Etingof.Definition5_8_1 H indStd) ≅ twoDimRep ⊞ stdRep ⊞ rotRep) := by
  refine iso_of_forall_finrank_hom_eq _ _ _ rfl (fun S hS => ?_)
  haveI : Simple S := hS
  rcases S4_simple_iso S with h | h | h | h | h
  · -- S ≅ trivRep : 0 = 0 + 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indStd)) : ℂ) = 0 := by
      rw [ind_mult_std S, hc,
        csum (fun σ => trivRep.character (ιHom σ) *
            ((Etingof.Discussion5_11.fixCard σ : ℂ) - 1))
          (fun σ => (Etingof.Discussion5_11.fixCard σ : ℤ) - 1) 0
          (fun σ => by rw [trivChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ twoDimRep ⊞ stdRep ⊞ rotRep) = 0 := by
      rw [finrank_hom_biprod, finrank_hom_biprod, FDRep.finrank_hom_simple_simple S twoDimRep,
        FDRep.finrank_hom_simple_simple S stdRep, FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => trivRep_not_iso_twoDimRep ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => trivRep_not_iso_stdRep ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => trivRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ signRep : 0 = 0 + 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indStd)) : ℂ) = 0 := by
      rw [ind_mult_std S, hc,
        csum (fun σ => signRep.character (ιHom σ) *
            ((Etingof.Discussion5_11.fixCard σ : ℂ) - 1))
          (fun σ => (Equiv.Perm.sign σ : ℤ) * ((Etingof.Discussion5_11.fixCard σ : ℤ) - 1)) 0
          (fun σ => by rw [signChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ twoDimRep ⊞ stdRep ⊞ rotRep) = 0 := by
      rw [finrank_hom_biprod, finrank_hom_biprod, FDRep.finrank_hom_simple_simple S twoDimRep,
        FDRep.finrank_hom_simple_simple S stdRep, FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => signRep_not_iso_twoDimRep ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => signRep_not_iso_stdRep ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => signRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ twoDimRep : 1 = 1 + 0 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indStd)) : ℂ) = 1 := by
      rw [ind_mult_std S, hc,
        csum (fun σ => twoDimRep.character (ιHom σ) *
            ((Etingof.Discussion5_11.fixCard σ : ℂ) - 1))
          (fun σ => ((fix3Card (ιHom σ) : ℤ) - 1) *
            ((Etingof.Discussion5_11.fixCard σ : ℤ) - 1)) 6
          (fun σ => by rw [twoDimChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ twoDimRep ⊞ stdRep ⊞ rotRep) = 1 := by
      rw [finrank_hom_biprod, finrank_hom_biprod, FDRep.finrank_hom_simple_simple S twoDimRep,
        FDRep.finrank_hom_simple_simple S stdRep, FDRep.finrank_hom_simple_simple S rotRep,
        if_pos ⟨e⟩,
        if_neg (fun hh => twoDimRep_not_iso_stdRep ⟨e.symm ≪≫ hh.some⟩),
        if_neg (fun hh => twoDimRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ stdRep : 1 = 0 + 1 + 0
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indStd)) : ℂ) = 1 := by
      rw [ind_mult_std S, hc,
        csum (fun σ => stdRep.character (ιHom σ) *
            ((Etingof.Discussion5_11.fixCard σ : ℂ) - 1))
          (fun σ => ((fixCard (ιHom σ) : ℤ) - 1) *
            ((Etingof.Discussion5_11.fixCard σ : ℤ) - 1)) 6
          (fun σ => by rw [stdChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ twoDimRep ⊞ stdRep ⊞ rotRep) = 1 := by
      rw [finrank_hom_biprod, finrank_hom_biprod, FDRep.finrank_hom_simple_simple S twoDimRep,
        FDRep.finrank_hom_simple_simple S stdRep, FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => twoDimRep_not_iso_stdRep ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩,
        if_neg (fun hh => stdRep_not_iso_rotRep ⟨e.symm ≪≫ hh.some⟩)]
    rw [hR]; exact_mod_cast hL
  · -- S ≅ rotRep : 1 = 0 + 0 + 1
    obtain ⟨e⟩ := h; have hc := FDRep.char_iso e
    have hL : (finrank ℂ (S ⟶ FDRep.of (Etingof.Definition5_8_1 H indStd)) : ℂ) = 1 := by
      rw [ind_mult_std S, hc,
        csum (fun σ => rotRep.character (ιHom σ) *
            ((Etingof.Discussion5_11.fixCard σ : ℂ) - 1))
          (fun σ => ((Equiv.Perm.sign σ : ℤ) * ((fixCard (ιHom σ) : ℤ) - 1)) *
            ((Etingof.Discussion5_11.fixCard σ : ℤ) - 1)) 6
          (fun σ => by rw [rotChar_ιHom σ]; push_cast; ring) (by decide)]
      rw [invOf_smul_eq_iff, H_card, smul_eq_mul]; norm_num
    have hR : finrank ℂ (S ⟶ twoDimRep ⊞ stdRep ⊞ rotRep) = 1 := by
      rw [finrank_hom_biprod, finrank_hom_biprod, FDRep.finrank_hom_simple_simple S twoDimRep,
        FDRep.finrank_hom_simple_simple S stdRep, FDRep.finrank_hom_simple_simple S rotRep,
        if_neg (fun hh => twoDimRep_not_iso_rotRep ⟨hh.some.symm ≪≫ e⟩),
        if_neg (fun hh => stdRep_not_iso_rotRep ⟨hh.some.symm ≪≫ e⟩), if_pos ⟨e⟩]
    rw [hR]; exact_mod_cast hL

end Etingof.Example4_3_S4
