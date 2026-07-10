import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Golden
import EtingofRepresentationTheory.Chapter4.Example4_9_1
import EtingofRepresentationTheory.Chapter4.Problem4_12_5

/-!
# Problem 5.11.1: induced representations of `A₅`

**Problem 5.11.1.** Compute the decomposition into irreducibles of all the representations of
`A₅` induced from the irreducible representations of

(a) `ℤ₂`; (b) `ℤ₃`; (c) `ℤ₅`; (d) `A₄`; (e) `ℤ₂ × ℤ₂`.

## Formalization

`A₅ = ↥(alternatingGroup (Fin 5))` has five irreducible complex representations, of dimensions
`1, 3, 3', 4, 5`; they are the catalogue
`{repTriv, repC3plus, repC3minus, repC4, repC5}` built in `Etingof.Example4_8_1.A5` (the two
`3`-dimensional ones `repC3plus`, `repC3minus` are the golden-ratio icosahedral
representations, non-isomorphic). Its character table on the five classes
`(1a, 2a, 3a, 5a, 5b)` (sizes `1, 15, 20, 12, 12`) is

| | `1a` | `2a` | `3a` | `5a` | `5b` |
|---|---|---|---|---|---|
| `1`  | `1` | `1`  | `1`  | `1`     | `1`     |
| `3`  | `3` | `-1` | `0`  | `φ`     | `φ'`    |
| `3'` | `3` | `-1` | `0`  | `φ'`    | `φ`     |
| `4`  | `4` | `0`  | `1`  | `-1`    | `-1`    |
| `5`  | `5` | `1`  | `-1` | `0`     | `0`     |

with `φ = (1+√5)/2`, `φ' = (1-√5)/2`.

Each induced representation is decomposed via **Frobenius reciprocity** (Theorem 5.9.1): the
multiplicity of an irreducible `W` of `A₅` in `Ind_H^G ρ` equals the inner product
`⟨Res_H χ_W, χ_ρ⟩_H`. Because every subgroup of a given order in the list is unique up to
conjugacy in `A₅` — all involutions are conjugate (one class `2a`), all Sylow-`3` and Sylow-`5`
subgroups are conjugate, the order-`4` subgroups are the (conjugate) Klein four Sylow-`2`
subgroups `ℤ₂ × ℤ₂` (`A₅` has no element of order `4`), and the order-`12` subgroups are the
(conjugate) point stabilisers `A₄` — the decomposition depends only on the order of `H` and the
isomorphism class of the inducing character `ρ`, not on the particular subgroup chosen. We
therefore phrase each statement for an arbitrary subgroup `H` of the relevant order, and an
arbitrary irreducible `ρ` of `H` distinguished by dimension and (for one-dimensional `ρ`)
triviality of its character.

The resulting decompositions (dimensions in parentheses; `[G:H]·dim ρ` on the right):

* **(a) `H = ℤ₂`** (`|H| = 2`, index `30`), two irreducibles `1₊, 1₋`:
  * `Ind 1₊ ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³` (`30`) — the coset/edge permutation representation;
  * `Ind 1₋ ≅ 3² ⊕ 3'² ⊕ 4² ⊕ 5²` (`30`).
* **(b) `H = ℤ₃`** (`|H| = 3`, index `20`), irreducibles `1, ω, ω²`:
  * `Ind 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5` (`20`) — the coset/face permutation representation;
  * `Ind ω ≅ Ind ω² ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5²` (`20`).
* **(c) `H = ℤ₅`** (`|H| = 5`, index `12`), irreducibles `1, ζ, ζ², ζ³, ζ⁴`:
  * `Ind 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (`12`) — the coset/vertex permutation representation;
  * each nontrivial `Ind ζ^k ≅ 3 ⊕ 4 ⊕ 5` or `≅ 3' ⊕ 4 ⊕ 5` (`12`) — the pair `{ζ, ζ⁴}`
    yields one of the two `3`-dimensionals and `{ζ², ζ³}` the other (the split matches the two
    classes `5a, 5b` of `5`-cycles inside `ℤ₅`), so we state the nontrivial case as a
    disjunction over the two `3`-dimensionals.
* **(d) `H = A₄`** (`|H| = 12`, index `5`), irreducibles `1, ω, ω², 3_{A₄}`:
  * `Ind 1 ≅ 1 ⊕ 4` (`5`) — the coset/`5`-point permutation representation;
  * `Ind ω ≅ Ind ω² ≅ 5` (`5`);
  * `Ind 3_{A₄} ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5` (`15`).
* **(e) `H = ℤ₂ × ℤ₂`** (`|H| = 4`, index `15`), four irreducibles `1, χ₁, χ₂, χ₃`:
  * `Ind 1 ≅ 1 ⊕ 4 ⊕ 5²` (`15`) — the coset permutation representation;
  * each nontrivial `Ind χᵢ ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5` (`15`).

Statement pass: every decomposition is stated as `Nonempty (Ind_H^G ρ ≅ ⊞ …)` in `FDRep ℂ A₅`,
with `sorry` proofs. `Ind_H^G` is `Etingof.Definition5_8_1`; the target biproducts use the
catalogue objects `repTriv, repC3plus, repC3minus, repC4, repC5`.
-/

open CategoryTheory CategoryTheory.Limits Etingof.Example4_8_1 Etingof.Example4_8_1.A5 Module
  Finset
open scoped Pointwise

noncomputable section

namespace Etingof.Problem5_11_1

/-- `A₅`, the alternating group on five letters, as the underlying group of the catalogue. -/
abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

/-- The representation of `A₅` induced from an irreducible `σ : FDRep ℂ ↥H` of a subgroup
`H ≤ A₅`, packaged as an object of `FDRep ℂ A₅` via `Etingof.Definition5_8_1`. -/
abbrev ind {H : Subgroup A5} (σ : FDRep ℂ ↥H) : FDRep ℂ A5 :=
  FDRep.of (Etingof.Definition5_8_1 H σ.ρ)

/-! ## Character additivity over binary biproducts

The `charEq_iso` route (`Chapter5/CharEqIso.lean`) reduces each `Ind σ ≅ ⊞ …` claim to a
character identity. To compute the character of the target biproduct we need additivity of the
character over `⊞`, which is not in Mathlib; we establish it here (reusable for all of parts
(a)–(e)). -/

/-- Underlying-linear-map intertwining for a morphism of `FDRep`: the underlying `ℂ`-linear map
of `f : A ⟶ B` commutes with the `G`-actions. -/
lemma fdrep_hom_comm {G : Type} [Group G] {A B : FDRep ℂ G} (f : A ⟶ B) (g : G) (a : (A : Type)) :
    f.hom.hom.hom (A.ρ g a) = B.ρ g (f.hom.hom.hom a) := by
  have h := f.comm g
  apply_fun (fun m : A.V ⟶ B.V => m.hom.hom) at h
  have h2 := congrFun (congrArg (fun (m : (A.V.obj) →ₗ[ℂ] (B.V.obj)) => (m : _ → _)) h) a
  simpa using h2

/-- The `ℂ`-linear equivalence underlying a binary biproduct in `FDRep ℂ G`, sending `v` to its
two projections. -/
noncomputable def biprodProdEquiv {G : Type} [Group G] (X Y : FDRep ℂ G) :
    (X ⊞ Y : FDRep ℂ G) ≃ₗ[ℂ] Prod (X : Type) (Y : Type) where
  toFun v := ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v,
              (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
  map_add' a b := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' r a := Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  invFun p := (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
              (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2
  left_inv v := by
    change ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
      (X ⊞ Y : FDRep ℂ G) ⟶ (X ⊞ Y))).hom.hom.hom v = v
    rw [biprod.total]; rfl
  right_inv p := by
    have hzero : ∀ (A B : FDRep ℂ G) (x : (A : Type)), (0 : A ⟶ B).hom.hom.hom x = 0 := by
      intro A B x
      change (0 : A.V.obj ⟶ B.V.obj).hom x = 0
      simp [ModuleCat.Hom.hom]
    have hid : ∀ (A : FDRep ℂ G) (x : (A : Type)), (𝟙 A : A ⟶ A).hom.hom.hom x = x :=
      fun _ _ => rfl
    ext <;> dsimp only
    · change ((biprod.fst : X ⊞ Y ⟶ X)).hom.hom.hom
          ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
           (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.1
      rw [map_add]
      change ((biprod.inl ≫ biprod.fst : X ⟶ X)).hom.hom.hom p.1 +
           ((biprod.inr ≫ biprod.fst : Y ⟶ X)).hom.hom.hom p.2 = p.1
      rw [biprod.inl_fst, biprod.inr_fst, hid, hzero, add_zero]
    · change ((biprod.snd : X ⊞ Y ⟶ Y)).hom.hom.hom
          ((biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
           (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2) = p.2
      rw [map_add]
      change ((biprod.inl ≫ biprod.snd : X ⟶ Y)).hom.hom.hom p.1 +
           ((biprod.inr ≫ biprod.snd : Y ⟶ Y)).hom.hom.hom p.2 = p.2
      rw [biprod.inl_snd, biprod.inr_snd, hzero, hid, zero_add]

/-- **Character additivity over a binary biproduct** in `FDRep ℂ G`:
`(X ⊞ Y).character = X.character + Y.character`. -/
lemma character_biprod {G : Type} [Group G] (X Y : FDRep ℂ G) (g : G) :
    (X ⊞ Y).character g = X.character g + Y.character g := by
  have hequiv : ∀ v, (biprodProdEquiv X Y) ((X ⊞ Y).ρ g v)
      = LinearMap.prodMap (X.ρ g) (Y.ρ g) ((biprodProdEquiv X Y) v) := by
    intro v
    apply Prod.ext
    · change (biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom ((X ⊞ Y).ρ g v)
        = X.ρ g ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v)
      exact fdrep_hom_comm (biprod.fst : X ⊞ Y ⟶ X) g v
    · change (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom ((X ⊞ Y).ρ g v)
        = Y.ρ g ((biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
      exact fdrep_hom_comm (biprod.snd : X ⊞ Y ⟶ Y) g v
  have hconj : (biprodProdEquiv X Y).conj ((X ⊞ Y).ρ g)
      = LinearMap.prodMap (X.ρ g) (Y.ρ g) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have hv := hequiv ((biprodProdEquiv X Y).symm w)
    rw [LinearEquiv.apply_symm_apply] at hv
    simpa using hv
  calc (X ⊞ Y).character g
      = LinearMap.trace ℂ _ ((X ⊞ Y).ρ g) := rfl
    _ = LinearMap.trace ℂ _ ((biprodProdEquiv X Y).conj ((X ⊞ Y).ρ g)) :=
        (LinearMap.trace_conj' _ _).symm
    _ = LinearMap.trace ℂ _ (LinearMap.prodMap (X.ρ g) (Y.ρ g)) := by rw [hconj]
    _ = X.character g + Y.character g := LinearMap.trace_prodMap' _ _

/-! ## Induced-character computation for `ℤ₂`

The character of `Ind_H^G σ` is computed by the Frobenius formula (Theorem 5.9.1); for an
order-`2` subgroup `H` the twisted counts reduce, by conjugacy of `H` with the concrete cyclic
subgroup `⟨classRepA5 2⟩`, to `decide`-evaluable computations over `A₅`. -/

/-- The character of `ind σ` via the Frobenius formula (Theorem 5.9.1). -/
lemma ind_character_eq {H : Subgroup A5} [DecidablePred (· ∈ H)] (σ : FDRep ℂ ↥H) (g : A5) :
    (ind σ).character g
      = (Fintype.card ↥H : ℂ)⁻¹ *
          ∑ x : A5, if h : x * g * x⁻¹ ∈ H then σ.character ⟨x * g * x⁻¹, h⟩ else 0 := by
  have hchar : (ind σ).character g
      = LinearMap.trace ℂ (Representation.IndV H.subtype σ.ρ)
          (Etingof.Definition5_8_1 H σ.ρ g) := rfl
  rw [hchar, Etingof.Theorem5_9_1 H σ.ρ g]
  rfl

/-- Membership filter rewrite for the `x * g * x⁻¹` convention. -/
lemma twisted_filter_eq' (a g : A5) (m : ℕ) (h : orderOf a = m) :
    (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ Subgroup.zpowers a))
      = (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ (Finset.range m).image (a ^ ·))) := by
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact Etingof.Problem4_12_5.mem_zpowers_range a m h _

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The twisted counts `#{x : x·(classRepA5 j)·x⁻¹ ∈ ⟨classRepA5 2⟩}` on the five classes. -/
lemma twisted_p2' (j : Fin 5) :
    (univ.filter
        (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ Subgroup.zpowers (classRepA5 2))).card
      = ![60, 0, 4, 0, 0] j := by
  rw [twisted_filter_eq' (classRepA5 2) (classRepA5 j) 2 Etingof.Problem4_12_5.ord_cr2]
  fin_cases j <;> decide

/-- An order-`2` subgroup of `A₅` is conjugate to `⟨classRepA5 2⟩`: there is `d` with
`y ∈ H ↔ d y d⁻¹ ∈ ⟨classRepA5 2⟩`. -/
lemma exists_conj_H (H : Subgroup A5) (hH : Nat.card H = 2) :
    ∃ d : A5, ∀ y : A5, y ∈ H ↔ d * y * d⁻¹ ∈ Subgroup.zpowers (classRepA5 2) := by
  haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; norm_num)
  obtain ⟨s, hs_mem, hs_ne⟩ := H.nontrivial_iff_exists_ne_one.mp inferInstance
  have hdvd : orderOf s ∣ 2 := by
    rw [← hH]
    have := orderOf_dvd_natCard (⟨s, hs_mem⟩ : H)
    rwa [Subgroup.orderOf_mk] at this
  have hord2 : orderOf s = 2 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs_ne
    · exact h
  have hs2 : s ^ 2 = 1 := by rw [← hord2]; exact pow_orderOf_eq_one s
  have hcl : classIdxA5 s = 2 := Etingof.Problem4_12_5.classIdx_of_involution s hs2 hs_ne
  obtain ⟨c, hc⟩ := classIdxA5_spec s
  rw [hcl] at hc
  have hzs : Subgroup.zpowers s = H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hs_mem
    · rw [Nat.card_zpowers, hord2, hH]
  refine ⟨c⁻¹, fun y => ?_⟩
  have hHeq : H = MulAut.conj c • Subgroup.zpowers (classRepA5 2) := by
    rw [Etingof.Problem4_12_5.conj_smul_zpowers, hc, hzs]
  rw [hHeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]

/-- The count of conjugators landing in an order-2 `H` matches that for `⟨classRepA5 2⟩`. -/
lemma countH_eq (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2) (g : A5) :
    (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ H)).card
      = (univ.filter
          (fun x : A5 => x * g * x⁻¹ ∈ Subgroup.zpowers (classRepA5 2))).card := by
  obtain ⟨d, hd⟩ := exists_conj_H H hH
  apply Finset.card_bij' (fun x _ => d * x) (fun x _ => d⁻¹ * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd] at hx
    rw [show d * x * g * (d * x)⁻¹ = d * (x * g * x⁻¹) * d⁻¹ by group]
    exact hx
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [hd]
    rw [show d * (d⁻¹ * x * g * (d⁻¹ * x)⁻¹) * d⁻¹ = x * g * x⁻¹ by group]
    exact hx
  · intro x hx; group
  · intro x hx; group

/-- **Trivial character, class-rep values.** For an order-2 `H` and the trivial character `σ`,
`(ind σ).character` on the five class reps is `(30, 0, 2, 0, 0)`. -/
lemma indZ2_triv_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (ind σ).character (classRepA5 j) = ![30, 0, 2, 0, 0] j := by
  rw [ind_character_eq]
  have hcard : (Fintype.card ↥H : ℂ) = 2 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : A5, if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * classRepA5 j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, countH_eq H hH, twisted_p2', hcard]
  fin_cases j <;> norm_num

/-- Arbitrary-`g` trivial-character values, via the class-function property. -/
lemma indZ2_triv_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : A5) :
    (ind σ).character g = ![30, 0, 2, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ2_triv_value H hH σ htriv (classIdxA5 g)

/-- **Target character, class-rep values** for the trivial-character decomposition. -/
lemma indZ2_triv_target_value (j : Fin 5) :
    (repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5 ⊞ repC5).character
        (classRepA5 j) = ![30, 0, 2, 0, 0] j := by
  simp only [character_biprod, repTriv_character, repC3plus_character, repC3minus_character,
    repC4_character, repC5_character]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, chiA5, tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re, Q5.one_im,
      Q5.zero_re, Q5.zero_im] <;>
    ring

/-- Arbitrary-`g` target character values, via the class-function property. -/
lemma indZ2_triv_target_char_all (g : A5) :
    (repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5 ⊞ repC5).character g
      = ![30, 0, 2, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ2_triv_target_value (classIdxA5 g)

/-! ## (a) Induction from `ℤ₂` -/

/-- **(a) trivial character.** `Ind_{ℤ₂}^{A₅} 1₊ ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5³` (dimension `30`), the
permutation representation on the `30` cosets. Multiplicities `(χ_W(1a) + χ_W(2a))/2`. -/
theorem indZ2_triv (H : Subgroup A5) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅
      repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5 ⊞ repC5) := by
  classical
  apply Etingof.charEq_iso
  funext g
  rw [indZ2_triv_char_all H hH σ htriv g, indZ2_triv_target_char_all g]

/-! ## Sign character of `ℤ₂`

For the sign case we lack a triviality hypothesis, so we must pin the character of `σ` from
`Simple σ` alone. Since `|H| = 2`, `↥H = {1, t'}` with `t'² = 1`; every simple representation of
this two-element group is one-dimensional (the involution `σ.ρ t'` is a `±1`-projection, forcing
`finrank σ = 1` via the norm-one identity), so `σ.character` takes the value `1` at `1` and `±1`
at `t'`; `hntriv` selects `−1`. -/

/-- **Sign character values.** If `σ` is a simple representation of an order-`2` group with a
nontrivial character, then `σ.character x = 1` for `x = 1` and `= -1` otherwise. -/
lemma sign_char (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    ∀ x : ↥H, σ.character x = if x = 1 then (1 : ℂ) else -1 := by
  classical
  -- The two elements of `↥H`: identity and an involution `t'`.
  obtain ⟨t', ht'ne, ht'all⟩ : ∃ t' : ↥H, t' ≠ 1 ∧ ∀ x : ↥H, x = 1 ∨ x = t' := by
    obtain ⟨a, b, hab, hpair⟩ := Nat.card_eq_two_iff.mp hH
    have hmem : ∀ z : ↥H, z = a ∨ z = b := by
      intro z
      have hz : z ∈ ({a, b} : Set ↥H) := by rw [hpair]; exact Set.mem_univ z
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hmem 1 with h1 | h1
    · refine ⟨b, fun hb => hab (h1.symm.trans hb.symm), fun x => ?_⟩
      rcases hmem x with hx | hx
      · exact Or.inl (hx.trans h1.symm)
      · exact Or.inr hx
    · refine ⟨a, fun ha => hab (ha.trans h1), fun x => ?_⟩
      rcases hmem x with hx | hx
      · exact Or.inr hx
      · exact Or.inl (hx.trans h1.symm)
  -- Every element of `↥H` is self-inverse (exponent divides `2`).
  have hself : ∀ h : ↥H, h * h = 1 := fun h => by
    have hpow : h ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hH ▸ orderOf_dvd_natCard h)
    rwa [pow_two] at hpow
  have hinv : ∀ h : ↥H, h⁻¹ = h := fun h => inv_eq_of_mul_eq_one_right (hself h)
  have ht'2 : t' * t' = 1 := hself t'
  -- Norm-one identity: `∑ χ(h)·χ(h⁻¹) = |H| = 2`.
  have hnorm : ∑ h : ↥H, σ.character h * σ.character h⁻¹ = (Nat.card ↥H : ℂ) :=
    (FDRep.simple_iff_char_is_norm_one σ).mp inferInstance
  simp only [hinv] at hnorm
  have hsum2 : ∑ h : ↥H, σ.character h * σ.character h
      = σ.character 1 * σ.character 1 + σ.character t' * σ.character t' :=
    Fintype.sum_eq_add 1 t' (Ne.symm ht'ne)
      (fun x hx => (not_or.mpr hx (ht'all x)).elim)
  rw [hsum2, hH, Nat.cast_ofNat] at hnorm
  -- Character at `1` is the dimension.
  have hchar1 : σ.character 1 = (Module.finrank ℂ σ : ℂ) := FDRep.char_one σ
  rw [hchar1] at hnorm
  set d := Module.finrank ℂ σ with hd_def
  have hnorm2 : (d : ℂ) * (d : ℂ) + σ.character t' * σ.character t' = 2 := hnorm
  -- The involution `σ.ρ t'` gives an idempotent `p = (1 + σ.ρ t')/2`, whose trace is a natural
  -- number `K`; hence `χ(t') = 2K - d`.
  have hf2 : σ.ρ t' * σ.ρ t' = 1 := by rw [← map_mul, ht'2, map_one]
  set p : Module.End ℂ σ := (2⁻¹ : ℂ) • (1 + σ.ρ t') with hp_def
  have hidem : IsIdempotentElem p := by
    show p * p = p
    have e1 : p * p = (2⁻¹ * 2⁻¹ : ℂ) • ((1 + σ.ρ t') * (1 + σ.ρ t')) := by
      simp only [hp_def, smul_mul_assoc, mul_smul_comm, smul_smul]
    have e2 : (1 + σ.ρ t') * (1 + σ.ρ t') = (2 : ℂ) • (1 + σ.ρ t') := by
      have hexp : (1 + σ.ρ t') * (1 + σ.ρ t') = 1 + σ.ρ t' + σ.ρ t' + σ.ρ t' * σ.ρ t' := by
        noncomm_ring
      rw [hexp, hf2, two_smul]; abel
    rw [e1, e2, smul_smul, hp_def, show (2⁻¹ * 2⁻¹ * 2 : ℂ) = 2⁻¹ by norm_num]
  have htr : LinearMap.trace ℂ σ p = (Module.finrank ℂ (LinearMap.range p) : ℂ) :=
    (LinearMap.IsIdempotentElem.isProj_range p hidem).trace
  set K := Module.finrank ℂ (LinearMap.range p) with hK_def
  have htr2 : LinearMap.trace ℂ σ p = 2⁻¹ * ((d : ℂ) + σ.character t') := by
    simp only [hp_def, map_smul, map_add, LinearMap.trace_one, smul_eq_mul]
    rfl
  have heq : (K : ℂ) = 2⁻¹ * ((d : ℂ) + σ.character t') := htr.symm.trans htr2
  have hchi : σ.character t' = 2 * (K : ℂ) - (d : ℂ) := by linear_combination -2 * heq
  -- Integer Diophantine `d² + (2K - d)² = 2` forces `d = 1`.
  have hZ : (d : ℤ) ^ 2 + (2 * (K : ℤ) - (d : ℤ)) ^ 2 = 2 := by
    have hC : (d : ℂ) * (d : ℂ) + (2 * (K : ℂ) - (d : ℂ)) * (2 * (K : ℂ) - (d : ℂ)) = 2 := by
      rw [← hchi]; exact hnorm2
    have hcast : (((d : ℤ) ^ 2 + (2 * (K : ℤ) - (d : ℤ)) ^ 2 : ℤ) : ℂ) = ((2 : ℤ) : ℂ) := by
      push_cast; linear_combination hC
    exact_mod_cast hcast
  have hd1 : d = 1 := by
    have hsq : (d : ℤ) ^ 2 ≤ 2 := by nlinarith [sq_nonneg (2 * (K : ℤ) - (d : ℤ))]
    have hlt : d < 2 := by
      rcases Nat.lt_or_ge d 2 with h | h
      · exact h
      · exfalso
        have h2 : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast h
        nlinarith [hsq, h2]
    interval_cases d
    · exfalso
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (2 * (K : ℤ) - ((0 : ℕ) : ℤ)) ^ 2 = 4 * m := ⟨(K : ℤ) ^ 2, by ring⟩
      rw [hm] at hZ; push_cast at hZ; omega
    · rfl
  -- With `d = 1`, `χ(t')² = 1`, so `χ(t') = ±1`; `hntriv` rules out `+1`.
  have hchisq : σ.character t' * σ.character t' = 1 := by
    rw [hd1] at hnorm2; push_cast at hnorm2; linear_combination hnorm2
  have hpm : σ.character t' = 1 ∨ σ.character t' = -1 := by
    have hfac : (σ.character t' - 1) * (σ.character t' + 1) = 0 := by linear_combination hchisq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  have hchit : σ.character t' = -1 := by
    rcases hpm with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hntriv
      apply hw
      rcases ht'all w with rfl | rfl
      · rw [hchar1, hd1]; norm_num
      · exact h
    · exact h
  -- Conclude the character function.
  intro x
  rcases ht'all x with rfl | rfl
  · rw [if_pos rfl, hchar1, hd1]; norm_num
  · rw [if_neg ht'ne]; exact hchit

set_option maxRecDepth 8000 in
-- `decide` evaluates conjugation counts over all 60 elements of `A₅`, needing raised limits.
set_option maxHeartbeats 4000000 in
/-- The count `#{x : x·(classRepA5 j)·x⁻¹ = 1}` on the five classes: `60` at the identity class,
`0` elsewhere. -/
lemma oneCount (j : Fin 5) :
    (univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = 1)).card = ![60, 0, 0, 0, 0] j := by
  fin_cases j <;> decide

/-- **Sign character, class-rep values.** For an order-2 `H` and a simple nontrivial `σ`,
`(ind σ).character` on the five class reps is `(30, 0, -2, 0, 0)`. -/
lemma indZ2_sign_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (j : Fin 5) :
    (ind σ).character (classRepA5 j) = ![30, 0, -2, 0, 0] j := by
  classical
  rw [ind_character_eq]
  have hcard : (Fintype.card ↥H : ℂ) = 2 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsign := sign_char H hH σ hntriv
  have hsum : (∑ x : A5, if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ∑ x : A5, (2 * (if x * classRepA5 j * x⁻¹ = 1 then (1 : ℂ) else 0)
                    - (if x * classRepA5 j * x⁻¹ ∈ H then (1 : ℂ) else 0)) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx1 : x * classRepA5 j * x⁻¹ = 1
    · have hxH : x * classRepA5 j * x⁻¹ ∈ H := hx1 ▸ H.one_mem
      have hone : (⟨x * classRepA5 j * x⁻¹, hxH⟩ : ↥H) = 1 := Subtype.ext hx1
      rw [dif_pos hxH, hsign ⟨_, hxH⟩, hone, if_pos rfl, if_pos hx1, if_pos hxH]; ring
    · by_cases hxH : x * classRepA5 j * x⁻¹ ∈ H
      · have hne : (⟨x * classRepA5 j * x⁻¹, hxH⟩ : ↥H) ≠ 1 :=
          fun hEq => hx1 (Subtype.ext_iff.mp hEq)
        rw [dif_pos hxH, hsign ⟨_, hxH⟩, if_neg hne, if_neg hx1, if_pos hxH]; ring
      · rw [dif_neg hxH, if_neg hx1, if_neg hxH]; ring
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
    oneCount, countH_eq H hH, twisted_p2', hcard]
  fin_cases j <;> norm_num

/-- Arbitrary-`g` sign-character values, via the class-function property. -/
lemma indZ2_sign_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (g : A5) :
    (ind σ).character g = ![30, 0, -2, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ2_sign_value H hH σ hntriv (classIdxA5 g)

/-- **Target character, class-rep values** for the sign-character decomposition. -/
lemma indZ2_sign_target_value (j : Fin 5) :
    (repC3plus ⊞ repC3plus ⊞ repC3minus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5).character
        (classRepA5 j) = ![30, 0, -2, 0, 0] j := by
  simp only [character_biprod, repC3plus_character, repC3minus_character,
    repC4_character, repC5_character]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, chiA5, tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re, Q5.one_im,
      Q5.zero_re, Q5.zero_im] <;>
    ring

/-- Arbitrary-`g` target character values, via the class-function property. -/
lemma indZ2_sign_target_char_all (g : A5) :
    (repC3plus ⊞ repC3plus ⊞ repC3minus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5).character g
      = ![30, 0, -2, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ2_sign_target_value (classIdxA5 g)

/-- **(a) sign character.** `Ind_{ℤ₂}^{A₅} 1₋ ≅ 3² ⊕ 3'² ⊕ 4² ⊕ 5²` (dimension `30`).
Multiplicities `(χ_W(1a) − χ_W(2a))/2`. -/
theorem indZ2_sign (H : Subgroup A5) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅
      repC3plus ⊞ repC3plus ⊞ repC3minus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  classical
  apply Etingof.charEq_iso
  funext g
  rw [indZ2_sign_char_all H hH σ hntriv g, indZ2_sign_target_char_all g]

/-! ## (b) Induction from `ℤ₃` -/

/-- **(b) trivial character.** `Ind_{ℤ₃}^{A₅} 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5` (dimension `20`), the
permutation representation on the `20` cosets. Multiplicities `(χ_W(1a) + 2·χ_W(3a))/3`. -/
theorem indZ3_triv (H : Subgroup A5) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5) := by
  sorry

/-- **(b) nontrivial character.** For either nontrivial character `ω, ω²`,
`Ind_{ℤ₃}^{A₅} ω ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5²` (dimension `20`). -/
theorem indZ3_nontriv (H : Subgroup A5) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  sorry

/-! ## (c) Induction from `ℤ₅` -/

/-- **(c) trivial character.** `Ind_{ℤ₅}^{A₅} 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (dimension `12`), the
permutation representation on the `12` cosets. Multiplicities `(χ_W(1a) + 2·χ_W(5a) +
2·χ_W(5b))/5`. -/
theorem indZ5_triv (H : Subgroup A5) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC5) := by
  sorry

/-- **(c) nontrivial character.** For any of the four nontrivial characters `ζ^k` (`k ≠ 0`),
`Ind_{ℤ₅}^{A₅} ζ^k` is `3 ⊕ 4 ⊕ 5` or `3' ⊕ 4 ⊕ 5` (dimension `12`); the pair `{ζ, ζ⁴}` picks
one `3`-dimensional and `{ζ², ζ³}` the other. -/
theorem indZ5_nontriv (H : Subgroup A5) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC4 ⊞ repC5) ∨
      Nonempty (ind σ ≅ repC3minus ⊞ repC4 ⊞ repC5) := by
  sorry

/-! ## (d) Induction from `A₄` -/

/-- **(d) trivial character.** `Ind_{A₄}^{A₅} 1 ≅ 1 ⊕ 4` (dimension `5`), the permutation
representation on the `5` cosets. -/
theorem indA4_triv (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 1)
    (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC4) := by
  sorry

/-- **(d) nontrivial linear character.** For either nontrivial one-dimensional character
`ω, ω²` of `A₄`, `Ind_{A₄}^{A₅} ω ≅ 5` (dimension `5`). -/
theorem indA4_nontriv_linear (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 1)
    (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC5) := by
  sorry

/-- **(d) three-dimensional character.** `Ind_{A₄}^{A₅} 3_{A₄} ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5`
(dimension `15`). -/
theorem indA4_threeDim (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 3) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5) := by
  sorry

/-! ## (e) Induction from `ℤ₂ × ℤ₂` -/

/-- **(e) trivial character.** `Ind_{ℤ₂×ℤ₂}^{A₅} 1 ≅ 1 ⊕ 4 ⊕ 5²` (dimension `15`), the
permutation representation on the `15` cosets. -/
theorem indV4_triv (H : Subgroup A5) (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  sorry

/-- **(e) nontrivial character.** For any of the three nontrivial characters `χ₁, χ₂, χ₃` of
`ℤ₂ × ℤ₂`, `Ind_{ℤ₂×ℤ₂}^{A₅} χᵢ ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5` (dimension `15`). -/
theorem indV4_nontriv (H : Subgroup A5) (hH : Nat.card H = 4)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5) := by
  sorry

end Etingof.Problem5_11_1
