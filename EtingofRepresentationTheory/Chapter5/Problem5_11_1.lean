import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1
import EtingofRepresentationTheory.Chapter5.Theorem5_9_1
import EtingofRepresentationTheory.Chapter5.CharEqIso
import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Golden
import EtingofRepresentationTheory.Chapter4.Example4_9_1
import EtingofRepresentationTheory.Chapter4.Problem4_12_5
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Example4_3_FiniteAbelianGroups

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

/-! ## Induced-character computation for `ℤ₃`

The order-`3` analogue of the `ℤ₂` machinery above: an order-`3` subgroup `H` is conjugate to the
concrete cyclic subgroup `⟨classRepA5 1⟩` (the `3a` class of `3`-cycles), which reduces the twisted
counts to `decide`-evaluable computations over `A₅`. -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Every order-`3` element of `A₅` lies in class `3a` (index `1`). -/
lemma classIdx_of_order3 (s : A5) (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    classIdxA5 s = 1 := by
  revert s; decide

/-- An order-`3` subgroup of `A₅` is conjugate to `⟨classRepA5 1⟩`. -/
lemma exists_conj_H3 (H : Subgroup A5) (hH : Nat.card H = 3) :
    ∃ d : A5, ∀ y : A5, y ∈ H ↔ d * y * d⁻¹ ∈ Subgroup.zpowers (classRepA5 1) := by
  haveI : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hH]; norm_num)
  obtain ⟨s, hs_mem, hs_ne⟩ := H.nontrivial_iff_exists_ne_one.mp inferInstance
  have hdvd : orderOf s ∣ 3 := by
    rw [← hH]
    have := orderOf_dvd_natCard (⟨s, hs_mem⟩ : H)
    rwa [Subgroup.orderOf_mk] at this
  have hord3 : orderOf s = 3 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hs_ne
    · exact h
  have hs3 : s ^ 3 = 1 := by rw [← hord3]; exact pow_orderOf_eq_one s
  have hcl : classIdxA5 s = 1 := classIdx_of_order3 s hs3 hs_ne
  obtain ⟨c, hc⟩ := classIdxA5_spec s
  rw [hcl] at hc
  have hzs : Subgroup.zpowers s = H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact hs_mem
    · rw [Nat.card_zpowers, hord3, hH]
  refine ⟨c⁻¹, fun y => ?_⟩
  have hHeq : H = MulAut.conj c • Subgroup.zpowers (classRepA5 1) := by
    rw [Etingof.Problem4_12_5.conj_smul_zpowers, hc, hzs]
  rw [hHeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply, inv_inv]

/-- The count of conjugators landing in an order-`3` `H` matches that for `⟨classRepA5 1⟩`. -/
lemma countH_eq3 (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3) (g : A5) :
    (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ H)).card
      = (univ.filter
          (fun x : A5 => x * g * x⁻¹ ∈ Subgroup.zpowers (classRepA5 1))).card := by
  obtain ⟨d, hd⟩ := exists_conj_H3 H hH
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

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The twisted counts `#{x : x·(classRepA5 j)·x⁻¹ ∈ ⟨classRepA5 1⟩}` on the five classes. -/
lemma twisted_p1' (j : Fin 5) :
    (univ.filter
        (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ Subgroup.zpowers (classRepA5 1))).card
      = ![60, 6, 0, 0, 0] j := by
  rw [twisted_filter_eq' (classRepA5 1) (classRepA5 j) 3 Etingof.Problem4_12_5.ord_cr1]
  fin_cases j <;> decide

/-! ## (b) Induction from `ℤ₃` -/

/-- **Trivial character, class-rep values.** For an order-`3` `H` and the trivial character `σ`,
`(ind σ).character` on the five class reps is `(20, 2, 0, 0, 0)`. -/
lemma indZ3_triv_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (ind σ).character (classRepA5 j) = ![20, 2, 0, 0, 0] j := by
  rw [ind_character_eq]
  have hcard : (Fintype.card ↥H : ℂ) = 3 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : A5, if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * classRepA5 j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, countH_eq3 H hH, twisted_p1', hcard]
  fin_cases j <;> norm_num

/-- Arbitrary-`g` trivial-character values, via the class-function property. -/
lemma indZ3_triv_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : A5) :
    (ind σ).character g = ![20, 2, 0, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ3_triv_value H hH σ htriv (classIdxA5 g)

/-- **Target character, class-rep values** for the trivial-character decomposition. -/
lemma indZ3_triv_target_value (j : Fin 5) :
    (repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5).character
        (classRepA5 j) = ![20, 2, 0, 0, 0] j := by
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
lemma indZ3_triv_target_char_all (g : A5) :
    (repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5).character g
      = ![20, 2, 0, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ3_triv_target_value (classIdxA5 g)

/-- **(b) trivial character.** `Ind_{ℤ₃}^{A₅} 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 4² ⊕ 5` (dimension `20`), the
permutation representation on the `20` cosets. Multiplicities `(χ_W(1a) + 2·χ_W(3a))/3`. -/
theorem indZ3_triv (H : Subgroup A5) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5) := by
  classical
  apply Etingof.charEq_iso
  funext g
  rw [indZ3_triv_char_all H hH σ htriv g, indZ3_triv_target_char_all g]

/-- The number of conjugators sending `g` to `y₂` equals the number sending it to a conjugate
`y₁` (bijection `x ↦ c⁻¹ x` where `c y₁ c⁻¹ = y₂`). -/
lemma conjCount_shift (g y₁ y₂ : A5) (hconj : ∃ c : A5, c * y₁ * c⁻¹ = y₂) :
    (univ.filter (fun x : A5 => x * g * x⁻¹ = y₂)).card
      = (univ.filter (fun x : A5 => x * g * x⁻¹ = y₁)).card := by
  obtain ⟨c, hc⟩ := hconj
  apply Finset.card_bij' (fun x _ => c⁻¹ * x) (fun x _ => c * x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [show c⁻¹ * x * g * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * g * x⁻¹) * c by group, hx, ← hc]; group
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [show c * x * g * (c * x)⁻¹ = c * (x * g * x⁻¹) * c⁻¹ by group, hx]; exact hc
  · intro x hx; group
  · intro x hx; group

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The counts `#{x : x·(classRepA5 j)·x⁻¹ = classRepA5 1}` on the five classes: nonzero only on
the `3a` class, where the centralizer of a `3`-cycle contributes `3`. -/
lemma twisted_eq_cr1 (j : Fin 5) :
    (univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = classRepA5 1)).card = ![0, 3, 0, 0, 0] j := by
  fin_cases j <;> decide

/-- **Nontrivial character, class-rep values.** For an order-`3` `H` and a simple nontrivial `σ`,
`(ind σ).character` on the five class reps is `(20, -1, 0, 0, 0)`. -/
lemma indZ3_nontriv_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (j : Fin 5) :
    (ind σ).character (classRepA5 j) = ![20, -1, 0, 0, 0] j := by
  classical
  -- Character facts: `σ` is one-dimensional and its character is multiplicative.
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hcyc : IsCyclic ↥H := isCyclic_of_prime_card hH
  letI cg : CommGroup ↥H := IsCyclic.commGroup
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ ↥H) (Representation.asModule σ.ρ) :=
    Etingof.isSimpleModule_asModule_of_simple σ
  have hdim : Module.finrank ℂ (σ : Type) = 1 := Etingof.Example4_3_FiniteAbelianGroups σ.ρ
  have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
    have hcc : σ.character g = c := by
      change LinearMap.trace ℂ _ (σ.ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
    rw [hcc]; exact hc
  have hone : σ.character 1 = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : ↥H, σ.character (g * h) = σ.character g * σ.character h := by
    intro g h
    have key : (σ.character (g * h) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
             = (σ.character g * σ.character h : ℂ) • LinearMap.id := by
      rw [← hscalar (g * h), map_mul, hscalar g, hscalar h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
    rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at htr
  -- The character packaged as a monoid hom, for `map_pow`.
  set χ : ↥H →* ℂ := { toFun := σ.character, map_one' := hone, map_mul' := hmul } with hχ
  have hχa : ∀ g : ↥H, χ g = σ.character g := fun _ => rfl
  -- A generator `a₀` of `H`, its underlying element `a`, and `a2 = a ^ 2`.
  obtain ⟨a₀, ha₀⟩ := hcyc.exists_generator
  have horda₀ : orderOf a₀ = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers ha₀]; exact hH
  set a : A5 := (a₀ : A5) with ha_def
  set a2 : A5 := a ^ 2 with ha2_def
  have horda : orderOf a = 3 := by
    rw [ha_def, ← horda₀]
    exact orderOf_injective H.subtype (Subgroup.subtype_injective H) a₀
  have ha3 : a ^ 3 = 1 := by rw [← horda]; exact pow_orderOf_eq_one a
  have ha_ne1 : a ≠ 1 := by
    intro h; rw [h, orderOf_one] at horda; exact absurd horda (by norm_num)
  have ha2_ne1 : a2 ≠ 1 := by
    rw [ha2_def]; intro h
    have h2 := orderOf_le_of_pow_eq_one (n := 2) (by norm_num) h
    rw [horda] at h2; omega
  obtain ⟨z, hz_def⟩ : ∃ z : ℂ, z = σ.character a₀ := ⟨σ.character a₀, rfl⟩
  have ha₀3 : a₀ ^ 3 = 1 := by rw [← horda₀]; exact pow_orderOf_eq_one a₀
  have hz3 : z ^ 3 = 1 := by
    have h := map_pow χ a₀ 3
    rw [ha₀3, map_one, hχa, ← hz_def] at h; exact h.symm
  have hchar_a2 : σ.character (a₀ ^ 2) = z ^ 2 := by
    have h := map_pow χ a₀ 2
    rw [hχa, hχa, ← hz_def] at h; exact h
  -- Enumerate the elements of `H`.
  have hgen_top : Subgroup.zpowers a₀ = ⊤ := by rw [eq_top_iff]; intro x _; exact ha₀ x
  have hHzp : Subgroup.zpowers a = H := by
    have h1 : (Subgroup.zpowers a₀).map H.subtype = Subgroup.zpowers a :=
      MonoidHom.map_zpowers H.subtype a₀
    rw [hgen_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have ha2coe : a2 = ((a₀ ^ 2 : ↥H) : A5) := by rw [ha2_def, ha_def]; push_cast; ring
  have henum : ∀ y : A5, y ∈ H → y = 1 ∨ y = a ∨ y = a2 := by
    intro y hy
    rw [← hHzp, Etingof.Problem4_12_5.mem_zpowers_range a 3 horda] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨k, hk, hky⟩ := hy
    interval_cases k
    · left; rw [← hky]; simp
    · right; left; rw [← hky]; simp
    · right; right; rw [← hky, ha2_def]
  have ha_mem : a ∈ H := by rw [ha_def]; exact SetLike.coe_mem a₀
  have ha2_mem : a2 ∈ H := by rw [ha2coe]; exact SetLike.coe_mem _
  have hne_aa2 : a ≠ a2 := by
    intro h
    rw [ha2_def, sq] at h
    exact ha_ne1 (mul_left_cancel (a := a) (by rw [mul_one]; exact h.symm))
  -- The two nontrivial elements are conjugate (in `A₅`) to the class rep `classRepA5 1`.
  have hconj_a : ∃ c : A5, c * classRepA5 1 * c⁻¹ = a := by
    obtain ⟨c, hc⟩ := classIdxA5_spec a
    rw [classIdx_of_order3 a ha3 ha_ne1] at hc; exact ⟨c, hc⟩
  have ha2_3 : a2 ^ 3 = 1 := by rw [ha2_def, ← pow_mul, mul_comm, pow_mul, ha3, one_pow]
  have hconj_a2 : ∃ c : A5, c * classRepA5 1 * c⁻¹ = a2 := by
    obtain ⟨c, hc⟩ := classIdxA5_spec a2
    rw [classIdx_of_order3 a2 ha2_3 ha2_ne1] at hc; exact ⟨c, hc⟩
  -- `z + z^2 = -1`.
  have hz_ne : z ≠ 1 := by
    obtain ⟨h0, hh0⟩ := hntriv
    rcases henum (h0 : A5) (SetLike.coe_mem h0) with he | he | he
    · exact absurd (by rw [show h0 = 1 from Subtype.ext he]; exact hone) hh0
    · intro hz1; apply hh0
      rw [show h0 = a₀ from Subtype.ext (he.trans ha_def), ← hz_def]; exact hz1
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 2 from Subtype.ext (he.trans ha2coe), hchar_a2, hz1]; ring
  have hz_sum : z + z ^ 2 = -1 := by
    have hfac : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination hz3
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h) hz_ne
    · linear_combination h
  -- Reduce the induced character to a weighted sum of conjugator counts.
  rw [ind_character_eq]
  have hcardℂ : (Fintype.card ↥H : ℂ) = 3 := by rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hterm : ∀ x : A5,
      (if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨x * classRepA5 j * x⁻¹, h⟩ else 0)
        = σ.character 1 * (if x * classRepA5 j * x⁻¹ = 1 then (1 : ℂ) else 0)
          + z * (if x * classRepA5 j * x⁻¹ = a then 1 else 0)
          + z ^ 2 * (if x * classRepA5 j * x⁻¹ = a2 then 1 else 0) := by
    intro x
    set y := x * classRepA5 j * x⁻¹ with hy
    by_cases hmem : y ∈ H
    · rcases henum y hmem with h1 | ha | ha2
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = 1 from Subtype.ext h1, if_pos h1,
          if_neg (by intro h; rw [h1] at h; exact ha_ne1 h.symm),
          if_neg (by intro h; rw [h1] at h; exact ha2_ne1 h.symm)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ from Subtype.ext (ha.trans ha_def),
          if_neg (by intro h; rw [ha] at h; exact ha_ne1 h),
          if_pos ha, if_neg (by intro h; rw [ha] at h; exact hne_aa2 h), ← hz_def]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 2 from Subtype.ext (ha2.trans ha2coe),
          hchar_a2, if_neg (by intro h; rw [ha2] at h; exact ha2_ne1 h),
          if_neg (by intro h; rw [ha2] at h; exact hne_aa2 h.symm), if_pos ha2]
        ring
    · rw [dif_neg hmem,
        if_neg (by intro h; exact hmem (by rw [h]; exact H.one_mem)),
        if_neg (by intro h; exact hmem (by rw [h]; exact ha_mem)),
        if_neg (by intro h; exact hmem (by rw [h]; exact ha2_mem))]
      ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
    Finset.sum_boole, hone, oneCount,
    conjCount_shift (classRepA5 j) (classRepA5 1) a hconj_a,
    conjCount_shift (classRepA5 j) (classRepA5 1) a2 hconj_a2, twisted_eq_cr1, hcardℂ]
  fin_cases j <;> norm_num <;> linear_combination hz_sum

/-- Arbitrary-`g` nontrivial-character values, via the class-function property. -/
lemma indZ3_nontriv_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) (g : A5) :
    (ind σ).character g = ![20, -1, 0, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ3_nontriv_value H hH σ hntriv (classIdxA5 g)

/-- **Target character, class-rep values** for the nontrivial-character decomposition. -/
lemma indZ3_nontriv_target_value (j : Fin 5) :
    (repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5 ⊞ repC5).character (classRepA5 j)
      = ![20, -1, 0, 0, 0] j := by
  simp only [character_biprod, repC3plus_character, repC3minus_character, repC4_character,
    repC5_character]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, chiA5, tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re, Q5.one_im,
      Q5.zero_re, Q5.zero_im] <;>
    ring

/-- Arbitrary-`g` target character values, via the class-function property. -/
lemma indZ3_nontriv_target_char_all (g : A5) :
    (repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5 ⊞ repC5).character g
      = ![20, -1, 0, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ3_nontriv_target_value (classIdxA5 g)

/-- **(b) nontrivial character.** For either nontrivial character `ω, ω²`,
`Ind_{ℤ₃}^{A₅} ω ≅ 3 ⊕ 3' ⊕ 4 ⊕ 5²` (dimension `20`). -/
theorem indZ3_nontriv (H : Subgroup A5) (hH : Nat.card H = 3)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC3minus ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  classical
  apply Etingof.charEq_iso
  funext g
  rw [indZ3_nontriv_char_all H hH σ hntriv g, indZ3_nontriv_target_char_all g]

/-! ## (c) Induction from `ℤ₅`

For an order-`5` subgroup `H` the twisted counts reduce, by conjugacy of `H` with the concrete
Sylow `5`-subgroup `⟨classRepA5 3⟩` (all Sylow `5`-subgroups are conjugate), to `decide`-evaluable
computations over `A₅`. -/

set_option maxRecDepth 8000 in
-- `decide` evaluates the twisted membership over all 60 elements of `A₅`, needing raised limits.
set_option maxHeartbeats 4000000 in
/-- The twisted counts `#{x : x·(classRepA5 j)·x⁻¹ ∈ ⟨classRepA5 3⟩}` on the five classes:
`60` at the identity, `10` at each of the two `5`-cycle classes (`⟨classRepA5 3⟩` contains two
elements of each `5`-cycle class), `0` on `3a`/`2a`. -/
lemma twisted_p5' (j : Fin 5) :
    (univ.filter
        (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ Subgroup.zpowers (classRepA5 3))).card
      = ![60, 0, 0, 10, 10] j := by
  rw [twisted_filter_eq' (classRepA5 3) (classRepA5 j) 5 Etingof.Problem4_12_5.ord_cr3]
  fin_cases j <;> decide

/-- An order-`5` subgroup of `A₅` is conjugate to `⟨classRepA5 3⟩`: there is `d` with
`y ∈ H ↔ d y d⁻¹ ∈ ⟨classRepA5 3⟩` (Sylow's second theorem — all Sylow `5`-subgroups are
conjugate). -/
lemma exists_conj_H5 (H : Subgroup A5) (hH : Nat.card H = 5) :
    ∃ d : A5, ∀ y : A5, y ∈ H ↔ d * y * d⁻¹ ∈ Subgroup.zpowers (classRepA5 3) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 A5 := Sylow.ofCard H (by rw [hH, Etingof.Problem4_12_5.fact5, pow_one])
  have hQc : Nat.card (Subgroup.zpowers (classRepA5 3)) = 5 := by
    rw [Nat.card_zpowers, Etingof.Problem4_12_5.ord_cr3]
  let Q : Sylow 5 A5 := Sylow.ofCard (Subgroup.zpowers (classRepA5 3))
    (by rw [hQc, Etingof.Problem4_12_5.fact5, pow_one])
  obtain ⟨cc, hcc⟩ := MulAction.exists_smul_eq A5 P Q
  have hPc : (P : Subgroup A5) = H := Sylow.coe_ofCard _ _
  have hQcoe : (Q : Subgroup A5) = Subgroup.zpowers (classRepA5 3) := Sylow.coe_ofCard _ _
  have hco : (Q : Subgroup A5) = MulAut.conj cc • (P : Subgroup A5) := by rw [← hcc]; rfl
  have hzeq : Subgroup.zpowers (classRepA5 3) = MulAut.conj cc • H := by
    rw [← hQcoe, ← hPc]; exact hco
  refine ⟨cc, fun y => ?_⟩
  rw [hzeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · intro hy; rw [show cc⁻¹ * (cc * y * cc⁻¹) * cc = y by group]; exact hy
  · intro hy; rw [show cc⁻¹ * (cc * y * cc⁻¹) * cc = y by group] at hy; exact hy

/-- The count of conjugators landing in an order-`5` `H` matches that for `⟨classRepA5 3⟩`. -/
lemma countH_eq5 (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5) (g : A5) :
    (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ H)).card
      = (univ.filter
          (fun x : A5 => x * g * x⁻¹ ∈ Subgroup.zpowers (classRepA5 3))).card := by
  obtain ⟨d, hd⟩ := exists_conj_H5 H hH
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

/-- **Trivial character, class-rep values.** For an order-`5` `H` and the trivial character `σ`,
`(ind σ).character` on the five class reps is `(12, 0, 0, 2, 2)`. -/
lemma indZ5_triv_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (ind σ).character (classRepA5 j) = ![12, 0, 0, 2, 2] j := by
  rw [ind_character_eq]
  have hcard : (Fintype.card ↥H : ℂ) = 5 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : A5, if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * classRepA5 j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, countH_eq5 H hH, twisted_p5', hcard]
  fin_cases j <;> norm_num

/-- Arbitrary-`g` trivial-character values, via the class-function property. -/
lemma indZ5_triv_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : A5) :
    (ind σ).character g = ![12, 0, 0, 2, 2] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ5_triv_value H hH σ htriv (classIdxA5 g)

/-- **Target character, class-rep values** for the trivial-character decomposition. -/
lemma indZ5_triv_target_value (j : Fin 5) :
    (repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC5).character (classRepA5 j)
      = ![12, 0, 0, 2, 2] j := by
  simp only [character_biprod, repTriv_character, repC3plus_character, repC3minus_character,
    repC5_character]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, chiA5, tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re, Q5.one_im,
      Q5.zero_re, Q5.zero_im] <;>
    ring

/-- Arbitrary-`g` target character values, via the class-function property. -/
lemma indZ5_triv_target_char_all (g : A5) :
    (repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC5).character g
      = ![12, 0, 0, 2, 2] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ5_triv_target_value (classIdxA5 g)

/-- **(c) trivial character.** `Ind_{ℤ₅}^{A₅} 1 ≅ 1 ⊕ 3 ⊕ 3' ⊕ 5` (dimension `12`), the
permutation representation on the `12` cosets. Multiplicities `(χ_W(1a) + 2·χ_W(5a) +
2·χ_W(5b))/5`. -/
theorem indZ5_triv (H : Subgroup A5) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC3plus ⊞ repC3minus ⊞ repC5) := by
  classical
  apply Etingof.charEq_iso
  funext g
  rw [indZ5_triv_char_all H hH σ htriv g, indZ5_triv_target_char_all g]

/-! ### Nontrivial characters of `ℤ₅`

Unlike the `3`-cycle class, the two `5`-cycle classes `5a`/`5b` are distinct, and the four
nontrivial elements `a, a², a³, a⁴` of `H = ⟨a⟩` split as `{a, a⁴} ⊂ 5x`, `{a², a³} ⊂ 5y`
(inverse pairs), with `{5x, 5y} = {5a, 5b}` depending on the class of the generator. The
induced character therefore takes values `z + z⁴` and `z² + z³` (`z = χ(a)` a primitive `5`th
root of unity) on the two `5`-cycle classes, in one order or the other. Both are roots of
`t² + t − 1`, i.e. `(−1 ± √5)/2`, matching the golden-ratio character values of `3`/`3'`. -/

set_option maxRecDepth 8000 in
-- honest `decide` over the 60 elements: which `5`-cycle class each power of an order-`5`
-- element lands in (`{s, s⁴}` share a class, `{s², s³}` the other).
set_option maxHeartbeats 4000000 in
/-- For an order-`5` element `s`, the powers split as `{s, s⁴}` in one `5`-cycle class and
`{s², s³}` in the other (`3 = 5a`, `4 = 5b`). -/
lemma classIdxA5_pow5 (s : A5) (h5 : s ^ 5 = 1) (hne : s ≠ 1) :
    (classIdxA5 s = 3 ∧ classIdxA5 (s ^ 2) = 4 ∧ classIdxA5 (s ^ 3) = 4 ∧ classIdxA5 (s ^ 4) = 3)
    ∨ (classIdxA5 s = 4 ∧ classIdxA5 (s ^ 2) = 3 ∧ classIdxA5 (s ^ 3) = 3 ∧
        classIdxA5 (s ^ 4) = 4) := by
  revert s; decide

set_option maxRecDepth 8000 in
-- `decide` evaluates the conjugator equality over all 60 elements of `A₅`.
set_option maxHeartbeats 4000000 in
/-- The count `#{x : x·(classRepA5 j)·x⁻¹ = classRepA5 3}`: `5` (the centralizer order) on the
`5a` class, `0` elsewhere. -/
lemma cr3Count (j : Fin 5) :
    (univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = classRepA5 3)).card
      = ![0, 0, 0, 5, 0] j := by
  fin_cases j <;> decide

set_option maxRecDepth 8000 in
-- `decide` evaluates the conjugator equality over all 60 elements of `A₅`.
set_option maxHeartbeats 4000000 in
/-- The count `#{x : x·(classRepA5 j)·x⁻¹ = classRepA5 4}`: `5` (the centralizer order) on the
`5b` class, `0` elsewhere. -/
lemma cr4Count (j : Fin 5) :
    (univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = classRepA5 4)).card
      = ![0, 0, 0, 0, 5] j := by
  fin_cases j <;> decide

/-- **Target character (`3 ⊕ 4 ⊕ 5`), class-rep values.** `(3, 4, 5)` sum to
`(12, 0, 0, (−1+√5)/2, (−1−√5)/2)` on the five class reps. -/
lemma indZ5_target1_value (j : Fin 5) :
    (repC3plus ⊞ repC4 ⊞ repC5).character (classRepA5 j)
      = ![12, 0, 0, (-1 + (Real.sqrt 5 : ℂ)) / 2, (-1 - (Real.sqrt 5 : ℂ)) / 2] j := by
  simp only [character_biprod, repC3plus_character, repC4_character, repC5_character]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, chiA5, tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re, Q5.one_im,
      Q5.zero_re, Q5.zero_im] <;>
    ring

/-- **Target character (`3' ⊕ 4 ⊕ 5`), class-rep values.** `(3', 4, 5)` sum to
`(12, 0, 0, (−1−√5)/2, (−1+√5)/2)` on the five class reps (the two `5`-cycle values swapped). -/
lemma indZ5_target2_value (j : Fin 5) :
    (repC3minus ⊞ repC4 ⊞ repC5).character (classRepA5 j)
      = ![12, 0, 0, (-1 - (Real.sqrt 5 : ℂ)) / 2, (-1 + (Real.sqrt 5 : ℂ)) / 2] j := by
  simp only [character_biprod, repC3minus_character, repC4_character, repC5_character]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, chiA5, tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im, Q5.one_re, Q5.one_im,
      Q5.zero_re, Q5.zero_im] <;>
    ring

/-- **Nontrivial character, class-rep values.** For an order-`5` `H` and a simple nontrivial `σ`
with `z = σ.character` of a generator, `(ind σ).character` takes the values
`(12, 0, 0, A, B)` on the five class reps, where `{A, B} = {z + z⁴, z² + z³}` (in one order or the
other, per the class of the generator), `A + B = -1`, and `A² + A − 1 = 0`. -/
lemma indZ5_nontriv_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    ∃ A B : ℂ, A + B = -1 ∧ A ^ 2 + A - 1 = 0 ∧
      ∀ j, (ind σ).character (classRepA5 j) = ![12, 0, 0, A, B] j := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hcyc : IsCyclic ↥H := isCyclic_of_prime_card hH
  letI cg : CommGroup ↥H := IsCyclic.commGroup
  haveI hsm : IsSimpleModule (MonoidAlgebra ℂ ↥H) (Representation.asModule σ.ρ) :=
    Etingof.isSimpleModule_asModule_of_simple σ
  have hdim : Module.finrank ℂ (σ : Type) = 1 := Etingof.Example4_3_FiniteAbelianGroups σ.ρ
  have hscalar : ∀ g : ↥H, σ.ρ g = (σ.character g : ℂ) • LinearMap.id := by
    intro g
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (σ.ρ g)
    have hcc : σ.character g = c := by
      change LinearMap.trace ℂ _ (σ.ρ g) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]; simp
    rw [hcc]; exact hc
  have hone : σ.character 1 = 1 := by rw [FDRep.char_one, hdim, Nat.cast_one]
  have hmul : ∀ g h : ↥H, σ.character (g * h) = σ.character g * σ.character h := by
    intro g h
    have key : (σ.character (g * h) : ℂ) • (LinearMap.id : (σ : Type) →ₗ[ℂ] (σ : Type))
             = (σ.character g * σ.character h : ℂ) • LinearMap.id := by
      rw [← hscalar (g * h), map_mul, hscalar g, hscalar h]
      ext x
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_smul]
    have htr := congrArg (LinearMap.trace ℂ (σ : Type)) key
    rwa [map_smul, map_smul, LinearMap.trace_id, hdim, Nat.cast_one, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at htr
  set χ : ↥H →* ℂ := { toFun := σ.character, map_one' := hone, map_mul' := hmul } with hχ
  have hχa : ∀ g : ↥H, χ g = σ.character g := fun _ => rfl
  obtain ⟨a₀, ha₀⟩ := hcyc.exists_generator
  have horda₀ : orderOf a₀ = 5 := by rw [orderOf_eq_card_of_forall_mem_zpowers ha₀]; exact hH
  set a : A5 := (a₀ : A5) with ha_def
  -- Avoid rewriting the numeral `5` (it collides with the `5` in `Fin 5`, a₀'s type).
  have horda : orderOf a = 5 := by
    rw [ha_def]
    exact (orderOf_injective H.subtype (Subgroup.subtype_injective H) a₀).trans horda₀
  have ha5 : a ^ 5 = 1 := by have h := pow_orderOf_eq_one a; rwa [horda] at h
  have ha_ne1 : a ≠ 1 := by
    intro h; rw [h, orderOf_one] at horda; exact absurd horda (by norm_num)
  obtain ⟨z, hz_def⟩ : ∃ z : ℂ, z = σ.character a₀ := ⟨σ.character a₀, rfl⟩
  have ha₀5 : a₀ ^ 5 = 1 := by have h := pow_orderOf_eq_one a₀; rwa [horda₀] at h
  have hz5 : z ^ 5 = 1 := by
    have h := map_pow χ a₀ 5
    rw [ha₀5, map_one, hχa, ← hz_def] at h; exact h.symm
  have hchar_pow : ∀ k : ℕ, σ.character (a₀ ^ k) = z ^ k := by
    intro k
    have h := map_pow χ a₀ k
    rw [hχa, hχa, ← hz_def] at h; exact h
  -- Enumerate `H = {1, a, a², a³, a⁴}`.
  have hgen_top : Subgroup.zpowers a₀ = ⊤ := by rw [eq_top_iff]; intro x _; exact ha₀ x
  have hHzp : Subgroup.zpowers a = H := by
    have h1 : (Subgroup.zpowers a₀).map H.subtype = Subgroup.zpowers a :=
      MonoidHom.map_zpowers H.subtype a₀
    rw [hgen_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    exact h1.symm
  have ha2coe : a ^ 2 = ((a₀ ^ 2 : ↥H) : A5) := by rw [ha_def]; push_cast; ring
  have ha3coe : a ^ 3 = ((a₀ ^ 3 : ↥H) : A5) := by rw [ha_def]; push_cast; ring
  have ha4coe : a ^ 4 = ((a₀ ^ 4 : ↥H) : A5) := by rw [ha_def]; push_cast; ring
  have henum : ∀ y : A5, y ∈ H → y = 1 ∨ y = a ∨ y = a ^ 2 ∨ y = a ^ 3 ∨ y = a ^ 4 := by
    intro y hy
    rw [← hHzp, Etingof.Problem4_12_5.mem_zpowers_range a 5 horda] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨k, hk, hky⟩ := hy
    interval_cases k
    · left; rw [← hky]; simp
    · right; left; rw [← hky, pow_one]
    · right; right; left; rw [← hky]
    · right; right; right; left; rw [← hky]
    · right; right; right; right; rw [← hky]
  have ha_mem : a ∈ H := by rw [ha_def]; exact SetLike.coe_mem a₀
  have ha2_mem : a ^ 2 ∈ H := by rw [ha2coe]; exact SetLike.coe_mem _
  have ha3_mem : a ^ 3 ∈ H := by rw [ha3coe]; exact SetLike.coe_mem _
  have ha4_mem : a ^ 4 ∈ H := by rw [ha4coe]; exact SetLike.coe_mem _
  -- Distinctness of the powers `a⁰,…,a⁴`.
  have hne : ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → a ^ i ≠ a ^ j := by
    intro i j hi hj hij h
    wlog hlt : i < j generalizing i j
    · exact this j i hj hi (Ne.symm hij) h.symm (by omega)
    have hd : a ^ (j - i) = 1 := by
      have hcancel : a ^ i * a ^ (j - i) = a ^ i * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' (le_of_lt hlt)]; exact h.symm
      exact mul_left_cancel hcancel
    have hle := orderOf_le_of_pow_eq_one (n := j - i) (by omega) hd
    rw [horda] at hle; omega
  have e01 : (1 : A5) ≠ a := by
    have := hne 0 1 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero, pow_one] at this
  have e02 : (1 : A5) ≠ a ^ 2 := by
    have := hne 0 2 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
  have e03 : (1 : A5) ≠ a ^ 3 := by
    have := hne 0 3 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
  have e04 : (1 : A5) ≠ a ^ 4 := by
    have := hne 0 4 (by norm_num) (by norm_num) (by norm_num); rwa [pow_zero] at this
  have e12 : a ≠ a ^ 2 := by
    have := hne 1 2 (by norm_num) (by norm_num) (by norm_num); rwa [pow_one] at this
  have e13 : a ≠ a ^ 3 := by
    have := hne 1 3 (by norm_num) (by norm_num) (by norm_num); rwa [pow_one] at this
  have e14 : a ≠ a ^ 4 := by
    have := hne 1 4 (by norm_num) (by norm_num) (by norm_num); rwa [pow_one] at this
  have e23 : a ^ 2 ≠ a ^ 3 := hne 2 3 (by norm_num) (by norm_num) (by norm_num)
  have e24 : a ^ 2 ≠ a ^ 4 := hne 2 4 (by norm_num) (by norm_num) (by norm_num)
  have e34 : a ^ 3 ≠ a ^ 4 := hne 3 4 (by norm_num) (by norm_num) (by norm_num)
  -- `z ≠ 1` and `z + z² + z³ + z⁴ = -1`.
  have hz_ne : z ≠ 1 := by
    obtain ⟨h0, hh0⟩ := hntriv
    rcases henum (h0 : A5) (SetLike.coe_mem h0) with he | he | he | he | he
    · exact absurd (by rw [show h0 = 1 from Subtype.ext he]; exact hone) hh0
    · intro hz1; apply hh0
      rw [show h0 = a₀ from Subtype.ext (he.trans ha_def), ← hz_def]; exact hz1
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 2 from Subtype.ext (he.trans ha2coe), hchar_pow 2, hz1]; ring
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 3 from Subtype.ext (he.trans ha3coe), hchar_pow 3, hz1]; ring
    · intro hz1; apply hh0
      rw [show h0 = a₀ ^ 4 from Subtype.ext (he.trans ha4coe), hchar_pow 4, hz1]; ring
  have hz_sum4 : z + z ^ 2 + z ^ 3 + z ^ 4 = -1 := by
    have hfac : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by linear_combination hz5
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linear_combination h : z = 1) hz_ne
    · linear_combination h
  have hcardℂ : (Fintype.card ↥H : ℂ) = 5 := by rw [← Nat.card_eq_fintype_card, hH]; norm_num
  -- The `hterm` decomposition, shared by both class cases.
  have hterm : ∀ (j : Fin 5) (x : A5),
      (if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨x * classRepA5 j * x⁻¹, h⟩ else 0)
        = (1 : ℂ) * (if x * classRepA5 j * x⁻¹ = 1 then 1 else 0)
          + z * (if x * classRepA5 j * x⁻¹ = a then 1 else 0)
          + z ^ 2 * (if x * classRepA5 j * x⁻¹ = a ^ 2 then 1 else 0)
          + z ^ 3 * (if x * classRepA5 j * x⁻¹ = a ^ 3 then 1 else 0)
          + z ^ 4 * (if x * classRepA5 j * x⁻¹ = a ^ 4 then 1 else 0) := by
    intro j x
    set y := x * classRepA5 j * x⁻¹ with hy
    by_cases hmem : y ∈ H
    · rcases henum y hmem with h1 | hA | hA2 | hA3 | hA4
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = 1 from Subtype.ext h1, hone,
          if_pos h1, if_neg (by rw [h1]; exact e01), if_neg (by rw [h1]; exact e02),
          if_neg (by rw [h1]; exact e03), if_neg (by rw [h1]; exact e04)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ from Subtype.ext (hA.trans ha_def), ← hz_def,
          if_neg (by rw [hA]; exact e01.symm), if_pos hA, if_neg (by rw [hA]; exact e12),
          if_neg (by rw [hA]; exact e13), if_neg (by rw [hA]; exact e14)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 2 from Subtype.ext (hA2.trans ha2coe),
          hchar_pow 2, if_neg (by rw [hA2]; exact e02.symm), if_neg (by rw [hA2]; exact e12.symm),
          if_pos hA2, if_neg (by rw [hA2]; exact e23), if_neg (by rw [hA2]; exact e24)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 3 from Subtype.ext (hA3.trans ha3coe),
          hchar_pow 3, if_neg (by rw [hA3]; exact e03.symm), if_neg (by rw [hA3]; exact e13.symm),
          if_neg (by rw [hA3]; exact e23.symm), if_pos hA3, if_neg (by rw [hA3]; exact e34)]
        ring
      · rw [dif_pos hmem, show (⟨y, hmem⟩ : ↥H) = a₀ ^ 4 from Subtype.ext (hA4.trans ha4coe),
          hchar_pow 4, if_neg (by rw [hA4]; exact e04.symm), if_neg (by rw [hA4]; exact e14.symm),
          if_neg (by rw [hA4]; exact e24.symm), if_neg (by rw [hA4]; exact e34.symm), if_pos hA4]
        ring
    · rw [dif_neg hmem,
        if_neg (fun h => hmem (by rw [h]; exact H.one_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha2_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha3_mem)),
        if_neg (fun h => hmem (by rw [h]; exact ha4_mem))]
      ring
  -- Reduce the induced character on class reps to conjugator counts, shared form.
  have hraw : ∀ j : Fin 5, (ind σ).character (classRepA5 j)
      = (5 : ℂ)⁻¹ * ((1 : ℂ) * ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = 1)).card : ℂ)
          + z * ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = a)).card : ℂ)
          + z ^ 2 * ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = a ^ 2)).card : ℂ)
          + z ^ 3 * ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = a ^ 3)).card : ℂ)
          + z ^ 4 * ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ = a ^ 4)).card : ℂ)) := by
    intro j
    rw [ind_character_eq, hcardℂ, Finset.sum_congr rfl (fun x _ => hterm j x),
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_boole, Finset.sum_boole]
  -- Split on the class of the generator.
  rcases classIdxA5_pow5 a ha5 ha_ne1 with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · -- `a ∈ 5a`: `A = z + z⁴`, `B = z² + z³`.
    refine ⟨z + z ^ 4, z ^ 2 + z ^ 3, by linear_combination hz_sum4,
      by linear_combination (z ^ 3 + 2) * hz5 + hz_sum4, ?_⟩
    intro j
    have hca : ∃ c : A5, c * classRepA5 3 * c⁻¹ = a := by
      obtain ⟨c, hc⟩ := classIdxA5_spec a; rw [h1] at hc; exact ⟨c, hc⟩
    have hca2 : ∃ c : A5, c * classRepA5 4 * c⁻¹ = a ^ 2 := by
      obtain ⟨c, hc⟩ := classIdxA5_spec (a ^ 2); rw [h2] at hc; exact ⟨c, hc⟩
    have hca3 : ∃ c : A5, c * classRepA5 4 * c⁻¹ = a ^ 3 := by
      obtain ⟨c, hc⟩ := classIdxA5_spec (a ^ 3); rw [h3] at hc; exact ⟨c, hc⟩
    have hca4 : ∃ c : A5, c * classRepA5 3 * c⁻¹ = a ^ 4 := by
      obtain ⟨c, hc⟩ := classIdxA5_spec (a ^ 4); rw [h4] at hc; exact ⟨c, hc⟩
    rw [hraw j, oneCount, conjCount_shift (classRepA5 j) (classRepA5 3) a hca,
      conjCount_shift (classRepA5 j) (classRepA5 4) (a ^ 2) hca2,
      conjCount_shift (classRepA5 j) (classRepA5 4) (a ^ 3) hca3,
      conjCount_shift (classRepA5 j) (classRepA5 3) (a ^ 4) hca4, cr3Count, cr4Count]
    fin_cases j <;> norm_num <;> ring
  · -- `a ∈ 5b`: `A = z² + z³`, `B = z + z⁴`.
    refine ⟨z ^ 2 + z ^ 3, z + z ^ 4, by linear_combination hz_sum4,
      by linear_combination (z + 2) * hz5 + hz_sum4, ?_⟩
    intro j
    have hca : ∃ c : A5, c * classRepA5 4 * c⁻¹ = a := by
      obtain ⟨c, hc⟩ := classIdxA5_spec a; rw [h1] at hc; exact ⟨c, hc⟩
    have hca2 : ∃ c : A5, c * classRepA5 3 * c⁻¹ = a ^ 2 := by
      obtain ⟨c, hc⟩ := classIdxA5_spec (a ^ 2); rw [h2] at hc; exact ⟨c, hc⟩
    have hca3 : ∃ c : A5, c * classRepA5 3 * c⁻¹ = a ^ 3 := by
      obtain ⟨c, hc⟩ := classIdxA5_spec (a ^ 3); rw [h3] at hc; exact ⟨c, hc⟩
    have hca4 : ∃ c : A5, c * classRepA5 4 * c⁻¹ = a ^ 4 := by
      obtain ⟨c, hc⟩ := classIdxA5_spec (a ^ 4); rw [h4] at hc; exact ⟨c, hc⟩
    rw [hraw j, oneCount, conjCount_shift (classRepA5 j) (classRepA5 4) a hca,
      conjCount_shift (classRepA5 j) (classRepA5 3) (a ^ 2) hca2,
      conjCount_shift (classRepA5 j) (classRepA5 3) (a ^ 3) hca3,
      conjCount_shift (classRepA5 j) (classRepA5 4) (a ^ 4) hca4, cr3Count, cr4Count]
    fin_cases j <;> norm_num <;> ring

/-- Arbitrary-`g` nontrivial-character values, from a class-rep value vector. -/
lemma indZ5_nontriv_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] {A B : ℂ}
    (hval : ∀ j, (ind σ).character (classRepA5 j) = ![12, 0, 0, A, B] j) (g : A5) :
    (ind σ).character g = ![12, 0, 0, A, B] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact hval (classIdxA5 g)

/-- Arbitrary-`g` target character values for `3 ⊕ 4 ⊕ 5`, via the class-function property. -/
lemma indZ5_target1_char_all (g : A5) :
    (repC3plus ⊞ repC4 ⊞ repC5).character g
      = ![12, 0, 0, (-1 + (Real.sqrt 5 : ℂ)) / 2, (-1 - (Real.sqrt 5 : ℂ)) / 2] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ5_target1_value (classIdxA5 g)

/-- Arbitrary-`g` target character values for `3' ⊕ 4 ⊕ 5`, via the class-function property. -/
lemma indZ5_target2_char_all (g : A5) :
    (repC3minus ⊞ repC4 ⊞ repC5).character g
      = ![12, 0, 0, (-1 - (Real.sqrt 5 : ℂ)) / 2, (-1 + (Real.sqrt 5 : ℂ)) / 2] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indZ5_target2_value (classIdxA5 g)

/-- **(c) nontrivial character.** For any of the four nontrivial characters `ζ^k` (`k ≠ 0`),
`Ind_{ℤ₅}^{A₅} ζ^k` is `3 ⊕ 4 ⊕ 5` or `3' ⊕ 4 ⊕ 5` (dimension `12`); the pair `{ζ, ζ⁴}` picks
one `3`-dimensional and `{ζ², ζ³}` the other. -/
theorem indZ5_nontriv (H : Subgroup A5) (hH : Nat.card H = 5)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅ repC3plus ⊞ repC4 ⊞ repC5) ∨
      Nonempty (ind σ ≅ repC3minus ⊞ repC4 ⊞ repC5) := by
  classical
  obtain ⟨A, B, hAB, hAq, hval⟩ := indZ5_nontriv_value H hH σ hntriv
  -- `A` is a root of `t² + t − 1`, hence `(−1 ± √5)/2`.
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = 5 := sqrt5_sq
  have hfac : (A - (-1 + (Real.sqrt 5 : ℂ)) / 2) * (A - (-1 - (Real.sqrt 5 : ℂ)) / 2) = 0 := by
    linear_combination hAq - (1 / 4 : ℂ) * hs
  rcases mul_eq_zero.mp hfac with hA | hA
  · -- `A = (−1+√5)/2`, `B = (−1−√5)/2`: matches `3 ⊕ 4 ⊕ 5`.
    left
    apply Etingof.charEq_iso
    funext g
    rw [indZ5_nontriv_char_all H hH σ hval g, indZ5_target1_char_all g,
      show A = (-1 + (Real.sqrt 5 : ℂ)) / 2 by linear_combination hA,
      show B = (-1 - (Real.sqrt 5 : ℂ)) / 2 by linear_combination hAB - hA]
  · -- `A = (−1−√5)/2`, `B = (−1+√5)/2`: matches `3' ⊕ 4 ⊕ 5`.
    right
    apply Etingof.charEq_iso
    funext g
    rw [indZ5_nontriv_char_all H hH σ hval g, indZ5_target2_char_all g,
      show A = (-1 - (Real.sqrt 5 : ℂ)) / 2 by linear_combination hA,
      show B = (-1 + (Real.sqrt 5 : ℂ)) / 2 by linear_combination hAB - hA]

/-! ## (d) Induction from `A₄`

The order-`12` subgroups of `A₅` are the (conjugate) point stabilizers `A₄` — not Sylow
subgroups — so the cyclic-case route (`exists_conj_H5` via Sylow's theorem) does not apply.
We fix the concrete `A₄` as the stabilizer of `0` under the natural action `natHom` and reduce
an arbitrary order-`12` subgroup to it. The induced-character counts then reduce, exactly as in
the cyclic cases, to `decide`-evaluable computations over the `60` elements of `A₅`. -/

/-- The natural action of `A₅` on `Fin 5`, as a `MonoidHom`. -/
def natHom : A5 →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype

/-- The concrete order-`12` subgroup `A₄ ≤ A₅`: the point stabilizer of `0`. -/
abbrev A4std : Subgroup A5 := Etingof.Problem4_12_5.stabSub natHom 0

/-- Membership in the concrete `A₄` is fixing the point `0`. -/
lemma mem_A4std (a : A5) : a ∈ A4std ↔ natHom a 0 = 0 := Iff.rfl

instance : DecidablePred (· ∈ A4std) := fun a => decidable_of_iff _ (mem_A4std a).symm

set_option maxRecDepth 12000 in
-- `decide` counts the `12` even permutations of `Fin 5` fixing `0`.
set_option maxHeartbeats 4000000 in
/-- The concrete `A₄` has order `12`. -/
lemma card_A4std : Nat.card A4std = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/-- **Order-`12` conjugacy reduction.** Every order-`12` subgroup `H ≤ A₅` is conjugate to the
concrete point-stabilizer `A₄`: there is `d` with `y ∈ H ↔ d y d⁻¹ ∈ A4std`.

The order-`12` subgroups of `A₅` are not Sylow subgroups, so this is proved via the Sylow-`2`
normalizer: a Sylow-`2` subgroup `P` of `H` (order `4`) is a Sylow-`2` of `A₅`; it is normal in
`H` (`n₂(H)=1`, ruling out `n₃(H)=1` since `|N_{A₅}(order-3)| ∈ {6,15}` is not a multiple of
`12`), so `H = N_{A₅}(P)`; and `P` is conjugate to the Sylow-`2` of `A4std` (Sylow II), whence
`H = c · A4std · c⁻¹`. -/
lemma exists_conj_H12 (H : Subgroup A5) (hH : Nat.card H = 12) :
    ∃ d : A5, ∀ y : A5, y ∈ H ↔ d * y * d⁻¹ ∈ A4std := by
  sorry

/-- The count of conjugators landing in an order-`12` `H` matches that for the concrete `A₄`. -/
lemma countH_eq12 (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12) (g : A5) :
    (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ H)).card
      = (univ.filter (fun x : A5 => x * g * x⁻¹ ∈ A4std)).card := by
  obtain ⟨d, hd⟩ := exists_conj_H12 H hH
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

set_option maxRecDepth 12000 in
-- `decide` evaluates the twisted membership (fixing `0`) over all `60` elements of `A₅`.
set_option maxHeartbeats 4000000 in
/-- **Twisted counts in the concrete `A₄`.** `#{x : x·(classRepA5 j)·x⁻¹ ∈ A₄}` on the five
class reps is `(60, 24, 12, 0, 0)` — that is `12 ·` the fixed-point count `(5,2,1,0,0)`. -/
lemma twisted_A4std (j : Fin 5) :
    (univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ A4std)).card
      = ![60, 24, 12, 0, 0] j := by
  have h : (univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ A4std))
      = (univ.filter (fun x : A5 => natHom (x * classRepA5 j * x⁻¹) 0 = 0)) := by
    apply Finset.filter_congr; intro x _; simp only [mem_A4std]
  rw [h]; fin_cases j <;> decide

/-- **Trivial character, class-rep values.** For an order-`12` `H` and the trivial character `σ`,
`(ind σ).character` on the five class reps is `(5, 2, 1, 0, 0)`. -/
lemma indA4_triv_value (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (j : Fin 5) :
    (ind σ).character (classRepA5 j) = ![5, 2, 1, 0, 0] j := by
  rw [ind_character_eq]
  have hcard : (Fintype.card ↥H : ℂ) = 12 := by
    rw [← Nat.card_eq_fintype_card, hH]; norm_num
  have hsum : (∑ x : A5, if h : x * classRepA5 j * x⁻¹ ∈ H then σ.character ⟨_, h⟩ else 0)
      = ((univ.filter (fun x : A5 => x * classRepA5 j * x⁻¹ ∈ H)).card : ℂ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x * classRepA5 j * x⁻¹ ∈ H
    · rw [dif_pos hx, if_pos hx, htriv]
    · rw [dif_neg hx, if_neg hx]
  rw [hsum, countH_eq12 H hH, twisted_A4std, hcard]
  fin_cases j <;> norm_num

/-- Arbitrary-`g` trivial-character values, via the class-function property. -/
lemma indA4_triv_char_all (H : Subgroup A5) [DecidablePred (· ∈ H)] (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) (htriv : ∀ h : ↥H, σ.character h = 1) (g : A5) :
    (ind σ).character g = ![5, 2, 1, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indA4_triv_value H hH σ htriv (classIdxA5 g)

/-- **Target character, class-rep values** for `1 ⊕ 4`: `(5, 2, 1, 0, 0)`. -/
lemma indA4_triv_target_value (j : Fin 5) :
    (repTriv ⊞ repC4).character (classRepA5 j) = ![5, 2, 1, 0, 0] j := by
  simp only [character_biprod, repTriv_character, repC4_character]
  fin_cases j <;>
    norm_num [tblA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- Arbitrary-`g` target character values, via the class-function property. -/
lemma indA4_triv_target_char_all (g : A5) :
    (repTriv ⊞ repC4).character g = ![5, 2, 1, 0, 0] (classIdxA5 g) := by
  obtain ⟨c, hc⟩ := classIdxA5_spec g
  conv_lhs => rw [← hc]
  rw [FDRep.char_conj]
  exact indA4_triv_target_value (classIdxA5 g)

/-- **(d) trivial character.** `Ind_{A₄}^{A₅} 1 ≅ 1 ⊕ 4` (dimension `5`), the permutation
representation on the `5` cosets. -/
theorem indA4_triv (H : Subgroup A5) (hH : Nat.card H = 12)
    (σ : FDRep ℂ ↥H) [Simple σ] (hdim : Module.finrank ℂ σ = 1)
    (htriv : ∀ h : ↥H, σ.character h = 1) :
    Nonempty (ind σ ≅ repTriv ⊞ repC4) := by
  classical
  apply Etingof.charEq_iso
  funext g
  rw [indA4_triv_char_all H hH σ htriv g, indA4_triv_target_char_all g]

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
