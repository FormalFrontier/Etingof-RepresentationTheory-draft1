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

/-- **(a) sign character.** `Ind_{ℤ₂}^{A₅} 1₋ ≅ 3² ⊕ 3'² ⊕ 4² ⊕ 5²` (dimension `30`).
Multiplicities `(χ_W(1a) − χ_W(2a))/2`. -/
theorem indZ2_sign (H : Subgroup A5) (hH : Nat.card H = 2)
    (σ : FDRep ℂ ↥H) [Simple σ] (hntriv : ∃ h : ↥H, σ.character h ≠ 1) :
    Nonempty (ind σ ≅
      repC3plus ⊞ repC3plus ⊞ repC3minus ⊞ repC3minus ⊞ repC4 ⊞ repC4 ⊞ repC5 ⊞ repC5) := by
  sorry

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
