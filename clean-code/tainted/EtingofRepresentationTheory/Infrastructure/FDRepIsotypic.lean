import Mathlib
import EtingofRepresentationTheory.Chapter4.Corollary4_2_4
import EtingofRepresentationTheory.Chapter4.Theorem4_5_1

/-!
# Isotypic decomposition against a complete family of irreducibles

Let `G` be a finite group, `k` an algebraically closed field of characteristic zero, and
`T : ι → FDRep k G` a *complete family* of irreducibles: the `T i` are simple, pairwise
non-isomorphic, and every simple object of `FDRep k G` is isomorphic to some `T i`. This file
shows that every finite-dimensional representation `V` is isomorphic to the direct sum of
`finrank k (T i ⟶ V)` copies of `T i`.

## Main results

* `Etingof.FDRep.finrank_hom_biproduct` : `dim Hom(S, ⨁ⱼ Uⱼ) = Σⱼ dim Hom(S, Uⱼ)`.
* `Etingof.FDRep.character_biprod` : characters are additive over binary biproducts.
* `Etingof.FDRep.exists_character_eq_sum` : the character of any `V` is a natural-number
  combination of the characters of a complete family.
* `Etingof.FDRep.multiplicity T V i = finrank k (T i ⟶ V)` and `Etingof.FDRep.isotypicSum T n`,
  the direct sum `⨁ᵢ (T i)^(n i)` realised as the biproduct over `Σ i, Fin (n i)`.
* `Etingof.FDRep.nonempty_iso_isotypicSum` : `V ≅ ⨁ᵢ (T i)^(dim Hom(T i, V))`.

## Method

The multiplicities are read off from characters rather than by peeling summands one at a time,
which avoids reindexing biproducts. Writing `χ_V = Σᵢ nᵢ χ_{Tᵢ}` (obtained by induction on
`dim V` from `Etingof.Semisimple.exists_simple_biprod`) and pairing with `χ_S` for an arbitrary
`S`, Theorem 4.5.1(i) turns the character identity into the Hom-dimension identity
`dim Hom(S, V) = Σᵢ nᵢ · dim Hom(S, Tᵢ)`. The right-hand side is exactly
`dim Hom(S, isotypicSum T n)`, so `Etingof.Semisimple.iso_of_hom_finrank_eq` produces the
isomorphism. Pairing with `χ_{Tᵢ}` instead identifies `nᵢ` with `dim Hom(Tᵢ, V)`.
-/

open CategoryTheory CategoryTheory.Limits Module

namespace Etingof.FDRep

variable {k : Type} [Field k] {G : Type} [Group G] [Fintype G]

-- `FDRep k G` is abelian, hence has finite biproducts; this is not a global instance in Mathlib.
attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-! ## Underlying linear algebra of biproducts -/

omit [Fintype G] in
/-- Underlying-linear-map intertwining for a morphism of `FDRep`: the underlying `k`-linear map
of `f : A ⟶ B` commutes with the `G`-actions. -/
lemma hom_comm {A B : FDRep k G} (f : A ⟶ B) (g : G) (a : (A : Type)) :
    f.hom.hom.hom (A.ρ g a) = B.ρ g (f.hom.hom.hom a) := by
  have h := f.comm g
  apply_fun (fun m : A.V ⟶ B.V => m.hom.hom) at h
  have h2 := congrFun (congrArg (fun (m : (A.V.obj) →ₗ[k] (B.V.obj)) => (m : _ → _)) h) a
  simpa using h2

/-- The `k`-linear equivalence underlying a binary biproduct in `FDRep k G`, sending `v` to its
two projections. -/
noncomputable def biprodProdEquiv (X Y : FDRep k G) :
    (X ⊞ Y : FDRep k G) ≃ₗ[k] Prod (X : Type) (Y : Type) where
  toFun v := ((biprod.fst : X ⊞ Y ⟶ X).hom.hom.hom v,
              (biprod.snd : X ⊞ Y ⟶ Y).hom.hom.hom v)
  map_add' a b := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' r a := Prod.ext (map_smul _ _ _) (map_smul _ _ _)
  invFun p := (biprod.inl : X ⟶ X ⊞ Y).hom.hom.hom p.1 +
              (biprod.inr : Y ⟶ X ⊞ Y).hom.hom.hom p.2
  left_inv v := by
    change ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
      (X ⊞ Y : FDRep k G) ⟶ (X ⊞ Y))).hom.hom.hom v = v
    rw [biprod.total]; rfl
  right_inv p := by
    have hzero : ∀ (A B : FDRep k G) (x : (A : Type)), (0 : A ⟶ B).hom.hom.hom x = 0 := by
      intro A B x
      change (0 : A.V.obj ⟶ B.V.obj).hom x = 0
      simp [ModuleCat.Hom.hom]
    have hid : ∀ (A : FDRep k G) (x : (A : Type)), (𝟙 A : A ⟶ A).hom.hom.hom x = x :=
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

/-- **Character additivity over a binary biproduct**:
`(X ⊞ Y).character = X.character + Y.character`. -/
lemma character_biprod (X Y : FDRep k G) (g : G) :
    (X ⊞ Y : FDRep k G).character g = X.character g + Y.character g := by
  have hequiv : ∀ v, (biprodProdEquiv X Y) ((X ⊞ Y : FDRep k G).ρ g v)
      = LinearMap.prodMap (X.ρ g) (Y.ρ g) ((biprodProdEquiv X Y) v) := by
    intro v
    apply Prod.ext
    · exact hom_comm (biprod.fst : X ⊞ Y ⟶ X) g v
    · exact hom_comm (biprod.snd : X ⊞ Y ⟶ Y) g v
  have hconj : (biprodProdEquiv X Y).conj ((X ⊞ Y : FDRep k G).ρ g)
      = LinearMap.prodMap (X.ρ g) (Y.ρ g) := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have hv := hequiv ((biprodProdEquiv X Y).symm w)
    rw [LinearEquiv.apply_symm_apply] at hv
    simpa using hv
  calc (X ⊞ Y : FDRep k G).character g
      = LinearMap.trace k _ ((X ⊞ Y : FDRep k G).ρ g) := rfl
    _ = LinearMap.trace k _ ((biprodProdEquiv X Y).conj ((X ⊞ Y : FDRep k G).ρ g)) :=
        (LinearMap.trace_conj' _ _).symm
    _ = LinearMap.trace k _ (LinearMap.prodMap (X.ρ g) (Y.ρ g)) := by rw [hconj]
    _ = X.character g + Y.character g := LinearMap.trace_prodMap' _ _

omit [Fintype G] in
/-- The character of a zero object vanishes. -/
lemma character_of_isZero {V : FDRep k G} (hV : IsZero V) (g : G) : V.character g = 0 := by
  have hsub : Subsingleton (V : Type) := by
    have hid : (𝟙 V : V ⟶ V) = 0 := (IsZero.iff_id_eq_zero V).mp hV
    refine ⟨fun a b => ?_⟩
    have ha : (𝟙 V : V ⟶ V).hom.hom.hom a = (0 : V ⟶ V).hom.hom.hom a := by rw [hid]
    have hb : (𝟙 V : V ⟶ V).hom.hom.hom b = (0 : V ⟶ V).hom.hom.hom b := by rw [hid]
    simp only [show ∀ x : (V : Type), (0 : V ⟶ V).hom.hom.hom x = 0 from fun x => by
      change (0 : V.V.obj ⟶ V.V.obj).hom x = 0; simp [ModuleCat.Hom.hom]] at ha hb
    exact ha.trans hb.symm
  have hρ : V.ρ g = 0 := by ext v; exact Subsingleton.elim _ _
  change LinearMap.trace k _ (V.ρ g) = 0
  rw [hρ, map_zero]

/-! ## Hom spaces into a finite biproduct -/

/-- Hom into a finite biproduct decomposes, `k`-linearly, as the product of the Hom spaces. -/
noncomputable def homBiproductLinearEquiv (S : FDRep k G) {J : Type} [Fintype J] [DecidableEq J]
    (U : J → FDRep k G) :
    (S ⟶ ⨁ U) ≃ₗ[k] (∀ j, (S ⟶ U j)) where
  toFun f j := f ≫ biproduct.π U j
  map_add' f g := by funext j; simp [Preadditive.add_comp]
  map_smul' r f := by funext j; simp
  invFun φ := biproduct.lift φ
  left_inv f := by
    apply biproduct.hom_ext
    intro j
    simp
  right_inv φ := by funext j; simp

omit [Fintype G] in
/-- `dim Hom(S, ⨁ⱼ Uⱼ) = Σⱼ dim Hom(S, Uⱼ)`. -/
lemma finrank_hom_biproduct (S : FDRep k G) {J : Type} [Fintype J] [DecidableEq J]
    (U : J → FDRep k G) :
    finrank k (S ⟶ ⨁ U) = ∑ j, finrank k (S ⟶ U j) := by
  rw [(homBiproductLinearEquiv S U).finrank_eq, finrank_pi_fintype]

/-! ## Decomposition against a complete family -/

section Complete

variable [IsAlgClosed k] [CharZero k] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Every character is a natural combination of the characters of a complete family.**
If every simple object of `FDRep k G` is isomorphic to some `T i`, then for every `V` there are
multiplicities `n i` with `χ_V = Σᵢ nᵢ χ_{Tᵢ}`. -/
theorem exists_character_eq_sum (T : ι → FDRep k G)
    (hcomplete : ∀ S : FDRep k G, Simple S → ∃ i, Nonempty (S ≅ T i))
    (V : FDRep k G) :
    ∃ n : ι → ℕ, ∀ g : G, V.character g = ∑ i, (n i : k) * (T i).character g := by
  -- Strong induction on `finrank k V`.
  suffices key : ∀ (m : ℕ) (V : FDRep k G), finrank k V ≤ m →
      ∃ n : ι → ℕ, ∀ g : G, V.character g = ∑ i, (n i : k) * (T i).character g from
    key _ V le_rfl
  intro m
  induction m with
  | zero =>
    intro V hV
    refine ⟨fun _ => 0, fun g => ?_⟩
    rw [character_of_isZero
      (Etingof.Semisimple.isZero_of_finrank_zero V (Nat.eq_zero_of_le_zero hV)) g]
    simp
  | succ m ih =>
    intro V hV
    by_cases hz : IsZero V
    · exact ⟨fun _ => 0, fun g => by rw [character_of_isZero hz g]; simp⟩
    obtain ⟨S, V', hS, ⟨φ⟩⟩ := Etingof.Semisimple.exists_simple_biprod V hz
    haveI := hS
    obtain ⟨i₀, ⟨ψ⟩⟩ := hcomplete S hS
    -- `dim V' < dim V ≤ m + 1`, so the inductive hypothesis applies to `V'`.
    have hdim : finrank k V = finrank k S + finrank k V' := by
      rw [Etingof.Semisimple.finrank_iso V (S ⊞ V') φ, Etingof.Semisimple.finrank_biprod]
    have hSpos : 0 < finrank k S := Etingof.Semisimple.finrank_pos_of_simple S
    obtain ⟨n', hn'⟩ := ih V' (by omega)
    refine ⟨fun i => n' i + if i = i₀ then 1 else 0, fun g => ?_⟩
    have hV_char : V.character g = S.character g + V'.character g := by
      rw [FDRep.char_iso φ, character_biprod]
    rw [hV_char, FDRep.char_iso ψ, hn' g]
    have hsplit : ∑ i, ((n' i + if i = i₀ then 1 else 0 : ℕ) : k) * (T i).character g
        = (∑ i, (n' i : k) * (T i).character g) + (T i₀).character g := by
      push_cast
      simp only [add_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i₀ (fun i => (T i).character g)]
      simp
    rw [hsplit]
    ring

variable (T : ι → FDRep k G)

/-- The multiplicity of `T i` in `V`: the dimension of the space of intertwiners `T i → V`.
For a complete family of irreducibles this is the number of copies of `T i` in `V`
(`nonempty_iso_isotypicSum`). -/
noncomputable def multiplicity (V : FDRep k G) (i : ι) : ℕ := finrank k (T i ⟶ V)

/-- The direct sum `⨁ᵢ (T i)^(n i)`, realised as the biproduct over `Σ i, Fin (n i)`. -/
noncomputable def isotypicSum (n : ι → ℕ) : FDRep k G :=
  ⨁ (fun p : Σ i : ι, Fin (n i) => T p.1)

/-- `dim Hom(S, ⨁ᵢ (Tᵢ)^(nᵢ)) = Σᵢ nᵢ · dim Hom(S, Tᵢ)`. -/
lemma finrank_hom_isotypicSum (n : ι → ℕ) (S : FDRep k G) :
    finrank k (S ⟶ isotypicSum T n) = ∑ i, n i * finrank k (S ⟶ T i) := by
  rw [isotypicSum, finrank_hom_biproduct, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [Finset.sum_const_nat (m := finrank k (S ⟶ T i)) (fun _ _ => rfl), Finset.card_univ,
    Fintype.card_fin]

variable (hT : ∀ i, Simple (T i)) (hinj : ∀ i j, Nonempty (T i ≅ T j) → i = j)
  (hcomplete : ∀ S : FDRep k G, Simple S → ∃ i, Nonempty (S ≅ T i))

omit [Fintype G] [CharZero k] [Fintype ι] in
include hT hinj in
/-- Schur's lemma for the family: `dim Hom(Tᵢ, Tⱼ) = δᵢⱼ`. -/
lemma finrank_hom_family (i j : ι) :
    finrank k (T i ⟶ T j) = if i = j then 1 else 0 := by
  haveI := hT i
  haveI := hT j
  rw [FDRep.finrank_hom_simple_simple]
  by_cases h : i = j
  · subst h; simp
  · simp only [h, if_false, ite_eq_right_iff]
    intro hiso
    exact absurd (hinj i j hiso) h

include hcomplete in
/-- **Hom-dimension form of the isotypic decomposition.** With `nᵢ` the multiplicities of
`exists_character_eq_sum`, `dim Hom(S, V) = Σᵢ nᵢ · dim Hom(S, Tᵢ)` for every `S`. -/
theorem exists_finrank_hom_eq_sum (V : FDRep k G) :
    ∃ n : ι → ℕ, ∀ S : FDRep k G,
      finrank k (S ⟶ V) = ∑ i, n i * finrank k (S ⟶ T i) := by
  obtain ⟨n, hn⟩ := exists_character_eq_sum T hcomplete V
  haveI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨n, fun S => ?_⟩
  have hkey : ((finrank k (S ⟶ V) : ℕ) : k) = ((∑ i, n i * finrank k (S ⟶ T i) : ℕ) : k) := by
    rw [← Etingof.Theorem4_5_1_i V S]
    push_cast
    have hrhs : ∀ i : ι, ((n i : k) * (finrank k (S ⟶ T i) : k))
        = (n i : k) * (⅟(Fintype.card G : k) • ∑ g : G, (T i).character g * S.character g⁻¹) := by
      intro i
      rw [Etingof.Theorem4_5_1_i (T i) S]
    rw [Finset.sum_congr rfl (fun i _ => hrhs i)]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hn g, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact_mod_cast hkey

include hT hinj hcomplete in
/-- The multiplicities of `exists_character_eq_sum` are the Hom-space dimensions
`dim Hom(Tᵢ, V)`. -/
theorem finrank_hom_eq_sum_multiplicity (V : FDRep k G) (S : FDRep k G) :
    finrank k (S ⟶ V) = ∑ i, multiplicity T V i * finrank k (S ⟶ T i) := by
  obtain ⟨n, hn⟩ := exists_finrank_hom_eq_sum T hcomplete V
  have hmul : ∀ i, multiplicity T V i = n i := by
    intro i
    rw [multiplicity, hn (T i)]
    rw [Finset.sum_congr rfl (fun j _ => by rw [finrank_hom_family T hT hinj i j])]
    simp
  rw [Finset.sum_congr rfl (fun i _ => by rw [hmul i])]
  exact hn S

include hT hinj hcomplete in
/-- **Isotypic decomposition.** Over an algebraically closed field of characteristic zero, every
finite-dimensional representation of a finite group is the direct sum of `dim Hom(Tᵢ, V)` copies
of `Tᵢ`, for any complete family `T` of pairwise non-isomorphic irreducibles. -/
theorem nonempty_iso_isotypicSum (V : FDRep k G) :
    Nonempty (V ≅ isotypicSum T (multiplicity T V)) := by
  refine Etingof.Semisimple.iso_of_hom_finrank_eq V _ fun S => ?_
  rw [finrank_hom_isotypicSum]
  exact finrank_hom_eq_sum_multiplicity T hT hinj hcomplete V S

end Complete

end Etingof.FDRep
