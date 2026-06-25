import Mathlib

/-!
# Discussion 5.25.4: counting complementary series representations

This file gives a faithful, self-contained formalization of the count appearing in
Discussion 5.25.4 of Etingof's *Introduction to Representation Theory*: there are
`½ q (q − 1)` complementary-series representations `Y_ν = Ind_K^G ℂ_ν`.

The book argues that `Ind_K^G ℂ_{ν^q} ≅ Ind_K^G ℂ_ν` (they have the same character),
so the distinct complementary-series representations are indexed by the orbits of the
map `ν ↦ ν^q` on the character group `K^∨` of the cyclic group `K` (`|K| = q² − 1`),
restricted to those `ν` with `ν^q ≠ ν`.

The mathematical content is a **pure character-group orbit count**, entirely independent
of the GL₂ representation machinery. Modelling `K^∨ ≅ ZMod (q² − 1)` additively (with
`ν ↦ ν^q` corresponding to multiplication by `q`), we prove:

* `cs_f_involutive` — the map `f : x ↦ q · x` is an involution on `ZMod (q² − 1)`
  (since `q² ≡ 1 mod (q² − 1)` for `q ≥ 2`);
* `cs_moved_card` — exactly `q (q − 1)` characters satisfy `q · ν ≠ ν` (the remaining
  `q − 1` are fixed, because `ν^q = ν ⟺ (q + 1) ∣ ν` in the additive model);
* `cs_reps_transversal` — the involution `f` pairs the moved set into two-element orbits,
  with `cs_reps q` a transversal (one representative per orbit);
* `cs_reps_card` — hence the number of orbits, i.e. the number of complementary-series
  representations, is `q (q − 1) / 2`.
-/

namespace Etingof.ComplementarySeries

variable (q : ℕ)

/-- The map `ν ↦ ν^q` on the character group, modelled additively as multiplication by
`q` on `ZMod (q² − 1)`. -/
def cs_f (x : ZMod (q ^ 2 - 1)) : ZMod (q ^ 2 - 1) := (q : ZMod (q ^ 2 - 1)) * x

/-- The "moved" set: characters `ν` with `ν^q ≠ ν`, i.e. `q · x ≠ x`. -/
def cs_moved [NeZero (q ^ 2 - 1)] : Finset (ZMod (q ^ 2 - 1)) :=
  Finset.univ.filter (fun x => cs_f q x ≠ x)

/-- A canonical transversal for the orbits of `cs_f` on the moved set: from each
two-element orbit `{x, q·x}` we keep the element with the smaller `ZMod.val`. -/
def cs_reps [NeZero (q ^ 2 - 1)] : Finset (ZMod (q ^ 2 - 1)) :=
  (cs_moved q).filter (fun x => x.val < (cs_f q x).val)

private lemma four_le (hq : 2 ≤ q) : 4 ≤ q ^ 2 := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2

private lemma factor_eq (hq : 2 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have h1 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
  have h2 : (m + 1 - 1) * (m + 1 + 1) = m * m + 2 * m := by
    have hm : m + 1 - 1 = m := by omega
    rw [hm]; ring
  rw [h1, h2]; omega

/-- In the additive model, `ν^q = ν` (a fixed point of `cs_f`) iff `(q + 1) ∣ ν.val`. -/
lemma fixed_iff (hq : 2 ≤ q) (x : ZMod (q ^ 2 - 1)) :
    cs_f q x = x ↔ (q + 1) ∣ x.val := by
  haveI : NeZero (q ^ 2 - 1) := ⟨by have := four_le q hq; omega⟩
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := factor_eq q hq
  have hq1 : (q - 1 : ℕ) ≠ 0 := by omega
  simp only [cs_f]
  constructor
  · intro h
    have hz : ((q - 1 : ℕ) : ZMod (q ^ 2 - 1)) * x = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_mul, one_mul, sub_eq_zero]
      exact h
    rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hz
    -- hz : (q^2-1) ∣ (q-1) * x.val
    rw [← mul_dvd_mul_iff_left hq1, ← hfac]
    exact hz
  · intro h
    have hz : (q ^ 2 - 1) ∣ (q - 1) * x.val := by
      have h2 : (q - 1) * (q + 1) ∣ (q - 1) * x.val := mul_dvd_mul_left _ h
      rwa [← hfac] at h2
    have hzero : ((q - 1 : ℕ) : ZMod (q ^ 2 - 1)) * x = 0 := by
      rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact hz
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_mul, one_mul, sub_eq_zero] at hzero
    exact hzero

/-- The fixed set `{ν : ν^q = ν}` has exactly `q − 1` elements. -/
lemma fixedSet_card [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    (Finset.univ.filter (fun x : ZMod (q ^ 2 - 1) => cs_f q x = x)).card = q - 1 := by
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := factor_eq q hq
  have hlt_k : ∀ k, k < q - 1 → (q + 1) * k < q ^ 2 - 1 := by
    intro k hk
    rw [hfac, mul_comm (q - 1) (q + 1)]
    gcongr
  rw [show q - 1 = (Finset.range (q - 1)).card from (Finset.card_range _).symm]
  apply Finset.card_nbij' (fun x => x.val / (q + 1))
    (fun k => (((q + 1) * k : ℕ) : ZMod (q ^ 2 - 1)))
  · -- MapsTo: x.val / (q+1) ∈ range (q-1)
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    rw [Finset.mem_coe, Finset.mem_range]
    have hdvd : (q + 1) ∣ x.val := (fixed_iff q hq x).mp hx.2
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < q + 1), ← hfac]
    exact ZMod.val_lt x
  · -- MapsTo (other direction): ((q+1)*k cast) ∈ fixed set
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [fixed_iff q hq, ZMod.val_natCast_of_lt (hlt_k k hk)]
    exact dvd_mul_right (q + 1) k
  · -- left_inv: j (i x) = x
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    have hdvd : (q + 1) ∣ x.val := (fixed_iff q hq x).mp hx.2
    change (((q + 1) * (x.val / (q + 1)) : ℕ) : ZMod (q ^ 2 - 1)) = x
    rw [Nat.mul_div_cancel' hdvd]
    exact ZMod.natCast_zmod_val x
  · -- right_inv: i (j k) = k
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range] at hk
    change ((((q + 1) * k : ℕ) : ZMod (q ^ 2 - 1)).val) / (q + 1) = k
    rw [ZMod.val_natCast_of_lt (hlt_k k hk)]
    exact Nat.mul_div_cancel_left k (by omega)

/-- Membership in the moved set unfolds to `ν^q ≠ ν`. -/
lemma mem_moved [NeZero (q ^ 2 - 1)] (x : ZMod (q ^ 2 - 1)) :
    x ∈ cs_moved q ↔ cs_f q x ≠ x := by
  simp only [cs_moved, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The moved set `{ν : ν^q ≠ ν}` has exactly `q (q − 1)` elements. -/
theorem cs_moved_card [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) : (cs_moved q).card = q * (q - 1) := by
  classical
  set F := Finset.univ.filter (fun x : ZMod (q ^ 2 - 1) => cs_f q x = x) with hF
  have hdisj : Disjoint (cs_moved q) F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [mem_moved] at ha
    rw [hF, Finset.mem_filter] at haF
    exact ha haF.2
  have hunion : cs_moved q ∪ F = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    rw [Finset.mem_union, mem_moved, hF, Finset.mem_filter]
    by_cases h : cs_f q a = a
    · exact Or.inr ⟨Finset.mem_univ _, h⟩
    · exact Or.inl h
  have hcard : (cs_moved q).card + F.card = q ^ 2 - 1 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, ZMod.card]
  have hFcard : F.card = q - 1 := by rw [hF]; exact fixedSet_card q hq
  have halg : q ^ 2 - 1 - (q - 1) = q * (q - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
    have h2 : (m + 1) * m = m * m + m := by ring
    rw [h1, h2]; omega
  omega

/-- `cs_f` is an involution: applying `ν ↦ ν^q` twice returns `ν` (since `q² ≡ 1`). -/
lemma cs_f_involutive (hq : 2 ≤ q) (x : ZMod (q ^ 2 - 1)) : cs_f q (cs_f q x) = x := by
  haveI : NeZero (q ^ 2 - 1) := ⟨by have := four_le q hq; omega⟩
  have hsq : (q : ZMod (q ^ 2 - 1)) ^ 2 = 1 := by
    have e1 : ((q ^ 2 : ℕ) : ZMod (q ^ 2 - 1)) = (q : ZMod (q ^ 2 - 1)) ^ 2 := by push_cast; ring
    have e2 : (q ^ 2 : ℕ) = (q ^ 2 - 1) + 1 := by have := four_le q hq; omega
    rw [← e1, e2, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add]
  simp only [cs_f]
  rw [← mul_assoc, ← pow_two, hsq, one_mul]

/-- The transversal `cs_reps` genuinely picks one representative from each two-element
orbit: the moved set is the disjoint union of `cs_reps` and its image under `cs_f`, and
the image has the same cardinality. This exhibits `cs_reps` as a set of orbit
representatives. -/
theorem cs_reps_transversal [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    Disjoint (cs_reps q) ((cs_reps q).image (cs_f q))
      ∧ (cs_reps q) ∪ (cs_reps q).image (cs_f q) = cs_moved q
      ∧ ((cs_reps q).image (cs_f q)).card = (cs_reps q).card := by
  classical
  have hinv : Function.Involutive (cs_f q) := cs_f_involutive q hq
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_image] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    simp only [cs_reps, Finset.mem_filter] at ha hx
    obtain ⟨_, ha2⟩ := ha
    obtain ⟨_, hx2⟩ := hx
    rw [cs_f_involutive q hq] at ha2
    omega
  · -- union = moved
    apply Finset.Subset.antisymm
    · intro a ha
      rw [Finset.mem_union] at ha
      rcases ha with ha | ha
      · simp only [cs_reps, Finset.mem_filter] at ha; exact ha.1
      · rw [Finset.mem_image] at ha
        obtain ⟨x, hx, rfl⟩ := ha
        simp only [cs_reps, Finset.mem_filter] at hx
        have hxne : cs_f q x ≠ x := (mem_moved q x).mp hx.1
        have hne2 : cs_f q (cs_f q x) ≠ cs_f q x := by
          rw [cs_f_involutive q hq]; exact Ne.symm hxne
        exact (mem_moved q (cs_f q x)).mpr hne2
    · intro a ha
      rw [Finset.mem_union]
      by_cases hlt : a.val < (cs_f q a).val
      · left; simp only [cs_reps, Finset.mem_filter]; exact ⟨ha, hlt⟩
      · right
        rw [Finset.mem_image]
        refine ⟨cs_f q a, ?_, cs_f_involutive q hq a⟩
        simp only [cs_reps, Finset.mem_filter]
        have hane : cs_f q a ≠ a := (mem_moved q a).mp ha
        have hmem : cs_f q a ∈ cs_moved q := by
          have hne2 : cs_f q (cs_f q a) ≠ cs_f q a := by
            rw [cs_f_involutive q hq]; exact Ne.symm hane
          exact (mem_moved q (cs_f q a)).mpr hne2
        refine ⟨hmem, ?_⟩
        rw [cs_f_involutive q hq]
        have hvalne : (cs_f q a).val ≠ a.val := fun h => hane (ZMod.val_injective _ h)
        omega
  · -- image card = reps card
    exact Finset.card_image_of_injective _ hinv.injective

/-- **The count.** The number of complementary-series representations `Y_ν` is
`½ q (q − 1)`: this is the number of orbits of `ν ↦ ν^q` on the `q (q − 1)` characters
with `ν^q ≠ ν`, each orbit having two elements. -/
theorem cs_reps_card [NeZero (q ^ 2 - 1)] (hq : 2 ≤ q) :
    (cs_reps q).card = q * (q - 1) / 2 := by
  obtain ⟨hdisj, hunion, hcard⟩ := cs_reps_transversal q hq
  have h2 : (cs_moved q).card = (cs_reps q).card + (cs_reps q).card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hcard]
  have hmc : (cs_moved q).card = q * (q - 1) := cs_moved_card q hq
  omega

end Etingof.ComplementarySeries
