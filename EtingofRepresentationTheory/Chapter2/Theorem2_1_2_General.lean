import EtingofRepresentationTheory.Chapter2.Theorem2_1_2

/-!
# Theorem 2.1.2 for arbitrary finite quivers

`Etingof.Theorem_2_1_2` classifies the quivers of finite representation type under three
standing restrictions: every arrow type is a `Subsingleton`, the quiver has no loops, and no
edge is oriented in both directions (the last two are packaged as
`IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n)`). The book's Definition 2.8.1
places no such restriction on a quiver: loops and parallel arrows are allowed.

This file removes the restrictions. The excluded configurations are handled by *proved*
negative branches: a connected quiver carrying a loop, a pair of parallel arrows, or a pair
of opposite arrows has infinite representation type. The remaining case is exactly the
hypothesis of `Theorem_2_1_2`.

## The counterexample families

All three negative branches use the same one-dimensional family. Fix a set `S` of vertices
and a scalar `c a b e` for each arrow. `suppRep S c` puts a one-dimensional space at every
vertex of `S`, the zero space elsewhere, and lets the arrow `e` act by `c a b e` through the
canonical identifications. Concretely:

* a loop at `v` gives the family `S = {v}`, `c ≡ lam`, i.e. `(k, lam)`, and
  `(k, lam) ≅ (k, mu)` forces `lam = mu`;
* two distinct arrows joining `v ≠ w` give the Kronecker family `S = {v, w}` with the first
  arrow acting by `1` and the second by `lam`; again `lam` is an isomorphism invariant.

Since an algebraically closed field is infinite, either family contains infinitely many
pairwise non-isomorphic indecomposables, contradicting finite representation type.

## Main results

* `Etingof.not_hasFiniteRepresentationType_of_loop`
* `Etingof.not_hasFiniteRepresentationType_of_two_arrows`
* `Etingof.Theorem_2_1_2_general` : the classification for an arbitrary connected quiver
* `Etingof.Theorem_2_1_2_general_orientation` : the same, phrased with `IsOrientationOf`
-/

namespace Etingof

open Etingof.QuiverRepresentation

/-! ## Isomorphism of quiver representations is an equivalence relation -/

section EquivGroupoid

variable {k Q : Type*} [CommSemiring k] [Quiver Q] {ρ₁ ρ₂ ρ₃ : QuiverRepresentation k Q}

/-- The inverse of an isomorphism of quiver representations. -/
def QuiverRepresentationEquiv.symm (e : QuiverRepresentationEquiv k Q ρ₁ ρ₂) :
    QuiverRepresentationEquiv k Q ρ₂ ρ₁ where
  equivAt v := (e.equivAt v).symm
  commutes {v w} f x := by
    rw [LinearEquiv.symm_apply_eq, e.commutes f, LinearEquiv.apply_symm_apply]

/-- The composite of two isomorphisms of quiver representations. -/
def QuiverRepresentationEquiv.trans (e₁ : QuiverRepresentationEquiv k Q ρ₁ ρ₂)
    (e₂ : QuiverRepresentationEquiv k Q ρ₂ ρ₃) :
    QuiverRepresentationEquiv k Q ρ₁ ρ₃ where
  equivAt v := (e₁.equivAt v).trans (e₂.equivAt v)
  commutes {v w} f x := by
    simp only [LinearEquiv.trans_apply]
    rw [e₁.commutes f, e₂.commutes f]

end EquivGroupoid

/-! ## Linear-algebra helpers -/

section Helpers

variable (k : Type*) [CommSemiring k]

/-- The linear map `(Fin p → k) →ₗ[k] (Fin q → k)` keeping the coordinates that exist on both
sides and padding with zeros. For `p = q` it is the identity, and it is the zero map whenever
`p = 0` or `q = 0`. -/
def truncMap (p q : ℕ) : (Fin p → k) →ₗ[k] (Fin q → k) where
  toFun x i := if h : (i : ℕ) < p then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i; by_cases h : (i : ℕ) < p <;> simp [h]
  map_smul' a x := by
    funext i; by_cases h : (i : ℕ) < p <;> simp [h]

/-- The canonical identification of a one-dimensional coordinate space with `k`. -/
def finPiEquivOfEqOne {p : ℕ} (hp : p = 1) : (Fin p → k) ≃ₗ[k] k where
  toFun x := x ⟨0, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun t := fun _ => t
  left_inv x := by
    subst hp
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

@[simp] lemma finPiEquivOfEqOne_apply {p : ℕ} (hp : p = 1) (x : Fin p → k) :
    finPiEquivOfEqOne k hp x = x ⟨0, by omega⟩ := rfl

@[simp] lemma finPiEquivOfEqOne_symm_apply {p : ℕ} (hp : p = 1) (t : k) (i : Fin p) :
    (finPiEquivOfEqOne k hp).symm t i = t := rfl

/-- Under the identifications of source and target with `k`, `truncMap` is the identity. -/
lemma finPiEquivOfEqOne_truncMap {p q : ℕ} (hp : p = 1) (hq : q = 1) (x : Fin p → k) :
    finPiEquivOfEqOne k hq (truncMap k p q x) = finPiEquivOfEqOne k hp x := by
  simp only [finPiEquivOfEqOne_apply, truncMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos (show (0 : ℕ) < p by omega)]

variable {k}

/-- A module isomorphic to `k` is nontrivial. -/
lemma nontrivial_of_linearEquiv {M : Type*} [AddCommMonoid M] [Module k M] [Nontrivial k]
    (E : M ≃ₗ[k] k) : Nontrivial M :=
  ⟨⟨E.symm 0, E.symm 1, fun h => zero_ne_one (E.symm.injective h)⟩⟩

/-- Every submodule of a trivial module is `⊥`. -/
lemma submodule_eq_bot_of_subsingleton {M : Type*} [AddCommMonoid M] [Module k M]
    [Subsingleton M] (W : Submodule k M) : W = ⊥ :=
  eq_bot_iff.mpr fun x _ => (Submodule.mem_bot k).mpr (Subsingleton.elim x 0)

end Helpers

section RankOne

variable {k M : Type*} [Field k] [AddCommMonoid M] [Module k M]

/-- A one-dimensional space admits no nontrivial direct sum decomposition. -/
lemma isCompl_eq_bot_or_eq_bot (E : M ≃ₗ[k] k) {W₁ W₂ : Submodule k M} (h : IsCompl W₁ W₂) :
    W₁ = ⊥ ∨ W₂ = ⊥ := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  obtain ⟨x, hxW, hx0⟩ := (Submodule.ne_bot_iff W₁).mp h₁
  obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff W₂).mp h₂
  have hEx : E x ≠ 0 := fun hE => hx0 (by simpa using E.injective (hE.trans (map_zero E).symm))
  have hxy : (E y * (E x)⁻¹) • x = y := by
    apply E.injective
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hEx, mul_one]
  have hyW₁ : y ∈ W₁ := hxy ▸ W₁.smul_mem _ hxW
  exact hy0 ((Submodule.mem_bot k).mp (h.disjoint.le_bot ⟨hyW₁, hyW⟩))

end RankOne

/-! ## The one-dimensional families -/

section SuppRep

variable (k : Type) [Field k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- The representation supported on `S`: a one-dimensional space at each vertex of `S`, the
zero space elsewhere, and the arrow `e : a ⟶ b` acting by the scalar `c a b e` through the
canonical identifications (automatically zero unless both `a` and `b` lie in `S`). -/
abbrev suppRep (S : Fin n → Prop) [DecidablePred S] (c : ∀ a b : Fin n, (a ⟶ b) → k) :
    FinQuiverRep k n where
  obj j := Fin (if S j then 1 else 0) → k
  mapLinear {a b} e := c a b e • truncMap k (if S a then 1 else 0) (if S b then 1 else 0)

variable (S : Fin n → Prop) [DecidablePred S]

/-- The identification of the space at a supported vertex with `k`. It does not depend on the
arrow scalars, which lets it be used for two members of the same family at once. -/
def suppEquivRaw {j : Fin n} (hj : S j) : (Fin (if S j then 1 else 0) → k) ≃ₗ[k] k :=
  finPiEquivOfEqOne k (if_pos hj)

lemma suppRep_subsingleton (c : ∀ a b : Fin n, (a ⟶ b) → k) {j : Fin n} (hj : ¬ S j) :
    Subsingleton ((suppRep k S c).obj j) := by
  have h : (if S j then 1 else 0) = 0 := if_neg hj
  refine ⟨fun x y => ?_⟩
  funext i
  exact absurd i.isLt (by omega)

instance suppRep_finite (c : ∀ a b : Fin n, (a ⟶ b) → k) (j : Fin n) :
    Module.Finite k ((suppRep k S c).obj j) :=
  Module.Finite.pi

variable {S}

/-- The action of an arrow between two supported vertices, read through the identifications
with `k`. -/
lemma suppRep_map_apply (c : ∀ a b : Fin n, (a ⟶ b) → k) {a b : Fin n} (ha : S a) (hb : S b)
    (e : a ⟶ b) (x : Fin (if S a then 1 else 0) → k) :
    suppEquivRaw k S hb ((suppRep k S c).mapLinear e x) = c a b e * suppEquivRaw k S ha x := by
  change suppEquivRaw k S hb ((c a b e • truncMap k _ _) x) = _
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, suppEquivRaw, suppEquivRaw,
    finPiEquivOfEqOne_truncMap]

/-- An arrow acting by a nonzero scalar between supported vertices is onto. -/
lemma suppRep_map_surjective (c : ∀ a b : Fin n, (a ⟶ b) → k) {a b : Fin n} (ha : S a)
    (hb : S b) (e : a ⟶ b) (hc : c a b e ≠ 0) :
    Function.Surjective ((suppRep k S c).mapLinear e) := by
  intro y
  refine ⟨(suppEquivRaw k S ha).symm ((c a b e)⁻¹ * suppEquivRaw k S hb y), ?_⟩
  apply (suppEquivRaw k S hb).injective
  rw [suppRep_map_apply k c ha hb, LinearEquiv.apply_symm_apply, ← mul_assoc,
    mul_inv_cancel₀ hc, one_mul]

/-! ### Indecomposability -/

/-- A family supported at a single vertex is indecomposable. -/
lemma suppRep_isIndecomposable_single (c : ∀ a b : Fin n, (a ⟶ b) → k) {v : Fin n}
    (hS : ∀ j, S j ↔ j = v) : (suppRep k S c).IsIndecomposable := by
  have hSv : S v := (hS v).mpr rfl
  refine ⟨⟨v, nontrivial_of_linearEquiv (suppEquivRaw k S hSv)⟩, ?_⟩
  intro W₁ W₂ _ _ hcompl
  have hother : ∀ (W : ∀ j, Submodule k ((suppRep k S c).obj j)) (j : Fin n), j ≠ v →
      W j = ⊥ := by
    intro W j hj
    haveI := suppRep_subsingleton k S c (fun h => hj ((hS j).mp h))
    exact submodule_eq_bot_of_subsingleton (W j)
  rcases isCompl_eq_bot_or_eq_bot (suppEquivRaw k S hSv) (hcompl v) with h | h
  · exact Or.inl fun j => by
      by_cases hj : j = v
      · exact hj ▸ h
      · exact hother W₁ j hj
  · exact Or.inr fun j => by
      by_cases hj : j = v
      · exact hj ▸ h
      · exact hother W₂ j hj

/-- Auxiliary step for the two-vertex case: if one half of a decomposition vanishes at `v`,
it vanishes everywhere. -/
private lemma suppRep_pair_aux (c : ∀ a b : Fin n, (a ⟶ b) → k) {v w : Fin n}
    (hS : ∀ j, S j ↔ (j = v ∨ j = w)) (e₁ : v ⟶ w) (hc : c v w e₁ ≠ 0)
    (W₁ W₂ : ∀ j, Submodule k ((suppRep k S c).obj j))
    (hW₂ : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W₂ a, (suppRep k S c).mapLinear e x ∈ W₂ b)
    (hcompl : ∀ j, IsCompl (W₁ j) (W₂ j)) (hv : W₁ v = ⊥) : ∀ j, W₁ j = ⊥ := by
  have hSv : S v := (hS v).mpr (Or.inl rfl)
  have hSw : S w := (hS w).mpr (Or.inr rfl)
  have hW₂v : W₂ v = ⊤ := by
    have h := (hcompl v).sup_eq_top
    rwa [hv, bot_sup_eq] at h
  have hW₂w : W₂ w = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, hx⟩ := suppRep_map_surjective k c hSv hSw e₁ hc y
    have hxmem : x ∈ W₂ v := by rw [hW₂v]; trivial
    exact hx ▸ hW₂ e₁ x hxmem
  have hw : W₁ w = ⊥ :=
    (hcompl w).disjoint.eq_bot_of_le (by rw [hW₂w]; exact le_top)
  intro j
  by_cases hjv : j = v
  · exact hjv ▸ hv
  by_cases hjw : j = w
  · exact hjw ▸ hw
  haveI := suppRep_subsingleton k S c (fun h => by rcases (hS j).mp h with h' | h' <;> simp_all)
  exact submodule_eq_bot_of_subsingleton (W₁ j)

/-- A family supported on two vertices joined by an arrow acting invertibly is
indecomposable. -/
lemma suppRep_isIndecomposable_pair (c : ∀ a b : Fin n, (a ⟶ b) → k) {v w : Fin n}
    (hS : ∀ j, S j ↔ (j = v ∨ j = w)) (e₁ : v ⟶ w) (hc : c v w e₁ ≠ 0) :
    (suppRep k S c).IsIndecomposable := by
  have hSv : S v := (hS v).mpr (Or.inl rfl)
  refine ⟨⟨v, nontrivial_of_linearEquiv (suppEquivRaw k S hSv)⟩, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hcompl
  rcases isCompl_eq_bot_or_eq_bot (suppEquivRaw k S hSv) (hcompl v) with h | h
  · exact Or.inl (suppRep_pair_aux k c hS e₁ hc W₁ W₂ hW₂ hcompl h)
  · exact Or.inr
      (suppRep_pair_aux k c hS e₁ hc W₂ W₁ hW₁ (fun j => (hcompl j).symm) h)

/-! ### The scalar attached to an isomorphism -/

variable {c c' : ∀ a b : Fin n, (a ⟶ b) → k}

/-- The scalar by which an isomorphism of two members of the family acts at a supported
vertex. -/
def suppScal (φ : QuiverRepresentationEquiv k (Fin n) (suppRep k S c) (suppRep k S c'))
    {j : Fin n} (hj : S j) : k :=
  suppEquivRaw k S hj (φ.equivAt j ((suppEquivRaw k S hj).symm 1))

lemma suppScal_apply (φ : QuiverRepresentationEquiv k (Fin n) (suppRep k S c) (suppRep k S c'))
    {j : Fin n} (hj : S j) (t : k) :
    suppEquivRaw k S hj (φ.equivAt j ((suppEquivRaw k S hj).symm t))
      = suppScal k φ hj * t := by
  have ht : (suppEquivRaw k S hj).symm t = t • (suppEquivRaw k S hj).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [ht, map_smul, map_smul, smul_eq_mul, suppScal, mul_comm]

lemma suppScal_ne_zero
    (φ : QuiverRepresentationEquiv k (Fin n) (suppRep k S c) (suppRep k S c'))
    {j : Fin n} (hj : S j) : suppScal k φ hj ≠ 0 := by
  intro h
  rw [suppScal] at h
  have h1 : ((suppEquivRaw k S hj).symm 1 : Fin (if S j then 1 else 0) → k) = 0 := by
    apply (φ.equivAt j).injective
    rw [map_zero]
    exact (suppEquivRaw k S hj).injective (by rw [h, map_zero])
  have : (1 : k) = 0 := by
    have := congrArg (suppEquivRaw k S hj) h1
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

/-- The defining relation between the arrow scalars of two isomorphic members of the
family. -/
lemma suppScal_relation
    (φ : QuiverRepresentationEquiv k (Fin n) (suppRep k S c) (suppRep k S c'))
    {a b : Fin n} (ha : S a) (hb : S b) (e : a ⟶ b) :
    suppScal k φ hb * c a b e = c' a b e * suppScal k φ ha := by
  have h1 : (suppRep k S c).mapLinear e ((suppEquivRaw k S ha).symm 1)
      = (suppEquivRaw k S hb).symm (c a b e) := by
    apply (suppEquivRaw k S hb).injective
    rw [suppRep_map_apply k c ha hb, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, mul_one]
  have hcomm := congrArg (suppEquivRaw k S hb) (φ.commutes e ((suppEquivRaw k S ha).symm 1))
  rw [h1, suppScal_apply, suppRep_map_apply k c' ha hb, suppScal_apply, mul_one] at hcomm
  exact hcomm

end SuppRep

/-! ## Infinite representation type from a loop -/

section Loop

variable (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- Pigeonhole: an infinitely-parameterised family of pairwise non-isomorphic
finite-dimensional indecomposables rules out finite representation type. -/
lemma not_hasFiniteRepresentationType_of_family
    (R : k → FinQuiverRep k n)
    (hfin : ∀ lam v, Module.Finite k ((R lam).obj v))
    (hindec : ∀ lam, (R lam).IsIndecomposable)
    (hsep : ∀ lam mu : k,
      Nonempty (QuiverRepresentationEquiv k (Fin n) (R lam) (R mu)) → lam = mu) :
    ¬ HasFiniteRepresentationType k n := by
  rintro ⟨m, reps, -, -, hcover⟩
  choose F hF using fun lam => hcover (R lam) (hfin lam) (hindec lam)
  have hinj : Function.Injective F := by
    intro lam mu hlm
    refine hsep lam mu ?_
    obtain ⟨e₁⟩ := hF lam
    obtain ⟨e₂⟩ := hF mu
    have e₂' : QuiverRepresentationEquiv k (Fin n) (R mu) (reps (F lam)) := by
      rw [hlm]; exact e₂
    exact ⟨e₁.trans e₂'.symm⟩
  haveI : Finite k := Finite.of_injective F hinj
  exact not_finite k

/-- The support predicate of the loop family. -/
private def loopSupp (v : Fin n) : Fin n → Prop := fun j => j = v

instance (v : Fin n) : DecidablePred (loopSupp (n := n) v) :=
  fun j => inferInstanceAs (Decidable (j = v))

/-- **A loop forces infinite representation type.** The one-dimensional representations
`(k, lam)` supported at `v`, with every loop at `v` acting by `lam`, are indecomposable and
pairwise non-isomorphic. -/
theorem not_hasFiniteRepresentationType_of_loop {v : Fin n} (e₀ : v ⟶ v) :
    ¬ HasFiniteRepresentationType k n := by
  have hS : ∀ j, loopSupp (n := n) v j ↔ j = v := fun _ => Iff.rfl
  have hSv : loopSupp (n := n) v v := rfl
  refine not_hasFiniteRepresentationType_of_family k
    (fun lam => suppRep k (loopSupp v) (fun _ _ _ => lam))
    (fun lam j => suppRep_finite k _ _ j)
    (fun lam => suppRep_isIndecomposable_single k _ hS) ?_
  rintro lam mu ⟨φ⟩
  have h := suppScal_relation k φ hSv hSv e₀
  have hg := suppScal_ne_zero k φ hSv
  exact mul_left_cancel₀ hg (h.trans (mul_comm _ _))

end Loop

/-! ## Infinite representation type from two arrows joining a pair of vertices -/

section TwoArrows

variable (k : Type) [Field k] [IsAlgClosed k] {n : ℕ} [Quiver.{0} (Fin n)]

/-- The support predicate of the two-vertex family. -/
private def pairSupp (v w : Fin n) : Fin n → Prop := fun j => j = v ∨ j = w

instance (v w : Fin n) : DecidablePred (pairSupp (n := n) v w) :=
  fun j => inferInstanceAs (Decidable (j = v ∨ j = w))

-- Arrow types carry no `DecidableEq`, so the arrow scalars below are defined classically.
attribute [local instance 0] Classical.propDecidable

/-- The arrow scalars of the Kronecker family: the distinguished arrow `E₁` acts by `1`, the
second arrow `E₂` acts by `lam`, everything else by `0`. -/
noncomputable def twoArrowScalar (E₁ E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) (lam : k)
    (a b : Fin n) (e : a ⟶ b) : k :=
  if (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₁ then 1
  else if (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₂ then lam else 0

omit [IsAlgClosed k] in
lemma twoArrowScalar_fst (E₁ E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) (lam : k)
    {a b : Fin n} (e : a ⟶ b) (h : (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₁) :
    twoArrowScalar k E₁ E₂ lam a b e = 1 := by
  rw [twoArrowScalar, if_pos h]

omit [IsAlgClosed k] in
lemma twoArrowScalar_snd (E₁ E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) (lam : k)
    {a b : Fin n} (e : a ⟶ b) (h : (⟨a, b, e⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b)) = E₂)
    (hne : E₂ ≠ E₁) : twoArrowScalar k E₁ E₂ lam a b e = lam := by
  rw [twoArrowScalar, if_neg (by rw [h]; exact hne), if_pos h]

/-- **Two distinct arrows joining a pair of distinct vertices force infinite representation
type.** This covers both parallel arrows (`E₂` also runs `v ⟶ w`) and a pair of opposite
arrows (`E₂` runs `w ⟶ v`). -/
theorem not_hasFiniteRepresentationType_of_two_arrows {v w : Fin n} (e₁ : v ⟶ w)
    (E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b))
    (hE₂a : E₂.1 = v ∨ E₂.1 = w) (hE₂b : E₂.2.1 = v ∨ E₂.2.1 = w)
    (hne : E₂ ≠ (⟨v, w, e₁⟩ : (a : Fin n) × (b : Fin n) × (a ⟶ b))) :
    ¬ HasFiniteRepresentationType k n := by
  obtain ⟨a₂, b₂, e₂⟩ := E₂
  simp only at hE₂a hE₂b
  set S : Fin n → Prop := pairSupp v w with hSdef
  have hS : ∀ j, S j ↔ (j = v ∨ j = w) := fun _ => Iff.rfl
  have hSv : S v := Or.inl rfl
  have hSw : S w := Or.inr rfl
  have hSa : S a₂ := hE₂a
  have hSb : S b₂ := hE₂b
  set E₁ : (a : Fin n) × (b : Fin n) × (a ⟶ b) := ⟨v, w, e₁⟩ with hE₁def
  set E₂ : (a : Fin n) × (b : Fin n) × (a ⟶ b) := ⟨a₂, b₂, e₂⟩ with hE₂def
  have hone : ∀ lam : k, twoArrowScalar k E₁ E₂ lam v w e₁ = 1 := fun lam =>
    twoArrowScalar_fst k E₁ E₂ lam e₁ rfl
  have hlam : ∀ lam : k, twoArrowScalar k E₁ E₂ lam a₂ b₂ e₂ = lam := fun lam =>
    twoArrowScalar_snd k E₁ E₂ lam e₂ rfl hne
  refine not_hasFiniteRepresentationType_of_family k
    (fun lam => suppRep k S (twoArrowScalar k E₁ E₂ lam))
    (fun lam j => suppRep_finite k S _ j)
    (fun lam => suppRep_isIndecomposable_pair k _ hS e₁ (by rw [hone lam]; exact one_ne_zero)) ?_
  rintro lam mu ⟨φ⟩
  have hgv := suppScal_ne_zero k φ hSv
  -- the distinguished arrow forces the two vertex scalars to agree
  have hvw : suppScal k φ hSw = suppScal k φ hSv := by
    have h := suppScal_relation k φ hSv hSw e₁
    rw [hone lam, hone mu, mul_one, one_mul] at h
    exact h
  -- the second arrow then identifies the parameters
  have h := suppScal_relation k φ hSa hSb e₂
  rw [hlam lam, hlam mu] at h
  have hga : suppScal k φ hSa = suppScal k φ hSv := by
    rcases hE₂a with h' | h'
    · subst h'; rfl
    · subst h'; exact hvw
  have hgb : suppScal k φ hSb = suppScal k φ hSv := by
    rcases hE₂b with h' | h'
    · subst h'; rfl
    · subst h'; exact hvw
  rw [hga, hgb] at h
  exact mul_left_cancel₀ hgv (h.trans (mul_comm _ _))

/-- **Parallel arrows force infinite representation type.** -/
theorem not_hasFiniteRepresentationType_of_parallel {v w : Fin n} (e₁ e₂ : v ⟶ w)
    (hne : e₁ ≠ e₂) : ¬ HasFiniteRepresentationType k n := by
  refine not_hasFiniteRepresentationType_of_two_arrows k e₁ ⟨v, w, e₂⟩ (Or.inl rfl)
    (Or.inr rfl) ?_
  intro h
  apply hne
  injection h with _ h₂
  injection h₂ with _ h₄
  exact h₄.symm

/-- **An edge oriented in both directions forces infinite representation type.** -/
theorem not_hasFiniteRepresentationType_of_opposite {v w : Fin n} (hvw : v ≠ w) (e₁ : v ⟶ w)
    (e₂ : w ⟶ v) : ¬ HasFiniteRepresentationType k n := by
  refine not_hasFiniteRepresentationType_of_two_arrows k e₁ ⟨w, v, e₂⟩ (Or.inr rfl)
    (Or.inl rfl) ?_
  intro h
  exact hvw (congrArg Sigma.fst h).symm

end TwoArrows

/-! ## The classification for arbitrary finite quivers -/

section General

variable (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) [Quiver.{0} (Fin n)]
  [∀ a b : Fin n, Decidable (Nonempty (a ⟶ b))]

/-- For the undirected adjacency matrix of a quiver, `IsOrientationOf` says exactly that the
quiver has no loops and no edge oriented in both directions. -/
lemma isOrientationOf_quiverUndirectedAdj_iff :
    IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n) ↔
      ((∀ v : Fin n, IsEmpty (v ⟶ v)) ∧
        ∀ v w : Fin n, Nonempty (v ⟶ w) → Nonempty (w ⟶ v) → False) := by
  constructor
  · rintro ⟨h₁, -, h₃⟩
    refine ⟨fun v => h₁ v v ?_, h₃⟩
    rw [quiverUndirectedAdj_diag]
    exact zero_ne_one
  · rintro ⟨hloop, hbi⟩
    refine ⟨?_, ?_, hbi⟩
    · intro i j hij
      by_cases h : i = j
      · exact h ▸ hloop i
      · rw [← not_nonempty_iff]
        intro hcon
        exact hij (by simp [quiverUndirectedAdj, h, hcon])
    · intro i j hij
      by_contra hcon
      rw [not_or] at hcon
      have : quiverUndirectedAdj n i j = 0 := by
        simp only [quiverUndirectedAdj]
        rw [if_neg]
        rintro ⟨-, h | h⟩
        · exact hcon.1 h
        · exact hcon.2 h
      rw [this] at hij
      exact zero_ne_one hij

/-- **Gabriel's theorem for an arbitrary connected finite quiver** (Etingof Theorem 2.1.2).

No restriction is placed on the quiver: loops and parallel arrows are permitted by the book's
Definition 2.8.1 and are covered here by proved negative branches. A connected quiver on
`Fin n` has finite representation type over an algebraically closed field if and only if it
has no loops, no edge oriented in both directions, no parallel arrows, and its underlying
undirected graph is a Dynkin diagram.

The footnote to Theorem 2.1.2 says that the classification remains valid over an arbitrary field,
but the book only proves the algebraically closed case formalized here. -/
theorem Theorem_2_1_2_general (hconn : QuiverUndirectedConnected n) :
    HasFiniteRepresentationType k n ↔
      ((∀ v : Fin n, IsEmpty (v ⟶ v)) ∧
        (∀ v w : Fin n, Nonempty (v ⟶ w) → Nonempty (w ⟶ v) → False) ∧
        (∀ a b : Fin n, Subsingleton (a ⟶ b)) ∧
        IsDynkinDiagram n (quiverUndirectedAdj n)) := by
  constructor
  · intro hfrt
    -- no loops
    have hloop : ∀ v : Fin n, IsEmpty (v ⟶ v) := by
      intro v
      rw [← not_nonempty_iff]
      intro hcon
      exact not_hasFiniteRepresentationType_of_loop k hcon.some hfrt
    -- no edge oriented both ways
    have hbi : ∀ v w : Fin n, Nonempty (v ⟶ w) → Nonempty (w ⟶ v) → False := by
      rintro v w ⟨e₁⟩ ⟨e₂⟩
      by_cases hvw : v = w
      · subst hvw
        exact (hloop v).false e₁
      · exact not_hasFiniteRepresentationType_of_opposite k hvw e₁ e₂ hfrt
    -- no parallel arrows
    have hsub : ∀ a b : Fin n, Subsingleton (a ⟶ b) := by
      intro a b
      refine ⟨fun e₁ e₂ => ?_⟩
      by_cases hab : a = b
      · subst hab
        exact ((hloop a).false e₁).elim
      by_contra hne
      exact not_hasFiniteRepresentationType_of_parallel k e₁ e₂ hne hfrt
    haveI := hsub
    have hOrient : IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n) :=
      (isOrientationOf_quiverUndirectedAdj_iff n).mpr ⟨hloop, hbi⟩
    exact ⟨hloop, hbi, hsub, (Theorem_2_1_2 k n hOrient hconn).mp hfrt⟩
  · rintro ⟨hloop, hbi, hsub, hDynkin⟩
    haveI := hsub
    have hOrient : IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n) :=
      (isOrientationOf_quiverUndirectedAdj_iff n).mpr ⟨hloop, hbi⟩
    exact (Theorem_2_1_2 k n hOrient hconn).mpr hDynkin

/-- The classification of Theorem 2.1.2, with the loop-free and single-orientation conditions
packaged as `IsOrientationOf`. In this form the two typeclass hypotheses of
`Etingof.Theorem_2_1_2` appear as conditions in the classification rather than as standing
assumptions. -/
theorem Theorem_2_1_2_general_orientation (hconn : QuiverUndirectedConnected n) :
    HasFiniteRepresentationType k n ↔
      (IsOrientationOf ‹Quiver (Fin n)› (quiverUndirectedAdj n) ∧
        (∀ a b : Fin n, Subsingleton (a ⟶ b)) ∧
        IsDynkinDiagram n (quiverUndirectedAdj n)) := by
  rw [Theorem_2_1_2_general k n hconn, isOrientationOf_quiverUndirectedAdj_iff n]
  tauto

end General

end Etingof
