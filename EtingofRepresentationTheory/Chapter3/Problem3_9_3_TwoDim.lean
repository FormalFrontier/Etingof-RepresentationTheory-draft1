import EtingofRepresentationTheory.Chapter3.Problem3_9_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_9

/-!
# Problem 3.9.3: the isomorphism classification of two-dimensional representations

`Chapter3/Problem3_9_3.lean` records a *necessary condition* on a two-dimensional
representation of a path algebra `P_Q`: it is either decomposable, or some arrow acts
bijectively between two distinct vertices. That disjunction is not a classification -- it
names no normal forms and produces no isomorphisms.

This file completes Problem 3.9.3 by exhibiting the actual isomorphism classes.

## The normal form

`twoRep i j c` is the representation with

* `k` at vertex `i` and `k` at vertex `j` (so `k²` at `i` when `i = j`), zero elsewhere;
* the arrow `e : i ⟶ j` acting by the scalar `c ⟨i, j, e⟩`, every other arrow by `0`.

Concretely the vertex space is the product
`(Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)`, which is exactly the
vertex space of `S_i ⊕ S_j`, and the arrow maps are built from the padding map `truncMap`, which
is automatically zero whenever the source or target dimension is `0`. So a *single* family
covers both the decomposable and the indecomposable normal forms:

* `twoRep i j 0` is `S_i ⊕ S_j` (`twoRepZeroEquivDirectSum`), and is decomposable
  (`twoRep_zero_not_isIndecomposable`);
* `twoRep i j c` with `i ≠ j` and `c` nonzero on some arrow `i → j` is indecomposable
  (`twoRep_isIndecomposable`).

## Results

* `sum_dimVec_twoRep` -- every normal form really is two-dimensional.
* `two_dim_normalForm` -- **exhaustiveness**: for `Q` finite without oriented cycles, every
  two-dimensional `ρ` carries an *isomorphism* onto a normal form, and the two branches are the
  decomposable (`c = 0`) and indecomposable (`c ≠ 0` on an arrow `i → j`) cases.
* `twoRep_isIndecomposable`, `twoRep_zero_not_isIndecomposable` -- the two branches are
  genuinely different isomorphism classes.
* `twoRep_equiv_smul` and `exists_smul_of_equiv_twoRep` -- the **parameter criterion**: for
  `i ≠ j`, `twoRep i j c ≅ twoRep i j c'` if and only if `c'` and `c` agree up to a single
  nonzero scalar on the arrows `i → j`. This is where parallel arrows enter: the
  isomorphism classes of indecomposable two-dimensional representations supported on `i ≠ j` are
  the points of the projective space `ℙ(k^{#(i ⟶ j)})`, so a quiver with `m` parallel arrows
  `i → j` has an `(m-1)`-dimensional family of them, not just one.
* `vertices_eq_of_equiv_twoRep` -- the **support criterion**: the unordered pair `{i, j}` is an
  isomorphism invariant.
* `two_dim_classification_of_normalForm` -- the old necessary-condition disjunction
  `Problem3_9_3.two_dim_classification`, recovered as a corollary of the normal form.
-/

namespace Etingof

open Module (finrank)

variable {k Q : Type*} [Field k] [Quiver Q]

/-! ### Basic API for isomorphism of quiver representations

`QuiverRepresentationEquiv` (Chapter 2, Theorem 2.1.2) had no groupoid API. -/

namespace QuiverRepresentationEquiv

variable {ρ σ τ : QuiverRepresentation k Q}

/-- The identity isomorphism. -/
def refl (ρ : QuiverRepresentation k Q) : QuiverRepresentationEquiv k Q ρ ρ where
  equivAt _ := LinearEquiv.refl k _
  commutes _ _ := rfl

/-- The inverse isomorphism. -/
def symm (φ : QuiverRepresentationEquiv k Q ρ σ) : QuiverRepresentationEquiv k Q σ ρ where
  equivAt v := (φ.equivAt v).symm
  commutes e x := by
    apply (φ.equivAt _).injective
    rw [LinearEquiv.apply_symm_apply, φ.commutes e, LinearEquiv.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans (φ : QuiverRepresentationEquiv k Q ρ σ) (ψ : QuiverRepresentationEquiv k Q σ τ) :
    QuiverRepresentationEquiv k Q ρ τ where
  equivAt v := (φ.equivAt v).trans (ψ.equivAt v)
  commutes e x := by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, φ.commutes e, ψ.commutes e]

/-- The dimension vector is an isomorphism invariant. -/
theorem dimVec_eq (φ : QuiverRepresentationEquiv k Q ρ σ) (v : Q) :
    Problem6_9_3.dimVec ρ v = Problem6_9_3.dimVec σ v := by
  letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
  letI : AddCommGroup (σ.obj v) := Module.addCommMonoidToAddCommGroup k
  exact (φ.equivAt v).finrank_eq

end QuiverRepresentationEquiv

namespace Problem3_9_3

open Etingof.Problem6_9_3 (simpleRep dimVec)

/-! ### Linear-algebra helpers

All carriers below are of the shape `Fin (if _ then 1 else 0) → k`, whose `if` is stuck for a
variable vertex. Following the pattern recorded for `#7408`, we never case-split on types:
`truncMap` gives one uniform arrow map, and all reasoning goes through `finPiEquivOfEqOne`
stated on the *raw* `Pi` type. -/

/-- The padding/truncation map `(Fin p → k) →ₗ (Fin q → k)`: keep the first `min p q`
coordinates, pad with zeros. It is the zero map as soon as `p = 0` or `q = 0`, and the identity
when `p = q = 1`; this is what lets a single expression define an arrow map that "acts by a
scalar between the two supported vertices and by zero everywhere else". -/
def truncMap (k : Type*) [Field k] (p q : ℕ) : (Fin p → k) →ₗ[k] (Fin q → k) where
  toFun x i := if h : (i : ℕ) < p then x ⟨i, h⟩ else 0
  map_add' x y := by funext i; by_cases h : (i : ℕ) < p <;> simp [h]
  map_smul' a x := by funext i; by_cases h : (i : ℕ) < p <;> simp [h]

theorem truncMap_apply (p q : ℕ) (x : Fin p → k) (i : Fin q) :
    truncMap k p q x i = if h : (i : ℕ) < p then x ⟨i, h⟩ else 0 := rfl

/-- Padding out of a zero-dimensional source is zero. -/
theorem truncMap_eq_zero_of_source {p q : ℕ} (hp : p = 0) : truncMap k p q = 0 := by
  subst hp
  refine LinearMap.ext fun x => funext fun i => ?_
  rw [truncMap_apply, dif_neg (by omega), LinearMap.zero_apply, Pi.zero_apply]

/-- Padding into a zero-dimensional target is zero. -/
theorem truncMap_eq_zero_of_target {p q : ℕ} (hq : q = 0) : truncMap k p q = 0 := by
  subst hq
  exact LinearMap.ext fun x => funext fun i => i.elim0

/-- A `Pi` type over `Fin p` with `p = 1` is the ground field. Stated on the raw type (not on a
representation's `obj` projection) so it can be shared between members of a family. -/
def finPiEquivOfEqOne (k : Type*) [Field k] {p : ℕ} (hp : p = 1) : (Fin p → k) ≃ₗ[k] k where
  toFun x := x ⟨0, by omega⟩
  invFun t := fun _ => t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by subst hp; funext i; exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

@[simp] theorem finPiEquivOfEqOne_symm_apply {p : ℕ} (hp : p = 1) (t : k) (i : Fin p) :
    (finPiEquivOfEqOne k hp).symm t i = t := rfl

/-- The workhorse identification: between one-dimensional source and target, `truncMap` is the
identity. -/
theorem finPiEquivOfEqOne_truncMap {p q : ℕ} (hp : p = 1) (hq : q = 1) (x : Fin p → k) :
    finPiEquivOfEqOne k hq (truncMap k p q x) = finPiEquivOfEqOne k hp x := by
  subst hp
  change truncMap k 1 q x ⟨0, _⟩ = x ⟨0, _⟩
  rw [truncMap_apply, dif_pos (show ((⟨0, by omega⟩ : Fin q) : ℕ) < 1 from Nat.zero_lt_one)]

omit [Field k] in
/-- A subsingleton `Pi` type over `Fin q` with `q = 0`. -/
theorem finPi_subsingleton {q : ℕ} (hq : q = 0) : Subsingleton (Fin q → k) := by
  subst hq; infer_instance

section Prod

variable {M N : Type*} [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]

/-- Drop a trivial right factor of a product. -/
def prodTrivRight (k : Type*) [Field k] {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] (hN : Subsingleton N) : (M × N) ≃ₗ[k] M where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := (m, 0)
  left_inv _ := Prod.ext rfl (@Subsingleton.elim N hN _ _)
  right_inv _ := rfl

/-- Drop a trivial left factor of a product. -/
def prodTrivLeft (k : Type*) [Field k] {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] (hM : Subsingleton M) : (M × N) ≃ₗ[k] N where
  toFun := Prod.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun n := (0, n)
  left_inv _ := Prod.ext (@Subsingleton.elim M hM _ _) rfl
  right_inv _ := rfl

@[simp] theorem prodTrivRight_symm_apply (hN : Subsingleton N) (m : M) :
    (prodTrivRight k hN).symm m = (m, 0) := rfl

@[simp] theorem prodTrivLeft_symm_apply (hM : Subsingleton M) (n : N) :
    (prodTrivLeft (M := M) k hM).symm n = (0, n) := rfl

/-- Any two trivial modules are isomorphic. -/
def subsingletonEquiv (k : Type*) [Field k] {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] (hM : Subsingleton M) (hN : Subsingleton N) : M ≃ₗ[k] N where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := (add_zero 0).symm
  map_smul' c _ := (smul_zero c).symm
  left_inv _ := @Subsingleton.elim M hM _ _
  right_inv _ := @Subsingleton.elim N hN _ _

end Prod

/-! ### The normal form `twoRep` -/

variable {k Q : Type*} [Field k] [Quiver Q]

/-- The **two-dimensional normal form** `twoRep i j c`: the field `k` at vertex `i` and at
vertex `j` (so `k²` at `i` when `i = j`), zero at every other vertex, with an arrow `e : i ⟶ j`
acting by the scalar `c ⟨i, j, e⟩` and every other arrow by zero.

The vertex space is literally the vertex space of `S_i ⊕ S_j`; the coefficient family `c` is
indexed by *all* arrows of `Q`, but only its values on arrows `i → j` matter, since `truncMap`
vanishes as soon as the source or target dimension is `0`. -/
noncomputable def twoRep [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    QuiverRepresentation k Q where
  obj v := (Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)
  mapLinear {a b} e :=
    (LinearMap.inr k _ _).comp
      ((c ⟨a, b, e⟩ • truncMap k (if a = i then 1 else 0) (if b = j then 1 else 0)).comp
        (LinearMap.fst k _ _))

@[simp] theorem twoRep_mapLinear_apply [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {a b : Q} (e : a ⟶ b) (x : (twoRep i j c).obj a) :
    (twoRep i j c).mapLinear e x =
      (0, c ⟨a, b, e⟩ • truncMap k (if a = i then 1 else 0) (if b = j then 1 else 0) x.1) :=
  rfl

/-- Away from `i` and `j` the normal form is trivial. -/
theorem twoRep_obj_subsingleton [DecidableEq Q] {i j : Q} (c : (Σ a b : Q, (a ⟶ b)) → k)
    {v : Q} (hi : v ≠ i) (hj : v ≠ j) : Subsingleton ((twoRep i j c).obj v) := by
  have h1 : Subsingleton (Fin (if v = i then 1 else 0) → k) := finPi_subsingleton (if_neg hi)
  have h2 : Subsingleton (Fin (if v = j then 1 else 0) → k) := finPi_subsingleton (if_neg hj)
  exact @instSubsingletonProd _ _ h1 h2

instance twoRep_free [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    Module.Free k ((twoRep i j c).obj v) :=
  inferInstanceAs
    (Module.Free k ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)))

instance twoRep_finite [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    Module.Finite k ((twoRep i j c).obj v) :=
  inferInstanceAs
    (Module.Finite k ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)))

/-- The carriers of the normal form are honest `AddCommGroup`s. Registered at low priority so
that the bundled `AddCommMonoid` stays preferred elsewhere. -/
noncomputable instance (priority := 100) twoRep_addCommGroup [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) : AddCommGroup ((twoRep i j c).obj v) :=
  inferInstanceAs
    (AddCommGroup ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)))

/-- The dimension vector of the normal form. -/
theorem dimVec_twoRep [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    dimVec (twoRep i j c) v = (if v = i then 1 else 0) + (if v = j then 1 else 0) := by
  change finrank k ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)) = _
  rw [Module.finrank_prod, Module.finrank_pi k, Module.finrank_pi k, Fintype.card_fin,
    Fintype.card_fin]

/-- Every normal form is two-dimensional. -/
theorem sum_dimVec_twoRep [DecidableEq Q] [Fintype Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) : ∑ v, dimVec (twoRep i j c) v = 2 := by
  simp only [dimVec_twoRep, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

/-- With zero coefficients every arrow of the normal form acts by zero. -/
theorem twoRep_zero_mapLinear [DecidableEq Q] (i j : Q) {a b : Q} (e : a ⟶ b) :
    (twoRep (k := k) i j (0 : (Σ a b : Q, (a ⟶ b)) → k)).mapLinear e = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [twoRep_mapLinear_apply]
  simp only [Pi.zero_apply, zero_smul, LinearMap.zero_apply]
  rfl

/-- `twoRep i j 0` is the direct sum of the two vertex simples `S_i ⊕ S_j`. -/
noncomputable def twoRepZeroEquivDirectSum [DecidableEq Q] (i j : Q) :
    QuiverRepresentationEquiv k Q (twoRep i j (0 : (Σ a b : Q, (a ⟶ b)) → k))
      (QuiverRepresentation.directSum k Q (simpleRep i) (simpleRep j)) where
  equivAt _ := LinearEquiv.refl k _
  commutes e x := by
    have h1 : ((twoRep (k := k) i j (0 : (Σ a b : Q, (a ⟶ b)) → k)).mapLinear e) x = 0 := by
      rw [twoRep_zero_mapLinear, LinearMap.zero_apply]
    rw [h1, map_zero]
    rfl

/-! ### The two normal forms are not isomorphic: indecomposability -/

/-- **`twoRep i j 0` is decomposable** -- it splits as `S_i ⊕ S_j`. -/
theorem twoRep_zero_not_isIndecomposable [DecidableEq Q] (i j : Q) :
    ¬ (twoRep (k := k) i j (0 : (Σ a b : Q, (a ⟶ b)) → k)).IsIndecomposable := by
  intro hIndec
  obtain ⟨-, hdecomp⟩ := hIndec
  let c : (Σ a b : Q, (a ⟶ b)) → k := 0
  -- All arrow maps vanish, so the two coordinate summands are stable subrepresentations.
  have hmaps : ∀ {a b : Q} (e : a ⟶ b), (twoRep (k := k) i j c).mapLinear e = 0 :=
    fun e => twoRep_zero_mapLinear i j e
  let W₁ : ∀ v, Submodule k ((twoRep (k := k) i j c).obj v) :=
    fun v => LinearMap.range (LinearMap.inl k (Fin (if v = i then 1 else 0) → k)
      (Fin (if v = j then 1 else 0) → k))
  let W₂ : ∀ v, Submodule k ((twoRep (k := k) i j c).obj v) :=
    fun v => LinearMap.range (LinearMap.inr k (Fin (if v = i then 1 else 0) → k)
      (Fin (if v = j then 1 else 0) → k))
  have hstable : ∀ (W : ∀ v, Submodule k ((twoRep (k := k) i j c).obj v)),
      ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, (twoRep (k := k) i j c).mapLinear e x ∈ W b := by
    intro W a b e x _
    rw [hmaps e, LinearMap.zero_apply]
    exact (W b).zero_mem
  have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := fun _ => LinearMap.isCompl_range_inl_inr
  -- Neither summand is everywhere zero: `W₁ i` and `W₂ j` are one-dimensional.
  rcases hdecomp W₁ W₂ (hstable W₁) (hstable W₂) hcompl with h1 | h2
  · have hne : (LinearMap.inl k (Fin (if i = i then 1 else 0) → k)
        (Fin (if i = j then 1 else 0) → k)) ((finPiEquivOfEqOne k (if_pos rfl)).symm 1) ≠ 0 := by
      intro h
      have := congrArg Prod.fst h
      have h0 : (finPiEquivOfEqOne k (if_pos (rfl : i = i))).symm (1 : k) = 0 := this
      have := congrArg (finPiEquivOfEqOne k (if_pos (rfl : i = i))) h0
      simp only [LinearEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero this
    exact hne (by
      have := h1 i
      rw [Submodule.eq_bot_iff] at this
      exact this _ (LinearMap.mem_range_self _ _))
  · have hne : (LinearMap.inr k (Fin (if j = i then 1 else 0) → k)
        (Fin (if j = j then 1 else 0) → k)) ((finPiEquivOfEqOne k (if_pos rfl)).symm 1) ≠ 0 := by
      intro h
      have := congrArg Prod.snd h
      have h0 : (finPiEquivOfEqOne k (if_pos (rfl : j = j))).symm (1 : k) = 0 := this
      have := congrArg (finPiEquivOfEqOne k (if_pos (rfl : j = j))) h0
      simp only [LinearEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero this
    exact hne (by
      have := h2 j
      rw [Submodule.eq_bot_iff] at this
      exact this _ (LinearMap.mem_range_self _ _))

end Problem3_9_3

end Etingof
