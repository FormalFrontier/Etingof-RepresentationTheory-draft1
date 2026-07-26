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

theorem twoRep_mapLinear_apply_fst [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {a b : Q} (e : a ⟶ b) (x : (twoRep i j c).obj a) :
    ((twoRep i j c).mapLinear e x).1 = 0 := rfl

theorem twoRep_mapLinear_apply_snd [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {a b : Q} (e : a ⟶ b) (x : (twoRep i j c).obj a) :
    ((twoRep i j c).mapLinear e x).2 =
      c ⟨a, b, e⟩ • truncMap k (if a = i then 1 else 0) (if b = j then 1 else 0) x.1 := rfl

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

/-- The carriers of the normal form are honest `AddCommGroup`s, built from the bundled
`AddCommMonoid` via `Module.addCommMonoidToAddCommGroup` so that `toAddCommMonoid` is *defeq* to
the bundled one (hence the bundled `Module k` is still found). Registered at low priority so that
the bundled `AddCommMonoid` stays preferred elsewhere. -/
noncomputable instance (priority := 100) twoRep_addCommGroup [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) : AddCommGroup ((twoRep i j c).obj v) :=
  Module.addCommMonoidToAddCommGroup k

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

/-! ### Generators of the two one-dimensional slots -/

/-- The generator of the `i`-slot of `twoRep i j c`. -/
noncomputable def genFst [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    (twoRep i j c).obj i :=
  ((finPiEquivOfEqOne k (if_pos rfl)).symm 1, 0)

/-- The generator of the `j`-slot of `twoRep i j c`. -/
noncomputable def genSnd [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    (twoRep i j c).obj j :=
  (0, (finPiEquivOfEqOne k (if_pos rfl)).symm 1)

/-- An arrow `e : i ⟶ j` sends the `i`-generator to `c ⟨i, j, e⟩` times the `j`-generator. This is
the defining property of the normal form. -/
theorem twoRep_mapLinear_genFst [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k)
    (e : i ⟶ j) :
    (twoRep i j c).mapLinear e (genFst i j c) = c ⟨i, j, e⟩ • genSnd i j c := by
  rw [twoRep_mapLinear_apply]
  refine Prod.ext (smul_zero _).symm ?_
  change c ⟨i, j, e⟩ • truncMap k _ _ ((finPiEquivOfEqOne k (if_pos rfl)).symm (1 : k))
    = c ⟨i, j, e⟩ • (finPiEquivOfEqOne k (if_pos rfl)).symm (1 : k)
  congr 1
  apply (finPiEquivOfEqOne k (if_pos (rfl : j = j))).injective
  rw [finPiEquivOfEqOne_truncMap (if_pos (rfl : i = i)) (if_pos (rfl : j = j)),
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The `j`-generator is nonzero. -/
theorem genSnd_ne_zero [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    genSnd (k := k) i j c ≠ 0 := by
  intro h
  have h2 : (finPiEquivOfEqOne k (if_pos (rfl : j = j))).symm (1 : k) = 0 := congrArg Prod.snd h
  have := congrArg (finPiEquivOfEqOne k (if_pos (rfl : j = j))) h2
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

/-- The `i`-generator is nonzero. -/
theorem genFst_ne_zero [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    genFst (k := k) i j c ≠ 0 := by
  intro h
  have h2 : (finPiEquivOfEqOne k (if_pos (rfl : i = i))).symm (1 : k) = 0 := congrArg Prod.fst h
  have := congrArg (finPiEquivOfEqOne k (if_pos (rfl : i = i))) h2
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

/-! ### The two normal forms are not isomorphic: indecomposability -/

/-- In a simple module a complementary pair is `(⊥, ⊤)` or `(⊤, ⊥)`. -/
private theorem isCompl_dichotomy {M : Type*} [AddCommGroup M] [Module k M]
    [IsSimpleModule k M] {A B : Submodule k M} (h : IsCompl A B) :
    (A = ⊥ ∧ B = ⊤) ∨ (A = ⊤ ∧ B = ⊥) := by
  rcases eq_bot_or_eq_top A with hA | hA
  · exact Or.inl ⟨hA, by rw [← h.sup_eq_top, hA, bot_sup_eq]⟩
  · exact Or.inr ⟨hA, by rw [← h.inf_eq_bot, hA, top_inf_eq]⟩

/-- Off the two supported vertices every subrepresentation of `twoRep i j c` is zero. -/
theorem eq_bot_of_ne [DecidableEq Q] {i j : Q} {c : (Σ a b : Q, (a ⟶ b)) → k}
    (W : ∀ v, Submodule k ((twoRep i j c).obj v)) {v : Q} (hvi : v ≠ i) (hvj : v ≠ j) :
    W v = ⊥ := by
  haveI := twoRep_obj_subsingleton c hvi hvj
  rw [Submodule.eq_bot_iff]
  intro x _
  exact Subsingleton.elim x 0

/-- The `i`-slot of `twoRep i j c` is one-dimensional when `i ≠ j`. -/
theorem finrank_twoRep_fst [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) : finrank k ((twoRep i j c).obj i) = 1 := by
  have h := dimVec_twoRep (k := k) i j c i
  rw [if_pos rfl, if_neg hij] at h
  exact h

/-- The `j`-slot of `twoRep i j c` is one-dimensional when `i ≠ j`. -/
theorem finrank_twoRep_snd [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) : finrank k ((twoRep i j c).obj j) = 1 := by
  have h := dimVec_twoRep (k := k) i j c j
  rw [if_pos rfl, if_neg (Ne.symm hij)] at h
  exact h

/-- **`twoRep i j c` is indecomposable** as soon as `i ≠ j` and some arrow `i → j` acts by a
nonzero scalar. Together with `twoRep_zero_not_isIndecomposable` this separates the two families
of normal forms. -/
theorem twoRep_isIndecomposable [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {e₀ : i ⟶ j} (hc : c ⟨i, j, e₀⟩ ≠ 0) :
    (twoRep i j c).IsIndecomposable := by
  haveI hsi : IsSimpleModule k ((twoRep (k := k) i j c).obj i) :=
    isSimpleModule_iff_finrank_eq_one.mpr (finrank_twoRep_fst hij c)
  haveI hsj : IsSimpleModule k ((twoRep (k := k) i j c).obj j) :=
    isSimpleModule_iff_finrank_eq_one.mpr (finrank_twoRep_snd hij c)
  -- The arrow `e₀` sends the (nonzero) `i`-generator to a nonzero multiple of the `j`-generator.
  have hmap : (twoRep i j c).mapLinear e₀ (genFst i j c) ≠ 0 := by
    rw [twoRep_mapLinear_genFst]
    exact smul_ne_zero hc (genSnd_ne_zero i j c)
  refine ⟨⟨i, Module.finrank_pos_iff.mp (by rw [finrank_twoRep_fst hij c]; norm_num)⟩, ?_⟩
  intro W₁ W₂ h1 h2 hcompl
  -- One-dimensionality at `i` and at `j` forces each `W` to be `⊥` or `⊤` there.
  rcases isCompl_dichotomy (hcompl i) with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
  · rcases isCompl_dichotomy (hcompl j) with ⟨hj1, _⟩ | ⟨_, hj2⟩
    · -- `W₁` is zero at both supported vertices, hence everywhere.
      refine Or.inl fun v => ?_
      by_cases hvi : v = i
      · exact hvi ▸ hi1
      by_cases hvj : v = j
      · exact hvj ▸ hj1
      exact eq_bot_of_ne W₁ hvi hvj
    · -- `W₂ i = ⊤` but `W₂ j = ⊥`: the arrow `e₀` breaks stability of `W₂`.
      exact absurd (by
        have hmem : genFst i j c ∈ W₂ i := by rw [hi2]; exact Submodule.mem_top
        have := h2 e₀ _ hmem
        rw [hj2, Submodule.mem_bot] at this
        exact this) hmap
  · rcases isCompl_dichotomy (hcompl j) with ⟨hj1, _⟩ | ⟨_, hj2⟩
    · -- `W₁ i = ⊤` but `W₁ j = ⊥`: the arrow `e₀` breaks stability of `W₁`.
      exact absurd (by
        have hmem : genFst i j c ∈ W₁ i := by rw [hi1]; exact Submodule.mem_top
        have := h1 e₀ _ hmem
        rw [hj1, Submodule.mem_bot] at this
        exact this) hmap
    · -- `W₂` is zero at both supported vertices, hence everywhere.
      refine Or.inr fun v => ?_
      by_cases hvi : v = i
      · exact hvi ▸ hi2
      by_cases hvj : v = j
      · exact hvj ▸ hj2
      exact eq_bot_of_ne W₂ hvi hvj


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

/-! ### Reading a representation off at its two supported vertices -/

/-- Transport a vertexwise linear equivalence along an equality of vertices. Using this instead
of a bare `▸` keeps the rewrite from also renaming the *normal form's* vertex parameters. -/
def transportEquivAt {ρ σ : QuiverRepresentation k Q} {v w : Q} (h : v = w)
    (φ : ρ.obj w ≃ₗ[k] σ.obj w) : ρ.obj v ≃ₗ[k] σ.obj v := by
  subst h; exact φ

@[simp] theorem transportEquivAt_rfl {ρ σ : QuiverRepresentation k Q} {v : Q}
    (φ : ρ.obj v ≃ₗ[k] σ.obj v) : transportEquivAt (rfl : v = v) φ = φ := rfl

/-- The coefficient family of a representation `ρ`, read off through trivializations `α` at `i`
and `β` at `j`: the arrow `e : i ⟶ j` gets the scalar by which it acts on the chosen generator.
Only the values on arrows `i → j` matter, so all other arrows are sent to `0`. -/
noncomputable def coeffOf [DecidableEq Q] {ρ : QuiverRepresentation k Q} {i j : Q}
    (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k) : (Σ a b : Q, (a ⟶ b)) → k :=
  fun p =>
    if h : p.1 = i then
      (if h' : p.2.1 = j then β (h' ▸ ρ.mapLinear p.2.2 (h.symm ▸ α.symm 1)) else 0)
    else 0

theorem coeffOf_apply [DecidableEq Q] {ρ : QuiverRepresentation k Q} {i j : Q}
    (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k) (e : i ⟶ j) :
    coeffOf α β ⟨i, j, e⟩ = β (ρ.mapLinear e (α.symm 1)) := by
  simp [coeffOf]

/-- The vertexwise trivialization putting a representation supported on two distinct vertices
`i ≠ j` into normal form: `α` at `i`, `β` at `j`, and the unique map between trivial spaces
elsewhere. -/
noncomputable def normalFormEquivAt [DecidableEq Q] {ρ : QuiverRepresentation k Q} {i j : Q}
    (hij : i ≠ j) (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k)
    (htriv : ∀ v, v ≠ i → v ≠ j → Subsingleton (ρ.obj v))
    (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    ρ.obj v ≃ₗ[k] (twoRep i j c).obj v :=
  if hv : v = i then
    transportEquivAt hv (α.trans ((finPiEquivOfEqOne k (if_pos rfl)).symm.trans
      (prodTrivRight k (finPi_subsingleton (k := k) (if_neg hij))).symm))
  else if hv' : v = j then
    transportEquivAt hv' (β.trans ((finPiEquivOfEqOne k (if_pos rfl)).symm.trans
      (prodTrivLeft k (finPi_subsingleton (k := k) (if_neg (Ne.symm hij)))).symm))
  else subsingletonEquiv k (htriv v hv hv') (twoRep_obj_subsingleton c hv hv')

section NormalFormEquivAt

variable [DecidableEq Q] {ρ : QuiverRepresentation k Q} {i j : Q} (hij : i ≠ j)
  (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k)
  (htriv : ∀ v, v ≠ i → v ≠ j → Subsingleton (ρ.obj v)) (c : (Σ a b : Q, (a ⟶ b)) → k)

/-- At `i` the trivialization is `α`, read in the first slot. -/
theorem normalFormEquivAt_fst (x : ρ.obj i) :
    (normalFormEquivAt hij α β htriv c i x).1 = (finPiEquivOfEqOne k (if_pos rfl)).symm (α x) := by
  rw [normalFormEquivAt, dif_pos (rfl : i = i), transportEquivAt_rfl]
  rfl

/-- At `j` the trivialization is `β`, read in the second slot. -/
theorem normalFormEquivAt_snd (y : ρ.obj j) :
    (normalFormEquivAt hij α β htriv c j y).2 = (finPiEquivOfEqOne k (if_pos rfl)).symm (β y) := by
  rw [normalFormEquivAt, dif_neg (Ne.symm hij), dif_pos (rfl : j = j), transportEquivAt_rfl]
  rfl

end NormalFormEquivAt

/-- **The normal form of a representation supported on two distinct vertices.** If `ρ` is
one-dimensional at `i` and at `j` (`i ≠ j`), trivial elsewhere, and every arrow other than those
from `i` to `j` acts by zero, then `ρ` is isomorphic to `twoRep i j (coeffOf α β)`. -/
theorem nonempty_equiv_twoRep [DecidableEq Q] {ρ : QuiverRepresentation k Q} {i j : Q}
    (hij : i ≠ j) (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k)
    (htriv : ∀ v, v ≠ i → v ≠ j → Subsingleton (ρ.obj v))
    (hzero : ∀ {a b : Q} (e : a ⟶ b), a ≠ i ∨ b ≠ j → ρ.mapLinear e = 0) :
    Nonempty (QuiverRepresentationEquiv k Q ρ (twoRep i j (coeffOf α β))) := by
  refine ⟨⟨normalFormEquivAt hij α β htriv (coeffOf α β), ?_⟩⟩
  intro a b e x
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      refine Prod.ext ?_ ?_
      · -- The first slot at `j` is trivial, since `j ≠ i`.
        haveI := finPi_subsingleton (k := k) (if_neg (Ne.symm hij) : (if j = i then 1 else 0) = 0)
        exact Subsingleton.elim _ _
      · -- The second slot carries the whole content: `β (ρ_e x) = c ⟨i, j, e⟩ * α x`.
        have hfin : (if j = j then 1 else 0) = 1 := if_pos rfl
        apply (finPiEquivOfEqOne k hfin).injective
        rw [normalFormEquivAt_snd, twoRep_mapLinear_apply_snd, LinearEquiv.apply_symm_apply,
          map_smul, normalFormEquivAt_fst,
          finPiEquivOfEqOne_truncMap (if_pos (rfl : i = i)) hfin, LinearEquiv.apply_symm_apply,
          smul_eq_mul, coeffOf_apply]
        have hx : ρ.mapLinear e x = α x • ρ.mapLinear e (α.symm (1 : k)) := by
          rw [← map_smul]
          congr 1
          rw [← map_smul, smul_eq_mul, mul_one, α.symm_apply_apply]
        rw [hx, map_smul, smul_eq_mul, mul_comm]
    · -- `b ≠ j`: the normal form's target slot is zero-dimensional, and `ρ_e = 0`.
      rw [hzero e (Or.inr hb), LinearMap.zero_apply, map_zero]
      symm
      refine Prod.ext rfl ?_
      rw [twoRep_mapLinear_apply_snd, truncMap_eq_zero_of_target (if_neg hb),
        LinearMap.zero_apply, smul_zero]
      rfl
  · -- `a ≠ i`: the normal form's source slot is zero-dimensional, and `ρ_e = 0`.
    rw [hzero e (Or.inl ha), LinearMap.zero_apply, map_zero]
    symm
    refine Prod.ext rfl ?_
    rw [twoRep_mapLinear_apply_snd, truncMap_eq_zero_of_source (if_neg ha),
      LinearMap.zero_apply, smul_zero]
    rfl

/-- Two representations all of whose arrow maps vanish and whose dimension vectors agree are
isomorphic. -/
theorem nonempty_equiv_of_mapLinear_eq_zero (ρ σ : QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [∀ v, Module.Free k (σ.obj v)] [∀ v, Module.Finite k (σ.obj v)]
    (hρ : ∀ {a b : Q} (e : a ⟶ b), ρ.mapLinear e = 0)
    (hσ : ∀ {a b : Q} (e : a ⟶ b), σ.mapLinear e = 0)
    (hdim : ∀ v, dimVec ρ v = dimVec σ v) :
    Nonempty (QuiverRepresentationEquiv k Q ρ σ) := by
  have hE : ∀ v, Nonempty (ρ.obj v ≃ₗ[k] σ.obj v) := by
    intro v
    letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
    letI : AddCommGroup (σ.obj v) := Module.addCommMonoidToAddCommGroup k
    exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hdim v)
  refine ⟨⟨fun v => (hE v).some, ?_⟩⟩
  intro a b e x
  rw [hρ e, LinearMap.zero_apply, map_zero, hσ e, LinearMap.zero_apply]

/-! ### Support of a two-dimensional representation -/

/-- A vertex space of dimension `0` is trivial. -/
theorem subsingleton_of_dimVec_eq_zero {ρ : QuiverRepresentation k Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] {v : Q}
    (h : dimVec ρ v = 0) : Subsingleton (ρ.obj v) := by
  letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  have h1 : 0 < finrank k (ρ.obj v) := Module.finrank_pos_iff.mpr hns
  have h2 : finrank k (ρ.obj v) = 0 := h
  omega

/-- A vertex space of dimension `1` is the ground field. -/
theorem nonempty_linearEquiv_of_dimVec_eq_one {ρ : QuiverRepresentation k Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] {v : Q}
    (h : dimVec ρ v = 1) : Nonempty (ρ.obj v ≃ₗ[k] k) := by
  letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
  refine FiniteDimensional.nonempty_linearEquiv_of_finrank_eq ?_
  rw [Module.finrank_self]
  exact h

/-- A dimension vector on a finite vertex set summing to `2` is either `2` at a single vertex or
`1` at each of two distinct vertices. -/
theorem support_of_sum_eq_two {Q : Type*} [Fintype Q] (d : Q → ℕ) (h2 : ∑ v, d v = 2) :
    (∃ i, d i = 2 ∧ ∀ v, v ≠ i → d v = 0) ∨
      (∃ i j, i ≠ j ∧ d i = 1 ∧ d j = 1 ∧ ∀ v, v ≠ i → v ≠ j → d v = 0) := by
  classical
  set S : Finset Q := Finset.univ.filter (fun v => d v ≠ 0) with hS
  have hmemS : ∀ v, v ∈ S ↔ d v ≠ 0 := by intro v; simp [hS]
  have hout : ∀ v, v ∉ S → d v = 0 := by
    intro v hv
    by_contra h
    exact hv ((hmemS v).mpr h)
  have hsum : ∑ v ∈ S, d v = 2 :=
    (Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => hout x hx)).trans h2
  have hcard : S.card ≤ 2 := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr ((hmemS v).mp hv)
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hcard1 : 1 ≤ S.card := Finset.card_pos.mpr hne
  interval_cases h : S.card
  · -- `S = {i}`
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    refine Or.inl ⟨i, ?_, ?_⟩
    · rw [hi, Finset.sum_singleton] at hsum; exact hsum
    · intro v hv
      exact hout v (by rw [hi]; simpa using hv)
  · -- `S = {i, j}` with `i ≠ j`
    obtain ⟨i, j, hij, hS2⟩ := Finset.card_eq_two.mp h
    rw [hS2, Finset.sum_pair hij] at hsum
    have hi : d i ≠ 0 := (hmemS i).mp (by rw [hS2]; simp)
    have hj : d j ≠ 0 := (hmemS j).mp (by rw [hS2]; simp)
    refine Or.inr ⟨i, j, hij, by omega, by omega, fun v hvi hvj => ?_⟩
    exact hout v (by rw [hS2]; simp [hvi, hvj])

end Problem3_9_3

end Etingof
