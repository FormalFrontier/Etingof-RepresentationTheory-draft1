import EtingofRepresentationTheory.Chapter3.Problem3_9_3

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
* `twoRepEquivSmul` and `exists_smul_of_equiv_twoRep` -- the **parameter criterion**: for
  `i ≠ j`, `twoRep i j c ≅ twoRep i j c'` if and only if `c'` and `c` agree up to a single
  nonzero scalar on the arrows `i → j`. This is where parallel arrows enter: the
  isomorphism classes of indecomposable two-dimensional representations supported on `i ≠ j` are
  the points of the projective space `ℙ(k^{#(i ⟶ j)})`, so a quiver with `m` parallel arrows
  `i → j` has an `(m-1)`-dimensional family of them, not just one.
* `vertices_eq_of_equiv_twoRep` -- the **support criterion**: the unordered pair `{i, j}` is an
  isomorphism invariant.
* `two_dim_classification_of_normalForm` -- the old necessary-condition disjunction
  `Problem3_9_3.two_dim_classification`, recovered verbatim as a corollary of the normal form
  (its original standalone proof is retained in `Problem3_9_3.lean`, which this file imports).
-/

namespace Etingof

open Module (finrank)

variable {k Q : Type*} [Field k] [Quiver Q]

/-! ### Basic API for isomorphism of quiver representations

`QuiverRepresentationEquiv` (Chapter 2, Theorem 2.1.2) had no groupoid API.
`symm` and `trans` come from `Chapter2/Theorem2_1_2_General.lean`; `refl` and the
dimension-vector invariance are added here. -/

namespace QuiverRepresentationEquiv

variable {ρ σ τ : QuiverRepresentation k Q}

/-- The identity isomorphism. -/
def refl (ρ : QuiverRepresentation k Q) : QuiverRepresentationEquiv k Q ρ ρ where
  equivAt _ := LinearEquiv.refl k _
  commutes _ _ := rfl

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

/-! ### Exhaustiveness: every two-dimensional representation is a normal form -/

/-- **Classification of the two-dimensional representations of a path algebra.** Let `Q` be a
finite quiver without oriented cycles and `ρ` a representation of total dimension `2`. Then `ρ`
is *isomorphic* to a normal form, in exactly one of two ways:

* `ρ ≅ twoRep i j 0 ≅ S_i ⊕ S_j` for a (possibly equal) pair of vertices -- the decomposable
  case (`twoRep_zero_not_isIndecomposable`); or
* `ρ ≅ twoRep i j c` with `i ≠ j` and some arrow `e₀ : i ⟶ j` acting by a nonzero scalar -- the
  indecomposable case (`twoRep_isIndecomposable`).

This is the isomorphism-class statement that `two_dim_classification` only approximated by a
dimension/map-condition disjunction; that disjunction is recovered below as
`two_dim_classification_of_normalForm`. -/
theorem two_dim_normalForm [DecidableEq Q] [Fintype Q]
    (hQ : NoOrientedCycles Q) (ρ : QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, dimVec ρ v = 2) :
    (∃ i j : Q, Nonempty (QuiverRepresentationEquiv k Q ρ
        (twoRep i j (0 : (Σ a b : Q, (a ⟶ b)) → k))))
      ∨ (∃ (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (e₀ : i ⟶ j),
          i ≠ j ∧ c ⟨i, j, e₀⟩ ≠ 0 ∧
            Nonempty (QuiverRepresentationEquiv k Q ρ (twoRep i j c))) := by
  classical
  -- Acyclicity rules out loops and 2-cycles.
  have hnoloop : ∀ v : Q, IsEmpty (v ⟶ v) := by
    intro v
    rw [isEmpty_iff]
    intro a
    have h := congrArg Quiver.Path.length (hQ v (Quiver.Path.nil.cons a))
    simp [Quiver.Path.length_cons] at h
  have hno2 : ∀ {u w : Q}, (u ⟶ w) → IsEmpty (w ⟶ u) := by
    intro u w e
    rw [isEmpty_iff]
    intro f
    have h := congrArg Quiver.Path.length (hQ u ((Quiver.Path.nil.cons e).cons f))
    simp [Quiver.Path.length_cons] at h
  -- The indecomposable case, packaged so it can be applied to either orientation.
  have key : ∀ u w : Q, u ≠ w → dimVec ρ u = 1 → dimVec ρ w = 1 →
      (∀ v, v ≠ u → v ≠ w → dimVec ρ v = 0) → ∀ e₀ : u ⟶ w, ρ.mapLinear e₀ ≠ 0 →
      (∃ (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (e : i ⟶ j),
        i ≠ j ∧ c ⟨i, j, e⟩ ≠ 0 ∧
          Nonempty (QuiverRepresentationEquiv k Q ρ (twoRep i j c))) := by
    intro u w huw hu1 hw1 h0 e₀ hne0
    have htriv : ∀ v, v ≠ u → v ≠ w → Subsingleton (ρ.obj v) :=
      fun v h1 h2 => subsingleton_of_dimVec_eq_zero (h0 v h1 h2)
    obtain ⟨α⟩ := nonempty_linearEquiv_of_dimVec_eq_one hu1
    obtain ⟨β⟩ := nonempty_linearEquiv_of_dimVec_eq_one hw1
    -- Every arrow other than the ones from `u` to `w` has a trivial source or target.
    have hzero : ∀ {a b : Q} (e : a ⟶ b), a ≠ u ∨ b ≠ w → ρ.mapLinear e = 0 := by
      intro a b e hd
      by_cases ha : a = u
      · subst a
        have hbw : b ≠ w := hd.resolve_left fun h => h rfl
        have hbu : b ≠ u := fun h => (hnoloop u).false (h ▸ e)
        haveI := htriv b hbu hbw
        exact LinearMap.ext fun _ => Subsingleton.elim _ _
      · by_cases haw : a = w
        · subst a
          have hbu : b ≠ u := fun h => (hno2 e₀).false (h ▸ e)
          have hbw : b ≠ w := fun h => (hnoloop w).false (h ▸ e)
          haveI := htriv b hbu hbw
          exact LinearMap.ext fun _ => Subsingleton.elim _ _
        · haveI := htriv a ha haw
          exact LinearMap.ext fun y => by
            rw [Subsingleton.elim y 0, map_zero, LinearMap.zero_apply]
    -- The coefficient of `e₀` is nonzero: otherwise `ρ_{e₀}` kills a generator, hence vanishes.
    have hc : coeffOf α β ⟨u, w, e₀⟩ ≠ 0 := by
      rw [coeffOf_apply]
      intro h
      have h0' : ρ.mapLinear e₀ (α.symm 1) = 0 := by
        apply β.injective
        rw [h, map_zero]
      refine hne0 (LinearMap.ext fun y => ?_)
      have hy : ρ.mapLinear e₀ y = α y • ρ.mapLinear e₀ (α.symm (1 : k)) := by
        rw [← map_smul]
        congr 1
        rw [← map_smul, smul_eq_mul, mul_one, α.symm_apply_apply]
      rw [hy, h0', smul_zero, LinearMap.zero_apply]
    exact ⟨u, w, coeffOf α β, e₀, huw, hc, nonempty_equiv_twoRep huw α β htriv hzero⟩
  rcases support_of_sum_eq_two (dimVec ρ) h2 with ⟨i, hi2, hi0⟩ | ⟨i, j, hij, hi1, hj1, h0⟩
  · -- Both dimensions sit at one vertex `i`; with no loops every arrow map vanishes.
    have hmz : ∀ {a b : Q} (e : a ⟶ b), ρ.mapLinear e = 0 := by
      intro a b e
      by_cases ha : a = i
      · subst a
        haveI := subsingleton_of_dimVec_eq_zero (hi0 b fun h => (hnoloop i).false (h ▸ e))
        exact LinearMap.ext fun _ => Subsingleton.elim _ _
      · haveI := subsingleton_of_dimVec_eq_zero (hi0 a ha)
        exact LinearMap.ext fun y => by
          rw [Subsingleton.elim y 0, map_zero, LinearMap.zero_apply]
    refine Or.inl ⟨i, i, nonempty_equiv_of_mapLinear_eq_zero ρ _ hmz
      (twoRep_zero_mapLinear i i) fun v => ?_⟩
    rw [dimVec_twoRep]
    by_cases hv : v = i
    · subst v
      rw [if_pos rfl]
      omega
    · rw [if_neg hv]
      have := hi0 v hv
      omega
  · -- Two distinct one-dimensional vertices.
    by_cases hall : ∀ (a b : Q) (e : a ⟶ b), ρ.mapLinear e = 0
    · -- All arrows act by zero: `ρ ≅ S_i ⊕ S_j`.
      refine Or.inl ⟨i, j, nonempty_equiv_of_mapLinear_eq_zero ρ _ (fun e => hall _ _ e)
        (twoRep_zero_mapLinear i j) fun v => ?_⟩
      rw [dimVec_twoRep]
      by_cases hvi : v = i
      · subst v
        rw [if_pos rfl, if_neg hij]
        omega
      · by_cases hvj : v = j
        · subst v
          rw [if_neg (Ne.symm hij), if_pos rfl]
          omega
        · rw [if_neg hvi, if_neg hvj]
          have := h0 v hvi hvj
          omega
    · -- Some arrow acts nontrivially; its endpoints must be `i` and `j` in one of the two orders.
      push Not at hall
      obtain ⟨a, b, e, hne0⟩ := hall
      have hda : dimVec ρ a ≠ 0 := by
        intro h
        haveI := subsingleton_of_dimVec_eq_zero h
        exact hne0 (LinearMap.ext fun y => by
          rw [Subsingleton.elim y 0, map_zero, LinearMap.zero_apply])
      have hdb : dimVec ρ b ≠ 0 := by
        intro h
        haveI := subsingleton_of_dimVec_eq_zero h
        exact hne0 (LinearMap.ext fun _ => Subsingleton.elim _ _)
      have hain : a = i ∨ a = j := by
        by_cases h1 : a = i
        · exact Or.inl h1
        by_cases h2 : a = j
        · exact Or.inr h2
        exact absurd (h0 a h1 h2) hda
      have hbin : b = i ∨ b = j := by
        by_cases h1 : b = i
        · exact Or.inl h1
        by_cases h2 : b = j
        · exact Or.inr h2
        exact absurd (h0 b h1 h2) hdb
      have hab : a ≠ b := fun h => (hnoloop a).false (h ▸ e)
      rcases hain with hai | haj
      · subst a
        rcases hbin with hbi | hbj
        · exact absurd hbi.symm hab
        · subst b
          exact Or.inr (key i j hij hi1 hj1 h0 e hne0)
      · subst a
        rcases hbin with hbi | hbj
        · subst b
          exact Or.inr (key j i (Ne.symm hij) hj1 hi1 (fun v h1 h2 => h0 v h2 h1) e hne0)
        · exact absurd hbj.symm hab

/-! ### Distinguishing the isomorphism classes

Three invariants separate the normal forms: the unordered pair of supported vertices, the
indecomposability dichotomy, and -- within the indecomposable family supported on `i ≠ j` -- the
coefficient vector up to a single nonzero scalar. -/

/-- Rescaling all coefficients by a nonzero scalar `t` gives an isomorphic normal form: scale the
`j`-slot by `t` and leave the `i`-slot alone. -/
noncomputable def twoRepEquivSmul [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k)
    {t : k} (ht : t ≠ 0) :
    QuiverRepresentationEquiv k Q (twoRep i j c) (twoRep i j fun p => t * c p) where
  equivAt v := (LinearEquiv.refl k (Fin (if v = i then 1 else 0) → k)).prodCongr
    (LinearEquiv.smulOfNeZero k (Fin (if v = j then 1 else 0) → k) t ht)
  commutes e x := by
    refine Prod.ext rfl ?_
    change t • (((twoRep i j c).mapLinear e x).2) = _
    rw [twoRep_mapLinear_apply_snd, smul_smul]
    rfl

/-- **The parameter criterion.** An isomorphism between two normal forms supported on `i ≠ j`
forces the two coefficient vectors to agree, on the arrows `i → j`, up to one nonzero scalar.
Together with `twoRepEquivSmul` this says the indecomposable normal forms supported on `i ≠ j`
are classified by `k^{#(i ⟶ j)}` modulo scaling: a single point when there is exactly one arrow
`i → j`, and a projective space of positive dimension as soon as there are parallel arrows. -/
theorem exists_smul_of_equiv_twoRep [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c c' : (Σ a b : Q, (a ⟶ b)) → k)
    (φ : QuiverRepresentationEquiv k Q (twoRep i j c) (twoRep i j c')) :
    ∃ t : k, t ≠ 0 ∧ ∀ e : i ⟶ j, c' ⟨i, j, e⟩ = t * c ⟨i, j, e⟩ := by
  haveI hsub_i : Subsingleton (Fin (if i = j then 1 else 0) → k) :=
    finPi_subsingleton (if_neg hij)
  haveI hsub_j : Subsingleton (Fin (if j = i then 1 else 0) → k) :=
    finPi_subsingleton (if_neg (Ne.symm hij))
  have hi1 : (if i = i then 1 else 0) = 1 := if_pos rfl
  have hj1 : (if j = j then 1 else 0) = 1 := if_pos rfl
  -- `φ` acts on the `i`-slot by a scalar `gi` and on the `j`-slot by a scalar `gj`.
  obtain ⟨gi, hgi⟩ : ∃ g : k, finPiEquivOfEqOne k hi1 (φ.equivAt i (genFst i j c)).1 = g :=
    ⟨_, rfl⟩
  obtain ⟨gj, hgj⟩ : ∃ g : k, finPiEquivOfEqOne k hj1 (φ.equivAt j (genSnd i j c)).2 = g :=
    ⟨_, rfl⟩
  have hgi0 : gi ≠ 0 := by
    intro h
    have hz : φ.equivAt i (genFst i j c) = 0 := by
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      apply (finPiEquivOfEqOne k hi1).injective
      rw [hgi, h]
      exact (map_zero _).symm
    exact genFst_ne_zero i j c ((φ.equivAt i).injective (hz.trans (map_zero _).symm))
  have hgj0 : gj ≠ 0 := by
    intro h
    have hz : φ.equivAt j (genSnd i j c) = 0 := by
      refine Prod.ext (Subsingleton.elim _ _) ?_
      apply (finPiEquivOfEqOne k hj1).injective
      rw [hgj, h]
      exact (map_zero _).symm
    exact genSnd_ne_zero i j c ((φ.equivAt j).injective (hz.trans (map_zero _).symm))
  -- Compare the two sides of `commutes` on the `i`-generator, read in the `j`-slot.
  have hrel : ∀ e : i ⟶ j, c ⟨i, j, e⟩ * gj = c' ⟨i, j, e⟩ * gi := by
    intro e
    have hcomm := φ.commutes e (genFst i j c)
    rw [twoRep_mapLinear_genFst, map_smul] at hcomm
    have h4 : finPiEquivOfEqOne k hj1 (c ⟨i, j, e⟩ • (φ.equivAt j (genSnd i j c)).2)
        = finPiEquivOfEqOne k hj1 (c' ⟨i, j, e⟩ •
            truncMap k (if i = i then 1 else 0) (if j = j then 1 else 0)
              (φ.equivAt i (genFst i j c)).1) :=
      congrArg (fun y => finPiEquivOfEqOne k hj1 (Prod.snd y)) hcomm
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      finPiEquivOfEqOne_truncMap hi1 hj1, hgi, hgj] at h4
    exact h4
  refine ⟨gj * gi⁻¹, mul_ne_zero hgj0 (inv_ne_zero hgi0), fun e => ?_⟩
  calc c' ⟨i, j, e⟩ = c' ⟨i, j, e⟩ * gi * gi⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hgi0, mul_one]
    _ = c ⟨i, j, e⟩ * gj * gi⁻¹ := by rw [hrel e]
    _ = gj * gi⁻¹ * c ⟨i, j, e⟩ := by ring

/-- **The support criterion.** The unordered pair of supported vertices is an isomorphism
invariant of the normal form. -/
theorem vertices_eq_of_equiv_twoRep [DecidableEq Q] {i j i' j' : Q}
    (c c' : (Σ a b : Q, (a ⟶ b)) → k)
    (φ : QuiverRepresentationEquiv k Q (twoRep i j c) (twoRep i' j' c')) :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  have hd : ∀ v : Q, (if v = i then 1 else 0) + (if v = j then 1 else 0)
      = (if v = i' then 1 else 0) + (if v = j' then 1 else 0) := by
    intro v
    rw [← dimVec_twoRep i j c v, ← dimVec_twoRep i' j' c' v]
    exact φ.dimVec_eq v
  have hi : i = i' ∨ i = j' := by
    by_contra hcon
    have h1 := hd i
    rw [if_pos rfl, if_neg (fun h => hcon (Or.inl h)), if_neg (fun h => hcon (Or.inr h))] at h1
    omega
  have hj : j = i' ∨ j = j' := by
    by_contra hcon
    have h1 := hd j
    rw [if_pos rfl, if_neg (fun h => hcon (Or.inl h)), if_neg (fun h => hcon (Or.inr h))] at h1
    omega
  rcases hi with hi | hi
  · refine Or.inl ⟨hi, ?_⟩
    rcases hj with hj | hj
    · -- `j = i' = i`, so `i = j` and the whole dimension sits at one vertex.
      have hij : i = j := hi.trans hj.symm
      have h1 := hd i
      rw [if_pos rfl, if_pos hij, if_pos hi] at h1
      have hij' : i = j' := by
        by_contra hne
        rw [if_neg hne] at h1
        omega
      exact hij.symm.trans hij'
    · exact hj
  · refine Or.inr ⟨hi, ?_⟩
    rcases hj with hj | hj
    · exact hj
    · -- `j = j' = i`, so `i = j` again.
      have hij : i = j := hi.trans hj.symm
      have h1 := hd i
      rw [if_pos rfl, if_pos hij, if_pos hi] at h1
      have hij' : i = i' := by
        by_contra hne
        rw [if_neg hne] at h1
        omega
      exact hij.symm.trans hij'

/-! ### The old necessary condition, as a corollary -/

/-- Indecomposability transports along an isomorphism of quiver representations. -/
theorem isIndecomposable_of_equiv {ρ σ : QuiverRepresentation k Q}
    (φ : QuiverRepresentationEquiv k Q ρ σ) (h : ρ.IsIndecomposable) : σ.IsIndecomposable := by
  obtain ⟨⟨v₀, hv₀⟩, hdec⟩ := h
  refine ⟨⟨v₀, ?_⟩, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hv₀
    exact ⟨φ.equivAt v₀ x, φ.equivAt v₀ y, fun h => hxy ((φ.equivAt v₀).injective h)⟩
  intro W₁ W₂ h1 h2 hcompl
  -- Pull the two subrepresentations back along `φ`.
  have hpull : ∀ (W : ∀ v, Submodule k (σ.obj v)),
      (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, σ.mapLinear e x ∈ W b) →
      ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ Submodule.comap (φ.equivAt a).toLinearMap (W a),
        ρ.mapLinear e x ∈ Submodule.comap (φ.equivAt b).toLinearMap (W b) := by
    intro W hW a b e x hx
    rw [Submodule.mem_comap] at hx ⊢
    rw [LinearEquiv.coe_coe, φ.commutes e]
    exact hW e _ hx
  have hcompl' : ∀ v, IsCompl (Submodule.comap (φ.equivAt v).toLinearMap (W₁ v))
      (Submodule.comap (φ.equivAt v).toLinearMap (W₂ v)) := by
    intro v
    exact (Submodule.orderIsoMapComap (φ.equivAt v)).symm.isCompl (hcompl v)
  have hcomap_inj : ∀ (v : Q) (W : Submodule k (σ.obj v)),
      Submodule.comap (φ.equivAt v).toLinearMap W = ⊥ → W = ⊥ := by
    intro v W hW
    have := (Submodule.orderIsoMapComap (φ.equivAt v)).symm.injective
      (a₁ := W) (a₂ := ⊥) (by simpa using hW)
    exact this
  rcases hdec _ _ (hpull W₁ h1) (hpull W₂ h2) hcompl' with hb | hb
  · exact Or.inl fun v => hcomap_inj v (W₁ v) (hb v)
  · exact Or.inr fun v => hcomap_inj v (W₂ v) (hb v)

/-- An arrow with a nonzero coefficient acts bijectively on the normal form `twoRep i j c`
(`i ≠ j`): both slots are one-dimensional. -/
theorem twoRep_mapLinear_bijective [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {e : i ⟶ j} (hc : c ⟨i, j, e⟩ ≠ 0) :
    Function.Bijective ((twoRep i j c).mapLinear e) := by
  haveI hsi : IsSimpleModule k ((twoRep (k := k) i j c).obj i) :=
    isSimpleModule_iff_finrank_eq_one.mpr (finrank_twoRep_fst hij c)
  haveI hsj : IsSimpleModule k ((twoRep (k := k) i j c).obj j) :=
    isSimpleModule_iff_finrank_eq_one.mpr (finrank_twoRep_snd hij c)
  have hne : (twoRep i j c).mapLinear e ≠ 0 := by
    intro h
    have hg := twoRep_mapLinear_genFst i j c e
    rw [h, LinearMap.zero_apply] at hg
    exact smul_ne_zero hc (genSnd_ne_zero i j c) hg.symm
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    rcases eq_bot_or_eq_top (LinearMap.ker ((twoRep i j c).mapLinear e)) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hne
  · rw [← LinearMap.range_eq_top]
    rcases eq_bot_or_eq_top (LinearMap.range ((twoRep i j c).mapLinear e)) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hne
    · exact h

/-- The necessary-condition disjunction of `Problem3_9_3.two_dim_classification`, now a corollary
of the normal-form classification: the decomposable branch comes from
`twoRep_zero_not_isIndecomposable`, the bijective-arrow branch from
`twoRep_mapLinear_bijective`. -/
theorem two_dim_classification_of_normalForm [Fintype Q]
    (hQ : NoOrientedCycles Q) (ρ : QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, dimVec ρ v = 2) :
    (¬ ρ.IsIndecomposable)
      ∨ (∃ (i j : Q) (a : i ⟶ j), i ≠ j ∧ Function.Bijective (ρ.mapLinear a)) := by
  classical
  rcases two_dim_normalForm hQ ρ h2 with ⟨i, j, ⟨φ⟩⟩ | ⟨i, j, c, e₀, hij, hc, ⟨φ⟩⟩
  · exact Or.inl fun h => twoRep_zero_not_isIndecomposable i j (isIndecomposable_of_equiv φ h)
  · refine Or.inr ⟨i, j, e₀, hij, ?_⟩
    have hcomp : ∀ x, ρ.mapLinear e₀ x =
        (φ.equivAt j).symm ((twoRep i j c).mapLinear e₀ (φ.equivAt i x)) := by
      intro x
      rw [← φ.commutes e₀, LinearEquiv.symm_apply_apply]
    have hbij := twoRep_mapLinear_bijective hij c hc
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · refine (φ.equivAt i).injective (hbij.1 ((φ.equivAt j).symm.injective ?_))
      rw [← hcomp, ← hcomp]
      exact hxy
    · obtain ⟨z, hz⟩ := hbij.2 (φ.equivAt j y)
      obtain ⟨x, hx⟩ := (φ.equivAt i).surjective z
      exact ⟨x, by rw [hcomp, hx, hz, LinearEquiv.symm_apply_apply]⟩

end Problem3_9_3

end Etingof
