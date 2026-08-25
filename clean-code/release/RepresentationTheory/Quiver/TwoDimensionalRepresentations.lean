/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.AuxiliaryConstructions
import RepresentationTheory.Alignment.Attribute

/-!
# Two-dimensional quiver representations

Normal forms and auxiliary classification results for two-dimensional representations of finite acyclic quivers.
-/

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams (AuxiliaryQuiverModuleData)
open RepresentationTheory.CategoryTheory.QuiverLinearMaps (AuxiliaryQuiverEquivData)
open RepresentationTheory.Quiver.Auxiliary (auxiliaryObjectAtVertex auxiliaryVertexValue)
open RepresentationTheory.Quiver.AuxiliaryConstructions (HasAuxiliaryQuiverProperty)

open Module (finrank)

variable {k Q : Type*} [Field k] [Quiver Q]

namespace RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData

variable {ρ σ τ : AuxiliaryQuiverModuleData k Q}

/-- The reflexive displayed equivalence of a quiver representation with itself. -/
def refl (ρ : AuxiliaryQuiverModuleData k Q) : AuxiliaryQuiverEquivData k Q ρ ρ where
  app _ := LinearEquiv.refl k _
  naturality _ _ := rfl

/-- Equivalent quiver representations have equal displayed dimensions at every vertex. -/
theorem dimension_eq (φ : AuxiliaryQuiverEquivData k Q ρ σ) (v : Q) :
    auxiliaryVertexValue ρ v = auxiliaryVertexValue σ v := by
  letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
  letI : AddCommGroup (σ.obj v) := Module.addCommMonoidToAddCommGroup k
  exact (φ.app v).finrank_eq

end RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverEquivData

namespace RepresentationTheory.Quiver.TwoDimensionalRepresentations

/-- An auxiliary linear map between field-valued function spaces on finite types. -/
def auxiliaryFinFunctionLinearMap (k : Type*) [Field k] (p q : ℕ) : (Fin p → k) →ₗ[k] (Fin q → k) where
  toFun x i := if h : (i : ℕ) < p then x ⟨i, h⟩ else 0
  map_add' x y := by funext i; by_cases h : (i : ℕ) < p <;> simp [h]
  map_smul' a x := by funext i; by_cases h : (i : ℕ) < p <;> simp [h]

/-- An auxiliary evaluation formula for the linear map between finite function spaces. -/
theorem auxiliaryFinFunctionLinearMap_apply (p q : ℕ) (x : Fin p → k) (i : Fin q) :
    auxiliaryFinFunctionLinearMap k p q x i = if h : (i : ℕ) < p then x ⟨i, h⟩ else 0 := rfl

/-- The auxiliary map is zero when its source cardinal parameter is zero. -/
theorem auxiliaryFinFunctionLinearMap_eq_zero_of_source_eq_zero {p q : ℕ} (hp : p = 0) : auxiliaryFinFunctionLinearMap k p q = 0 := by
  subst hp
  refine LinearMap.ext fun x => funext fun i => ?_
  rw [auxiliaryFinFunctionLinearMap_apply, dif_neg (by omega), LinearMap.zero_apply, Pi.zero_apply]

/-- The auxiliary map is zero when its target cardinal parameter is zero. -/
theorem auxiliaryFinFunctionLinearMap_eq_zero_of_target_eq_zero {p q : ℕ} (hq : q = 0) : auxiliaryFinFunctionLinearMap k p q = 0 := by
  subst hq
  exact LinearMap.ext fun x => funext fun i => i.elim0

/-- The linear equivalence from functions on a one-element finite type to the base field. -/
def finOneLinearEquiv (k : Type*) [Field k] {p : ℕ} (hp : p = 1) : (Fin p → k) ≃ₗ[k] k where
  toFun x := x ⟨0, by omega⟩
  invFun t := fun _ => t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by subst hp; funext i; exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- The inverse one-coordinate equivalence sends a scalar to the constant function with that value. -/
@[simp] theorem finOneLinearEquiv_symm_apply {p : ℕ} (hp : p = 1) (t : k) (i : Fin p) :
    (finOneLinearEquiv k hp).symm t i = t := rfl

/-- The auxiliary linear map between one-coordinate function spaces preserves the scalar selected by their canonical equivalences. -/
theorem finOneLinearEquiv_auxiliaryFinFunctionLinearMap {p q : ℕ} (hp : p = 1) (hq : q = 1) (x : Fin p → k) :
    finOneLinearEquiv k hq (auxiliaryFinFunctionLinearMap k p q x) = finOneLinearEquiv k hp x := by
  subst hp
  change auxiliaryFinFunctionLinearMap k 1 q x ⟨0, _⟩ = x ⟨0, _⟩
  rw [auxiliaryFinFunctionLinearMap_apply, dif_pos (show ((⟨0, by omega⟩ : Fin q) : ℕ) < 1 from Nat.zero_lt_one)]

omit [Field k] in

/-- The function space on a finite type of cardinal parameter zero is a subsingleton. -/
theorem finFunction_subsingleton_of_eq_zero {q : ℕ} (hq : q = 0) : Subsingleton (Fin q → k) := by
  subst hq; infer_instance

section Prod

variable {M N : Type*} [AddCommMonoid M] [Module k M] [AddCommMonoid N] [Module k N]

/-- The product of a module with a subsingleton module is linearly equivalent to the first module. -/
def prodEquivLeftOfSubsingleton (k : Type*) [Field k] {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] (hN : Subsingleton N) : (M × N) ≃ₗ[k] M where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun m := (m, 0)
  left_inv _ := Prod.ext rfl (@Subsingleton.elim N hN _ _)
  right_inv _ := rfl

/-- The product of a subsingleton module with another module is linearly equivalent to the second module. -/
def prodEquivRightOfSubsingleton (k : Type*) [Field k] {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] (hM : Subsingleton M) : (M × N) ≃ₗ[k] N where
  toFun := Prod.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun n := (0, n)
  left_inv _ := Prod.ext (@Subsingleton.elim M hM _ _) rfl
  right_inv _ := rfl

/-- The inverse product equivalence inserts zero in the subsingleton second factor. -/
@[simp] theorem prodEquivLeftOfSubsingleton_symm_apply (hN : Subsingleton N) (m : M) :
    (prodEquivLeftOfSubsingleton k hN).symm m = (m, 0) := rfl

/-- The inverse product equivalence inserts zero in the subsingleton first factor. -/
@[simp] theorem prodEquivRightOfSubsingleton_symm_apply (hM : Subsingleton M) (n : N) :
    (prodEquivRightOfSubsingleton (M := M) k hM).symm n = (0, n) := rfl

/-- Any two subsingleton modules over a field are linearly equivalent. -/
def linearEquivOfSubsingleton (k : Type*) [Field k] {M N : Type*} [AddCommMonoid M] [Module k M]
    [AddCommMonoid N] [Module k N] (hM : Subsingleton M) (hN : Subsingleton N) : M ≃ₗ[k] N where
  toFun _ := 0
  invFun _ := 0
  map_add' _ _ := (add_zero 0).symm
  map_smul' c _ := (smul_zero c).symm
  left_inv _ := @Subsingleton.elim M hM _ _
  right_inv _ := @Subsingleton.elim N hN _ _

end Prod

variable {k Q : Type*} [Field k] [Quiver Q]

/-- A quiver representation determined by two vertices and scalar coefficient data on arrows. -/
noncomputable def twoVertexRepresentation [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    AuxiliaryQuiverModuleData k Q where
  obj v := (Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)
  map {a b} e :=
    (LinearMap.inr k _ _).comp
      ((c ⟨a, b, e⟩ • auxiliaryFinFunctionLinearMap k (if a = i then 1 else 0) (if b = j then 1 else 0)).comp
        (LinearMap.fst k _ _))

/-- An auxiliary formula involving an arrow map of the two-vertex representation and the finite-function linear map. -/
@[simp] theorem auxiliary_fact14 [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {a b : Q} (e : a ⟶ b) (x : (twoVertexRepresentation i j c).obj a) :
    (twoVertexRepresentation i j c).map e x =
      (0, c ⟨a, b, e⟩ • auxiliaryFinFunctionLinearMap k (if a = i then 1 else 0) (if b = j then 1 else 0) x.1) :=
  rfl

/-- An auxiliary formula for an arrow map of the two-vertex representation. -/
theorem auxiliary_fact15 [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {a b : Q} (e : a ⟶ b) (x : (twoVertexRepresentation i j c).obj a) :
    ((twoVertexRepresentation i j c).map e x).1 = 0 := rfl

/-- A second auxiliary formula involving an arrow map and the finite-function linear map. -/
theorem auxiliary_fact16 [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {a b : Q} (e : a ⟶ b) (x : (twoVertexRepresentation i j c).obj a) :
    ((twoVertexRepresentation i j c).map e x).2 =
      c ⟨a, b, e⟩ • auxiliaryFinFunctionLinearMap k (if a = i then 1 else 0) (if b = j then 1 else 0) x.1 := rfl

/-- An auxiliary statement about the spaces of a two-vertex representation. -/
theorem auxiliary_fact19 [DecidableEq Q] {i j : Q} (c : (Σ a b : Q, (a ⟶ b)) → k)
    {v : Q} (hi : v ≠ i) (hj : v ≠ j) : Subsingleton ((twoVertexRepresentation i j c).obj v) := by
  have h1 : Subsingleton (Fin (if v = i then 1 else 0) → k) := finFunction_subsingleton_of_eq_zero (if_neg hi)
  have h2 : Subsingleton (Fin (if v = j then 1 else 0) → k) := finFunction_subsingleton_of_eq_zero (if_neg hj)
  exact @instSubsingletonProd _ _ h1 h2

/-- A second auxiliary statement about a vertex space of the two-vertex representation. -/
instance auxiliary_fact12 [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    Module.Free k ((twoVertexRepresentation i j c).obj v) :=
  inferInstanceAs
    (Module.Free k ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)))

/-- An auxiliary statement about a vertex space of the two-vertex representation. -/
instance auxiliary_fact11 [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    Module.Finite k ((twoVertexRepresentation i j c).obj v) :=
  inferInstanceAs
    (Module.Finite k ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)))

/-- An auxiliary linear equivalence associated with a vertex space of a two-vertex representation. -/
noncomputable instance (priority := 100) auxiliaryVertexEquiv [DecidableEq Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) : AddCommGroup ((twoVertexRepresentation i j c).obj v) :=
  Module.addCommMonoidToAddCommGroup k

/-- An auxiliary statement involving a displayed quiver representation and its dimension data. -/
theorem auxiliary_fact1 [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    auxiliaryVertexValue (twoVertexRepresentation i j c) v = (if v = i then 1 else 0) + (if v = j then 1 else 0) := by
  change finrank k ((Fin (if v = i then 1 else 0) → k) × (Fin (if v = j then 1 else 0) → k)) = _
  rw [Module.finrank_prod, Module.finrank_pi k, Module.finrank_pi k, Fintype.card_fin,
    Fintype.card_fin]

/-- An auxiliary dimension statement for the displayed two-vertex representation. -/
theorem auxiliary_fact10 [DecidableEq Q] [Fintype Q] (i j : Q)
    (c : (Σ a b : Q, (a ⟶ b)) → k) : ∑ v, auxiliaryVertexValue (twoVertexRepresentation i j c) v = 2 := by
  simp only [auxiliary_fact1, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ,
    Finset.mem_univ, if_true]

/-- Every arrow map in the zero-coefficient two-vertex representation is zero. -/
theorem twoVertexRepresentation_zero_arrowMap [DecidableEq Q] (i j : Q) {a b : Q} (e : a ⟶ b) :
    (twoVertexRepresentation (k := k) i j (0 : (Σ a b : Q, (a ⟶ b)) → k)).map e = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [auxiliary_fact14]
  simp only [Pi.zero_apply, zero_smul, LinearMap.zero_apply]
  rfl

/-- Displayed equivalence data between the zero-coefficient two-vertex representation and an auxiliary construction on its two vertices. -/
noncomputable def zeroTwoVertexAuxiliaryEquiv [DecidableEq Q] (i j : Q) :
    AuxiliaryQuiverEquivData k Q (twoVertexRepresentation i j (0 : (Σ a b : Q, (a ⟶ b)) → k))
      (AuxiliaryQuiverModuleData.auxiliaryBinaryConstruction k Q (auxiliaryObjectAtVertex i) (auxiliaryObjectAtVertex j)) where
  app _ := LinearEquiv.refl k _
  naturality e x := by
    have h1 : ((twoVertexRepresentation (k := k) i j (0 : (Σ a b : Q, (a ⟶ b)) → k)).map e) x = 0 := by
      rw [twoVertexRepresentation_zero_arrowMap, LinearMap.zero_apply]
    rw [h1, map_zero]
    rfl

/-- An auxiliary linear equivalence associated with the first distinguished vertex of a two-vertex representation. -/
noncomputable def auxiliaryLeftVertexEquiv [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    (twoVertexRepresentation i j c).obj i :=
  ((finOneLinearEquiv k (if_pos rfl)).symm 1, 0)

/-- An auxiliary linear equivalence associated with the second distinguished vertex of a two-vertex representation. -/
noncomputable def auxiliaryRightVertexEquiv [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    (twoVertexRepresentation i j c).obj j :=
  (0, (finOneLinearEquiv k (if_pos rfl)).symm 1)

/-- An auxiliary compatibility statement for vertex equivalences and arrow maps of two-vertex representations. -/
theorem auxiliary_fact18 [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k)
    (e : i ⟶ j) :
    (twoVertexRepresentation i j c).map e (auxiliaryLeftVertexEquiv i j c) = c ⟨i, j, e⟩ • auxiliaryRightVertexEquiv i j c := by
  rw [auxiliary_fact14]
  refine Prod.ext (smul_zero _).symm ?_
  change c ⟨i, j, e⟩ • auxiliaryFinFunctionLinearMap k _ _ ((finOneLinearEquiv k (if_pos rfl)).symm (1 : k))
    = c ⟨i, j, e⟩ • (finOneLinearEquiv k (if_pos rfl)).symm (1 : k)
  congr 1
  apply (finOneLinearEquiv k (if_pos (rfl : j = j))).injective
  rw [finOneLinearEquiv_auxiliaryFinFunctionLinearMap (if_pos (rfl : i = i)) (if_pos (rfl : j = j)),
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- An auxiliary evaluation theorem for the linear equivalence at the second distinguished vertex. -/
theorem auxiliary_fact7 [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    auxiliaryRightVertexEquiv (k := k) i j c ≠ 0 := by
  intro h
  have h2 : (finOneLinearEquiv k (if_pos (rfl : j = j))).symm (1 : k) = 0 := congrArg Prod.snd h
  have := congrArg (finOneLinearEquiv k (if_pos (rfl : j = j))) h2
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

/-- An auxiliary evaluation theorem for the linear equivalence at the first distinguished vertex. -/
theorem auxiliary_fact6 [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) :
    auxiliaryLeftVertexEquiv (k := k) i j c ≠ 0 := by
  intro h
  have h2 : (finOneLinearEquiv k (if_pos (rfl : i = i))).symm (1 : k) = 0 := congrArg Prod.fst h
  have := congrArg (finOneLinearEquiv k (if_pos (rfl : i = i))) h2
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

private theorem isCompl_dichotomy {M : Type*} [AddCommGroup M] [Module k M]
    [IsSimpleModule k M] {A B : Submodule k M} (h : IsCompl A B) :
    (A = ⊥ ∧ B = ⊤) ∨ (A = ⊤ ∧ B = ⊥) := by
  rcases eq_bot_or_eq_top A with hA | hA
  · exact Or.inl ⟨hA, by rw [← h.sup_eq_top, hA, bot_sup_eq]⟩
  · exact Or.inr ⟨hA, by rw [← h.inf_eq_bot, hA, top_inf_eq]⟩

/-- An auxiliary statement about the vertex spaces of a displayed quiver representation. -/
theorem auxiliary_fact2 [DecidableEq Q] {i j : Q} {c : (Σ a b : Q, (a ⟶ b)) → k}
    (W : ∀ v, Submodule k ((twoVertexRepresentation i j c).obj v)) {v : Q} (hvi : v ≠ i) (hvj : v ≠ j) :
    W v = ⊥ := by
  haveI := auxiliary_fact19 c hvi hvj
  rw [Submodule.eq_bot_iff]
  intro x _
  exact Subsingleton.elim x 0

/-- An auxiliary theorem about the vertex spaces of the displayed two-vertex representation. -/
theorem auxiliary_fact4 [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) : finrank k ((twoVertexRepresentation i j c).obj i) = 1 := by
  have h := auxiliary_fact1 (k := k) i j c i
  rw [if_pos rfl, if_neg hij] at h
  exact h

/-- A second auxiliary theorem about the vertex spaces of the displayed two-vertex representation. -/
theorem auxiliary_fact5 [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) : finrank k ((twoVertexRepresentation i j c).obj j) = 1 := by
  have h := auxiliary_fact1 (k := k) i j c j
  rw [if_pos rfl, if_neg (Ne.symm hij)] at h
  exact h

/-- An auxiliary statement relating the zero-coefficient two-vertex representation to the displayed predicate. -/
theorem auxiliary_fact13 [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {e₀ : i ⟶ j} (hc : c ⟨i, j, e₀⟩ ≠ 0) :
    (twoVertexRepresentation i j c).AuxiliaryCondition := by
  haveI hsi : IsSimpleModule k ((twoVertexRepresentation (k := k) i j c).obj i) :=
    isSimpleModule_iff_finrank_eq_one.mpr (auxiliary_fact4 hij c)
  haveI hsj : IsSimpleModule k ((twoVertexRepresentation (k := k) i j c).obj j) :=
    isSimpleModule_iff_finrank_eq_one.mpr (auxiliary_fact5 hij c)

  have hmap : (twoVertexRepresentation i j c).map e₀ (auxiliaryLeftVertexEquiv i j c) ≠ 0 := by
    rw [auxiliary_fact18]
    exact smul_ne_zero hc (auxiliary_fact7 i j c)
  refine ⟨⟨i, Module.finrank_pos_iff.mp (by rw [auxiliary_fact4 hij c]; norm_num)⟩, ?_⟩
  intro W₁ W₂ h1 h2 hcompl

  rcases isCompl_dichotomy (hcompl i) with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
  · rcases isCompl_dichotomy (hcompl j) with ⟨hj1, _⟩ | ⟨_, hj2⟩
    ·
      refine Or.inl fun v => ?_
      by_cases hvi : v = i
      · exact hvi ▸ hi1
      by_cases hvj : v = j
      · exact hvj ▸ hj1
      exact auxiliary_fact2 W₁ hvi hvj
    ·
      exact absurd (by
        have hmem : auxiliaryLeftVertexEquiv i j c ∈ W₂ i := by rw [hi2]; exact Submodule.mem_top
        have := h2 e₀ _ hmem
        rw [hj2, Submodule.mem_bot] at this
        exact this) hmap
  · rcases isCompl_dichotomy (hcompl j) with ⟨hj1, _⟩ | ⟨_, hj2⟩
    ·
      exact absurd (by
        have hmem : auxiliaryLeftVertexEquiv i j c ∈ W₁ i := by rw [hi1]; exact Submodule.mem_top
        have := h1 e₀ _ hmem
        rw [hj1, Submodule.mem_bot] at this
        exact this) hmap
    ·
      refine Or.inr fun v => ?_
      by_cases hvi : v = i
      · exact hvi ▸ hi2
      by_cases hvj : v = j
      · exact hvj ▸ hj2
      exact auxiliary_fact2 W₂ hvi hvj

/-- The zero-coefficient two-vertex representation does not satisfy the displayed predicate. -/
theorem not_auxiliaryProperty_twoVertexRepresentation_zero [DecidableEq Q] (i j : Q) :
    ¬ (twoVertexRepresentation (k := k) i j (0 : (Σ a b : Q, (a ⟶ b)) → k)).AuxiliaryCondition := by
  intro hIndec
  obtain ⟨-, hdecomp⟩ := hIndec
  let c : (Σ a b : Q, (a ⟶ b)) → k := 0

  have hmaps : ∀ {a b : Q} (e : a ⟶ b), (twoVertexRepresentation (k := k) i j c).map e = 0 :=
    fun e => twoVertexRepresentation_zero_arrowMap i j e
  let W₁ : ∀ v, Submodule k ((twoVertexRepresentation (k := k) i j c).obj v) :=
    fun v => LinearMap.range (LinearMap.inl k (Fin (if v = i then 1 else 0) → k)
      (Fin (if v = j then 1 else 0) → k))
  let W₂ : ∀ v, Submodule k ((twoVertexRepresentation (k := k) i j c).obj v) :=
    fun v => LinearMap.range (LinearMap.inr k (Fin (if v = i then 1 else 0) → k)
      (Fin (if v = j then 1 else 0) → k))
  have hstable : ∀ (W : ∀ v, Submodule k ((twoVertexRepresentation (k := k) i j c).obj v)),
      ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, (twoVertexRepresentation (k := k) i j c).map e x ∈ W b := by
    intro W a b e x _
    rw [hmaps e, LinearMap.zero_apply]
    exact (W b).zero_mem
  have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := fun _ => LinearMap.isCompl_range_inl_inr

  rcases hdecomp W₁ W₂ (hstable W₁) (hstable W₂) hcompl with h1 | h2
  · have hne : (LinearMap.inl k (Fin (if i = i then 1 else 0) → k)
        (Fin (if i = j then 1 else 0) → k)) ((finOneLinearEquiv k (if_pos rfl)).symm 1) ≠ 0 := by
      intro h
      have := congrArg Prod.fst h
      have h0 : (finOneLinearEquiv k (if_pos (rfl : i = i))).symm (1 : k) = 0 := this
      have := congrArg (finOneLinearEquiv k (if_pos (rfl : i = i))) h0
      simp only [LinearEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero this
    exact hne (by
      have := h1 i
      rw [Submodule.eq_bot_iff] at this
      exact this _ (LinearMap.mem_range_self _ _))
  · have hne : (LinearMap.inr k (Fin (if j = i then 1 else 0) → k)
        (Fin (if j = j then 1 else 0) → k)) ((finOneLinearEquiv k (if_pos rfl)).symm 1) ≠ 0 := by
      intro h
      have := congrArg Prod.snd h
      have h0 : (finOneLinearEquiv k (if_pos (rfl : j = j))).symm (1 : k) = 0 := this
      have := congrArg (finOneLinearEquiv k (if_pos (rfl : j = j))) h0
      simp only [LinearEquiv.apply_symm_apply, map_zero] at this
      exact one_ne_zero this
    exact hne (by
      have := h2 j
      rw [Submodule.eq_bot_iff] at this
      exact this _ (LinearMap.mem_range_self _ _))

/-- Transports a linear equivalence between two representation spaces along an equality of vertices. -/
def linearEquivOfVertexEq {ρ σ : AuxiliaryQuiverModuleData k Q} {v w : Q} (h : v = w)
    (φ : ρ.obj w ≃ₗ[k] σ.obj w) : ρ.obj v ≃ₗ[k] σ.obj v := by
  subst h; exact φ

/-- Transporting a vertex-space linear equivalence along reflexivity leaves it unchanged. -/
@[simp] theorem linearEquivOfVertexEq_rfl {ρ σ : AuxiliaryQuiverModuleData k Q} {v : Q}
    (φ : ρ.obj v ≃ₗ[k] σ.obj v) : linearEquivOfVertexEq (rfl : v = v) φ = φ := rfl

/-- The scalar coefficient of an arrow map after choosing linear equivalences from its source and target vertex spaces to the field. -/
noncomputable def arrowCoefficient [DecidableEq Q] {ρ : AuxiliaryQuiverModuleData k Q} {i j : Q}
    (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k) : (Σ a b : Q, (a ⟶ b)) → k :=
  fun p =>
    if h : p.1 = i then
      (if h' : p.2.1 = j then β (h' ▸ ρ.map p.2.2 (h.symm ▸ α.symm 1)) else 0)
    else 0

/-- The coefficient of an arrow is obtained by applying its target equivalence to the arrow map evaluated at the inverse image of one under its source equivalence. -/
theorem arrowCoefficient_apply [DecidableEq Q] {ρ : AuxiliaryQuiverModuleData k Q} {i j : Q}
    (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k) (e : i ⟶ j) :
    arrowCoefficient α β ⟨i, j, e⟩ = β (ρ.map e (α.symm 1)) := by
  simp [arrowCoefficient]

/-- Auxiliary coefficient data associated with a quiver representation and a displayed two-vertex representation. -/
noncomputable def auxiliaryCoefficientData [DecidableEq Q] {ρ : AuxiliaryQuiverModuleData k Q} {i j : Q}
    (hij : i ≠ j) (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k)
    (htriv : ∀ v, v ≠ i → v ≠ j → Subsingleton (ρ.obj v))
    (c : (Σ a b : Q, (a ⟶ b)) → k) (v : Q) :
    ρ.obj v ≃ₗ[k] (twoVertexRepresentation i j c).obj v :=
  if hv : v = i then
    linearEquivOfVertexEq hv (α.trans ((finOneLinearEquiv k (if_pos rfl)).symm.trans
      (prodEquivLeftOfSubsingleton k (finFunction_subsingleton_of_eq_zero (k := k) (if_neg hij))).symm))
  else if hv' : v = j then
    linearEquivOfVertexEq hv' (β.trans ((finOneLinearEquiv k (if_pos rfl)).symm.trans
      (prodEquivRightOfSubsingleton k (finFunction_subsingleton_of_eq_zero (k := k) (if_neg (Ne.symm hij)))).symm))
  else linearEquivOfSubsingleton k (htriv v hv hv') (auxiliary_fact19 c hv hv')

section NormalFormEquivAt

variable [DecidableEq Q] {ρ : AuxiliaryQuiverModuleData k Q} {i j : Q} (hij : i ≠ j)
  (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k)
  (htriv : ∀ v, v ≠ i → v ≠ j → Subsingleton (ρ.obj v)) (c : (Σ a b : Q, (a ⟶ b)) → k)

/-- An auxiliary relation between coefficient data and one-coordinate linear equivalences. -/
theorem auxiliary_fact8 (x : ρ.obj i) :
    (auxiliaryCoefficientData hij α β htriv c i x).1 = (finOneLinearEquiv k (if_pos rfl)).symm (α x) := by
  rw [auxiliaryCoefficientData, dif_pos (rfl : i = i), linearEquivOfVertexEq_rfl]
  rfl

/-- A second auxiliary relation between coefficient data and one-coordinate linear equivalences. -/
theorem auxiliary_fact9 (y : ρ.obj j) :
    (auxiliaryCoefficientData hij α β htriv c j y).2 = (finOneLinearEquiv k (if_pos rfl)).symm (β y) := by
  rw [auxiliaryCoefficientData, dif_neg (Ne.symm hij), dif_pos (rfl : j = j), linearEquivOfVertexEq_rfl]
  rfl

end NormalFormEquivAt

/-- A representation supported on two distinct one-dimensional vertex spaces, with all other relevant arrow maps zero, is equivalent to the associated two-vertex representation. -/
theorem nonempty_equiv_twoVertexRepresentation_of_support [DecidableEq Q] {ρ : AuxiliaryQuiverModuleData k Q} {i j : Q}
    (hij : i ≠ j) (α : ρ.obj i ≃ₗ[k] k) (β : ρ.obj j ≃ₗ[k] k)
    (htriv : ∀ v, v ≠ i → v ≠ j → Subsingleton (ρ.obj v))
    (hzero : ∀ {a b : Q} (e : a ⟶ b), a ≠ i ∨ b ≠ j → ρ.map e = 0) :
    Nonempty (AuxiliaryQuiverEquivData k Q ρ (twoVertexRepresentation i j (arrowCoefficient α β))) := by
  refine ⟨⟨auxiliaryCoefficientData hij α β htriv (arrowCoefficient α β), ?_⟩⟩
  intro a b e x
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      refine Prod.ext ?_ ?_
      ·
        haveI := finFunction_subsingleton_of_eq_zero (k := k) (if_neg (Ne.symm hij) : (if j = i then 1 else 0) = 0)
        exact Subsingleton.elim _ _
      ·
        have hfin : (if j = j then 1 else 0) = 1 := if_pos rfl
        apply (finOneLinearEquiv k hfin).injective
        rw [auxiliary_fact9, auxiliary_fact16, LinearEquiv.apply_symm_apply,
          map_smul, auxiliary_fact8,
          finOneLinearEquiv_auxiliaryFinFunctionLinearMap (if_pos (rfl : i = i)) hfin, LinearEquiv.apply_symm_apply,
          smul_eq_mul, arrowCoefficient_apply]
        have hx : ρ.map e x = α x • ρ.map e (α.symm (1 : k)) := by
          rw [← map_smul]
          congr 1
          rw [← map_smul, smul_eq_mul, mul_one, α.symm_apply_apply]
        rw [hx, map_smul, smul_eq_mul, mul_comm]
    ·
      rw [hzero e (Or.inr hb), LinearMap.zero_apply, map_zero]
      symm
      refine Prod.ext rfl ?_
      rw [auxiliary_fact16, auxiliaryFinFunctionLinearMap_eq_zero_of_target_eq_zero (if_neg hb),
        LinearMap.zero_apply, smul_zero]
      rfl
  ·
    rw [hzero e (Or.inl ha), LinearMap.zero_apply, map_zero]
    symm
    refine Prod.ext rfl ?_
    rw [auxiliary_fact16, auxiliaryFinFunctionLinearMap_eq_zero_of_source_eq_zero (if_neg ha),
      LinearMap.zero_apply, smul_zero]
    rfl

/-- Two finite free quiver representations with zero arrow maps and equal vertex dimensions admit the displayed representation equivalence. -/
theorem nonempty_equiv_of_arrowMap_eq_zero_of_dimension_eq (ρ σ : AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    [∀ v, Module.Free k (σ.obj v)] [∀ v, Module.Finite k (σ.obj v)]
    (hρ : ∀ {a b : Q} (e : a ⟶ b), ρ.map e = 0)
    (hσ : ∀ {a b : Q} (e : a ⟶ b), σ.map e = 0)
    (hdim : ∀ v, auxiliaryVertexValue ρ v = auxiliaryVertexValue σ v) :
    Nonempty (AuxiliaryQuiverEquivData k Q ρ σ) := by
  have hE : ∀ v, Nonempty (ρ.obj v ≃ₗ[k] σ.obj v) := by
    intro v
    letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
    letI : AddCommGroup (σ.obj v) := Module.addCommMonoidToAddCommGroup k
    exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hdim v)
  refine ⟨⟨fun v => (hE v).some, ?_⟩⟩
  intro a b e x
  rw [hρ e, LinearMap.zero_apply, map_zero, hσ e, LinearMap.zero_apply]

/-- A finite free vertex space whose displayed dimension is zero is a subsingleton. -/
theorem vertexSpace_subsingleton_of_dimension_eq_zero {ρ : AuxiliaryQuiverModuleData k Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] {v : Q}
    (h : auxiliaryVertexValue ρ v = 0) : Subsingleton (ρ.obj v) := by
  letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  have h1 : 0 < finrank k (ρ.obj v) := Module.finrank_pos_iff.mpr hns
  have h2 : finrank k (ρ.obj v) = 0 := h
  omega

/-- A finite free vertex space of dimension one is nonempty linearly equivalent to the base field. -/
theorem nonempty_linearEquiv_finrank_one {ρ : AuxiliaryQuiverModuleData k Q}
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)] {v : Q}
    (h : auxiliaryVertexValue ρ v = 1) : Nonempty (ρ.obj v ≃ₗ[k] k) := by
  letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
  refine FiniteDimensional.nonempty_linearEquiv_of_finrank_eq ?_
  rw [Module.finrank_self]
  exact h

/-- A natural-number-valued function on a finite type with sum two is supported either at one point with value two or at two distinct points with value one. -/
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
  ·
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    refine Or.inl ⟨i, ?_, ?_⟩
    · rw [hi, Finset.sum_singleton] at hsum; exact hsum
    · intro v hv
      exact hout v (by rw [hi]; simpa using hv)
  ·
    obtain ⟨i, j, hij, hS2⟩ := Finset.card_eq_two.mp h
    rw [hS2, Finset.sum_pair hij] at hsum
    have hi : d i ≠ 0 := (hmemS i).mp (by rw [hS2]; simp)
    have hj : d j ≠ 0 := (hmemS j).mp (by rw [hS2]; simp)
    refine Or.inr ⟨i, j, hij, by omega, by omega, fun v hvi hvj => ?_⟩
    exact hout v (by rw [hS2]; simp [hvi, hvj])

/-- Under the displayed quiver hypothesis, a representation of total dimension two is equivalent to a two-vertex representation, either with zero coefficients or with a specified nonzero arrow coefficient. -/
theorem exists_equiv_twoVertexRepresentation_of_totalDimension_eq_two [DecidableEq Q] [Fintype Q]
    (hQ : HasAuxiliaryQuiverProperty Q) (ρ : AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, auxiliaryVertexValue ρ v = 2) :
    (∃ i j : Q, Nonempty (AuxiliaryQuiverEquivData k Q ρ
        (twoVertexRepresentation i j (0 : (Σ a b : Q, (a ⟶ b)) → k))))
      ∨ (∃ (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (e₀ : i ⟶ j),
          i ≠ j ∧ c ⟨i, j, e₀⟩ ≠ 0 ∧
            Nonempty (AuxiliaryQuiverEquivData k Q ρ (twoVertexRepresentation i j c))) := by
  classical

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

  have key : ∀ u w : Q, u ≠ w → auxiliaryVertexValue ρ u = 1 → auxiliaryVertexValue ρ w = 1 →
      (∀ v, v ≠ u → v ≠ w → auxiliaryVertexValue ρ v = 0) → ∀ e₀ : u ⟶ w, ρ.map e₀ ≠ 0 →
      (∃ (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k) (e : i ⟶ j),
        i ≠ j ∧ c ⟨i, j, e⟩ ≠ 0 ∧
          Nonempty (AuxiliaryQuiverEquivData k Q ρ (twoVertexRepresentation i j c))) := by
    intro u w huw hu1 hw1 h0 e₀ hne0
    have htriv : ∀ v, v ≠ u → v ≠ w → Subsingleton (ρ.obj v) :=
      fun v h1 h2 => vertexSpace_subsingleton_of_dimension_eq_zero (h0 v h1 h2)
    obtain ⟨α⟩ := nonempty_linearEquiv_finrank_one hu1
    obtain ⟨β⟩ := nonempty_linearEquiv_finrank_one hw1

    have hzero : ∀ {a b : Q} (e : a ⟶ b), a ≠ u ∨ b ≠ w → ρ.map e = 0 := by
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

    have hc : arrowCoefficient α β ⟨u, w, e₀⟩ ≠ 0 := by
      rw [arrowCoefficient_apply]
      intro h
      have h0' : ρ.map e₀ (α.symm 1) = 0 := by
        apply β.injective
        rw [h, map_zero]
      refine hne0 (LinearMap.ext fun y => ?_)
      have hy : ρ.map e₀ y = α y • ρ.map e₀ (α.symm (1 : k)) := by
        rw [← map_smul]
        congr 1
        rw [← map_smul, smul_eq_mul, mul_one, α.symm_apply_apply]
      rw [hy, h0', smul_zero, LinearMap.zero_apply]
    exact ⟨u, w, arrowCoefficient α β, e₀, huw, hc, nonempty_equiv_twoVertexRepresentation_of_support huw α β htriv hzero⟩
  rcases support_of_sum_eq_two (auxiliaryVertexValue ρ) h2 with ⟨i, hi2, hi0⟩ | ⟨i, j, hij, hi1, hj1, h0⟩
  ·
    have hmz : ∀ {a b : Q} (e : a ⟶ b), ρ.map e = 0 := by
      intro a b e
      by_cases ha : a = i
      · subst a
        haveI := vertexSpace_subsingleton_of_dimension_eq_zero (hi0 b fun h => (hnoloop i).false (h ▸ e))
        exact LinearMap.ext fun _ => Subsingleton.elim _ _
      · haveI := vertexSpace_subsingleton_of_dimension_eq_zero (hi0 a ha)
        exact LinearMap.ext fun y => by
          rw [Subsingleton.elim y 0, map_zero, LinearMap.zero_apply]
    refine Or.inl ⟨i, i, nonempty_equiv_of_arrowMap_eq_zero_of_dimension_eq ρ _ hmz
      (twoVertexRepresentation_zero_arrowMap i i) fun v => ?_⟩
    rw [auxiliary_fact1]
    by_cases hv : v = i
    · subst v
      rw [if_pos rfl]
      omega
    · rw [if_neg hv]
      have := hi0 v hv
      omega
  ·
    by_cases hall : ∀ (a b : Q) (e : a ⟶ b), ρ.map e = 0
    ·
      refine Or.inl ⟨i, j, nonempty_equiv_of_arrowMap_eq_zero_of_dimension_eq ρ _ (fun e => hall _ _ e)
        (twoVertexRepresentation_zero_arrowMap i j) fun v => ?_⟩
      rw [auxiliary_fact1]
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
    ·
      push Not at hall
      obtain ⟨a, b, e, hne0⟩ := hall
      have hda : auxiliaryVertexValue ρ a ≠ 0 := by
        intro h
        haveI := vertexSpace_subsingleton_of_dimension_eq_zero h
        exact hne0 (LinearMap.ext fun y => by
          rw [Subsingleton.elim y 0, map_zero, LinearMap.zero_apply])
      have hdb : auxiliaryVertexValue ρ b ≠ 0 := by
        intro h
        haveI := vertexSpace_subsingleton_of_dimension_eq_zero h
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

/-- Auxiliary equivalence data between displayed two-vertex representations. -/
noncomputable def auxiliaryTwoVertexEquiv [DecidableEq Q] (i j : Q) (c : (Σ a b : Q, (a ⟶ b)) → k)
    {t : k} (ht : t ≠ 0) :
    AuxiliaryQuiverEquivData k Q (twoVertexRepresentation i j c) (twoVertexRepresentation i j fun p => t * c p) where
  app v := (LinearEquiv.refl k (Fin (if v = i then 1 else 0) → k)).prodCongr
    (LinearEquiv.smulOfNeZero k (Fin (if v = j then 1 else 0) → k) t ht)
  naturality e x := by
    refine Prod.ext rfl ?_
    change t • (((twoVertexRepresentation i j c).map e x).2) = _
    rw [auxiliary_fact16, smul_smul]
    rfl

/-- An auxiliary statement involving a displayed quiver representation and representation-equivalence data. -/
theorem auxiliary_fact3 [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c c' : (Σ a b : Q, (a ⟶ b)) → k)
    (φ : AuxiliaryQuiverEquivData k Q (twoVertexRepresentation i j c) (twoVertexRepresentation i j c')) :
    ∃ t : k, t ≠ 0 ∧ ∀ e : i ⟶ j, c' ⟨i, j, e⟩ = t * c ⟨i, j, e⟩ := by
  haveI hsub_i : Subsingleton (Fin (if i = j then 1 else 0) → k) :=
    finFunction_subsingleton_of_eq_zero (if_neg hij)
  haveI hsub_j : Subsingleton (Fin (if j = i then 1 else 0) → k) :=
    finFunction_subsingleton_of_eq_zero (if_neg (Ne.symm hij))
  have hi1 : (if i = i then 1 else 0) = 1 := if_pos rfl
  have hj1 : (if j = j then 1 else 0) = 1 := if_pos rfl

  obtain ⟨gi, hgi⟩ : ∃ g : k, finOneLinearEquiv k hi1 (φ.app i (auxiliaryLeftVertexEquiv i j c)).1 = g :=
    ⟨_, rfl⟩
  obtain ⟨gj, hgj⟩ : ∃ g : k, finOneLinearEquiv k hj1 (φ.app j (auxiliaryRightVertexEquiv i j c)).2 = g :=
    ⟨_, rfl⟩
  have hgi0 : gi ≠ 0 := by
    intro h
    have hz : φ.app i (auxiliaryLeftVertexEquiv i j c) = 0 := by
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      apply (finOneLinearEquiv k hi1).injective
      rw [hgi, h]
      exact (map_zero _).symm
    exact auxiliary_fact6 i j c ((φ.app i).injective (hz.trans (map_zero _).symm))
  have hgj0 : gj ≠ 0 := by
    intro h
    have hz : φ.app j (auxiliaryRightVertexEquiv i j c) = 0 := by
      refine Prod.ext (Subsingleton.elim _ _) ?_
      apply (finOneLinearEquiv k hj1).injective
      rw [hgj, h]
      exact (map_zero _).symm
    exact auxiliary_fact7 i j c ((φ.app j).injective (hz.trans (map_zero _).symm))

  have hrel : ∀ e : i ⟶ j, c ⟨i, j, e⟩ * gj = c' ⟨i, j, e⟩ * gi := by
    intro e
    have hcomm := φ.naturality e (auxiliaryLeftVertexEquiv i j c)
    rw [auxiliary_fact18, map_smul] at hcomm
    have h4 : finOneLinearEquiv k hj1 (c ⟨i, j, e⟩ • (φ.app j (auxiliaryRightVertexEquiv i j c)).2)
        = finOneLinearEquiv k hj1 (c' ⟨i, j, e⟩ •
            auxiliaryFinFunctionLinearMap k (if i = i then 1 else 0) (if j = j then 1 else 0)
              (φ.app i (auxiliaryLeftVertexEquiv i j c)).1) :=
      congrArg (fun y => finOneLinearEquiv k hj1 (Prod.snd y)) hcomm
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      finOneLinearEquiv_auxiliaryFinFunctionLinearMap hi1 hj1, hgi, hgj] at h4
    exact h4
  refine ⟨gj * gi⁻¹, mul_ne_zero hgj0 (inv_ne_zero hgi0), fun e => ?_⟩
  calc c' ⟨i, j, e⟩ = c' ⟨i, j, e⟩ * gi * gi⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hgi0, mul_one]
    _ = c ⟨i, j, e⟩ * gj * gi⁻¹ := by rw [hrel e]
    _ = gj * gi⁻¹ * c ⟨i, j, e⟩ := by ring

/-- An auxiliary statement involving two-vertex representations and displayed representation-equivalence data. -/
theorem auxiliary_fact20 [DecidableEq Q] {i j i' j' : Q}
    (c c' : (Σ a b : Q, (a ⟶ b)) → k)
    (φ : AuxiliaryQuiverEquivData k Q (twoVertexRepresentation i j c) (twoVertexRepresentation i' j' c')) :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  have hd : ∀ v : Q, (if v = i then 1 else 0) + (if v = j then 1 else 0)
      = (if v = i' then 1 else 0) + (if v = j' then 1 else 0) := by
    intro v
    rw [← auxiliary_fact1 i j c v, ← auxiliary_fact1 i' j' c' v]
    exact φ.dimension_eq v
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
    ·
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
    ·
      have hij : i = j := hi.trans hj.symm
      have h1 := hd i
      rw [if_pos rfl, if_pos hij, if_pos hi] at h1
      have hij' : i = i' := by
        by_contra hne
        rw [if_neg hne] at h1
        omega
      exact hij.symm.trans hij'

/-- The displayed predicate on quiver representations is preserved by the displayed representation equivalence. -/
theorem auxiliaryProperty_of_equiv {ρ σ : AuxiliaryQuiverModuleData k Q}
    (φ : AuxiliaryQuiverEquivData k Q ρ σ) (h : ρ.AuxiliaryCondition) : σ.AuxiliaryCondition := by
  obtain ⟨⟨v₀, hv₀⟩, hdec⟩ := h
  refine ⟨⟨v₀, ?_⟩, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hv₀
    exact ⟨φ.app v₀ x, φ.app v₀ y, fun h => hxy ((φ.app v₀).injective h)⟩
  intro W₁ W₂ h1 h2 hcompl

  have hpull : ∀ (W : ∀ v, Submodule k (σ.obj v)),
      (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, σ.map e x ∈ W b) →
      ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ Submodule.comap (φ.app a).toLinearMap (W a),
        ρ.map e x ∈ Submodule.comap (φ.app b).toLinearMap (W b) := by
    intro W hW a b e x hx
    rw [Submodule.mem_comap] at hx ⊢
    rw [LinearEquiv.coe_coe, φ.naturality e]
    exact hW e _ hx
  have hcompl' : ∀ v, IsCompl (Submodule.comap (φ.app v).toLinearMap (W₁ v))
      (Submodule.comap (φ.app v).toLinearMap (W₂ v)) := by
    intro v
    exact (Submodule.orderIsoMapComap (φ.app v)).symm.isCompl (hcompl v)
  have hcomap_inj : ∀ (v : Q) (W : Submodule k (σ.obj v)),
      Submodule.comap (φ.app v).toLinearMap W = ⊥ → W = ⊥ := by
    intro v W hW
    have := (Submodule.orderIsoMapComap (φ.app v)).symm.injective
      (a₁ := W) (a₂ := ⊥) (by simpa using hW)
    exact this
  rcases hdec _ _ (hpull W₁ h1) (hpull W₂ h2) hcompl' with hb | hb
  · exact Or.inl fun v => hcomap_inj v (W₁ v) (hb v)
  · exact Or.inr fun v => hcomap_inj v (W₂ v) (hb v)

/-- A further auxiliary formula for an arrow map of the two-vertex representation. -/
theorem auxiliary_fact17 [DecidableEq Q] {i j : Q} (hij : i ≠ j)
    (c : (Σ a b : Q, (a ⟶ b)) → k) {e : i ⟶ j} (hc : c ⟨i, j, e⟩ ≠ 0) :
    Function.Bijective ((twoVertexRepresentation i j c).map e) := by
  haveI hsi : IsSimpleModule k ((twoVertexRepresentation (k := k) i j c).obj i) :=
    isSimpleModule_iff_finrank_eq_one.mpr (auxiliary_fact4 hij c)
  haveI hsj : IsSimpleModule k ((twoVertexRepresentation (k := k) i j c).obj j) :=
    isSimpleModule_iff_finrank_eq_one.mpr (auxiliary_fact5 hij c)
  have hne : (twoVertexRepresentation i j c).map e ≠ 0 := by
    intro h
    have hg := auxiliary_fact18 i j c e
    rw [h, LinearMap.zero_apply] at hg
    exact smul_ne_zero hc (auxiliary_fact7 i j c) hg.symm
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    rcases eq_bot_or_eq_top (LinearMap.ker ((twoVertexRepresentation i j c).map e)) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hne
  · rw [← LinearMap.range_eq_top]
    rcases eq_bot_or_eq_top (LinearMap.range ((twoVertexRepresentation i j c).map e)) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hne
    · exact h

/-- Under the displayed quiver hypothesis, a representation of total dimension two either fails the displayed predicate or has a bijective arrow map between distinct vertices. -/
@[source_ref "Chapter3/Problem3.9.3" (role := supporting)]
theorem not_auxiliaryProperty_or_exists_bijectiveArrow_of_totalDimension_eq_two [Fintype Q]
    (hQ : HasAuxiliaryQuiverProperty Q) (ρ : AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, auxiliaryVertexValue ρ v = 2) :
    (¬ ρ.AuxiliaryCondition)
      ∨ (∃ (i j : Q) (a : i ⟶ j), i ≠ j ∧ Function.Bijective (ρ.map a)) := by
  classical
  rcases exists_equiv_twoVertexRepresentation_of_totalDimension_eq_two hQ ρ h2 with ⟨i, j, ⟨φ⟩⟩ | ⟨i, j, c, e₀, hij, hc, ⟨φ⟩⟩
  · exact Or.inl fun h => not_auxiliaryProperty_twoVertexRepresentation_zero i j (auxiliaryProperty_of_equiv φ h)
  · refine Or.inr ⟨i, j, e₀, hij, ?_⟩
    have hcomp : ∀ x, ρ.map e₀ x =
        (φ.app j).symm ((twoVertexRepresentation i j c).map e₀ (φ.app i x)) := by
      intro x
      rw [← φ.naturality e₀, LinearEquiv.symm_apply_apply]
    have hbij := auxiliary_fact17 hij c hc
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · refine (φ.app i).injective (hbij.1 ((φ.app j).symm.injective ?_))
      rw [← hcomp, ← hcomp]
      exact hxy
    · obtain ⟨z, hz⟩ := hbij.2 (φ.app j y)
      obtain ⟨x, hx⟩ := (φ.app i).surjective z
      exact ⟨x, by rw [hcomp, hx, hz, LinearEquiv.symm_apply_apply]⟩

end RepresentationTheory.Quiver.TwoDimensionalRepresentations

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition1 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.arrowCoefficient

/--
The first auxiliary definition is evaluated by applying the target equivalence to the displayed
arrow map at the inverse image of one under the source equivalence.
-/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition1_apply := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.arrowCoefficient_apply

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition2 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryLeftVertexEquiv

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition3 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryRightVertexEquiv

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition4 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryCoefficientData

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition5 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.twoVertexRepresentation

/-- Every displayed arrow-indexed map of the fifth auxiliary definition at zero is zero. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition5_zero_map := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.twoVertexRepresentation_zero_arrowMap

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition6 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryTwoVertexEquiv

/-- An auxiliary definition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition7 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryVertexEquiv

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact1 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact1

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact10 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact10

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact11 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFinFunctionLinearMap_apply

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact12 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact11

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact13 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact12

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact14 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact13

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact15 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact14

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact16 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact15

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact17 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact16

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact18 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact17

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact19 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact18

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact2 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact2

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact20 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact19

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact21 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact20

/-- An auxiliary proposition whose formal type is partially elided. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact22 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.linearEquivOfVertexEq_rfl

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact3 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact3

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact4 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact4

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact5 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact5

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact6 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact6

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact7 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact7

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact8 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact8

/-- An auxiliary proposition whose formal type is unavailable. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact9 := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliary_fact9

/--
Under the displayed quiver hypothesis, a representation of total dimension two admits the
displayed equivalence to the fifth auxiliary definition, either at zero or at data nonzero on a
displayed arrow.
-/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.exists_equiv_auxiliaryDefinition5_of_totalDimension_eq_two := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.exists_equiv_twoVertexRepresentation_of_totalDimension_eq_two

/--
Under the displayed two-vertex support and zero-map hypotheses, the representation admits the
displayed equivalence to the fifth auxiliary definition.
-/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.nonempty_equiv_auxiliaryDefinition5_of_support := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.nonempty_equiv_twoVertexRepresentation_of_support

/-- The fifth auxiliary definition at zero does not satisfy the displayed predicate. -/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.not_auxiliaryProperty_auxiliaryDefinition5_zero := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.not_auxiliaryProperty_twoVertexRepresentation_zero

/--
Displayed equivalence data between the fifth auxiliary definition at zero and the displayed
construction on its two vertices.
-/
alias _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.zeroAuxiliaryEquivalenceData := _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.zeroTwoVertexAuxiliaryEquiv

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition5

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryDefinition6

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact10

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact14

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact21

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.auxiliaryFact3

attribute [source_ref "Chapter3/Problem3.9.3" (role := primary)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.exists_equiv_auxiliaryDefinition5_of_totalDimension_eq_two

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.not_auxiliaryProperty_auxiliaryDefinition5_zero

attribute [source_ref "Chapter3/Problem3.9.3" (role := supporting)] _root_.RepresentationTheory.Quiver.TwoDimensionalRepresentations.zeroAuxiliaryEquivalenceData
