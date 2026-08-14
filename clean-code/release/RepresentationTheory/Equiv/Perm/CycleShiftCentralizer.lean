/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib

/-!
# Centralizers of Cycle Shifts

This module describes permutations centralizing the canonical shift on an indexed family of
finite cycles. It constructs centralizer parameter data, its action on the cycle space, and a
multiplicative equivalence with the corresponding centralizer subgroup.
-/

namespace RepresentationTheory.Equiv.Perm.CycleShiftCentralizer

open _root_.Equiv _root_.Function _root_.Subgroup

/-- Permutation of a function domain as a monoid homomorphism into multiplicative automorphisms
of group-valued functions. -/
def permuteFunctions (β M : Type*) [Group M] : _root_.Equiv.Perm β →* MulAut (β → M) where
  toFun σ :=
    { toFun := fun v => v ∘ σ.symm
      invFun := fun v => v ∘ σ
      left_inv := fun v => funext fun b => congrArg v (σ.symm_apply_apply b)
      right_inv := fun v => funext fun b => congrArg v (σ.apply_symm_apply b)
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

/-- The permuted function evaluates at a point by applying the original function to its inverse
image. -/
@[simp]
theorem permuteFunctions_apply {β M : Type*} [Group M] (σ : _root_.Equiv.Perm β)
    (v : β → M) (b : β) :
    permuteFunctions β M σ v b = v (σ.symm b) := rfl

/-- An auxiliary type associated with a label type and a natural-number cycle size. -/
abbrev CentralizerFactor (β : Type*) (m : ℕ) : Type _ :=
  SemidirectProduct (β → Multiplicative (ZMod m)) (_root_.Equiv.Perm β)
    (permuteFunctions β (Multiplicative (ZMod m)))

/-- An equivalence of label types induces a multiplicative equivalence of their auxiliary
centralizer factors. -/
def centralizerFactorCongr {β γ : Type*} (e : β ≃ γ) (m : ℕ) :
    CentralizerFactor β m ≃* CentralizerFactor γ m where
  toFun w := ⟨fun c => w.left (e.symm c), e.permCongr w.right⟩
  invFun w := ⟨fun b => w.left (e b), e.symm.permCongr w.right⟩
  left_inv w := SemidirectProduct.ext (funext fun _ => by simp) (_root_.Equiv.ext fun _ => by simp)
  right_inv w := SemidirectProduct.ext (funext fun _ => by simp) (_root_.Equiv.ext fun _ => by simp)
  map_mul' w₁ w₂ :=
    SemidirectProduct.ext
      (funext fun c => by
        simp [SemidirectProduct.mul_left, _root_.Equiv.permCongr_def])
      (_root_.Equiv.ext fun c => by simp [SemidirectProduct.mul_right])

/-- The auxiliary centralizer factor of an empty label type is a subsingleton. -/
instance centralizerFactor_subsingleton_of_isEmpty (β : Type*) [IsEmpty β] (m : ℕ) :
    Subsingleton (CentralizerFactor β m) :=
  ⟨fun _ _ => SemidirectProduct.ext (funext fun b => isEmptyElim b)
    (_root_.Equiv.ext fun b => isEmptyElim b)⟩

/-- For a finite label type, the auxiliary factor has cardinality equal to the cycle size raised to
the label cardinality times its factorial. -/
theorem card_centralizerFactor (β : Type*) [Finite β] (m : ℕ) :
    Nat.card (CentralizerFactor β m) = m ^ Nat.card β * Nat.factorial (Nat.card β) := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_perm, Nat.card_fun,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod m)), Nat.card_zmod]

/-- A dependent function space whose factors above a bound are subsingletons is equivalent to the
corresponding finite dependent function space. -/
def piEquivFin {G : ℕ → Type*} [∀ m, One (G m)] (N : ℕ)
    (h : ∀ m, N < m → Subsingleton (G m)) : (∀ m, G m) ≃ (∀ m : Fin (N + 1), G m) where
  toFun f m := f m
  invFun f m := if hm : m < N + 1 then f ⟨m, hm⟩ else 1
  left_inv f := by
    funext m
    by_cases hm : m < N + 1
    · simp [hm]
    · haveI := h m (by omega)
      simp only [hm, dif_neg, not_false_eq_true]
      exact Subsingleton.elim _ _
  right_inv f := by
    funext m
    simp [m.isLt]

variable (β : ℕ → Type*)

/-- An auxiliary type assembled from a family of types indexed by natural numbers. -/
abbrev CycleIndexSpace : Type _ := Σ m : ℕ, β m × ZMod m

/-- The canonical permutation of the indexed cycle space that advances each cyclic coordinate. -/
def cycleShift : _root_.Equiv.Perm (CycleIndexSpace β) where
  toFun s := ⟨s.1, (s.2.1, s.2.2 + 1)⟩
  invFun s := ⟨s.1, (s.2.1, s.2.2 - 1)⟩
  left_inv s := by cases s with | mk m p => cases p; simp
  right_inv s := by cases s with | mk m p => cases p; simp

/-- The cycle shift fixes the index and label and adds one to the cyclic coordinate. -/
@[simp]
theorem cycleShift_apply (m : ℕ) (b : β m) (x : ZMod m) :
    cycleShift β ⟨m, (b, x)⟩ = ⟨m, (b, x + 1)⟩ := rfl

/-- Auxiliary multiplicative data used to parametrize permutations centralizing the cycle shift. -/
abbrev CentralizerData : Type _ := ∀ m : ℕ, CentralizerFactor (β m) m

variable {β}

/-- The action of centralizer parameter data on the indexed cycle space. -/
def centralizerDataAction (w : CentralizerData β) (s : CycleIndexSpace β) : CycleIndexSpace β :=
  ⟨s.1, ((w s.1).right s.2.1,
    s.2.2 + Multiplicative.toAdd ((w s.1).left ((w s.1).right s.2.1)))⟩

/-- Centralizer data acts by permuting a cycle label and adding the associated cyclic component to
its position. -/
@[simp]
theorem centralizerDataAction_apply (w : CentralizerData β) (m : ℕ) (b : β m) (x : ZMod m) :
    centralizerDataAction w ⟨m, (b, x)⟩ =
      ⟨m, ((w m).right b, x + Multiplicative.toAdd ((w m).left ((w m).right b)))⟩ := rfl

/-- The identity centralizer datum acts as the identity. -/
@[simp]
theorem centralizerDataAction_one (s : CycleIndexSpace β) : centralizerDataAction 1 s = s := by
  obtain ⟨m, b, x⟩ := s
  simp [centralizerDataAction]

/-- The action of a product of centralizer data is the composite of the two actions. -/
theorem centralizerDataAction_mul (w₁ w₂ : CentralizerData β) (s : CycleIndexSpace β) :
    centralizerDataAction (w₁ * w₂) s =
      centralizerDataAction w₁ (centralizerDataAction w₂ s) := by
  obtain ⟨m, b, x⟩ := s
  simp only [centralizerDataAction_apply, Pi.mul_apply, SemidirectProduct.mul_right,
    SemidirectProduct.mul_left, _root_.Equiv.Perm.mul_apply, Pi.mul_apply,
    permuteFunctions_apply, toAdd_mul, _root_.Equiv.symm_apply_apply]
  rw [add_assoc, add_comm (Multiplicative.toAdd ((w₁ m).left _))]

/-- The monoid homomorphism from centralizer data to permutations of the indexed cycle space. -/
def centralizerDataPermHom : CentralizerData β →* _root_.Equiv.Perm (CycleIndexSpace β) where
  toFun w :=
    { toFun := centralizerDataAction w
      invFun := centralizerDataAction w⁻¹
      left_inv := fun s => by
        rw [← centralizerDataAction_mul, inv_mul_cancel, centralizerDataAction_one]
      right_inv := fun s => by
        rw [← centralizerDataAction_mul, mul_inv_cancel, centralizerDataAction_one] }
  map_one' := _root_.Equiv.ext centralizerDataAction_one
  map_mul' w₁ w₂ := _root_.Equiv.ext (centralizerDataAction_mul w₁ w₂)

/-- The permutation homomorphism acts on cycle points by the centralizer-data action. -/
@[simp]
theorem centralizerDataPermHom_apply (w : CentralizerData β) (s : CycleIndexSpace β) :
    centralizerDataPermHom w s = centralizerDataAction w s := rfl

/-- The action of centralizer data commutes with the canonical cycle shift. -/
theorem centralizerDataAction_cycleShift (w : CentralizerData β) (s : CycleIndexSpace β) :
    centralizerDataAction w (cycleShift β s) = cycleShift β (centralizerDataAction w s) := by
  obtain ⟨m, b, x⟩ := s
  rw [cycleShift_apply, centralizerDataAction_apply, centralizerDataAction_apply, cycleShift_apply]
  exact congrArg (Sigma.mk m) (by rw [add_right_comm])

/-- Every permutation arising from centralizer data belongs to the centralizer of the cycle
shift. -/
theorem centralizerDataPermHom_mem_centralizer (w : CentralizerData β) :
    centralizerDataPermHom w ∈ _root_.Subgroup.centralizer {cycleShift β} := by
  rw [_root_.Subgroup.mem_centralizer_singleton_iff]
  refine _root_.Equiv.ext fun s => ?_
  simp only [_root_.Equiv.Perm.mul_apply, centralizerDataPermHom_apply]
  exact centralizerDataAction_cycleShift w s

/-- Equality of two dependent pairs with the same natural-number index implies equality of their
second components. -/
theorem sigma_mk_inj {m : ℕ} {p q : β m × ZMod m}
    (h : (⟨m, p⟩ : CycleIndexSpace β) = ⟨m, q⟩) : p = q := by
  simpa using h

/-- The permutation homomorphism from centralizer data is injective. -/
theorem centralizerDataPermHom_injective :
    _root_.Function.Injective (centralizerDataPermHom (β := β)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : ∀ (m : ℕ) (b : β m) (x : ZMod m),
      centralizerDataAction w ⟨m, (b, x)⟩ = ⟨m, (b, x)⟩ := by
    intro m b x
    rw [← centralizerDataPermHom_apply, hw]
    rfl
  funext m
  have key : ∀ b : β m, ((w m).right b,
      (0 : ZMod m) + Multiplicative.toAdd ((w m).left ((w m).right b))) = (b, (0 : ZMod m)) :=
    fun b => sigma_mk_inj (hw' m b 0)
  have hσ : ∀ b : β m, (w m).right b = b := fun b => congrArg Prod.fst (key b)
  have hv : ∀ b : β m, (w m).left b = 1 := by
    intro b
    have h := congrArg Prod.snd (key b)
    rw [hσ b] at h
    simpa using h
  exact SemidirectProduct.ext (funext hv) (_root_.Equiv.ext hσ)

section Centralizer

variable {k : _root_.Equiv.Perm (CycleIndexSpace β)}

/-- A natural power of the cycle shift adds the cast of that power to the cyclic coordinate. -/
theorem cycleShift_pow_apply (j : ℕ) {m : ℕ} (b : β m) (x : ZMod m) :
    (cycleShift β ^ j) ⟨m, (b, x)⟩ = ⟨m, (b, x + j)⟩ := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, _root_.Equiv.Perm.mul_apply, cycleShift_apply, ih]
      exact congrArg (Sigma.mk m) (congrArg (Prod.mk b) (by push_cast; ring))

/-- A permutation centralizing the cycle shift commutes pointwise with every natural power of that
shift. -/
theorem apply_pow_eq_pow_apply (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    (j : ℕ) (s : CycleIndexSpace β) :
    k ((cycleShift β ^ j) s) = (cycleShift β ^ j) (k s) := by
  have h : k * cycleShift β ^ j = cycleShift β ^ j * k :=
    (Commute.pow_right (_root_.Subgroup.mem_centralizer_singleton_iff.mp hk) j)
  exact congrArg (fun (e : _root_.Equiv.Perm (CycleIndexSpace β)) => e s) h

variable [IsEmpty (β 0)]

/-- If the zeroth label type is empty, any index carrying a label is nonzero. -/
theorem neZero_index_of_nonempty {m : ℕ} (b : β m) : NeZero m :=
  ⟨fun h => IsEmpty.false (show β 0 from h ▸ b)⟩

/-- The natural-number index of the image under a centralizing permutation divides the original
cycle size. -/
theorem sigma_fst_apply_dvd (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    {m : ℕ} (b : β m) (x : ZMod m) :
    (k ⟨m, (b, x)⟩).1 ∣ m := by
  rcases h : k ⟨m, (b, x)⟩ with ⟨m', b', c⟩
  have hm' : NeZero m' := neZero_index_of_nonempty b'
  have h1 : (cycleShift β ^ m) ⟨m, (b, x)⟩ = ⟨m, (b, x)⟩ := by
    rw [cycleShift_pow_apply]; simp
  have h2 : (cycleShift β ^ m) (k ⟨m, (b, x)⟩) = k ⟨m, (b, x)⟩ := by
    rw [← apply_pow_eq_pow_apply hk, h1]
  rw [h, cycleShift_pow_apply] at h2
  have h3 : c + (m : ZMod m') = c := congrArg Prod.snd (sigma_mk_inj h2)
  exact (ZMod.natCast_eq_zero_iff m m').mp (by simpa using h3)

/-- A permutation centralizing the cycle shift preserves the natural-number index of every cycle
point. -/
theorem sigma_fst_apply (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    {m : ℕ} (b : β m) (x : ZMod m) :
    (k ⟨m, (b, x)⟩).1 = m := by
  refine Nat.dvd_antisymm (sigma_fst_apply_dvd hk b x) ?_
  rcases h : k ⟨m, (b, x)⟩ with ⟨m', b', c⟩
  have h1 := sigma_fst_apply_dvd (_root_.InvMemClass.inv_mem hk) b' c
  have h2 : k⁻¹ (⟨m', (b', c)⟩ : CycleIndexSpace β) = ⟨m, (b, x)⟩ := by
    rw [← h]; exact k.symm_apply_apply _
  rw [h2] at h1
  exact h1

/-- On each cycle label, a centralizing permutation acts by a target label and a fixed cyclic
offset. -/
theorem exists_cycleParameter (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    {m : ℕ} (b : β m) :
    ∃ p : β m × ZMod m, ∀ x : ZMod m, k ⟨m, (b, x)⟩ = ⟨m, (p.1, p.2 + x)⟩ := by
  have hm : NeZero m := neZero_index_of_nonempty b
  have h0 := sigma_fst_apply hk b (0 : ZMod m)
  rcases h : k ⟨m, (b, (0 : ZMod m))⟩ with ⟨m', b', c⟩
  rw [h] at h0
  subst h0
  refine ⟨(b', c), fun x => ?_⟩
  have hx : (⟨m', (b, x)⟩ : CycleIndexSpace β) = (cycleShift β ^ x.val) ⟨m', (b, 0)⟩ := by
    rw [cycleShift_pow_apply]
    simp
  rw [hx, apply_pow_eq_pow_apply hk, h, cycleShift_pow_apply]
  simp

/-- The target label and cyclic offset associated with a centralizing permutation and a cycle
label. -/
noncomputable def cycleParameter (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    {m : ℕ} (b : β m) :
    β m × ZMod m :=
  (exists_cycleParameter hk b).choose

/-- A centralizing permutation sends a cycle point to the parameterized target label and adds the
associated cyclic offset. -/
theorem apply_eq_cycleParameter (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    {m : ℕ} (b : β m) (x : ZMod m) :
    k ⟨m, (b, x)⟩ = ⟨m, ((cycleParameter hk b).1, (cycleParameter hk b).2 + x)⟩ :=
  (exists_cycleParameter hk b).choose_spec x

/-- The first components of the cycle parameters for a centralizing permutation and its inverse
compose to the identity in one order. -/
theorem cycleParameter_fst_leftInverse
    (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β}) {m : ℕ} (b : β m) :
    (cycleParameter (_root_.InvMemClass.inv_mem hk) (cycleParameter hk b).1).1 = b := by
  have h : k⁻¹ (k ⟨m, (b, (0 : ZMod m))⟩) = ⟨m, (b, (0 : ZMod m))⟩ :=
    k.symm_apply_apply _
  rw [apply_eq_cycleParameter hk b 0,
    apply_eq_cycleParameter (_root_.InvMemClass.inv_mem hk)] at h
  exact congrArg Prod.fst (sigma_mk_inj h)

/-- The first components of the cycle parameters for a centralizing permutation and its inverse
compose to the identity in the other order. -/
theorem cycleParameter_fst_rightInverse
    (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β}) {m : ℕ} (b : β m) :
    (cycleParameter hk (cycleParameter (_root_.InvMemClass.inv_mem hk) b).1).1 = b := by
  have h : k (k⁻¹ ⟨m, (b, (0 : ZMod m))⟩) = ⟨m, (b, (0 : ZMod m))⟩ :=
    k.apply_symm_apply _
  rw [apply_eq_cycleParameter (_root_.InvMemClass.inv_mem hk) b 0,
    apply_eq_cycleParameter hk] at h
  exact congrArg Prod.fst (sigma_mk_inj h)

/-- The permutation induced on labels of a fixed cycle size by a permutation centralizing the
cycle shift. -/
noncomputable def cycleLabelPerm (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    (m : ℕ) : _root_.Equiv.Perm (β m) where
  toFun b := (cycleParameter hk b).1
  invFun b := (cycleParameter (_root_.InvMemClass.inv_mem hk) b).1
  left_inv b := cycleParameter_fst_leftInverse hk b
  right_inv b := cycleParameter_fst_rightInverse hk b

/-- The induced permutation on cycle labels is the first component of the associated cycle
parameter. -/
@[simp]
theorem cycleLabelPerm_apply (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β})
    {m : ℕ} (b : β m) :
    cycleLabelPerm hk m b = (cycleParameter hk b).1 := rfl

/-- Centralizer parameter data extracted from a permutation belonging to the cycle-shift
centralizer. -/
noncomputable def centralizerDataOfMem
    (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β}) : CentralizerData β := fun m =>
  { left := fun b => Multiplicative.ofAdd (cycleParameter hk ((cycleLabelPerm hk m).symm b)).2
    right := cycleLabelPerm hk m }

/-- Extracting data from a centralizing permutation and mapping it back recovers the original
permutation. -/
theorem centralizerDataPermHom_fromCentralizer
    (hk : k ∈ _root_.Subgroup.centralizer {cycleShift β}) :
    centralizerDataPermHom (centralizerDataOfMem hk) = k := by
  refine _root_.Equiv.ext fun s => ?_
  obtain ⟨m, b, x⟩ := s
  rw [centralizerDataPermHom_apply, centralizerDataAction_apply, apply_eq_cycleParameter hk b x]
  simp only [centralizerDataOfMem, ← cycleLabelPerm_apply hk b,
    _root_.Equiv.symm_apply_apply, toAdd_ofAdd]
  rw [add_comm]

/-- A multiplicative equivalence between centralizer data and the subgroup of permutations
centralizing the cycle shift. -/
noncomputable def centralizerDataEquiv :
    CentralizerData β ≃* _root_.Subgroup.centralizer {cycleShift β} :=
  MulEquiv.ofBijective (centralizerDataPermHom.codRestrict _ centralizerDataPermHom_mem_centralizer)
    ⟨fun _ _ h => centralizerDataPermHom_injective (congrArg Subtype.val h),
      fun k => ⟨centralizerDataOfMem k.2,
        Subtype.ext (centralizerDataPermHom_fromCentralizer k.2)⟩⟩

/-- The permutation underlying the centralizer-data equivalence agrees with the permutation
homomorphism. -/
@[simp]
theorem coe_centralizerDataEquiv (w : CentralizerData β) :
    (centralizerDataEquiv w : _root_.Equiv.Perm (CycleIndexSpace β)) =
      centralizerDataPermHom w := rfl

end Centralizer

end RepresentationTheory.Equiv.Perm.CycleShiftCentralizer
