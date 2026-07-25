import Mathlib

/-!
# The centralizer of a permutation is a product of wreath products

For a permutation `g` of a finite set with `iₘ` cycles of length `m` (counting fixed points as
cycles of length `1`), the centralizer of `g` in the symmetric group is

`∏ₘ (ℤ/mℤ)^{iₘ} ⋊ S_{iₘ}`,

the displayed group of the proof of Theorem 5.14.3 in the book (written there as
`∏ₘ S_{iₘ} ⋉ (ℤ/mℤ)^{iₘ}`; the two orientations differ only in which factor is written first).

This file develops the *standard model*: instead of an arbitrary permutation it treats the shift
on `Σ m, β m × ZMod m`, a disjoint union of cycles that has already been grouped by length. The
transport of the result to an arbitrary permutation is in
`EtingofRepresentationTheory/Chapter5/Theorem5_14_3_Centralizer.lean`.

## Main definitions

* `Etingof.Wreath.coordAut β M` : the coordinate-permutation action of `Equiv.Perm β` on `β → M`.
* `Etingof.Wreath.WreathBlock β m` : the block `(β → Multiplicative (ZMod m)) ⋊ Equiv.Perm β`.
* `Etingof.Wreath.Std β` : the standard `g`-set `Σ m, β m × ZMod m`.
* `Etingof.Wreath.stdShift β` : the standard permutation, rotating each cycle by one step.
* `Etingof.Wreath.stdHom β : (∀ m, WreathBlock (β m) m) →* Equiv.Perm (Std β)`.

## Main results

* `Etingof.Wreath.stdHom_injective`
* `Etingof.Wreath.stdCentralizerMulEquiv` :
  `(∀ m, WreathBlock (β m) m) ≃* centralizer {stdShift β}`.
-/

namespace Etingof.Wreath

open Equiv Function Subgroup

/-- The coordinate-permutation action of `Equiv.Perm β` on functions `β → M`:
`σ` sends `v` to `v ∘ σ⁻¹`. -/
def coordAut (β M : Type*) [Group M] : Perm β →* MulAut (β → M) where
  toFun σ :=
    { toFun := fun v => v ∘ σ.symm
      invFun := fun v => v ∘ σ
      left_inv := fun v => funext fun b => congrArg v (σ.symm_apply_apply b)
      right_inv := fun v => funext fun b => congrArg v (σ.apply_symm_apply b)
      map_mul' := fun _ _ => rfl }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' _ _ := MulEquiv.ext fun _ => rfl

@[simp]
theorem coordAut_apply {β M : Type*} [Group M] (σ : Perm β) (v : β → M) (b : β) :
    coordAut β M σ v b = v (σ.symm b) := rfl

/-- The homogeneous block of the centralizer belonging to cycles of length `m`: the wreath
product `(ℤ/mℤ)^β ⋊ S_β`, where `S_β` permutes the coordinates. Here `β` indexes the cycles
of length `m`. -/
abbrev WreathBlock (β : Type*) (m : ℕ) : Type _ :=
  SemidirectProduct (β → Multiplicative (ZMod m)) (Perm β)
    (coordAut β (Multiplicative (ZMod m)))

/-- Reindexing the cycles of a fixed length by an equivalent type. -/
def wreathBlockCongr {β γ : Type*} (e : β ≃ γ) (m : ℕ) : WreathBlock β m ≃* WreathBlock γ m where
  toFun w := ⟨fun c => w.left (e.symm c), e.permCongr w.right⟩
  invFun w := ⟨fun b => w.left (e b), e.symm.permCongr w.right⟩
  left_inv w := SemidirectProduct.ext (funext fun _ => by simp) (Equiv.ext fun _ => by simp)
  right_inv w := SemidirectProduct.ext (funext fun _ => by simp) (Equiv.ext fun _ => by simp)
  map_mul' w₁ w₂ :=
    SemidirectProduct.ext
      (funext fun c => by
        simp [SemidirectProduct.mul_left, Equiv.permCongr_def])
      (Equiv.ext fun c => by simp [SemidirectProduct.mul_right])

instance wreathBlock_subsingleton (β : Type*) [IsEmpty β] (m : ℕ) :
    Subsingleton (WreathBlock β m) :=
  ⟨fun _ _ => SemidirectProduct.ext (funext fun b => isEmptyElim b)
    (Equiv.ext fun b => isEmptyElim b)⟩

/-- The order of a wreath block: `|(ℤ/mℤ)^β ⋊ S_β| = m^{|β|} · |β|!`. -/
theorem nat_card_wreathBlock (β : Type*) [Finite β] (m : ℕ) :
    Nat.card (WreathBlock β m) = m ^ Nat.card β * Nat.factorial (Nat.card β) := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_perm, Nat.card_fun,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod m)), Nat.card_zmod]

/-- A dependent product over `ℕ` whose factors above `N` are all trivial is the finite product
of the first `N + 1` factors. -/
def piTruncEquiv {G : ℕ → Type*} [∀ m, One (G m)] (N : ℕ)
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

/-- The standard set on which a permutation with `β m` cycles of length `m` acts: a disjoint
union of cycles, the length-`m` ones indexed by `β m`, each cycle being a copy of `ZMod m`. -/
abbrev Std : Type _ := Σ m : ℕ, β m × ZMod m

/-- The standard permutation of `Std β`: rotate every cycle by one step. -/
def stdShift : Perm (Std β) where
  toFun s := ⟨s.1, (s.2.1, s.2.2 + 1)⟩
  invFun s := ⟨s.1, (s.2.1, s.2.2 - 1)⟩
  left_inv s := by cases s with | mk m p => cases p; simp
  right_inv s := by cases s with | mk m p => cases p; simp

@[simp]
theorem stdShift_apply (m : ℕ) (b : β m) (x : ZMod m) :
    stdShift β ⟨m, (b, x)⟩ = ⟨m, (b, x + 1)⟩ := rfl

/-- The full wreath group `∏ₘ (ℤ/mℤ)^{β m} ⋊ S_{β m}`. Only finitely many factors are
nontrivial in the application, but nothing here needs that. -/
abbrev StdWreath : Type _ := ∀ m : ℕ, WreathBlock (β m) m

variable {β}

/-- The action of the wreath group on the standard set: the `Perm (β m)` part permutes the
length-`m` cycles, and the `(ℤ/mℤ)^{β m}` part rotates each cycle. -/
def stdAct (w : StdWreath β) (s : Std β) : Std β :=
  ⟨s.1, ((w s.1).right s.2.1,
    s.2.2 + Multiplicative.toAdd ((w s.1).left ((w s.1).right s.2.1)))⟩

@[simp]
theorem stdAct_apply (w : StdWreath β) (m : ℕ) (b : β m) (x : ZMod m) :
    stdAct w ⟨m, (b, x)⟩ =
      ⟨m, ((w m).right b, x + Multiplicative.toAdd ((w m).left ((w m).right b)))⟩ := rfl

@[simp]
theorem stdAct_one (s : Std β) : stdAct 1 s = s := by
  obtain ⟨m, b, x⟩ := s
  simp [stdAct]

theorem stdAct_mul (w₁ w₂ : StdWreath β) (s : Std β) :
    stdAct (w₁ * w₂) s = stdAct w₁ (stdAct w₂ s) := by
  obtain ⟨m, b, x⟩ := s
  simp only [stdAct_apply, Pi.mul_apply, SemidirectProduct.mul_right, SemidirectProduct.mul_left,
    Perm.mul_apply, Pi.mul_apply, coordAut_apply, toAdd_mul, Equiv.symm_apply_apply]
  rw [add_assoc, add_comm (Multiplicative.toAdd ((w₁ m).left _))]

/-- The wreath group acts on the standard set by permutations. -/
def stdHom : StdWreath β →* Perm (Std β) where
  toFun w :=
    { toFun := stdAct w
      invFun := stdAct w⁻¹
      left_inv := fun s => by rw [← stdAct_mul, inv_mul_cancel, stdAct_one]
      right_inv := fun s => by rw [← stdAct_mul, mul_inv_cancel, stdAct_one] }
  map_one' := Equiv.ext stdAct_one
  map_mul' w₁ w₂ := Equiv.ext (stdAct_mul w₁ w₂)

@[simp]
theorem stdHom_apply (w : StdWreath β) (s : Std β) : stdHom w s = stdAct w s := rfl

theorem stdAct_stdShift (w : StdWreath β) (s : Std β) :
    stdAct w (stdShift β s) = stdShift β (stdAct w s) := by
  obtain ⟨m, b, x⟩ := s
  rw [stdShift_apply, stdAct_apply, stdAct_apply, stdShift_apply]
  exact congrArg (Sigma.mk m) (by rw [add_right_comm])

theorem stdHom_mem_centralizer (w : StdWreath β) :
    stdHom w ∈ centralizer {stdShift β} := by
  rw [mem_centralizer_singleton_iff]
  refine Equiv.ext fun s => ?_
  simp only [Perm.mul_apply, stdHom_apply]
  exact stdAct_stdShift w s

/-- Two elements of `Std β` in the same block are equal exactly when their data agree. -/
theorem std_mk_inj {m : ℕ} {p q : β m × ZMod m} (h : (⟨m, p⟩ : Std β) = ⟨m, q⟩) : p = q := by
  simpa using h

/-- `stdHom` is injective: a wreath element acting trivially is trivial. -/
theorem stdHom_injective : Function.Injective (stdHom (β := β)) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : ∀ (m : ℕ) (b : β m) (x : ZMod m), stdAct w ⟨m, (b, x)⟩ = ⟨m, (b, x)⟩ := by
    intro m b x
    rw [← stdHom_apply, hw]
    rfl
  funext m
  have key : ∀ b : β m, ((w m).right b,
      (0 : ZMod m) + Multiplicative.toAdd ((w m).left ((w m).right b))) = (b, (0 : ZMod m)) :=
    fun b => std_mk_inj (hw' m b 0)
  have hσ : ∀ b : β m, (w m).right b = b := fun b => congrArg Prod.fst (key b)
  have hv : ∀ b : β m, (w m).left b = 1 := by
    intro b
    have h := congrArg Prod.snd (key b)
    rw [hσ b] at h
    simpa using h
  exact SemidirectProduct.ext (funext hv) (Equiv.ext hσ)

section Centralizer

variable {k : Perm (Std β)}

theorem stdShift_pow (j : ℕ) {m : ℕ} (b : β m) (x : ZMod m) :
    (stdShift β ^ j) ⟨m, (b, x)⟩ = ⟨m, (b, x + j)⟩ := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Perm.mul_apply, stdShift_apply, ih]
      exact congrArg (Sigma.mk m) (congrArg (Prod.mk b) (by push_cast; ring))

theorem apply_stdShift_pow (hk : k ∈ centralizer {stdShift β}) (j : ℕ) (s : Std β) :
    k ((stdShift β ^ j) s) = (stdShift β ^ j) (k s) := by
  have h : k * stdShift β ^ j = stdShift β ^ j * k :=
    (Commute.pow_right (mem_centralizer_singleton_iff.mp hk) j)
  exact congrArg (fun (e : Perm (Std β)) => e s) h

variable [IsEmpty (β 0)]

/-- Every index carrying a cycle is nonzero: there are no cycles of length `0`. -/
theorem neZero_of_elt {m : ℕ} (b : β m) : NeZero m :=
  ⟨fun h => IsEmpty.false (show β 0 from h ▸ b)⟩

/-- A permutation commuting with the shift maps the block of length-`m` cycles into a block
whose length divides `m`. -/
theorem fst_apply_dvd (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) (x : ZMod m) :
    (k ⟨m, (b, x)⟩).1 ∣ m := by
  rcases h : k ⟨m, (b, x)⟩ with ⟨m', b', c⟩
  have hm' : NeZero m' := neZero_of_elt b'
  have h1 : (stdShift β ^ m) ⟨m, (b, x)⟩ = ⟨m, (b, x)⟩ := by
    rw [stdShift_pow]; simp
  have h2 : (stdShift β ^ m) (k ⟨m, (b, x)⟩) = k ⟨m, (b, x)⟩ := by
    rw [← apply_stdShift_pow hk, h1]
  rw [h, stdShift_pow] at h2
  have h3 : c + (m : ZMod m') = c := congrArg Prod.snd (std_mk_inj h2)
  exact (ZMod.natCast_eq_zero_iff m m').mp (by simpa using h3)

/-- A permutation commuting with the shift preserves cycle lengths. -/
theorem fst_apply (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) (x : ZMod m) :
    (k ⟨m, (b, x)⟩).1 = m := by
  refine Nat.dvd_antisymm (fst_apply_dvd hk b x) ?_
  rcases h : k ⟨m, (b, x)⟩ with ⟨m', b', c⟩
  have h1 := fst_apply_dvd (inv_mem hk) b' c
  have h2 : k⁻¹ (⟨m', (b', c)⟩ : Std β) = ⟨m, (b, x)⟩ := by
    rw [← h]; exact k.symm_apply_apply _
  rw [h2] at h1
  exact h1

/-- The key structure lemma: a permutation commuting with the shift rotates each cycle by a
fixed amount and permutes the cycles of each fixed length. -/
theorem exists_blockRep (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) :
    ∃ p : β m × ZMod m, ∀ x : ZMod m, k ⟨m, (b, x)⟩ = ⟨m, (p.1, p.2 + x)⟩ := by
  have hm : NeZero m := neZero_of_elt b
  have h0 := fst_apply hk b (0 : ZMod m)
  rcases h : k ⟨m, (b, (0 : ZMod m))⟩ with ⟨m', b', c⟩
  rw [h] at h0
  subst h0
  refine ⟨(b', c), fun x => ?_⟩
  have hx : (⟨m', (b, x)⟩ : Std β) = (stdShift β ^ x.val) ⟨m', (b, 0)⟩ := by
    rw [stdShift_pow]
    simp
  rw [hx, apply_stdShift_pow hk, h, stdShift_pow]
  simp

/-- The cycle permutation and rotation amounts read off from a centralizing permutation. -/
noncomputable def blockRep (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) :
    β m × ZMod m :=
  (exists_blockRep hk b).choose

theorem blockRep_spec (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) (x : ZMod m) :
    k ⟨m, (b, x)⟩ = ⟨m, ((blockRep hk b).1, (blockRep hk b).2 + x)⟩ :=
  (exists_blockRep hk b).choose_spec x

theorem blockRep_fst_leftInv (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) :
    (blockRep (inv_mem hk) (blockRep hk b).1).1 = b := by
  have h : k⁻¹ (k ⟨m, (b, (0 : ZMod m))⟩) = ⟨m, (b, (0 : ZMod m))⟩ := k.symm_apply_apply _
  rw [blockRep_spec hk b 0, blockRep_spec (inv_mem hk)] at h
  exact congrArg Prod.fst (std_mk_inj h)

theorem blockRep_fst_rightInv (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) :
    (blockRep hk (blockRep (inv_mem hk) b).1).1 = b := by
  have h : k (k⁻¹ ⟨m, (b, (0 : ZMod m))⟩) = ⟨m, (b, (0 : ZMod m))⟩ := k.apply_symm_apply _
  rw [blockRep_spec (inv_mem hk) b 0, blockRep_spec hk] at h
  exact congrArg Prod.fst (std_mk_inj h)

/-- The permutation of the length-`m` cycles induced by a centralizing permutation. -/
noncomputable def blockPerm (hk : k ∈ centralizer {stdShift β}) (m : ℕ) : Perm (β m) where
  toFun b := (blockRep hk b).1
  invFun b := (blockRep (inv_mem hk) b).1
  left_inv b := blockRep_fst_leftInv hk b
  right_inv b := blockRep_fst_rightInv hk b

@[simp]
theorem blockPerm_apply (hk : k ∈ centralizer {stdShift β}) {m : ℕ} (b : β m) :
    blockPerm hk m b = (blockRep hk b).1 := rfl

/-- The wreath element corresponding to a centralizing permutation. -/
noncomputable def toWreath (hk : k ∈ centralizer {stdShift β}) : StdWreath β := fun m =>
  { left := fun b => Multiplicative.ofAdd (blockRep hk ((blockPerm hk m).symm b)).2
    right := blockPerm hk m }

theorem stdHom_toWreath (hk : k ∈ centralizer {stdShift β}) : stdHom (toWreath hk) = k := by
  refine Equiv.ext fun s => ?_
  obtain ⟨m, b, x⟩ := s
  rw [stdHom_apply, stdAct_apply, blockRep_spec hk b x]
  simp only [toWreath, ← blockPerm_apply hk b, Equiv.symm_apply_apply, toAdd_ofAdd]
  rw [add_comm]

/-- **The centralizer of the standard permutation is the product of its wreath blocks.**
This is the group `∏ₘ S_{iₘ} ⋉ (ℤ/mℤ)^{iₘ}` displayed in the proof of Theorem 5.14.3. -/
noncomputable def stdCentralizerMulEquiv : StdWreath β ≃* centralizer {stdShift β} :=
  MulEquiv.ofBijective (stdHom.codRestrict _ stdHom_mem_centralizer)
    ⟨fun _ _ h => stdHom_injective (congrArg Subtype.val h),
      fun k => ⟨toWreath k.2, Subtype.ext (stdHom_toWreath k.2)⟩⟩

@[simp]
theorem stdCentralizerMulEquiv_apply (w : StdWreath β) :
    (stdCentralizerMulEquiv w : Perm (Std β)) = stdHom w := rfl

end Centralizer

end Etingof.Wreath
