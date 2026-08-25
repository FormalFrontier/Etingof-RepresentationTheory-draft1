import EtingofRepresentationTheory.Chapter2.Problem2_11_3_SymExtPow
import Mathlib.Data.Sym.Card

/-!
# Problem 2.11.3(d), symmetric case: universal property, basis and dimension of `S^n V`

`Problem2_11_3_SymExtPow.lean` constructs Etingof's quotient model
`SymPow k V n = V^{⊗ n} ⧸ span {T - s(T)}` together with the canonical symmetric multilinear map
`symTprod`. This file supplies the three things that turn that construction into the symmetric
half of part (d) of the problem:

* the universal property of `S^n V`;
* a basis of `S^n V` indexed by multisets of basis indices of `V`;
* the resulting dimension formula `dim S^n V = (m + n - 1).choose n` when `dim V = m`.

The route is the one the exterior half could not use. Mathlib's `SymmetricPower` is a bare
quotient with no universal property, no basis and no grading, so everything here is built from
scratch out of `Module.Basis.piTensorProduct`: the basis of `V^{⊗ n}` indexed by tuples
`g : Fin n → I` is permuted by `permAct`, and `S^n V` is the quotient of a free module by the
span of the differences along those permutation orbits, so it is free on the orbit set. The
orbits are exactly the fibres of `tupleSym : (Fin n → I) → Sym I n`, the multiset of entries.

## Main definitions

* `Etingof.Problem2_11_3.tupleSym` : the multiset of entries of a tuple `Fin n → I`.
* `Etingof.Problem2_11_3.symPowLift` : the descent of a symmetric multilinear map to `S^n V`.
* `Etingof.Problem2_11_3.symPowLiftEquiv` : the universal property of `S^n V`, packaged as a
  bijection between linear maps `S^n V → N` and symmetric multilinear maps `V^n → N`.
* `Etingof.Problem2_11_3.tensorPowBasis` : the basis of `V^{⊗ n}` induced by a basis of `V`.
* `Etingof.Problem2_11_3.symPowBasis` : **Problem 2.11.3(d), symmetric case** — the basis of
  `S^n V` indexed by `Sym I n`.

## Main results

* `Etingof.Problem2_11_3.exists_perm_of_map_univ_val_eq` : two tuples indexed by a finite type
  with the same multiset of entries differ by a permutation of the index type.
* `Etingof.Problem2_11_3.symPowBasis_apply` : the basis vector at a multiset `s` is the class of
  *any* pure tensor `v_{g 0} ⊗ ⋯ ⊗ v_{g (n-1)}` whose indices realise `s`.
* `Etingof.Problem2_11_3.finrank_symPow` : **Problem 2.11.3(d), symmetric case** — if
  `dim V = m` then `dim S^n V = (m + n - 1).choose n`, restated as
  `Nat.multichoose m n` in `finrank_symPow_eq_multichoose`.
-/

namespace Etingof.Problem2_11_3

open PiTensorProduct

/-! ### Tuples with the same multiset of entries -/

section Tuples

/-- Two families indexed by a finite type that take the same values with the same multiplicities
differ by a permutation of the index type. -/
theorem exists_perm_of_map_univ_val_eq {ι I : Type*} [Fintype ι] {f g : ι → I}
    (h : (Finset.univ : Finset ι).val.map f = (Finset.univ : Finset ι).val.map g) :
    ∃ σ : Equiv.Perm ι, f = g ∘ σ := by
  classical
  have hcard : ∀ c : I, Fintype.card {i // f i = c} = Fintype.card {i // g i = c} := by
    intro c
    have hc := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    simp only [Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    simpa only [eq_comm] using hc
  refine ⟨Equiv.ofFiberEquiv (f := f) (g := g) fun c => Fintype.equivOfCardEq (hcard c), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm

/-- The multiset of entries of a tuple `g : Fin n → I`, as an element of `Sym I n`. -/
def tupleSym {I : Type*} {n : ℕ} (g : Fin n → I) : Sym I n :=
  ⟨(Finset.univ : Finset (Fin n)).val.map g, by simp⟩

/-- Coercing a tuple multiset exposes the multiset obtained by mapping the tuple over Fin n. -/
@[simp]
lemma tupleSym_coe {I : Type*} {n : ℕ} (g : Fin n → I) :
    (tupleSym g : Multiset I) = (Finset.univ : Finset (Fin n)).val.map g := rfl

/-- Permuting the entries of a tuple does not change its associated multiset. -/
@[simp]
lemma tupleSym_comp_perm {I : Type*} {n : ℕ} (g : Fin n → I) (σ : Equiv.Perm (Fin n)) :
    tupleSym (fun i => g (σ i)) = tupleSym g := by
  refine Sym.ext ?_
  rw [tupleSym_coe, tupleSym_coe, show (fun i => g (σ i)) = g ∘ σ from rfl, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

/-- Two tuples have the same multiset of entries exactly when they differ by a permutation of
`Fin n`. -/
lemma tupleSym_eq_iff {I : Type*} {n : ℕ} {g h : Fin n → I} :
    tupleSym g = tupleSym h ↔ ∃ σ : Equiv.Perm (Fin n), g = fun i => h (σ i) := by
  constructor
  · intro hgh
    obtain ⟨σ, hσ⟩ := exists_perm_of_map_univ_val_eq
      (f := g) (g := h) (by simpa using congrArg Sym.toMultiset hgh)
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    exact tupleSym_comp_perm h σ

/-- Every multiset of size `n` is the multiset of entries of some tuple `Fin n → I`. -/
lemma tupleSym_surjective {I : Type*} {n : ℕ} :
    Function.Surjective (tupleSym (I := I) (n := n)) := by
  intro s
  have hlen : (s : Multiset I).toList.length = n := by
    rw [Multiset.length_toList]; exact s.2
  refine ⟨fun i => (s : Multiset I).toList.get (Fin.cast hlen.symm i), Sym.ext ?_⟩
  rw [tupleSym_coe, Fin.univ_val_map, ← List.ofFn_congr hlen, List.ofFn_get,
    Multiset.coe_toList]

end Tuples

/-! ### The universal property of `S^n V` -/

section UniversalProperty

variable {k : Type*} [CommRing k] {V N : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup N] [Module k N]

/-- Any linear map out of `V^{⊗ n}` invariant under permuting the tensor factors kills the
relations defining the book's `S^n V`. -/
lemma symRelSubmodule_le_ker {n : ℕ} (Φ : TensorPow k V n →ₗ[k] N)
    (hΦ : ∀ (σ : Equiv.Perm (Fin n)) (T : TensorPow k V n), Φ (permAct σ T) = Φ T) :
    symRelSubmodule k V n ≤ LinearMap.ker Φ := by
  rw [symRelSubmodule, Submodule.span_le]
  rintro _ ⟨T, i, j, hij, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hΦ, sub_self]

/-- A multilinear map invariant under permuting its arguments induces a permutation-invariant
linear map on `V^{⊗ n}`. -/
lemma lift_permAct {n : ℕ} (φ : MultilinearMap k (fun _ : Fin n => V) N)
    (hφ : ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f)
    (σ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    PiTensorProduct.lift φ (permAct σ T) = PiTensorProduct.lift φ T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      simp only [map_smul, permAct_tprod, PiTensorProduct.lift.tprod]
      rw [hφ σ.symm f]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- **The universal property of the book's `S^n V`.** A multilinear map `V^n → N` invariant under
permuting its arguments descends to a linear map `S^n V → N`. -/
def symPowLift {n : ℕ} (φ : MultilinearMap k (fun _ : Fin n => V) N)
    (hφ : ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f) :
    SymPow k V n →ₗ[k] N :=
  Submodule.liftQ _ (PiTensorProduct.lift φ) (symRelSubmodule_le_ker _ (lift_permAct φ hφ))

/-- The descended map agrees with the original multilinear map on pure symmetric tensors. -/
lemma symPowLift_symTprod {n : ℕ} (φ : MultilinearMap k (fun _ : Fin n => V) N)
    (hφ : ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f)
    (f : Fin n → V) : symPowLift φ hφ (symTprod k V n f) = φ f := by
  simp [symPowLift, symTprod, Submodule.liftQ_apply]

/-- Linear maps out of `S^n V` are determined by their values on the classes of pure tensors. -/
lemma symPow_ext {n : ℕ} {F G : SymPow k V n →ₗ[k] N}
    (h : ∀ f : Fin n → V, F (symTprod k V n f) = G (symTprod k V n f)) : F = G := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, rfl⟩ := Submodule.mkQ_surjective _ x
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      have := h f
      simp only [symTprod_apply, Submodule.mkQ_apply] at this
      simp only [Submodule.mkQ_apply, map_smul, this]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (k V N) in
/-- **The universal property of the book's `S^n V`, packaged as a bijection.** Linear maps
`S^n V → N` correspond to multilinear maps `V^n → N` invariant under permuting the arguments. -/
def symPowLiftEquiv (n : ℕ) :
    {φ : MultilinearMap k (fun _ : Fin n => V) N //
      ∀ (σ : Equiv.Perm (Fin n)) (f : Fin n → V), φ (fun l => f (σ l)) = φ f} ≃
      (SymPow k V n →ₗ[k] N) where
  toFun φ := symPowLift φ.1 φ.2
  invFun F := ⟨F.compMultilinearMap (symTprod k V n), fun σ f => by
    simp only [LinearMap.compMultilinearMap_apply, symTprod_comp_perm]⟩
  left_inv φ := by
    ext f
    exact symPowLift_symTprod φ.1 φ.2 f
  right_inv F := by
    refine symPow_ext fun f => ?_
    exact symPowLift_symTprod (F.compMultilinearMap (symTprod k V n)) _ f

end UniversalProperty

/-! ### A basis of `S^n V` -/

section Basis

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
  {I : Type*} (b : Module.Basis I k V) (n : ℕ)

/-- The basis of `V^{⊗ n}` induced by a basis `b` of `V`, indexed by tuples `Fin n → I`. -/
noncomputable def tensorPowBasis : Module.Basis (Fin n → I) k (TensorPow k V n) :=
  Basis.piTensorProduct fun _ : Fin n => b

/-- The tensor-power basis evaluates to the corresponding pure tensor of basis vectors. -/
@[simp]
lemma tensorPowBasis_apply (g : Fin n → I) :
    tensorPowBasis b n g = PiTensorProduct.tprod k fun i => b (g i) :=
  Basis.piTensorProduct_apply _ _

/-- Permuting a tensor-basis vector permutes its tuple of basis indices. -/
lemma permAct_tensorPowBasis (σ : Equiv.Perm (Fin n)) (g : Fin n → I) :
    permAct σ (tensorPowBasis b n g) = tensorPowBasis b n (g ∘ σ.symm) := by
  simp [Function.comp_def]

/-- Basis tensors whose index tuples have the same multiset of entries become equal in `S^n V`. -/
lemma symTprod_basis_eq_of_tupleSym_eq {g h : Fin n → I} (hgh : tupleSym g = tupleSym h) :
    symTprod k V n (fun i => b (g i)) = symTprod k V n fun i => b (h i) := by
  obtain ⟨σ, rfl⟩ := tupleSym_eq_iff.1 hgh
  exact symTprod_comp_perm σ fun i => b (h i)

/-- The linear map `V^{⊗ n} → (Sym I n →₀ k)` sending a basis tensor to the basis element indexed
by its multiset of indices. -/
noncomputable def tensorPowToSymFinsupp : TensorPow k V n →ₗ[k] Sym I n →₀ k :=
  Finsupp.lmapDomain k k tupleSym ∘ₗ (tensorPowBasis b n).repr.toLinearMap

/-- The coefficient map sends a tensor-basis vector to the corresponding Finsupp singleton. -/
lemma tensorPowToSymFinsupp_basis (g : Fin n → I) :
    tensorPowToSymFinsupp b n (tensorPowBasis b n g) = Finsupp.single (tupleSym g) 1 := by
  rw [tensorPowToSymFinsupp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_self, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The coefficient map sends a pure tensor of basis vectors to its multiset singleton. -/
@[simp]
lemma tensorPowToSymFinsupp_tprod (g : Fin n → I) :
    tensorPowToSymFinsupp b n (PiTensorProduct.tprod k fun i => b (g i))
      = Finsupp.single (tupleSym g) 1 := by
  rw [← tensorPowBasis_apply b n g, tensorPowToSymFinsupp_basis]

/-- The coefficient map is invariant under permutation of tensor factors. -/
lemma tensorPowToSymFinsupp_permAct (σ : Equiv.Perm (Fin n)) (T : TensorPow k V n) :
    tensorPowToSymFinsupp b n (permAct σ T) = tensorPowToSymFinsupp b n T := by
  have key : tensorPowToSymFinsupp b n ∘ₗ (permAct (k := k) (V := V) σ).toLinearMap
      = tensorPowToSymFinsupp b n := by
    refine (tensorPowBasis b n).ext fun g => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, permAct_tensorPowBasis,
      tensorPowToSymFinsupp_basis, tensorPowToSymFinsupp_basis,
      show (g ∘ ⇑σ.symm) = fun i => g (σ.symm i) from rfl, tupleSym_comp_perm]
  exact congrArg (fun F => F T) key

/-- The descent of `tensorPowToSymFinsupp` to `S^n V`. -/
noncomputable def symPowToFinsupp : SymPow k V n →ₗ[k] Sym I n →₀ k :=
  Submodule.liftQ _ (tensorPowToSymFinsupp b n)
    (symRelSubmodule_le_ker _ (tensorPowToSymFinsupp_permAct b n))

/-- The descended coefficient map sends a pure symmetric basis tensor to its singleton. -/
lemma symPowToFinsupp_symTprod (g : Fin n → I) :
    symPowToFinsupp b n (symTprod k V n fun i => b (g i)) = Finsupp.single (tupleSym g) 1 := by
  rw [symTprod_apply, symPowToFinsupp, Submodule.mkQ_apply, Submodule.liftQ_apply,
    tensorPowToSymFinsupp_tprod]

/-- A tuple realising a given multiset of basis indices. -/
noncomputable def symIndexRep : Sym I n → Fin n → I :=
  Function.surjInv tupleSym_surjective

/-- The chosen tuple representative has the prescribed multiset of entries. -/
@[simp]
lemma tupleSym_symIndexRep (s : Sym I n) : tupleSym (symIndexRep n s) = s :=
  Function.surjInv_eq tupleSym_surjective s

/-- The map `(Sym I n →₀ k) → S^n V` sending a multiset to the class of any pure tensor of basis
vectors realising it. -/
noncomputable def finsuppToSymPow : (Sym I n →₀ k) →ₗ[k] SymPow k V n :=
  Finsupp.linearCombination k fun s => symTprod k V n fun i => b (symIndexRep n s i)

/-- The reconstruction map sends a Finsupp singleton to the corresponding symmetric tensor. -/
@[simp]
lemma finsuppToSymPow_single (s : Sym I n) (c : k) :
    finsuppToSymPow b n (Finsupp.single s c)
      = c • symTprod k V n fun i => b (symIndexRep n s i) := by
  simp [finsuppToSymPow]

/-- **Problem 2.11.3(d), symmetric case.** A basis `{vᵢ}` of `V` identifies the book's `S^n V`
with the free module on the multisets of size `n` of basis indices. -/
noncomputable def symPowEquivFinsupp : SymPow k V n ≃ₗ[k] Sym I n →₀ k :=
  LinearEquiv.ofLinear (symPowToFinsupp b n) (finsuppToSymPow b n)
    (by
      refine Finsupp.lhom_ext' fun s => LinearMap.ext_ring ?_
      change symPowToFinsupp b n (finsuppToSymPow b n (Finsupp.single s 1)) = Finsupp.single s 1
      rw [finsuppToSymPow_single, one_smul, symPowToFinsupp_symTprod, tupleSym_symIndexRep])
    (by
      -- the composite agrees with `mkQ` on the tensor basis, and `mkQ` is surjective
      have key : (finsuppToSymPow b n ∘ₗ symPowToFinsupp b n) ∘ₗ
          (symRelSubmodule k V n).mkQ = (symRelSubmodule k V n).mkQ := by
        refine (tensorPowBasis b n).ext fun g => ?_
        have h : (symRelSubmodule k V n).mkQ (tensorPowBasis b n g)
            = symTprod k V n fun i => b (g i) := by
          rw [tensorPowBasis_apply, symTprod_apply]
        rw [LinearMap.comp_apply, LinearMap.comp_apply, h, symPowToFinsupp_symTprod,
          finsuppToSymPow_single, one_smul]
        exact symTprod_basis_eq_of_tupleSym_eq b n (by rw [tupleSym_symIndexRep])
      refine symPow_ext fun f => ?_
      exact congrArg (fun F => F (PiTensorProduct.tprod k f)) key)

/-- **Problem 2.11.3(d), symmetric case.** A basis `{vᵢ}` of `V` indexed by `I` induces a basis of
`S^n V` indexed by the multisets of size `n` of elements of `I`. -/
noncomputable def symPowBasis : Module.Basis (Sym I n) k (SymPow k V n) :=
  Module.Basis.ofRepr (symPowEquivFinsupp b n)

/-- The basis vector of `S^n V` at a multiset `s` is the class of *any* pure tensor of basis
vectors whose index tuple realises `s`. -/
lemma symPowBasis_apply (s : Sym I n) (g : Fin n → I) (hg : tupleSym g = s) :
    symPowBasis b n s = symTprod k V n fun i => b (g i) := by
  have h0 : symPowBasis b n s = (symPowEquivFinsupp b n).symm (Finsupp.single s 1) :=
    (Module.Basis.repr_symm_single_one (symPowBasis b n) s).symm
  rw [h0, symPowEquivFinsupp, LinearEquiv.ofLinear_symm_apply, finsuppToSymPow_single, one_smul]
  exact symTprod_basis_eq_of_tupleSym_eq b n (by simp [hg])

end Basis

/-! ### The dimension of `S^n V` -/

section Finrank

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]

/-- **Problem 2.11.3(d), symmetric case.** If `dim V = m` then `dim S^n V = (m + n - 1).choose n`,
the number of multisets of size `n` drawn from `m` basis vectors. -/
theorem finrank_symPow [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (SymPow k V n) = (Module.finrank k V + n - 1).choose n := by
  classical
  rw [Module.finrank_eq_card_basis (symPowBasis (Module.finBasis k V) n),
    Sym.card_sym_eq_choose, Fintype.card_fin]

/-- The dimension of `S^n V` in multichoose form: the number of size-`n` multisets drawn from
`dim V` basis vectors. -/
theorem finrank_symPow_eq_multichoose [FiniteDimensional k V] (n : ℕ) :
    Module.finrank k (SymPow k V n) = Nat.multichoose (Module.finrank k V) n := by
  rw [finrank_symPow, Nat.multichoose_eq]

end Finrank

end Etingof.Problem2_11_3

-- The leaf names follow Mathlib conventions; the underscore comes solely from the stable
-- book-number namespace Problem2_11_3, which is part of this project's public API.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_11_3.tupleSym Etingof.Problem2_11_3.symPowLift
  Etingof.Problem2_11_3.symPowLiftEquiv Etingof.Problem2_11_3.tensorPowBasis
  Etingof.Problem2_11_3.tensorPowToSymFinsupp Etingof.Problem2_11_3.symPowToFinsupp
  Etingof.Problem2_11_3.symIndexRep Etingof.Problem2_11_3.finsuppToSymPow
  Etingof.Problem2_11_3.symPowEquivFinsupp Etingof.Problem2_11_3.symPowBasis
