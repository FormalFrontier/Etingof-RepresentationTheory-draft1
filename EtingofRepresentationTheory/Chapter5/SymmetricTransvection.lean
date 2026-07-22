import Mathlib
import EtingofRepresentationTheory.Chapter5.SymmetricPowerBasis
import EtingofRepresentationTheory.Chapter5.Example5_19_3

/-!
# Transvection connectivity on the monomial basis of `SⁿV`

This file supplies the *transvection-connectivity* ingredient for the symmetric half of
Problem 4.12.3 (irreducibility of `SⁿV` as a `GL(V)`-representation, cited in Example 5.19.3).

The exterior half (`Etingof.exteriorPower_eq_bot_or_top`) used permutation matrices, which act
transitively on `n`-subsets. For the symmetric power the permutation matrices act *trivially* on
the monomial basis (permuting the index tuple leaves its monomial class unchanged), so one must use
the transvections `1 + Eᵢⱼ` (`i ≠ j`) to move between distinct monomials. This file:

* builds the transvection `transvection bV i j : V ≃ₗ[k] V` (with `1 + Eᵢⱼ` sending
  `eⱼ ↦ eⱼ + eᵢ`, everything else fixed), together with `transvectionMap` (the underlying linear
  map) and its action on basis vectors;
* computes the action of a transvection on a monomial basis vector of `SⁿV`
  (`symmetricPowerMap_transvection_eq_sum`): expanding `⨂ (eⱼ + eᵢ)` over the `j`-positions gives a
  sum, indexed by subsets `s` of the `j`-positions, of the monomials obtained by re-labelling the
  positions in `s` to `i`;
* extracts the coordinate at the *single-unit move* `e^α ↦ e^{α - eⱼ + eᵢ}`
  (`transvection_repr_ne_zero`): it is a nonzero natural number in characteristic zero (the number
  of `j`-positions that get moved), so a single move survives;
* packages the *combinatorial connectivity* of degree-`n` monomials under single-unit moves
  (`MonomialAdj`, `monomialAdj_connected`);
* combines these into `monomialAdj_step_mem`, the `hstep` hypothesis of
  `Etingof.DiagonalCoordinate.eq_bot_or_eq_top_of_connected`: given the diagonal element supplying
  distinct eigenvalues, a transvection realises each `Adj`-step inside any `GL(V)`-stable subspace.

Downstream, Example 5.19.3 assembles `monomialAdj_connected` + `monomialAdj_step_mem` with the
diagonal element into the full irreducibility `theorem`.
-/

open scoped TensorProduct BigOperators
open Module
open Etingof.SymmetricPowerBasis

namespace Etingof

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
variable {d n : ℕ}

section Transvection

/-- The underlying linear map of the transvection `1 + Eᵢⱼ`: `x ↦ x + ⟨eⱼ*, x⟩ eᵢ`. On the basis
it sends `eⱼ ↦ eⱼ + eᵢ` and fixes the other `eₗ`. -/
noncomputable def transvectionMap (bV : Basis (Fin d) k V) (i j : Fin d) : V →ₗ[k] V :=
  LinearMap.id + (bV.coord j).smulRight (bV i)

@[simp] lemma transvectionMap_apply_basis (bV : Basis (Fin d) k V) (i j l : Fin d) :
    transvectionMap bV i j (bV l) = bV l + (if l = j then bV i else 0) := by
  simp only [transvectionMap, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    Basis.coord_apply, Basis.repr_self]
  by_cases h : l = j <;> simp [h]

/-- `Eᵢⱼ ∘ Eᵢⱼ = 0` when `i ≠ j` (the transvection generator is nilpotent). -/
private lemma transElem_comp_self (bV : Basis (Fin d) k V) {i j : Fin d} (hij : i ≠ j) :
    ((bV.coord j).smulRight (bV i)).comp ((bV.coord j).smulRight (bV i)) = 0 := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.zero_apply, map_smul,
    Basis.coord_apply, Basis.repr_self, smul_smul]
  rw [Finsupp.single_apply, if_neg hij]
  simp

/-- The transvection `1 + Eᵢⱼ` as a linear automorphism of `V` (`i ≠ j`), with inverse `1 - Eᵢⱼ`. -/
noncomputable def transvection (bV : Basis (Fin d) k V) (i j : Fin d) (hij : i ≠ j) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (transvectionMap bV i j)
    (LinearMap.id - (bV.coord j).smulRight (bV i))
    (by
      simp only [transvectionMap, LinearMap.add_comp, LinearMap.comp_sub, LinearMap.id_comp,
        LinearMap.comp_id, transElem_comp_self bV hij]
      abel)
    (by
      simp only [transvectionMap, LinearMap.sub_comp, LinearMap.comp_add, LinearMap.id_comp,
        LinearMap.comp_id, transElem_comp_self bV hij]
      abel)

@[simp] lemma transvection_coe (bV : Basis (Fin d) k V) (i j : Fin d) (hij : i ≠ j) :
    (transvection bV i j hij : V →ₗ[k] V) = transvectionMap bV i j :=
  rfl

end Transvection

section Expansion

variable [Module.Finite k V]

omit [Module.Finite k V] in
/-- **Transvection action on a monomial.** Applying `1 + Eᵢⱼ` to the monomial `e^α = mk (⨂ eₚₘ)`
expands, via multilinearity, into a sum over subsets `s` of the positions where `p m = j`: the term
for `s` is the monomial obtained by re-labelling every position in `s` from `j` to `i`. -/
theorem symmetricPowerMap_transvection_eq_sum
    (bV : Basis (Fin d) k V) (i j : Fin d) (p : Fin n → Fin d) :
    symmetricPowerMap (transvectionMap bV i j)
        (symmetricPowerMonomialBasis bV (toMonomial p))
      = ∑ s ∈ (Finset.univ.filter (fun m => p m = j)).powerset,
          symmetricPowerMonomialBasis bV (toMonomial (fun m => if m ∈ s then i else p m)) := by
  classical
  -- Multilinear expansion of `⨂ (eₚₘ + [pₘ = j] eᵢ)` over all subsets.
  have expand : PiTensorProduct.tprod k (fun m => transvectionMap bV i j (bV (p m)))
      = ∑ s : Finset (Fin n), PiTensorProduct.tprod k
          (s.piecewise (fun m => if p m = j then bV i else 0) (fun m => bV (p m))) := by
    rw [← MultilinearMap.map_add_univ]
    congr 1
    funext m
    rw [transvectionMap_apply_basis, Pi.add_apply]
    exact add_comm _ _
  rw [symmetricPowerMonomialBasis_toMonomial, symmetricPowerMap_mk, tensorBasis,
    Basis.piTensorProduct_apply]
  simp only [PiTensorProduct.map_tprod]
  rw [expand, map_sum,
    ← Finset.sum_subset (Finset.subset_univ
        ((Finset.univ.filter (fun m => p m = j)).powerset))
        (fun s _ hs => by
          rw [Finset.mem_powerset] at hs
          obtain ⟨m, hms, hmJ⟩ := Finset.not_subset.mp hs
          have hpm : p m ≠ j := fun h => hmJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hz : (Finset.piecewise s (fun m => if p m = j then bV i else 0)
              (fun m => bV (p m))) m = 0 := by
            rw [Finset.piecewise_eq_of_mem (s := s) (f := fun m => if p m = j then bV i else 0)
              (g := fun m => bV (p m)) hms]
            simp [hpm]
          rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod k) m hz, map_zero])]
  -- terms for `s ⊆ {j-positions}` match the re-labelled monomial.
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [Finset.mem_powerset] at hs
  rw [symmetricPowerMonomialBasis_toMonomial, tensorBasis, Basis.piTensorProduct_apply]
  refine congrArg (SymmetricPower.mk k (Fin n) V)
    (congrArg (fun f => PiTensorProduct.tprod k f) (funext (fun m => ?_)))
  by_cases hm : m ∈ s
  · have hpj : p m = j := (Finset.mem_filter.mp (hs hm)).2
    rw [Finset.piecewise_eq_of_mem (s := s) (f := fun m => if p m = j then bV i else 0)
      (g := fun m => bV (p m)) hm]
    simp [hpj, hm]
  · rw [Finset.piecewise_eq_of_notMem (s := s) (f := fun m => if p m = j then bV i else 0)
      (g := fun m => bV (p m)) hm]
    simp [hm]

omit [Module.Finite k V] in
/-- **Single move survives.** The coordinate of `(1 + Eᵢⱼ) · e^α` at the monomial `e^β` obtained by
moving one unit from `j` to `i` (at a position `m₀` with `p m₀ = j`) is the number of `j`-positions
that could be moved — a positive natural number, hence nonzero in characteristic zero. -/
theorem transvection_repr_ne_zero [CharZero k]
    (bV : Basis (Fin d) k V) (i j : Fin d) (p : Fin n → Fin d) (m₀ : Fin n) (hm₀ : p m₀ = j) :
    (symmetricPowerMonomialBasis bV).repr
        (symmetricPowerMap (transvectionMap bV i j)
          (symmetricPowerMonomialBasis bV (toMonomial p)))
        (toMonomial (Function.update p m₀ i)) ≠ 0 := by
  classical
  rw [symmetricPowerMap_transvection_eq_sum, map_sum, Finsupp.finsetSum_apply]
  simp only [Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_boole, Ne, Nat.cast_eq_zero, Finset.card_eq_zero,
    ← Ne, ← Finset.nonempty_iff_ne_empty]
  -- The single-move witness `s = {m₀}`.
  refine ⟨{m₀}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩⟩
  · exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm₀⟩)
  · refine congrArg toMonomial (funext (fun m => ?_))
    simp only [Finset.mem_singleton, Function.update_apply]

end Expansion

section Connectivity

/-- **Single-unit moves between monomials.** `MonomialAdj M N` holds when `N` is obtained from `M`
by re-labelling one position of a representative tuple to a different value. This is exactly the
relation realised inside a `GL(V)`-stable subspace by a transvection. -/
def MonomialAdj : Monomial n (Fin d) → Monomial n (Fin d) → Prop :=
  fun M N => ∃ (p : Fin n → Fin d) (m₀ : Fin n) (c : Fin d),
    toMonomial p = M ∧ toMonomial (Function.update p m₀ c) = N ∧ p m₀ ≠ c

/-- **Connectivity.** Any two degree-`n` monomials are connected by a chain of single-unit moves:
transform one representative tuple into the other, changing one position at a time. -/
theorem monomialAdj_connected (M N : Monomial n (Fin d)) :
    Relation.ReflTransGen (MonomialAdj (n := n) (d := d)) M N := by
  classical
  refine Quotient.inductionOn₂ M N (fun p q => ?_)
  -- Induct on the set of positions where `p` and `q` still disagree.
  suffices H : ∀ (D : Finset (Fin n)) (p : Fin n → Fin d),
      (∀ m, p m ≠ q m → m ∈ D) →
      Relation.ReflTransGen (MonomialAdj (n := n) (d := d)) (toMonomial p) (toMonomial q) by
    exact H (Finset.univ.filter (fun m => p m ≠ q m)) p (by intro m h; simp [h])
  intro D
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    intro p hp
    by_cases hpq : ∀ m, p m = q m
    · rw [congrArg toMonomial (funext hpq)]
    · simp only [not_forall] at hpq
      obtain ⟨m₀, hm₀⟩ := hpq
      have hm₀D : m₀ ∈ D := hp m₀ hm₀
      have step : MonomialAdj (n := n) (d := d) (toMonomial p)
          (toMonomial (Function.update p m₀ (q m₀))) := ⟨p, m₀, q m₀, rfl, rfl, hm₀⟩
      have hsub : D.erase m₀ ⊂ D := Finset.erase_ssubset hm₀D
      have hp' : ∀ m, (Function.update p m₀ (q m₀)) m ≠ q m → m ∈ D.erase m₀ := by
        intro m hm
        have hmm0 : m ≠ m₀ := by
          rintro rfl; exact hm (by rw [Function.update_self])
        refine Finset.mem_erase.mpr ⟨hmm0, hp m ?_⟩
        rwa [Function.update_of_ne hmm0] at hm
      exact Relation.ReflTransGen.head step (ih _ hsub _ hp')

end Connectivity

section Step

variable [CharZero k] [Module.Finite k V]

omit [Module.Finite k V] in
/-- **A transvection realises one `Adj`-step inside a stable subspace.** Given the diagonal
element `T` acting on the monomial basis with distinct eigenvalues (`hT`, `hw`) and a subspace `W`
stable under `T` (`hWT`) and under every `symmetricPowerMap g` (`hWG`): if the monomial `M` lies in
`W` and `MonomialAdj M N`, then `N` lies in `W`. This is the `hstep` hypothesis of
`DiagonalCoordinate.eq_bot_or_eq_top_of_connected`. -/
theorem monomialAdj_step_mem
    (bV : Basis (Fin d) k V)
    {T : Module.End k (SymmetricPower k (Fin n) V)} {w : Monomial n (Fin d) → k}
    (hT : ∀ M, T (symmetricPowerMonomialBasis bV M) = w M • symmetricPowerMonomialBasis bV M)
    (hw : Function.Injective w)
    {W : Submodule k (SymmetricPower k (Fin n) V)}
    (hWT : ∀ x ∈ W, T x ∈ W)
    (hWG : ∀ g : V ≃ₗ[k] V, ∀ x ∈ W,
      symmetricPowerMap (g : V →ₗ[k] V) x ∈ W)
    (M N : Monomial n (Fin d))
    (hMW : symmetricPowerMonomialBasis bV M ∈ W)
    (hMN : MonomialAdj M N) :
    symmetricPowerMonomialBasis bV N ∈ W := by
  obtain ⟨p, m₀, c, rfl, rfl, hpc⟩ := hMN
  -- The transvection `1 + E_{c, p m₀}` moves the unit at `m₀` from `p m₀` to `c`.
  have hy : symmetricPowerMap (transvection bV c (p m₀) (fun h => hpc h.symm) : V →ₗ[k] V)
      (symmetricPowerMonomialBasis bV (toMonomial p)) ∈ W :=
    hWG _ _ hMW
  rw [transvection_coe] at hy
  exact DiagonalCoordinate.mem_of_repr_ne_zero (symmetricPowerMonomialBasis bV) hT hw hWT hy
    (transvection_repr_ne_zero bV c (p m₀) p m₀ rfl)

end Step

end Etingof
