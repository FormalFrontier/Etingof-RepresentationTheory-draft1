import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_9
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import Mathlib

/-!
# Existence of a decomposition into indecomposables

Every finite-dimensional quiver representation over a field is isomorphic to a finite
(iterated) direct sum of **indecomposable** representations. This is the *existence*
half of Krull–Schmidt; uniqueness is deliberately **not** proved here (it is not needed
for the orbit-counting route to Gabriel's theorem, directive #4777 step 1).

The proof is strong induction on the total dimension `∑ v, finrank (V.obj v)`: if `V`
is indecomposable we are done, otherwise the failure of indecomposability hands us a
pair of complementary invariant sub-representations, each of strictly smaller total
dimension, and we recurse.

## Main results

* `Etingof.QuiverRepresentation.directSumList` — iterated direct sum of a list.
* `Etingof.QuiverRepresentation.AreIsomorphic.refl/.trans` and friends — the iso relation
  is a (partial) equivalence with the expected congruences.
* `Etingof.QuiverRepresentation.exists_decomposition` — the existence theorem.
-/

namespace Etingof.QuiverRepresentation

open Etingof

section Iso

variable {k : Type*} [Field k] {n : ℕ} [Q : Quiver (Fin n)]

/-- Pointwise form of the intertwining condition of `AreIsomorphic`. -/
theorem AreIsomorphic.intertwine {V W : QuiverRepresentation k (Fin n)}
    {e : ∀ v, V.obj v ≃ₗ[k] W.obj v}
    (he : ∀ {a b : Fin n} (f : a ⟶ b),
      (e b).toLinearMap ∘ₗ V.mapLinear f = W.mapLinear f ∘ₗ (e a).toLinearMap)
    {a b : Fin n} (f : a ⟶ b) (x : V.obj a) :
    e b (V.mapLinear f x) = W.mapLinear f (e a x) := by
  have := LinearMap.congr_fun (he f) x
  simpa using this

@[refl]
theorem AreIsomorphic.refl (V : QuiverRepresentation k (Fin n)) : V.AreIsomorphic V :=
  ⟨fun v => LinearEquiv.refl k (V.obj v), by
    intro a b f
    ext x
    simp⟩

theorem AreIsomorphic.trans {U V W : QuiverRepresentation k (Fin n)}
    (h₁ : U.AreIsomorphic V) (h₂ : V.AreIsomorphic W) : U.AreIsomorphic W := by
  obtain ⟨e, he⟩ := h₁
  obtain ⟨e', he'⟩ := h₂
  refine ⟨fun v => (e v).trans (e' v), ?_⟩
  intro a b f
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [AreIsomorphic.intertwine he f x, AreIsomorphic.intertwine he' f (e a x)]

theorem AreIsomorphic.symm {V W : QuiverRepresentation k (Fin n)}
    (h : V.AreIsomorphic W) : W.AreIsomorphic V := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun v => (e v).symm, ?_⟩
  intro a b f
  ext y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq, AreIsomorphic.intertwine he f ((e a).symm y),
    LinearEquiv.apply_symm_apply]

/-- Direct sum is a congruence for isomorphism. -/
theorem AreIsomorphic.directSum {V₁ V₂ W₁ W₂ : QuiverRepresentation k (Fin n)}
    (h₁ : V₁.AreIsomorphic W₁) (h₂ : V₂.AreIsomorphic W₂) :
    (directSum k (Fin n) V₁ V₂).AreIsomorphic (directSum k (Fin n) W₁ W₂) := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  refine ⟨fun v => (e₁ v).prodCongr (e₂ v), ?_⟩
  intro a b f
  ext x
  simp only [QuiverRepresentation.directSum, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply, LinearMap.prodMap_apply]
  rw [AreIsomorphic.intertwine he₁ f x.1, AreIsomorphic.intertwine he₂ f x.2]

end Iso

section ZeroAndList

variable {k : Type*} [Field k] {n : ℕ} [Q : Quiver (Fin n)]

/-- The zero representation: the trivial module at every vertex, the zero map on arrows.
The space is fixed to `PUnit : Type 0` so that `directSumList` (whose direct-sum step takes
the `max` of the two obj universes) introduces no spurious free universe. -/
def zeroRep : QuiverRepresentation k (Fin n) where
  obj := fun _ => PUnit.{1}
  mapLinear := fun _ => 0

/-- A representation with a trivial space at every vertex is isomorphic to `zeroRep`. -/
theorem areIsomorphic_zeroRep (V : QuiverRepresentation k (Fin n))
    (h : ∀ v, Subsingleton (V.obj v)) : V.AreIsomorphic zeroRep := by
  refine ⟨fun v => ?_, ?_⟩
  · haveI := h v
    exact ({ toFun := 0
             invFun := 0
             map_add' := fun x y => Subsingleton.elim _ _
             map_smul' := fun c x => Subsingleton.elim _ _
             left_inv := fun x => Subsingleton.elim _ _
             right_inv := fun x => Subsingleton.elim _ _ } : V.obj v ≃ₗ[k] PUnit.{1})
  · intro a b f
    haveI : Subsingleton ((zeroRep : QuiverRepresentation k (Fin n)).obj b) :=
      (inferInstance : Subsingleton PUnit)
    ext x
    exact Subsingleton.elim _ _

/-- The iterated direct sum of a list of representations (right-folded, base `zeroRep`). -/
noncomputable def directSumList (L : List (QuiverRepresentation k (Fin n))) :
    QuiverRepresentation k (Fin n) :=
  L.foldr (directSum k (Fin n)) zeroRep

@[simp] theorem directSumList_nil :
    directSumList ([] : List (QuiverRepresentation k (Fin n))) = zeroRep := rfl

@[simp] theorem directSumList_cons (a : QuiverRepresentation k (Fin n))
    (L : List (QuiverRepresentation k (Fin n))) :
    directSumList (a :: L) = directSum k (Fin n) a (directSumList L) := rfl

/-- `V ⊕ 0 ≅ V`: right unit for the direct sum. -/
theorem areIsomorphic_directSum_zeroRep (V : QuiverRepresentation k (Fin n)) :
    V.AreIsomorphic (directSum k (Fin n) V zeroRep) := by
  refine ⟨fun v => (LinearEquiv.prodUnique (R := k) (M := V.obj v) (M₂ := PUnit)).symm, ?_⟩
  intro a b f
  ext x
  simp [QuiverRepresentation.directSum, zeroRep, LinearMap.prodMap_apply]

/-- `0 ⊕ V ≅ V`: left unit for the direct sum. -/
theorem areIsomorphic_zeroRep_directSum (V : QuiverRepresentation k (Fin n)) :
    (directSum k (Fin n) zeroRep V).AreIsomorphic V := by
  refine ⟨fun v => LinearEquiv.uniqueProd (R := k) (M := V.obj v) (M₂ := PUnit), ?_⟩
  intro a b f
  ext x
  simp [QuiverRepresentation.directSum, zeroRep, LinearMap.prodMap_apply]

/-- Associativity of the direct sum, up to isomorphism. -/
theorem areIsomorphic_directSum_assoc (A B C : QuiverRepresentation k (Fin n)) :
    (directSum k (Fin n) (directSum k (Fin n) A B) C).AreIsomorphic
      (directSum k (Fin n) A (directSum k (Fin n) B C)) := by
  refine ⟨fun v => LinearEquiv.prodAssoc k (A.obj v) (B.obj v) (C.obj v), ?_⟩
  intro a b f
  ext x
  simp [QuiverRepresentation.directSum, LinearMap.prodMap_apply, LinearEquiv.prodAssoc_apply]

/-- The direct sum of two list direct sums is the list direct sum of the concatenation. -/
theorem areIsomorphic_directSumList_append
    (LA LB : List (QuiverRepresentation k (Fin n))) :
    (directSum k (Fin n) (directSumList LA) (directSumList LB)).AreIsomorphic
      (directSumList (LA ++ LB)) := by
  induction LA with
  | nil =>
      simp only [List.nil_append, directSumList_nil]
      refine ⟨fun v => ?_, ?_⟩
      · exact LinearEquiv.uniqueProd (R := k) (M := (directSumList LB).obj v) (M₂ := PUnit)
      · intro a b f
        ext x
        simp [QuiverRepresentation.directSum, zeroRep, LinearMap.prodMap_apply]
  | cons a L IH =>
      simp only [List.cons_append, directSumList_cons]
      refine (areIsomorphic_directSum_assoc a (directSumList L) (directSumList LB)).trans ?_
      exact (AreIsomorphic.refl a).directSum IH

end ZeroAndList

section SubRep

variable {k : Type*} [Field k] {n : ℕ} [Q : Quiver (Fin n)]

/-- The sub-representation carried by an arrow-invariant family of submodules. -/
def subRep (V : QuiverRepresentation k (Fin n)) (W : ∀ v, Submodule k (V.obj v))
    (hW : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W a, V.mapLinear e x ∈ W b) :
    QuiverRepresentation k (Fin n) where
  obj := fun v => W v
  mapLinear := fun {_a _b} e => (V.mapLinear e).restrict (hW e)

@[simp] theorem subRep_obj (V : QuiverRepresentation k (Fin n)) (W) (hW) (v : Fin n) :
    (subRep V W hW).obj v = W v := rfl

/-- A representation splits as the direct sum of two complementary invariant
sub-representations. -/
theorem areIsomorphic_subRep_directSum (V : QuiverRepresentation k (Fin n))
    (W₁ W₂ : ∀ v, Submodule k (V.obj v))
    (hW₁ : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W₁ a, V.mapLinear e x ∈ W₁ b)
    (hW₂ : ∀ {a b : Fin n} (e : a ⟶ b), ∀ x ∈ W₂ a, V.mapLinear e x ∈ W₂ b)
    (hc : ∀ v, IsCompl (W₁ v) (W₂ v)) :
    V.AreIsomorphic (directSum k (Fin n) (subRep V W₁ hW₁) (subRep V W₂ hW₂)) := by
  letI : ∀ v, AddCommGroup (V.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
  refine ⟨fun v => (Submodule.prodEquivOfIsCompl (W₁ v) (W₂ v) (hc v)).symm, ?_⟩
  intro a b f
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_eq]
  simp only [QuiverRepresentation.directSum, LinearMap.prodMap_apply,
    Submodule.coe_prodEquivOfIsCompl', subRep, LinearMap.restrict_coe_apply]
  rw [← map_add]
  congr 1
  change x = (Submodule.prodEquivOfIsCompl (W₁ a) (W₂ a) (hc a))
      ((Submodule.prodEquivOfIsCompl (W₁ a) (W₂ a) (hc a)).symm x)
  rw [LinearEquiv.apply_symm_apply]

end SubRep

section Existence

universe uk uh

/-- **Existence of a decomposition into indecomposables.**
Every finite-dimensional quiver representation over a field is isomorphic to an iterated
direct sum of indecomposable representations. (Uniqueness is not asserted.)

The vertex spaces live in `Type 0` (`obj`-universe `0`), which is the setting the
orbit-counting application uses (`V.obj v ≃ Fin (d v) → k`). The `directSumList`
construction has base `zeroRep` at `Type 0`, so all summands stay at `Type 0` too. -/
theorem exists_decomposition {k : Type uk} [Field k] {n : ℕ} [Quiver.{uh} (Fin n)]
    (V : QuiverRepresentation.{uk, 0, 0, uh} k (Fin n))
    [∀ v, Module.Finite k (V.obj v)] :
    ∃ L : List (QuiverRepresentation.{uk, 0, 0, uh} k (Fin n)),
      (∀ W ∈ L, W.IsIndecomposable) ∧ V.AreIsomorphic (directSumList L) := by
  -- Strong induction on the total dimension.
  suffices H : ∀ N, ∀ (V : QuiverRepresentation.{uk, 0, 0, uh} k (Fin n))
      [∀ v, Module.Finite k (V.obj v)],
      (∑ v, Module.finrank k (V.obj v)) = N →
      ∃ L : List (QuiverRepresentation.{uk, 0, 0, uh} k (Fin n)),
        (∀ W ∈ L, W.IsIndecomposable) ∧ V.AreIsomorphic (directSumList L) by
    exact H _ V rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro V _ hVN
    by_cases hInd : V.IsIndecomposable
    · -- Indecomposable: take the singleton list.
      exact ⟨[V], by simpa using hInd, by
        simpa using areIsomorphic_directSum_zeroRep V⟩
    · -- Not indecomposable: either zero, or splits into complementary subreps.
      rw [QuiverRepresentation.IsIndecomposable, not_and_or] at hInd
      rcases hInd with hzero | hsplit
      · -- Zero representation: empty list.
        push_neg at hzero
        exact ⟨[], by simp, areIsomorphic_zeroRep V hzero⟩
      · -- Genuine splitting.
        letI : ∀ v, AddCommGroup (V.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
        push_neg at hsplit
        obtain ⟨W₁, W₂, hW₁, hW₂, hc, hne₁, hne₂⟩ := hsplit
        -- The two complementary subreps, both finite-dimensional.
        haveI hfd₁ : ∀ v, Module.Finite k ((subRep V W₁ hW₁).obj v) :=
          fun v => inferInstanceAs (Module.Finite k (W₁ v))
        haveI hfd₂ : ∀ v, Module.Finite k ((subRep V W₂ hW₂).obj v) :=
          fun v => inferInstanceAs (Module.Finite k (W₂ v))
        -- Dimensions: finrank V_v = finrank W₁_v + finrank W₂_v at each vertex.
        have hdim : ∀ v, Module.finrank k (W₁ v) + Module.finrank k (W₂ v)
            = Module.finrank k (V.obj v) := fun v =>
          Submodule.finrank_add_eq_of_isCompl (hc v)
        have hsum : (∑ v, Module.finrank k ((subRep V W₁ hW₁).obj v))
            + (∑ v, Module.finrank k ((subRep V W₂ hW₂).obj v))
            = ∑ v, Module.finrank k (V.obj v) := by
          simp only [subRep_obj]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun v _ => hdim v)
        -- Each piece is nonzero somewhere, giving strict decrease.
        obtain ⟨v₁, hv₁⟩ := hne₁
        obtain ⟨v₂, hv₂⟩ := hne₂
        have hpos₂ : 0 < ∑ v, Module.finrank k ((subRep V W₂ hW₂).obj v) := by
          refine Finset.sum_pos' (fun v _ => Nat.zero_le _) ⟨v₂, Finset.mem_univ _, ?_⟩
          change 0 < Module.finrank k (W₂ v₂)
          exact Nat.pos_of_ne_zero (fun h => hv₂ (Submodule.finrank_eq_zero.mp h))
        have hpos₁ : 0 < ∑ v, Module.finrank k ((subRep V W₁ hW₁).obj v) := by
          refine Finset.sum_pos' (fun v _ => Nat.zero_le _) ⟨v₁, Finset.mem_univ _, ?_⟩
          change 0 < Module.finrank k (W₁ v₁)
          exact Nat.pos_of_ne_zero (fun h => hv₁ (Submodule.finrank_eq_zero.mp h))
        have hlt₁ : (∑ v, Module.finrank k ((subRep V W₁ hW₁).obj v)) < N := by
          rw [← hVN, ← hsum]; omega
        have hlt₂ : (∑ v, Module.finrank k ((subRep V W₂ hW₂).obj v)) < N := by
          rw [← hVN, ← hsum]; omega
        -- Recurse.
        obtain ⟨L₁, hL₁ind, hL₁iso⟩ := IH _ hlt₁ (subRep V W₁ hW₁) rfl
        obtain ⟨L₂, hL₂ind, hL₂iso⟩ := IH _ hlt₂ (subRep V W₂ hW₂) rfl
        refine ⟨L₁ ++ L₂, ?_, ?_⟩
        · intro W hW
          rcases List.mem_append.mp hW with h | h
          · exact hL₁ind W h
          · exact hL₂ind W h
        · refine (areIsomorphic_subRep_directSum V W₁ W₂ hW₁ hW₂ hc).trans ?_
          exact (hL₁iso.directSum hL₂iso).trans
            (areIsomorphic_directSumList_append L₁ L₂)

end Existence

end Etingof.QuiverRepresentation
