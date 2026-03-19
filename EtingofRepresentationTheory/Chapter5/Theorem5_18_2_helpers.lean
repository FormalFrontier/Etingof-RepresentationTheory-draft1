import Mathlib
import EtingofRepresentationTheory.Chapter5.Lemma5_18_3

/-!
# Helper lemmas for Theorem 5.18.2: centralizer ⊆ fullDiagonalSubalgebra
-/

open scoped TensorProduct

namespace Etingof.Theorem5_18_2_Helpers

variable {k : Type*} [Field k]
  {V : Type*} [AddCommGroup V] [Module k V]
  {n : ℕ}

/-- Conjugation by reindex(σ) sends map(f) to map(f ∘ σ⁻¹). -/
lemma map_conj_reindex (f : Fin n → Module.End k V)
    (σ : Equiv.Perm (Fin n)) :
    (PiTensorProduct.reindex k (fun _ => V) σ).toLinearMap *
      PiTensorProduct.map f *
      (PiTensorProduct.reindex k (fun _ => V) σ).symm.toLinearMap =
    PiTensorProduct.map (fun i => f (σ.symm i)) := by
  set e := PiTensorProduct.reindex k (fun _ : Fin n => V) σ
  set eL := e.toLinearMap
  set eSL := e.symm.toLinearMap
  have h := PiTensorProduct.map_comp_reindex_eq f σ
  have hee : eL * eSL = 1 := by ext v; simp [eL, eSL, Module.End.mul_eq_comp]
  calc eL * PiTensorProduct.map f * eSL
      = PiTensorProduct.map (fun i => f (σ.symm i)) * eL * eSL := by
        congr 1; exact h.symm
    _ = PiTensorProduct.map (fun i => f (σ.symm i)) * (eL * eSL) := by
        rw [mul_assoc]
    _ = PiTensorProduct.map (fun i => f (σ.symm i)) * 1 := by rw [hee]
    _ = PiTensorProduct.map (fun i => f (σ.symm i)) := mul_one _

section Spanning

variable [Module.Free k V] [Module.Finite k V]

/-- map applied to End-basis elements produces the End-basis of V^⊗n. -/
lemma map_endBasis_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bV : Module.Basis ι k V)
    (q r : Fin n → ι) :
    PiTensorProduct.map (fun l => bV.«end» (q l, r l)) =
    (Basis.piTensorProduct (fun _ : Fin n => bV)).«end» (q, r) := by
  set bTP := Basis.piTensorProduct (fun _ : Fin n => bV)
  apply bTP.ext
  intro s
  -- RHS: bTP.end (q,r) applied to bTP s
  rw [Module.Basis.end_apply_apply]
  -- RHS is now: if r = s then bTP q else 0
  -- LHS: PiTensorProduct.map (...) (bTP s)
  rw [show bTP s = PiTensorProduct.tprod k (fun l => bV (s l))
      from Basis.piTensorProduct_apply _ _]
  rw [PiTensorProduct.map_tprod]
  -- LHS is now: tprod k (fun l => bV.end (q l, r l) (bV (s l)))
  -- Simplify each component
  simp_rw [Module.Basis.end_apply_apply]
  -- LHS: tprod k (fun l => if r l = s l then bV (q l) else 0)
  -- RHS: if r = s then bTP q else 0
  by_cases hrs : r = s
  · subst hrs
    simp only [ite_true]
    exact (Basis.piTensorProduct_apply (fun _ : Fin n => bV) q).symm
  · rw [if_neg hrs]
    -- Need: tprod k (fun l => if r l = s l then bV (q l) else 0) = 0
    obtain ⟨l, hl⟩ := Function.ne_iff.mp hrs
    exact (PiTensorProduct.tprod k).map_coord_zero l (if_neg hl)

/-- The image of PiTensorProduct.map spans all of End(V^⊗n). -/
lemma map_span_eq_top :
    Submodule.span k (Set.range (fun f : Fin n → Module.End k V =>
      PiTensorProduct.map f)) = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  set bV := Module.Free.chooseBasis k V
  set ι := Module.Free.ChooseBasisIndex k V
  set bTP := Basis.piTensorProduct (fun _ : Fin n => bV)
  set bEnd := bTP.«end»
  rw [show φ = ∑ qr : (Fin n → ι) × (Fin n → ι),
      bEnd.repr φ qr • bEnd qr from (bEnd.sum_repr φ).symm]
  apply Submodule.sum_mem
  intro ⟨q, r⟩ _
  apply Submodule.smul_mem
  rw [show bEnd (q, r) = PiTensorProduct.map (fun l => bV.«end» (q l, r l))
      from (map_endBasis_eq bV q r).symm]
  exact Submodule.subset_span ⟨_, rfl⟩

end Spanning

end Etingof.Theorem5_18_2_Helpers
