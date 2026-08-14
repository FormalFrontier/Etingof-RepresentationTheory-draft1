/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Defs

namespace RepresentationTheory.RingTheory.Ideal.IdempotentLifting

/-- A complete orthogonal family of idempotents in the quotient by a nilpotent two-sided ideal
lifts to a complete orthogonal family in the ring. -/
theorem exists_completeOrthogonalIdempotents_lift_of_isNilpotent {A : Type*} [Ring A]
    {I : Ideal A} [I.IsTwoSided] (hI : IsNilpotent I)
    {ι : Type*} [Fintype ι] {ebar : ι → A ⧸ I}
    (h_coi : CompleteOrthogonalIdempotents ebar) :
    ∃ e : ι → A, CompleteOrthogonalIdempotents e ∧
      ∀ i, Ideal.Quotient.mk I (e i) = ebar i := by
  obtain ⟨n, hn⟩ := hI
  have hker : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk I), IsNilpotent x := by
    intro x hx
    rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact ⟨n, by
      have := Ideal.pow_mem_pow hx n
      rw [hn] at this
      exact Ideal.mem_bot.mp this⟩
  obtain ⟨e, he_coi, he_lift⟩ :=
    CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
      (Ideal.Quotient.mk I) hker h_coi (fun i => Ideal.Quotient.mk_surjective (ebar i))
  exact ⟨e, he_coi, fun i => congr_fun he_lift i⟩

end RepresentationTheory.RingTheory.Ideal.IdempotentLifting
