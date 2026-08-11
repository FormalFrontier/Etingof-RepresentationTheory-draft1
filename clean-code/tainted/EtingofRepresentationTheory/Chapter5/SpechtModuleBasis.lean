import EtingofRepresentationTheory.Chapter5.TabloidModule
import EtingofRepresentationTheory.Chapter5.Theorem5_17_1

/-!
# The standard-polytabloid basis of a Specht module

The tabloid realization already proves that the standard polytabloids are linearly
independent and that the tabloid projection is injective on the Specht module.  The
hook-length theorem supplies the missing dimension equality.  Together these give an
axiom-free standard-polytabloid basis without reviving the deleted Garnir recursion.

This basis is the coordinate system used by the Young-rule straightening argument.
-/

namespace Etingof

noncomputable section

variable {n : ℕ} {la : Nat.Partition n}

/-- The Specht vector whose tabloid projection is the standard polytabloid `e_T`.

The normalizing factor removes the cardinality of the row subgroup appearing in
`tabloidProjection_of_mul_youngSymmetrizer`. -/
noncomputable def spechtPolytabloid (T : StandardYoungTableau n la) :
    SpechtModule n la :=
  ⟨(Nat.card (↥(RowSubgroup n la)) : ℂ)⁻¹ •
      MonoidAlgebra.of ℂ _ (sytPerm n la T)⁻¹ * YoungSymmetrizer n la, by
    rw [SpechtModule, Submodule.mem_span_singleton]
    exact ⟨(Nat.card (↥(RowSubgroup n la)) : ℂ)⁻¹ •
      MonoidAlgebra.of ℂ _ (sytPerm n la T)⁻¹, rfl⟩⟩

/-- The tabloid projection of `spechtPolytabloid T` is the usual standard
polytabloid indexed by `T`. -/
theorem tabloidProjection_spechtPolytabloid (T : StandardYoungTableau n la) :
    tabloidProjection (n := n) (la := la) (spechtPolytabloid T : SymGroupAlgebra n) =
      polytabloidTab T := by
  simp only [spechtPolytabloid, map_smul, smul_mul_assoc,
    tabloidProjection_of_mul_youngSymmetrizer]
  rw [smul_smul, inv_mul_cancel₀, one_smul, inv_inv]
  · exact generalizedPolytabloidTab_eq_polytabloidTab T
  · exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RowSubgroup n la))).ne'

/-- Standard polytabloids are linearly independent in the Specht module. -/
theorem spechtPolytabloid_linearIndependent :
    LinearIndependent ℂ (spechtPolytabloid :
      StandardYoungTableau n la → SpechtModule n la) := by
  let ψ : SpechtModule n la →ₗ[ℂ] TabloidRepresentation n la :=
    (tabloidProjection (n := n) (la := la)).comp
      ((SpechtModule n la).restrictScalars ℂ).subtype
  have hψ : ψ ∘ (spechtPolytabloid :
      StandardYoungTableau n la → SpechtModule n la) =
      (polytabloidTab : StandardYoungTableau n la → TabloidRepresentation n la) := by
    funext T
    change tabloidProjection (spechtPolytabloid T : SymGroupAlgebra n) = polytabloidTab T
    exact tabloidProjection_spechtPolytabloid T
  apply LinearIndependent.of_comp ψ
  rw [hψ]
  exact polytabloidTab_linearIndependent

/-- The standard polytabloids span the Specht module. -/
theorem span_spechtPolytabloid :
    Submodule.span ℂ (Set.range (spechtPolytabloid :
      StandardYoungTableau n la → SpechtModule n la)) = ⊤ := by
  apply spechtPolytabloid_linearIndependent.span_eq_top_of_card_eq_finrank'
  simpa only [Nat.card_eq_fintype_card] using
    (finrank_spechtModule_eq_card_standardYoungTableau n la).symm

/-- The standard-polytabloid basis of the Specht module. -/
noncomputable def spechtPolytabloidBasis :
    Module.Basis (StandardYoungTableau n la) ℂ (SpechtModule n la) :=
  Module.Basis.mk spechtPolytabloid_linearIndependent span_spechtPolytabloid.ge

@[simp] theorem spechtPolytabloidBasis_apply (T : StandardYoungTableau n la) :
    spechtPolytabloidBasis T = spechtPolytabloid T := by
  rw [spechtPolytabloidBasis, Module.Basis.mk_apply]

/-- The tabloid projection restricted to the Specht module. -/
noncomputable def tabloidProjectionSpecht :
    SpechtModule n la →ₗ[ℂ] TabloidRepresentation n la :=
  (tabloidProjection (n := n) (la := la)).comp
    ((SpechtModule n la).restrictScalars ℂ).subtype

@[simp] theorem tabloidProjectionSpecht_spechtPolytabloid
    (T : StandardYoungTableau n la) :
    tabloidProjectionSpecht (spechtPolytabloid T) = polytabloidTab T :=
  tabloidProjection_spechtPolytabloid T

/-- The image of the Specht module in the tabloid representation is exactly the span
of standard polytabloids.  This is the straightening endpoint needed downstream; its
proof uses the standard-polytabloid basis rather than a recursive Garnir termination
argument. -/
theorem range_tabloidProjectionSpecht_eq_span_polytabloidTab :
    LinearMap.range (tabloidProjectionSpecht (n := n) (la := la)) =
      Submodule.span ℂ (Set.range (polytabloidTab :
        StandardYoungTableau n la → TabloidRepresentation n la)) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let b := spechtPolytabloidBasis (n := n) (la := la)
    have hrepr := b.sum_repr v
    rw [← hrepr, map_sum]
    apply Submodule.sum_mem
    intro T hT
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨T, ?_⟩
    simp only [b, spechtPolytabloidBasis_apply,
      tabloidProjectionSpecht_spechtPolytabloid]
  · apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact ⟨spechtPolytabloid T, tabloidProjectionSpecht_spechtPolytabloid T⟩

/-- Every generalized polytabloid is in the image of the Specht module under the
tabloid projection. -/
theorem generalizedPolytabloidTab_mem_range_tabloidProjectionSpecht
    (σ : Equiv.Perm (Fin n)) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      LinearMap.range (tabloidProjectionSpecht (n := n) (la := la)) := by
  let c : ℂ := Nat.card ↥(RowSubgroup n la)
  have hc : c ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := ↥(RowSubgroup n la))).ne'
  let v : SpechtModule n la :=
    ⟨c⁻¹ • MonoidAlgebra.of ℂ _ σ⁻¹ * YoungSymmetrizer n la, by
      rw [SpechtModule, Submodule.mem_span_singleton]
      exact ⟨c⁻¹ • MonoidAlgebra.of ℂ _ σ⁻¹, rfl⟩⟩
  refine ⟨v, ?_⟩
  change tabloidProjection
      (c⁻¹ • MonoidAlgebra.of ℂ _ σ⁻¹ * YoungSymmetrizer n la) =
    generalizedPolytabloidTab σ
  simp only [map_smul, smul_mul_assoc,
    tabloidProjection_of_mul_youngSymmetrizer]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, inv_inv]

/-- **Generalized-polytabloid straightening.** Every generalized polytabloid is a
linear combination of standard polytabloids. -/
theorem generalizedPolytabloidTab_mem_span_polytabloidTab
    (σ : Equiv.Perm (Fin n)) :
    generalizedPolytabloidTab (n := n) (la := la) σ ∈
      Submodule.span ℂ (Set.range (polytabloidTab :
        StandardYoungTableau n la → TabloidRepresentation n la)) := by
  rw [← range_tabloidProjectionSpecht_eq_span_polytabloidTab]
  exact generalizedPolytabloidTab_mem_range_tabloidProjectionSpecht σ

end

end Etingof
