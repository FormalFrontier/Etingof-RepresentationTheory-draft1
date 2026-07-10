import Mathlib

/-!
# Problem 4.5.2: the primitive central idempotents of `ℂ[G]`

**Problem 4.5.2.** Let `G` be a finite group. Let `Vᵢ` be the irreducible complex
representations of `G`. For every `i`, let
`ψᵢ = (dim Vᵢ / |G|) · ∑_{g ∈ G} χ_{Vᵢ}(g) · g⁻¹ ∈ ℂ[G]`.

(i) Prove that `ψᵢ` acts on `Vⱼ` as the identity if `j = i`, and as the null map if
`j ≠ i`.

(ii) Prove that the `ψᵢ` are **idempotents**: `ψᵢ² = ψᵢ` for every `i`, and `ψᵢ ψⱼ = 0`
for `i ≠ j`.

*Hint.* In (i), `ψᵢ` commutes with every element of `ℂ[G]` and thus acts on `Vⱼ` as an
intertwining operator; Schur's lemma (Corollary 2.3.10) forces it to act as a scalar,
which is computed by taking the trace in `Vⱼ`.

## Formalization

We formalize the family indexed by the actual irreducible representations: an element
`ψ V ∈ ℂ[G]` is attached to each finite-dimensional complex representation `V`, and the
statements quantify over simple `V, W : FDRep ℂ G`. Non-isomorphism `Vⱼ ≇ Vᵢ` is
expressed as `IsEmpty (W ≅ V)`.

The action of `ψ V` on a representation `W` is via the group-algebra action
`Representation.asAlgebraHom W.ρ : ℂ[G] →ₐ[ℂ] End ℂ W`.

The scalar step of the hint is realised via the categorical Schur's lemma: the space of
`G`-equivariant endomorphisms of a simple object is one dimensional
(`CategoryTheory.finrank_endomorphism_simple_eq_one`), so any equivariant endomorphism is a
scalar multiple of the identity, and the scalar is read off from the trace.
-/

open CategoryTheory MonoidAlgebra Module

namespace Etingof

variable {G : Type*} [Group G] [Fintype G]

/-- The element `ψ_V = (dim V / |G|) · ∑_{g ∈ G} χ_V(g) · g⁻¹ ∈ ℂ[G]` associated to a
finite-dimensional complex representation `V`, as in Problem 4.5.2. -/
noncomputable def psi (V : FDRep ℂ G) : MonoidAlgebra ℂ G :=
  ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
    ∑ g : G, V.character g • MonoidAlgebra.single g⁻¹ (1 : ℂ)

/-! ### Basic positivity/nonvanishing facts -/

private lemma card_ne_zero_cx : (Fintype.card G : ℂ) ≠ 0 := by
  haveI : Nonempty G := ⟨1⟩
  exact_mod_cast Fintype.card_ne_zero

/-- Simple `FDRep` objects have positive finrank. -/
private lemma finrank_pos_of_simple (V : FDRep ℂ G) [Simple V] : 0 < Module.finrank ℂ V := by
  by_contra hcon
  push_neg at hcon
  have h0 : Module.finrank ℂ V = 0 := Nat.eq_zero_of_le_zero hcon
  have hsub : Subsingleton (V : Type _) := Module.finrank_zero_iff.mp h0
  have hsub2 : Subsingleton (V ⟶ V) := by
    constructor; intro f g
    exact Action.Hom.ext (FGModuleCat.hom_ext (LinearMap.ext (fun x => hsub.elim _ _)))
  have hone : Module.finrank ℂ (V ⟶ V) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]; simp
  have hzero : Module.finrank ℂ (V ⟶ V) = 0 := Module.finrank_zero_of_subsingleton
  omega

private lemma finrank_ne_zero_cx (V : FDRep ℂ G) [Simple V] :
    (Module.finrank ℂ V : ℂ) ≠ 0 := by
  have := finrank_pos_of_simple V
  exact_mod_cast this.ne'

/-! ### Schur scalar helper

Any equivariant endomorphism of a simple `FDRep` is a scalar multiple of the identity, with
the scalar determined by the trace. -/

/-- If a linear endomorphism `T` of a simple object `V : FDRep ℂ G` commutes with the action,
then it is a scalar multiple of the identity, and the scalar is `trace T / dim V`. -/
private lemma endo_scalar (V : FDRep ℂ G) [Simple V]
    (T : V →ₗ[ℂ] V) (hT : ∀ g : G, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id ∧
      LinearMap.trace ℂ V T = c * (Module.finrank ℂ V : ℂ) := by
  -- `T` lies in the invariants of `linHom V.ρ V.ρ`, i.e. it is `G`-equivariant.
  have hmemT : T ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g
    rw [Representation.linHom_apply, hT g⁻¹, ← LinearMap.comp_assoc,
      show V.ρ g ∘ₗ V.ρ g⁻¹ = LinearMap.id by
        rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_eq_id],
      LinearMap.id_comp]
  -- the invariant space is one dimensional (categorical Schur)
  have h1dim : Module.finrank ℂ (Representation.linHom V.ρ V.ρ).invariants = 1 := by
    rw [LinearEquiv.finrank_eq (Representation.linHom.invariantsEquivFDRepHom V V)]
    exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ V
  -- the identity is a nonzero invariant
  have hid_mem : (LinearMap.id : V →ₗ[ℂ] V) ∈ (Representation.linHom V.ρ V.ρ).invariants := by
    intro g; ext v
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    change (V.ρ g * V.ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]; rfl
  have hid_ne : (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, Submodule.coe_zero]
    intro hz
    have : (Module.finrank ℂ V : ℂ) = 0 := by
      rw [← LinearMap.trace_id (R := ℂ) (M := V), hz, map_zero]
    exact finrank_ne_zero_cx V this
  -- every invariant is a scalar multiple of the identity
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    (⟨LinearMap.id, hid_mem⟩ : (Representation.linHom V.ρ V.ρ).invariants) hid_ne).mp h1dim
    ⟨T, hmemT⟩
  have hTeq : T = c • LinearMap.id := by
    have hval := congrArg Subtype.val hc
    simpa using hval.symm
  refine ⟨c, hTeq, ?_⟩
  rw [hTeq, map_smul, LinearMap.trace_id, smul_eq_mul]

/-! ### The action of `ψ V` -/

/-- The action of `ψ V` on `W` as an explicit scalar multiple of a sum of `W.ρ g⁻¹`. -/
private lemma asAlgebraHom_psi (V W : FDRep ℂ G) :
    Representation.asAlgebraHom W.ρ (psi V)
      = ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) •
          ∑ g : G, V.character g • W.ρ g⁻¹ := by
  simp only [psi, map_smul, map_sum, Representation.asAlgebraHom_single_one]

/-- `ψ V` commutes with every group element `single h 1` in `ℂ[G]`. -/
private lemma psi_comm_single (V : FDRep ℂ G) (h : G) :
    psi V * MonoidAlgebra.single h (1 : ℂ) = MonoidAlgebra.single h (1 : ℂ) * psi V := by
  rw [psi, smul_mul_assoc, mul_smul_comm]
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum]
  -- reindex by conjugation `g ↦ h⁻¹ g h`
  let e : G ≃ G :=
    { toFun := fun g => h⁻¹ * g * h
      invFun := fun g => h * g * h⁻¹
      left_inv := by intro g; group
      right_inv := by intro g; group }
  refine Fintype.sum_equiv e _ _ ?_
  intro g
  have hchar : V.character (h⁻¹ * g * h) = V.character g := by
    have := V.char_conj g h⁻¹; simpa using this
  simp only [e, Equiv.coe_fn_mk, smul_mul_assoc, mul_smul_comm,
    MonoidAlgebra.single_mul_single, one_mul]
  rw [hchar, show h * (h⁻¹ * g * h)⁻¹ = g⁻¹ * h by group]

/-- The action of `ψ V` on `W` commutes with the `G`-action. -/
private lemma asAlgebraHom_psi_comm (V W : FDRep ℂ G) (g : G) :
    (Representation.asAlgebraHom W.ρ (psi V)) ∘ₗ W.ρ g
      = W.ρ g ∘ₗ (Representation.asAlgebraHom W.ρ (psi V)) := by
  have hc := psi_comm_single V g
  have h2 := congrArg (Representation.asAlgebraHom W.ρ) hc
  rw [map_mul, map_mul, Representation.asAlgebraHom_single_one] at h2
  simpa only [Module.End.mul_eq_comp] using h2

/-- The trace of the action of `ψ V` on `W`. -/
private lemma trace_asAlgebraHom_psi (V W : FDRep ℂ G) :
    LinearMap.trace ℂ W (Representation.asAlgebraHom W.ρ (psi V))
      = ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) *
          ∑ g : G, V.character g * W.character g⁻¹ := by
  rw [asAlgebraHom_psi V W, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- **Problem 4.5.2(i), diagonal case.** `ψ_V` acts on `V` itself as the identity. -/
theorem psi_acts_self (V : FDRep ℂ G) [Simple V] :
    Representation.asAlgebraHom V.ρ (psi V) = LinearMap.id := by
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero card_ne_zero_cx
  obtain ⟨c, hTc, htr⟩ := endo_scalar V _ (asAlgebraHom_psi_comm V V)
  have hsum : ∑ g : G, V.character g * V.character g⁻¹ = (Fintype.card G : ℂ) := by
    have ho := FDRep.char_orthonormal V V
    rw [if_pos ⟨Iso.refl V⟩] at ho
    have h2 : ∑ g : G, V.character g * V.character g⁻¹
        = (Fintype.card G : ℂ) •
            (⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * V.character g⁻¹) := by
      rw [smul_smul, mul_invOf_self, one_smul]
    rw [h2, ho]; simp
  have htrace : LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (psi V))
      = (Module.finrank ℂ V : ℂ) := by
    rw [trace_asAlgebraHom_psi V V, hsum, div_mul_cancel₀ _ card_ne_zero_cx]
  have hc1 : c = 1 := by
    have h : c * (Module.finrank ℂ V : ℂ) = (Module.finrank ℂ V : ℂ) := htr.symm.trans htrace
    have : c * (Module.finrank ℂ V : ℂ) = 1 * (Module.finrank ℂ V : ℂ) := by rw [one_mul]; exact h
    exact mul_right_cancel₀ (finrank_ne_zero_cx V) this
  rw [hTc, hc1, one_smul]

/-- **Problem 4.5.2(i), off-diagonal case.** If `W` and `V` are non-isomorphic simple
representations, then `ψ_V` acts on `W` as the null map. -/
theorem psi_acts_other (V W : FDRep ℂ G) [Simple V] [Simple W] (h : IsEmpty (W ≅ V)) :
    Representation.asAlgebraHom W.ρ (psi V) = 0 := by
  haveI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero card_ne_zero_cx
  obtain ⟨c, hTc, htr⟩ := endo_scalar W _ (asAlgebraHom_psi_comm V W)
  have hsum : ∑ g : G, V.character g * W.character g⁻¹ = 0 := by
    have ho := FDRep.char_orthonormal V W
    rw [if_neg (by rintro ⟨e⟩; exact h.false e.symm)] at ho
    have h2 : ∑ g : G, V.character g * W.character g⁻¹
        = (Fintype.card G : ℂ) •
            (⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * W.character g⁻¹) := by
      rw [smul_smul, mul_invOf_self, one_smul]
    rw [h2, ho]; simp
  have htrace : LinearMap.trace ℂ W (Representation.asAlgebraHom W.ρ (psi V)) = 0 := by
    rw [trace_asAlgebraHom_psi V W, hsum, mul_zero]
  have hc0 : c = 0 := by
    have h2 : c * (Module.finrank ℂ W : ℂ) = 0 := htr.symm.trans htrace
    exact (mul_eq_zero.mp h2).resolve_right (finrank_ne_zero_cx W)
  rw [hTc, hc0, zero_smul]

/-- **Problem 4.5.2(ii), idempotence.** Each `ψ_V` is an idempotent of `ℂ[G]`. -/
theorem psi_idempotent (V : FDRep ℂ G) [Simple V] :
    psi V * psi V = psi V := by
  sorry

/-- **Problem 4.5.2(ii), orthogonality.** For non-isomorphic simple representations `V`
and `W`, the idempotents `ψ_V` and `ψ_W` are orthogonal. -/
theorem psi_orthogonal (V W : FDRep ℂ G) [Simple V] [Simple W] (h : IsEmpty (W ≅ V)) :
    psi W * psi V = 0 := by
  sorry

end Etingof
