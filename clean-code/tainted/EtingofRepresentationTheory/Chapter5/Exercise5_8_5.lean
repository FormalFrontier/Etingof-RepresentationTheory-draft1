import Mathlib
import EtingofRepresentationTheory.Chapter5.Definition5_8_1

/-!
# Exercise 5.8.5: `Ind_K^G ℂ_χ ≅ ℂ[G] e_χ`

**Exercise 5.8.5.** Let `K ⊂ G` be finite groups, and let `χ : K → ℂ*` be a homomorphism.
Let `ℂ_χ` be the corresponding 1-dimensional representation of `K`. Let

  `e_χ = (1/|K|) ∑_{g ∈ K} χ(g)⁻¹ g ∈ ℂ[K]`

be the idempotent corresponding to `χ`. Show that the `G`-representation `Ind_K^G ℂ_χ` is
naturally isomorphic to `ℂ[G] e_χ` (with `G` acting by left multiplication).

## Formalization

* `chiRep χ : Representation ℂ K ℂ` is the 1-dimensional representation `ℂ_χ` where `k` acts
  by the scalar `χ k`.
* `idempotentOfChar χ : ℂ[G]` is `e_χ = |K|⁻¹ ∑_{g ∈ K} χ(g)⁻¹ · g` (the elements of `K` are
  included into `G`).
* `charLeftIdeal χ : Submodule ℂ[G] ℂ[G]` is the left ideal `ℂ[G] · e_χ`, on which `G` acts by
  left multiplication `g · x = of(g) * x`.

The induced representation is `Etingof.Definition5_8_1 K (chiRep χ)`. The claim is a
`G`-equivariant `ℂ`-linear isomorphism `e` between its carrier and the left ideal `ℂ[G] e_χ`,
expressed by the intertwining identity `↑(e (ρ_ind g x)) = of(g) * ↑(e x)` in `ℂ[G]`.

The isomorphism sends `⟦single h 1 ⊗ z⟧` to `z • (of h⁻¹ * e_χ)`; its inverse sends
`single g c` to `c • ⟦single g⁻¹ 1 ⊗ 1⟧`. Well-definedness on the coinvariants uses
`of k * e_χ = χ(k) • e_χ` for `k ∈ K`, and the two composites are the identity by the
idempotence `e_χ * e_χ = e_χ` and the coinvariant relation.
-/

namespace Etingof

open scoped Classical
open Representation MonoidAlgebra

variable {G : Type*} [Group G] [Fintype G] (K : Subgroup G)

/-- The 1-dimensional representation `ℂ_χ` of `K` attached to a character `χ : K → ℂ*`:
`k` acts on `ℂ` by multiplication by the scalar `χ k`. -/
noncomputable def chiRep (χ : K →* ℂˣ) : Representation ℂ K ℂ where
  toFun k := ((χ k : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' k₁ k₂ := by
    apply LinearMap.ext; intro z
    change ((χ (k₁ * k₂) : ℂˣ) : ℂ) * z = ((χ k₁ : ℂˣ) : ℂ) * (((χ k₂ : ℂˣ) : ℂ) * z)
    rw [map_mul, Units.val_mul, mul_assoc]

/-- The idempotent `e_χ = |K|⁻¹ ∑_{g ∈ K} χ(g)⁻¹ · g ∈ ℂ[G]` attached to `χ`. -/
noncomputable def idempotentOfChar (χ : K →* ℂˣ) : MonoidAlgebra ℂ G :=
  (Nat.card K : ℂ)⁻¹ •
    ∑ g : K, ((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)

/-- The left ideal `ℂ[G] · e_χ`, with `G` acting by left multiplication. -/
noncomputable def charLeftIdeal (χ : K →* ℂˣ) : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
  Submodule.span (MonoidAlgebra ℂ G) {idempotentOfChar K χ}

section Proof

variable (χ : K →* ℂˣ)

/-- Abbreviation for the underlying `K`-representation on `ℂ[G] ⊗ ℂ` whose coinvariants form
`Ind_K^G ℂ_χ`. The type ascription is deliberately omitted: writing it out wraps the term so
that the defeq `Coinvariants (indRep K χ) = Representation.IndV K.subtype (chiRep K χ)` forces
Lean to fully reduce the tensor-product representation, blowing the `whnf` heartbeat budget. -/
private noncomputable abbrev indRep :=
  Representation.tprod ((leftRegular ℂ G).comp K.subtype) (chiRep K χ)

omit [Fintype G] in
private lemma chiRep_apply (k : K) (z : ℂ) : chiRep K χ k z = ((χ k : ℂˣ) : ℂ) • z := rfl

/-- Key relation: left multiplication of the idempotent `e_χ` by `of k` (for `k ∈ K`)
scales it by `χ k`. -/
private lemma of_smul_idempotentOfChar (k : K) :
    MonoidAlgebra.of ℂ G (k : G) * idempotentOfChar K χ
      = ((χ k : ℂˣ) : ℂ) • idempotentOfChar K χ := by
  classical
  have ha : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [idempotentOfChar, mul_smul_comm, smul_comm]
  congr 1
  rw [Finset.mul_sum, Finset.smul_sum,
    ← Equiv.sum_comp (Equiv.mulLeft k)
      (fun g : K => ((χ k : ℂˣ) : ℂ) • (((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)))]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [mul_smul_comm, ← map_mul, ← Subgroup.coe_mul, smul_smul]
  congr 1
  -- scalar identity: `↑(χ g)⁻¹ = ↑(χ k) * ↑(χ (k*g))⁻¹`
  have hb : ((χ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul, Units.val_mul]
  field_simp

/-- The idempotent `e_χ` is idempotent: `e_χ * e_χ = e_χ`. -/
private lemma idempotentOfChar_mul_self :
    idempotentOfChar K χ * idempotentOfChar K χ = idempotentOfChar K χ := by
  classical
  have hn : (Nat.card K : ℂ) ≠ 0 := by
    have : 0 < Nat.card K := Nat.card_pos
    exact_mod_cast this.ne'
  have hdef : idempotentOfChar K χ
      = (Nat.card K : ℂ)⁻¹ • ∑ g : K, ((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G) := rfl
  nth_rewrite 1 [hdef]
  rw [Finset.smul_sum, Finset.sum_mul]
  have hstep : ∀ g : K, ((Nat.card K : ℂ)⁻¹ • ((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G))
      * idempotentOfChar K χ
      = (Nat.card K : ℂ)⁻¹ • idempotentOfChar K χ := by
    intro g
    rw [smul_mul_assoc, smul_mul_assoc, of_smul_idempotentOfChar, smul_smul, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero (χ g)), mul_one]
  rw [Finset.sum_congr rfl (fun g _ => hstep g), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.card_eq_fintype_card, smul_smul,
    mul_inv_cancel₀ hn, one_smul]

/-- The linear functional `ℂ[G] → ℂ[G]`, `single g c ↦ c • (of g⁻¹ * e_χ)`, that (after tensoring
down) underlies the forward map. -/
private noncomputable def fwdFin : MonoidAlgebra ℂ G →ₗ[ℂ] MonoidAlgebra ℂ G :=
  Finsupp.linearCombination ℂ
      (fun g : G => MonoidAlgebra.of ℂ G g⁻¹ * idempotentOfChar K χ) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] private lemma fwdFin_single (x : G) (c : ℂ) :
    fwdFin K χ (MonoidAlgebra.single x c) =
      c • (MonoidAlgebra.of ℂ G x⁻¹ * idempotentOfChar K χ) := by
  rw [fwdFin, LinearMap.comp_apply]
  change (Finsupp.linearCombination ℂ
    (fun g : G => MonoidAlgebra.of ℂ G g⁻¹ * idempotentOfChar K χ))
      (Finsupp.single x c) = _
  exact Finsupp.linearCombination_single ℂ c x

/-- The invariance step: pushing the `K`-action through `fwdFin` scales by `χ k` and cancels. -/
private lemma fwdFin_leftRegular (k : K) (a : MonoidAlgebra ℂ G) :
    ((χ k : ℂˣ) : ℂ) • fwdFin K χ ((leftRegular ℂ G) (K.subtype k) a) = fwdFin K χ a := by
  classical
  have ha : ((χ k : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, smul_add, hp, hq]
  | single x c =>
    simp only [Subgroup.coe_subtype, ofMulAction_single, smul_eq_mul, fwdFin_single]
    rw [smul_smul, mul_comm ((χ k : ℂˣ) : ℂ) c, ← smul_smul]
    congr 1
    rw [mul_inv_rev, ← Subgroup.coe_inv, map_mul, mul_assoc, of_smul_idempotentOfChar,
      mul_smul_comm, smul_smul, map_inv, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ ha, one_smul]

/-- The forward map `Ind_K^G ℂ_χ → ℂ[G]` underlying the isomorphism, sending
`⟦single h 1 ⊗ z⟧` to `z • (of h⁻¹ * e_χ)`. -/
private noncomputable def fwd :
    Representation.IndV K.subtype (chiRep K χ) →ₗ[ℂ] MonoidAlgebra ℂ G :=
  Coinvariants.lift (indRep K χ)
    ((fwdFin K χ) ∘ₗ (TensorProduct.rid ℂ (MonoidAlgebra ℂ G)).toLinearMap)
    (by
      intro k
      refine TensorProduct.ext' (fun a z => ?_)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, indRep, Representation.tprod_apply,
        TensorProduct.map_tmul, TensorProduct.rid_tmul, chiRep_apply, MonoidHom.comp_apply,
        smul_eq_mul, map_smul]
      rw [mul_comm ((χ k : ℂˣ) : ℂ) z, ← smul_smul, fwdFin_leftRegular])

/-- Evaluation of `fwd` on a generator `⟦single h 1 ⊗ z⟧`. -/
private lemma fwd_mk (h : G) (z : ℂ) :
    fwd K χ (Representation.IndV.mk K.subtype (chiRep K χ) h z)
      = z • (MonoidAlgebra.of ℂ G h⁻¹ * idempotentOfChar K χ) := by
  simp only [fwd, Representation.IndV.mk, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.mk_apply, Coinvariants.lift_mk, TensorProduct.rid_tmul, map_smul,
    fwdFin_single, one_smul]

/-- The range of `fwdFin`, and hence of `fwd`, lands in the left ideal. -/
private lemma fwdFin_eq (y : MonoidAlgebra ℂ G) :
    fwdFin K χ y
      = (Finsupp.linearCombination ℂ (fun g : G => MonoidAlgebra.of ℂ G g⁻¹) y.coeff)
        * idempotentOfChar K χ := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [map_add, hp, hq, MonoidAlgebra.coeff_add, map_add, add_mul]
  | single x c =>
    rw [fwdFin_single, MonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, smul_mul_assoc]

private lemma fwd_mem (x : Representation.IndV K.subtype (chiRep K χ)) :
    fwd K χ x ∈ charLeftIdeal K χ := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective (indRep K χ) x
  have hfx : fwd K χ (Coinvariants.mk (indRep K χ) v)
      = (Finsupp.linearCombination ℂ (fun g : G => MonoidAlgebra.of ℂ G g⁻¹)
          ((TensorProduct.rid ℂ (MonoidAlgebra ℂ G)) v).coeff) * idempotentOfChar K χ := by
    rw [show fwd K χ (Coinvariants.mk (indRep K χ) v)
        = fwdFin K χ ((TensorProduct.rid ℂ (MonoidAlgebra ℂ G)) v) from rfl, fwdFin_eq]
  rw [hfx, charLeftIdeal]
  exact Submodule.mem_span_singleton.2 ⟨_, smul_eq_mul _ _⟩

omit [Fintype G] in
/-- The backward map `ℂ[G] → Ind_K^G ℂ_χ`, `single g c ↦ c • ⟦single g⁻¹ 1 ⊗ 1⟧`. -/
private noncomputable def bwd :
    MonoidAlgebra ℂ G →ₗ[ℂ] Representation.IndV K.subtype (chiRep K χ) :=
  Finsupp.linearCombination ℂ
      (fun g : G => Representation.IndV.mk K.subtype (chiRep K χ) g⁻¹ 1) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

omit [Fintype G] in
private lemma bwd_of (x : G) :
    bwd K χ (MonoidAlgebra.of ℂ G x) = Representation.IndV.mk K.subtype (chiRep K χ) x⁻¹ 1 := by
  change Finsupp.linearCombination ℂ
      (fun g : G => Representation.IndV.mk K.subtype (chiRep K χ) g⁻¹ 1)
        (Finsupp.single x 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

omit [Fintype G] in
/-- The coinvariant relation: `⟦single (κ·x) 1 ⊗ χ(κ)·w⟧ = ⟦single x 1 ⊗ w⟧`. -/
private lemma indV_mk_smul (κ : K) (x : G) (w : ℂ) :
    Representation.IndV.mk K.subtype (chiRep K χ) ((κ : G) * x) (((χ κ : ℂˣ) : ℂ) • w)
      = Representation.IndV.mk K.subtype (chiRep K χ) x w := by
  have h := Coinvariants.mk_self_apply (indRep K χ) κ
    (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] w)
  simpa only [Representation.IndV.mk, LinearMap.comp_apply, TensorProduct.mk_apply, indRep,
    Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ofMulAction_single, smul_eq_mul, chiRep_apply] using h

/-- Key computation for the left inverse: `bwd (of h⁻¹ · e_χ) = ⟦single h 1 ⊗ 1⟧`. -/
private lemma bwd_of_inv_mul_idem (h : G) :
    bwd K χ (MonoidAlgebra.of ℂ G h⁻¹ * idempotentOfChar K χ)
      = Representation.IndV.mk K.subtype (chiRep K χ) h 1 := by
  classical
  have hn : (Nat.card K : ℂ) ≠ 0 := by
    have : 0 < Nat.card K := Nat.card_pos
    exact_mod_cast this.ne'
  rw [idempotentOfChar, mul_smul_comm, map_smul, Finset.mul_sum, map_sum]
  have hsummand : ∀ g : K,
      bwd K χ (MonoidAlgebra.of ℂ G h⁻¹ *
          (((χ g : ℂˣ)⁻¹ : ℂ) • MonoidAlgebra.of ℂ G (g : G)))
        = Representation.IndV.mk K.subtype (chiRep K χ) h 1 := by
    intro g
    rw [mul_smul_comm, map_smul, ← map_mul, bwd_of, mul_inv_rev, inv_inv, ← Subgroup.coe_inv,
      ← indV_mk_smul K χ g⁻¹ h 1, ← map_smul]
    congr 1
    rw [map_inv, Units.val_inv_eq_inv_val]
  rw [Finset.sum_congr rfl (fun g _ => hsummand g), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.card_eq_fintype_card, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

/-- The composite `fwd ∘ bwd` is right multiplication by `e_χ`. -/
private lemma fwd_bwd (x : MonoidAlgebra ℂ G) :
    fwd K χ (bwd K χ x) = x * idempotentOfChar K χ := by
  -- Induct with `MonoidAlgebra.induction_on` (not `Finsupp.induction_linear`): its case
  -- variables stay in `ℂ[G]`, whereas the `Finsupp` principle types them as `G →₀ ℂ`, and the
  -- resulting `ℂ[G] = G →₀ ℂ` mismatch is only defeq at default (not `instances`) transparency,
  -- which breaks the `map_add`/`map_smul` rewrites into `bwd`/`fwd`.
  induction x using MonoidAlgebra.induction_on with
  | hM g => rw [bwd_of, fwd_mk, inv_inv, one_smul]
  | hadd p q hp hq => rw [map_add, map_add, hp, hq, add_mul]
  | hsmul r p hp => rw [map_smul, map_smul, hp, smul_mul_assoc]

end Proof

/-- Exercise 5.8.5. The induced representation `Ind_K^G ℂ_χ` is `G`-equivariantly isomorphic
to the left ideal `ℂ[G] e_χ` (with `G` acting by left multiplication). The intertwining is
recorded via the coercion to `ℂ[G]`: `↑(e (ρ_ind g x)) = of(g) * ↑(e x)`. -/
theorem ind_chiRep_iso_charLeftIdeal (χ : K →* ℂˣ) :
    ∃ e : Representation.IndV K.subtype (chiRep K χ) ≃ₗ[ℂ] ↥(charLeftIdeal K χ),
      ∀ (g : G) x,
        (e (Etingof.Definition5_8_1 K (chiRep K χ) g x) : MonoidAlgebra ℂ G)
          = MonoidAlgebra.of ℂ G g * (e x : MonoidAlgebra ℂ G) := by
  classical
  -- pointwise computations on generators `⟦single h 1 ⊗ z⟧`
  have hpt_left : ∀ (h : G) (z : ℂ),
      bwd K χ (fwd K χ (Representation.IndV.mk K.subtype (chiRep K χ) h z))
        = Representation.IndV.mk K.subtype (chiRep K χ) h z := by
    intro h z
    rw [fwd_mk, map_smul, bwd_of_inv_mul_idem, ← map_smul, smul_eq_mul, mul_one]
  have key_left : bwd K χ ∘ₗ fwd K χ = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro h
    apply LinearMap.ext
    intro z
    change bwd K χ (fwd K χ (Representation.IndV.mk K.subtype (chiRep K χ) h z))
        = Representation.IndV.mk K.subtype (chiRep K χ) h z
    exact hpt_left h z
  refine ⟨LinearEquiv.ofLinear
      ((fwd K χ).codRestrict ((charLeftIdeal K χ).restrictScalars ℂ) (fun x => fwd_mem K χ x))
      ((bwd K χ).comp ((charLeftIdeal K χ).subtype.restrictScalars ℂ)) ?_ ?_, ?_⟩
  · -- `fwd ∘ bwd = id` on the left ideal (right inverse)
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change fwd K χ (bwd K χ (x : MonoidAlgebra ℂ G)) = (x : MonoidAlgebra ℂ G)
    rw [fwd_bwd]
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1
      ((Submodule.restrictScalars_mem ℂ _ _).1 x.2)
    rw [← hr, smul_eq_mul, mul_assoc, idempotentOfChar_mul_self]
  · -- left inverse
    apply LinearMap.ext
    intro y
    change bwd K χ (fwd K χ y) = y
    exact LinearMap.congr_fun key_left y
  · -- intertwining identity
    intro g x
    have hpt : ∀ (h : G) (z : ℂ),
        fwd K χ (Representation.ind K.subtype (chiRep K χ) g
            (Representation.IndV.mk K.subtype (chiRep K χ) h z))
          = MonoidAlgebra.of ℂ G g *
              fwd K χ (Representation.IndV.mk K.subtype (chiRep K χ) h z) := by
      intro h z
      rw [Representation.ind_mk, fwd_mk, fwd_mk, mul_inv_rev, inv_inv, map_mul, mul_assoc,
        mul_smul_comm]
    have key_intw : (fwd K χ) ∘ₗ (Representation.ind K.subtype (chiRep K χ) g)
        = (LinearMap.mulLeft ℂ (MonoidAlgebra.of ℂ G g)) ∘ₗ (fwd K χ) := by
      apply Representation.IndV.hom_ext
      intro h
      apply LinearMap.ext
      intro z
      change fwd K χ (Representation.ind K.subtype (chiRep K χ) g
          (Representation.IndV.mk K.subtype (chiRep K χ) h z))
        = MonoidAlgebra.of ℂ G g *
            fwd K χ (Representation.IndV.mk K.subtype (chiRep K χ) h z)
      exact hpt h z
    simp only [LinearEquiv.ofLinear_apply]
    exact LinearMap.congr_fun key_intw x

end Etingof
