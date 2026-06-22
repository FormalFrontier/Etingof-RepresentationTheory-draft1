import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_12_2_ClassificationGeneral
import EtingofRepresentationTheory.Chapter5.SpechtCharacterGeneral

/-!
# The Specht bridge over a general field `k`

This file lifts the **Specht bridge** of `Theorem5_22_1.lean` (β.2) from ℂ to a general
characteristic-zero algebraically closed field `k`. The bridge identifies a simple
`symGroupImage`-submodule `S ≤ V^⊗n` (`V = Fin N → k`) with a Specht module and reads off its
permutation-trace character as the general-`k` Specht character `spechtModuleCharacterK k n la`
(from `SpechtCharacterGeneral.lean`, #4991).

## Why a new file

The ℂ bridge lives in `Theorem5_22_1.lean`, but its general-`k` analogue needs
`Theorem5_12_2_classification_general` (the general-field Specht classification) and the
general-`k` Specht character API — both in files that *import* `Theorem5_22_1.lean`
(via `Infrastructure.SpechtModuleSimple`). Editing the bridge in place would create an
import cycle, so the general-`k` bridge is placed here, strictly downstream of all three
ingredients, leaving the ℂ original untouched. (This is the documented ℂ→general-`k`
downstream-file pattern.) The private bridge infrastructure of `Theorem5_22_1.lean`
(`symGroupAlgHomToImage`, `submoduleAsSymGroupAlgebraModule`, …) is re-stated here over `k`,
reusing only the public, already-generic pieces (`symGroupImage`, `symGroupAction`,
`symGroupAlgHom`, `symGroupAlgHom_range`, `symGroupAction_mem_of_symGroupImage_submodule`).

## Main results

* `trace_symGroupAction_eq_spechtModuleCharacterK` — every simple `symGroupImage`-submodule
  `S` admits a label `la'` with `σ`-trace `= spechtModuleCharacterK k n la'`.
* `simpleSubmodule_iso_of_spechtCharacterK_eq` and its wrapper
  `simpleSymGroupImageSubmodule_iso_of_spechtCharacterK_eq` — two simple submodules with the
  same Specht character are `symGroupImage`-isomorphic.
-/

noncomputable section

namespace Etingof

/-! ### The Specht bridge over `k` -/

-- The module-ferrying infrastructure in this section needs only `[Field k]`; the
-- algebraic-closure and characteristic-zero hypotheses enter only at the classification /
-- character-injectivity steps (the public theorems below).
section Infrastructure

variable {k : Type} [Field k] {N n : ℕ}

/-- Codomain-restricted version of `symGroupAlgHom`, landing in `symGroupImage`.
This is a surjection `k[S_n] →ₐ[k] symGroupImage`. -/
private noncomputable def symGroupAlgHomToImageK :
    MonoidAlgebra k (Equiv.Perm (Fin n)) →ₐ[k] ↥(symGroupImage k (Fin N → k) n) :=
  AlgHom.codRestrict (symGroupAlgHom k (Fin N → k) n)
    (symGroupImage k (Fin N → k) n)
    (fun a => by rw [← symGroupAlgHom_range]; exact ⟨a, rfl⟩)

@[simp]
private theorem symGroupAlgHomToImageK_val (a : MonoidAlgebra k (Equiv.Perm (Fin n))) :
    ((symGroupAlgHomToImageK (k := k) (N := N) (n := n)) a).val =
      (symGroupAlgHom k (Fin N → k) n) a := rfl

private theorem symGroupAlgHomToImageK_surjective :
    Function.Surjective (symGroupAlgHomToImageK (k := k) (N := N) (n := n)) := by
  intro b
  have h_in : (b.val : Module.End k _) ∈ (symGroupAlgHom k (Fin N → k) n).range := by
    rw [symGroupAlgHom_range]; exact b.prop
  obtain ⟨a, ha⟩ := h_in
  exact ⟨a, Subtype.ext ha⟩

private theorem symGroupAlgHomToImageK_of (σ : Equiv.Perm (Fin n)) :
    (symGroupAlgHomToImageK (k := k) (N := N) (n := n)) (MonoidAlgebra.of k _ σ) =
      ⟨(symGroupAction k (Fin N → k) n σ).toLinearMap,
        Algebra.subset_adjoin ⟨σ, rfl⟩⟩ := by
  apply Subtype.ext
  change (symGroupAlgHom k (Fin N → k) n) (MonoidAlgebra.of k _ σ) = _
  unfold symGroupAlgHom
  rw [MonoidAlgebra.lift_of]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The `symGroupImage`-action synthesis traverses the deep `Subalgebra → Subsemiring → Module`
-- instance chain exceeding the default heartbeats.
/-- Value-level description of the `↥(symGroupImage)`-action on a submodule
`S ≤ V^⊗n` via `symGroupAlgHomToImageK`. -/
private theorem symGroupAlgHomToImageK_smul_val
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (x : ↥S) :
    ((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).val =
      (symGroupAlgHom k (Fin N → k) n a) x.val := by
  rw [Submodule.coe_smul, Subalgebra.smul_def, Module.End.smul_def,
      symGroupAlgHomToImageK_val]

set_option synthInstance.maxHeartbeats 200000 in
-- `Module.compHom` synthesises a `Module (symGroupImage) ↥(S.restrictScalars k)`
-- instance, traversing a deep `Subalgebra → Subsemiring → Module` chain that
-- exceeds the default 20000 heartbeats.
/-- The `k[S_n]`-module structure on `↥(S.restrictScalars k)` induced from the
`symGroupImage`-module structure on `↥S` via `symGroupAlgHomToImageK`. -/
private noncomputable def submoduleAsSymGroupAlgebraModuleK
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n)) :
    Module (MonoidAlgebra k (Equiv.Perm (Fin n))) ↥(S.restrictScalars k) :=
  Module.compHom _ (symGroupAlgHomToImageK (k := k) (N := N) (n := n)).toRingHom

set_option synthInstance.maxHeartbeats 200000 in
-- The `letI := submoduleAsSymGroupAlgebraModuleK S` forces synthesis of the deep
-- `Subalgebra → Subsemiring → Module` instance chain.
/-- The smul of `submoduleAsSymGroupAlgebraModuleK` agrees with applying
`symGroupAlgHomToImageK(a)` to the carrier. -/
private theorem submoduleAsSymGroupAlgebraModuleK_smul_def
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    (a : MonoidAlgebra k (Equiv.Perm (Fin n))) (v : ↥(S.restrictScalars k)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    (a • v).val = (symGroupAlgHom k (Fin N → k) n) a v.val := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The `IsScalarTower` elaboration traverses the deep `Subalgebra → Subsemiring → Module`
-- instance chain.
/-- Scalar tower: `(c • a) • v = c • (a • v)` for `c : k`,
`a : k[S_n]`, `v : ↥(S.restrictScalars k)`. -/
private theorem submoduleAsSymGroupAlgebra_isScalarTowerK
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    IsScalarTower k (MonoidAlgebra k (Equiv.Perm (Fin n))) ↥(S.restrictScalars k) := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  refine ⟨fun c a v => ?_⟩
  apply Subtype.ext
  rw [submoduleAsSymGroupAlgebraModuleK_smul_def, map_smul]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Constructing the semilinear map elaborates both `Module` instances on the carrier, each via
-- the deep `Subalgebra → Subsemiring → Module` instance chain.
/-- The identity-on-carrier `↥(S.restrictScalars k) → ↥S`, semilinear over the
surjective ring hom `symGroupAlgHomToImageK`. -/
private noncomputable def submoduleSemilinearIdK
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    ↥(S.restrictScalars k) →ₛₗ[(symGroupAlgHomToImageK (k := k) (N := N) (n := n)).toRingHom] ↥S :=
  letI := submoduleAsSymGroupAlgebraModuleK S
  { toFun := fun v => ⟨v.val, v.prop⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

set_option synthInstance.maxHeartbeats 200000 in
-- Same deep `Subalgebra → Subsemiring → Module` instance chain as `submoduleSemilinearIdK`.
private theorem submoduleSemilinearIdK_bijective
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n)) :
    letI := submoduleAsSymGroupAlgebraModuleK S
    Function.Bijective (submoduleSemilinearIdK S) := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  refine ⟨?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    exact Subtype.ext_iff.mp h
  · rintro ⟨w, hw⟩; exact ⟨⟨w, hw⟩, rfl⟩

set_option synthInstance.maxHeartbeats 200000 in
-- The `RingHomSurjective` instance and bijective-semilinear transfer both invoke `Module`
-- synthesis traversing the deep `Subalgebra → Subsemiring → Module` instance chain.
/-- Simplicity of `↥S` as a `↥(symGroupImage)`-module transfers to simplicity
of `↥(S.restrictScalars k)` as a `k[S_n]`-module. -/
private theorem submoduleAsSymGroupAlgebra_isSimpleModuleK
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    [IsSimpleModule (↥(symGroupImage k (Fin N → k) n)) ↥S] :
    letI := submoduleAsSymGroupAlgebraModuleK S
    IsSimpleModule (MonoidAlgebra k (Equiv.Perm (Fin n))) ↥(S.restrictScalars k) := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  haveI : RingHomSurjective
      (symGroupAlgHomToImageK (k := k) (N := N) (n := n)).toRingHom :=
    ⟨symGroupAlgHomToImageK_surjective⟩
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (submoduleSemilinearIdK S)
    (submoduleSemilinearIdK_bijective S)).mpr ‹_›

/-- The action of `MonoidAlgebra.of k _ σ` on a Specht module is left
multiplication, i.e., `spechtModuleActionK k n la' σ`. -/
private theorem spechtModuleK_smul_of
    (la' : Nat.Partition n) (σ : Equiv.Perm (Fin n)) (w : ↥(SpechtModuleK k n la')) :
    ((MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) • w :
        ↥(SpechtModuleK k n la')) =
      spechtModuleActionK k n la' σ w := by
  apply Subtype.ext
  rfl

set_option maxHeartbeats 400000 in
-- The Specht-bridge conjugation unfolds `Module.compHom`, traverses a deep
-- `Subalgebra → Subsemiring → Module` chain, and applies trace conjugation.
set_option synthInstance.maxHeartbeats 200000 in
/-- The conjugation step of the Specht bridge over `k`. Given a `k[S_n]`-iso
`e : ↥(S.restrictScalars k) ≃ₗ SpechtModuleK k n la'`, the trace of the restricted
`σ`-action on `↥(S.restrictScalars k)` equals `spechtModuleCharacterK k n la' σ`. -/
private theorem trace_restrictedSymGroupAction_eq_of_spechtIsoK
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    (la' : Nat.Partition n)
    (e : letI := submoduleAsSymGroupAlgebraModuleK S
         ↥(S.restrictScalars k) ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
           ↥(SpechtModuleK k n la'))
    (σ : Equiv.Perm (Fin n)) :
    LinearMap.trace k ↥(S.restrictScalars k)
        ((symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
          (p := S.restrictScalars k) (q := S.restrictScalars k)
          (fun _ hv =>
            symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
      spechtModuleCharacterK k n la' σ := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S
  -- Convert `e` to a `k`-linear equiv.
  let ek : ↥(S.restrictScalars k) ≃ₗ[k] ↥(SpechtModuleK k n la') :=
    LinearEquiv.restrictScalars k e
  set restrictedAction :
      ↥(S.restrictScalars k) →ₗ[k] ↥(S.restrictScalars k) :=
    (symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
      (p := S.restrictScalars k) (q := S.restrictScalars k)
      (fun _ hv =>
        symGroupAction_mem_of_symGroupImage_submodule S σ hv)
  -- `ek` intertwines `restrictedAction` with `spechtModuleActionK k n la' σ`.
  have h_intertwine : ∀ v : ↥(S.restrictScalars k),
      ek (restrictedAction v) = spechtModuleActionK k n la' σ (ek v) := by
    intro v
    have h := e.map_smul (MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) v
    have h_lhs : (MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) • v =
        restrictedAction v := by
      apply Subtype.ext
      change (symGroupAlgHom k (Fin N → k) n) (MonoidAlgebra.of k _ σ) v.val =
        (symGroupAction k (Fin N → k) n σ).toLinearMap v.val
      unfold symGroupAlgHom
      rw [MonoidAlgebra.lift_of]
      rfl
    have h_rhs : (MonoidAlgebra.of k _ σ : MonoidAlgebra k (Equiv.Perm (Fin n))) • e v =
        spechtModuleActionK k n la' σ (e v) := spechtModuleK_smul_of la' σ (e v)
    rw [h_lhs, h_rhs] at h
    exact h
  have h_eq : restrictedAction = ek.symm.toLinearMap ∘ₗ
      (spechtModuleActionK k n la' σ) ∘ₗ ek.toLinearMap := by
    apply LinearMap.ext
    intro v
    change restrictedAction v = ek.symm (spechtModuleActionK k n la' σ (ek v))
    rw [← h_intertwine v, ek.symm_apply_apply]
  rw [h_eq]
  -- Trace conjugation: tr(ek.symm ∘ T ∘ ek) = tr(T) for `k`-linear T.
  have h_conj : ek.symm.toLinearMap ∘ₗ
      (spechtModuleActionK k n la' σ) ∘ₗ ek.toLinearMap =
        ek.symm.conj (spechtModuleActionK k n la' σ) := by
    rfl
  rw [h_conj, LinearMap.trace_conj']
  rfl

end Infrastructure

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N n : ℕ}

set_option maxHeartbeats 400000 in
-- The bridge construction unfolds `Module.compHom` and traverses the deep
-- `Subalgebra → Subsemiring → Module` instance chain.
set_option synthInstance.maxHeartbeats 200000 in
/-- **Specht bridge** (β.2) over `k`. Every simple `symGroupImage`-submodule `S ≤ V^⊗n`
admits a partition `la'` such that the trace of every `σ`-permutation operator restricted to
`S` equals `spechtModuleCharacterK k n la'`. -/
theorem trace_symGroupAction_eq_spechtModuleCharacterK
    (S : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    [IsSimpleModule (↥(symGroupImage k (Fin N → k) n)) ↥S] :
    ∃ la' : Nat.Partition n, ∀ σ : Equiv.Perm (Fin n),
      LinearMap.trace k ↥(S.restrictScalars k)
          ((symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv =>
              symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
        spechtModuleCharacterK k n la' σ := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S
  haveI := submoduleAsSymGroupAlgebra_isSimpleModuleK S
  obtain ⟨la', ⟨e⟩⟩ :=
    Theorem5_12_2_classification_general k n ↥(S.restrictScalars k)
  exact ⟨la', fun σ => trace_restrictedSymGroupAction_eq_of_spechtIsoK S la' e σ⟩

set_option maxHeartbeats 1600000 in
-- The transfer elaborates both `Module` instances on the shared carrier and the
-- surjective-ring-hom semilinearity, each via the deep instance chain.
set_option synthInstance.maxHeartbeats 400000 in
/-- Transfer a `k[S_n]`-linear equivalence between the restricted-scalar modules
`↥(S.restrictScalars k)` and `↥(S'.restrictScalars k)` to a `symGroupImage`-linear
equivalence `↥S ≃ₗ ↥S'`. -/
private noncomputable def transferToSymGroupImageEquivK
    (S S' : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    (g : letI := submoduleAsSymGroupAlgebraModuleK S
         letI := submoduleAsSymGroupAlgebraModuleK S'
         ↥(S.restrictScalars k) ≃ₗ[MonoidAlgebra k (Equiv.Perm (Fin n))]
           ↥(S'.restrictScalars k)) :
    ↥S ≃ₗ[↥(symGroupImage k (Fin N → k) n)] ↥S' :=
  letI := submoduleAsSymGroupAlgebraModuleK S
  letI := submoduleAsSymGroupAlgebraModuleK S'
  { toFun := fun x => ⟨(g ⟨x.val, x.property⟩).val, (g ⟨x.val, x.property⟩).property⟩
    invFun := fun y =>
      ⟨(g.symm ⟨y.val, y.property⟩).val, (g.symm ⟨y.val, y.property⟩).property⟩
    left_inv := fun x => by
      apply Subtype.ext
      exact congrArg Subtype.val (g.symm_apply_apply ⟨x.val, x.property⟩)
    right_inv := fun y => by
      apply Subtype.ext
      exact congrArg Subtype.val (g.apply_symm_apply ⟨y.val, y.property⟩)
    map_add' := fun x y => by
      apply Subtype.ext
      exact congrArg Subtype.val (g.map_add ⟨x.val, x.property⟩ ⟨y.val, y.property⟩)
    map_smul' := fun b x => by
      obtain ⟨a, rfl⟩ := symGroupAlgHomToImageK_surjective b
      apply Subtype.ext
      have hxeq : (⟨((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).val,
            ((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).property⟩ :
            ↥(S.restrictScalars k))
            = a • (⟨x.val, x.property⟩ : ↥(S.restrictScalars k)) := by
        apply Subtype.ext
        rw [submoduleAsSymGroupAlgebraModuleK_smul_def, symGroupAlgHomToImageK_smul_val]
      change (g ⟨((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).val,
            ((symGroupAlgHomToImageK (k := k) (N := N) (n := n) a) • x).property⟩).val = _
      rw [hxeq, map_smul, submoduleAsSymGroupAlgebraModuleK_smul_def,
          RingHom.id_apply, symGroupAlgHomToImageK_smul_val] }

set_option maxHeartbeats 800000 in
-- Classifying both restrictScalars modules and transferring the resulting iso traverses
-- the deep `Subalgebra → Subsemiring → Module` instance chain twice.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Character determines the module over `k`.** Two simple `symGroupImage`-submodules
`S, S' ≤ V^⊗n` whose `σ`-trace functions both equal `spechtModuleCharacterK k n la` are
isomorphic as `symGroupImage`-modules. -/
theorem simpleSubmodule_iso_of_spechtCharacterK_eq
    (S S' : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    [IsSimpleModule (↥(symGroupImage k (Fin N → k) n)) ↥S]
    [IsSimpleModule (↥(symGroupImage k (Fin N → k) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S.restrictScalars k)
          ((symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
          spechtModuleCharacterK k n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S'.restrictScalars k)
          ((symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
            (p := S'.restrictScalars k) (q := S'.restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S' σ hv)) =
          spechtModuleCharacterK k n la σ) :
    Nonempty (↥S ≃ₗ[↥(symGroupImage k (Fin N → k) n)] ↥S') := by
  letI := submoduleAsSymGroupAlgebraModuleK S
  letI := submoduleAsSymGroupAlgebraModuleK S'
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S
  haveI := submoduleAsSymGroupAlgebra_isScalarTowerK S'
  haveI := submoduleAsSymGroupAlgebra_isSimpleModuleK S
  haveI := submoduleAsSymGroupAlgebra_isSimpleModuleK S'
  -- Classify each restrictScalars module as a Specht module.
  obtain ⟨μ, ⟨eS⟩⟩ := Theorem5_12_2_classification_general k n ↥(S.restrictScalars k)
  obtain ⟨μ', ⟨eS'⟩⟩ := Theorem5_12_2_classification_general k n ↥(S'.restrictScalars k)
  -- Both labels equal `la` by Specht character injectivity.
  have hμ : μ = la := spechtModuleCharacterK_injective k n fun σ =>
    (trace_restrictedSymGroupAction_eq_of_spechtIsoK S μ eS σ).symm.trans (hS σ)
  have hμ' : μ' = la := spechtModuleCharacterK_injective k n fun σ =>
    (trace_restrictedSymGroupAction_eq_of_spechtIsoK S' μ' eS' σ).symm.trans (hS' σ)
  have hμμ' : μ = μ' := hμ.trans hμ'.symm
  subst hμμ'
  exact ⟨transferToSymGroupImageEquivK S S' (eS.trans eS'.symm)⟩

set_option synthInstance.maxHeartbeats 400000 in
-- Elaborating the `IsSimpleModule (↥(symGroupImage …)) ↥S` hypotheses forces synthesis of the
-- `Module ↥(symGroupImage …) ↥S` instance, traversing the deep `Subalgebra → Subsemiring →
-- Module` chain that exceeds the default heartbeats.
/-- `symGroupImage`-wrapper of `simpleSubmodule_iso_of_spechtCharacterK_eq`, matching the
shape of the ℂ wrapper `simpleSymGroupImageSubmodule_iso_of_spechtCharacter_eq` for use by
the general-`k` special-block assembly. -/
theorem simpleSymGroupImageSubmodule_iso_of_spechtCharacterK_eq
    (S S' : Submodule (symGroupImage k (Fin N → k) n)
      (TensorPower k (Fin N → k) n))
    [IsSimpleModule (↥(symGroupImage k (Fin N → k) n)) ↥S]
    [IsSimpleModule (↥(symGroupImage k (Fin N → k) n)) ↥S']
    (la : Nat.Partition n)
    (hS : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S.restrictScalars k)
          ((symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
            (p := S.restrictScalars k) (q := S.restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S σ hv)) =
          spechtModuleCharacterK k n la σ)
    (hS' : ∀ σ : Equiv.Perm (Fin n),
        LinearMap.trace k ↥(S'.restrictScalars k)
          ((symGroupAction k (Fin N → k) n σ).toLinearMap.restrict
            (p := S'.restrictScalars k) (q := S'.restrictScalars k)
            (fun _ hv => symGroupAction_mem_of_symGroupImage_submodule S' σ hv)) =
          spechtModuleCharacterK k n la σ) :
    Nonempty (↥S ≃ₗ[↥(symGroupImage k (Fin N → k) n)] ↥S') :=
  simpleSubmodule_iso_of_spechtCharacterK_eq S S' la hS hS'

end Etingof

end
