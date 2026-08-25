/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.PathAlgebra.VertexComponents
import RepresentationTheory.QuiverAuxiliary
import RepresentationTheory.Quiver.PathAlgebra.LoopQuiver
import RepresentationTheory.RingModuleAuxiliary
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-! # Vertex Simple Auxiliary -/

universe u w

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q] [Fintype Q]

/-! ## The auxiliary map on the vertex idempotents -/

/-- The auxiliary map sends the auxiliary element with the matching index to one. -/
theorem auxiliaryMap_auxiliaryElement (i : Q) :
    auxiliaryRingHom i (auxiliaryVertexIdempotent (k := k) i) = 1 := by
  rw [auxiliaryVertexIdempotent, auxiliaryOfPath, auxiliaryRingHom_apply, auxiliaryLinearMap_single,
    if_pos rfl]

/-- The auxiliary map indexed by a quiver element sends an algebra-mapped field scalar to that scalar. -/
theorem auxiliaryMap_algebraMap (i : Q) (c : k) :
    auxiliaryRingHom i (algebraMap k (AuxiliaryPathType k Q) c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, auxiliaryRingHom_apply, map_smul,
    ← auxiliaryRingHom_apply, map_one, smul_eq_mul, mul_one]

/-- The auxiliary element associated with each quiver index is nonzero. -/
theorem auxiliaryElement_ne_zero (i : Q) :
    (auxiliaryVertexIdempotent i : AuxiliaryPathType k Q) ≠ 0 := by
  intro h
  have h1 : auxiliaryRingHom i (auxiliaryVertexIdempotent (k := k) i) = 1 :=
    auxiliaryMap_auxiliaryElement i
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The displayed auxiliary element of the secondary vertex-indexed type is nonzero. -/
theorem secondaryAuxiliaryElement_ne_zero (i : Q) :
    (auxiliaryVertexElement k Q i : AuxiliaryVertexSpace k Q i) ≠ 0 := fun h =>
  auxiliaryElement_ne_zero i (congrArg Subtype.val h)

/-- The secondary auxiliary type at each quiver index is nontrivial. -/
instance secondaryAuxiliary_nontrivial (i : Q) : Nontrivial (AuxiliaryVertexSpace k Q i) :=
  ⟨⟨auxiliaryVertexElement k Q i, 0, secondaryAuxiliaryElement_ne_zero i⟩⟩

/-- The submodule spanned by the displayed secondary auxiliary element is top. -/
theorem span_secondaryAuxiliaryElement_eq_top (i : Q) :
    Submodule.span (AuxiliaryPathType k Q) {auxiliaryVertexElement k Q i} = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
  exact Submodule.mem_span_singleton.mpr ⟨a, Subtype.ext ha⟩

/-! ## Simplicity of the auxiliary modules -/

/-- The auxiliary module at each quiver index is nontrivial. -/
instance auxiliary_nontrivial (i : Q) : Nontrivial (Auxiliary k Q i) :=
  inferInstanceAs (Nontrivial (ULift.{u + 1} k))

/-- The auxiliary module indexed by any element of the finite quiver is simple. -/
theorem auxiliary_isSimpleModule (i : Q) :
    IsSimpleModule (AuxiliaryPathType k Q) (Auxiliary k Q i) := by
  refine { exists_pair_ne := exists_pair_ne _, eq_bot_or_eq_top := fun N => ?_ }
  rcases eq_or_ne N ⊥ with h | h
  · exact Or.inl h
  refine Or.inr (eq_top_iff.mpr fun w _ => ?_)
  obtain ⟨v, hvN, hv⟩ := (Submodule.ne_bot_iff N).mp h
  have hvd : (v : Auxiliary k Q i).down ≠ 0 := fun hc => hv (by apply ULift.ext; exact hc)
  have hw : (algebraMap k (AuxiliaryPathType k Q) (w.down / v.down)) • v = w := by
    apply ULift.ext
    rw [auxiliary_smul_down, auxiliaryMap_algebraMap, div_mul_cancel₀ _ hvd]
  exact hw ▸ N.smul_mem _ hvN

/-! ## Projectivity of the secondary auxiliary type -/

/-- An auxiliary linear map from the ambient algebra to the secondary vertex-indexed type. -/
noncomputable def toSecondaryAuxiliaryLinearMap (i : Q) :
    AuxiliaryPathType k Q →ₗ[AuxiliaryPathType k Q] AuxiliaryVertexSpace k Q i :=
  LinearMap.codRestrict (Submodule.span (AuxiliaryPathType k Q) {auxiliaryVertexIdempotent (k := k) i})
    (LinearMap.mulRight (AuxiliaryPathType k Q) (auxiliaryVertexIdempotent i))
    (fun a => Submodule.mem_span_singleton.mpr ⟨a, by rw [smul_eq_mul]; rfl⟩)

/-- The value underlying the auxiliary linear map is right multiplication by the auxiliary vertex element. -/
@[simp] theorem toSecondaryAuxiliaryLinearMap_apply (i : Q) (a : AuxiliaryPathType k Q) :
    ((toSecondaryAuxiliaryLinearMap i a : AuxiliaryVertexSpace k Q i) : AuxiliaryPathType k Q) =
      a * auxiliaryVertexIdempotent i := rfl

/-- Each secondary auxiliary type is projective over the ambient scalar type. -/
instance secondaryAuxiliary_projective (i : Q) :
    Module.Projective (AuxiliaryPathType k Q) (AuxiliaryVertexSpace k Q i) :=
  Module.Projective.of_split
    (Submodule.span (AuxiliaryPathType k Q) {auxiliaryVertexIdempotent (k := k) i}).subtype
    (toSecondaryAuxiliaryLinearMap i)
    (LinearMap.ext fun y => Subtype.ext (mul_vertexIdempotent_eq_of_mem_span y.2))

/-! ## The auxiliary predicate for an acyclic quiver -/

omit [DecidableEq Q] [Fintype Q] in
/-- If every loop path is nil, the paths from any quiver element to itself form a subsingleton. -/
theorem path_subsingleton_of_loops_eq_nil
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) (i : Q) :
    Subsingleton (Quiver.Path i i) :=
  ⟨fun p q => by rw [hacyclic i p, hacyclic i q]⟩

/-- If every loop path is nil, the endomorphism space of the secondary auxiliary type has field dimension one. -/
theorem finrank_end_secondaryAuxiliary_eq_one
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) (i : Q) :
    Module.finrank k
        (AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] AuxiliaryVertexSpace k Q i) = 1 := by
  haveI := path_subsingleton_of_loops_eq_nil hacyclic i
  rw [(linearMapEquivPathFinsupp k Q i i).finrank_eq,
    (Finsupp.uniqueLinearEquiv k k (Quiver.Path.nil : Quiver.Path i i)).finrank_eq,
    Module.finrank_self]

/-- The identity linear map on the displayed vertex-indexed type is nonzero. -/
theorem linearMap_id_ne_zero (i : Q) :
    (LinearMap.id : AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q]
      AuxiliaryVertexSpace k Q i) ≠ 0 := by
  intro h
  exact secondaryAuxiliaryElement_ne_zero i
    (by simpa using congrArg (fun f => f (auxiliaryVertexElement k Q i)) h)

/-- If every loop path is nil, the displayed predicate holds for each secondary auxiliary type. -/
theorem auxiliaryPredicate_of_no_nontrivial_loops
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) (i : Q) :
    RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate
      (AuxiliaryPathType k Q) (AuxiliaryVertexSpace k Q i) := by
  refine ⟨inferInstance, fun W₁ W₂ hc => ?_⟩
  set P := W₁.projection W₂ hc with hPdef
  obtain ⟨c, hcP⟩ :=
    (finrank_eq_one_iff_of_nonzero' (LinearMap.id :
        AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] AuxiliaryVertexSpace k Q i)
      (linearMap_id_ne_zero i)).mp (finrank_end_secondaryAuxiliary_eq_one hacyclic i) P
  have hidem : ∀ x, P (P x) = P x := fun x =>
    Submodule.projection_apply_of_mem_left hc (Submodule.projection_apply_mem hc x)
  have hc2 : (c * c) • (LinearMap.id :
      AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] AuxiliaryVertexSpace k Q i) =
      c • LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    have hx := hidem x
    rw [← hcP] at hx
    have hx' : c • (c • x) = c • x := by
      simpa only [LinearMap.smul_apply, LinearMap.id_apply] using hx
    change (c * c) • x = c • x
    exact (SemigroupAction.mul_smul c c x).trans hx'
  have hcc : c * c = c := by
    have h0 : (c * c - c) • (LinearMap.id :
        AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] AuxiliaryVertexSpace k Q i) = 0 := by
      exact (sub_smul (c * c) c (LinearMap.id :
        AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] AuxiliaryVertexSpace k Q i)).trans
          (sub_eq_zero.mpr hc2)
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (linearMap_id_ne_zero i)
  rcases mul_eq_zero.mp (show c * (c - 1) = 0 by linear_combination hcc) with h | h
  · left
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Submodule.mem_bot]
    have hx1 : P x = x := Submodule.projection_apply_of_mem_left hc hx
    rw [← hx1, ← hcP, h, zero_smul, LinearMap.zero_apply]
  · right
    have hc1 : c = 1 := sub_eq_zero.mp h
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Submodule.mem_bot]
    have hx1 : P x = 0 := Submodule.projection_apply_of_mem_right hc hx
    rw [← hcP, hc1, one_smul, LinearMap.id_apply] at hx1
    exact hx1

/-! ## The auxiliary map from the secondary type -/

/-- An auxiliary linear map from the secondary vertex-indexed type to the auxiliary module with the same index. -/
noncomputable def secondaryToAuxiliaryLinearMap (i : Q) :
    AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] Auxiliary k Q i where
  toFun y := ULift.up (auxiliaryRingHom i (y : AuxiliaryPathType k Q))
  map_add' y z := by apply ULift.ext; exact map_add (auxiliaryRingHom i) _ _
  map_smul' a y := by
    apply ULift.ext
    rw [auxiliary_smul_down]
    exact map_mul (auxiliaryRingHom i) a (y : AuxiliaryPathType k Q)

/-- The value underlying the auxiliary linear map agrees with the auxiliary map applied to the underlying input. -/
@[simp] theorem secondaryToAuxiliaryLinearMap_down_apply
    (i : Q) (y : AuxiliaryVertexSpace k Q i) :
    (secondaryToAuxiliaryLinearMap i y).down = auxiliaryRingHom i (y : AuxiliaryPathType k Q) := rfl

/-- The auxiliary linear map sends the displayed secondary element to the displayed auxiliary element. -/
theorem secondaryToAuxiliaryLinearMap_auxiliaryElement (i : Q) :
    secondaryToAuxiliaryLinearMap i (auxiliaryVertexElement k Q i) =
      auxiliary (k := k) (Q := Q) i := by
  apply ULift.ext
  rw [secondaryToAuxiliaryLinearMap_down_apply, coe_auxiliaryVertexElement,
    auxiliaryMap_auxiliaryElement, auxiliary_down]

/-- The auxiliary linear map from the secondary type to the auxiliary module is surjective. -/
theorem secondaryToAuxiliaryLinearMap_surjective (i : Q) :
    Function.Surjective (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i) := by
  intro w
  refine ⟨(algebraMap k (AuxiliaryPathType k Q) w.down) • auxiliaryVertexElement k Q i, ?_⟩
  apply ULift.ext
  rw [secondaryToAuxiliaryLinearMap_down_apply, Submodule.coe_smul,
    coe_auxiliaryVertexElement, smul_eq_mul, map_mul, auxiliaryMap_auxiliaryElement, mul_one,
    auxiliaryMap_algebraMap]

/-- When all loop paths are nil, an element in the indicated singleton span with auxiliary value one is fixed by multiplication with the auxiliary vertex element. -/
theorem auxiliaryElement_mul_eq_self_of_mem_span
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) {i : Q}
    {n : AuxiliaryPathType k Q}
    (hn : n ∈ Submodule.span (AuxiliaryPathType k Q) {auxiliaryVertexIdempotent (k := k) i})
    (haug : auxiliaryRingHom i n = 1) :
    auxiliaryVertexIdempotent i * n = auxiliaryVertexIdempotent i := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
  rw [smul_eq_mul] at haug ⊢
  refine ext fun x => ?_
  by_cases hx : x = (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q)
  · subst hx
    rw [coeff_vertexIdempotent_mul, if_pos rfl, auxiliaryVertexIdempotent, auxiliaryOfPath,
      coeff_single, if_pos rfl]
    exact haug
  · have hcut : auxiliaryVertexIdempotent i * (a * auxiliaryVertexIdempotent i) ∈
        pathComponent k Q i i :=
      mem_pathComponent_iff.mpr ⟨a, by rw [mul_assoc]⟩
    rw [coeff_eq_zero_of_mem_pathComponent hcut ?_, auxiliaryVertexIdempotent, auxiliaryOfPath,
      coeff_single, if_neg (Ne.symm hx)]
    rintro ⟨h1, h2⟩
    refine hx ?_
    obtain ⟨s, t, p⟩ := x
    cases h1
    cases h2
    rw [hacyclic _ p]

/-- If every loop path is nil, a submodule whose supremum with the kernel of the auxiliary map is top must itself be top. -/
theorem eq_top_of_sup_ker_secondaryToAuxiliary_eq_top
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) (i : Q)
    (N : Submodule (AuxiliaryPathType k Q) (AuxiliaryVertexSpace k Q i))
    (hN : N ⊔ LinearMap.ker (secondaryToAuxiliaryLinearMap i) = ⊤) : N = ⊤ := by
  have hmem : auxiliaryVertexElement k Q i ∈
      N ⊔ LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i) := by
    rw [hN]; exact Submodule.mem_top
  obtain ⟨n, hn, r, hr, hnr⟩ := Submodule.mem_sup.mp hmem
  have haug : auxiliaryRingHom i (n : AuxiliaryPathType k Q) = 1 := by
    have h1 : secondaryToAuxiliaryLinearMap i n + secondaryToAuxiliaryLinearMap i r =
        auxiliary (k := k) (Q := Q) i := by
      rw [← map_add, hnr, secondaryToAuxiliaryLinearMap_auxiliaryElement]
    rw [LinearMap.mem_ker.mp hr, add_zero] at h1
    simpa using congrArg ULift.down h1
  have hgen : (auxiliaryVertexIdempotent i : AuxiliaryPathType k Q) • n =
      auxiliaryVertexElement k Q i :=
    Subtype.ext (auxiliaryElement_mul_eq_self_of_mem_span hacyclic n.2 haug)
  have : auxiliaryVertexElement k Q i ∈ N := hgen ▸ N.smul_mem _ hn
  rw [eq_top_iff, ← span_secondaryAuxiliaryElement_eq_top i, Submodule.span_le,
    Set.singleton_subset_iff]
  exact this

/-- An auxiliary structure on each vertex-indexed auxiliary module when every loop path is nil. -/
noncomputable def auxiliaryStructureOfNoNontrivialLoops
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) (i : Q) :
    RepresentationTheory.RingModuleAuxiliary.Auxiliary
      (AuxiliaryPathType k Q) (Auxiliary k Q i) where
  Carrier := AuxiliaryVertexSpace k Q i
  auxiliaryProperty := auxiliaryPredicate_of_no_nontrivial_loops hacyclic i
  toLinearMap := secondaryToAuxiliaryLinearMap i
  surjective_toLinearMap := secondaryToAuxiliaryLinearMap_surjective i
  eq_top_of_sup_kernel_eq_top := eq_top_of_sup_ker_secondaryToAuxiliary_eq_top hacyclic i

/-! ## The auxiliary modules exhaust the simple modules -/

/-- The sum of the auxiliary elements over all quiver indices is one. -/
theorem sum_auxiliaryElement_eq_one :
    (∑ i : Q, (auxiliaryVertexIdempotent i : AuxiliaryPathType k Q)) = 1 :=
  sum_vertexPath_eq_one k Q

/-- At a different index, the auxiliary map sends the auxiliary element to zero. -/
theorem auxiliaryMap_auxiliaryElement_of_ne {i j : Q} (h : i ≠ j) :
    auxiliaryRingHom j (auxiliaryVertexIdempotent (k := k) i) = 0 := by
  rw [auxiliaryVertexIdempotent, auxiliaryOfPath, auxiliaryRingHom_apply, auxiliaryLinearMap_single,
    if_neg]
  intro hc
  exact h (congrArg Sigma.fst hc)

/-- Auxiliary modules at distinct quiver indices admit no linear equivalence. -/
theorem not_linearEquiv_auxiliary_of_ne {i j : Q} (h : i ≠ j)
    (e : Auxiliary k Q i ≃ₗ[AuxiliaryPathType k Q] Auxiliary k Q j) : False := by
  have h1 : (auxiliaryVertexIdempotent i : AuxiliaryPathType k Q) •
      auxiliary (k := k) (Q := Q) i = auxiliary i := by
    apply ULift.ext
    rw [auxiliary_smul_down, auxiliaryMap_auxiliaryElement, one_mul]
  have h2 : (auxiliaryVertexIdempotent i : AuxiliaryPathType k Q) •
      e (auxiliary (k := k) (Q := Q) i) = 0 := by
    apply ULift.ext
    rw [auxiliary_smul_down, auxiliaryMap_auxiliaryElement_of_ne h, zero_mul]
    rfl
  rw [← map_smul, h1] at h2
  have h3 : auxiliary (k := k) (Q := Q) i = 0 := e.injective (h2.trans (map_zero e).symm)
  exact one_ne_zero (congrArg ULift.down h3)

/-- If every loop path is nil, every simple module is linearly equivalent to an auxiliary module at some quiver index. -/
theorem exists_linearEquiv_auxiliary
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil)
    (M : Type w) [AddCommGroup M] [Module (AuxiliaryPathType k Q) M]
    [IsSimpleModule (AuxiliaryPathType k Q) M] :
    ∃ i : Q, Nonempty (M ≃ₗ[AuxiliaryPathType k Q] Auxiliary k Q i) := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (AuxiliaryPathType k Q) M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨i, hi⟩ : ∃ i : Q, (auxiliaryVertexIdempotent (k := k) i : AuxiliaryPathType k Q) • m ≠ 0 := by
    by_contra hcon
    refine hm ?_
    have h0 : (∑ i : Q, (auxiliaryVertexIdempotent (k := k) i : AuxiliaryPathType k Q)) • m = 0 := by
      rw [Finset.sum_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_contra hne
      exact hcon ⟨j, hne⟩
    rwa [sum_auxiliaryElement_eq_one, one_smul] at h0
  set f : AuxiliaryVertexSpace k Q i →ₗ[AuxiliaryPathType k Q] M :=
    { toFun := fun y => (y : AuxiliaryPathType k Q) • m
      map_add' := fun y z => by rw [Submodule.coe_add, add_smul]
      map_smul' := fun a y => by
        rw [RingHom.id_apply, Submodule.coe_smul, smul_eq_mul]
        exact SemigroupAction.mul_smul a (y : AuxiliaryPathType k Q) m } with hfdef
  have hfne : f (auxiliaryVertexElement k Q i) ≠ 0 := hi
  have hfsurj : Function.Surjective f := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range f) with h | h
    · refine absurd ?_ hfne
      have hmem : f (auxiliaryVertexElement k Q i) ∈ LinearMap.range f :=
        LinearMap.mem_range_self f _
      rw [h, Submodule.mem_bot] at hmem
      exact hmem
    · exact LinearMap.range_eq_top.mp h
  have hker : LinearMap.ker f ≤ LinearMap.ker (secondaryToAuxiliaryLinearMap i) := by
    by_contra hcon
    obtain ⟨y, hyf, hyp⟩ := SetLike.not_le_iff_exists.mp hcon
    have hyp' : secondaryToAuxiliaryLinearMap i y ≠ 0 := fun hc =>
      hyp (LinearMap.mem_ker.mpr hc)
    haveI := auxiliary_isSimpleModule (k := k) (Q := Q) i
    have hspan : Submodule.span (AuxiliaryPathType k Q) {secondaryToAuxiliaryLinearMap i y} = ⊤ := by
      rcases IsSimpleOrder.eq_bot_or_eq_top
        (Submodule.span (AuxiliaryPathType k Q) {secondaryToAuxiliaryLinearMap i y}) with h | h
      · refine absurd ?_ hyp'
        have hmem := Submodule.mem_span_singleton_self (R := AuxiliaryPathType k Q)
          (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i y)
        rw [h, Submodule.mem_bot] at hmem
        exact hmem
      · exact h
    have htop : LinearMap.ker f ⊔ LinearMap.ker (secondaryToAuxiliaryLinearMap i) = ⊤ := by
      refine eq_top_iff.mpr fun z _ => ?_
      have hz : secondaryToAuxiliaryLinearMap i z ∈
          Submodule.span (AuxiliaryPathType k Q) {secondaryToAuxiliaryLinearMap i y} := by
        rw [hspan]; exact Submodule.mem_top
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hz
      have h1 : a • y ∈ LinearMap.ker f := (LinearMap.ker f).smul_mem a hyf
      have h2 : z - a • y ∈ LinearMap.ker (secondaryToAuxiliaryLinearMap i) := by
        rw [LinearMap.mem_ker, map_sub, map_smul, ha, sub_self]
      simpa using Submodule.add_mem_sup h1 h2
    have hfull := eq_top_of_sup_ker_secondaryToAuxiliary_eq_top hacyclic i
      (LinearMap.ker f) htop
    refine hfne ?_
    have hgen : auxiliaryVertexElement k Q i ∈ LinearMap.ker f := by
      rw [hfull]; exact Submodule.mem_top
    exact LinearMap.mem_ker.mp hgen
  have hkereq : LinearMap.ker f = LinearMap.ker (secondaryToAuxiliaryLinearMap i) := by
    refine le_antisymm hker ?_
    rcases IsSimpleOrder.eq_bot_or_eq_top
      (Submodule.map f (LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i))) with h | h
    · intro z hz
      have hfz : f z ∈ Submodule.map f
          (LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i)) :=
        Submodule.mem_map_of_mem hz
      rw [h, Submodule.mem_bot] at hfz
      exact LinearMap.mem_ker.mpr hfz
    · exfalso
      have hpitop : LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i) = ⊤ := by
        refine eq_top_iff.mpr fun z _ => ?_
        have hz : f z ∈ Submodule.map f
            (LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i)) := by
          rw [h]; exact Submodule.mem_top
        obtain ⟨y, hy, hfy⟩ := hz
        have hzy : z - y ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, map_sub, hfy, sub_self]
        have hzy' : z - y ∈
            LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i) := hker hzy
        have hsplit : z = (z - y) + y := by abel
        rw [hsplit]
        exact (LinearMap.ker _).add_mem hzy' hy
      obtain ⟨y, hy⟩ := secondaryToAuxiliaryLinearMap_surjective (k := k) (Q := Q) i
        (auxiliary i)
      have hyk : y ∈ LinearMap.ker (secondaryToAuxiliaryLinearMap (k := k) (Q := Q) i) := by
        rw [hpitop]; exact Submodule.mem_top
      have hzero : secondaryToAuxiliaryLinearMap i y = 0 := LinearMap.mem_ker.mp hyk
      rw [hy] at hzero
      exact one_ne_zero (congrArg ULift.down hzero)
  exact ⟨i, ⟨((f.quotKerEquivOfSurjective hfsurj).symm.trans
    (Submodule.quotEquivOfEq _ _ hkereq)).trans
    ((secondaryToAuxiliaryLinearMap i).quotKerEquivOfSurjective
      (secondaryToAuxiliaryLinearMap_surjective i))⟩⟩

/-- The displayed value of the auxiliary structure is the corresponding secondary auxiliary type. -/
theorem auxiliaryStructure_value
    (hacyclic : ∀ (v : Q) (p : Quiver.Path v v), p = Quiver.Path.nil) (i : Q) :
    (auxiliaryStructureOfNoNontrivialLoops (k := k) hacyclic i).Carrier =
      AuxiliaryVertexSpace k Q i := rfl

end RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType

namespace RepresentationTheory.VertexSimpleAuxiliary

open RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
open RepresentationTheory.Quiver.PathAlgebra.LoopQuiver

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [Fintype Q] [DecidableEq Q]

/-- For a finite quiver with only nil loop paths and finite hom types, the displayed simplicity, classification, auxiliary identification, and family equality all hold. -/
theorem auxiliaryResults_of_no_nontrivial_loops
    (hacyclic : ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil)
    [∀ i j : Q, Finite (i ⟶ j)] :
    (∀ i : Q, IsSimpleModule
      (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) (Auxiliary k Q i)) ∧
      (∀ i j : Q, Nonempty
        (Auxiliary k Q i ≃ₗ[_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q]
          Auxiliary k Q j) → i = j) ∧
      (∀ (M : Type w) [AddCommGroup M]
          [Module (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) M]
          [IsSimpleModule (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q) M],
        ∃ i : Q, Nonempty
          (M ≃ₗ[_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q]
            Auxiliary k Q i)) ∧
      (∀ i : Q, (auxiliaryStructureOfNoNontrivialLoops (k := k) hacyclic i).Carrier =
        AuxiliaryVertexSpace k Q i) ∧
      RepresentationTheory.ModuleFamilyNatMatrix.ModuleFamilyNatMatrix.matrix
        (k := k)
        (A := _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType k Q)
        (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.AuxiliaryVertexSpace
          k Q) = quiverNatMatrix Q :=
  ⟨fun i => auxiliary_isSimpleModule i,
    fun i j ⟨e⟩ => by
      by_contra hne
      exact not_linearEquiv_auxiliary_of_ne hne e,
    fun M => exists_linearEquiv_auxiliary hacyclic M,
    fun _ => rfl,
    specializedAssociatedMatrix_eq_quiverNatMatrix hacyclic⟩

end RepresentationTheory.VertexSimpleAuxiliary
