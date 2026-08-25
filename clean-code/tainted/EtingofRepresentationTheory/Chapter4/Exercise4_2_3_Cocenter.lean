import Mathlib

/-!
# Cocenter of a finite group algebra (Exercise 4.2.3)

This file computes the dimension of the **cocenter**
`C = k[G] / [k[G], k[G]]` of a finite group algebra:

  `Module.finrank k C = Nat.card (ConjClasses G)`.

The result holds over an arbitrary field: only `[Field k]` is assumed, with no `IsAlgClosed`
and no invertibility of `|G|`. This is dual to the center computation
`finrank_center_monoidAlgebra` in `Chapter4/Corollary4_2_2.lean` (which shows
`finrank_k Z(k[G]) = #ConjClasses` via class sums). It is one ingredient of the counting
bound `#(simple k[G]-modules) ≤ Nat.card (ConjClasses G)`; the remaining ingredients are the
trace form on the cocenter and the linear-independence argument giving the bound.

## Proof strategy

The cocenter's linear dual is the space of trace-like (class) functionals, and the
images of conjugacy-class representatives form a `k`-basis of `C`. We prove the
dimension by squeezing between two bounds, each obtained from a surjective linear map:

* **Lower bound.** The *class-coefficient* map
  `φ : k[G] → (ConjClasses G → k)`, sending `single g c` to `c • Pi.single (mk g) 1`
  (equivalently, `φ a C' = ∑_{g ∈ C'} a g`), is a "trace": `φ (x*y) = φ (y*x)`. Hence
  it kills the commutator submodule and descends to a **surjection**
  `C ↠ (ConjClasses G → k)`, giving `#ConjClasses ≤ finrank C`.
* **Upper bound.** The images `[single (out C') 1]` of conjugacy-class representatives
  **span** `C` (conjugate group elements have equal image in `C`), so `#ConjClasses`
  of them suffice, giving `finrank C ≤ #ConjClasses`.
-/

open MonoidAlgebra

namespace Etingof

namespace CocenterMonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Fintype G] [DecidableEq G]

variable (k G) in
/-- The commutator submodule `[k[G], k[G]]`: the `k`-span of all `x*y - y*x`. -/
noncomputable def commSubmodule : Submodule k (MonoidAlgebra k G) :=
  Submodule.span k (Set.range (fun p : MonoidAlgebra k G × MonoidAlgebra k G =>
    p.1 * p.2 - p.2 * p.1))

variable (k G) in
/-- The **cocenter** `C = k[G] / [k[G], k[G]]` of the group algebra. -/
noncomputable abbrev Cocenter : Type _ := MonoidAlgebra k G ⧸ commSubmodule k G

/-! ### The class-coefficient map `φ : k[G] → (ConjClasses G → k)` -/

variable (k G) in
/-- The **class-coefficient map**: `φ a C'` is the sum of the coefficients of `a` over the
conjugacy class `C'`. On a basis element, `φ (single g c) C' = if mk g = C' then c else 0`. -/
noncomputable def classCoeff : MonoidAlgebra k G →ₗ[k] (ConjClasses G → k) where
  toFun a := fun C' => ∑ g : G, if ConjClasses.mk g = C' then a.coeff g else 0
  map_add' a b := by
    funext C'
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun g _ => by
      rw [show (a + b).coeff g = a.coeff g + b.coeff g from rfl]; split <;> simp
  map_smul' r a := by
    funext C'
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [show (r • a).coeff g = r • a.coeff g from rfl, smul_eq_mul]; split <;> simp

lemma classCoeff_single (g : G) (c : k) :
    classCoeff k G (single g c) = fun C' => if ConjClasses.mk g = C' then c else 0 := by
  funext C'
  simp only [classCoeff, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single g]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl]
  · intro b _ hbg
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hbg), ite_self]
  · intro hg; exact absurd (Finset.mem_univ g) hg

/-- The class-coefficient map is a trace: `φ (x*y) = φ (y*x)`. This is the algebraic
heart of the descent to the cocenter. -/
lemma classCoeff_mul_comm (x y : MonoidAlgebra k G) :
    classCoeff k G (x * y) = classCoeff k G (y * x) := by
  induction x using MonoidAlgebra.induction_on with
  | hM g =>
    induction y using MonoidAlgebra.induction_on with
    | hM h =>
      rw [of_apply, of_apply, single_mul_single, single_mul_single,
        classCoeff_single, classCoeff_single,
        show ConjClasses.mk (g * h) = ConjClasses.mk (h * g) from
          ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)]
    | hadd y₁ y₂ h₁ h₂ => rw [mul_add, add_mul, map_add, map_add, h₁, h₂]
    | hsmul r y h => rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_smul, map_smul, h]
  | hadd x₁ x₂ h₁ h₂ => rw [add_mul, mul_add, map_add, map_add, h₁, h₂]
  | hsmul r x h => rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul, map_smul, h]

lemma commSubmodule_le_ker : commSubmodule k G ≤ LinearMap.ker (classCoeff k G) := by
  rw [commSubmodule, Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, classCoeff_mul_comm x y, sub_self]

/-- The class-coefficient map is surjective: it hits every indicator `Pi.single C' 1`. -/
lemma classCoeff_surjective : Function.Surjective (classCoeff k G) := by
  have hmk : ∀ C' : ConjClasses G, ConjClasses.mk (Quotient.out C') = C' := fun C' => by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  intro f
  refine ⟨∑ C' : ConjClasses G, f C' • single (Quotient.out C') 1, ?_⟩
  funext D
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, classCoeff_single, hmk, Pi.smul_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ D f]
  simp

variable (k G) in
/-- The descent of the class-coefficient map to the cocenter `C = k[G] / [k[G], k[G]]`. -/
noncomputable def classCoeffQ : Cocenter k G →ₗ[k] (ConjClasses G → k) :=
  Submodule.liftQ (commSubmodule k G) (classCoeff k G) commSubmodule_le_ker

lemma classCoeffQ_surjective : Function.Surjective (classCoeffQ k G) := by
  intro f
  obtain ⟨a, ha⟩ := classCoeff_surjective f
  exact ⟨Submodule.Quotient.mk a, by rw [classCoeffQ, Submodule.liftQ_apply, ha]⟩

/-! ### The spanning family of conjugacy-class representatives -/

variable (k G) in
/-- The image `[single (out C') 1]` in the cocenter of a representative of the conjugacy
class `C'`. These span the cocenter. -/
noncomputable def classRep : ConjClasses G → Cocenter k G :=
  fun C' => Submodule.mkQ (commSubmodule k G) (single (Quotient.out C') 1)

omit [Fintype G] [DecidableEq G] in
/-- If `a` and `b` are conjugate, then `single a 1 - single b 1` lies in the commutator
submodule. Indeed `b = c a c⁻¹` gives `single a 1 - single b 1 =
single c⁻¹ 1 * single (c*a) 1 - single (c*a) 1 * single c⁻¹ 1`. -/
lemma single_sub_single_conj_mem {a b : G} (h : IsConj a b) :
    single a (1 : k) - single b 1 ∈ commSubmodule k G := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hrw : single (c⁻¹) (1 : k) * single (c * a) 1 - single (c * a) 1 * single (c⁻¹) 1
      = single a 1 - single b 1 := by
    rw [single_mul_single, single_mul_single, one_mul,
      show c⁻¹ * (c * a) = a by group, show c * a * c⁻¹ = b from hc]
  rw [← hrw]
  exact Submodule.subset_span ⟨(single (c⁻¹) 1, single (c * a) 1), rfl⟩

omit [Fintype G] [DecidableEq G] in
/-- The image of `single g 1` in the cocenter equals the class representative `classRep (mk g)`. -/
lemma mkQ_single_eq_classRep (g : G) :
    Submodule.mkQ (commSubmodule k G) (single g 1) = classRep k G (ConjClasses.mk g) := by
  have hmk : ConjClasses.mk (Quotient.out (ConjClasses.mk g)) = ConjClasses.mk g := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  rw [classRep, ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact single_sub_single_conj_mem (ConjClasses.mk_eq_mk_iff_isConj.mp hmk.symm)

omit [Fintype G] [DecidableEq G] in
/-- The elements `single g 1` span the whole group algebra `k[G]`. -/
lemma span_range_single_eq_top :
    Submodule.span k (Set.range (fun g : G => (single g 1 : MonoidAlgebra k G))) = ⊤ := by
  rw [eq_top_iff]
  rintro a -
  induction a using MonoidAlgebra.induction_on with
  | hM g => exact Submodule.subset_span ⟨g, rfl⟩
  | hadd x y hx hy => exact Submodule.add_mem _ hx hy
  | hsmul r x hx => exact Submodule.smul_mem _ r hx

omit [Fintype G] [DecidableEq G] in
/-- The class representatives span the cocenter. -/
lemma span_range_classRep_eq_top :
    Submodule.span k (Set.range (classRep k G)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← Submodule.range_mkQ (commSubmodule k G), LinearMap.range_eq_map,
    ← span_range_single_eq_top, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mkQ_single_eq_classRep g]
  exact Submodule.subset_span ⟨ConjClasses.mk g, rfl⟩

/-! ### The dimension of the cocenter -/

noncomputable instance : Module.Finite k (MonoidAlgebra k G) :=
  Module.Finite.of_basis (MonoidAlgebra.basis G k)

noncomputable instance : Module.Finite k (Cocenter k G) :=
  Module.Finite.of_surjective (Submodule.mkQ (commSubmodule k G)) (Submodule.mkQ_surjective _)

/-- **Cocenter dimension (Exercise 4.2.3).** The cocenter
`C = k[G] / [k[G], k[G]]` of a finite group algebra has `finrank` equal to the number
of conjugacy classes of `G`. Holds over an arbitrary field: no `IsAlgClosed`, no
invertibility of `|G|`. -/
theorem finrank_cocenter_eq_card_conjClasses :
    Module.finrank k (Cocenter k G) = Nat.card (ConjClasses G) := by
  have hle1 : Fintype.card (ConjClasses G) ≤ Module.finrank k (Cocenter k G) := by
    have h := LinearMap.finrank_le_finrank_of_surjective (classCoeffQ_surjective (k := k) (G := G))
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hle2 : Module.finrank k (Cocenter k G) ≤ Fintype.card (ConjClasses G) := by
    have hv := finrank_range_le_card (R := k) (classRep k G)
    have heq : (Set.range (classRep k G)).finrank k = Module.finrank k (Cocenter k G) := by
      change Module.finrank k (Submodule.span k (Set.range (classRep k G))) = _
      rw [span_range_classRep_eq_top, finrank_top]
    rwa [heq] at hv
  rw [le_antisymm hle2 hle1, Nat.card_eq_fintype_card]

/-! ### The trace form of a finite-dimensional `k[G]`-module

A finite-dimensional `k[G]`-module `M` carries a **trace functional** `k[G] →ₗ[k] k`,
`x ↦ trace(x acting on M)`. Because `trace(a*b) = trace(b*a)`, this functional kills the
commutator submodule and hence descends to a linear functional `τ_M : C →ₗ[k] k` on the
cocenter. Evaluated on a class representative `[single g 1]` it returns the character value
`χ_M(g) = trace(g acting on M)`.

Together with the dimension formula (`finrank_cocenter_eq_card_conjClasses`) these trace forms
are the tool for the counting bound: the trace forms of the distinct simple `k[G]`-modules are
linearly independent functionals on `C`, so their number is at most `finrank C = #ConjClasses`.
-/

section TraceForm

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M] [Module.Finite k M]

-- The trace form and its descent never use finiteness of `G`; omit those instances so the
-- statements stay clean (they are still available in scope from the file-level variables).
omit [Fintype G] [DecidableEq G]

variable (k) in
/-- The action of the group algebra `k[G]` on a `k[G]`-module `M`, packaged as the
`k`-algebra map `k[G] →ₐ[k] Module.End k M`. This is `Algebra.lsmul`, i.e. `x ↦ (x • ·)`. -/
noncomputable def moduleEnd : MonoidAlgebra k G →ₐ[k] Module.End k M :=
  Algebra.lsmul k k M

omit [Module.Finite k M] in
@[simp] lemma moduleEnd_apply (x : MonoidAlgebra k G) (m : M) :
    moduleEnd k M x m = x • m := rfl

variable (k) in
/-- The **trace functional** of a finite-dimensional `k[G]`-module `M`, sending an element
`x ∈ k[G]` to the trace of its action on `M`. -/
noncomputable def traceForm : MonoidAlgebra k G →ₗ[k] k :=
  (LinearMap.trace k M).comp (moduleEnd k M).toLinearMap

omit [Module.Finite k M] in
lemma traceForm_apply (x : MonoidAlgebra k G) :
    traceForm k M x = LinearMap.trace k M (moduleEnd k M x) := rfl

omit [Module.Finite k M] in
/-- The trace functional is a trace: it is invariant under transposing a product, since
`trace(a*b) = trace(b*a)` (`LinearMap.trace_mul_comm`). -/
lemma traceForm_mul_comm (x y : MonoidAlgebra k G) :
    traceForm k M (x * y) = traceForm k M (y * x) := by
  simp only [traceForm_apply, map_mul]
  exact LinearMap.trace_mul_comm k _ _

omit [Module.Finite k M] in
/-- The trace functional vanishes on the commutator submodule `[k[G], k[G]]`. -/
lemma commSubmodule_le_ker_traceForm :
    commSubmodule k G ≤ LinearMap.ker (traceForm k M) := by
  rw [commSubmodule, Submodule.span_le]
  rintro _ ⟨⟨x, y⟩, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, traceForm_mul_comm M x y, sub_self]

variable (k) in
/-- The **cocenter trace functional** `τ_M : C →ₗ[k] k`: the descent of the trace form of a
finite-dimensional `k[G]`-module `M` to the cocenter `C = k[G] / [k[G], k[G]]`, via
`Submodule.liftQ` using that the trace form kills the commutator submodule. -/
noncomputable def traceFormQ : Cocenter k G →ₗ[k] k :=
  Submodule.liftQ (commSubmodule k G) (traceForm k M) (commSubmodule_le_ker_traceForm M)

omit [Module.Finite k M] in
@[simp] lemma traceFormQ_mkQ (x : MonoidAlgebra k G) :
    traceFormQ k M (Submodule.mkQ (commSubmodule k G) x) = traceForm k M x :=
  Submodule.liftQ_apply _ _ _

omit [Module.Finite k M] in
/-- The cocenter trace functional `τ_M` evaluated on the class of `single g 1` is the trace of
the action of `g` on `M`, i.e. the character value `χ_M(g)`. -/
lemma traceFormQ_mkQ_single (g : G) :
    traceFormQ k M (Submodule.mkQ (commSubmodule k G) (single g 1)) =
      LinearMap.trace k M (moduleEnd k M (single g (1 : k))) := by
  rw [traceFormQ_mkQ, traceForm_apply]

omit [Module.Finite k M] in
/-- The cocenter trace functional evaluated on the class representative `classRep (mk g)` is
the character value `χ_M(g) = trace(g acting on M)`. -/
lemma traceFormQ_classRep (g : G) :
    traceFormQ k M (classRep k G (ConjClasses.mk g)) =
      LinearMap.trace k M (moduleEnd k M (single g (1 : k))) := by
  rw [← mkQ_single_eq_classRep, traceFormQ_mkQ_single]

end TraceForm

end CocenterMonoidAlgebra

end Etingof
