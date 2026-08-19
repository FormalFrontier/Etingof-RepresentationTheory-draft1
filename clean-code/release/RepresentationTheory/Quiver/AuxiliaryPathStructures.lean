/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.LinearAlgebra.Finsupp.LSum
import RepresentationTheory.Alignment.Attribute

/-! # Auxiliary path structures -/

namespace RepresentationTheory.Quiver.AuxiliaryPathStructures

/-- An auxiliary type associated with paths in a quiver. -/
abbrev Quiver.AuxiliaryBundledPathType (Q : Type*) [Quiver Q] : Type _ :=
  Σ (a : Q) (b : Q), Quiver.Path a b

namespace Quiver.AuxiliaryBundledPathType

variable {Q : Type*} [Quiver Q] [DecidableEq Q]

/-- Composition of bundled paths, returning no result when their intermediate vertices differ. -/
noncomputable def compose : Quiver.AuxiliaryBundledPathType Q → Quiver.AuxiliaryBundledPathType Q → Option (Quiver.AuxiliaryBundledPathType Q)
  | ⟨a, b, p⟩, ⟨c, d, q⟩ =>
    if h : b = c then some ⟨a, d, p.comp (h ▸ q)⟩ else none

/-- Composable bundled paths compose to the bundled concatenated path. -/
theorem compose_eq_some {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    compose (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) ⟨b, d, q⟩ = some ⟨a, d, p.comp q⟩ := by
  simp [compose]

/-- Bundled paths with unequal intermediate vertices do not compose. -/
theorem compose_eq_none {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d) (h : b ≠ c) :
    compose (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) ⟨c, d, q⟩ = none := by
  simp only [compose, dif_neg h]

end Quiver.AuxiliaryBundledPathType

/-- An auxiliary type associated with a field and a quiver. -/
def Quiver.AuxiliaryPathType (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  Quiver.AuxiliaryBundledPathType Q →₀ k

namespace Quiver.AuxiliaryPathType

section Instances
variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

/-- The additive commutative group structure on the auxiliary type. -/
noncomputable instance instAddCommGroup : AddCommGroup (Quiver.AuxiliaryPathType k Q) :=
  inferInstanceAs (AddCommGroup (Quiver.AuxiliaryBundledPathType Q →₀ k))

/-- The scalar module structure on the auxiliary type. -/
noncomputable instance instModule : Module k (Quiver.AuxiliaryPathType k Q) :=
  inferInstanceAs (Module k (Quiver.AuxiliaryBundledPathType Q →₀ k))

/-- The canonical inhabited structure on the auxiliary type. -/
instance instInhabited : Inhabited (Quiver.AuxiliaryPathType k Q) :=
  inferInstanceAs (Inhabited (Quiver.AuxiliaryBundledPathType Q →₀ k))

end Instances

variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

variable {k Q}

/-- The auxiliary basis element represented by a bundled quiver path. -/
noncomputable def auxiliaryOfPath (x : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q :=
  Finsupp.single x 1

omit [DecidableEq Q] in
/-- Scaling an auxiliary basis vector with coefficient one replaces its coefficient by the scalar. -/
theorem smul_single_one (c : k) (x : Quiver.AuxiliaryBundledPathType Q) :
    c • Finsupp.single x (1 : k) = Finsupp.single x c := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- A scalar multiple of the zero auxiliary element is zero. -/
theorem smul_zero (c : k) : c • (0 : Quiver.AuxiliaryPathType k Q) = 0 :=
  (_root_.smul_zero c : c • (0 : Quiver.AuxiliaryBundledPathType Q →₀ k) = 0)

/-- The auxiliary product of two quiver paths is a basis vector when they compose and zero otherwise. -/
noncomputable def auxiliaryProduct (x y : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q :=
  (x.compose y).elim 0 (fun z => Finsupp.single z (1 : k))

/-- The auxiliary product attached to two composable paths is the basis vector of their composite. -/
theorem auxiliaryProduct_of_composable {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    auxiliaryProduct (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) ⟨b, d, q⟩
      = Finsupp.single (⟨a, d, p.comp q⟩ : Quiver.AuxiliaryBundledPathType Q) (1 : k) := by
  rw [auxiliaryProduct, _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType.compose_eq_some]; rfl

/-- The auxiliary product attached to paths with unequal intermediate vertices is zero. -/
theorem auxiliaryProduct_of_not_composable {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (h : b ≠ c) :
    auxiliaryProduct (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) ⟨c, d, q⟩ = (0 : Quiver.AuxiliaryPathType k Q) := by
  rw [auxiliaryProduct, _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryBundledPathType.compose_eq_none _ _ h]; rfl

/-- The auxiliary product by a length-zero path on the left selects paths with the matching source vertex. -/
theorem auxiliaryProduct_vertexPath (i a b : Q) (p : Quiver.Path a b) :
    auxiliaryProduct (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) ⟨a, b, p⟩
      = if i = a then Finsupp.single (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) (1 : k) else 0 := by
  by_cases h : i = a
  · subst h
    rw [auxiliaryProduct_of_composable, Quiver.Path.nil_comp, if_pos rfl]
  · rw [if_neg h]; exact auxiliaryProduct_of_not_composable _ _ h

/-- The auxiliary product by a length-zero path on the right selects paths with the matching target vertex. -/
theorem auxiliaryProduct_pathVertex (i a b : Q) (p : Quiver.Path a b) :
    auxiliaryProduct (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) ⟨i, i, Quiver.Path.nil⟩
      = if b = i then Finsupp.single (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) (1 : k) else 0 := by
  by_cases h : b = i
  · subst h
    rw [auxiliaryProduct_of_composable, Quiver.Path.comp_nil, if_pos rfl]
  · rw [if_neg h]; exact auxiliaryProduct_of_not_composable _ _ h

variable (k Q)

/-- Auxiliary multiplication expressed as a linear map into linear maps. -/
noncomputable def auxiliaryMulLinearMap :
    (Quiver.AuxiliaryBundledPathType Q →₀ k) →ₗ[k] (Quiver.AuxiliaryBundledPathType Q →₀ k) →ₗ[k] Quiver.AuxiliaryPathType k Q :=
  Finsupp.lsum k fun x =>
    (LinearMap.id : k →ₗ[k] k).smulRight
      (Finsupp.lsum k fun y => (LinearMap.id : k →ₗ[k] k).smulRight (auxiliaryProduct x y))

/-- The distributive multiplication structure on the auxiliary type before associativity and a unit are installed. -/
noncomputable instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (Quiver.AuxiliaryPathType k Q) :=
  { (inferInstance : AddCommGroup (Quiver.AuxiliaryPathType k Q)) with
    mul := fun f g => auxiliaryMulLinearMap k Q f g

    left_distrib := fun a b c => map_add (auxiliaryMulLinearMap k Q a) b c
    right_distrib := fun a b c =>
      (LinearMap.congr_fun (map_add (auxiliaryMulLinearMap k Q) a b) c).trans (LinearMap.add_apply _ _ _)
    zero_mul := fun a =>
      (LinearMap.congr_fun (map_zero (auxiliaryMulLinearMap k Q)) a).trans (LinearMap.zero_apply a)
    mul_zero := fun a => map_zero (auxiliaryMulLinearMap k Q a) }

variable {k Q}

/-- The auxiliary product agrees with the bilinear multiplication map. -/
theorem mul_eq_auxiliaryMulLinearMap (f g : Quiver.AuxiliaryPathType k Q) : f * g = auxiliaryMulLinearMap k Q f g := rfl

/-- The product of two weighted auxiliary basis vectors is their coefficient product times the auxiliary product. -/
theorem single_mul_single (x y : Quiver.AuxiliaryBundledPathType Q) (a b : k) :
    (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
        (Finsupp.single x a) (Finsupp.single y b))
      = (a * b) • auxiliaryProduct x y := by
  rw [mul_eq_auxiliaryMulLinearMap, auxiliaryMulLinearMap]
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq,
    LinearMap.smul_apply, smul_smul]

/-- Scalar multiplication in the left factor commutes with auxiliary multiplication. -/
theorem smul_mul (r : k) (a b : Quiver.AuxiliaryPathType k Q) : (r • a) * b = r • (a * b) :=
  (LinearMap.congr_fun (map_smul (auxiliaryMulLinearMap k Q) r a) b).trans (LinearMap.smul_apply r _ b)

/-- Scalar multiplication in the right factor commutes with auxiliary multiplication. -/
theorem mul_smul (r : k) (a b : Quiver.AuxiliaryPathType k Q) : a * (r • b) = r • (a * b) :=
  map_smul (auxiliaryMulLinearMap k Q a) r b

/-- Auxiliary multiplication is associative on three weighted basis vectors. -/
theorem single_mul_single_mul_single_assoc (x y z : Quiver.AuxiliaryBundledPathType Q) (a b c : k) :
    (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
        (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
          (Finsupp.single x a) (Finsupp.single y b))
        (Finsupp.single z c))
      = (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
          (Finsupp.single x a)
          (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
            (Finsupp.single y b) (Finsupp.single z c))) := by
  obtain ⟨xa, xb, xp⟩ := x
  obtain ⟨yc, yd, yq⟩ := y
  obtain ⟨ze, zf, zr⟩ := z
  by_cases hbc : xb = yc
  · subst hbc
    by_cases hde : yd = ze
    · subst hde
      rw [single_mul_single, auxiliaryProduct_of_composable, smul_mul, single_mul_single, auxiliaryProduct_of_composable,
        single_mul_single, auxiliaryProduct_of_composable, mul_smul, single_mul_single, auxiliaryProduct_of_composable,
        Quiver.Path.comp_assoc, smul_smul, smul_smul]
      congr 1
      ring
    · rw [single_mul_single, auxiliaryProduct_of_composable, smul_mul, single_mul_single,
        auxiliaryProduct_of_not_composable _ _ hde, _root_.smul_zero, _root_.smul_zero,
        single_mul_single, auxiliaryProduct_of_not_composable _ _ hde, _root_.smul_zero, mul_zero]
  · by_cases hde : yd = ze
    · subst hde
      rw [single_mul_single, auxiliaryProduct_of_not_composable _ _ hbc, _root_.smul_zero, zero_mul,
        single_mul_single, auxiliaryProduct_of_composable, mul_smul, single_mul_single,
        auxiliaryProduct_of_not_composable _ _ hbc, _root_.smul_zero, _root_.smul_zero]
    · rw [single_mul_single, auxiliaryProduct_of_not_composable _ _ hbc, _root_.smul_zero, zero_mul,
        single_mul_single, auxiliaryProduct_of_not_composable _ _ hde, _root_.smul_zero, mul_zero]

/-- A property of auxiliary elements follows from its zero, addition, and single-basis-vector cases. -/
@[elab_as_elim]
theorem induction_on {motive : Quiver.AuxiliaryPathType k Q → Prop} (f : Quiver.AuxiliaryPathType k Q)
    (zero : motive 0) (add : ∀ g h : Quiver.AuxiliaryPathType k Q, motive g → motive h → motive (g + h))
    (single : ∀ (x : Quiver.AuxiliaryBundledPathType Q) (a : k), motive (Finsupp.single x a)) : motive f :=
  Finsupp.induction_linear f zero add single

/-- Auxiliary multiplication is associative. -/
protected theorem mul_assoc (f g h : Quiver.AuxiliaryPathType k Q) : f * g * h = f * (g * h) := by
  induction f using _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
  | zero => simp only [zero_mul]
  | add f1 f2 hf1 hf2 => rw [add_mul, add_mul, add_mul, hf1, hf2]
  | single x a =>
    induction g using _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
    | zero => simp only [mul_zero, zero_mul]
    | add g1 g2 hg1 hg2 => rw [mul_add, add_mul, add_mul, mul_add, hg1, hg2]
    | single y b =>
      induction h using _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
      | zero => simp only [mul_zero]
      | add h1 h2 hh1 hh2 => rw [mul_add, mul_add, mul_add, hh1, hh2]
      | single z c => exact single_mul_single_mul_single_assoc x y z a b c

variable (k Q)

/-- The associative nonunital ring structure on the auxiliary type. -/
noncomputable instance instNonUnitalRing : NonUnitalRing (Quiver.AuxiliaryPathType k Q) :=
  { (inferInstance : NonUnitalNonAssocRing (Quiver.AuxiliaryPathType k Q)) with
    mul_assoc := _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.mul_assoc }

/-- An auxiliary element available when the vertex type is finite. -/
noncomputable def finiteAuxiliaryElement [Fintype Q] : Quiver.AuxiliaryPathType k Q :=
  ∑ i, auxiliaryOfPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q)

/-- The multiplicative identity on the auxiliary type with finitely many vertices. -/
noncomputable instance instOne [Fintype Q] : One (Quiver.AuxiliaryPathType k Q) := ⟨finiteAuxiliaryElement k Q⟩

variable {k Q}

/-- The unit of the auxiliary type is the sum of the single basis vectors belonging to length-zero paths. -/
theorem one_eq_sum_single_vertexPath [Fintype Q] :
    (1 : Quiver.AuxiliaryPathType k Q) = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) 1 :=
  rfl

/-- The unit of the auxiliary type is the sum of the embedded length-zero paths over all vertices. -/
theorem one_eq_sum_ofPath_vertexPath [Fintype Q] :
    (1 : Quiver.AuxiliaryPathType k Q) = ∑ i, auxiliaryOfPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) :=
  rfl

/-- One is a left identity for the auxiliary type with finitely many vertices. -/
protected theorem one_mul [Fintype Q] (f : Quiver.AuxiliaryPathType k Q) : (1 : Quiver.AuxiliaryPathType k Q) * f = f := by
  induction f using _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
  | zero => rw [mul_zero]
  | add f g hf hg => rw [mul_add, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_eq_sum_ofPath_vertexPath, Finset.sum_mul]
    have hterm : ∀ i : Q,
        (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
          (auxiliaryOfPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q))
          (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.AuxiliaryBundledPathType Q) a))
        = if i = xa then (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.AuxiliaryBundledPathType Q) a : Quiver.AuxiliaryPathType k Q)
          else 0 := by
      intro i
      unfold auxiliaryOfPath
      rw [single_mul_single, auxiliaryProduct_vertexPath]
      by_cases h : i = xa
      · rw [one_mul, if_pos h, if_pos h]; exact smul_single_one a _
      · rw [if_neg h, if_neg h]; exact smul_zero _
    rw [Finset.sum_eq_single_of_mem xa (Finset.mem_univ xa)
        (fun b _ hb => (hterm b).trans (if_neg hb)), hterm xa, if_pos rfl]

/-- One is a right identity for the auxiliary type with finitely many vertices. -/
protected theorem mul_one [Fintype Q] (f : Quiver.AuxiliaryPathType k Q) : f * (1 : Quiver.AuxiliaryPathType k Q) = f := by
  induction f using _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.induction_on with
  | zero => rw [zero_mul]
  | add f g hf hg => rw [add_mul, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_eq_sum_ofPath_vertexPath, Finset.mul_sum]
    have hterm : ∀ i : Q,
        (@HMul.hMul (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) (Quiver.AuxiliaryPathType k Q) _
          (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.AuxiliaryBundledPathType Q) a)
          (auxiliaryOfPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q)))
        = if xb = i then (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.AuxiliaryBundledPathType Q) a : Quiver.AuxiliaryPathType k Q)
          else 0 := by
      intro i
      unfold auxiliaryOfPath
      rw [single_mul_single, auxiliaryProduct_pathVertex]
      by_cases h : xb = i
      · rw [mul_one, if_pos h, if_pos h]; exact smul_single_one a _
      · rw [if_neg h, if_neg h]; exact smul_zero _
    rw [Finset.sum_eq_single_of_mem xb (Finset.mem_univ xb)
        (fun b _ hb => (hterm b).trans (if_neg (Ne.symm hb))), hterm xb, if_pos rfl]

variable (k Q)

/-- The unital ring structure on the auxiliary type with finitely many vertices. -/
noncomputable instance instRing [Fintype Q] : Ring (Quiver.AuxiliaryPathType k Q) :=
  { (inferInstance : NonUnitalRing (Quiver.AuxiliaryPathType k Q)),
    (inferInstance : One (Quiver.AuxiliaryPathType k Q)) with
    one_mul := _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.one_mul
    mul_one := _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.mul_one }

/-- The algebra structure on the auxiliary type when the quiver has finitely many vertices. -/
noncomputable instance instAlgebra [Fintype Q] : Algebra k (Quiver.AuxiliaryPathType k Q) :=
  Algebra.ofModule smul_mul mul_smul

/-- The sum of all embedded length-zero paths is the multiplicative identity of the auxiliary type. -/
theorem sum_vertexPath_eq_one [Fintype Q] :
    (∑ i, auxiliaryOfPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryPathType k Q) = 1 :=
  one_eq_sum_ofPath_vertexPath.symm

end Quiver.AuxiliaryPathType

/-- An auxiliary type associated with a field and a quiver. -/
@[source_ref "Chapter2/Definition2.8.4" (role := supporting),
  source_ref "Chapter2/Discussion_path_algebra_intro" (role := primary)]
abbrev Quiver.AuxiliaryOppositeType (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  (Quiver.AuxiliaryPathType k Q)ᵐᵒᵖ

namespace Quiver.AuxiliaryOppositeType

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- An element of the auxiliary type associated with a bundled quiver path. -/
@[source_ref "Chapter2/Definition2.8.4" (role := supporting)]
noncomputable def auxiliaryElementOfPath (x : Quiver.AuxiliaryBundledPathType Q) : Quiver.AuxiliaryOppositeType k Q :=
  MulOpposite.op (_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath (k := k) x)

/-- Removing the opposite wrapper from the designated auxiliary element gives the corresponding auxiliary path element. -/
@[simp]
theorem unop_auxiliaryElement_eq_auxiliaryOfPath (x : Quiver.AuxiliaryBundledPathType Q) :
    MulOpposite.unop (auxiliaryElementOfPath (k := k) x) = _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath (k := k) x :=
  rfl

/-- Multiplying the designated auxiliary elements of composable paths gives the element of their composite. -/
@[source_ref "Chapter2/Definition2.8.4" (role := primary)]
theorem auxiliaryElement_mul_auxiliaryElement {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    auxiliaryElementOfPath (k := k) (⟨b, c, q⟩ : Quiver.AuxiliaryBundledPathType Q) *
        auxiliaryElementOfPath (k := k) (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) =
      auxiliaryElementOfPath (k := k) (⟨a, c, p.comp q⟩ : Quiver.AuxiliaryBundledPathType Q) := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul]
  simp only [unop_auxiliaryElement_eq_auxiliaryOfPath]
  unfold _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single, one_mul, one_smul, _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_of_composable]

/-- The designated auxiliary elements multiply to zero when the corresponding paths are not composable. -/
@[source_ref "Chapter2/Definition2.8.4" (role := primary)]
theorem auxiliaryElement_mul_auxiliaryElement_eq_zero {a b c d : Q} (p : Quiver.Path a b)
    (q : Quiver.Path c d) (h : b ≠ c) :
    auxiliaryElementOfPath (k := k) (⟨c, d, q⟩ : Quiver.AuxiliaryBundledPathType Q) *
        auxiliaryElementOfPath (k := k) (⟨a, b, p⟩ : Quiver.AuxiliaryBundledPathType Q) = 0 := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul]
  simp only [unop_auxiliaryElement_eq_auxiliaryOfPath, MulOpposite.unop_zero]
  unfold _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryOfPath
  rw [_root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.single_mul_single,
    _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.auxiliaryProduct_of_not_composable _ _ h,
    _root_.smul_zero]

/-- An auxiliary element associated with a vertex of the quiver. -/
@[source_ref "Chapter2/Definition2.8.4" (role := supporting)]
noncomputable def auxiliaryVertexElement (i : Q) : Quiver.AuxiliaryOppositeType k Q :=
  auxiliaryElementOfPath (k := k) ⟨i, i, Quiver.Path.nil⟩

/-- For a finite vertex type, the sum of the designated vertex elements is one in the auxiliary type. -/
@[source_ref "Chapter2/Remark2.8.5" (role := supporting)]
theorem sum_auxiliaryVertexElement_eq_one [Fintype Q] :
    (∑ i, auxiliaryVertexElement (k := k) (Q := Q) i : Quiver.AuxiliaryOppositeType k Q) = 1 := by
  apply MulOpposite.unop_injective
  rw [show MulOpposite.unop
      (∑ i, auxiliaryVertexElement (k := k) (Q := Q) i : Quiver.AuxiliaryOppositeType k Q) =
        ∑ i, MulOpposite.unop (auxiliaryVertexElement (k := k) (Q := Q) i) from
      map_sum MulOpposite.opAddEquiv.symm _ Finset.univ]
  simp only [auxiliaryVertexElement, unop_auxiliaryElement_eq_auxiliaryOfPath, MulOpposite.unop_one]
  exact _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType.sum_vertexPath_eq_one k Q

end Quiver.AuxiliaryOppositeType

end RepresentationTheory.Quiver.AuxiliaryPathStructures

attribute [nolint unusedArguments] _root_.RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryPathType
