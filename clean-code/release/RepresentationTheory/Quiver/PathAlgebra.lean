/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.LinearAlgebra.Finsupp.LSum
import RepresentationTheory.Alignment.Attribute

/-! # Path algebras of quivers -/

namespace RepresentationTheory.Quiver.PathAlgebra

/-- A quiver path bundled together with its source and target vertices. -/
abbrev Quiver.BundledPath (Q : Type*) [Quiver Q] : Type _ :=
  Σ (a : Q) (b : Q), Quiver.Path a b

namespace Quiver.BundledPath

variable {Q : Type*} [Quiver Q] [DecidableEq Q]

/-- Composition of bundled paths, returning no result when their intermediate vertices differ. -/
noncomputable def compose : Quiver.BundledPath Q → Quiver.BundledPath Q → Option (Quiver.BundledPath Q)
  | ⟨a, b, p⟩, ⟨c, d, q⟩ =>
    if h : b = c then some ⟨a, d, p.comp (h ▸ q)⟩ else none

/-- Composable bundled paths compose to the bundled concatenated path. -/
theorem compose_eq_some {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    compose (⟨a, b, p⟩ : Quiver.BundledPath Q) ⟨b, d, q⟩ = some ⟨a, d, p.comp q⟩ := by
  simp [compose]

/-- Bundled paths with unequal intermediate vertices do not compose. -/
theorem compose_eq_none {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d) (h : b ≠ c) :
    compose (⟨a, b, p⟩ : Quiver.BundledPath Q) ⟨c, d, q⟩ = none := by
  simp only [compose, dif_neg h]

end Quiver.BundledPath

/-- The vector space of finitely supported coefficients on all paths of a quiver, equipped with path concatenation. -/
def Quiver.PathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  Quiver.BundledPath Q →₀ k

namespace Quiver.PathAlgebra

section Instances
variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

/-- The additive commutative group structure on a path algebra. -/
noncomputable instance instAddCommGroup : AddCommGroup (Quiver.PathAlgebra k Q) :=
  inferInstanceAs (AddCommGroup (Quiver.BundledPath Q →₀ k))

/-- The scalar module structure on a path algebra. -/
noncomputable instance instModule : Module k (Quiver.PathAlgebra k Q) :=
  inferInstanceAs (Module k (Quiver.BundledPath Q →₀ k))

/-- The canonical inhabited structure on a path algebra. -/
instance instInhabited : Inhabited (Quiver.PathAlgebra k Q) :=
  inferInstanceAs (Inhabited (Quiver.BundledPath Q →₀ k))

end Instances

variable (k : Type*) (Q : Type*) [Field k] [Quiver Q] [DecidableEq Q]

variable {k Q}

/-- The path-algebra basis element represented by a bundled path. -/
noncomputable def ofPath (x : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q :=
  Finsupp.single x 1

omit [DecidableEq Q] in
/-- Scaling a path basis vector with coefficient one replaces its coefficient by the scalar. -/
theorem smul_single_one (c : k) (x : Quiver.BundledPath Q) :
    c • Finsupp.single x (1 : k) = Finsupp.single x c := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- A scalar multiple of the zero path-algebra element is zero. -/
theorem smul_zero (c : k) : c • (0 : Quiver.PathAlgebra k Q) = 0 :=
  (_root_.smul_zero c : c • (0 : Quiver.BundledPath Q →₀ k) = 0)

/-- The path-algebra product of two bundled paths, represented as a basis vector when they compose and as zero otherwise. -/
noncomputable def mulPath (x y : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q :=
  (x.compose y).elim 0 (fun z => Finsupp.single z (1 : k))

/-- The product attached to two composable paths is the basis vector of their composite. -/
theorem mulPath_of_composable {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    mulPath (⟨a, b, p⟩ : Quiver.BundledPath Q) ⟨b, d, q⟩
      = Finsupp.single (⟨a, d, p.comp q⟩ : Quiver.BundledPath Q) (1 : k) := by
  rw [mulPath, _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.BundledPath.compose_eq_some]; rfl

/-- The product attached to paths with unequal intermediate vertices is zero. -/
theorem mulPath_of_not_composable {a b c d : Q} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (h : b ≠ c) :
    mulPath (⟨a, b, p⟩ : Quiver.BundledPath Q) ⟨c, d, q⟩ = (0 : Quiver.PathAlgebra k Q) := by
  rw [mulPath, _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.BundledPath.compose_eq_none _ _ h]; rfl

/-- Multiplication by a length-zero path on the left selects paths with the matching source vertex. -/
theorem mulPath_vertexPath (i a b : Q) (p : Quiver.Path a b) :
    mulPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) ⟨a, b, p⟩
      = if i = a then Finsupp.single (⟨a, b, p⟩ : Quiver.BundledPath Q) (1 : k) else 0 := by
  by_cases h : i = a
  · subst h
    rw [mulPath_of_composable, Quiver.Path.nil_comp, if_pos rfl]
  · rw [if_neg h]; exact mulPath_of_not_composable _ _ h

/-- Multiplication by a length-zero path on the right selects paths with the matching target vertex. -/
theorem mulPath_pathVertex (i a b : Q) (p : Quiver.Path a b) :
    mulPath (⟨a, b, p⟩ : Quiver.BundledPath Q) ⟨i, i, Quiver.Path.nil⟩
      = if b = i then Finsupp.single (⟨a, b, p⟩ : Quiver.BundledPath Q) (1 : k) else 0 := by
  by_cases h : b = i
  · subst h
    rw [mulPath_of_composable, Quiver.Path.comp_nil, if_pos rfl]
  · rw [if_neg h]; exact mulPath_of_not_composable _ _ h

variable (k Q)

/-- Path-algebra multiplication expressed as a linear map into linear maps. -/
noncomputable def mulLinearMap :
    (Quiver.BundledPath Q →₀ k) →ₗ[k] (Quiver.BundledPath Q →₀ k) →ₗ[k] Quiver.PathAlgebra k Q :=
  Finsupp.lsum k fun x =>
    (LinearMap.id : k →ₗ[k] k).smulRight
      (Finsupp.lsum k fun y => (LinearMap.id : k →ₗ[k] k).smulRight (mulPath x y))

/-- The distributive multiplication structure on a path algebra before associativity and a unit are installed. -/
noncomputable instance instNonUnitalNonAssocRing : NonUnitalNonAssocRing (Quiver.PathAlgebra k Q) :=
  { (inferInstance : AddCommGroup (Quiver.PathAlgebra k Q)) with
    mul := fun f g => mulLinearMap k Q f g

    left_distrib := fun a b c => map_add (mulLinearMap k Q a) b c
    right_distrib := fun a b c =>
      (LinearMap.congr_fun (map_add (mulLinearMap k Q) a b) c).trans (LinearMap.add_apply _ _ _)
    zero_mul := fun a =>
      (LinearMap.congr_fun (map_zero (mulLinearMap k Q)) a).trans (LinearMap.zero_apply a)
    mul_zero := fun a => map_zero (mulLinearMap k Q a) }

variable {k Q}

/-- The path-algebra product agrees with the bilinear multiplication map. -/
theorem mul_eq_mulLinearMap (f g : Quiver.PathAlgebra k Q) : f * g = mulLinearMap k Q f g := rfl

/-- The product of two weighted path basis vectors is their coefficient product times the path product. -/
theorem single_mul_single (x y : Quiver.BundledPath Q) (a b : k) :
    (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
        (Finsupp.single x a) (Finsupp.single y b))
      = (a * b) • mulPath x y := by
  rw [mul_eq_mulLinearMap, mulLinearMap]
  simp only [Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq,
    LinearMap.smul_apply, smul_smul]

/-- Scalar multiplication in the left factor commutes with path-algebra multiplication. -/
theorem smul_mul (r : k) (a b : Quiver.PathAlgebra k Q) : (r • a) * b = r • (a * b) :=
  (LinearMap.congr_fun (map_smul (mulLinearMap k Q) r a) b).trans (LinearMap.smul_apply r _ b)

/-- Scalar multiplication in the right factor commutes with path-algebra multiplication. -/
theorem mul_smul (r : k) (a b : Quiver.PathAlgebra k Q) : a * (r • b) = r • (a * b) :=
  map_smul (mulLinearMap k Q a) r b

/-- Multiplication is associative on three weighted path basis vectors. -/
theorem single_mul_single_mul_single_assoc (x y z : Quiver.BundledPath Q) (a b c : k) :
    (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
        (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
          (Finsupp.single x a) (Finsupp.single y b))
        (Finsupp.single z c))
      = (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
          (Finsupp.single x a)
          (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
            (Finsupp.single y b) (Finsupp.single z c))) := by
  obtain ⟨xa, xb, xp⟩ := x
  obtain ⟨yc, yd, yq⟩ := y
  obtain ⟨ze, zf, zr⟩ := z
  by_cases hbc : xb = yc
  · subst hbc
    by_cases hde : yd = ze
    · subst hde
      rw [single_mul_single, mulPath_of_composable, smul_mul, single_mul_single, mulPath_of_composable,
        single_mul_single, mulPath_of_composable, mul_smul, single_mul_single, mulPath_of_composable,
        Quiver.Path.comp_assoc, smul_smul, smul_smul]
      congr 1
      ring
    · rw [single_mul_single, mulPath_of_composable, smul_mul, single_mul_single,
        mulPath_of_not_composable _ _ hde, _root_.smul_zero, _root_.smul_zero,
        single_mul_single, mulPath_of_not_composable _ _ hde, _root_.smul_zero, mul_zero]
  · by_cases hde : yd = ze
    · subst hde
      rw [single_mul_single, mulPath_of_not_composable _ _ hbc, _root_.smul_zero, zero_mul,
        single_mul_single, mulPath_of_composable, mul_smul, single_mul_single,
        mulPath_of_not_composable _ _ hbc, _root_.smul_zero, _root_.smul_zero]
    · rw [single_mul_single, mulPath_of_not_composable _ _ hbc, _root_.smul_zero, zero_mul,
        single_mul_single, mulPath_of_not_composable _ _ hde, _root_.smul_zero, mul_zero]

/-- A property of path-algebra elements follows from its zero, addition, and single-basis-vector cases. -/
@[elab_as_elim]
theorem induction_on {motive : Quiver.PathAlgebra k Q → Prop} (f : Quiver.PathAlgebra k Q)
    (zero : motive 0) (add : ∀ g h : Quiver.PathAlgebra k Q, motive g → motive h → motive (g + h))
    (single : ∀ (x : Quiver.BundledPath Q) (a : k), motive (Finsupp.single x a)) : motive f :=
  Finsupp.induction_linear f zero add single

/-- Path-algebra multiplication is associative. -/
protected theorem mul_assoc (f g h : Quiver.PathAlgebra k Q) : f * g * h = f * (g * h) := by
  induction f using _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.induction_on with
  | zero => simp only [zero_mul]
  | add f1 f2 hf1 hf2 => rw [add_mul, add_mul, add_mul, hf1, hf2]
  | single x a =>
    induction g using _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.induction_on with
    | zero => simp only [mul_zero, zero_mul]
    | add g1 g2 hg1 hg2 => rw [mul_add, add_mul, add_mul, mul_add, hg1, hg2]
    | single y b =>
      induction h using _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.induction_on with
      | zero => simp only [mul_zero]
      | add h1 h2 hh1 hh2 => rw [mul_add, mul_add, mul_add, hh1, hh2]
      | single z c => exact single_mul_single_mul_single_assoc x y z a b c

variable (k Q)

/-- The associative nonunital ring structure on a path algebra. -/
noncomputable instance instNonUnitalRing : NonUnitalRing (Quiver.PathAlgebra k Q) :=
  { (inferInstance : NonUnitalNonAssocRing (Quiver.PathAlgebra k Q)) with
    mul_assoc := _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mul_assoc }

/-- An auxiliary path-algebra element available when the vertex type is finite. -/
noncomputable def auxiliaryElement [Fintype Q] : Quiver.PathAlgebra k Q :=
  ∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)

/-- The multiplicative identity on a path algebra with finitely many vertices. -/
noncomputable instance instOne [Fintype Q] : One (Quiver.PathAlgebra k Q) := ⟨auxiliaryElement k Q⟩

variable {k Q}

/-- The unit is the sum of the single basis vectors belonging to length-zero paths. -/
theorem one_eq_sum_single_vertexPath [Fintype Q] :
    (1 : Quiver.PathAlgebra k Q) = ∑ i, Finsupp.single (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) 1 :=
  rfl

/-- The unit is the sum of the embedded length-zero paths over all vertices. -/
theorem one_eq_sum_ofPath_vertexPath [Fintype Q] :
    (1 : Quiver.PathAlgebra k Q) = ∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) :=
  rfl

/-- One is a left identity for a path algebra with finitely many vertices. -/
protected theorem one_mul [Fintype Q] (f : Quiver.PathAlgebra k Q) : (1 : Quiver.PathAlgebra k Q) * f = f := by
  induction f using _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.induction_on with
  | zero => rw [mul_zero]
  | add f g hf hg => rw [mul_add, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_eq_sum_ofPath_vertexPath, Finset.sum_mul]
    have hterm : ∀ i : Q,
        (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
          (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q))
          (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.BundledPath Q) a))
        = if i = xa then (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.BundledPath Q) a : Quiver.PathAlgebra k Q)
          else 0 := by
      intro i
      unfold ofPath
      rw [single_mul_single, mulPath_vertexPath]
      by_cases h : i = xa
      · rw [one_mul, if_pos h, if_pos h]; exact smul_single_one a _
      · rw [if_neg h, if_neg h]; exact smul_zero _
    rw [Finset.sum_eq_single_of_mem xa (Finset.mem_univ xa)
        (fun b _ hb => (hterm b).trans (if_neg hb)), hterm xa, if_pos rfl]

/-- One is a right identity for a path algebra with finitely many vertices. -/
protected theorem mul_one [Fintype Q] (f : Quiver.PathAlgebra k Q) : f * (1 : Quiver.PathAlgebra k Q) = f := by
  induction f using _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.induction_on with
  | zero => rw [zero_mul]
  | add f g hf hg => rw [add_mul, hf, hg]
  | single x a =>
    obtain ⟨xa, xb, xp⟩ := x
    rw [one_eq_sum_ofPath_vertexPath, Finset.mul_sum]
    have hterm : ∀ i : Q,
        (@HMul.hMul (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) (Quiver.PathAlgebra k Q) _
          (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.BundledPath Q) a)
          (ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q)))
        = if xb = i then (Finsupp.single (⟨xa, xb, xp⟩ : Quiver.BundledPath Q) a : Quiver.PathAlgebra k Q)
          else 0 := by
      intro i
      unfold ofPath
      rw [single_mul_single, mulPath_pathVertex]
      by_cases h : xb = i
      · rw [mul_one, if_pos h, if_pos h]; exact smul_single_one a _
      · rw [if_neg h, if_neg h]; exact smul_zero _
    rw [Finset.sum_eq_single_of_mem xb (Finset.mem_univ xb)
        (fun b _ hb => (hterm b).trans (if_neg (Ne.symm hb))), hterm xb, if_pos rfl]

variable (k Q)

/-- The unital ring structure on a path algebra with finitely many vertices. -/
noncomputable instance instRing [Fintype Q] : Ring (Quiver.PathAlgebra k Q) :=
  { (inferInstance : NonUnitalRing (Quiver.PathAlgebra k Q)),
    (inferInstance : One (Quiver.PathAlgebra k Q)) with
    one_mul := _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.one_mul
    mul_one := _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mul_one }

/-- The algebra structure on a path algebra when the quiver has finitely many vertices. -/
noncomputable instance instAlgebra [Fintype Q] : Algebra k (Quiver.PathAlgebra k Q) :=
  Algebra.ofModule smul_mul mul_smul

/-- The sum of all embedded length-zero paths is the multiplicative identity. -/
theorem sum_vertexPath_eq_one [Fintype Q] :
    (∑ i, ofPath (⟨i, i, Quiver.Path.nil⟩ : Quiver.BundledPath Q) : Quiver.PathAlgebra k Q) = 1 :=
  one_eq_sum_ofPath_vertexPath.symm

end Quiver.PathAlgebra

/-- The opposite of the path algebra of a quiver over a field. -/
@[source_ref "Chapter2/Definition2.8.4" (role := supporting),
  source_ref "Chapter2/Discussion_path_algebra_intro" (role := primary)]
abbrev Quiver.OppositePathAlgebra (k : Type*) (Q : Type*) [Field k] [Quiver Q]
    [DecidableEq Q] : Type _ :=
  (Quiver.PathAlgebra k Q)ᵐᵒᵖ

namespace Quiver.OppositePathAlgebra

variable {k : Type*} {Q : Type*} [Field k] [Quiver Q] [DecidableEq Q]

/-- The element of the opposite path algebra represented by a single bundled path. -/
@[source_ref "Chapter2/Definition2.8.4" (role := supporting)]
noncomputable def opOfPath (x : Quiver.BundledPath Q) : Quiver.OppositePathAlgebra k Q :=
  MulOpposite.op (_root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.ofPath (k := k) x)

/-- Removing the opposite wrapper from a path basis element gives the corresponding path-algebra basis element. -/
@[simp]
theorem unop_opOfPath (x : Quiver.BundledPath Q) :
    MulOpposite.unop (opOfPath (k := k) x) = _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.ofPath (k := k) x :=
  rfl

/-- Multiplying opposite-algebra basis elements associated to composable paths represents their composite. -/
@[source_ref "Chapter2/Definition2.8.4" (role := primary)]
theorem opOfPath_mul_opOfPath {a b c : Q} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    opOfPath (k := k) (⟨b, c, q⟩ : Quiver.BundledPath Q) *
        opOfPath (k := k) (⟨a, b, p⟩ : Quiver.BundledPath Q) =
      opOfPath (k := k) (⟨a, c, p.comp q⟩ : Quiver.BundledPath Q) := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul]
  simp only [unop_opOfPath]
  unfold _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.ofPath
  rw [_root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.single_mul_single, one_mul, one_smul, _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mulPath_of_composable]

/-- Opposite-algebra basis elements multiply to zero when the corresponding paths are not composable. -/
@[source_ref "Chapter2/Definition2.8.4" (role := primary)]
theorem opOfPath_mul_opOfPath_eq_zero {a b c d : Q} (p : Quiver.Path a b)
    (q : Quiver.Path c d) (h : b ≠ c) :
    opOfPath (k := k) (⟨c, d, q⟩ : Quiver.BundledPath Q) *
        opOfPath (k := k) (⟨a, b, p⟩ : Quiver.BundledPath Q) = 0 := by
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul]
  simp only [unop_opOfPath, MulOpposite.unop_zero]
  unfold _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.ofPath
  rw [_root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.single_mul_single,
    _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.mulPath_of_not_composable _ _ h,
    _root_.smul_zero]

/-- An opposite path-algebra element associated to a vertex. -/
@[source_ref "Chapter2/Definition2.8.4" (role := supporting)]
noncomputable def vertexElement (i : Q) : Quiver.OppositePathAlgebra k Q :=
  opOfPath (k := k) ⟨i, i, Quiver.Path.nil⟩

/-- For a finite vertex type, the sum of the vertex-associated elements is one in the opposite path algebra. -/
@[source_ref "Chapter2/Remark2.8.5" (role := primary)]
theorem sum_vertexElement_eq_one [Fintype Q] :
    (∑ i, vertexElement (k := k) (Q := Q) i : Quiver.OppositePathAlgebra k Q) = 1 := by
  apply MulOpposite.unop_injective
  rw [show MulOpposite.unop
      (∑ i, vertexElement (k := k) (Q := Q) i : Quiver.OppositePathAlgebra k Q) =
        ∑ i, MulOpposite.unop (vertexElement (k := k) (Q := Q) i) from
      map_sum MulOpposite.opAddEquiv.symm _ Finset.univ]
  simp only [vertexElement, unop_opOfPath, MulOpposite.unop_one]
  exact _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.sum_vertexPath_eq_one k Q

end Quiver.OppositePathAlgebra

end RepresentationTheory.Quiver.PathAlgebra

attribute [nolint unusedArguments] _root_.RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra
