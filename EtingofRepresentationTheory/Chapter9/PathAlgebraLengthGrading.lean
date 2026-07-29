import EtingofRepresentationTheory.Chapter9.PathAlgebraArrowBimodule
import EtingofRepresentationTheory.Chapter9.KoszulHelpers

set_option backward.isDefEq.respectTransparency false

/-!
# Path-length grading of the path algebra `A = PathAlgebra k Q`

The length grading of the path algebra, part of the standard length-`1` projective resolution
of path-algebra modules (Problem 9.4.6 (i)). It provides the length-grading infrastructure that
makes `Mono (stdd M)` and middle exactness of the standard short complex
(`Chapter9/PathAlgebraStandardComplex.lean`) provable, the noncommutative analogue of the
polynomial coordinate isomorphism `coordMapCH` in `Chapter9/KoszulHelpers.lean`.

`A = QuiverPathIndex Q →₀ k` is graded by path length: the basis path `⟨a, b, p⟩` has degree
`p.length`. We package the grading as a coordinate map

```
lengthGrading : A →ₗ[k] (ℕ →₀ A)
```

sending a basis path to its single homogeneous component. It is a section of the summation map
`lengthTotalize` (sum of components), hence injective. The homogeneous projections `lengthProj n`
extract the degree-`n` part.

The coordinate map is typed with the underlying `QuiverPathIndex Q →₀ k` as its domain (so
instance synthesis is unambiguous), while its graded components are `PathAlgebra k Q` values (so
their product is path concatenation).

The cons-splitting direction, that every length-`(n+1)` path is uniquely a length-`n` path
followed by one arrow, is recorded here at the path-index level (`pathLen_comp_arrow`,
`lengthProj_ofPath_mul_arrowElt`), underlying the `S`-bimodule isomorphism `A_n ⊗_S V ≅ A_{n+1}`
used downstream. It mirrors `coordMapCH` and `finsupp_shift_eq_zero` in
`Chapter9/KoszulHelpers.lean`.
-/

universe u

open Etingof

namespace Etingof.PathAlgebra

variable {k : Type u} {Q : Type u} [Field k] [Quiver.{u + 1} Q] [DecidableEq Q]

/-! ## The length of a basis path -/

/-- The length (number of arrows) of the oriented path underlying a basis index. This is the
grading degree of the corresponding basis element of `A`. -/
def pathLen (p : QuiverPathIndex Q) : ℕ := p.2.2.length

omit [DecidableEq Q] in
@[simp] theorem pathLen_mk {a b : Q} (p : Quiver.Path a b) :
    pathLen (⟨a, b, p⟩ : QuiverPathIndex Q) = p.length := rfl

omit [DecidableEq Q] in
/-- The length of a concatenation is the sum of the lengths. -/
theorem pathLen_comp {a b d : Q} (p : Quiver.Path a b) (q : Quiver.Path b d) :
    pathLen (⟨a, d, p.comp q⟩ : QuiverPathIndex Q) = pathLen (⟨a, b, p⟩ : QuiverPathIndex Q)
      + pathLen (⟨b, d, q⟩ : QuiverPathIndex Q) := by
  simp [pathLen, Quiver.Path.length_comp]

/-! ## The length-grading coordinate map -/

variable (k Q) in
/-- **The length grading of `A`.** The `k`-linear coordinate map `A →ₗ[k] (ℕ →₀ A)` sending a
basis path `⟨a, b, p⟩` (scaled by `c`) to its single homogeneous component in degree `p.length`.
The noncommutative analogue of `coordMapCH` for the polynomial Koszul resolution: it splits `A`
into its length-graded pieces. -/
noncomputable def lengthGrading :
    (QuiverPathIndex Q →₀ k) →ₗ[k] (ℕ →₀ PathAlgebra k Q) :=
  Finsupp.lsum k fun p =>
    (LinearMap.id : k →ₗ[k] k).smulRight (Finsupp.single (pathLen p) (ofPath p))

@[simp] theorem lengthGrading_single (p : QuiverPathIndex Q) (c : k) :
    lengthGrading k Q (Finsupp.single p c)
      = Finsupp.single (pathLen p) (Finsupp.single p c : PathAlgebra k Q) := by
  rw [lengthGrading, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_coe, id_eq,
    Finsupp.smul_single, ofPath, Finsupp.smul_single, smul_eq_mul, mul_one]

variable (k Q) in
/-- **Totalization.** The `k`-linear map `(ℕ →₀ A) →ₗ[k] A` summing the graded components. It is a
left inverse of `lengthGrading` (`lengthTotalize_lengthGrading`). -/
noncomputable def lengthTotalize : (ℕ →₀ PathAlgebra k Q) →ₗ[k] PathAlgebra k Q :=
  Finsupp.lsum k fun _ => LinearMap.id

@[simp] theorem lengthTotalize_single (n : ℕ) (a : PathAlgebra k Q) :
    lengthTotalize k Q (Finsupp.single n a) = a := by
  rw [lengthTotalize, Finsupp.lsum_single, LinearMap.id_coe, id_eq]

/-- Reassembling the length grading recovers the original element: `lengthTotalize` is a left
inverse of `lengthGrading`. -/
@[simp] theorem lengthTotalize_lengthGrading (a : PathAlgebra k Q) :
    lengthTotalize k Q (lengthGrading k Q a) = a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single p c => rw [lengthGrading_single, lengthTotalize_single]

/-- **The length grading is injective.** Distinct elements have distinct graded decompositions. -/
theorem lengthGrading_injective : Function.Injective (lengthGrading k Q) :=
  Function.LeftInverse.injective (lengthTotalize_lengthGrading (k := k) (Q := Q))

/-! ## Homogeneous projections -/

variable (k Q) in
/-- **The degree-`n` projection** `A →ₗ[k] A`, extracting the length-`n` homogeneous component:
the `n`-th coordinate of `lengthGrading`. -/
noncomputable def lengthProj (n : ℕ) : (QuiverPathIndex Q →₀ k) →ₗ[k] PathAlgebra k Q :=
  (Finsupp.lapply n).comp (lengthGrading k Q)

theorem lengthProj_apply (n : ℕ) (a : QuiverPathIndex Q →₀ k) :
    lengthProj k Q n a = lengthGrading k Q a n := rfl

@[simp] theorem lengthProj_single (n : ℕ) (p : QuiverPathIndex Q) (c : k) :
    lengthProj k Q n (Finsupp.single p c)
      = if pathLen p = n then (Finsupp.single p c : PathAlgebra k Q) else 0 := by
  rw [lengthProj_apply, lengthGrading_single]
  exact Finsupp.single_apply

/-- A basis path lands in its own length degree. -/
theorem lengthProj_single_self (p : QuiverPathIndex Q) (c : k) :
    lengthProj k Q (pathLen p) (Finsupp.single p c) = (Finsupp.single p c : PathAlgebra k Q) := by
  rw [lengthProj_single, if_pos rfl]

/-- The degree-`n` component is already homogeneous: projecting it again to degree `m` is the
identity when `m = n` and zero otherwise. -/
theorem lengthProj_lengthProj (m n : ℕ) (a : QuiverPathIndex Q →₀ k) :
    lengthProj k Q m (lengthProj k Q n a) =
      if m = n then lengthProj k Q n a else 0 := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add, map_add, hf, hg]; split_ifs <;> simp
  | single p c =>
      by_cases hpn : pathLen p = n
      · subst hpn
        rw [lengthProj_single_self, lengthProj_single]
        by_cases hmp : pathLen p = m
        · rw [if_pos hmp, if_pos hmp.symm]
        · rw [if_neg hmp, if_neg (fun h => hmp h.symm)]
      · rw [lengthProj_single, if_neg hpn, map_zero, ite_self]

/-! ## Cons-splitting: concatenation shifts length -/

omit [DecidableEq Q] in
/-- The length of a path followed by one arrow is one more. -/
theorem pathLen_comp_arrow {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    pathLen (⟨a, c, p.comp e.toPath⟩ : QuiverPathIndex Q) = p.length + 1 := by
  change (p.comp e.toPath).length = p.length + 1
  rw [Quiver.Path.length_comp, Quiver.Path.length_toPath]

/-- **Cons-splitting.** The product of a basis path `⟨a, b, p⟩` and an arrow `e : b ⟶ c`
in `A` is the single basis path obtained by appending the arrow: `p · e = cons p e`. This is the
`x ⊗ arrow ↦ x · arrow` map underlying the `S`-bimodule isomorphism `A_n ⊗_S V ≅ A_{n+1}`. -/
theorem ofPath_mul_arrowElt {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    (ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) * arrowElt ⟨b, c, e⟩
      = ofPath (⟨a, c, p.comp e.toPath⟩ : QuiverPathIndex Q) := by
  rw [arrowElt, ArrowIndex.toPathIndex, ofPath_mul_ofPath, compSingle_eq, ofPath]

/-- Right-multiplication of a basis path by an arrow lands in the next length degree: projecting
`p · e` onto degree `len p + 1` returns it unchanged. This is the degree-shift underlying the
top-degree component of the boundary map `d`. -/
theorem lengthProj_ofPath_mul_arrowElt {a b c : Q} (p : Quiver.Path a b) (e : b ⟶ c) :
    lengthProj k Q (p.length + 1)
        ((ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) * arrowElt ⟨b, c, e⟩)
      = (ofPath (⟨a, b, p⟩ : QuiverPathIndex Q) : PathAlgebra k Q) * arrowElt ⟨b, c, e⟩ := by
  rw [ofPath_mul_arrowElt, ofPath, ← pathLen_comp_arrow p e, lengthProj_single_self]

end Etingof.PathAlgebra
