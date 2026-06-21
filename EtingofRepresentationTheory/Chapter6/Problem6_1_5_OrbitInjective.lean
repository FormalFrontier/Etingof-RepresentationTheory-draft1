import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitComorphism
import Mathlib

/-!
# Problem 6.1.5, Step 2(a): the orbit-map comorphism is injective

This file is part of the orbit-counting redirect for the Chapter 6 infinite-type
direction (directive #4777). It closes the genuinely geometric input of Etingof
Problem 6.1.2(a): from *finitely many orbits* it extracts an **algebraically dense
orbit**, and from algebraic density it proves the orbit-map comorphism
`Etingof.Problem6_1_5.orbitComorphism` (constructed in #4803) **injective**.

## The argument (Problem 6.1.2(a), algebraic form)

The book's notion of "Zariski dense" is purely algebraic (6.1.2(a)): a subset
`X ⊆ W = 𝔸ᴺ` is dense if any polynomial `f(x₁,…,x_N)` vanishing on `X` is zero
coefficientwise. We take this as the definition (`IsAlgDense`) and avoid the
Zariski topology entirely:

* **Existence of a dense orbit** (`exists_isAlgDense_orbit`). The orbits cover `W`.
  Were no orbit algebraically dense, each orbit `O` would carry a nonzero witness
  polynomial `f_O` vanishing on it; the product `F = ∏_O f_O` over the (finitely
  many) orbits is nonzero (the polynomial ring is a domain) yet vanishes at every
  point of `W` (each point lies in some orbit). Over an infinite field a polynomial
  vanishing on all of `𝔸ᴺ` is zero (`MvPolynomial.funext`) — contradiction.

* **Density ⟹ comorphism injective** (`injective_orbitComorphism_of_isAlgDense`).
  For each group element `g`, evaluating the generic coordinates `g_{pq}` at the
  actual matrix entries of `g` gives a `k`-algebra map `evalAt g : B → k` of the
  principal-open coordinate ring; it sends the generic matrix `genMatB m i` to the
  actual matrix `↑(g i)` and its inverse `genMatBInv m i` to `↑(g i)⁻¹`, so
  `evalAt g ∘ orbitComorphism v₀ = aeval (coords (g • v₀))` (the orbit map evaluated
  at `g`). Hence if `orbitComorphism v₀ f = 0` then `f` vanishes on the whole orbit
  of `v₀`; algebraic density of that orbit forces `f = 0`.

Combining the two (`exists_injective_orbitComorphism`) supplies, for finitely many
orbits over an infinite field, a base point whose orbit-map comorphism is injective —
exactly the hypothesis consumed by
`Etingof.Problem6_1_5.dim_le_of_injective_comorphism_isLocalization` to deduce
`N ≤ M` (step 2(b)/(c), the field-embedding bridge of #4783/#4804).
-/

open Matrix MvPolynomial MulAction

namespace Etingof.Problem6_1_5

variable {k : Type} [Field k] {n : ℕ} [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)]

/-! ## Coordinates on the representation space -/

/-- The `WIdx`-indexed coordinate vector of a point of `W(m)`: the `(a,b)` entry of
the `i→j` block, read off as the coordinate `⟨i,j,e,(a,b)⟩`. This is the bijection
`W(m) ≃ (WIdx m → k)` identifying `W(m)` with affine space `𝔸ᴺ`. -/
def pointCoords (m : Fin n → ℕ) (x : repSpace (k := k) m) : WIdx m → k :=
  fun w => x w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2

/-- The point of `W(m)` with prescribed coordinates: the right inverse of
`pointCoords`, witnessing that `pointCoords` is surjective (`W(m) = 𝔸ᴺ`). -/
def pointOfCoords (m : Fin n → ℕ) (c : WIdx m → k) : repSpace (k := k) m :=
  fun i j e => Matrix.of fun a b => c ⟨i, j, e, (a, b)⟩

omit [Field k] in
@[simp]
theorem pointCoords_pointOfCoords (m : Fin n → ℕ) (c : WIdx m → k) :
    pointCoords m (pointOfCoords m c) = c := by
  funext w
  rcases w with ⟨i, j, e, a, b⟩
  rfl

/-- **Algebraic density (Problem 6.1.2(a)).** A subset `X ⊆ W(m)` is algebraically
dense if every polynomial vanishing at every point of `X` (via the coordinate map) is
zero. This is the book's notion of Zariski-dense, stated coefficientwise. -/
def IsAlgDense (m : Fin n → ℕ) (X : Set (repSpace (k := k) m)) : Prop :=
  ∀ f : MvPolynomial (WIdx m) k, (∀ x ∈ X, aeval (pointCoords m x) f = 0) → f = 0

/-! ## Existence of an algebraically dense orbit -/

/-- **Problem 6.1.2(a).** If `G(m)` has finitely many orbits on `W(m)` (over an
infinite field), then some orbit is algebraically dense.

If no orbit were dense, the product of one nonzero vanishing witness per orbit would
be a nonzero polynomial vanishing on all of `W(m) = 𝔸ᴺ`, impossible over an infinite
field (`MvPolynomial.funext`). -/
theorem exists_isAlgDense_orbit [Infinite k] (m : Fin n → ℕ)
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    ∃ v₀ : repSpace (k := k) m, IsAlgDense m (orbit (repGroup k m) v₀) := by
  classical
  by_contra h
  push_neg at h
  set Q := orbitRel.Quotient (repGroup k m) (repSpace (k := k) m) with hQ
  letI : Fintype Q := Fintype.ofFinite Q
  -- one nonzero polynomial per orbit, vanishing on that orbit
  have hw : ∀ q : Q, ∃ f : MvPolynomial (WIdx m) k,
      (∀ x ∈ orbit (repGroup k m) q.out, aeval (pointCoords m x) f = 0) ∧ f ≠ 0 := by
    intro q
    have hq := h q.out
    unfold IsAlgDense at hq
    push_neg at hq
    exact hq
  choose f hfvan hf0 using hw
  -- their product is nonzero (polynomial ring over a field is a domain) ...
  set F : MvPolynomial (WIdx m) k := ∏ q : Q, f q with hF
  have hFne : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => hf0 q
  -- ... yet vanishes at every point, hence is zero.
  have hF0 : F = 0 := by
    apply MvPolynomial.funext
    intro c
    rw [map_zero]
    set x := pointOfCoords m c with hx
    have hxc : pointCoords m x = c := pointCoords_pointOfCoords m c
    set q₀ : Q := Quotient.mk'' x with hq0
    have h1 : q₀.orbit = orbit (repGroup k m) q₀.out :=
      orbitRel.Quotient.orbit_eq_orbit_out q₀ Quotient.out_eq'
    have h2 : q₀.orbit = orbit (repGroup k m) x := orbitRel.Quotient.orbit_mk x
    have hxmem : x ∈ orbit (repGroup k m) q₀.out := by
      rw [← h1, h2]; exact mem_orbit_self x
    have hzero : aeval (pointCoords m x) (f q₀) = 0 := hfvan q₀ x hxmem
    have : (eval c) F = aeval (pointCoords m x) F := by rw [← hxc]; rfl
    rw [this, hF, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ q₀) hzero
  exact hFne hF0

/-! ## Per-element evaluation of the principal-open coordinate ring -/

section Reduction

variable (m : Fin n → ℕ)
variable {B : Type} [CommRing B]
  [Algebra (MvPolynomial (GIdx m) k) B]
  [IsLocalization (Submonoid.powers (detProd (k := k) m)) B]
  [Algebra k B] [IsScalarTower k (MvPolynomial (GIdx m) k) B]

/-- The coordinate assignment evaluating the generic group entries `g_{pq}` at the
actual matrix entries of a group element `g`: `X⟨i,(a,b)⟩ ↦ (g i)ₐᵦ`. -/
def groupEntries (g : repGroup k m) : GIdx m → k :=
  fun w => (g w.1 : Matrix (Fin (m w.1)) (Fin (m w.1)) k) w.2.1 w.2.2

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
theorem aeval_groupEntries_genMat (g : repGroup k m) (i : Fin n) :
    (aeval (groupEntries m g)).mapMatrix (genMat (k := k) m i) = (g i : Matrix _ _ k) := by
  ext a b
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, genMat, aeval_X]
  rfl

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
/-- At a group element, the generic-determinant product `detProd m` evaluates to the
product of the (nonzero) determinants `det (g i)`, hence to a unit of the field `k`. -/
theorem isUnit_aeval_groupEntries_detProd (g : repGroup k m) :
    IsUnit (aeval (groupEntries m g) (detProd (k := k) m)) := by
  rw [detProd, map_prod, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  rw [AlgHom.map_det, aeval_groupEntries_genMat]
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp (g i).isUnit).ne_zero

/-- **The evaluation map** `evalAt g : B → k` of the principal-open coordinate ring at
the group element `g`: it lifts `aeval (groupEntries m g)` across the localization
because `detProd m` evaluates to a unit. -/
noncomputable def evalAt (g : repGroup k m) : B →ₐ[k] k :=
  IsLocalization.liftAlgHom (f := aeval (groupEntries m g))
    (fun y => by
      obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [show (y : MvPolynomial (GIdx m) k) = detProd (k := k) m ^ j from hj.symm, map_pow]
      exact (isUnit_aeval_groupEntries_detProd m g).pow j)

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
theorem evalAt_algebraMap (g : repGroup k m) (p : MvPolynomial (GIdx m) k) :
    evalAt (B := B) m g (algebraMap (MvPolynomial (GIdx m) k) B p)
      = aeval (groupEntries m g) p := by
  rw [evalAt, IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq _ p

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
theorem evalAt_map_genMatB (g : repGroup k m) (i : Fin n) :
    (genMatB (k := k) (B := B) m i).map (evalAt (B := B) m g) = (g i : Matrix _ _ k) := by
  ext a b
  simp only [genMatB, Matrix.map_apply]
  rw [evalAt_algebraMap]
  simp [genMat, groupEntries]

omit [Quiver.{0} (Fin n)] [∀ i j : Fin n, Fintype (i ⟶ j)] in
theorem evalAt_map_genMatBInv (g : repGroup k m) (i : Fin n) :
    (genMatBInv (k := k) (B := B) m i).map (evalAt (B := B) m g)
      = (((g i)⁻¹ : GL (Fin (m i)) k) : Matrix (Fin (m i)) (Fin (m i)) k) := by
  have hmul : (g i : Matrix _ _ k) *
      (genMatBInv (k := k) (B := B) m i).map (evalAt (B := B) m g) = 1 := by
    rw [← evalAt_map_genMatB (B := B) m g i, ← Matrix.map_mul, genMatB_mul_inv,
      show ((1 : Matrix (Fin (m i)) (Fin (m i)) B).map (evalAt (B := B) m g)) = 1 from
        Matrix.map_one (⇑(evalAt (B := B) m g)) (map_zero _) (map_one _)]
  have h1 : ((g i : Matrix _ _ k))⁻¹ = (genMatBInv (k := k) (B := B) m i).map (evalAt m g) :=
    Matrix.inv_eq_right_inv hmul
  have h2 : ((g i : Matrix _ _ k))⁻¹
      = (((g i)⁻¹ : GL (Fin (m i)) k) : Matrix (Fin (m i)) (Fin (m i)) k) := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  rw [← h1, h2]

/-- **The evaluation identity.** Composing the orbit-map comorphism with evaluation at
`g` recovers the orbit map evaluated at `g`: it is the polynomial map `coords (g • v₀)`.
Both sides are `k`-algebra maps out of `k[W(m)]`, so it suffices to check on the
coordinate generators, where it is the base-change formula `g j · (v₀) · (g i)⁻¹`. -/
theorem evalAt_comp_orbitComorphism (g : repGroup k m) (v₀ : repSpace (k := k) m) :
    (evalAt (B := B) m g).comp (orbitComorphism (B := B) m v₀)
      = aeval (pointCoords m (g • v₀)) := by
  apply MvPolynomial.algHom_ext
  intro w
  have hmid : ((v₀ w.1 w.2.1 w.2.2.1).map (algebraMap k B)).map (evalAt (B := B) m g)
      = v₀ w.1 w.2.1 w.2.2.1 := by
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, AlgHom.commutes]
    simp
  have key : ∀ M : Matrix (Fin (m w.2.1)) (Fin (m w.1)) B,
      (evalAt (B := B) m g) (M w.2.2.2.1 w.2.2.2.2)
        = (M.map (evalAt (B := B) m g)) w.2.2.2.1 w.2.2.2.2 := fun _ => rfl
  rw [AlgHom.comp_apply, orbitComorphism_X, aeval_X, pointCoords, repSpace_smul_apply,
    key, Matrix.map_mul, Matrix.map_mul, evalAt_map_genMatB, evalAt_map_genMatBInv, hmid]

/-! ## Density ⟹ injectivity -/

/-- **Problem 6.1.2(a) ⟹ injectivity.** If the `G(m)`-orbit of `v₀` is algebraically
dense, the orbit-map comorphism `orbitComorphism m v₀` is injective: a polynomial in its
kernel vanishes on the whole orbit (via `evalAt`), hence is zero by density. -/
theorem injective_orbitComorphism_of_isAlgDense (v₀ : repSpace (k := k) m)
    (hdense : IsAlgDense m (orbit (repGroup k m) v₀)) :
    Function.Injective (orbitComorphism (B := B) m v₀) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply hdense
  intro x hx
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  have := congrArg (evalAt (B := B) m g) hf
  rw [map_zero, ← AlgHom.comp_apply, evalAt_comp_orbitComorphism] at this
  exact this

/-- **Step 2(a) payoff.** Over an infinite field, finitely many `G(m)`-orbits on `W(m)`
yield a base point whose orbit-map comorphism is injective — the geometric input the
field-embedding bridge of #4783 turns into the dimension bound `N ≤ M`. -/
theorem exists_injective_orbitComorphism [Infinite k]
    [Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))] :
    ∃ v₀ : repSpace (k := k) m, Function.Injective (orbitComorphism (B := B) m v₀) := by
  obtain ⟨v₀, hv₀⟩ := exists_isAlgDense_orbit (k := k) m
  exact ⟨v₀, injective_orbitComorphism_of_isAlgDense m v₀ hv₀⟩

end Reduction

end Etingof.Problem6_1_5
