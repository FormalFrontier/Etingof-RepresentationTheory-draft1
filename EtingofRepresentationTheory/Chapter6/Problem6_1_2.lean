import EtingofRepresentationTheory.Chapter5.DetLocalization
import EtingofRepresentationTheory.Chapter6.Problem6_1_5_DimBound

/-!
# Problem 6.1.2: finitely many orbits of algebraic general-linear actions

This file states the dimension bound at the generality of the book.  For an
algebraic representation of `GL_m(k)` on a finite-dimensional vector space `V`,
finitely many orbits force

`finrank k V ≤ m²`.

The proof is the book's argument: a finite orbit decomposition of affine space
has an algebraically dense orbit, its orbit-map comorphism into
`k[GL_m] = k[Xᵢⱼ, det⁻¹]` is injective, and Problem 6.1.1 bounds the number of
source coordinates by the `m²` matrix-entry coordinates.  The final section
gives the corresponding finite-product statement.
-/

namespace Etingof.Problem6_1_2

open MvPolynomial MulAction
open Etingof.DetLocalization

variable {k : Type} [Field k]

/-! ## Affine-space density in basis coordinates -/

/-- Coordinates of a vector in a finite basis. -/
noncomputable def vectorCoords {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (v : V) : Fin d → k :=
  fun i => b.repr v i

/-- A subset of a finite-dimensional vector space is algebraically dense when
every polynomial vanishing on it in basis coordinates is zero. -/
def IsAlgDense {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (X : Set V) : Prop :=
  ∀ f : MvPolynomial (Fin d) k,
    (∀ v ∈ X, aeval (vectorCoords b v) f = 0) → f = 0

private noncomputable def vectorOfCoords {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (c : Fin d → k) : V :=
  b.repr.symm (Finsupp.equivFunOnFinite.symm c)

@[simp] private theorem vectorCoords_vectorOfCoords
    {V : Type*} [AddCommGroup V] [Module k V]
    {d : ℕ} (b : Module.Basis (Fin d) k V) (c : Fin d → k) :
    vectorCoords b (vectorOfCoords b c) = c := by
  funext i
  simp [vectorCoords, vectorOfCoords]

/-- Finitely many orbits on affine space give an algebraically dense orbit.
This is the coefficientwise form needed for the comorphism argument. -/
theorem exists_isAlgDense_orbit
    [Infinite k] {G V : Type*} [Group G] [AddCommGroup V] [Module k V] [MulAction G V]
    {d : ℕ} (b : Module.Basis (Fin d) k V)
    [Finite (orbitRel.Quotient G V)] :
    ∃ v₀ : V, IsAlgDense b (orbit G v₀) := by
  classical
  by_contra h
  push Not at h
  letI : Fintype (orbitRel.Quotient G V) := Fintype.ofFinite _
  have hw : ∀ q : orbitRel.Quotient G V,
      ∃ f : MvPolynomial (Fin d) k,
        (∀ v ∈ orbit G q.out, aeval (vectorCoords b v) f = 0) ∧ f ≠ 0 := by
    intro q
    have hq := h q.out
    unfold IsAlgDense at hq
    push Not at hq
    exact hq
  choose f hfvan hf0 using hw
  let F : MvPolynomial (Fin d) k := ∏ q : orbitRel.Quotient G V, f q
  have hFne : F ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => hf0 q
  apply hFne
  apply MvPolynomial.funext
  intro c
  rw [map_zero]
  let v := vectorOfCoords b c
  let q : orbitRel.Quotient G V := Quotient.mk'' v
  have hv : v ∈ orbit G q.out := by
    rw [← q.orbit_eq_orbit_out Quotient.out_eq', orbitRel.Quotient.orbit_mk]
    exact mem_orbit_self v
  have hzero : aeval (vectorCoords b v) (f q) = 0 := hfvan q v hv
  have hc : vectorCoords b v = c := vectorCoords_vectorOfCoords b c
  change eval c F = 0
  rw [← hc, show F = ∏ q : orbitRel.Quotient G V, f q from rfl, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ q) hzero

/-! ## A reusable orbit comorphism from regular matrix coefficients -/

section RegularCoefficients

variable {G V B : Type*} [Group G] [AddCommGroup V] [Module k V]
  [CommRing B] [Algebra k B] [MulAction G V]
  (ev : G → B →ₐ[k] k) (ρ : Representation k G V)
  {d : ℕ} (b : Module.Basis (Fin d) k V)
  (P : Fin d → Fin d → B)

/-- The comorphism of the orbit map `g ↦ ρ(g)v₀`, assembled from regular
matrix coefficients in the basis `b`. -/
noncomputable def orbitComorphism (v₀ : V) : MvPolynomial (Fin d) k →ₐ[k] B :=
  aeval fun a => ∑ c : Fin d, (b.repr v₀ c) • P a c

omit [MulAction G V] in
private theorem repr_apply_eq_sum (g : G) (v : V) (a : Fin d) :
    b.repr (ρ g v) a = ∑ c : Fin d, b.repr v c * b.repr (ρ g (b c)) a := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, LinearMapClass.map_smul]
  change (Finsupp.applyAddHom a) (∑ x, (b.repr v) x • b.repr (ρ g (b x))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change ((b.repr v c) • b.repr (ρ g (b c))) a = _
  rw [Finsupp.smul_apply, smul_eq_mul]

omit [MulAction G V] in
/-- Evaluating the orbit comorphism at a group element recovers the coordinates
of the actual orbit point. -/
theorem eval_comp_orbitComorphism
    (hP : ∀ (g : G) (a c : Fin d), b.repr (ρ g (b c)) a = ev g (P a c))
    (g : G) (v₀ : V) :
    (ev g).comp (orbitComorphism b P v₀) =
      aeval (vectorCoords b (ρ g v₀)) := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [AlgHom.comp_apply, orbitComorphism, aeval_X, aeval_X, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [vectorCoords, repr_apply_eq_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hP]

/-- Algebraic density of an orbit makes its orbit-map comorphism injective. -/
theorem injective_orbitComorphism_of_isAlgDense
    (hact : ∀ (g : G) (v : V), g • v = ρ g v)
    (hP : ∀ (g : G) (a c : Fin d), b.repr (ρ g (b c)) a = ev g (P a c))
    (v₀ : V)
    (hdense : IsAlgDense b (orbit G v₀)) :
    Function.Injective (orbitComorphism b P v₀) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply hdense
  intro v hv
  obtain ⟨g, rfl⟩ := mem_orbit_iff.mp hv
  have h := congrArg (ev g) hf
  rw [map_zero, ← AlgHom.comp_apply,
    eval_comp_orbitComorphism ev ρ b P hP] at h
  simpa only [hact] using h

end RegularCoefficients

/-! ## The canonical action attached to a representation -/

/-- A bundled representation supplies its canonical multiplicative action on
the underlying vector space.  Naming this instance lets orbit finiteness be
stated without asking callers to install a redundant action instance. -/
@[reducible] def representationMulAction
    {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : MulAction G V where
  smul := fun g v => ρ g v
  one_smul := by
    intro v
    change ρ 1 v = v
    rw [map_one]
    rfl
  mul_smul := by
    intro g h v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

/-- The orbit set for the canonical action supplied by a representation. -/
abbrev RepresentationOrbitQuotient
    {G V : Type*} [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) :=
  @orbitRel.Quotient G V _ (representationMulAction ρ)

/-! ## A single general linear group -/

/-- Evaluation of the determinant-localized coordinate ring at a point of `GL_n`. -/
noncomputable def evalGLAwayAt {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) k) :
    Localization.Away (detPoly k n) →ₐ[k] k where
  toFun := fun x => evalGLAway x g
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp
  commutes' := fun r => by
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin n × Fin n) k)
      (Localization.Away (detPoly k n)), evalGLAway_algebraMap]
    simp [evalGLHom_apply]

/-- The orbit comorphism attached to the coefficient witnesses in
`IsAlgebraicRepresentation`.  Its target is the honest coordinate ring
`k[GL_n] = k[Xᵢⱼ, det⁻¹]`, not a polynomial ring with an incorrectly independent
extra determinant-inverse variable. -/
noncomputable def glOrbitComorphism
    {V : Type*} [AddCommGroup V] [Module k V]
    {n d : ℕ}
    (b : Module.Basis (Fin d) k V)
    (P : Fin d → Fin d → MvPolynomial (Etingof.GLCoordVars n) k)
    (v₀ : V) :
    MvPolynomial (Fin d) k →ₐ[k] Localization.Away (detPoly k n) :=
  orbitComorphism b (fun a c => coordToAway (P a c)) v₀

/-- An algebraic `GL_n` representation with finitely many orbits has an
injective orbit-map comorphism into `k[GL_n]`. -/
theorem exists_injective_glOrbitComorphism
    [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (hρ : Etingof.IsAlgebraicRepresentation n ρ)
    [MulAction (Matrix.GeneralLinearGroup (Fin n) k) V]
    (hact : ∀ g v, g • v = ρ g v)
    [Finite (orbitRel.Quotient (Matrix.GeneralLinearGroup (Fin n) k) V)] :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) k V)
      (P : Fin d → Fin d → MvPolynomial (Etingof.GLCoordVars n) k)
      (v₀ : V),
      d = Module.finrank k V ∧
      Function.Injective (glOrbitComorphism b P v₀) := by
  classical
  obtain ⟨d, b, P, hP⟩ := hρ
  obtain ⟨v₀, hv₀⟩ :=
    exists_isAlgDense_orbit (G := Matrix.GeneralLinearGroup (Fin n) k) b
  refine ⟨d, b, P, v₀, ?_, ?_⟩
  · simpa using (Module.finrank_eq_card_basis b).symm
  apply injective_orbitComorphism_of_isAlgDense
    (ev := fun g => evalGLAwayAt g) ρ b (fun a c => coordToAway (P a c)) hact _ v₀ hv₀
  intro g a c
  change b.repr (ρ g (b c)) a = evalGLAway (coordToAway (P a c)) g
  rw [← evalAtGL_eq_evalGLAway_coordToAway]
  exact hP g a c

/-- **Problem 6.1.2, single-group form.** If an algebraic representation of
`GL_n(k)` has finitely many orbits, then `dim V ≤ n²`. -/
theorem finrank_le_sq_of_finite_orbits_of_compatible_action
    [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (hρ : Etingof.IsAlgebraicRepresentation n ρ)
    [MulAction (Matrix.GeneralLinearGroup (Fin n) k) V]
    (hact : ∀ g v, g • v = ρ g v)
    [Finite (orbitRel.Quotient (Matrix.GeneralLinearGroup (Fin n) k) V)] :
    Module.finrank k V ≤ n ^ 2 := by
  obtain ⟨d, b, P, v₀, hd, hφ⟩ :=
    exists_injective_glOrbitComorphism ρ hρ hact
  haveI : IsDomain (Localization.Away (detPoly k n)) :=
    IsLocalization.isDomain_localization (powers_detPoly_le_nonZeroDivisors (k := k) (N := n))
  have hle := Etingof.Problem6_1_5.dim_le_of_injective_comorphism_isLocalization_index
    (S := Submonoid.powers (detPoly k n)) (glOrbitComorphism b P v₀) hφ
  rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, hd] at hle
  simpa [pow_two] using hle

/-- **Problem 6.1.2, single-group form.** This is the book-facing statement:
the orbit quotient is formed from the representation's canonical action, so
the only mathematical inputs are algebraicity and finiteness of the orbit set. -/
theorem finrank_le_sq_of_finite_orbits
    [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {n : ℕ} (ρ : Representation k (Matrix.GeneralLinearGroup (Fin n) k) V)
    (hρ : Etingof.IsAlgebraicRepresentation n ρ)
    [Finite (RepresentationOrbitQuotient ρ)] :
    Module.finrank k V ≤ n ^ 2 := by
  letI : MulAction (Matrix.GeneralLinearGroup (Fin n) k) V :=
    representationMulAction ρ
  exact finrank_le_sq_of_finite_orbits_of_compatible_action ρ hρ (fun _ _ => rfl)

/-! ## Finite products of general linear groups -/

/-- Regularity of a representation of `∏ᵢ GL_{mᵢ}`.  Matrix coefficients are
elements of the principal-open coordinate ring obtained by inverting the
product of the generic determinants. -/
def IsAlgebraicProductRepresentation
    {r : ℕ} (m : Fin r → ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Etingof.repGroup k m) V) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) k V)
    (P : Fin d → Fin d →
      Localization.Away (Etingof.Problem6_1_5.detProd (k := k) m)),
    ∀ (g : Etingof.repGroup k m) (a c : Fin d),
      b.repr (ρ g (b c)) a =
        Etingof.Problem6_1_5.evalAt m g (P a c)

/-- **Problem 6.1.2, product form.** An algebraic representation of
`∏ᵢ GL_{mᵢ}(k)` with finitely many orbits satisfies
`dim V ≤ ∑ᵢ mᵢ²`. -/
theorem finrank_le_sum_sq_of_finite_orbits_of_compatible_action
    [Infinite k]
    {r : ℕ} (m : Fin r → ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Etingof.repGroup k m) V)
    [MulAction (Etingof.repGroup k m) V]
    (hact : ∀ g v, g • v = ρ g v)
    (hρ : IsAlgebraicProductRepresentation m ρ)
    [Finite (orbitRel.Quotient (Etingof.repGroup k m) V)] :
    Module.finrank k V ≤ ∑ i : Fin r, (m i) ^ 2 := by
  classical
  obtain ⟨d, b, P, hP⟩ := hρ
  obtain ⟨v₀, hv₀⟩ := exists_isAlgDense_orbit (G := Etingof.repGroup k m) b
  let φ := orbitComorphism b P v₀
  have hφ : Function.Injective φ :=
    injective_orbitComorphism_of_isAlgDense
      (ev := fun g => Etingof.Problem6_1_5.evalAt m g) ρ b P hact hP v₀ hv₀
  haveI : IsDomain
      (Localization.Away (Etingof.Problem6_1_5.detProd (k := k) m)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (Etingof.Problem6_1_5.detProd_ne_zero (k := k) m))
  have hle := Etingof.Problem6_1_5.dim_le_of_injective_comorphism_isLocalization_index
    (S := Submonoid.powers (Etingof.Problem6_1_5.detProd (k := k) m)) φ hφ
  rw [Fintype.card_fin, Etingof.Problem6_1_5.gIdx_card,
    show d = Module.finrank k V by simpa using (Module.finrank_eq_card_basis b).symm] at hle
  exact hle

/-- **Problem 6.1.2, finite-product form.** For the canonical action of an
algebraic representation of `∏ᵢ GL_{mᵢ}`, finite orbit type implies
`dim V ≤ ∑ᵢ mᵢ²`. -/
theorem finrank_le_sum_sq_of_finite_orbits
    [Infinite k]
    {r : ℕ} (m : Fin r → ℕ)
    {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k (Etingof.repGroup k m) V)
    (hρ : IsAlgebraicProductRepresentation m ρ)
    [Finite (RepresentationOrbitQuotient ρ)] :
    Module.finrank k V ≤ ∑ i : Fin r, (m i) ^ 2 := by
  letI : MulAction (Etingof.repGroup k m) V := representationMulAction ρ
  exact finrank_le_sum_sq_of_finite_orbits_of_compatible_action
    m ρ (fun _ _ => rfl) hρ

end Etingof.Problem6_1_2
