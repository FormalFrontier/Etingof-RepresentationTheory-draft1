import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.Algebra.DualNumber
import EtingofRepresentationTheory.Chapter2.Problem2_3_15
import EtingofRepresentationTheory.Chapter2.Definition2_3_8

/-!
# Problem 2.3.16: The central character

Let `A` be an algebra over a field `k`. The center `Z(A)` is the set of elements commuting
with all of `A`.

**(a)** If `V` is an irreducible finite dimensional representation of `A` (over an algebraically
closed field), then any `z ∈ Z(A)` acts on `V` by multiplication by a scalar `χ_V(z)`, and
`χ_V : Z(A) → k` is a homomorphism (the central character of `V`).

The scalar action is a direct consequence of Schur's lemma for algebraically closed fields
(Corollary 2.3.10 / `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`): a central element
`z` acts by an `A`-linear endomorphism (it commutes with the `A`-action), hence by a scalar. The
homomorphism property is captured by packaging the whole assignment `z ↦ χ_V(z)` as a `k`-algebra
homomorphism `centralCharacter : Z(A) →ₐ[k] k`.

**(b)** If `V` is an indecomposable finite dimensional representation of `A`, then for any
`z ∈ Z(A)` the operator `ρ(z)` has a single eigenvalue `χ_V(z)`, equal to the scalar by which
`z` acts on some irreducible subrepresentation of `V`; and `χ_V` is again a homomorphism.

The proof is the Fitting/generalized-eigenspace argument. Fix a simple subrepresentation `S ≤ V`
(Problem 2.3.15) and let `χ := χ_S(z)` be the scalar by which `z` acts on `S` (part (a)). A nonzero
vector of `S` is an eigenvector of `ρ(z)` for `χ`, so `g := ρ(z) - χ` has nonzero kernel. As `z`
is central, `g` is `A`-linear, so its Fitting decomposition `V = (⨆ₙ ker gⁿ) ⊕ (⨅ₙ range gⁿ)`
(`LinearMap.isCompl_iSup_ker_pow_iInf_range_pow`) is a decomposition into subrepresentations.
Indecomposability forces `⨅ₙ range gⁿ = 0`, hence `⨆ₙ ker gⁿ = V`, and finite-dimensionality then
gives `gᴺ = 0`: `ρ(z) - χ` is nilpotent, i.e. `χ` is the only eigenvalue. The eigenvalue is unique
(`Etingof.indecEigenvalue_unique`), so `χ_V := χ_S` is well defined independently of `S`, and it is
a homomorphism because `χ_S` is (part (a)).

**(c)** `ρ(z)` need not be a scalar operator: on the regular representation of the dual numbers
`k[ε]` (an indecomposable finite dimensional representation, since `k[ε]` is local), the central
element `ε` acts by a non-scalar nilpotent operator (`Etingof.eps_smul_not_scalar`).
-/

namespace Etingof

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The action of a central element `z ∈ Z(A)` on `V`, packaged as an `A`-linear endomorphism.
Because `z` commutes with every element of `A`, the map `v ↦ z • v` commutes with the
`A`-action, so it is `A`-linear. -/
def centralAction (z : Subalgebra.center k A) : Module.End A V where
  toFun v := (z : A) • v
  map_add' := smul_add _
  map_smul' a v := by
    change (z : A) • (a • v) = a • ((z : A) • v)
    rw [smul_smul, smul_smul, Subalgebra.mem_center_iff.mp z.2 a]

omit [Module k V] [IsScalarTower k A V] in
/-- Evaluating the central-action endomorphism is the original action by the central element. -/
@[simp]
theorem centralAction_apply (z : Subalgebra.center k A) (v : V) :
    centralAction z v = (z : A) • v := rfl

/-- The assignment `z ↦ (v ↦ z • v)` from the center of `A` to the `A`-linear endomorphisms of
`V`, as a `k`-algebra homomorphism. -/
def centralActionHom : Subalgebra.center k A →ₐ[k] Module.End A V where
  toFun := centralAction
  map_one' := by ext v; simp
  map_mul' z w := by
    ext v
    simp only [centralAction_apply, Module.End.mul_apply, Subalgebra.coe_mul, mul_smul]
  map_zero' := by ext v; simp
  map_add' z w := by ext v; simp [add_smul]
  commutes' r := by
    ext v
    simp only [centralAction_apply, Module.algebraMap_end_apply]
    exact algebraMap_smul A r v

variable [IsAlgClosed k] [IsSimpleModule A V] [FiniteDimensional k V]

/-- Schur's lemma (Corollary 2.3.10) packaged as a `k`-algebra isomorphism `k ≃ₐ End_A(V)`:
the algebra map `k → End_A(V)`, `c ↦ c • id`, is bijective. -/
noncomputable def endScalarEquiv : k ≃ₐ[k] Module.End A V :=
  AlgEquiv.ofBijective (Algebra.ofId k (Module.End A V))
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)

/-- Schur's scalar equivalence is the canonical algebra map in the forward direction. -/
@[simp]
theorem endScalarEquiv_apply (c : k) :
    endScalarEquiv (A := A) (V := V) c = algebraMap k (Module.End A V) c := rfl

/-- **The central character** `χ_V : Z(A) → k` of an irreducible finite dimensional
representation `V`, as a `k`-algebra homomorphism. (Etingof Problem 2.3.16(a))

It is defined by inverting Schur's isomorphism `k ≃ End_A(V)`: a central element `z` acts by a
scalar endomorphism, and `χ_V(z)` is that scalar. Being a composite of algebra homomorphisms it
is itself a homomorphism, which is the content of the second half of part (a). -/
noncomputable def centralCharacter : Subalgebra.center k A →ₐ[k] k :=
  (endScalarEquiv (k := k) (A := A) (V := V)).symm.toAlgHom.comp centralActionHom

/-- The defining property of the central character: every central element `z` acts on `V` by
multiplication by the scalar `χ_V(z)`. -/
theorem centralCharacter_smul (z : Subalgebra.center k A) (v : V) :
    (z : A) • v = centralCharacter (k := k) (V := V) z • v := by
  have h : endScalarEquiv (A := A) (V := V)
      (centralCharacter (k := k) (V := V) z) = centralActionHom (k := k) z :=
    endScalarEquiv.apply_symm_apply _
  rw [endScalarEquiv_apply] at h
  have hv := congrArg (fun f : Module.End A V => f v) h
  simp only [Module.algebraMap_end_apply] at hv
  -- `(centralActionHom z) v` is definitionally `(z : A) • v`
  exact hv.symm

/-- Part (a), existence form: any element of the center acts on an irreducible finite dimensional
representation by multiplication by some scalar. -/
theorem exists_central_scalar (z : Subalgebra.center k A) :
    ∃ c : k, ∀ v : V, (z : A) • v = c • v :=
  ⟨centralCharacter (k := k) (V := V) z, fun v => centralCharacter_smul z v⟩

/-!
## Part (b): the indecomposable case
-/

/- Indecomposability of a representation is `Etingof.IsIndecomposable` (Definition 2.3.8):
`V` is nonzero and admits no nontrivial direct-sum decomposition. -/
section Indecomposable

variable {k : Type*} [Field k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {V : Type*} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
variable [FiniteDimensional k V]

/-- **Single generalized eigenvalue (core of Problem 2.3.16(b)).** If `V` is an indecomposable
finite dimensional representation and `v₀ ≠ 0` is an eigenvector of `ρ(z)` with eigenvalue `χ`
(`z • v₀ = χ • v₀`), then `ρ(z) - χ` is nilpotent: `χ` is the only eigenvalue of `ρ(z)`.

Proof: `g := ρ(z) - χ` is `A`-linear with `v₀ ∈ ker g`, so `⨆ₙ ker gⁿ ≠ 0`; its Fitting
complement `⨅ₙ range gⁿ` is a subrepresentation, so by indecomposability it is `0`, forcing
`⨆ₙ ker gⁿ = V`; finite dimensionality then gives `gᴺ = 0`. -/
theorem centralAction_sub_smul_isNilpotent (hV : IsIndecomposable A V)
    (z : Subalgebra.center k A) {χ : k} {v₀ : V} (hv₀ : v₀ ≠ 0)
    (heig : (z : A) • v₀ = χ • v₀) :
    IsNilpotent (centralAction (V := V) z - χ • (1 : Module.End A V)) := by
  haveI : IsArtinian A V := isArtinian_of_tower k inferInstance
  haveI : IsNoetherian A V := isNoetherian_of_tower k inferInstance
  set g : Module.End A V := centralAction (V := V) z - χ • (1 : Module.End A V) with hg
  -- `v₀` lies in `ker g`.
  have hgv₀ : g v₀ = 0 := by
    simp only [hg, LinearMap.sub_apply, centralAction_apply, LinearMap.smul_apply,
      Module.End.one_apply, heig, sub_self]
  have hkerne : LinearMap.ker g ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨v₀, hgv₀, hv₀⟩
  -- Fitting decomposition of `V` with respect to `g`, as a decomposition into subrepresentations.
  have hcompl : IsCompl (⨆ n, LinearMap.ker (g ^ n)) (⨅ n, LinearMap.range (g ^ n)) :=
    LinearMap.isCompl_iSup_ker_pow_iInf_range_pow g
  have hker_le : LinearMap.ker g ≤ ⨆ n, LinearMap.ker (g ^ n) := by
    conv_lhs => rw [← pow_one g]
    exact le_iSup (fun n => LinearMap.ker (g ^ n)) 1
  have hsupne : (⨆ n, LinearMap.ker (g ^ n)) ≠ ⊥ := fun hbot =>
    hkerne (le_bot_iff.mp (hbot ▸ hker_le))
  -- Indecomposability kills the range part, so the kernel part is everything.
  rcases hV.2 _ _ hcompl with hP | hQ
  · exact absurd hP hsupne
  · have htop : (⨆ n, LinearMap.ker (g ^ n)) = ⊤ := by
      rw [hQ] at hcompl
      exact eq_top_of_isCompl_bot hcompl
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp g.eventually_iSup_ker_pow_eq
    have hkerN : LinearMap.ker (g ^ N) = ⊤ := by rw [← hN N le_rfl]; exact htop
    exact ⟨N, LinearMap.ker_eq_top.mp hkerN⟩

omit [FiniteDimensional k V] in
/-- A scalar operator `c • 1` on a nonzero representation is nilpotent only if `c = 0`. -/
theorem eq_zero_of_smul_one_isNilpotent [Nontrivial V] {c : k}
    (h : IsNilpotent (c • (1 : Module.End A V))) : c = 0 := by
  obtain ⟨m, hm⟩ := h
  -- Evaluate at a nonzero vector: `(c • 1)ᵐ v = cᵐ • v = 0`, so `cᵐ = 0`, so `c = 0`.
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hcmv : c ^ m • v = 0 := by
    have happ := LinearMap.congr_fun hm v
    rw [← Algebra.algebraMap_eq_smul_one, ← map_pow, Module.algebraMap_end_apply,
      LinearMap.zero_apply] at happ
    exact happ
  have hcm : c ^ m = 0 := (smul_eq_zero.mp hcmv).resolve_right hv
  have hm0 : m ≠ 0 := by rintro rfl; rw [pow_zero] at hcm; exact one_ne_zero hcm
  exact (pow_eq_zero_iff hm0).mp hcm

omit [FiniteDimensional k V] in
/-- **Uniqueness of the eigenvalue (Problem 2.3.16(b)).** On an indecomposable finite dimensional
representation the scalar `χ` with `ρ(z) - χ` nilpotent is unique; this is what makes the central
character `χ_V(z)` well defined. -/
theorem indecEigenvalue_unique (hV : IsIndecomposable A V) (z : Subalgebra.center k A) {χ χ' : k}
    (h : IsNilpotent (centralAction (V := V) z - χ • (1 : Module.End A V)))
    (h' : IsNilpotent (centralAction (V := V) z - χ' • (1 : Module.End A V))) : χ = χ' := by
  haveI : Nontrivial V := hV.1
  set a : Module.End A V := centralAction (V := V) z with ha
  -- `a - χ•1` and `a - χ'•1` commute (they differ by a central scalar), so their difference
  -- `(χ' - χ)•1` is nilpotent.
  have hcomm : Commute (a - χ • (1 : Module.End A V)) (a - χ' • (1 : Module.End A V)) := by
    have hrw : a - χ' • (1 : Module.End A V)
        = (a - χ • (1 : Module.End A V)) + (χ - χ') • (1 : Module.End A V) := by
      rw [sub_smul]; abel
    rw [hrw]
    refine (Commute.refl _).add_right ?_
    rw [show ((χ - χ') • (1 : Module.End A V)) = algebraMap k (Module.End A V) (χ - χ') from
      (Algebra.algebraMap_eq_smul_one _).symm]
    exact Algebra.commute_algebraMap_right _ _
  have hdiff : (a - χ • (1 : Module.End A V)) - (a - χ' • (1 : Module.End A V))
      = (χ' - χ) • (1 : Module.End A V) := by rw [sub_smul]; abel
  have hnil : IsNilpotent ((χ' - χ) • (1 : Module.End A V)) := by
    rw [← hdiff]; exact hcomm.isNilpotent_sub h h'
  have : χ' - χ = 0 := eq_zero_of_smul_one_isNilpotent hnil
  exact (sub_eq_zero.mp this).symm

variable [IsAlgClosed k]

/-- **Problem 2.3.16(b).** On an indecomposable finite dimensional representation `V` (over an
algebraically closed field) there is a `k`-algebra homomorphism `χ_V : Z(A) → k`, the central
character, such that for every `z ∈ Z(A)` the operator `ρ(z)` acts with the single eigenvalue
`χ_V(z)`, i.e. `ρ(z) - χ_V(z)` is nilpotent. It is realised as the central character (part (a)) of
any irreducible subrepresentation of `V`, so `χ_V(z)` is the scalar by which `z` acts there. -/
theorem exists_centralCharacter_isNilpotent (hV : IsIndecomposable A V) :
    ∃ χ_V : Subalgebra.center k A →ₐ[k] k, ∀ z : Subalgebra.center k A,
      IsNilpotent (centralAction (V := V) z - (χ_V z) • (1 : Module.End A V)) := by
  haveI : Nontrivial V := hV.1
  -- Pick an irreducible subrepresentation `S ≤ V` (Problem 2.3.15).
  obtain ⟨S, hS⟩ := exists_isSimpleModule_of_finite (k := k) (A := A) (V := V)
  haveI : IsSimpleModule A S := hS
  haveI : Nontrivial S := IsSimpleModule.nontrivial A S
  haveI : FiniteDimensional k S := (inferInstance : FiniteDimensional k (S.restrictScalars k))
  -- The central character of `S` is a `k`-algebra homomorphism (part (a)).
  refine ⟨centralCharacter (k := k) (V := S), fun z => ?_⟩
  set χ : k := centralCharacter (k := k) (V := S) z with hχ
  -- A nonzero vector of `S` is an eigenvector of `ρ(z)` on `V` with eigenvalue `χ`.
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
  have hv₀ : (s₀ : V) ≠ 0 := by simpa using hs₀
  have heig : (z : A) • (s₀ : V) = χ • (s₀ : V) := by
    have := centralCharacter_smul (k := k) (V := S) z s₀
    have h2 := congrArg (fun s : S => (s : V)) this
    simpa [hχ] using h2
  exact centralAction_sub_smul_isNilpotent hV z hv₀ heig

/-- **Problem 2.3.16(b), including the irreducible-subrepresentation clause.** There is an
irreducible subrepresentation `S ⊆ V` and a central character `χ_V : Z(A) → k` such that
every central action on `V` has the single generalized eigenvalue `χ_V(z)`, while its
restriction to `S` is literally the scalar action by `χ_V(z)`. This records the conjunct in
the source that is not visible in `exists_centralCharacter_isNilpotent`'s conclusion. -/
theorem exists_irreducibleSubrepresentation_centralCharacter
    (hV : IsIndecomposable A V) :
    ∃ S : Submodule A V, IsSimpleModule A S ∧
      ∃ χ_V : Subalgebra.center k A →ₐ[k] k,
        (∀ z : Subalgebra.center k A,
          IsNilpotent (centralAction (V := V) z - (χ_V z) • (1 : Module.End A V))) ∧
        ∀ (z : Subalgebra.center k A) (s : S),
          (z : A) • (s : V) = (χ_V z) • (s : V) := by
  haveI : Nontrivial V := hV.1
  obtain ⟨S, hS⟩ := exists_isSimpleModule_of_finite (k := k) (A := A) (V := V)
  haveI : IsSimpleModule A S := hS
  haveI : Nontrivial S := IsSimpleModule.nontrivial A S
  haveI : FiniteDimensional k S :=
    (inferInstance : FiniteDimensional k (S.restrictScalars k))
  let χ_V := centralCharacter (k := k) (A := A) (V := S)
  refine ⟨S, hS, χ_V, ?_, ?_⟩
  · intro z
    obtain ⟨s₀, hs₀⟩ := exists_ne (0 : S)
    have hv₀ : (s₀ : V) ≠ 0 := by simpa using hs₀
    have heig : (z : A) • (s₀ : V) = (χ_V z) • (s₀ : V) := by
      have h := centralCharacter_smul (k := k) (A := A) (V := S) z s₀
      exact congrArg (fun s : S => (s : V)) h
    exact centralAction_sub_smul_isNilpotent hV z hv₀ heig
  · intro z s
    have h := centralCharacter_smul (k := k) (A := A) (V := S) z s
    exact congrArg (fun t : S => (t : V)) h

end Indecomposable

/-!
## Part (c): `ρ(z)` need not be a scalar operator

The regular representation of the dual numbers `k[ε] = k[x]/(x²)` on itself is a two dimensional
indecomposable representation (`k[ε]` is a local ring). The element `ε` is central (the ring is
commutative) and nilpotent, and it acts on the regular representation by the non-scalar operator
`v ↦ ε · v`. So the single eigenvalue of part (b), here `χ_V(ε) = 0`, does not imply that
`ρ(z)` is a scalar operator.
-/

section DualNumberCounterexample

open DualNumber TrivSqZeroExt

variable {k : Type*} [Field k]

/-- The central element `ε` of the regular representation of the dual numbers `k[ε]`, as a member
of `Z(k[ε])` (which is all of `k[ε]`, since the ring is commutative). -/
def epsCenter : Subalgebra.center k (DualNumber k) :=
  ⟨ε, Subalgebra.mem_center_iff.mpr fun b => commute_eps_right b⟩

/-- The underlying dual number of `epsCenter` is `ε`. -/
@[simp] theorem epsCenter_coe : (epsCenter (k := k) : DualNumber k) = ε := rfl

/-- **Problem 2.3.16(c).** On the regular representation of the dual numbers `k[ε]`, the central
element `ε` does not act by a scalar operator: there is no `c : k` for which the operator
`ρ(ε) : v ↦ ε · v` equals the scalar operator `v ↦ c • v`. Together with part (b) (`ε` acts with
the single eigenvalue `0`), this shows a central element can act with a single eigenvalue without
acting by a scalar. -/
theorem eps_smul_not_scalar :
    ¬ ∃ c : k, ∀ v : DualNumber k, (ε : DualNumber k) * v = c • v := by
  rintro ⟨c, hc⟩
  -- Evaluate at `v = 1`: `ε = c • 1 = algebraMap k k[ε] c`.
  have h1 := hc 1
  rw [mul_one, Algebra.smul_def, mul_one] at h1
  -- Compare the `ε`-components: `1 = 0`.
  have h2 := congrArg TrivSqZeroExt.snd h1
  rw [snd_eps, algebraMap_eq_inl, snd_inl] at h2
  exact one_ne_zero h2

end DualNumberCounterexample

end Etingof
