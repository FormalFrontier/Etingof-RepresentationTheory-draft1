import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

set_option backward.isDefEq.respectTransparency false

/-!
# The horseshoe lemma

Given a short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in an abelian category with enough
projectives, and projective resolutions `P₁` of `X₁` and `P₃` of `X₃`, the **horseshoe lemma**
produces a projective resolution `P₂` of `X₂` whose terms are the biproducts
`P₂.X n = P₁.X n ⊞ P₃.X n`, together with a short exact sequence of chain complexes

`0 → P₁.complex →ᵅ P₂.complex →ᵝ P₃.complex → 0`

that is *degreewise split* (each degree is the split biproduct sequence
`0 → P₁ₙ → P₁ₙ ⊞ P₃ₙ → P₃ₙ → 0`) and lifts `S`, in the sense that the augmentations satisfy the
two compatibility squares
`α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f` and `β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g`.

This is the book's construction `P²ᵢ := P¹ᵢ ⊕ P³ᵢ` (Problem 8.2.6(v)), whose degreewise lifting
step is `Exercise_8_1_4`. It underlies the first-argument `Tor`/`Ext` long exact
sequences of Problem 8.2.6: because the sequence of complexes is degreewise split, it is
preserved by any additive functor (in particular `- ⊗_A N`), so applying such a functor and
taking homology yields the six-term homology window via
`CategoryTheory.ShortComplex.ShortExact.homology_exact₁/₂/₃`, with the objects identified with
left-derived functors through `CategoryTheory.ProjectiveResolution.isoLeftDerivedObj`.

## Construction (the standard horseshoe)

The augmentation compatibility squares in the conclusion are exactly the hypotheses required by
`ProjectiveResolution.isoLeftDerivedObj_hom_naturality` downstream, so they are stated as part of
the deliverable.

Write `S.f : X₁ ⟶ X₂`, `S.g : X₂ ⟶ X₃`, `ε₁ := P₁.π.f 0`, `ε₃ := P₃.π.f 0`,
`d¹ := P₁.complex.d`, `d³ := P₃.complex.d`.

* Terms: `P₂.X n := P₁.X n ⊞ P₃.X n`, with `α` degreewise `biprod.inl` and `β` degreewise
  `biprod.snd`. The degreewise sequence `0 → P₁ₙ → P₁ₙ ⊞ P₃ₙ → P₃ₙ → 0` is the split biproduct
  short exact sequence (`ShortComplex.Splitting`, hence `ShortExact`).
* Augmentation: choose a lift `h₀ : P₃₀ ⟶ X₂` of `ε₃` through the epi `S.g` (projectivity of
  `P₃₀`; `g ∘ h₀ = ε₃`). Set `ε₂ := biprod.desc (ε₁ ≫ S.f) h₀ : P₁₀ ⊞ P₃₀ ⟶ X₂`; it is epi and
  satisfies `α.f 0 ≫ ε₂ = ε₁ ≫ S.f` and `β.f 0 ≫ S.g ∘ ... = ...` giving the two squares.
* Differentials `d²ₙ = ⟪⟪d¹ₙ, sₙ⟫, ⟪0, d³ₙ⟫⟫`, the upper triangular biproduct matrix
  `[[d¹, s], [0, d³]]` (zero below the diagonal), with
  off-diagonal lift `sₙ : P₃ₙ ⟶ P₁_{n-1}` built by induction: projectivity of `P₃ₙ` against the
  epi `d¹_{n-1} : P₁ₙ ↠ ker …` (equivalently `Exercise_8_1_4`) produces `sₙ` making
  `d¹_{n-1} ≫ sₙ = - sₙ₋₁ ≫ d³ₙ` and `ε₂`-compatibility hold; this uses the exactness of the
  *given* resolutions `P₁`, `P₃`, not of the complex being built.
* `P₂` is a resolution: the sequence of complexes is short exact, `P₁`, `P₃` are exact off
  degree `0` and resolve `X₁`, `X₃`, so the homology long exact sequence (together with `hS`
  in degree `0`) forces `P₂.complex` exact off degree `0` with `H₀ = X₂`; each `P₂.X n` is
  projective as a biproduct of projectives.

The resolution data is built explicitly: the twisted differential `horseshoeD` carrying the
inductive off-diagonal lift `horseshoeTwist`, the augmentation `horseshoeπ`, and the chain maps
`horseshoeα`, `horseshoeβ`. The associated obligations are `d ≫ d = 0`
(`horseshoeD_comp_horseshoeD`), the chain-map laws, the `QuasiIso` of the augmentation
(`horseshoeπ_quasiIso`), and the degreewise-split `ShortExact`
(`horseshoeShortComplex_shortExact`).
-/

universe v u

open CategoryTheory Category Limits

namespace Etingof

section Augmentation

variable {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)

/-- The degree-`0` augmentation of the horseshoe resolution of `S.X₂`, on the biproduct
`P₁.complex.X 0 ⊞ P₃.complex.X 0`. On the `P₁` summand it is `P₁.π.f 0 ≫ S.f`; on the `P₃`
summand it is a lift of `P₃.π.f 0` through the epimorphism `S.g` (which exists because
`P₃.complex.X 0` is projective). This is the base case of the horseshoe augmentation; the two
compatibility squares of the horseshoe lemma reduce to `horseshoeπZero_inl` and
`horseshoeπZero_comp_g` in degree `0`. -/
noncomputable def horseshoeπZero :
    P₁.complex.X 0 ⊞ P₃.complex.X 0 ⟶ S.X₂ :=
  haveI := hS.epi_g
  biprod.desc (P₁.π.f 0 ≫ S.f) (Projective.factorThru (P₃.π.f 0) S.g)

@[reassoc (attr := simp)]
lemma horseshoeπZero_inl :
    biprod.inl ≫ horseshoeπZero hS P₁ P₃ = P₁.π.f 0 ≫ S.f := by
  simp [horseshoeπZero]

/-- The `P₃`-summand of the horseshoe augmentation covers `P₃.π.f 0` after `S.g`. -/
@[reassoc (attr := simp)]
lemma horseshoeπZero_inr_comp_g :
    haveI := hS.epi_g
    (biprod.inr ≫ horseshoeπZero hS P₁ P₃) ≫ S.g = P₃.π.f 0 := by
  haveI := hS.epi_g
  simp [horseshoeπZero, Projective.factorThru_comp]

/-- The second augmentation-compatibility square in degree `0`:
`biprod.snd ≫ P₃.π.f 0 = horseshoeπZero ≫ S.g` (with `β.f 0 = biprod.snd`,
`P₂.π.f 0 = horseshoeπZero`). Uses `S.f ≫ S.g = 0` to kill the `P₁` summand. -/
@[reassoc]
lemma horseshoeπZero_comp_g :
    horseshoeπZero hS P₁ P₃ ≫ S.g = biprod.snd ≫ P₃.π.f 0 := by
  haveI := hS.epi_g
  ext
  · simp [horseshoeπZero]
  · simp [horseshoeπZero, Projective.factorThru_comp]

/-! ### The twisted differential and the horseshoe chain complex

We now construct the *data* of the horseshoe resolution `P₂` of `S.X₂`: the terms
`P₁.X n ⊞ P₃.X n`, the upper-triangular twisted differential `⟪⟪d¹, s⟫, ⟪0, d³⟫⟫`, and the
off-diagonal lift family `s` built by induction against the exactness of the *given* resolutions
`P₁`, `P₃`. -/

/-- Degree-`0` exactness of the augmented resolution `P₁`:
`P₁.complex.X 1 →(d 1 0) P₁.complex.X 0 →(π 0) S.X₁` is exact, because `S.X₁` is the cokernel of
`d 1 0` (`ProjectiveResolution.isColimitCokernelCofork`). -/
lemma horseshoeP₁ExactZero :
    (ShortComplex.mk (P₁.complex.d 1 0) (P₁.π.f 0) P₁.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P₁.isColimitCokernelCofork

/-- The seed map `t₀ : P₃₁ ⟶ S.X₁` of the horseshoe off-diagonal lift. Writing
`h₀ := factorThru (P₃.π.f 0) S.g` (so `h₀ ≫ S.g = P₃.π.f 0`), the map `-(d³ 1 0) ≫ h₀` dies under
`S.g`, hence factors through the mono `S.f` by exactness of `S`. -/
noncomputable def horseshoeSeed : P₃.complex.X 1 ⟶ S.X₁ :=
  haveI := hS.epi_g
  haveI := hS.mono_f
  hS.exact.lift (-(P₃.complex.d 1 0) ≫ Projective.factorThru (P₃.π.f 0) S.g) (by
    haveI := hS.epi_g
    simp [Projective.factorThru_comp, P₃.complex_d_comp_π_f_zero])

/-- `t₀ ≫ S.f = -(d³ 1 0) ≫ h₀`, the defining property of the seed. -/
@[reassoc] lemma horseshoeSeed_comp_f :
    haveI := hS.epi_g
    horseshoeSeed hS P₃ ≫ S.f
      = -(P₃.complex.d 1 0) ≫ Projective.factorThru (P₃.π.f 0) S.g := by
  haveI := hS.epi_g
  haveI := hS.mono_f
  exact hS.exact.lift_f _ _

/-- `d³ 2 1 ≫ t₀ = 0`, using `S.f` mono and `d³ 2 1 ≫ d³ 1 0 = 0`. -/
lemma horseshoeSeed_comp_d :
    P₃.complex.d 2 1 ≫ horseshoeSeed hS P₃ = 0 := by
  haveI := hS.mono_f
  rw [← cancel_mono S.f, zero_comp, assoc, horseshoeSeed_comp_f]
  simp [P₃.complex.d_comp_d_assoc]

/-- The degree-`0` off-diagonal lift `s₀ : P₃₁ ⟶ P₁₀`, lifting the seed `t₀` through the epi
`P₁.π.f 0`. -/
noncomputable def horseshoeTwistZero : P₃.complex.X 1 ⟶ P₁.complex.X 0 :=
  Projective.factorThru (horseshoeSeed hS P₃) (P₁.π.f 0)

/-- `s₀ ≫ P₁.π.f 0 = t₀`. -/
@[reassoc] lemma horseshoeTwistZero_comp_π :
    horseshoeTwistZero hS P₁ P₃ ≫ P₁.π.f 0 = horseshoeSeed hS P₃ :=
  Projective.factorThru_comp _ _

/-- Auxiliary recursion for the horseshoe off-diagonal lift. For each `n` it produces a pair of
consecutive lift maps `sₙ : P₃_{n+1} ⟶ P₁_n` (first component) and `sₙ₊₁ : P₃_{n+2} ⟶ P₁_{n+1}`
(second component) satisfying the twist relation
`sₙ₊₁ ≫ d¹_{n+1,n} = -(d³_{n+2,n+1}) ≫ sₙ`.

The base pair `(s₀, s₁)` is seeded by the augmentation: `s₀` lifts, through the epi `P₁.π.f 0`,
a factorisation of `-(d³_{1,0}) ≫ h₀` through the mono `S.f` (where `h₀ := factorThru (P₃.π.f 0)
S.g`); `s₁` then lifts through `d¹_{1,0}` using degree-`0` exactness of `P₁`. Each subsequent
`sₙ₊₂` lifts `-(d³) ≫ sₙ₊₁` through `d¹` using `ProjectiveResolution.exact_succ`, the twist
relation of the previous step discharging the required vanishing. -/
noncomputable def horseshoeTwistAux :
    ∀ n, Σ' (a : P₃.complex.X (n + 1) ⟶ P₁.complex.X n)
      (_b : P₃.complex.X (n + 2) ⟶ P₁.complex.X (n + 1)),
        _b ≫ P₁.complex.d (n + 1) n = -(P₃.complex.d (n + 2) (n + 1)) ≫ a
  | 0 =>
      ⟨horseshoeTwistZero hS P₁ P₃,
        (horseshoeP₁ExactZero P₁).liftFromProjective
          (-(P₃.complex.d 2 1) ≫ horseshoeTwistZero hS P₁ P₃) (by
            simp [horseshoeTwistZero_comp_π, horseshoeSeed_comp_d]),
        (horseshoeP₁ExactZero P₁).liftFromProjective_comp _ _⟩
  | n + 1 => by
      -- `(a, b, hab)` are `(sₙ, sₙ₊₁, twist relation)`; build `sₙ₊₂` and return `(sₙ₊₁, sₙ₊₂, …)`.
      set a := (horseshoeTwistAux n).1 with hadef
      set b := (horseshoeTwistAux n).2.1 with hbdef
      have hab : b ≫ P₁.complex.d (n + 1) n = -(P₃.complex.d (n + 2) (n + 1)) ≫ a :=
        (horseshoeTwistAux n).2.2
      have hk : (-(P₃.complex.d (n + 3) (n + 2)) ≫ b) ≫ P₁.complex.d (n + 1) n = 0 := by
        simp [hab, P₃.complex.d_comp_d_assoc]
      exact ⟨b, (P₁.exact_succ n).liftFromProjective (-(P₃.complex.d (n + 3) (n + 2)) ≫ b) hk,
        (P₁.exact_succ n).liftFromProjective_comp _ _⟩

/-- The horseshoe off-diagonal lift `sₙ : P₃_{n+1} ⟶ P₁_n`. -/
noncomputable def horseshoeTwist (n : ℕ) : P₃.complex.X (n + 1) ⟶ P₁.complex.X n :=
  (horseshoeTwistAux hS P₁ P₃ n).1

/-- `sₙ₊₁ = (horseshoeTwistAux n).2.1`: the second component of the aux at level `n` is the map at
level `n + 1`. -/
lemma horseshoeTwist_succ (n : ℕ) :
    horseshoeTwist hS P₁ P₃ (n + 1) = (horseshoeTwistAux hS P₁ P₃ n).2.1 := rfl

/-- The defining twist relation: `sₙ₊₁ ≫ d¹_{n+1,n} = -(d³_{n+2,n+1}) ≫ sₙ`. -/
@[reassoc]
lemma horseshoeTwist_comp (n : ℕ) :
    horseshoeTwist hS P₁ P₃ (n + 1) ≫ P₁.complex.d (n + 1) n
      = -(P₃.complex.d (n + 2) (n + 1)) ≫ horseshoeTwist hS P₁ P₃ n := by
  rw [horseshoeTwist_succ]; exact (horseshoeTwistAux hS P₁ P₃ n).2.2

/-- `s₀ = horseshoeTwistZero`: the degree-`0` off-diagonal lift agrees with its seeded form. -/
lemma horseshoeTwist_zero : horseshoeTwist hS P₁ P₃ 0 = horseshoeTwistZero hS P₁ P₃ := rfl

/-- The degree-`0` augmentation compatibility of the off-diagonal lift:
`s₀ ≫ (ε₁ ≫ S.f) = -(d³ 1 0) ≫ h₀`. This is the relation making the twisted differential a chain
map for the augmentation in degree `0`. -/
@[reassoc] lemma horseshoeTwist_zero_comp_f :
    haveI := hS.epi_g
    horseshoeTwist hS P₁ P₃ 0 ≫ P₁.π.f 0 ≫ S.f
      = -(P₃.complex.d 1 0) ≫ Projective.factorThru (P₃.π.f 0) S.g := by
  haveI := hS.epi_g
  rw [horseshoeTwist_zero, ← assoc, horseshoeTwistZero_comp_π, horseshoeSeed_comp_f]

/-- The upper-triangular twisted differential
`d²ₙ = ⟪⟪d¹ₙ, sₙ⟫, ⟪0, d³ₙ⟫⟫ : P₁_{n+1} ⊞ P₃_{n+1} ⟶ P₁_n ⊞ P₃_n` (matrix `[[d¹, s], [0, d³]]`,
zero below the diagonal). -/
noncomputable def horseshoeD (n : ℕ) :
    P₁.complex.X (n + 1) ⊞ P₃.complex.X (n + 1) ⟶ P₁.complex.X n ⊞ P₃.complex.X n :=
  biprod.lift (biprod.desc (P₁.complex.d (n + 1) n) (horseshoeTwist hS P₁ P₃ n))
    (biprod.desc 0 (P₃.complex.d (n + 1) n))

@[reassoc (attr := simp)] lemma horseshoeD_fst (n : ℕ) :
    horseshoeD hS P₁ P₃ n ≫ biprod.fst
      = biprod.desc (P₁.complex.d (n + 1) n) (horseshoeTwist hS P₁ P₃ n) := by
  simp [horseshoeD]

@[reassoc (attr := simp)] lemma horseshoeD_snd (n : ℕ) :
    horseshoeD hS P₁ P₃ n ≫ biprod.snd = biprod.desc 0 (P₃.complex.d (n + 1) n) := by
  simp [horseshoeD]

@[reassoc (attr := simp)] lemma horseshoeD_inl (n : ℕ) :
    biprod.inl ≫ horseshoeD hS P₁ P₃ n = biprod.lift (P₁.complex.d (n + 1) n) 0 := by
  apply biprod.hom_ext <;> simp

@[reassoc (attr := simp)] lemma horseshoeD_inr (n : ℕ) :
    biprod.inr ≫ horseshoeD hS P₁ P₃ n
      = biprod.lift (horseshoeTwist hS P₁ P₃ n) (P₃.complex.d (n + 1) n) := by
  apply biprod.hom_ext <;> simp

/-- The twisted differential squares to zero; the only nontrivial corner (`P₃ → P₁`) is exactly the
twist relation `horseshoeTwist_comp`. -/
lemma horseshoeD_comp_horseshoeD (n : ℕ) :
    horseshoeD hS P₁ P₃ (n + 1) ≫ horseshoeD hS P₁ P₃ n = 0 := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp [horseshoeTwist_comp, biprod.lift_desc, P₁.complex.d_comp_d, P₃.complex.d_comp_d]

/-- The horseshoe chain complex `P₂` with terms `P₁.X n ⊞ P₃.X n` and the twisted differential. -/
noncomputable def horseshoeComplex : ChainComplex C ℕ :=
  ChainComplex.of (fun n => P₁.complex.X n ⊞ P₃.complex.X n) (horseshoeD hS P₁ P₃)
    (horseshoeD_comp_horseshoeD hS P₁ P₃)

instance horseshoeComplex_projective (n : ℕ) :
    Projective ((horseshoeComplex hS P₁ P₃).X n) := by
  dsimp [horseshoeComplex, ChainComplex.of]
  infer_instance

/-- The degree-`0` chain-map condition for the augmentation: `d²₁₀ ≫ ε₂ = 0`. The `P₁` corner is
`d¹₁₀ ≫ ε₁ ≫ S.f = 0` (`P₁` augmented complex is a complex), the `P₃` corner is the seed relation
`horseshoeTwist_zero_comp_f`. -/
lemma horseshoeD_zero_comp_π :
    horseshoeD hS P₁ P₃ 0 ≫ horseshoeπZero hS P₁ P₃ = 0 := by
  haveI := hS.epi_g
  apply biprod.hom_ext'
  · rw [horseshoeD_inl_assoc, comp_zero]
    simp only [horseshoeπZero, biprod.lift_desc, zero_comp, add_zero]
    rw [← assoc, P₁.complex_d_comp_π_f_zero, zero_comp]
  · rw [horseshoeD_inr_assoc, comp_zero]
    simp only [horseshoeπZero, biprod.lift_desc]
    rw [horseshoeTwist_zero_comp_f]
    simp

/-! ### The chain maps and the degreewise-split short exact sequence

The horseshoe complex sits in a short exact sequence of complexes
`0 → P₁.complex →ᵅ horseshoeComplex →ᵝ P₃.complex → 0`, with `α` the degreewise `biprod.inl` and
`β` the degreewise `biprod.snd`. Each degree is the split biproduct short exact sequence, so the
whole sequence is degreewise split and hence `ShortExact`. -/

/-- The horseshoe chain map `α : P₁.complex ⟶ horseshoeComplex`, degreewise `biprod.inl`. The
chain-map square holds because the twisted differential is upper triangular, so its `P₁` column
has no `P₃` component: `biprod.inl ≫ horseshoeD n = biprod.lift d¹ 0 = d¹ ≫ biprod.inl`. -/
noncomputable def horseshoeα : P₁.complex ⟶ horseshoeComplex hS P₁ P₃ :=
  ChainComplex.ofHom
    (fun i => (biprod.inl : P₁.complex.X i ⟶ P₁.complex.X i ⊞ P₃.complex.X i))
    (fun n => by
      simp only [horseshoeComplex, ChainComplex.of_d, horseshoeD_inl]
      apply biprod.hom_ext <;> simp)

/-- The horseshoe chain map `β : horseshoeComplex ⟶ P₃.complex`, degreewise `biprod.snd`. The
chain-map square holds because `horseshoeD n ≫ biprod.snd = biprod.desc 0 d³ = biprod.snd ≫ d³`. -/
noncomputable def horseshoeβ : horseshoeComplex hS P₁ P₃ ⟶ P₃.complex :=
  ChainComplex.ofHom
    (fun i => (biprod.snd : P₁.complex.X i ⊞ P₃.complex.X i ⟶ P₃.complex.X i))
    (fun n => by
      simp only [horseshoeComplex, ChainComplex.of_d, horseshoeD_snd]
      apply biprod.hom_ext' <;> simp)

@[simp] lemma horseshoeα_f (i : ℕ) :
    (horseshoeα hS P₁ P₃).f i
      = (biprod.inl : P₁.complex.X i ⟶ P₁.complex.X i ⊞ P₃.complex.X i) := rfl

@[simp] lemma horseshoeβ_f (i : ℕ) :
    (horseshoeβ hS P₁ P₃).f i
      = (biprod.snd : P₁.complex.X i ⊞ P₃.complex.X i ⟶ P₃.complex.X i) := rfl

/-- `α ≫ β = 0`, degreewise `biprod.inl ≫ biprod.snd = 0`. -/
lemma horseshoeα_comp_horseshoeβ :
    horseshoeα hS P₁ P₃ ≫ horseshoeβ hS P₁ P₃ = 0 := by
  ext n
  simp

/-- The horseshoe short complex of chain complexes
`0 → P₁.complex → horseshoeComplex → P₃.complex → 0`. -/
noncomputable def horseshoeShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (horseshoeα hS P₁ P₃) (horseshoeβ hS P₁ P₃) (horseshoeα_comp_horseshoeβ hS P₁ P₃)

/-- The explicit degreewise splitting of the horseshoe short complex: in each degree `i` it is the
split biproduct sequence `0 → P₁ᵢ → P₁ᵢ ⊞ P₃ᵢ → P₃ᵢ → 0`. Keeping the splitting explicit lets a
downstream additive functor transport it, so the image sequence stays short exact. -/
noncomputable def horseshoeSplitting (i : ℕ) :
    ((horseshoeShortComplex hS P₁ P₃).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) i)).Splitting :=
  ShortComplex.Splitting.ofHasBinaryBiproduct (P₁.complex.X i) (P₃.complex.X i)

/-- **The horseshoe short exact sequence of complexes.** Degreewise it is the split biproduct
sequence, hence short exact in each degree, hence short exact as a sequence of complexes. -/
lemma horseshoeShortComplex_shortExact :
    (horseshoeShortComplex hS P₁ P₃).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => (horseshoeSplitting hS P₁ P₃ i).shortExact)

/-! ### The augmentation and its quasi-isomorphism -/

/-- The augmentation `π₂ : horseshoeComplex ⟶ single₀ S.X₂`, with degree-`0` component
`horseshoeπZero` and higher components `0`. -/
noncomputable def horseshoeπ :
    horseshoeComplex hS P₁ P₃ ⟶ (ChainComplex.single₀ C).obj S.X₂ :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨horseshoeπZero hS P₁ P₃, by
      have hd : (horseshoeComplex hS P₁ P₃).d 1 0 = horseshoeD hS P₁ P₃ 0 := by
        simp only [horseshoeComplex]; exact ChainComplex.of_d _ _ 0
      rw [hd, horseshoeD_zero_comp_π]⟩

@[simp] lemma horseshoeπ_f_zero :
    (horseshoeπ hS P₁ P₃).f 0 = horseshoeπZero hS P₁ P₃ := by
  simp [horseshoeπ]

@[simp] lemma horseshoeπ_f_succ (n : ℕ) :
    (horseshoeπ hS P₁ P₃).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 S.X₂ (n + 1)
    (by simp)).eq_of_tgt _ _

/-- `S` placed in degree `0` as a short complex of chain complexes. -/
noncomputable def horseshoeSingle : ShortComplex (ChainComplex C ℕ) :=
  S.map (ChainComplex.single₀ C)

include hS in
/-- `single₀` is exact, so `S` placed in degree `0` stays short exact. -/
lemma horseshoeSingle_shortExact : (horseshoeSingle (S := S)).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS (ChainComplex.single₀ C)

/-- The morphism of short complexes of chain complexes from the horseshoe SES to `S` in degree `0`,
with vertical maps the augmentations `P₁.π`, `horseshoeπ`, `P₃.π`. The two nontrivial squares are
the augmentation-compatibility squares `horseshoeπZero_inl` and `horseshoeπZero_comp_g`. -/
noncomputable def horseshoeMorphism :
    horseshoeShortComplex hS P₁ P₃ ⟶ horseshoeSingle (S := S) :=
  ShortComplex.homMk P₁.π (horseshoeπ hS P₁ P₃) P₃.π
    (by
      apply HomologicalComplex.hom_ext; intro n
      obtain _ | n := n <;>
        simp [horseshoeShortComplex, horseshoeSingle, ShortComplex.map])
    (by
      apply HomologicalComplex.hom_ext; intro n
      obtain _ | n := n <;>
        simp [horseshoeShortComplex, horseshoeSingle, ShortComplex.map, horseshoeπZero_comp_g])

/-- The horseshoe augmentation is a quasi-isomorphism: off degree `0` both complexes are exact
(`horseshoeComplex` by `exactAt_X₂` from the horseshoe SES and exactness of `P₁`, `P₃`), and in
degree `0` the induced map on homology is an isomorphism by the middle three-lemma applied to the
map of homology short complexes (the outer verticals `homologyMap P₁.π 0`, `homologyMap P₃.π 0` are
isomorphisms because `P₁`, `P₃` are resolutions). -/
instance horseshoeπ_quasiIso : QuasiIso (horseshoeπ hS P₁ P₃) := by
  have hS₁ := horseshoeShortComplex_shortExact hS P₁ P₃
  have hS₂ := horseshoeSingle_shortExact hS
  rw [quasiIso_iff]
  rintro (_ | n)
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have hmono : Mono (HomologicalComplex.homologyMap (horseshoeSingle (S := S)).f 0) := by
      haveI := hS.mono_f
      refine (hS₂.homology_exact₁ 1 0 (by simp)).mono_g ?_
      exact (HomologicalComplex.isZero_single_obj_homology _ 0 S.X₃ 1 (by norm_num)).eq_of_src _ _
    have hepi : Epi (HomologicalComplex.homologyMap (horseshoeShortComplex hS P₁ P₃).g 0) := by
      haveI := hS₁.epi_g
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
    haveI : Mono (HomologicalComplex.homologyMap (horseshoeπ hS P₁ P₃) 0) :=
      ShortComplex.mono_of_mono_of_mono_of_mono
        ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) 0).mapShortComplex.map
          (horseshoeMorphism hS P₁ P₃)) (hS₁.homology_exact₂ 0) hmono
        (inferInstanceAs (Mono (HomologicalComplex.homologyMap P₁.π 0)))
        (inferInstanceAs (Mono (HomologicalComplex.homologyMap P₃.π 0)))
    haveI : Epi (HomologicalComplex.homologyMap (horseshoeπ hS P₁ P₃) 0) :=
      ShortComplex.epi_of_epi_of_epi_of_epi
        ((HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) 0).mapShortComplex.map
          (horseshoeMorphism hS P₁ P₃)) (hS₂.homology_exact₂ 0) hepi
        (inferInstanceAs (Epi (HomologicalComplex.homologyMap P₁.π 0)))
        (inferInstanceAs (Epi (HomologicalComplex.homologyMap P₃.π 0)))
    exact isIso_of_mono_of_epi _
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
    exact hS₁.exactAt_X₂ (n + 1) (P₁.complex_exactAt_succ n) (P₃.complex_exactAt_succ n)

/-- The horseshoe projective resolution of `S.X₂`. -/
noncomputable def horseshoeResolution : ProjectiveResolution S.X₂ where
  complex := horseshoeComplex hS P₁ P₃
  π := horseshoeπ hS P₁ P₃

end Augmentation

/-- **The horseshoe lemma.** A short exact sequence `S : 0 → X₁ → X₂ → X₃ → 0` in an abelian
category with enough projectives, together with projective resolutions `P₁` of `X₁` and `P₃` of
`X₃`, gives a projective resolution `P₂` of `X₂` and chain maps
`α : P₁.complex ⟶ P₂.complex`, `β : P₂.complex ⟶ P₃.complex` forming a short exact sequence of
complexes lifting `S`: the augmentation squares `α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f` and
`β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g` commute. (In the intended construction `P₂` has terms
`P₁.X n ⊞ P₃.X n` and the sequence of complexes is degreewise split, hence preserved by any
additive functor.) -/
theorem horseshoe {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃) :
    ∃ (P₂ : ProjectiveResolution S.X₂)
      (α : P₁.complex ⟶ P₂.complex) (β : P₂.complex ⟶ P₃.complex)
      (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
      α.f 0 ≫ P₂.π.f 0 = P₁.π.f 0 ≫ S.f ∧
      β.f 0 ≫ P₃.π.f 0 = P₂.π.f 0 ≫ S.g :=
  ⟨horseshoeResolution hS P₁ P₃, horseshoeα hS P₁ P₃, horseshoeβ hS P₁ P₃,
    horseshoeα_comp_horseshoeβ hS P₁ P₃, horseshoeShortComplex_shortExact hS P₁ P₃,
    by simp [horseshoeResolution],
    by simp [horseshoeResolution, horseshoeπZero_comp_g]⟩

end Etingof
