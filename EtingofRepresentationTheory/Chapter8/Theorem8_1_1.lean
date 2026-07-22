import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Theorem 8.1.1: Equivalent characterizations of projective modules

The following properties of P are equivalent:

(i) If α : M → N is a surjective morphism and ν : P → N is any morphism, then there exists
a morphism μ : P → M such that α ∘ μ = ν.

(ii) Any surjective morphism α : M → P splits; i.e., there exists μ : P → M such that
α ∘ μ = id.

(iii) There exists another A-module Q such that P ⊕ Q is a free A-module.

(iv) The functor Hom_A(P, ?) on the category of A-modules is exact.

## Mathlib correspondence

`Module.Projective` captures condition (i) (the lifting property). The equivalences with
splitting, direct summand of free, and exactness of Hom are available in various forms
across Mathlib's module theory.

- `Module.projective_lifting_property` : (i) follows from `Module.Projective`
- `Module.Projective.of_lifting_property` : `Module.Projective` follows from (i)
- `LinearMap.exists_rightInverse_of_surjective` : (ii) follows from `Module.Projective`
- `Module.Projective.iff_split` : equivalence with (iii)

Condition (iv) — exactness of the functor `Hom_A(P, ?)` — is formalized as preservation of
short exact sequences: for every short exact sequence `0 → K → M → N → 0`, applying
`Hom_A(P, ?)` yields a short exact sequence `0 → Hom(P,K) → Hom(P,M) → Hom(P,N) → 0`. The
left-exact part (injectivity at `Hom(P,K)` and exactness at `Hom(P,M)`) holds for every `P`;
the right-exact part (surjectivity onto `Hom(P,N)`) is precisely projectivity.
-/

universe u v

/-- **Part (i) ↔ (ii)**: P is projective (lifting property) if and only if every surjection
onto P splits.
(Etingof Theorem 8.1.1, equivalence of conditions (i) and (ii)) -/
theorem Etingof.Theorem_8_1_1_i_iff_ii
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Small.{v} R] :
    Module.Projective R P ↔
      (∀ {M : Type v} [AddCommGroup M] [Module R M]
        (f : M →ₗ[R] P), Function.Surjective f →
          ∃ g : P →ₗ[R] M, f.comp g = LinearMap.id) := by
  constructor
  · intro hP M _ _ f hf
    exact LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hf)
  · intro h
    refine Module.Projective.of_lifting_property'' (fun p hp ↦ ?_)
    let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
    obtain ⟨g, hg⟩ := h (p ∘ₗ e.toLinearMap) (hp.comp e.surjective)
    exact ⟨e.toLinearMap ∘ₗ g, hg⟩

/-- **Part (i) ↔ (iii)**: P is projective if and only if P is a direct summand of a
free module.
(Etingof Theorem 8.1.1, equivalence of conditions (i) and (iii)) -/
theorem Etingof.Theorem_8_1_1_i_iff_iii
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔
      (∃ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.Free R Q) (i : P →ₗ[R] Q) (s : Q →ₗ[R] P),
          s.comp i = LinearMap.id) := by
  constructor
  · intro hP
    obtain ⟨s, hs⟩ := hP.out
    exact ⟨P →₀ R, inferInstance, inferInstance, inferInstance, s,
      Finsupp.linearCombination R id, LinearMap.ext hs⟩
  · intro ⟨_, _, _, _, i, s, his⟩
    exact Module.Projective.of_split i s his

/-- **Part (i) ↔ (iv)**: P is projective if and only if the functor `Hom_A(P, ?)` is exact.

Exactness of `Hom_A(P, ?)` is formalized as preservation of short exact sequences: for every
short exact sequence `0 → K →[ι] M →[π] N → 0` (i.e. `ι` injective, `π` surjective, and
`range ι = ker π`), the image sequence
`0 → Hom(P,K) →[ι ∘ ·] Hom(P,M) →[π ∘ ·] Hom(P,N) → 0` is again short exact:
post-composition with `ι` is injective, its range is the kernel of post-composition with `π`,
and post-composition with `π` is surjective.

The first two conjuncts (left exactness) hold for every module `P`; the surjectivity conjunct
is exactly the lifting property, hence projectivity.
(Etingof Theorem 8.1.1, equivalence of conditions (i) and (iv)) -/
theorem Etingof.Theorem_8_1_1_i_iff_iv
    (R : Type u) [Ring R]
    (P : Type v) [AddCommGroup P] [Module R P] [Small.{v} R] :
    Module.Projective R P ↔
      (∀ {K M N : Type v} [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
        [Module R K] [Module R M] [Module R N]
        (ι : K →ₗ[R] M) (π : M →ₗ[R] N),
        Function.Injective ι → Function.Surjective π →
        LinearMap.range ι = LinearMap.ker π →
        Function.Injective (fun g : P →ₗ[R] K => ι ∘ₗ g) ∧
        (∀ h : P →ₗ[R] M, π ∘ₗ h = 0 ↔ ∃ g : P →ₗ[R] K, ι ∘ₗ g = h) ∧
        Function.Surjective (fun h : P →ₗ[R] M => π ∘ₗ h)) := by
  constructor
  · intro hP K M N _ _ _ _ _ _ ι π hι hπ hexact
    haveI := hP
    have hπι : π ∘ₗ ι = 0 := by
      ext k
      have hk : ι k ∈ LinearMap.ker π := hexact ▸ LinearMap.mem_range_self ι k
      simpa [LinearMap.mem_ker] using hk
    refine ⟨?_, ?_, ?_⟩
    · intro g g' hgg'
      ext p
      exact hι (LinearMap.congr_fun hgg' p)
    · intro h
      constructor
      · intro hπh
        have hpf : ∀ p, h p ∈ LinearMap.range ι := by
          intro p
          rw [hexact, LinearMap.mem_ker]
          simpa using LinearMap.congr_fun hπh p
        refine ⟨(LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
          LinearMap.codRestrict (LinearMap.range ι) h hpf, ?_⟩
        ext p
        simp
      · rintro ⟨g, rfl⟩
        rw [← LinearMap.comp_assoc, hπι, LinearMap.zero_comp]
    · intro h'
      exact Module.projective_lifting_property π h' hπ
  · intro hex
    refine Module.Projective.of_lifting_property'' (fun p hp ↦ ?_)
    let e := Finsupp.mapRange.linearEquiv (α := P) (Shrink.linearEquiv R R)
    have hfsurj : Function.Surjective (p ∘ₗ e.toLinearMap) := hp.comp e.surjective
    obtain ⟨-, -, hsurj⟩ := hex (LinearMap.ker (p ∘ₗ e.toLinearMap)).subtype
      (p ∘ₗ e.toLinearMap) Subtype.coe_injective hfsurj (Submodule.range_subtype _)
    obtain ⟨h, hh⟩ := hsurj LinearMap.id
    refine ⟨e.toLinearMap ∘ₗ h, ?_⟩
    rw [← LinearMap.comp_assoc]
    exact hh
