import EtingofRepresentationTheory.Chapter9.Definition9_7_2
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

universe u

/-!
# The literal/split basic-algebra bridge

`Chapter9/Definition9_7_2.lean` carries two basic-algebra predicates:

* `Etingof.IsBasicAlgebra k A` — the book's literal Definition 9.7.2, `A / Rad(A)` commutative;
* `Etingof.IsBasicAlgebraSplit k A` — every simple `A`-module is one-dimensional over `k`.

That file records that the two agree over an algebraically closed field but does not prove it,
so the Morita development (`MoritaStructural`, `Corollary_9_7_3_i_unique`,
`Corollary_9_7_3_ii`), which takes `IsBasicAlgebraSplit` as its hypothesis, could not be
applied to an algebra known only to satisfy the book's condition. This file supplies the
missing implications.

## Results

* `Etingof.IsBasicAlgebraSplit.isBasicAlgebra` — split ⟹ literal, over **any** field and with
  no finiteness hypothesis.
* `Etingof.IsBasicAlgebra.isBasicAlgebraSplit` — literal ⟹ split, for a finite-dimensional
  algebra over an algebraically closed field.
* `Etingof.isBasicAlgebra_iff_isBasicAlgebraSplit` — the two are equivalent in that setting.

## Proofs

Split ⟹ literal. `Rad(A)` is the intersection of the maximal left ideals `m`, so it suffices to
put each commutator `xy - yx` into each such `m`. The quotient `A ⧸ m` is a simple `A`-module,
hence one-dimensional over `k` by hypothesis, so every `a : A` acts on it as a `k`-scalar
`c a`. Scalars commute, so `xy` and `yx` act by the same scalar `c x * c y` and the commutator
kills the class of `1`, which says exactly `xy - yx ∈ m`.

Literal ⟹ split. Let `M` be a simple `A`-module. `M` is finite-dimensional over `k`, being a
quotient of the finite-dimensional `A`. Commutativity of `A / Rad(A)` puts every commutator
`rs - sr` in `Rad(A)`, which annihilates the simple (hence semisimple) module `M`
(`IsSemisimpleModule.jacobson_le_annihilator`); so the actions of any two elements of `A`
on `M` commute, making `m ↦ r • m` an `A`-endomorphism of `M`. Schur's lemma over an
algebraically closed field forces it to be a `k`-scalar, so the `A`-span of any nonzero
`m₀ : M` — all of `M`, by simplicity — is contained in `k ∙ m₀`.

The proof of literal ⟹ split follows the same route as the corner-ring-specific argument
inside `Infrastructure/BasicAlgebraExistence.lean` (`exists_full_idempotent_basic_corner`),
where commutativity is witnessed by an explicit ring hom to `∏ k` rather than by the
radical quotient.
-/

namespace Etingof

/-- **Split basic ⟹ literal basic.** If every simple `A`-module is one-dimensional over `k`,
then `A / Rad(A)` is commutative, i.e. `A` is basic in the sense of Etingof Definition 9.7.2.

This direction needs neither `IsAlgClosed k` nor finite-dimensionality: `Rad(A)` is the
intersection of the maximal left ideals, each quotient `A ⧸ m` is a simple module on which
`A` therefore acts through `k`, and `k` is commutative. -/
theorem IsBasicAlgebraSplit.isBasicAlgebra {k : Type u} [Field k]
    {A : Type u} [Ring A] [Algebra k A]
    (h : IsBasicAlgebraSplit.{u, u, u} k A) : IsBasicAlgebra k A := by
  intro xq yq
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xq
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yq
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
  -- `Rad(A) = ⨅ {m : maximal left ideal}`, so it suffices to hit every coatom.
  refine Submodule.mem_sInf.mpr fun m hm => ?_
  haveI : IsSimpleModule A (A ⧸ m) := isSimpleModule_iff_isCoatom.mpr hm
  -- The class of `1` is a nonzero vector of the one-dimensional space `A ⧸ m`.
  let v : A ⧸ m := Submodule.Quotient.mk (1 : A)
  have hv : v ≠ 0 := by
    rw [Ne, show v = Submodule.Quotient.mk (1 : A) from rfl, Submodule.Quotient.mk_eq_zero]
    exact fun h1 => hm.1 ((Ideal.eq_top_iff_one m).mpr h1)
  have hone : Module.finrank k (A ⧸ m) = 1 := h (A ⧸ m)
  rw [finrank_eq_one_iff_of_nonzero' v hv] at hone
  -- Every `a : A` acts on `v` by a scalar.
  have hscalar : ∀ a : A, ∃ c : k, a • v = c • v := fun a =>
    let ⟨c, hc⟩ := hone (a • v); ⟨c, hc.symm⟩
  obtain ⟨cx, hcx⟩ := hscalar x
  obtain ⟨cy, hcy⟩ := hscalar y
  -- `xy` and `yx` therefore act by the same scalar, so the commutator kills `v`.
  have hkill : (x * y - y * x) • v = 0 := by
    rw [sub_smul, mul_smul, mul_smul, hcx, hcy, smul_comm y cx v, smul_comm x cy v,
      hcx, hcy, smul_comm cx cy v, sub_self]
  rwa [show v = Submodule.Quotient.mk (1 : A) from rfl, ← Submodule.Quotient.mk_smul,
    smul_eq_mul, mul_one, Submodule.Quotient.mk_eq_zero] at hkill

/-- **Literal basic ⟹ split basic**, over an algebraically closed field. If `A` is a
finite-dimensional `k`-algebra with `A / Rad(A)` commutative, then every simple `A`-module is
one-dimensional over `k`.

Algebraic closedness is essential: over `ℝ`, the algebra `ℂ` is basic in the book's sense (it
is commutative, and its radical is trivial) yet its unique simple module `ℂ` is
two-dimensional over `ℝ`. -/
theorem IsBasicAlgebra.isBasicAlgebraSplit {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
    (h : IsBasicAlgebra k A) : IsBasicAlgebraSplit.{u, u, u} k A := by
  intro M _instACG _instMod _instSimple _instModk _instST
  -- Step 1: the radical annihilates `M`, so the actions of elements of `A` commute on `M`.
  have hcomm_act : ∀ (r s : A) (m : M), r • (s • m) = s • (r • m) := by
    intro r s m
    have hcomm : r * s - s * r ∈ Ring.jacobson A := by
      have hq := h (Ideal.Quotient.mk _ r) (Ideal.Quotient.mk _ s)
      rwa [← map_mul, ← map_mul, Ideal.Quotient.eq] at hq
    have hann : r * s - s * r ∈ Module.annihilator A M :=
      IsSemisimpleModule.jacobson_le_annihilator A M hcomm
    have h0 := Module.mem_annihilator.mp hann m
    rwa [sub_smul, mul_smul, mul_smul, sub_eq_zero] at h0
  -- Step 2: `M` is a cyclic module, hence finite-dimensional over `k`.
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hspan : Submodule.span A {m₀} = ⊤ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top (Submodule.span A {m₀}) with hb | ht
    · exfalso
      have hmem : m₀ ∈ (⊥ : Submodule A M) := hb ▸ Submodule.subset_span rfl
      rw [Submodule.mem_bot] at hmem
      exact hm₀ hmem
    · exact ht
  have hsurj : ∀ m : M, ∃ r : A, r • m₀ = m := fun m =>
    Submodule.mem_span_singleton.mp (hspan ▸ (Submodule.mem_top : m ∈ ⊤))
  haveI : FiniteDimensional k M := by
    let f : A →ₗ[k] M :=
      { toFun := fun r => r • m₀
        map_add' := fun a b => add_smul a b m₀
        map_smul' := fun c a => by simp only [RingHom.id_apply]; rw [← smul_assoc] }
    exact Module.Finite.of_surjective f fun m => hsurj m
  -- Step 3: Schur's lemma over an algebraically closed field: each action map is a `k`-scalar.
  have hschur := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k (A := A) (V := M)
  have hscalar : ∀ r : A, ∃ c : k, ∀ m : M, r • m = c • m := by
    intro r
    let φ : M →ₗ[A] M :=
      { toFun := fun m => r • m
        map_add' := fun a b => smul_add r a b
        map_smul' := fun s m => by simp only [RingHom.id_apply]; exact hcomm_act r s m }
    obtain ⟨c, hc⟩ := hschur.2 φ
    refine ⟨c, fun m => ?_⟩
    have hm := LinearMap.ext_iff.mp hc m
    simp only [Module.algebraMap_end_apply] at hm
    exact hm.symm
  -- Step 4: `M = A • m₀ ⊆ k ∙ m₀`, so `M` is one-dimensional.
  rw [finrank_eq_one_iff_of_nonzero' m₀ hm₀]
  intro m
  obtain ⟨r, hr⟩ := hsurj m
  obtain ⟨c, hc⟩ := hscalar r
  exact ⟨c, by rw [← hr, hc]⟩

/-- **The two basic-algebra notions agree over an algebraically closed field.** For a
finite-dimensional algebra `A` over an algebraically closed field `k`, the book's literal
Definition 9.7.2 (`A / Rad(A)` commutative) is equivalent to the split condition (every simple
`A`-module is one-dimensional over `k`) that the Morita development uses as its hypothesis. -/
theorem isBasicAlgebra_iff_isBasicAlgebraSplit {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A] :
    IsBasicAlgebra k A ↔ IsBasicAlgebraSplit.{u, u, u} k A :=
  ⟨IsBasicAlgebra.isBasicAlgebraSplit, IsBasicAlgebraSplit.isBasicAlgebra⟩

end Etingof
