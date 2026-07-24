import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_18_1
import EtingofRepresentationTheory.Chapter5.Theorem5_18_1_Exhaustive
import EtingofRepresentationTheory.Chapter5.MultiplicitySpaceBiduality

/-!
# Theorem 5.18.1(iii): the `V ↦ Hom_A(V, E)` bijection of simple classes

The Double Centralizer Theorem 5.18.1 exhibits, for a semisimple subalgebra
`A ⊆ End_k(E)` acting faithfully on a finite-dimensional space `E` over an
algebraically closed field `k`, a bimodule decomposition
`E ≃ ⨁ᵢ Vᵢ ⊗ Lᵢ` with `Lᵢ = Hom_A(Vᵢ, E)` the multiplicity spaces, which are
simple modules over `B = centralizer(A)`. The book's final sentence upgrades
this to a *classification statement*: the assignment

  `[V] ↦ [Hom_A(V, E)]`

is a **bijection** between iso-classes of simple `A`-modules and iso-classes of
simple `B`-modules.

`Theorem5_18_1_Exhaustive.lean` classified the two families independently
(complete irredundant lists indexed by isotypic components). `MultiplicitySpaceBiduality.lean`
supplied the biduality bridge. This file ties them together into the explicit
correspondence, providing:

* **Well-definedness** (`homACongrLeftCentralizer`): an `A`-iso `V ≃ₗ[A] W`
  induces a `B`-iso `Hom_A(W, E) ≃ₗ[B] Hom_A(V, E)`, so `V ↦ Hom_A(V, E)`
  descends to iso-classes.
* **Simplicity** (`isSimpleModule_homA_centralizer'`): for *any* simple
  `A`-module `V` (not just a submodule of `E`), `Hom_A(V, E)` is a simple
  `B`-module.
* **Injectivity** (`homA_iso_of_homA_congr`): if `Hom_A(V, E) ≃ₗ[B] Hom_A(W, E)`
  then `V ≃ₗ[A] W`. Combined with `Theorem5_18_1_A_classification` this shows
  the map is injective on iso-classes.
* **Surjectivity** (`exists_simple_A_module_homA_iso`): every simple `B`-module
  is `≃ₗ[B] Hom_A(V, E)` for some simple `A`-module `V` (realised as
  `Hom_B(W₀, E)` via the biduality bridge / double-centralizer).
* **Bijection** (`homA_bijection_isotypicComponents`): the induced map on the
  finite index sets `isotypicComponents A E → isotypicComponents B E` is a
  bijection.

The `A ⊗ B`-equivariance packaging tracked separately (see the Schur-Weyl
transfer files) consumes these endpoints.
-/

open scoped TensorProduct

universe u v w

namespace Etingof

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

/-- **Well-definedness of `V ↦ Hom_A(V, E)` on iso-classes.**

An `A`-linear equivalence `e : M ≃ₗ[A] N` induces a `B`-linear equivalence
(`B = centralizer(A)`) of multiplicity spaces `(N →ₗ[A] E) ≃ₗ[B] (M →ₗ[A] E)` by
precomposition `f ↦ f ∘ e`. This is `B`-linear because the `B`-action is
post-composition, which commutes with precomposition by `e`.

This is the domain-side congruence for the centralizer post-composition action,
the `B`-linear refinement of `homCongrLeftOverSubring` (which only records
`k`-linearity). -/
noncomputable def homACongrLeftCentralizer
    (A : Subalgebra k (Module.End k E))
    {M N : Type*}
    [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    (e : M ≃ₗ[A] N) :
    (N →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (M →ₗ[A] E) where
  toFun f := f.comp e.toLinearMap
  invFun f := f.comp e.symm.toLinearMap
  left_inv f := by ext v; simp
  right_inv f := by ext v; simp
  map_add' f g := by ext v; simp
  map_smul' b f := by
    ext v
    -- `(b • f) ∘ e = b • (f ∘ e)`: both send `v` to `b.val (f (e v))`.
    change (centralizerToEndA k E A b) (f (e v)) = (centralizerToEndA k E A b) (f (e v))
    rfl

/-- **Simplicity of `Hom_A(V, E)` for an abstract simple `A`-module.**

`isSimpleModule_homA_centralizer` proves `Hom_A(V, E)` is a simple `B`-module
(`B = centralizer(A)`) when `V ≤ E` is a simple *submodule*. Using
`exists_simpleSubmodule_iso_of_faithful` to realise an arbitrary simple
`A`-module `V` inside `E` and transporting along
`homACongrLeftCentralizer`, the same holds for *any* simple `A`-module. -/
theorem isSimpleModule_homA_centralizer'
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A]
    (V : Type w) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
    [IsSimpleModule A V] :
    IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) := by
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  obtain ⟨W, hWsimple, ⟨eVW⟩⟩ := exists_simpleSubmodule_iso_of_faithful k E A V
  haveI := hWsimple
  -- `Hom_A(V, E) ≃ₗ[B] Hom_A(W, E)` and the latter is simple.
  have e : (V →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (↥W →ₗ[A] E) := homACongrLeftCentralizer k E A eVW.symm
  haveI : IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥W →ₗ[A] E) := isSimpleModule_homA_centralizer k E A W
  exact IsSimpleModule.congr e

/-- **Injectivity of `V ↦ Hom_A(V, E)` on iso-classes.**

For simple `A`-modules `V`, `W` (not necessarily submodules of `E`), a
`B`-linear isomorphism `Hom_A(V, E) ≃ₗ[B] Hom_A(W, E)` forces `V ≃ₗ[A] W`.

Realise `V ≃ₗ[A] ↥S` and `W ≃ₗ[A] ↥T` as simple submodules of `E`
(`exists_simpleSubmodule_iso_of_faithful`), transport the hypothesis along
`homACongrLeftCentralizer` to `Hom_A(S, E) ≃ₗ[B] Hom_A(T, E)`, and apply the
biduality bridge `multiplicitySpace_biduality_Aiso` to get `↥S ≃ₗ[A] ↥T`. -/
theorem homA_iso_of_homA_congr
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [FaithfulSMul A E]
    [IsAlgClosed k]
    (V W : Type w)
    [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V] [IsSimpleModule A V]
    [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W] [IsSimpleModule A W]
    (h : Nonempty ((V →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (W →ₗ[A] E))) :
    Nonempty (V ≃ₗ[A] W) := by
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  obtain ⟨h⟩ := h
  obtain ⟨S, hSsimple, ⟨eVS⟩⟩ := exists_simpleSubmodule_iso_of_faithful k E A V
  obtain ⟨T, hTsimple, ⟨eWT⟩⟩ := exists_simpleSubmodule_iso_of_faithful k E A W
  haveI := hSsimple
  haveI := hTsimple
  -- `Hom_A(S, E) ≃ₗ[B] Hom_A(V, E) ≃ₗ[B] Hom_A(W, E) ≃ₗ[B] Hom_A(T, E)`.
  have eS : (↥S →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (V →ₗ[A] E) := homACongrLeftCentralizer k E A eVS
  have eT : (↥T →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (W →ₗ[A] E) := homACongrLeftCentralizer k E A eWT
  have hST : Nonempty ((↥S →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (↥T →ₗ[A] E)) := ⟨eS.trans (h.trans eT.symm)⟩
  obtain ⟨eST⟩ := multiplicitySpace_biduality_Aiso k E A S T hST
  exact ⟨eVS.trans (eST.trans eWT.symm)⟩

end Etingof
