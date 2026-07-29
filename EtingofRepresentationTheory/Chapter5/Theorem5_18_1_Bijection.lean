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
* **Surjectivity** (`exists_simple_A_submodule_homA_iso`): every simple
  `B`-module is `≃ₗ[B] Hom_A(V, E)` for some simple `A`-submodule `V ≤ E`,
  read off the surjectivity of the realization map below.
* **Bijection** (`homRealizationComponent_bijective`,
  `homRealizationComponentEquiv`): the induced map on the finite index sets
  `isotypicComponents A E → isotypicComponents B E` is a bijection. The engine
  is the generic realization map `homRealizationComponent` (injective by the
  biduality bridge), with bijectivity forced by the double-centralizer
  cardinality balance.

The `A ⊗ B`-equivariance packaging tracked separately (see the Schur-Weyl
transfer files) consumes these endpoints.
-/

open scoped TensorProduct

universe u v w

namespace Etingof

set_option backward.isDefEq.respectTransparency false

variable (k : Type u) [Field k]
  (E : Type v) [AddCommGroup E] [Module k E] [Module.Finite k E]

noncomputable local instance (priority := high) centralizerModuleHomSubmoduleBijection
    (A : Subalgebra k (Module.End k E)) (W : Submodule A E) :
    Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (↥W →ₗ[A] E) := centralizerModuleHom k E (A := A) (V := ↥W)

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

omit [Module.Finite k E] in
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
  letI : Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E))))
      (V →ₗ[A] E) := centralizerModuleHom k E (A := A) (V := V)
  -- `Hom_A(V, E) ≃ₗ[B] Hom_A(W, E)` and the latter is simple.
  have e : (V →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (↥W →ₗ[A] E) := homACongrLeftCentralizer k E A
        (M := ↥W) (N := V) eVW.symm
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
      (V →ₗ[A] E) := homACongrLeftCentralizer k E A (M := V) (N := ↥S) eVS
  have eT : (↥T →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (W →ₗ[A] E) := homACongrLeftCentralizer k E A (M := W) (N := ↥T) eWT
  have hST : Nonempty ((↥S →ₗ[A] E) ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
      (↥T →ₗ[A] E)) := ⟨eS.trans (h.trans eT.symm)⟩
  obtain ⟨eST⟩ := multiplicitySpace_biduality_Aiso k E A S T hST
  exact ⟨eVS.trans (eST.trans eWT.symm)⟩

/-!
## Surjectivity and the bijection

We now realise `V ↦ Hom_A(V, E)` as a bijection between the finite index sets
`isotypicComponents A E` and `isotypicComponents B E` (`B = centralizer A`).

The engine is a single **generic realization map**
`homRealizationComponent`: for any semisimple subalgebra `D ⊆ End_k(E)` acting
faithfully (`k` algebraically closed), send an isotypic component `c` over `D` to
the isotypic component over `centralizer D` of `Hom_D(V_c, E)` realised inside
`E` (`V_c ≤ c` a chosen simple submodule). It is injective by the biduality
bridge. Instantiating at `D = A` gives an injection
`isotypicComponents A E → isotypicComponents B E`; at `D = B` an injection
`isotypicComponents B E → isotypicComponents (centralizer B) E`. Since
`centralizer B = A` (double centralizer), the two index sets have equal finite
cardinality, so the first injection is a bijection.
-/

variable {k E} in
/-- The simple submodule of `E` chosen inside a nonzero isotypic component `c`
over a semisimple subalgebra `D`. -/
private noncomputable def compSimple
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) : Submodule D E :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule D E)).resolve_left
    (bot_lt_isotypicComponents c.2).ne').choose

variable {k E} in
omit [Module.Finite k E] in
private theorem compSimple_le
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) : compSimple D c ≤ c.1 :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule D E)).resolve_left
    (bot_lt_isotypicComponents c.2).ne').choose_spec.1

variable {k E} in
omit [Module.Finite k E] in
private instance compSimple_isSimple
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) : IsSimpleModule D (compSimple D c) :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  ((IsSemisimpleModule.eq_bot_or_exists_simple_le (c.1 : Submodule D E)).resolve_left
    (bot_lt_isotypicComponents c.2).ne').choose_spec.2

variable {k E} in
omit [Module.Finite k E] in
private theorem compSimple_component
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D]
    (c : isotypicComponents D E) :
    (c.1 : Submodule D E) = isotypicComponent D E (compSimple D c) :=
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  eq_isotypicComponent_of_le c.2 (compSimple_le D c)

/-- **Generic realization map.** For a semisimple subalgebra `D ⊆ End_k(E)`
acting faithfully on the finite-dimensional space `E` over an algebraically
closed field, send an isotypic component `c` over `D` to the isotypic component
over `centralizer D` carrying `Hom_D(V_c, E)` (`V_c ≤ c` the chosen simple
submodule). This is the component-level shadow of `V ↦ Hom_D(V, E)`. -/
noncomputable def homRealizationComponent
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D] [IsAlgClosed k]
    (c : isotypicComponents D E) :
    isotypicComponents (Subalgebra.centralizer k (D : Set (Module.End k E))) E :=
  haveI : IsSemisimpleRing (Subalgebra.centralizer k (D : Set (Module.End k E))) :=
    Theorem5_18_1_commutant_semisimple k E D
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  haveI : IsSimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E) := isSimpleModule_homA_centralizer k E D (compSimple D c)
  ⟨isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E
      (exists_simpleSubmodule_iso_of_faithful k E
        (Subalgebra.centralizer k (D : Set (Module.End k E)))
        (↥(compSimple D c) →ₗ[D] E)).choose,
    ⟨(exists_simpleSubmodule_iso_of_faithful k E
        (Subalgebra.centralizer k (D : Set (Module.End k E)))
        (↥(compSimple D c) →ₗ[D] E)).choose,
      (exists_simpleSubmodule_iso_of_faithful k E
        (Subalgebra.centralizer k (D : Set (Module.End k E)))
        (↥(compSimple D c) →ₗ[D] E)).choose_spec.1, rfl⟩⟩

/-- The generic realization map is injective: distinct isotypic components over
`D` map to distinct components over `centralizer D`. The proof runs the biduality
bridge `multiplicitySpace_biduality_Aiso` backwards — equal target components
force `Hom_D(V_c, E) ≃ Hom_D(V_{c'}, E)`, hence `V_c ≃ V_{c'}`, hence `c = c'`. -/
theorem homRealizationComponent_injective
    (D : Subalgebra k (Module.End k E)) [IsSemisimpleRing D] [IsAlgClosed k] :
    Function.Injective (homRealizationComponent k E D) := by
  classical
  haveI : IsSemisimpleModule D E := IsSemisimpleRing.isSemisimpleModule
  haveI hCss : IsSemisimpleRing (Subalgebra.centralizer k (D : Set (Module.End k E))) :=
    Theorem5_18_1_commutant_semisimple k E D
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  intro c c' hcc
  haveI : IsSimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E) := isSimpleModule_homA_centralizer k E D (compSimple D c)
  haveI : IsSimpleModule (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c') →ₗ[D] E) := isSimpleModule_homA_centralizer k E D (compSimple D c')
  -- Unfold the two realizations `W`, `W'` and their defining specs.
  set W := (exists_simpleSubmodule_iso_of_faithful k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E)).choose with hWdef
  set W' := (exists_simpleSubmodule_iso_of_faithful k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c') →ₗ[D] E)).choose with hW'def
  obtain ⟨hWsimple, ⟨eMW⟩⟩ := (exists_simpleSubmodule_iso_of_faithful k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c) →ₗ[D] E)).choose_spec
  obtain ⟨hW'simple, ⟨eMW'⟩⟩ := (exists_simpleSubmodule_iso_of_faithful k E
      (Subalgebra.centralizer k (D : Set (Module.End k E)))
      (↥(compSimple D c') →ₗ[D] E)).choose_spec
  haveI := hWsimple
  haveI := hW'simple
  -- `hcc` says the two chosen components coincide.
  have hcomp : isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W =
      isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W' :=
    congrArg (fun x => (x.1 : Submodule _ E)) hcc
  -- `W ≃ W'` over `centralizer D`: both simple submodules of a shared component.
  have hWle : W ≤ isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W :=
    Submodule.le_isotypicComponent W
  have hW'le : W' ≤ isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W :=
    hcomp ▸ Submodule.le_isotypicComponent W'
  obtain ⟨eWc⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W)
    W hWle
  obtain ⟨eW'c⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent (Subalgebra.centralizer k (D : Set (Module.End k E))) E W)
    W' hW'le
  -- Assemble `Hom_D(V_c, E) ≃ Hom_D(V_{c'}, E)` over `centralizer D`.
  have hMM : Nonempty ((↥(compSimple D c) →ₗ[D] E)
      ≃ₗ[Subalgebra.centralizer k (D : Set (Module.End k E))] (↥(compSimple D c') →ₗ[D] E)) :=
    ⟨eMW.trans (eWc.trans (eW'c.symm.trans eMW'.symm))⟩
  -- Biduality: `V_c ≃ V_{c'}` over `D`.
  obtain ⟨eVV⟩ := multiplicitySpace_biduality_Aiso k E D (compSimple D c) (compSimple D c') hMM
  -- Equal `D`-isotypic components ⟹ `c = c'`.
  have hDcomp : isotypicComponent D E (compSimple D c) = isotypicComponent D E (compSimple D c') :=
    eVV.isotypicComponent_eq
  have hc1 : (c.1 : Submodule D E) = c'.1 := by
    rw [compSimple_component D c, compSimple_component D c', hDcomp]
  exact Subtype.ext hc1

/-- **The `V ↦ Hom_A(V, E)` map is a bijection of simple-class index sets.**

The generic realization map at `A` is an injection
`isotypicComponents A E → isotypicComponents B E` (`B = centralizer A`); at `B`
it is an injection `isotypicComponents B E → isotypicComponents (centralizer B) E`.
Since `centralizer B = A` (double centralizer, `Theorem5_18_1_double_centralizer`),
the two finite index sets have equal cardinality, so the first injection is a
bijection. This is the index-set form of the book's bijection between simple
`A`-modules and simple `B`-modules. -/
theorem homRealizationComponent_bijective
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [IsAlgClosed k] :
    Function.Bijective (homRealizationComponent k E A) := by
  classical
  set C := Subalgebra.centralizer k (A : Set (Module.End k E)) with hC
  haveI hCss : IsSemisimpleRing C := Theorem5_18_1_commutant_semisimple k E A
  haveI hCCss : IsSemisimpleRing (Subalgebra.centralizer k (C : Set (Module.End k E))) :=
    Theorem5_18_1_commutant_semisimple k E C
  -- Finiteness of all three index sets.
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : IsSemisimpleModule C E := IsSemisimpleRing.isSemisimpleModule
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (C : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  haveI : Module.Finite A E := Module.Finite.of_restrictScalars_finite k A E
  haveI : Module.Finite C E := Module.Finite.of_restrictScalars_finite k C E
  haveI : Module.Finite (Subalgebra.centralizer k (C : Set (Module.End k E))) E :=
    Module.Finite.of_restrictScalars_finite k _ E
  haveI : IsNoetherian A E := inferInstance
  haveI : IsNoetherian C E := inferInstance
  haveI : IsNoetherian (Subalgebra.centralizer k (C : Set (Module.End k E))) E := inferInstance
  haveI : Fintype (isotypicComponents A E) := Fintype.ofFinite _
  haveI : Fintype (isotypicComponents C E) := Fintype.ofFinite _
  haveI : Fintype (isotypicComponents
      (Subalgebra.centralizer k (C : Set (Module.End k E))) E) := Fintype.ofFinite _
  -- Injections at `A` and at `C`.
  have hα : Function.Injective (homRealizationComponent k E A) :=
    homRealizationComponent_injective k E A
  have hβ : Function.Injective (homRealizationComponent k E C) :=
    homRealizationComponent_injective k E C
  have hcardα : Fintype.card (isotypicComponents A E) ≤ Fintype.card (isotypicComponents C E) :=
    Fintype.card_le_of_injective _ hα
  have hcardβ : Fintype.card (isotypicComponents C E) ≤
      Fintype.card (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E) :=
    Fintype.card_le_of_injective _ hβ
  -- Double centralizer: `centralizer C = A`, so the outer index set matches `Θ_A`.
  have hCC : Subalgebra.centralizer k (C : Set (Module.End k E)) = A :=
    Theorem5_18_1_double_centralizer k E A
  -- Transport the outer index set to `Θ_A` at the level of `Nat.card` (which,
  -- unlike `Fintype.card`, carries no instance argument, so `rw [hCC]` is
  -- motive-correct on the plain type equality).
  have hType : (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E :
        Type _) = (isotypicComponents A E : Type _) := by rw [hCC]
  have hcardCC : Fintype.card
      (isotypicComponents (Subalgebra.centralizer k (C : Set (Module.End k E))) E) =
      Fintype.card (isotypicComponents A E) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hType]
  have hcard_eq : Fintype.card (isotypicComponents A E) = Fintype.card (isotypicComponents C E) :=
    le_antisymm hcardα (hcardβ.trans (le_of_eq hcardCC))
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hα, hcard_eq⟩

/-- **The `V ↦ Hom_A(V, E)` bijection of simple-class index sets, packaged as an
`Equiv`.** See `homRealizationComponent_bijective`. -/
noncomputable def homRealizationComponentEquiv
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [IsAlgClosed k] :
    isotypicComponents A E ≃
      isotypicComponents (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
  Equiv.ofBijective _ (homRealizationComponent_bijective k E A)

/-- **Surjectivity of `V ↦ Hom_A(V, E)` (the book's final sentence).**

Every simple `B`-module `W` (`B = centralizer A`) is `B`-isomorphic to
`Hom_A(V, E)` for some simple `A`-submodule `V ≤ E`. This is the surjectivity
half of the classification: combined with `homA_iso_of_homA_congr` (injectivity)
and `isSimpleModule_homA_centralizer'` (simple-valued), it shows `V ↦ Hom_A(V, E)`
is a bijection between iso-classes of simple `A`-modules and simple `B`-modules.

The witness is read off the surjectivity of `homRealizationComponent A`: realise
`W ≃ₗ[B] ↥W₀` inside `E`, hit its isotypic component by some `c`, and identify
the realisation of `Hom_A(V_c, E)` with `↥W₀` inside the shared component. -/
theorem exists_simple_A_submodule_homA_iso
    (A : Subalgebra k (Module.End k E)) [IsSemisimpleRing A] [IsAlgClosed k]
    (W : Type w) [AddCommGroup W]
    [Module (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) W]
    [IsSimpleModule (↥(Subalgebra.centralizer k (A : Set (Module.End k E)))) W] :
    ∃ V : Submodule A E, IsSimpleModule A V ∧
      Nonempty (W ≃ₗ[↥(Subalgebra.centralizer k (A : Set (Module.End k E)))]
        (↥V →ₗ[A] E)) := by
  classical
  haveI hCss : IsSemisimpleRing (Subalgebra.centralizer k (A : Set (Module.End k E))) :=
    Theorem5_18_1_commutant_semisimple k E A
  haveI : IsSemisimpleModule A E := IsSemisimpleRing.isSemisimpleModule
  haveI : IsSemisimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    IsSemisimpleRing.isSemisimpleModule
  -- Realise `W` as a simple `B`-submodule `W₀ ≤ E`.
  obtain ⟨W₀, hW₀simple, ⟨eWW₀⟩⟩ := exists_simpleSubmodule_iso_of_faithful k E
    (Subalgebra.centralizer k (A : Set (Module.End k E))) W
  haveI := hW₀simple
  -- Its isotypic component `d`, hit by some `c` via surjectivity.
  set d : isotypicComponents (Subalgebra.centralizer k (A : Set (Module.End k E))) E :=
    ⟨isotypicComponent _ E W₀, ⟨W₀, hW₀simple, rfl⟩⟩ with hd
  obtain ⟨c, hc⟩ := (homRealizationComponent_bijective k E A).2 d
  -- Unfold the realisation `R` of `Hom_A(V_c, E)`.
  haveI : IsSimpleModule (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥(compSimple A c) →ₗ[A] E) := isSimpleModule_homA_centralizer k E A (compSimple A c)
  set R := (exists_simpleSubmodule_iso_of_faithful k E
      (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥(compSimple A c) →ₗ[A] E)).choose with hRdef
  obtain ⟨hRsimple, ⟨eMR⟩⟩ := (exists_simpleSubmodule_iso_of_faithful k E
      (Subalgebra.centralizer k (A : Set (Module.End k E)))
      (↥(compSimple A c) →ₗ[A] E)).choose_spec
  haveI := hRsimple
  -- `hc` gives `isotypicComponent B E R = isotypicComponent B E W₀`.
  have hcomp : isotypicComponent (Subalgebra.centralizer k (A : Set (Module.End k E))) E R =
      isotypicComponent (Subalgebra.centralizer k (A : Set (Module.End k E))) E W₀ :=
    congrArg Subtype.val hc
  -- `R ≃ W₀` over `B`: both simple submodules of the shared component.
  have hRle : R ≤ isotypicComponent (Subalgebra.centralizer k (A : Set (Module.End k E))) E R :=
    Submodule.le_isotypicComponent R
  have hW₀le : W₀ ≤ isotypicComponent (Subalgebra.centralizer k (A : Set (Module.End k E))) E R :=
    hcomp ▸ Submodule.le_isotypicComponent W₀
  obtain ⟨eRc⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent _ E R) R hRle
  obtain ⟨eW₀c⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent _ E R) W₀ hW₀le
  -- `W ≃ W₀ ≃ R ≃ Hom_A(V_c, E)`.
  exact ⟨compSimple A c, compSimple_isSimple A c,
    ⟨eWW₀.trans (eW₀c.trans (eRc.symm.trans eMR.symm))⟩⟩

end Etingof
