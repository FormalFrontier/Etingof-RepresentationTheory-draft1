import EtingofRepresentationTheory.Chapter9.Definition9_6_1
import EtingofRepresentationTheory.Chapter9.Definition9_6_2
import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Existence
import EtingofRepresentationTheory.Chapter9.KrullSchmidt.Exchange
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

universe u v w

/-!
# Introduction to §9.7: classification of projective generators

Etingof §9.7 (page 220) records, as an exercise ("check it!"), the classification of
all projective generators of a finite abelian category `𝒞`:

> Let `P₁, …, P_m` be the indecomposable projective objects of `𝒞` (they make sense by
> Theorem 9.6.4). Then all the projective generators of `𝒞` are the objects of the form
> `P_𝐧 := ⊕_{i=1}^m n_i P_i`, where `n_i ≥ 1`.

This file formalizes that classification. We work with a finite family `P : ι → 𝒞` of
the indecomposable projectives and define the *multiplicity biproduct*
`multBiproduct P n = ⨁_{i} n_i • P_i` (concretely, the biproduct over `Σ i, Fin (n i)`
of the spaces `P_i`).

The classification is the biconditional

`IsProgenerator Q ↔ ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (Q ≅ multBiproduct P n)`.

* The **backward** direction (any such `multBiproduct` with all `n_i ≥ 1` is a
  progenerator) is the elementary "check it!" content and is proved here in full
  (`Etingof.isProgenerator_multBiproduct`). The argument: `multBiproduct P n` is a
  biproduct of projectives, hence projective; and the given progenerator `⨁ P` (one
  copy of each `P_i`) is a *retract* of `multBiproduct P n` once every `n_i ≥ 1`, so
  every object — already a quotient of a biproduct of copies of `⨁ P` — is a quotient
  of a biproduct of copies of `multBiproduct P n`.

* The **forward** direction (every progenerator is of this shape, with each `P_i`
  occurring at least once) is the **Krull–Schmidt** content: a finitely generated
  projective object of a finite abelian category decomposes (essentially uniquely) into
  indecomposable projectives, each of which is one of the `P_i`, and generation forces
  every `P_i` to appear. Krull–Schmidt for finite abelian / finite-length additive
  categories is **not in Mathlib**; it is built up in `Chapter9/KrullSchmidt/` and
  consumed here. `Etingof.progenerator_decomposition` discharges this direction in full
  from the existence (`KrullSchmidt/Existence.lean`) and exchange
  (`KrullSchmidt/Exchange.lean`) links.
-/

open CategoryTheory CategoryTheory.Limits

namespace Etingof

variable {C : Type u} [Category.{v} C]

section MultBiproduct

variable [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- The **multiplicity biproduct** `⊕_i n_i • P_i` of Etingof §9.7: the biproduct, over
`Σ i, Fin (n i)`, of the objects `P_i`. It contains `n_i` copies of each `P_i`. -/
noncomputable def multBiproduct {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ) : C :=
  ⨁ (fun p : Σ i, Fin (n i) => P p.1)

/-- The `(i, a)`-component projection out of `multBiproduct P n`. -/
noncomputable def multBiproduct.π {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ)
    (p : Σ i, Fin (n i)) : multBiproduct P n ⟶ P p.1 :=
  biproduct.π (fun p : Σ i, Fin (n i) => P p.1) p

/-- The `(i, a)`-component inclusion into `multBiproduct P n`. -/
noncomputable def multBiproduct.ι {ι : Type v} [Fintype ι] (P : ι → C) (n : ι → ℕ)
    (p : Σ i, Fin (n i)) : P p.1 ⟶ multBiproduct P n :=
  biproduct.ι (fun p : Σ i, Fin (n i) => P p.1) p

end MultBiproduct

section Backward

variable [Preadditive C] [HasFiniteBiproducts C]

/-- Transport `IsProgenerator` across an isomorphism. -/
theorem IsProgenerator.of_iso {Q R : C} (e : Q ≅ R) [hR : IsProgenerator R] :
    IsProgenerator Q where
  toProjective := Projective.of_iso e.symm hR.toProjective
  epiFromBiproduct X := by
    obtain ⟨m, hbp, π, hπ⟩ := hR.epiFromBiproduct X
    haveI : HasBiproduct (fun _ : Fin m => R) := hbp
    haveI : HasBiproduct (fun _ : Fin m => Q) := inferInstance
    exact ⟨m, inferInstance,
      (biproduct.mapIso (fun _ : Fin m => e)).hom ≫ π, epi_comp _ _⟩

/-- **Backward direction of the §9.7 classification.** If `⨁ P` (one copy of each
indecomposable projective) is a progenerator and every multiplicity `n_i ≥ 1`, then the
multiplicity biproduct `⊕_i n_i • P_i` is again a progenerator.

The proof exhibits `⨁ P` as a retract of `multBiproduct P n`: the section
`s : ⨁ P ⟶ multBiproduct P n` sends the `i`-th summand to the `(i, 0)`-summand, and the
retraction `r` projects back; `s ≫ r = 𝟙`. Projectivity is automatic (a biproduct of
projectives is projective), and the retraction lets us pull back the epimorphisms
witnessing that `⨁ P` is a generator. -/
theorem isProgenerator_multBiproduct {ι : Type v} [Fintype ι] (P : ι → C)
    [∀ i, Projective (P i)] [hgen : IsProgenerator (⨁ P)]
    (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) :
    IsProgenerator (multBiproduct P n) := by
  classical
  -- the diagonal inclusion `i ↦ (i, 0)` of indices
  let e : ι → Σ i, Fin (n i) := fun i => ⟨i, ⟨0, hn i⟩⟩
  have he : Function.Injective e := fun i j h => congrArg Sigma.fst h
  -- section and retraction realising `⨁ P` as a retract of `multBiproduct P n`
  let s : (⨁ P) ⟶ multBiproduct P n :=
    biproduct.desc (fun i => multBiproduct.ι P n (e i))
  let r : multBiproduct P n ⟶ (⨁ P) :=
    biproduct.lift (fun i => multBiproduct.π P n (e i))
  have key : s ≫ r = 𝟙 (⨁ P) := by
    apply biproduct.hom_ext'
    intro i
    rw [Category.comp_id, ← Category.assoc,
      show biproduct.ι P i ≫ s = multBiproduct.ι P n (e i) from biproduct.ι_desc _ i]
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc,
      show r ≫ biproduct.π P j = multBiproduct.π P n (e j) from biproduct.lift_π _ j]
    unfold multBiproduct.ι multBiproduct.π
    rw [biproduct.ι_π, biproduct.ι_π]
    by_cases h : i = j
    · subst h; rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg (fun he' => h (he he')), dif_neg h]
  -- `r` is a split epimorphism, hence an epimorphism
  haveI : IsSplitEpi r := ⟨⟨s, key⟩⟩
  haveI : Projective (multBiproduct P n) :=
    inferInstanceAs (Projective (⨁ fun p : Σ i, Fin (n i) => P p.1))
  refine { toProjective := inferInstance, epiFromBiproduct := fun X => ?_ }
  obtain ⟨m, hbp, π, hπ⟩ := hgen.epiFromBiproduct X
  haveI : HasBiproduct (fun _ : Fin m => (⨁ P)) := hbp
  haveI : Epi r := inferInstance
  refine ⟨m, inferInstance, biproduct.map (fun _ : Fin m => r) ≫ π, ?_⟩
  exact epi_comp _ _

end Backward

section Classification

variable [IsFiniteAbelianCategory C] [HasFiniteBiproducts C]

/-- **Forward direction of the §9.7 classification (Krull–Schmidt).**

If `Q` is a projective generator of the finite abelian category `𝒞`, and `P : ι → 𝒞` is
the family of indecomposable projectives (each indecomposable, pairwise non-isomorphic,
and exhausting the indecomposable projectives up to isomorphism, with `⨁ P` a
progenerator), then `Q ≅ ⊕_i n_i P_i` for a unique multiplicity vector `n` with every
`n_i ≥ 1`.

The proof assembles the **Krull–Schmidt** links built in `Chapter9/KrullSchmidt/`:
1. `Q`, being projective in a finite (finite-length) abelian category, decomposes as a
   finite biproduct `Q ≅ ⨁ f` of indecomposable projective objects
   (`exists_indecomposable_projective_biproduct`).
2. Each summand `f k` is isomorphic to a unique `P (g k)` (`hcomplete`, `hdistinct`);
   the multiplicity `n i := #{k | g k = i}` and a reindexing of `⨁ f` along the fibre
   bijection `(Σ i, Fin (n i)) ≃ κ` give `Q ≅ multBiproduct P n`.
3. Because `Q` is a generator, every `P_i` is a quotient of `Q^m`, hence (being
   projective) an indecomposable direct summand of a biproduct of the `f k`'s; the
   exchange property (`indecomposable_summand_iso_factor`) matches it to some `f k`, and
   `hdistinct` forces `g k = i`, so every fibre is nonempty, i.e. `n_i ≥ 1`. -/
theorem progenerator_decomposition {ι : Type v} [Fintype ι] (P : ι → C)
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, CategoryTheory.Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → CategoryTheory.Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    (hgen : IsProgenerator (⨁ P)) (Q : C) (hQ : IsProgenerator Q) :
    ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (Q ≅ multBiproduct P n) := by
  classical
  -- Step 1: Krull–Schmidt existence decomposes the projective `Q` into a finite family `f`
  -- of indecomposable projectives, with `e : Q ≅ ⨁ f`.
  obtain ⟨κ, instκ, f, hf, ⟨e⟩⟩ := exists_indecomposable_projective_biproduct hQ.toProjective
  haveI := instκ
  -- Step 2: each summand `f k` is isomorphic to a unique `P (g k)` by completeness.
  choose g hg using fun k => hcomplete (f k) (hf k).1 (hf k).2
  -- the chosen iso `f k ≅ P (g k)`
  let fiso : ∀ k, f k ≅ P (g k) := fun k => (hg k).some
  -- the multiplicity of `P i` is the cardinality of the fibre `g⁻¹ i`.
  set n : ι → ℕ := fun i => Fintype.card {k // g k = i} with hn
  -- the reindexing bijection `(Σ i, Fin (n i)) ≃ κ`: split `κ` into fibres of `g`.
  let σ : (Σ i, Fin (n i)) ≃ κ :=
    (Equiv.sigmaCongrRight fun i => (Fintype.equivFin {k // g k = i}).symm).trans
      (Equiv.sigmaFiberEquiv g)
  -- the index of `σ p` lands in the fibre over `p.1`.
  have hgσ : ∀ p : Σ i, Fin (n i), g (σ p) = p.1 := by
    rintro ⟨i, a⟩
    exact ((Fintype.equivFin {k // g k = i}).symm a).2
  -- Step 3 (positivity): every `P i` occurs, so every fibre is nonempty.
  have hpos : ∀ i, 1 ≤ n i := by
    intro i
    -- `P i` is projective and indecomposable; as a generator `Q ≅ ⨁ f` admits an epi
    -- `⨁_{Fin m} Q ⟶ P i`, which splits since `P i` is projective.
    haveI : Projective (P i) := hproj i
    obtain ⟨m, hbp, π, hπ⟩ := hQ.epiFromBiproduct (P i)
    haveI := hbp
    haveI := hπ
    let t : P i ⟶ (⨁ fun _ : Fin m => Q) := Projective.factorThru (𝟙 (P i)) π
    have ht : t ≫ π = 𝟙 (P i) := Projective.factorThru_comp _ _
    -- `⨁_{Fin m} Q ≅ ⨁ (over Fin m × κ) f`, a biproduct of indecomposables.
    let E1 : (⨁ fun _ : Fin m => Q) ≅ ⨁ (fun p : Σ _ : Fin m, κ => f p.2) :=
      biproduct.mapIso (fun _ : Fin m => e) ≪≫
        biproductBiproductIso (fun _ : Fin m => κ) (fun _ : Fin m => f)
    -- `P i` is therefore an indecomposable retract of `⨁ F`.
    let F : (Σ _ : Fin m, κ) → C := fun p => f p.2
    have hF : ∀ p, CategoryTheory.Indecomposable (F p) := fun p => (hf p.2).2
    have hsr : (t ≫ E1.hom) ≫ (E1.inv ≫ π) = 𝟙 (P i) := by
      rw [Category.assoc, ← Category.assoc E1.hom, E1.hom_inv_id, Category.id_comp, ht]
    obtain ⟨p, ⟨iso⟩⟩ :=
      indecomposable_summand_iso_factor F hF (hindec i) (t ≫ E1.hom) (E1.inv ≫ π) hsr
    -- `P i ≅ F p = f p.2 ≅ P (g p.2)`, so `g p.2 = i` by distinctness.
    have : i = g p.2 := hdistinct i (g p.2) ⟨iso ≪≫ fiso p.2⟩
    exact Fintype.card_pos_iff.mpr ⟨⟨p.2, this.symm⟩⟩
  -- Step 4: assemble `Q ≅ multBiproduct P n` by reindexing `⨁ f` along `σ` with the isos.
  refine ⟨n, hpos, ⟨?_⟩⟩
  let w : ∀ p : Σ i, Fin (n i), f (σ p) ≅ P p.1 :=
    fun p => fiso (σ p) ≪≫ eqToIso (congrArg P (hgσ p))
  exact e ≪≫ (biproduct.whiskerEquiv σ w).symm

/-- **Etingof §9.7 classification of projective generators.**

Let `P : ι → 𝒞` be the indecomposable projective objects of a finite abelian category
`𝒞` (each indecomposable, pairwise non-isomorphic, exhausting the indecomposable
projectives, with `⨁ P` a progenerator). Then an object `Q` is a projective generator
**iff** `Q ≅ ⊕_i n_i P_i` for some multiplicities `n_i ≥ 1`.

This is Etingof §9.7's `P_𝐧 = ⊕_{i=1}^m n_i P_i, n_i ≥ 1` classification ("check it!").
The backward direction is proved in full; the forward direction is the Krull–Schmidt
content isolated in `progenerator_decomposition`. -/
theorem progenerator_iff_multBiproduct {ι : Type v} [Fintype ι] (P : ι → C)
    (hproj : ∀ i, Projective (P i)) (hindec : ∀ i, CategoryTheory.Indecomposable (P i))
    (hdistinct : ∀ i j, Nonempty (P i ≅ P j) → i = j)
    (hcomplete : ∀ R : C, Projective R → CategoryTheory.Indecomposable R → ∃ i, Nonempty (R ≅ P i))
    [hgen : IsProgenerator (⨁ P)] (Q : C) :
    IsProgenerator Q ↔
      ∃ n : ι → ℕ, (∀ i, 1 ≤ n i) ∧ Nonempty (Q ≅ multBiproduct P n) := by
  haveI : ∀ i, Projective (P i) := hproj
  constructor
  · intro hQ
    exact progenerator_decomposition P hproj hindec hdistinct hcomplete hgen Q hQ
  · rintro ⟨n, hn, ⟨e⟩⟩
    haveI := isProgenerator_multBiproduct P n hn
    exact IsProgenerator.of_iso e

end Classification

end Etingof
