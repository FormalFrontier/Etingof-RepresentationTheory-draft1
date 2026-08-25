import EtingofRepresentationTheory.Chapter9.Problem9_5_3

/-!
# Problem 9.5.3(i): the named block ↔ idempotent bijection and idempotent support

`Problem9_5_3.lean` proves that the blocks of a finite dimensional algebra `R` are in bijection
with its indecomposable central idempotents, but only in the proof-irrelevant form
`Nonempty (Block R ≃ {e // IsIndecomposableCentralIdempotent R e})`: a client cannot recover
*which* idempotent belongs to a given block, and nothing is said about how that idempotent acts
on the modules of the block.

This file supplies the missing content.

* `Etingof.Problem953.eq_of_mul_ne_zero` — distinct indecomposable central idempotents are
  orthogonal (no finiteness needed).
* `Etingof.Problem953.simpleIdempotent` — the unique indecomposable central idempotent acting as
  the identity on a given simple module, with `simpleIdempotent_smul` and
  `simpleIdempotent_unique` as its defining pair.
* `Etingof.Problem953.blockIdempotent` — the induced *named* map `Block R → {indecomposable
  central idempotents}`, well defined because linked simples share their central character.
* `Etingof.Problem953.inBlock_iff_simpleIdempotent_smul` — the **support characterization**: a
  module lies in the block of `S` iff the block's idempotent acts on it as the identity. Note
  that no finiteness hypothesis on the module is needed on either side.
* `Etingof.Problem953.smul_eq_zero_of_inBlock_of_ne` — the complementary idempotents act by zero
  on the block.
* `Etingof.Problem953.blockEquivIndecomposableCentralIdempotent` — the bijection itself, as a
  named `Equiv` whose forward map is `blockIdempotent`.
* `Etingof.Problem953.blocks_equiv_indecomposableCentralIdempotents` — the original bare
  `Nonempty` statement, now a one-line corollary.

The categorical half of the book's statement ("`𝒞ₖ` is the category of `eₖ A`-modules") is built
on top of the support characterization in `Problem9_5_3_BlockCategory.lean`.
-/

universe v u

open CategoryTheory

namespace Etingof

namespace Problem953

variable (R : Type u) [Ring R]

/-- **Distinct indecomposable central idempotents are orthogonal.** If `f * g ≠ 0` for two
indecomposable central idempotents then `f = g`.

Indeed `f = f * g + (f - f * g)` is a splitting of `f` into two orthogonal central idempotents,
so indecomposability of `f` and `f * g ≠ 0` force `f = f * g`; symmetrically `g = g * f`, and
`f * g = g * f` by centrality. No finiteness hypothesis is needed. -/
theorem eq_of_mul_ne_zero {f g : R}
    (hf : IsIndecomposableCentralIdempotent R f) (hg : IsIndecomposableCentralIdempotent R g)
    (hfg : f * g ≠ 0) : f = g := by
  obtain ⟨-, hfi, hfc, hfns⟩ := hf
  obtain ⟨-, hgi, hgc, hgns⟩ := hg
  have hcomm : f * g = g * f := hfc g
  -- `f * g` is a central idempotent.
  have hprod_comm : ∀ y : R, f * g * y = y * (f * g) := by
    intro y
    rw [mul_assoc, hgc y, ← mul_assoc, hfc y, mul_assoc]
  have hprod_idem : IsIdempotentElem (f * g) := by
    change f * g * (f * g) = f * g
    rw [mul_assoc, ← mul_assoc g f g, ← hcomm, mul_assoc f g g, hgi.eq, ← mul_assoc, hfi.eq]
  have hffg : f * (f * g) = f * g := by rw [← mul_assoc, hfi.eq]
  have hfgf : f * g * f = f * g := by rw [mul_assoc, ← hcomm, ← mul_assoc, hfi.eq]
  -- `f - f * g` is a central idempotent orthogonal to `f * g`, and the two sum to `f`.
  have hrest_comm : ∀ y : R, (f - f * g) * y = y * (f - f * g) := by
    intro y
    rw [sub_mul, mul_sub, hfc y, hprod_comm y]
  have hrest_idem : IsIdempotentElem (f - f * g) := by
    change (f - f * g) * (f - f * g) = f - f * g
    rw [sub_mul, mul_sub, mul_sub, hfi.eq, hffg, hfgf, hprod_idem.eq]
    abel
  have hortho : (f * g) * (f - f * g) = 0 := by
    rw [mul_sub, hprod_idem.eq, hfgf, sub_self]
  have hsum : f = f * g + (f - f * g) := by abel
  -- Indecomposability of `f` kills the second summand, so `f = f * g`.
  have hf_eq : f = f * g := by
    by_contra hne
    exact hfns ⟨f * g, f - f * g, hfg, fun h0 => hne (by rw [← sub_eq_zero]; exact h0),
      hprod_idem, hrest_idem, hprod_comm, hrest_comm, hortho, hsum⟩
  -- The same argument for `g`, using `g * f = f * g ≠ 0`.
  have hgf : g * f ≠ 0 := by rw [← hcomm]; exact hfg
  have hprod_comm' : ∀ y : R, g * f * y = y * (g * f) := by
    intro y
    rw [mul_assoc, hfc y, ← mul_assoc, hgc y, mul_assoc]
  have hprod_idem' : IsIdempotentElem (g * f) := by
    change g * f * (g * f) = g * f
    rw [mul_assoc, ← mul_assoc f g f, hcomm, mul_assoc g f f, hfi.eq, ← mul_assoc, hgi.eq]
  have hggf : g * (g * f) = g * f := by rw [← mul_assoc, hgi.eq]
  have hgfg : g * f * g = g * f := by rw [mul_assoc, hcomm, ← mul_assoc, hgi.eq]
  have hrest_comm' : ∀ y : R, (g - g * f) * y = y * (g - g * f) := by
    intro y
    rw [sub_mul, mul_sub, hgc y, hprod_comm' y]
  have hrest_idem' : IsIdempotentElem (g - g * f) := by
    change (g - g * f) * (g - g * f) = g - g * f
    rw [sub_mul, mul_sub, mul_sub, hgi.eq, hggf, hgfg, hprod_idem'.eq]
    abel
  have hortho' : (g * f) * (g - g * f) = 0 := by
    rw [mul_sub, hprod_idem'.eq, hgfg, sub_self]
  have hg_eq : g = g * f := by
    by_contra hne
    exact hgns ⟨g * f, g - g * f, hgf, fun h0 => hne (by rw [← sub_eq_zero]; exact h0),
      hprod_idem', hrest_idem', hprod_comm', hrest_comm', hortho', by abel⟩
  rw [hf_eq, hcomm, ← hg_eq]

/-- **Uniqueness of the idempotent of a simple module.** Two indecomposable central idempotents
acting as the identity on the same simple module coincide: their product acts as the identity on
a nonzero vector, hence is nonzero, and `eq_of_mul_ne_zero` applies. -/
theorem eq_of_actsAsOne {f g : R}
    (hf : IsIndecomposableCentralIdempotent R f) (hg : IsIndecomposableCentralIdempotent R g)
    {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (hfS : ∀ m : (S : Type v), f • m = m) (hgS : ∀ m : (S : Type v), g • m = m) : f = g := by
  haveI := hS
  haveI : Nontrivial (S : Type v) := IsSimpleModule.nontrivial R (S : Type v)
  obtain ⟨s, hs⟩ := exists_ne (0 : (S : Type v))
  refine eq_of_mul_ne_zero R hf hg (fun h0 => hs ?_)
  have h1 : (f * g) • s = s := by rw [mul_smul, hgS s, hfS s]
  rw [h0, zero_smul] at h1
  exact h1.symm

section FiniteDimensional

variable (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R]

include k

/-- A finite dimensional algebra has finite length as a module over itself. -/
theorem isFiniteLength_self : IsFiniteLength R R := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

/-- **Existence and uniqueness of the idempotent of a simple module.** Over a finite dimensional
algebra, exactly one indecomposable central idempotent acts as the identity on a given simple
module: existence comes from the complete orthogonal family `1 = ∑ eₖ`
(`exists_completeOrthogonal_isIndecomposableCentral` together with
`existsUnique_actsAsOne_of_completeOrthogonal`), uniqueness from `eq_of_actsAsOne`. -/
theorem existsUnique_indecomposableCentralIdempotent_actsAsOne {S : ModuleCat.{v} R}
    (hS : IsSimpleModule R S) :
    ∃! e : {e : R // IsIndecomposableCentralIdempotent R e}, ∀ m : (S : Type v), e.1 • m = m := by
  obtain ⟨ι, hFin, e, hsum, hortho, hindec, _⟩ :=
    exists_completeOrthogonal_isIndecomposableCentral (R := R) (k := k)
  letI : Fintype ι := hFin
  obtain ⟨i, hi, -⟩ := existsUnique_actsAsOne_of_completeOrthogonal R e hsum hortho
    (fun i => (hindec i).2.1) (fun i => (hindec i).2.2.1) hS
  refine ⟨⟨e i, hindec i⟩, hi, ?_⟩
  rintro ⟨f, hf⟩ hfS
  exact Subtype.ext (eq_of_actsAsOne R hf (hindec i) hS hfS hi)

/-- **The idempotent of a simple module.** The unique indecomposable central idempotent of a
finite dimensional algebra acting as the identity on the simple module `S`; by
`simpleIdempotent_eq_of_areLinked` it depends only on the linkage class (block) of `S`. -/
noncomputable def simpleIdempotent {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    {e : R // IsIndecomposableCentralIdempotent R e} :=
  (existsUnique_indecomposableCentralIdempotent_actsAsOne R k hS).choose

/-- The idempotent of a simple module acts on it as the identity. -/
theorem simpleIdempotent_smul {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    ∀ m : (S : Type v), (simpleIdempotent R k hS).1 • m = m :=
  (existsUnique_indecomposableCentralIdempotent_actsAsOne R k hS).choose_spec.1

/-- The idempotent of a simple module is the *only* indecomposable central idempotent acting on
it as the identity. -/
theorem simpleIdempotent_unique {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) {f : R}
    (hf : IsIndecomposableCentralIdempotent R f) (hfS : ∀ m : (S : Type v), f • m = m) :
    f = (simpleIdempotent R k hS).1 :=
  eq_of_actsAsOne R hf (simpleIdempotent R k hS).2 hS hfS (simpleIdempotent_smul R k hS)

/-- **Linkage invariance of the idempotent.** Linked simple modules have the same idempotent:
this is what makes `blockIdempotent` well defined on blocks. -/
theorem simpleIdempotent_eq_of_areLinked [Small.{v} R] {S T : ModuleCat.{v} R}
    (hS : IsSimpleModule R S) (hT : IsSimpleModule R T) (h : Etingof.AreLinked R S T) :
    simpleIdempotent R k hS = simpleIdempotent R k hT :=
  Subtype.ext (simpleIdempotent_unique R k hT (simpleIdempotent R k hS).2
    ((actsAsId_iff_of_areLinked R
      ⟨(simpleIdempotent R k hS).1, (simpleIdempotent R k hS).2.2.1,
        (simpleIdempotent R k hS).2.2.2.1⟩ h).mp (simpleIdempotent_smul R k hS)))

/-- **The idempotent of a block (Problem 9.5.3(i), forward map).** Each block `𝒞ₖ` of a finite
dimensional algebra determines an indecomposable central idempotent `eₖ`: the unique one acting
as the identity on the simple modules of the block. This is the data erased by the bare
`Nonempty (Block R ≃ …)` statement. -/
noncomputable def blockIdempotent [Small.{v} R] :
    Etingof.Block.{v} R → {e : R // IsIndecomposableCentralIdempotent R e} :=
  Quotient.lift (fun X : Etingof.SimpleObj.{v} R => simpleIdempotent R k X.2)
    (fun a b hab => simpleIdempotent_eq_of_areLinked R k a.2 b.2 hab)

@[simp]
theorem blockIdempotent_mk [Small.{v} R] {S : ModuleCat.{v} R} (hS : IsSimpleModule R S) :
    blockIdempotent R k (Quotient.mk (Etingof.blockSetoid R) ⟨S, hS⟩) = simpleIdempotent R k hS :=
  rfl

end FiniteDimensional

section Support

variable [Small.{v} R]

omit [Small.{v} R] in
/-- **A central element acting as zero descends to composition factors.** The zero-action
counterpart of `actsAsOne_of_isCompositionFactor`. -/
theorem actsAsZero_of_isCompositionFactor {M S : ModuleCat.{v} R} {f : R}
    (hM : ∀ m : (M : Type v), f • m = 0) (h : Etingof.IsCompositionFactor R M S) :
    ∀ s : (S : Type v), f • s = 0 := by
  rw [Etingof.isCompositionFactor_iff] at h
  obtain ⟨_, Q, g, hg⟩ := h
  intro s
  obtain ⟨q, rfl⟩ := hg s
  rw [← map_smul, show f • q = 0 from
    Subtype.ext (by rw [SetLike.val_smul, ZeroMemClass.coe_zero]; exact hM q.val), map_zero]

/-- A simple module on which a given indecomposable central idempotent acts as the identity; its
block is the inverse image of the idempotent under `blockIdempotent`. -/
noncomputable def idempotentSimple (e : {e : R // IsIndecomposableCentralIdempotent R e}) :
    ModuleCat.{v} R :=
  (exists_simple_actsAsOne R e.2.1 e.2.2.1 e.2.2.2.1).choose

/-- `idempotentSimple` is a simple module. -/
theorem idempotentSimple_isSimpleModule (e : {e : R // IsIndecomposableCentralIdempotent R e}) :
    IsSimpleModule R (idempotentSimple.{v} R e) :=
  (exists_simple_actsAsOne R e.2.1 e.2.2.1 e.2.2.2.1).choose_spec.1

/-- The idempotent acts as the identity on `idempotentSimple`. -/
theorem idempotentSimple_smul (e : {e : R // IsIndecomposableCentralIdempotent R e}) :
    ∀ m : (idempotentSimple.{v} R e : Type v), e.1 • m = m :=
  (exists_simple_actsAsOne R e.2.1 e.2.2.1 e.2.2.2.1).choose_spec.2

variable (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R]

include k

/-- **Support characterization of a block (Problem 9.5.3(i), module form).** A module `M` lies in
the block of the simple module `S` exactly when the block's idempotent acts on `M` as the
identity. This is the statement the bare indexing bijection erases: it identifies the block
`𝒞ₖ ⊆ Mod R` with the modules supported by `eₖ`.

Neither direction needs a finiteness hypothesis on `M`. Left to right: `(1 - eₖ) M` is a
submodule on which `eₖ` acts as `0`, so a composition factor of it would be a composition factor
of `M` on which `eₖ` acts both as `0` (by `actsAsZero_of_isCompositionFactor`) and as the identity
(by linkage invariance, `M` being in the block); hence `(1 - eₖ) M = 0`. Right to left: every
composition factor of `M` inherits the identity action, and `areLinked_of_actsAsOne_common` links
it to `S`. -/
theorem inBlock_iff_simpleIdempotent_smul {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    (M : ModuleCat.{v} R) :
    Etingof.InBlock R S M ↔ ∀ m : (M : Type v), (simpleIdempotent R k hS).1 • m = m := by
  set f : R := (simpleIdempotent R k hS).1 with hf
  have hfidem : IsIdempotentElem f := (simpleIdempotent R k hS).2.2.1
  have hfcentral : ∀ y : R, f * y = y * f := (simpleIdempotent R k hS).2.2.2.1
  constructor
  · intro hM
    -- `ψ : m ↦ m - f • m` is `R`-linear, and `f` acts as `0` on its range.
    let φ : (M : Type v) →ₗ[R] (M : Type v) :=
      { toFun := fun m => f • m
        map_add' := fun m₁ m₂ => smul_add f m₁ m₂
        map_smul' := fun r m => by simp only [RingHom.id_apply, smul_smul, hfcentral r] }
    let ψ : (M : Type v) →ₗ[R] (M : Type v) := LinearMap.id - φ
    have hψ_apply : ∀ m : (M : Type v), ψ m = m - f • m := fun m => rfl
    have hzero : ∀ q : (LinearMap.range ψ : Type v), f • q = 0 := by
      intro q
      obtain ⟨m, hm⟩ := q.2
      refine Subtype.ext ?_
      rw [SetLike.val_smul, ZeroMemClass.coe_zero, ← hm, hψ_apply, smul_sub, smul_smul,
        hfidem.eq, sub_self]
    -- The range is trivial, since a composition factor of it is impossible.
    have hbot : LinearMap.range ψ = ⊥ := by
      by_contra hne
      haveI : Nontrivial (LinearMap.range ψ : Type v) := Submodule.nontrivial_iff_ne_bot.mpr hne
      obtain ⟨U, hU⟩ :=
        Etingof.exists_isCompositionFactor (M := ModuleCat.of R (LinearMap.range ψ : Type v))
      have hUM : Etingof.IsCompositionFactor R M U :=
        Etingof.IsCompositionFactor.of_submodule (LinearMap.range ψ) hU
      -- `f` acts as `0` on `U` ...
      have hU0 : ∀ u : (U : Type v), f • u = 0 :=
        actsAsZero_of_isCompositionFactor R
          (M := ModuleCat.of R (LinearMap.range ψ : Type v))
          hzero hU
      -- ... and as the identity, since `U` is linked to `S`.
      have hU1 : ∀ u : (U : Type v), f • u = u :=
        (actsAsId_iff_of_areLinked R ⟨f, hfidem, hfcentral⟩
          ((Etingof.areLinked_equivalence R).symm (hM U hUM))).mp (simpleIdempotent_smul R k hS)
      haveI := hU.1
      haveI : Nontrivial (U : Type v) := IsSimpleModule.nontrivial R (U : Type v)
      obtain ⟨u, hu⟩ := exists_ne (0 : (U : Type v))
      exact hu ((hU1 u).symm.trans (hU0 u))
    intro m
    have hm : ψ m = 0 := by
      have hmem : ψ m ∈ LinearMap.range ψ := ⟨m, rfl⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot R).mp hmem
    rw [hψ_apply] at hm
    exact (sub_eq_zero.mp hm).symm
  · intro hM T hT
    have hTf : ∀ t : (T : Type v), f • t = t :=
      actsAsOne_of_isCompositionFactor R hM hT
    exact areLinked_of_actsAsOne_common R (isFiniteLength_self R k) (simpleIdempotent R k hS).2
      hT.1 hS hTf (simpleIdempotent_smul R k hS)

/-- **The complementary idempotents kill the block.** An indecomposable central idempotent other
than the block's own acts by zero on every module of the block: distinct indecomposable central
idempotents are orthogonal (`eq_of_mul_ne_zero`), and the block's idempotent acts as the identity
(`inBlock_iff_simpleIdempotent_smul`). Together with that theorem this is the full "supported
module category" statement: `M ∈ 𝒞ₖ` iff `eₖ` acts as `1` and every `eₗ`, `l ≠ k`, acts as `0`. -/
theorem smul_eq_zero_of_inBlock_of_ne {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)
    {M : ModuleCat.{v} R} (hM : Etingof.InBlock R S M) {e : R}
    (he : IsIndecomposableCentralIdempotent R e) (hne : e ≠ (simpleIdempotent R k hS).1) :
    ∀ m : (M : Type v), e • m = 0 := by
  intro m
  have hmul : e * (simpleIdempotent R k hS).1 = 0 := by
    by_contra h0
    exact hne (eq_of_mul_ne_zero R he (simpleIdempotent R k hS).2 h0)
  have h1 : (simpleIdempotent R k hS).1 • m = m :=
    (inBlock_iff_simpleIdempotent_smul R k hS M).mp hM m
  calc e • m = e • ((simpleIdempotent R k hS).1 • m) := by rw [h1]
    _ = (e * (simpleIdempotent R k hS).1) • m := (mul_smul _ _ m).symm
    _ = 0 := by rw [hmul, zero_smul]

/-- **Problem 9.5.3(i), as a named bijection.** The blocks of a finite dimensional algebra are in
bijection with its indecomposable central idempotents, via `blockIdempotent`: a block is sent to
the idempotent acting as the identity on its simple modules, and an idempotent `e` to the block of
any simple module on which `e` acts as the identity (`idempotentSimple`; such a module exists by
`exists_simple_actsAsOne` and is unique up to linkage by `areLinked_of_actsAsOne_common`). -/
noncomputable def blockEquivIndecomposableCentralIdempotent :
    Etingof.Block.{v} R ≃ {e : R // IsIndecomposableCentralIdempotent R e} where
  toFun := blockIdempotent R k
  invFun e :=
    Quotient.mk (Etingof.blockSetoid R)
      ⟨idempotentSimple R e, idempotentSimple_isSimpleModule R e⟩
  left_inv := by
    refine Quotient.ind (fun X => ?_)
    refine Quotient.sound ?_
    change Etingof.AreLinked R (idempotentSimple R (simpleIdempotent R k X.2)) X.1
    exact areLinked_of_actsAsOne_common R (isFiniteLength_self R k)
      (simpleIdempotent R k X.2).2
      (idempotentSimple_isSimpleModule R (simpleIdempotent R k X.2)) X.2
      (idempotentSimple_smul R (simpleIdempotent R k X.2)) (simpleIdempotent_smul R k X.2)
  right_inv e :=
    Subtype.ext
      (simpleIdempotent_unique R k (idempotentSimple_isSimpleModule R e) e.2
        (idempotentSimple_smul R e)).symm

@[simp]
theorem blockEquivIndecomposableCentralIdempotent_apply (b : Etingof.Block.{v} R) :
    blockEquivIndecomposableCentralIdempotent R k b = blockIdempotent R k b :=
  rfl

/-- **Problem 9.5.3(i), bare form.** The indexing bijection between blocks and indecomposable
central idempotents, now a corollary of the named equivalence. -/
theorem blocks_equiv_indecomposableCentralIdempotents :
    Nonempty (Etingof.Block.{v} R ≃ {e : R // IsIndecomposableCentralIdempotent R e}) :=
  ⟨blockEquivIndecomposableCentralIdempotent R k⟩

end Support

end Problem953

end Etingof
