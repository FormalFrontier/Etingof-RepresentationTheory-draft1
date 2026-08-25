import Mathlib
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3
import EtingofRepresentationTheory.Chapter4.Exercise4_2_3_BaseChangePiMatrix

/-!
# Base change of a semisimple algebra can only increase the number of simple modules

The separability-free base-change monotonicity `#(simple k[G]) ≤ #(simple K[G])` reduces to
the semisimple quotient `k[G]/rad`, so we never need semisimplicity of `K ⊗_k M` for a
general module `M` (which fails for an inseparable `K/k`). Only base change of the
already-semisimple algebra is needed, and that count inequality holds with no separability
hypothesis:

```
Nat.card (SimpleModuleClasses A) ≤ Nat.card (SimpleModuleClasses (K ⊗[k] A))
```

for a finite-dimensional semisimple `k`-algebra `A` and any field extension `K ⊇ k`.

## The argument (no separability required)

By Artin–Wedderburn, `A ≅ ∏ i, Matrix (Fin (d i)) (Fin (d i)) (D i)` for division rings
`D i`, so `#(simple A) = |ι|` (one simple per matrix factor). Base change distributes:
`K ⊗ A ≅ ∏ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗ D i)`, and each `K ⊗ D i` is a nonzero
finite-dimensional `K`-algebra, hence has at least one simple module. So
`#(simple (K ⊗ A)) = Σ i, #(simple (K ⊗ D i)) ≥ |ι| = #(simple A)`.

The count rests on four lemmas:

* `simpleModuleClassesCongr`: transports iso-classes of simple modules across an
  equivalence of module categories.
* `simpleModuleClassesPiEquiv`: the simple modules of a finite product of rings are the
  disjoint union of the simple modules of the factors.
* `simpleModuleClassesMatrixEquiv`: Morita invariance, a matrix ring has the same simple
  count as its base ring (from `ModuleCat.matrixEquivalence`).
* `nonempty_simpleModuleClasses` / `subsingleton_simpleModuleClasses_divisionRing`:
  existence and uniqueness of simple modules over nonzero finite-dimensional algebras and
  over division rings.
-/

open CategoryTheory

open scoped TensorProduct

namespace Etingof

universe u

attribute [local instance] CategoryTheory.isIsomorphicSetoid

/-- **Transport of simple iso-classes.** An equivalence of module categories
`E : ModuleCat R ≌ ModuleCat S` induces a bijection between the isomorphism classes of
simple `R`-modules and simple `S`-modules: it restricts to an equivalence of the full
subcategories of simple objects (`simpleProp_iff_of_equivalence`), which descends to
iso-classes by `isoClassesEquivOfEquivalence`. -/
noncomputable def simpleModuleClassesCongr {R S : Type u} [Ring R] [Ring S]
    (E : ModuleCat.{u} R ≌ ModuleCat.{u} S) :
    SimpleModuleClasses.{u} R ≃ SimpleModuleClasses.{u} S :=
  isoClassesEquivOfEquivalence
    (Equivalence.congrFullSubcategory E
      (P := simpleProp (ModuleCat.{u} R)) (Q := simpleProp (ModuleCat.{u} S))
      (funext fun X => propext (simpleProp_iff_of_equivalence E X)))

/-- **Transport of simple iso-classes along a ring isomorphism.** A ring isomorphism
`f : R ≃+* S` induces a bijection of iso-classes of simple modules, via restriction of scalars. -/
noncomputable def simpleModuleClassesCongrRingEquiv {R S : Type u} [Ring R] [Ring S]
    (f : R ≃+* S) : SimpleModuleClasses.{u} R ≃ SimpleModuleClasses.{u} S :=
  simpleModuleClassesCongr (ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm)

/-- **Morita invariance of the simple count for matrix rings.** A matrix ring
`Matrix (Fin m) (Fin m) R` (with `m ≠ 0`) has the same number of iso-classes of simple modules
as `R`, via `ModuleCat.matrixEquivalence`. -/
noncomputable def simpleModuleClassesMatrixEquiv {R : Type u} [Ring R] (m : ℕ) [NeZero m] :
    SimpleModuleClasses.{u} (Matrix (Fin m) (Fin m) R) ≃ SimpleModuleClasses.{u} R :=
  (simpleModuleClassesCongr
    (ModuleCat.matrixEquivalence R (⟨0, Nat.pos_of_neZero m⟩ : Fin m))).symm

/-- **Existence of a simple module.** A nonzero finite-dimensional algebra over a field has
at least one iso-class of simple modules: it is Artinian, so the regular module has a simple
submodule. -/
theorem nonempty_simpleModuleClasses (k : Type u) {B : Type u} [Field k] [Ring B]
    [Nontrivial B] [Algebra k B] [Module.Finite k B] :
    Nonempty (SimpleModuleClasses.{u} B) := by
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  haveI : IsAtomic (Submodule B B) := isAtomic_of_orderBot_wellFounded_lt IsWellFounded.wf
  obtain ⟨m, hm⟩ : ∃ m : Submodule B B, IsSimpleModule B m := by
    simpa only [isSimpleModule_iff_isAtom] using IsAtomic.exists_atom (Submodule B B)
  haveI := hm
  haveI : Simple (ModuleCat.of B (m : Type u)) := inferInstance
  exact ⟨Quotient.mk _ ⟨ModuleCat.of B (m : Type u), this⟩⟩

/-- **Uniqueness of the simple module over a division ring.** Every simple module over a
division ring `D` is isomorphic to `D ⧸ ⊥` (the only maximal left ideal is `⊥`), so there is at
most one iso-class. -/
theorem subsingleton_simpleModuleClasses_divisionRing (D : Type u) [DivisionRing D] :
    Subsingleton (SimpleModuleClasses.{u} D) := by
  -- A simple `D`-module is `≃ₗ D ⧸ I` for a maximal `I`; over a division ring `I = ⊥`.
  have key : ∀ (M : Type u) [AddCommGroup M] [Module D M] [IsSimpleModule D M],
      Nonempty (M ≃ₗ[D] (D ⧸ (⊥ : Ideal D))) := by
    intro M _ _ _
    obtain ⟨I, hmax, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := D) (M := M)).mp ‹_›
    have hI : I = ⊥ := (IsSimpleOrder.eq_bot_or_eq_top I).resolve_right hmax.ne_top
    exact ⟨hI ▸ e⟩
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ P =>
  induction b using Quotient.inductionOn with
  | _ Q =>
  haveI : Simple P.obj := P.property
  haveI : Simple Q.obj := Q.property
  haveI : IsSimpleModule D (P.obj : ModuleCat.{u} D) := inferInstance
  haveI : IsSimpleModule D (Q.obj : ModuleCat.{u} D) := inferInstance
  obtain ⟨eP⟩ := key (P.obj : ModuleCat.{u} D)
  obtain ⟨eQ⟩ := key (Q.obj : ModuleCat.{u} D)
  exact Quotient.sound
    ⟨(simpleProp (ModuleCat.{u} D)).fullyFaithfulι.preimageIso (eP.trans eQ.symm).toModuleIso⟩

/-! ### Simple modules of a finite product of rings

The simple modules of a finite product `∏ i, R i` are the disjoint union, over `i`, of the simple
modules of the factors, pulled back along the (surjective) projections `Pi.evalRingHom R i`. A
simple `∏ R i`-module is "supported" at exactly one factor: the central idempotent
`e i = Pi.single i 1` acts as the identity on it (existence follows from `∑ i, e i = 1`), so the
module is a simple `R i`-module. Conversely every simple `R i`-module inflates to a simple
`∏ R j`-module, and different factors give non-isomorphic modules (an `∏ R j`-isomorphism carries
the action of each `e i` to itself). This yields a bijection
`(Σ i, SimpleModuleClasses (R i)) ≃ SimpleModuleClasses (∏ i, R i)`. -/

section Pi

variable {n : ℕ} (R : Fin n → Type u) [∀ i, Ring (R i)]

/-- The identity map as an isomorphism of `ModuleCat` objects that share a carrier and have equal
scalar actions (used to identify a module with the restriction-then-inflation of itself). -/
private def idModuleIso {S : Type*} [Ring S] {M : Type u} [AddCommGroup M]
    (i₁ i₂ : Module S M) (h : ∀ (s : S) (x : M), (letI := i₁; s • x) = (letI := i₂; s • x)) :
    (letI := i₁; ModuleCat.of S M) ≅ (letI := i₂; ModuleCat.of S M) :=
  @LinearEquiv.toModuleIso S _ M M _ _ i₁ i₂
    (@AddEquiv.toLinearEquiv S M M _ _ _ i₁ i₂ (AddEquiv.refl M) h)

/-- **Inflation of a simple factor module.** Restriction of scalars of a simple `R i`-module along
the surjective projection `Pi.evalRingHom R i : (∀ j, R j) →+* R i` is a simple `∏ R j`-module. -/
private noncomputable def inflatePiObj (i : Fin n)
    (P : (simpleProp (ModuleCat.{u} (R i))).FullSubcategory) :
    (simpleProp (ModuleCat.{u} (∀ j, R j))).FullSubcategory := by
  haveI : Simple P.obj := P.property
  haveI hsP : IsSimpleModule (R i) (P.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
  letI : Module (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) :=
    Module.compHom _ (Pi.evalRingHom R i)
  haveI : RingHomSurjective (Pi.evalRingHom R i) := ⟨fun x => ⟨Pi.single i x, by simp⟩⟩
  haveI : IsSimpleModule (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) :=
    (LinearMap.isSimpleModule_iff_of_bijective
      ({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
        (P.obj : ModuleCat.{u} (R i)) →ₛₗ[Pi.evalRingHom R i]
          (P.obj : ModuleCat.{u} (R i))) Function.bijective_id).mpr hsP
  exact ⟨ModuleCat.of (∀ j, R j) (P.obj : ModuleCat.{u} (R i)), simple_of_isSimpleModule⟩

/-- Inflation on iso-classes: a well-defined map `SimpleModuleClasses (R i) → SimpleModuleClasses
(∏ R j)`. -/
private noncomputable def inflatePiClass (i : Fin n) :
    SimpleModuleClasses.{u} (R i) → SimpleModuleClasses.{u} (∀ j, R j) :=
  Quotient.map (inflatePiObj R i) (by
    rintro P P' ⟨iso⟩
    haveI : Simple P.obj := P.property
    haveI : Simple P'.obj := P'.property
    haveI : IsSimpleModule (R i) (P.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
    haveI : IsSimpleModule (R i) (P'.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
    have eR : (P.obj : ModuleCat.{u} (R i)) ≃ₗ[R i] (P'.obj : ModuleCat.{u} (R i)) :=
      ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
    letI : Module (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) :=
      Module.compHom _ (Pi.evalRingHom R i)
    letI : Module (∀ j, R j) (P'.obj : ModuleCat.{u} (R i)) :=
      Module.compHom _ (Pi.evalRingHom R i)
    refine ⟨(simpleProp (ModuleCat.{u} (∀ j, R j))).fullyFaithfulι.preimageIso
      (LinearEquiv.toModuleIso
        { toFun := eR, invFun := eR.symm, left_inv := eR.left_inv, right_inv := eR.right_inv,
          map_add' := eR.map_add,
          map_smul' := fun s x => eR.map_smul (Pi.evalRingHom R i s) x })⟩)

/-- The backward map `(Σ i, SimpleModuleClasses (R i)) → SimpleModuleClasses (∏ R j)`. -/
private noncomputable def sigmaToPi :
    (Σ i, SimpleModuleClasses.{u} (R i)) → SimpleModuleClasses.{u} (∀ j, R j) :=
  fun p => inflatePiClass R p.1 p.2

/-- **Support index.** A simple `∏ R j`-module has a factor `i` at which the identity idempotent
`e i = Pi.single i 1` acts as the identity. -/
private theorem exists_support_index (M : Type u) [AddCommGroup M] [Module (∀ j, R j) M]
    [IsSimpleModule (∀ j, R j) M] :
    ∃ i, ∀ m : M, (Pi.single i (1 : R i) : ∀ j, R j) • m = m := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial (∀ j, R j) M
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  have hsum : ∑ i, (Pi.single i (1 : R i) : ∀ j, R j) = 1 := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j
      (fun b _ hbj => by simp [hbj]) (fun hj => absurd (Finset.mem_univ j) hj)]
    simp
  have hne : ∃ i, (Pi.single i (1 : R i) : ∀ j, R j) • m₀ ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    apply hm₀
    calc m₀ = (1 : ∀ j, R j) • m₀ := (one_smul _ _).symm
      _ = (∑ i, (Pi.single i (1 : R i) : ∀ j, R j)) • m₀ := by rw [hsum]
      _ = ∑ i, (Pi.single i (1 : R i) : ∀ j, R j) • m₀ := Finset.sum_smul
      _ = 0 := Finset.sum_eq_zero (fun i _ => h i)
  obtain ⟨i, hi⟩ := hne
  refine ⟨i, ?_⟩
  set e : (∀ j, R j) := Pi.single i (1 : R i) with he
  have hcentral : ∀ s : ∀ j, R j, e * s = s * e := by
    intro s; funext j
    rcases eq_or_ne i j with h | h
    · subst h; simp [he, Pi.single_eq_same]
    · simp [he, Pi.single_eq_of_ne (Ne.symm h)]
  have hidem : e * e = e := by
    funext j
    rcases eq_or_ne i j with h | h
    · subst h; simp [he, Pi.single_eq_same]
    · simp [he, Pi.single_eq_of_ne (Ne.symm h)]
  let g : M →ₗ[∀ j, R j] M :=
    { toFun := fun m => e • m
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun s m => by
        simp only [RingHom.id_apply]
        rw [← mul_smul, ← mul_smul, hcentral s] }
  have hg : ∀ m, g m = e • m := fun _ => rfl
  have hrange : LinearMap.range g = ⊤ := by
    rcases eq_bot_or_eq_top (LinearMap.range g) with h | h
    · exfalso
      apply hi
      have hmem : g m₀ ∈ LinearMap.range g := ⟨m₀, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      exact hmem
    · exact h
  intro m
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp hrange m
  rw [hg] at hx
  rw [← hx, ← mul_smul, hidem]

/-- The backward map is injective: an `∏ R j`-isomorphism of inflated modules forces the factor
indices to agree, and then descends to an `R i`-isomorphism. -/
private theorem sigmaToPi_injective : Function.Injective (sigmaToPi R) := by
  rintro ⟨i, c⟩ ⟨i', c'⟩ hEq
  induction c using Quotient.inductionOn with | _ P => ?_
  induction c' using Quotient.inductionOn with | _ P' => ?_
  have hEq' : (Quotient.mk _ (inflatePiObj R i P) : SimpleModuleClasses.{u} (∀ j, R j))
      = Quotient.mk _ (inflatePiObj R i' P') := hEq
  obtain ⟨iso⟩ := Quotient.exact hEq'
  haveI : Simple P.obj := P.property
  haveI : Simple P'.obj := P'.property
  haveI hsP : IsSimpleModule (R i) (P.obj : ModuleCat.{u} (R i)) := isSimpleModule_of_simple _
  haveI hsP' : IsSimpleModule (R i') (P'.obj : ModuleCat.{u} (R i')) := isSimpleModule_of_simple _
  letI : Module (∀ j, R j) (P.obj : ModuleCat.{u} (R i)) := Module.compHom _ (Pi.evalRingHom R i)
  letI : Module (∀ j, R j) (P'.obj : ModuleCat.{u} (R i')) :=
    Module.compHom _ (Pi.evalRingHom R i')
  have φ : (P.obj : ModuleCat.{u} (R i)) ≃ₗ[∀ j, R j] (P'.obj : ModuleCat.{u} (R i')) :=
    ((ObjectProperty.ι _).mapIso iso).toLinearEquiv
  have hii : i = i' := by
    by_contra hne
    have hsrc : ∀ p : (P.obj : ModuleCat.{u} (R i)),
        (Pi.single i (1 : R i) : ∀ j, R j) • p = p := by
      intro p
      change (Pi.single i (1 : R i)) i • p = p
      rw [Pi.single_eq_same, one_smul]
    have htgt : ∀ q : (P'.obj : ModuleCat.{u} (R i')),
        (Pi.single i (1 : R i) : ∀ j, R j) • q = 0 := by
      intro q
      change (Pi.single i (1 : R i)) i' • q = 0
      rw [Pi.single_eq_of_ne (Ne.symm hne), zero_smul]
    haveI : Nontrivial (P.obj : ModuleCat.{u} (R i)) := IsSimpleModule.nontrivial (R i) _
    obtain ⟨p, hp⟩ := exists_ne (0 : (P.obj : ModuleCat.{u} (R i)))
    have hz : φ p = 0 := by
      have hmap := φ.map_smul (Pi.single i (1 : R i)) p
      rw [hsrc p] at hmap
      rw [htgt (φ p)] at hmap
      exact hmap
    exact hp (φ.injective (hz.trans (map_zero φ).symm))
  subst hii
  refine congrArg (Sigma.mk i) (Quotient.sound ?_)
  refine ⟨(simpleProp (ModuleCat.{u} (R i))).fullyFaithfulι.preimageIso (LinearEquiv.toModuleIso
    { toFun := φ, invFun := φ.symm, left_inv := φ.left_inv, right_inv := φ.right_inv,
      map_add' := φ.map_add,
      map_smul' := fun r p => by
        simp only [RingHom.id_apply]
        have h1 : (r : R i) • (p : (P.obj : ModuleCat.{u} (R i)))
            = (Pi.single i r : ∀ j, R j) • p := by
          change r • p = (Pi.single i r) i • p
          rw [Pi.single_eq_same]
        have h2 : (r : R i) • (φ p : (P'.obj : ModuleCat.{u} (R i)))
            = (Pi.single i r : ∀ j, R j) • φ p := by
          change r • φ p = (Pi.single i r) i • φ p
          rw [Pi.single_eq_same]
        rw [h1, h2, φ.map_smul] })⟩

/-- The backward map is surjective: a simple `∏ R j`-module is the inflation of a simple module over
its support factor. -/
private theorem sigmaToPi_surjective : Function.Surjective (sigmaToPi R) := by
  intro c
  induction c using Quotient.inductionOn with | _ M => ?_
  haveI : Simple M.obj := M.property
  haveI hsM : IsSimpleModule (∀ j, R j) (M.obj : ModuleCat.{u} (∀ j, R j)) :=
    isSimpleModule_of_simple _
  obtain ⟨i, hsupp⟩ := exists_support_index R (M.obj : ModuleCat.{u} (∀ j, R j))
  letI factor : Module (R i) (M.obj : ModuleCat.{u} (∀ j, R j)) :=
    { smul := fun r m => (Pi.single i r : ∀ j, R j) • m
      one_smul := fun m => hsupp m
      mul_smul := fun r r' m => by
        change (Pi.single i (r * r') : ∀ j, R j) • m
            = (Pi.single i r : ∀ j, R j) • ((Pi.single i r' : ∀ j, R j) • m)
        rw [← mul_smul]
        congr 1
        funext j
        rcases eq_or_ne i j with h | h
        · subst h; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne (Ne.symm h)]
      smul_zero := fun r => smul_zero _
      smul_add := fun r a b => smul_add _ _ _
      add_smul := fun r r' m => by
        change (Pi.single i (r + r') : ∀ j, R j) • m
            = (Pi.single i r : ∀ j, R j) • m + (Pi.single i r' : ∀ j, R j) • m
        rw [Pi.single_add, add_smul]
      zero_smul := fun m => by
        change (Pi.single i (0 : R i) : ∀ j, R j) • m = 0
        rw [Pi.single_zero, zero_smul] }
  have hrecover : ∀ (s : ∀ j, R j) (m : (M.obj : ModuleCat.{u} (∀ j, R j))),
      (Pi.single i (s i) : ∀ j, R j) • m = s • m := by
    intro s m
    have hs : (Pi.single i (s i) : ∀ j, R j) = s * Pi.single i (1 : R i) := by
      funext j
      rcases eq_or_ne i j with h | h
      · subst h; simp [Pi.single_eq_same]
      · simp [Pi.single_eq_of_ne (Ne.symm h)]
    rw [hs, mul_smul, hsupp m]
  haveI hsFactor : letI := factor; IsSimpleModule (R i) (M.obj : ModuleCat.{u} (∀ j, R j)) := by
    letI := factor
    haveI : RingHomSurjective (Pi.evalRingHom R i) := ⟨fun x => ⟨Pi.single i x, by simp⟩⟩
    -- Restricting the `factor` structure back along `evalRingHom` recovers the original action
    -- (`hrecover`), so the identity is a semilinear bijection from the original module to `factor`.
    exact (LinearMap.isSimpleModule_iff_of_bijective
      (σ := Pi.evalRingHom R i)
      ({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun s m => (hrecover s m).symm } :
        (M.obj : ModuleCat.{u} (∀ j, R j)) →ₛₗ[Pi.evalRingHom R i]
          (M.obj : ModuleCat.{u} (∀ j, R j))) Function.bijective_id).mp hsM
  let P₀ : (simpleProp (ModuleCat.{u} (R i))).FullSubcategory :=
    ⟨letI := factor; ModuleCat.of (R i) (M.obj : ModuleCat.{u} (∀ j, R j)),
     letI := factor; letI := hsFactor; simple_of_isSimpleModule⟩
  refine ⟨⟨i, Quotient.mk _ P₀⟩, ?_⟩
  have hiso := idModuleIso
    (Module.compHom (M.obj : ModuleCat.{u} (∀ j, R j)) (Pi.evalRingHom R i))
    M.obj.isModule
    (fun s m => by
      change (Pi.single i (s i) : ∀ j, R j) • m = s • m
      exact hrecover s m)
  exact Quotient.sound
    ⟨(simpleProp (ModuleCat.{u} (∀ j, R j))).fullyFaithfulι.preimageIso hiso⟩

/-- **Simple modules of a finite product of rings.** The isomorphism classes of simple modules over
`∏ i, R i` are in bijection with the disjoint union over `i` of the classes of simple `R i`-modules,
via inflation along the projections. -/
private noncomputable def simpleModuleClassesPiEquiv :
    (Σ i, SimpleModuleClasses.{u} (R i)) ≃ SimpleModuleClasses.{u} (∀ j, R j) :=
  Equiv.ofBijective (sigmaToPi R) ⟨sigmaToPi_injective R, sigmaToPi_surjective R⟩

end Pi

/-- **Counting simple modules of a finite product.** When each factor has finitely many simple
modules, the simple count of `∏ i, R i` is the sum of the factors' simple counts. (The finiteness
hypothesis is necessary: a factor with infinitely many simple modules makes both sides diverge
independently, e.g. `k × k[x]`.) -/
theorem natCard_simpleModuleClasses_pi {n : ℕ} (R : Fin n → Type u) [∀ i, Ring (R i)]
    [∀ i, Finite (SimpleModuleClasses.{u} (R i))] :
    Nat.card (SimpleModuleClasses.{u} (∀ i, R i))
      = ∑ i, Nat.card (SimpleModuleClasses.{u} (R i)) := by
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (simpleModuleClassesPiEquiv R)).symm

/-- **Base change of a semisimple algebra can only increase the number of simple modules.**
For a finite-dimensional semisimple `k`-algebra `A` and any field extension `K ⊇ k`,
`#(simple A) ≤ #(simple (K ⊗[k] A))`. Separability-free: no hypothesis on `K/k`.

Proof: by Artin–Wedderburn `A ≃ₐ[k] ∏ i, Matrix (Fin (d i)) (Fin (d i)) (D i)`, so
`#(simple A) = ∑ i, #(simple (Matrix … (D i))) = ∑ i, #(simple (D i)) = ∑ i, 1 = n`
(matrix Morita invariance and uniqueness of the simple module over a division ring). Base change
distributes to `K ⊗ A ≃ₐ[K] ∏ i, Matrix (Fin (d i)) (Fin (d i)) (K ⊗ D i)`, so
`#(simple (K ⊗ A)) = ∑ i, #(simple (K ⊗ D i)) ≥ ∑ i, 1 = n`, each `K ⊗ D i` being a nonzero
finite-dimensional `K`-algebra. -/
theorem natCard_simpleModuleClasses_le_baseChange_of_isSemisimpleRing
    (k K : Type u) {A : Type u} [Field k] [Field K] [Algebra k K]
    [Ring A] [Algebra k A] [Module.Finite k A] [IsSemisimpleRing A] :
    Nat.card (SimpleModuleClasses.{u} A)
      ≤ Nat.card (SimpleModuleClasses.{u} (K ⊗[k] A)) := by
  classical
  obtain ⟨n, D, d, _, _, hDfin, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite (R₀ := k) (R := A)
  -- Each division factor `D i` has exactly one simple module; each `K ⊗ D i` has at least one.
  have hDone : ∀ i, Nat.card (SimpleModuleClasses.{u} (D i)) = 1 := by
    intro i
    haveI := hDfin i
    have hne : Nonempty (SimpleModuleClasses.{u} (D i)) := nonempty_simpleModuleClasses k
    have hss : Subsingleton (SimpleModuleClasses.{u} (D i)) :=
      subsingleton_simpleModuleClasses_divisionRing (D i)
    exact Nat.card_eq_one_iff_unique.mpr ⟨hss, hne⟩
  -- LHS count: `#(simple A) = n`.
  have hL : Nat.card (SimpleModuleClasses.{u} A) = n := by
    haveI : ∀ i, Finite (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (D i))) := by
      intro i
      haveI : NeZero (d i) := hd i
      haveI : Subsingleton (SimpleModuleClasses.{u} (D i)) :=
        subsingleton_simpleModuleClasses_divisionRing (D i)
      exact Finite.of_equiv _ (simpleModuleClassesMatrixEquiv (R := D i) (d i)).symm
    rw [Nat.card_congr (simpleModuleClassesCongrRingEquiv (e.toRingEquiv)),
      natCard_simpleModuleClasses_pi]
    have : ∀ i, Nat.card
        (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (D i))) = 1 := by
      intro i
      haveI : NeZero (d i) := hd i
      rw [Nat.card_congr (simpleModuleClassesMatrixEquiv (R := D i) (d i)), hDone i]
    simp [this]
  -- RHS count: `#(simple (K ⊗ A)) = ∑ i, #(simple (K ⊗ D i)) ≥ n`.
  obtain ⟨f⟩ := nonempty_baseChange_pi_matrix_algEquiv k K D d e
  haveI : ∀ i, Finite (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
    intro i
    haveI : NeZero (d i) := hd i
    haveI := hDfin i
    haveI : Finite (SimpleModuleClasses.{u} (K ⊗[k] D i)) := finite_simpleModuleClasses K
    exact Finite.of_equiv _ (simpleModuleClassesMatrixEquiv (R := K ⊗[k] D i) (d i)).symm
  rw [Nat.card_congr (simpleModuleClassesCongrRingEquiv (f.toRingEquiv)),
    natCard_simpleModuleClasses_pi, hL]
  -- `1 ≤ #(simple (K ⊗ D i))` for each factor, so `∑ i, … ≥ ∑ i, 1 = n`.
  have key : ∀ i, 1 ≤ Nat.card
      (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) := by
    intro i
    haveI : NeZero (d i) := hd i
    haveI := hDfin i
    haveI : Module.Finite K (K ⊗[k] D i) := inferInstance
    rw [Nat.card_congr (simpleModuleClassesMatrixEquiv (R := K ⊗[k] D i) (d i))]
    have hne : Nonempty (SimpleModuleClasses.{u} (K ⊗[k] D i)) :=
      nonempty_simpleModuleClasses K
    haveI : Finite (SimpleModuleClasses.{u} (K ⊗[k] D i)) :=
      finite_simpleModuleClasses K
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hne, inferInstance⟩)
  have hsum : ∑ _i : Fin n, 1 ≤ ∑ i, Nat.card
      (SimpleModuleClasses.{u} (Matrix (Fin (d i)) (Fin (d i)) (K ⊗[k] D i))) :=
    Finset.sum_le_sum fun i _ => key i
  simpa using hsum

end Etingof
