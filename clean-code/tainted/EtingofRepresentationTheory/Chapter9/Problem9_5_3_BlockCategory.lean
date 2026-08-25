import EtingofRepresentationTheory.Chapter9.Problem9_5_3_BlockIdempotent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Problem 9.5.3(i): the block `𝒞ₖ` is the category of `eₖ A`-modules

`Problem9_5_3_BlockIdempotent.lean` attaches to each block `𝒞ₖ` its indecomposable central
idempotent `eₖ` and characterizes the block as the modules on which `eₖ` acts as the identity.
This file turns that characterization into the categorical statement of the book: `𝒞ₖ` *is* the
category of modules over the corner algebra `eₖ A`.

The corner algebra is realised as the quotient of `R` by the two-sided ideal
`{x | eₖ * x = 0} = (1 - eₖ) R`; `cornerEmbedding` records that this quotient really is the corner
`eₖ R`, by exhibiting the injective multiplicative map `x ↦ eₖ * x` onto it.

* `Etingof.Problem953.cornerIdeal`, `Etingof.Problem953.CornerAlgebra` — the corner algebra of a
  central idempotent, with `cornerMk` the quotient map and `cornerMk_val_eq_one` the fact that
  `eₖ` becomes its identity.
* `Etingof.Problem953.BlockCat` — the block, as the full subcategory of `ModuleCat R` on the
  objects `M` with `InBlock R S M`.
* `Etingof.Problem953.cornerToBlock` — restriction of scalars along `R ↠ eₖ A`, landing in the
  block.
* `Etingof.Problem953.blockEquivalence` — **the book's categorical statement**: `cornerToBlock`
  is an equivalence `ModuleCat (eₖ A) ≌ 𝒞ₖ`.
* `Etingof.Problem953.blockEquivalenceFin` — the book's finite form: the equivalence restricts to
  the finite length objects on both sides, since restriction of scalars along a surjection does
  not change the lattice of submodules (`isFiniteLength_restrictScalars_iff`).
-/

universe v u

open CategoryTheory

namespace Etingof

namespace Problem953

variable (R : Type u) [Ring R]

section Corner

variable (e : CentralIdempotent R)

/-- The **annihilator ideal of a central idempotent** `e`: the two-sided ideal
`{x | e * x = 0}`, which is `(1 - e) R`. Quotienting by it produces the corner algebra `e R`. -/
def cornerIdeal : Ideal R where
  carrier := {x : R | e.1 * x = 0}
  add_mem' := by
    intro a b ha hb
    change e.1 * (a + b) = 0
    rw [mul_add, show e.1 * a = 0 from ha, show e.1 * b = 0 from hb, add_zero]
  zero_mem' := mul_zero _
  smul_mem' := by
    intro r x hx
    change e.1 * (r • x) = 0
    rw [smul_eq_mul, ← mul_assoc, e.2.2 r, mul_assoc, show e.1 * x = 0 from hx, mul_zero]

theorem mem_cornerIdeal_iff {x : R} : x ∈ cornerIdeal R e ↔ e.1 * x = 0 := Iff.rfl

instance cornerIdeal_isTwoSided : (cornerIdeal R e).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    change e.1 * (a * b) = 0
    rw [← mul_assoc, show e.1 * a = 0 from ha, zero_mul]

/-- The **corner algebra** `e R` of a central idempotent `e`, realised as `R ⧸ (1 - e) R`. Its
identity is the image of `e` (`cornerMk_val_eq_one`), and multiplication by `e` identifies it with
the corner `e R ⊆ R` (`cornerEmbedding`). -/
abbrev CornerAlgebra : Type u := R ⧸ cornerIdeal R e

/-- The quotient map `R ↠ e R` onto the corner algebra. -/
def cornerMk : R →+* CornerAlgebra R e := Ideal.Quotient.mk (cornerIdeal R e)

theorem cornerMk_surjective : Function.Surjective (cornerMk R e) :=
  Ideal.Quotient.mk_surjective

instance : RingHomSurjective (cornerMk R e) := ⟨cornerMk_surjective R e⟩

theorem cornerMk_eq_iff {x y : R} : cornerMk R e x = cornerMk R e y ↔ e.1 * x = e.1 * y := by
  rw [cornerMk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_cornerIdeal_iff, mul_sub, sub_eq_zero]

/-- The idempotent becomes the identity of its corner algebra. -/
@[simp]
theorem cornerMk_val_eq_one : cornerMk R e e.1 = 1 := by
  rw [show (1 : CornerAlgebra R e) = cornerMk R e 1 from rfl, cornerMk_eq_iff, mul_one, e.2.1.eq]

/-- Multiplication by a central element, as an `R`-linear endomorphism of `R`. -/
def mulLeftCentral : R →ₗ[R] R where
  toFun x := e.1 * x
  map_add' := mul_add _
  map_smul' r x := by
    simp only [smul_eq_mul, RingHom.id_apply, ← mul_assoc, e.2.2 r]

/-- **The corner algebra really is the corner `e R`.** Multiplication by `e` descends to an
injective `R`-linear map `R ⧸ (1 - e) R → R` with image `e R`, sending the identity of the corner
algebra to `e` and preserving multiplication (`cornerEmbedding_mul`). This is the certificate that
the quotient presentation used here is the book's `eₖ A`. -/
def cornerEmbedding : CornerAlgebra R e →ₗ[R] R :=
  (cornerIdeal R e).liftQ (mulLeftCentral R e) (fun _ hx => hx)

@[simp]
theorem cornerEmbedding_mk (x : R) : cornerEmbedding R e (cornerMk R e x) = e.1 * x := rfl

theorem cornerEmbedding_injective : Function.Injective (cornerEmbedding R e) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := cornerMk_surjective R e a
  obtain ⟨y, rfl⟩ := cornerMk_surjective R e b
  rw [cornerEmbedding_mk, cornerEmbedding_mk] at hab
  exact (cornerMk_eq_iff R e).mpr hab

theorem cornerEmbedding_one : cornerEmbedding R e 1 = e.1 := by
  rw [show (1 : CornerAlgebra R e) = cornerMk R e 1 from rfl, cornerEmbedding_mk, mul_one]

theorem cornerEmbedding_mul (a b : CornerAlgebra R e) :
    cornerEmbedding R e (a * b) = cornerEmbedding R e a * cornerEmbedding R e b := by
  obtain ⟨x, rfl⟩ := cornerMk_surjective R e a
  obtain ⟨y, rfl⟩ := cornerMk_surjective R e b
  have key : (e.1 * x) * (e.1 * y) = e.1 * (x * y) := by
    calc (e.1 * x) * (e.1 * y) = e.1 * (x * (e.1 * y)) := by rw [mul_assoc]
      _ = e.1 * ((x * e.1) * y) := by rw [mul_assoc x e.1 y]
      _ = e.1 * ((e.1 * x) * y) := by rw [← e.2.2 x]
      _ = (e.1 * e.1) * (x * y) := by rw [mul_assoc e.1 x y, ← mul_assoc]
      _ = e.1 * (x * y) := by rw [e.2.1.eq]
  rw [← map_mul (cornerMk R e), cornerEmbedding_mk, cornerEmbedding_mk, cornerEmbedding_mk, key]

theorem range_cornerEmbedding :
    Set.range (cornerEmbedding R e) = {y : R | ∃ x : R, y = e.1 * x} := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := cornerMk_surjective R e a
    exact ⟨x, (cornerEmbedding_mk R e x)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨cornerMk R e x, cornerEmbedding_mk R e x⟩

end Corner

section RestrictScalars

variable {A B : Type*} [Ring A] [Ring B]

/-- **Restriction of scalars along a surjective ring map is full.** An `A`-linear map between
`B`-modules pulled back along a surjection `f : A ↠ B` is automatically `B`-linear, because every
scalar of `B` is `f a` for some `a`. -/
theorem restrictScalars_full_of_surjective (f : A →+* B) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom (X := M) (Y := N)
      { toFun := g.hom
        map_add' := g.hom.map_add
        map_smul' := ?_ }, ?_⟩
    · intro b m
      obtain ⟨a, rfl⟩ := hf b
      exact g.hom.map_smul a m
    · rfl

/-- The identity map is `f`-semilinear from the restriction of scalars of a `B`-module to the
module itself; this is what transports finiteness conditions across restriction of scalars along
a surjection. -/
def restrictScalarsSemilinear (f : A →+* B) (N : ModuleCat.{v} B) :
    ((ModuleCat.restrictScalars f).obj N) →ₛₗ[f] (N : Type v) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of scalars along a surjection does not change the lattice of submodules, hence
preserves and reflects finite length. -/
theorem isFiniteLength_restrictScalars_iff (f : A →+* B) [RingHomSurjective f]
    (N : ModuleCat.{v} B) :
    IsFiniteLength A (((ModuleCat.restrictScalars f).obj N) : Type v) ↔
      IsFiniteLength B (N : Type v) := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian,
    (restrictScalarsSemilinear f N).isNoetherian_iff_of_bijective Function.bijective_id,
    (restrictScalarsSemilinear f N).isArtinian_iff_of_bijective Function.bijective_id]

end RestrictScalars

section BlockCategory

variable [Small.{v} R]

/-- **The block `𝒞ₖ`**, as the full subcategory of `ModuleCat R` on the modules whose composition
factors are all linked to `S` (Etingof Definition 9.5.1). -/
abbrev BlockCat (S : ModuleCat.{v} R) : Type (max u (v + 1)) :=
  ObjectProperty.FullSubcategory (fun M : ModuleCat.{v} R => Etingof.InBlock R S M)

variable (k : Type*) [Field k] [Algebra k R] [FiniteDimensional k R]
variable {S : ModuleCat.{v} R} (hS : IsSimpleModule R S)

include k

/-- The idempotent of the block of `S`, packaged as a `CentralIdempotent`. -/
noncomputable def blockCentralIdempotent : CentralIdempotent R :=
  ⟨(simpleIdempotent R k hS).1,
    (simpleIdempotent R k hS).2.2.1, (simpleIdempotent R k hS).2.2.2.1⟩

omit [Small.{v} R] in
@[simp]
theorem blockCentralIdempotent_val :
    (blockCentralIdempotent R k hS).1 = (simpleIdempotent R k hS).1 := rfl

/-- Every module of the block is annihilated by the corner ideal, hence is a module over the
corner algebra. -/
theorem isTorsionBySet_of_inBlock {M : ModuleCat.{v} R} (hM : Etingof.InBlock R S M) :
    Module.IsTorsionBySet R (M : Type v) (cornerIdeal R (blockCentralIdempotent R k hS) : Set R) :=
  fun m a => by
    have h1 : (simpleIdempotent R k hS).1 • m = m :=
      (inBlock_iff_simpleIdempotent_smul R k hS M).mp hM m
    have ha : (simpleIdempotent R k hS).1 * (a : R) = 0 := a.2
    calc (a : R) • m = (a : R) • ((simpleIdempotent R k hS).1 • m) := by rw [h1]
      _ = ((a : R) * (simpleIdempotent R k hS).1) • m := (mul_smul _ _ m).symm
      _ = ((simpleIdempotent R k hS).1 * (a : R)) • m := by
            rw [(simpleIdempotent R k hS).2.2.2.1 (a : R)]
      _ = 0 := by rw [ha, zero_smul]

/-- Restriction of scalars along `R ↠ eₖ A` lands in the block: on a module over the corner
algebra, `eₖ` acts as the identity because it becomes the identity of the corner algebra. -/
theorem inBlock_restrictScalars
    (N : ModuleCat.{v} (CornerAlgebra R (blockCentralIdempotent R k hS))) :
    Etingof.InBlock R S
      ((ModuleCat.restrictScalars (cornerMk R (blockCentralIdempotent R k hS))).obj N) := by
  rw [inBlock_iff_simpleIdempotent_smul R k hS]
  intro m
  rw [ModuleCat.restrictScalars.smul_def]
  rw [show (simpleIdempotent R k hS).1 = (blockCentralIdempotent R k hS).1 from rfl,
    cornerMk_val_eq_one, one_smul]

/-- **Restriction of scalars `ModuleCat (eₖ A) ⥤ 𝒞ₖ`.** -/
noncomputable def cornerToBlock :
    ModuleCat.{v} (CornerAlgebra R (blockCentralIdempotent R k hS)) ⥤ BlockCat R S :=
  ObjectProperty.lift _ (ModuleCat.restrictScalars (cornerMk R (blockCentralIdempotent R k hS)))
    (inBlock_restrictScalars R k hS)

instance : (cornerToBlock R k hS).Faithful := by
  unfold cornerToBlock; infer_instance

instance : (cornerToBlock R k hS).Full := by
  haveI := restrictScalars_full_of_surjective.{v} (cornerMk R (blockCentralIdempotent R k hS))
    (cornerMk_surjective R _)
  unfold cornerToBlock; infer_instance

instance : (cornerToBlock R k hS).EssSurj where
  mem_essImage M := by
    letI := (isTorsionBySet_of_inBlock R k hS M.property).module
    refine ⟨ModuleCat.of _ (M.obj : Type v), ⟨ObjectProperty.isoMk _ ?_⟩⟩
    exact LinearEquiv.toModuleIso
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := id
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

instance : (cornerToBlock R k hS).IsEquivalence where

/-- **Problem 9.5.3(i), categorical form.** The block `𝒞ₖ` of a finite dimensional algebra is
equivalent to the category of modules over the corner algebra `eₖ A`, via restriction of scalars
along `R ↠ eₖ A`. This is the book's "`𝒞ₖ` is the category of `eₖ A`-modules". -/
noncomputable def blockEquivalence :
    ModuleCat.{v} (CornerAlgebra R (blockCentralIdempotent R k hS)) ≌ BlockCat R S :=
  (cornerToBlock R k hS).asEquivalence

@[simp]
theorem blockEquivalence_functor : (blockEquivalence R k hS).functor = cornerToBlock R k hS := rfl

/-- **The book's finite dimensional form.** The block of finite length modules is equivalent to
the category of finite length modules over the corner algebra: restriction of scalars along
`R ↠ eₖ A` does not change the underlying module, so it matches the finiteness conditions on the
two sides (`isFiniteLength_restrictScalars_iff`). Finite length is the finiteness notion the
project's Chapter 9 development uses for `𝒞`. -/
noncomputable def cornerToBlockFin :
    ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{v} (CornerAlgebra R (blockCentralIdempotent R k hS)) =>
          IsFiniteLength (CornerAlgebra R (blockCentralIdempotent R k hS)) (N : Type v)) ⥤
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{v} R => Etingof.InBlock R S M ∧ IsFiniteLength R (M : Type v)) :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ ModuleCat.restrictScalars (cornerMk R (blockCentralIdempotent R k hS)))
    (fun N => ⟨inBlock_restrictScalars R k hS N.obj,
      (isFiniteLength_restrictScalars_iff _ N.obj).mpr N.property⟩)

instance : (cornerToBlockFin R k hS).Faithful := by
  unfold cornerToBlockFin; infer_instance

instance : (cornerToBlockFin R k hS).Full := by
  haveI := restrictScalars_full_of_surjective.{v} (cornerMk R (blockCentralIdempotent R k hS))
    (cornerMk_surjective R _)
  unfold cornerToBlockFin; infer_instance

instance : (cornerToBlockFin R k hS).EssSurj where
  mem_essImage M := by
    letI := (isTorsionBySet_of_inBlock R k hS M.property.1).module
    refine ⟨⟨ModuleCat.of _ (M.obj : Type v), ?_⟩, ⟨ObjectProperty.isoMk _ ?_⟩⟩
    · exact (isFiniteLength_restrictScalars_iff
        (cornerMk R (blockCentralIdempotent R k hS)) (ModuleCat.of _ (M.obj : Type v))).mp
        M.property.2
    · have e : ((ModuleCat.restrictScalars (cornerMk R (blockCentralIdempotent R k hS))).obj
          (ModuleCat.of _ (M.obj : Type v))) ≅ M.obj :=
        LinearEquiv.toModuleIso
          { toFun := id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := id
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      exact e

instance : (cornerToBlockFin R k hS).IsEquivalence where

/-- **Problem 9.5.3(i), the book's finite dimensional categorical statement.** The finite length
part of the block `𝒞ₖ` is equivalent to the category of finite length `eₖ A`-modules. -/
noncomputable def blockEquivalenceFin :
    ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{v} (CornerAlgebra R (blockCentralIdempotent R k hS)) =>
          IsFiniteLength (CornerAlgebra R (blockCentralIdempotent R k hS)) (N : Type v)) ≌
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat.{v} R => Etingof.InBlock R S M ∧ IsFiniteLength R (M : Type v)) :=
  (cornerToBlockFin R k hS).asEquivalence

/-- The equivalence does not move the underlying abelian group: the object of `𝒞ₖ` attached to a
module `N` over the corner algebra is `N` itself, with `r` acting as its image in `eₖ A`. In
particular it identifies the *finite dimensional* objects on the two sides, which is the form of
the statement used in the book (`𝒞` is the category of finite dimensional modules). -/
theorem blockEquivalence_obj_carrier
    (N : ModuleCat.{v} (CornerAlgebra R (blockCentralIdempotent R k hS))) :
    (((blockEquivalence R k hS).functor.obj N).obj : Type v) = (N : Type v) := rfl

end BlockCategory

end Problem953

end Etingof
