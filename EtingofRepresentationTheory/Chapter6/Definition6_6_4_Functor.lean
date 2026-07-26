import EtingofRepresentationTheory.Chapter2.QuiverRepresentationCategory
import EtingofRepresentationTheory.Chapter6.Definition6_6_4

/-!
# Definition 6.6.4, morphism part: `F⁻ᵢ` as a functor `Rep Q ⥤ Rep Q̄ᵢ`

`Chapter6/Definition6_6_4.lean` constructs the object assignment of the
Bernstein-Gelfand-Ponomarev reflection functor at a source. This file supplies the missing
morphism assignment and the functor laws, producing an actual `CategoryTheory.Functor`
from `Rep Q` to `Rep Q̄ᵢ` (Example 7.2.2(9) lists these as examples of functors).

Given `f : ρ₁ ⟶ ρ₂` in `Rep Q`, the morphism `F⁻ᵢ(f)` is

* `f.app v` at every vertex `v ≠ i`;
* at `i`, the map induced on cokernels by the componentwise map
  `⊕_{i→j} (ρ₁)_j → ⊕_{i→j} (ρ₂)_j`. It descends to the quotients because `f` commutes
  with the arrow maps, hence with the two canonical maps `ψ`.

This is dual to `Chapter6/Definition6_6_3_Functor.lean`, with kernels replaced by
cokernels. As there, everything is built by `@Decidable.casesOn` at an explicit
discriminant `d : Decidable (v = i)`, so that the functor laws and naturality reduce by
`cases` on that discriminant instead of by transport.
-/

universe u_k u_V u_obj u_hom

namespace Etingof

variable {k : Type u_k} [CommRing k] {Q : Type u_V} [Quiver.{u_hom} Q]

/-! ### The componentwise map on `⊕_{i→j} V_j` -/

/-- The map `⊕_{i→j} (ρ₁)_j → ⊕_{i→j} (ρ₂)_j` induced by a morphism `f : ρ₁ ⟶ ρ₂`,
applying `f.app j` in each summand. -/
noncomputable def reflFunctorMinus_dsMap
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q) :
    DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1) →ₗ[k]
      DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1) := by
  letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
  exact DirectSum.toModule k (Etingof.ArrowsOutOf Q i) _
    (fun a => (DirectSum.lof k (Etingof.ArrowsOutOf Q i)
      (fun a => ρ₂.obj a.1) a).comp (f.app a.1))

/-- `reflFunctorMinus_dsMap` on a generator, stated for an arbitrary `DecidableEq`
instance on the index type (`DecidableEq` is a subsingleton, so all choices agree). -/
theorem reflFunctorMinus_dsMap_lof
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    (d : DecidableEq (Etingof.ArrowsOutOf Q i))
    (a : Etingof.ArrowsOutOf Q i) (x : ρ₁.obj a.1) :
    reflFunctorMinus_dsMap f i
        (@DirectSum.lof k _ (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1) _ _ d a x) =
      @DirectSum.lof k _ (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1) _ _ d a
        (f.app a.1 x) := by
  have hd : d = Classical.decEq _ := Subsingleton.elim _ _
  subst hd
  delta reflFunctorMinus_dsMap
  erw [DirectSum.toModule_lof]
  simp only [LinearMap.coe_comp, Function.comp_apply]

/-- `reflFunctorMinus_dsMap` is functorial: it sends the identity to the identity. -/
theorem reflFunctorMinus_dsMap_id
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q) (i : Q)
    (y : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :
    reflFunctorMinus_dsMap (Etingof.QuiverRepresentationHom.id ρ) i y = y := by
  letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : Etingof.ArrowsOutOf Q i => ρ.obj a.1) b x =
        DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1) b x from rfl,
      reflFunctorMinus_dsMap_lof]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- `reflFunctorMinus_dsMap` is functorial: it takes composition to composition. -/
theorem reflFunctorMinus_dsMap_comp
    {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentationHom k Q ρ₂ ρ₃) (i : Q)
    (y : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :
    reflFunctorMinus_dsMap (f.comp g) i y =
      reflFunctorMinus_dsMap g i (reflFunctorMinus_dsMap f i y) := by
  letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : Etingof.ArrowsOutOf Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      reflFunctorMinus_dsMap_lof, reflFunctorMinus_dsMap_lof, reflFunctorMinus_dsMap_lof]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A morphism of representations commutes with the canonical maps
`ψ : V_i → ⊕_{i→j} V_j` at a vertex `i`. -/
theorem reflFunctorMinus_sourceMap_comm
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] (x : ρ₁.obj i) :
    reflFunctorMinus_dsMap f i (ρ₁.sourceMap i x) = ρ₂.sourceMap i (f.app i x) := by
  delta Etingof.QuiverRepresentation.sourceMap
  simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [reflFunctorMinus_dsMap_lof f i _ a (ρ₁.mapLinear a.2 x), f.naturality a.2 x]

/-! ### The induced map on cokernels -/

/-- The map `coker ψ₁ → coker ψ₂` induced by a morphism of representations: the map on
quotients induced by `reflFunctorMinus_dsMap`, legitimate by
`reflFunctorMinus_sourceMap_comm`. -/
noncomputable def reflFunctorMinus_cokerMap
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) ⧸
        LinearMap.range (ρ₁.sourceMap i)) →ₗ[k]
      ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) ⧸
        LinearMap.range (ρ₂.sourceMap i)) :=
  letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
  letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := k)
  Submodule.mapQ _ _ (reflFunctorMinus_dsMap f i) (by
    rintro y ⟨x, rfl⟩
    exact ⟨f.app i x, (reflFunctorMinus_sourceMap_comm f i x).symm⟩)

/-- `reflFunctorMinus_cokerMap` on the class of `y` is the class of
`reflFunctorMinus_dsMap f i y`. -/
theorem reflFunctorMinus_cokerMap_mk
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (y : DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    reflFunctorMinus_cokerMap f i (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (reflFunctorMinus_dsMap f i y) :=
  rfl

/-! ### The vertexwise morphism assignment -/

/-- The vertex component of `F⁻ᵢ(f)`, with the `Decidable` discriminant exposed as an
explicit argument `d`. At `d = .isFalse _` this is `f.app v`; at `d = .isTrue _` it is the
induced map on cokernels `reflFunctorMinus_cokerMap`. -/
noncomputable def reflFunctorMinus_homAt
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i v : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] (d : Decidable (v = i)) :
    letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
    letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
    letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
    letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
    Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d →ₗ[k]
      Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₂ i v d :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
      letI := Etingof.reflFunctorMinus_acmAt.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
      letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d
      letI := Etingof.reflFunctorMinus_modAt.{u_k, u_V, u_obj, u_hom} ρ₂ i v d
      Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d →ₗ[k]
        Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₂ i v d)
    d
    (fun _ => f.app v)
    (fun _ => reflFunctorMinus_cokerMap f i)

/-- The functor law `F⁻ᵢ(𝟙) = 𝟙`, pointwise and at an explicit discriminant. -/
theorem reflFunctorMinus_homAt_id
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q) (i v : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] (d : Decidable (v = i))
    (x : Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ i v d) :
    reflFunctorMinus_homAt (Etingof.QuiverRepresentationHom.id ρ) i v d x = x := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    letI : ∀ v, AddCommGroup (ρ.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (ρ.sourceMap i))
      (show ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) ⧸
        LinearMap.range (ρ.sourceMap i)) from x)
    change Submodule.Quotient.mk (reflFunctorMinus_dsMap _ i y) = Submodule.Quotient.mk y
    rw [reflFunctorMinus_dsMap_id]

/-- The functor law `F⁻ᵢ(f ≫ g) = F⁻ᵢ(f) ≫ F⁻ᵢ(g)`, pointwise and at an explicit
discriminant. -/
theorem reflFunctorMinus_homAt_comp
    {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentationHom k Q ρ₂ ρ₃) (i v : Q)
    [Fintype (Etingof.ArrowsOutOf Q i)] (d : Decidable (v = i))
    (x : Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d) :
    reflFunctorMinus_homAt (f.comp g) i v d x =
      reflFunctorMinus_homAt g i v d (reflFunctorMinus_homAt f i v d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    letI : ∀ v, AddCommGroup (ρ₁.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : ∀ v, AddCommGroup (ρ₃.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₃.obj a.1)) :=
      Etingof.addCommGroupOfRing (k := k)
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range (ρ₁.sourceMap i))
      (show ((DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₁.obj a.1)) ⧸
        LinearMap.range (ρ₁.sourceMap i)) from x)
    change Submodule.Quotient.mk (reflFunctorMinus_dsMap (f.comp g) i y) =
      Submodule.Quotient.mk (reflFunctorMinus_dsMap g i (reflFunctorMinus_dsMap f i y))
    rw [reflFunctorMinus_dsMap_comp]

/-- Naturality of `F⁻ᵢ(f)` with respect to an arrow of `Q̄ᵢ`, at explicit discriminants.
This is the `naturality` field of the morphism `F⁻ᵢ(f)`. -/
theorem reflFunctorMinus_homAt_naturality
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) {i : Q} (hi : Etingof.IsSource Q i)
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (a b : Q) (da : Decidable (a = i)) (db : Decidable (b = i))
    (e : Etingof.reflFunctorPlus_arrowAt i a b da db)
    (x : Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₁ i a da) :
    reflFunctorMinus_homAt f i b db
        (Etingof.reflFunctorMinus_mapAt.{u_k, u_V, u_obj, u_hom} ρ₁ hi a b da db e x) =
      Etingof.reflFunctorMinus_mapAt.{u_k, u_V, u_obj, u_hom} ρ₂ hi a b da db e
        (reflFunctorMinus_homAt f i a da x) := by
  cases da with
  | isFalse ha =>
    cases db with
    | isFalse hb => exact f.naturality e x
    | isTrue hb =>
      letI : DecidableEq (Etingof.ArrowsOutOf Q i) := Classical.decEq _
      letI : ∀ v, AddCommGroup (ρ₂.obj v) := fun _ => Etingof.addCommGroupOfRing (k := k)
      letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ₂.obj a.1)) :=
        Etingof.addCommGroupOfRing (k := k)
      exact congrArg Submodule.Quotient.mk (reflFunctorMinus_dsMap_lof f i _ ⟨a, e⟩ x)
  | isTrue ha =>
    cases db with
    | isFalse hb => exact ((hi b).false e).elim
    | isTrue hb => exact ((hi a).false (show a ⟶ i by exact hb ▸ e)).elim

/-! ### `F⁻ᵢ` as a functor -/

/-- `F⁻ᵢ(f)` at a vertex `v ≠ i`, read through the identification
`reflFunctorMinus_equivAtAt_ne`, is `f.app v`. Stated at an explicit discriminant. -/
theorem reflFunctorMinus_homAt_equivAtAt_ne
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) {i : Q}
    [Fintype (Etingof.ArrowsOutOf Q i)] (v : Q) (hv : v ≠ i)
    (d : Decidable (v = i))
    (x : Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₁ i v d) :
    Etingof.reflFunctorMinus_equivAtAt_ne.{u_k, u_V, u_obj, u_hom} ρ₂ v hv d
        (reflFunctorMinus_homAt f i v d x) =
      f.app v (Etingof.reflFunctorMinus_equivAtAt_ne.{u_k, u_V, u_obj, u_hom} ρ₁ v hv d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h => exact absurd h hv

/-- `F⁻ᵢ(f)` at the source `i`, read through the identification
`reflFunctorMinus_equivAtAt_eq`, is `reflFunctorMinus_cokerMap f i`. Stated at an explicit
discriminant. -/
theorem reflFunctorMinus_homAt_equivAtAt_eq
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) {i : Q}
    [Fintype (Etingof.ArrowsOutOf Q i)] (d : Decidable (i = i))
    (x : Etingof.reflFunctorMinus_objAt.{u_k, u_V, u_obj, u_hom} ρ₁ i i d) :
    Etingof.reflFunctorMinus_equivAtAt_eq.{u_k, u_V, u_obj, u_hom} ρ₂ d
        (reflFunctorMinus_homAt f i i d x) =
      reflFunctorMinus_cokerMap f i
        (Etingof.reflFunctorMinus_equivAtAt_eq.{u_k, u_V, u_obj, u_hom} ρ₁ d x) := by
  cases d with
  | isFalse h => exact absurd rfl h
  | isTrue h => rfl

/-- The morphism `F⁻ᵢ(f) : F⁻ᵢ(ρ₁) ⟶ F⁻ᵢ(ρ₂)` of representations of `Q̄ᵢ` induced by a
morphism `f : ρ₁ ⟶ ρ₂` of representations of `Q`. -/
noncomputable def reflectionFunctorMinusMap
    {k : Type u_k} [CommRing k] {Q : Type u_V} [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) :
    @Etingof.QuiverRepresentationHom k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₁) (Etingof.reflectionFunctorMinus Q i hi ρ₂) :=
  @Etingof.QuiverRepresentationHom.mk k Q _ (Etingof.reversedAtVertex Q i) _ _
    (fun v => reflFunctorMinus_homAt f i v (inst v i))
    (fun {a b} e x =>
      reflFunctorMinus_homAt_naturality f hi a b (inst a i) (inst b i) e x)

/-- The reflection functor `F⁻ᵢ : Rep Q ⥤ Rep Q̄ᵢ` at a source `i`, as an actual functor
(Etingof Definition 6.6.4; Example 7.2.2(9)). Its object action is the Chapter 6
construction `Etingof.reflectionFunctorMinus`. -/
noncomputable def reflectionFunctorMinusFunctor
    (k : Type u_k) [CommRing k] (Q : Type u_V) [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    (i : Q) (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)] :
    @CategoryTheory.Functor
      (Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q)
      Etingof.QuiverRepresentation.instCategory
      (@Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q _
        (Etingof.reversedAtVertex Q i))
      (@Etingof.QuiverRepresentation.instCategory k _ Q (Etingof.reversedAtVertex Q i)) where
  obj ρ := Etingof.reflectionFunctorMinus Q i hi ρ
  map f := reflectionFunctorMinusMap hi f
  map_id ρ := by
    refine @Etingof.QuiverRepresentationHom.ext k Q _ (Etingof.reversedAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact reflFunctorMinus_homAt_id ρ i v (inst v i) x
  map_comp f g := by
    refine @Etingof.QuiverRepresentationHom.ext k Q _ (Etingof.reversedAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact reflFunctorMinus_homAt_comp f g i v (inst v i) x

/-- The object action of the functor `F⁻ᵢ` is the componentwise Chapter 6 construction. -/
@[simp] theorem reflectionFunctorMinusFunctor_obj
    {k : Type u_k} [CommRing k] {Q : Type u_V} [DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    (ρ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q) :
    (reflectionFunctorMinusFunctor.{u_k, u_V, u_obj, u_hom} k Q i hi).obj ρ =
      Etingof.reflectionFunctorMinus Q i hi ρ :=
  rfl

/-- The morphism action of the functor `F⁻ᵢ` is `reflectionFunctorMinusMap`. -/
@[simp] theorem reflectionFunctorMinusFunctor_map
    {k : Type u_k} [CommRing k] {Q : Type u_V} [DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : ρ₁ ⟶ ρ₂) :
    (reflectionFunctorMinusFunctor.{u_k, u_V, u_obj, u_hom} k Q i hi).map f =
      reflectionFunctorMinusMap hi f :=
  rfl

/-- Away from the source, `F⁻ᵢ(f)` is `f` itself: transported through the identifications
`reflFunctorMinus_equivAt_ne`, the vertex map at `v ≠ i` is `f.app v`. -/
theorem reflectionFunctorMinusMap_app_ne
    {k : Type u_k} [CommRing k] {Q : Type u_V} [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (v : Q) (hv : v ≠ i)
    (x : @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₁) v) :
    Etingof.reflFunctorMinus_equivAt_ne.{u_k, u_V, u_hom, u_obj} hi ρ₂ v hv
        (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          _ _ (reflectionFunctorMinusMap hi f) v x) =
      f.app v (Etingof.reflFunctorMinus_equivAt_ne.{u_k, u_V, u_hom, u_obj} hi ρ₁ v hv x) :=
  reflFunctorMinus_homAt_equivAtAt_ne f v hv (inst v i) x

/-- At the source, `F⁻ᵢ(f)` is the induced map on cokernels: transported through
`reflFunctorMinus_equivAt_eq`, the vertex map at `i` is `reflFunctorMinus_cokerMap`. -/
theorem reflectionFunctorMinusMap_app_eq
    {k : Type u_k} [CommRing k] {Q : Type u_V} [inst : DecidableEq Q] [Quiver.{u_hom} Q]
    {i : Q} (hi : Etingof.IsSource Q i) [Fintype (Etingof.ArrowsOutOf Q i)]
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation.{u_k, u_V, max u_V u_obj u_hom, u_hom} k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (x : @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ₁) i) :
    Etingof.reflFunctorMinus_equivAt_eq.{u_k, u_V, u_hom, u_obj} hi ρ₂
        (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          _ _ (reflectionFunctorMinusMap hi f) i x) =
      reflFunctorMinus_cokerMap f i
        (Etingof.reflFunctorMinus_equivAt_eq.{u_k, u_V, u_hom, u_obj} hi ρ₁ x) :=
  reflFunctorMinus_homAt_equivAtAt_eq f (inst i i) x

end Etingof
