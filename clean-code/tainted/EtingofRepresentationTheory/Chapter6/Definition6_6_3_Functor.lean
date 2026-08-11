import EtingofRepresentationTheory.Chapter2.QuiverRepresentationCategory
import EtingofRepresentationTheory.Chapter6.Definition6_6_3

/-!
# Definition 6.6.3, morphism part: `F⁺ᵢ` as a functor `Rep Q ⥤ Rep Q̄ᵢ`

`Chapter6/Definition6_6_3.lean` constructs the object assignment of the
Bernstein-Gelfand-Ponomarev reflection functor at a sink. This file supplies the missing
morphism assignment and the functor laws, producing an actual `CategoryTheory.Functor`
from `Rep Q` to `Rep Q̄ᵢ` (Example 7.2.2(9) lists these as examples of functors).

Given `f : ρ₁ ⟶ ρ₂` in `Rep Q`, the morphism `F⁺ᵢ(f)` is

* `f.app v` at every vertex `v ≠ i`;
* at `i`, the restriction to kernels of the componentwise map
  `⊕_{j→i} (ρ₁)_j → ⊕_{j→i} (ρ₂)_j`. The restriction is legitimate because `f` commutes
  with the arrow maps, hence with the two canonical maps `φ`.

As in `Definition6_6_3.lean`, everything is built by `@Decidable.casesOn` at an explicit
discriminant `d : Decidable (v = i)`, so that the functor laws and naturality reduce by
`cases` on that discriminant instead of by transport.
-/

namespace Etingof

variable {k : Type*} [CommSemiring k] {Q : Type*} [Quiver Q]

/-! ### The componentwise map on `⊕_{j→i} V_j` -/

/-- The map `⊕_{j→i} (ρ₁)_j → ⊕_{j→i} (ρ₂)_j` induced by a morphism `f : ρ₁ ⟶ ρ₂`,
applying `f.app j` in each summand. -/
noncomputable def reflFunctorPlus_dsMap {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q) :
    DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1) →ₗ[k]
      DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ₂.obj a.1) := by
  letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
  exact DirectSum.toModule k (Etingof.ArrowsInto Q i) _
    (fun a => (DirectSum.lof k (Etingof.ArrowsInto Q i)
      (fun a => ρ₂.obj a.1) a).comp (f.app a.1))

theorem reflFunctorPlus_dsMap_lof {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    (a : Etingof.ArrowsInto Q i) (x : ρ₁.obj a.1) :
    letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
    reflFunctorPlus_dsMap f i
        (DirectSum.lof k (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1) a x) =
      DirectSum.lof k (Etingof.ArrowsInto Q i) (fun a => ρ₂.obj a.1) a (f.app a.1 x) := by
  letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
  delta reflFunctorPlus_dsMap
  erw [DirectSum.toModule_lof]
  simp only [LinearMap.coe_comp, Function.comp_apply]

/-- `reflFunctorPlus_dsMap` is functorial: it sends the identity to the identity. -/
theorem reflFunctorPlus_dsMap_id (ρ : Etingof.QuiverRepresentation k Q) (i : Q)
    (y : DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1)) :
    reflFunctorPlus_dsMap (Etingof.QuiverRepresentationHom.id ρ) i y = y := by
  letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : Etingof.ArrowsInto Q i => ρ.obj a.1) b x =
        DirectSum.lof k (Etingof.ArrowsInto Q i) (fun a => ρ.obj a.1) b x from rfl,
      reflFunctorPlus_dsMap_lof]
    rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- `reflFunctorPlus_dsMap` is functorial: it takes composition to composition. -/
theorem reflFunctorPlus_dsMap_comp {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentationHom k Q ρ₂ ρ₃) (i : Q)
    (y : DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1)) :
    reflFunctorPlus_dsMap (f.comp g) i y =
      reflFunctorPlus_dsMap g i (reflFunctorPlus_dsMap f i y) := by
  letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : Etingof.ArrowsInto Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      reflFunctorPlus_dsMap_lof, reflFunctorPlus_dsMap_lof, reflFunctorPlus_dsMap_lof]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `reflFunctorPlus_dsMap` acts componentwise: taking the `a`-component commutes with it. -/
theorem reflFunctorPlus_component_dsMap {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    (a : Etingof.ArrowsInto Q i)
    (y : DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1)) :
    DirectSum.component k (Etingof.ArrowsInto Q i) (fun a => ρ₂.obj a.1) a
        (reflFunctorPlus_dsMap f i y) =
      f.app a.1 (DirectSum.component k (Etingof.ArrowsInto Q i)
        (fun a => ρ₁.obj a.1) a y) := by
  letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : Etingof.ArrowsInto Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      reflFunctorPlus_dsMap_lof f i b x]
    rcases eq_or_ne b a with rfl | hba
    · rw [DirectSum.component.lof_self, DirectSum.component.lof_self]
    · simp only [DirectSum.component.of, dif_neg hba, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A morphism of representations commutes with the canonical maps `φ : ⊕_{j→i} V_j → V_i`
at a vertex `i`. -/
theorem reflFunctorPlus_sinkMap_comm {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q)
    (y : DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1)) :
    ρ₂.sinkMap i (reflFunctorPlus_dsMap f i y) = f.app i (ρ₁.sinkMap i y) := by
  letI : DecidableEq (Etingof.ArrowsInto Q i) := Classical.decEq _
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of b x =>
    rw [show DirectSum.of (fun a : Etingof.ArrowsInto Q i => ρ₁.obj a.1) b x =
        DirectSum.lof k (Etingof.ArrowsInto Q i) (fun a => ρ₁.obj a.1) b x from rfl,
      reflFunctorPlus_dsMap_lof f i b x]
    delta Etingof.QuiverRepresentation.sinkMap
    erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
    exact (f.naturality b.2 x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The map `ker φ₁ → ker φ₂` induced by a morphism of representations: the restriction of
`reflFunctorPlus_dsMap` to kernels, legitimate by `reflFunctorPlus_sinkMap_comm`. -/
noncomputable def reflFunctorPlus_kerMap {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q) :
    ↥(ρ₁.sinkMap i).ker →ₗ[k] ↥(ρ₂.sinkMap i).ker :=
  LinearMap.restrict (reflFunctorPlus_dsMap f i) (q := (ρ₂.sinkMap i).ker) (fun x hx => by
    simp only [LinearMap.mem_ker] at hx ⊢
    rw [reflFunctorPlus_sinkMap_comm f i x, hx, map_zero])

@[simp] theorem reflFunctorPlus_kerMap_coe {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i : Q) (x : ↥(ρ₁.sinkMap i).ker) :
    ((reflFunctorPlus_kerMap f i x : ↥(ρ₂.sinkMap i).ker) :
        DirectSum (Etingof.ArrowsInto Q i) (fun a => ρ₂.obj a.1)) =
      reflFunctorPlus_dsMap f i (x : DirectSum (Etingof.ArrowsInto Q i)
        (fun a => ρ₁.obj a.1)) := rfl

/-! ### The vertexwise morphism assignment -/

/-- The vertex component of `F⁺ᵢ(f)`, with the `Decidable` discriminant exposed as an
explicit argument `d`. At `d = .isFalse _` this is `f.app v`; at `d = .isTrue _` it is the
kernel restriction `reflFunctorPlus_kerMap`. -/
noncomputable def reflFunctorPlus_homAt {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (i v : Q) (d : Decidable (v = i)) :
    letI := Etingof.reflFunctorPlus_acmAt ρ₁ i v d
    letI := Etingof.reflFunctorPlus_acmAt ρ₂ i v d
    letI := Etingof.reflFunctorPlus_modAt ρ₁ i v d
    letI := Etingof.reflFunctorPlus_modAt ρ₂ i v d
    Etingof.reflFunctorPlus_objAt ρ₁ i v d →ₗ[k] Etingof.reflFunctorPlus_objAt ρ₂ i v d :=
  @Decidable.casesOn (v = i)
    (fun d =>
      letI := Etingof.reflFunctorPlus_acmAt ρ₁ i v d
      letI := Etingof.reflFunctorPlus_acmAt ρ₂ i v d
      letI := Etingof.reflFunctorPlus_modAt ρ₁ i v d
      letI := Etingof.reflFunctorPlus_modAt ρ₂ i v d
      Etingof.reflFunctorPlus_objAt ρ₁ i v d →ₗ[k] Etingof.reflFunctorPlus_objAt ρ₂ i v d)
    d
    (fun _ => f.app v)
    (fun _ => reflFunctorPlus_kerMap f i)

/-- The functor law `F⁺ᵢ(𝟙) = 𝟙`, pointwise and at an explicit discriminant. -/
theorem reflFunctorPlus_homAt_id (ρ : Etingof.QuiverRepresentation k Q) (i v : Q)
    (d : Decidable (v = i)) (x : Etingof.reflFunctorPlus_objAt ρ i v d) :
    reflFunctorPlus_homAt (Etingof.QuiverRepresentationHom.id ρ) i v d x = x := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    refine Subtype.ext ?_
    exact reflFunctorPlus_dsMap_id ρ i _

/-- The functor law `F⁺ᵢ(f ≫ g) = F⁺ᵢ(f) ≫ F⁺ᵢ(g)`, pointwise and at an explicit
discriminant. -/
theorem reflFunctorPlus_homAt_comp {ρ₁ ρ₂ ρ₃ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (g : Etingof.QuiverRepresentationHom k Q ρ₂ ρ₃) (i v : Q) (d : Decidable (v = i))
    (x : Etingof.reflFunctorPlus_objAt ρ₁ i v d) :
    reflFunctorPlus_homAt (f.comp g) i v d x =
      reflFunctorPlus_homAt g i v d (reflFunctorPlus_homAt f i v d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h =>
    refine Subtype.ext ?_
    exact reflFunctorPlus_dsMap_comp f g i _

/-- Naturality of `F⁺ᵢ(f)` with respect to an arrow of `Q̄ᵢ`, at explicit discriminants.
This is the `naturality` field of the morphism `F⁺ᵢ(f)`. -/
theorem reflFunctorPlus_homAt_naturality
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) {i : Q} (hi : Etingof.IsSink Q i)
    (a b : Q) (da : Decidable (a = i)) (db : Decidable (b = i))
    (e : Etingof.reflFunctorPlus_arrowAt i a b da db)
    (x : Etingof.reflFunctorPlus_objAt ρ₁ i a da) :
    reflFunctorPlus_homAt f i b db (Etingof.reflFunctorPlus_mapAt ρ₁ hi a b da db e x) =
      Etingof.reflFunctorPlus_mapAt ρ₂ hi a b da db e (reflFunctorPlus_homAt f i a da x) := by
  cases da with
  | isFalse ha =>
    cases db with
    | isFalse hb => exact f.naturality e x
    | isTrue hb => exact ((hi a).false e).elim
  | isTrue ha =>
    cases db with
    | isFalse hb =>
      exact (reflFunctorPlus_component_dsMap f i ⟨b, e⟩ (Subtype.val x)).symm
    | isTrue hb => exact ((hi b).false (ha ▸ e)).elim


/-- `F⁺ᵢ(f)` at a vertex `v ≠ i`, read through the identification
`reflFunctorPlus_equivAtAt_ne`, is `f.app v`. Stated at an explicit discriminant. -/
theorem reflFunctorPlus_homAt_equivAtAt_ne {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) {i : Q} (v : Q) (hv : v ≠ i)
    (d : Decidable (v = i)) (x : Etingof.reflFunctorPlus_objAt ρ₁ i v d) :
    Etingof.reflFunctorPlus_equivAtAt_ne ρ₂ v hv d (reflFunctorPlus_homAt f i v d x) =
      f.app v (Etingof.reflFunctorPlus_equivAtAt_ne ρ₁ v hv d x) := by
  cases d with
  | isFalse h => rfl
  | isTrue h => exact absurd h hv

/-- `F⁺ᵢ(f)` at the sink `i`, read through the identification
`reflFunctorPlus_equivAtAt_eq`, is `reflFunctorPlus_kerMap f i`. Stated at an explicit
discriminant. -/
theorem reflFunctorPlus_homAt_equivAtAt_eq {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) {i : Q}
    (d : Decidable (i = i)) (x : Etingof.reflFunctorPlus_objAt ρ₁ i i d) :
    Etingof.reflFunctorPlus_equivAtAt_eq ρ₂ d (reflFunctorPlus_homAt f i i d x) =
      reflFunctorPlus_kerMap f i (Etingof.reflFunctorPlus_equivAtAt_eq ρ₁ d x) := by
  cases d with
  | isFalse h => exact absurd rfl h
  | isTrue h => rfl

/-! ### `F⁺ᵢ` as a functor -/

/-- The morphism `F⁺ᵢ(f) : F⁺ᵢ(ρ₁) ⟶ F⁺ᵢ(ρ₂)` of representations of `Q̄ᵢ` induced by a
morphism `f : ρ₁ ⟶ ρ₂` of representations of `Q`. -/
noncomputable def reflectionFunctorPlusMap
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i)
    {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) :
    @Etingof.QuiverRepresentationHom k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ₁) (Etingof.reflectionFunctorPlus Q i hi ρ₂) :=
  @Etingof.QuiverRepresentationHom.mk k Q _ (Etingof.reversedAtVertex Q i) _ _
    (fun v => reflFunctorPlus_homAt f i v (inst v i))
    (fun {a b} e x =>
      reflFunctorPlus_homAt_naturality f hi a b (inst a i) (inst b i) e x)

/-- The reflection functor `F⁺ᵢ : Rep Q ⥤ Rep Q̄ᵢ` at a sink `i`, as an actual functor
(Etingof Definition 6.6.3; Example 7.2.2(9)). Its object action is the Chapter 6
construction `Etingof.reflectionFunctorPlus`. -/
noncomputable def reflectionFunctorPlusFunctor
    (k : Type*) [CommSemiring k] (Q : Type*) [inst : DecidableEq Q] [Quiver Q]
    (i : Q) (hi : Etingof.IsSink Q i) :
    @CategoryTheory.Functor
      (Etingof.QuiverRepresentation k Q) Etingof.QuiverRepresentation.instCategory
      (@Etingof.QuiverRepresentation k Q _ (Etingof.reversedAtVertex Q i))
      (@Etingof.QuiverRepresentation.instCategory k _ Q (Etingof.reversedAtVertex Q i)) where
  obj ρ := Etingof.reflectionFunctorPlus Q i hi ρ
  map f := reflectionFunctorPlusMap hi f
  map_id ρ := by
    refine @Etingof.QuiverRepresentationHom.ext k Q _ (Etingof.reversedAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact reflFunctorPlus_homAt_id ρ i v (inst v i) x
  map_comp f g := by
    refine @Etingof.QuiverRepresentationHom.ext k Q _ (Etingof.reversedAtVertex Q i)
      _ _ _ _ (fun v => LinearMap.ext (fun x => ?_))
    exact reflFunctorPlus_homAt_comp f g i v (inst v i) x

/-- The object action of the functor `F⁺ᵢ` is the componentwise Chapter 6 construction. -/
@[simp] theorem reflectionFunctorPlusFunctor_obj
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) (ρ : Etingof.QuiverRepresentation k Q) :
    (reflectionFunctorPlusFunctor k Q i hi).obj ρ = Etingof.reflectionFunctorPlus Q i hi ρ :=
  rfl

/-- The morphism action of the functor `F⁺ᵢ` is `reflectionFunctorPlusMap`. -/
@[simp] theorem reflectionFunctorPlusFunctor_map
    {k : Type*} [CommSemiring k] {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : ρ₁ ⟶ ρ₂) :
    (reflectionFunctorPlusFunctor k Q i hi).map f = reflectionFunctorPlusMap hi f :=
  rfl

/-- Away from the sink, `F⁺ᵢ(f)` is `f` itself: transported through the identifications
`reflFunctorPlus_equivAt_ne`, the vertex map at `v ≠ i` is `f.app v`. -/
theorem reflectionFunctorPlusMap_app_ne
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂) (v : Q) (hv : v ≠ i)
    (x : @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ₁) v) :
    Etingof.reflFunctorPlus_equivAt_ne hi ρ₂ v hv
        (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          _ _ (reflectionFunctorPlusMap hi f) v x) =
      f.app v (Etingof.reflFunctorPlus_equivAt_ne hi ρ₁ v hv x) := by
  exact reflFunctorPlus_homAt_equivAtAt_ne f v hv (inst v i) x

/-- At the sink, `F⁺ᵢ(f)` is the kernel restriction of the componentwise map on
`⊕_{j→i} V_j`: transported through `reflFunctorPlus_equivAt_eq`, the vertex map at `i` is
`reflFunctorPlus_kerMap`. -/
theorem reflectionFunctorPlusMap_app_eq
    {k : Type*} [CommSemiring k] {Q : Type*} [inst : DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSink Q i) {ρ₁ ρ₂ : Etingof.QuiverRepresentation k Q}
    (f : Etingof.QuiverRepresentationHom k Q ρ₁ ρ₂)
    (x : @Etingof.QuiverRepresentation.obj k Q _ (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorPlus Q i hi ρ₁) i) :
    Etingof.reflFunctorPlus_equivAt_eq hi ρ₂
        (@Etingof.QuiverRepresentationHom.app k Q _ (Etingof.reversedAtVertex Q i)
          _ _ (reflectionFunctorPlusMap hi f) i x) =
      reflFunctorPlus_kerMap f i (Etingof.reflFunctorPlus_equivAt_eq hi ρ₁ x) := by
  exact reflFunctorPlus_homAt_equivAtAt_eq f (inst i i) x

end Etingof
