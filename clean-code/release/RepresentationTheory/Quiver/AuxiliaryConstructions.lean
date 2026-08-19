/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.Quiver.Auxiliary
import RepresentationTheory.Quiver.FiniteTypeCriterion

/-!
# Auxiliary constructions for quiver representations
-/

namespace RepresentationTheory.Quiver.AuxiliaryConstructions

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams (AuxiliaryQuiverModuleData)
open RepresentationTheory.CategoryTheory.QuiverLinearMaps (AuxiliaryQuiverEquivData)
open RepresentationTheory.Quiver.Auxiliary
  (auxiliaryObjectAtVertex auxiliaryRelation auxiliaryVertexValue)

variable {k Q : Type*} [Field k] [Quiver Q]

/-- An auxiliary predicate on a quiver. -/
def HasAuxiliaryQuiverProperty (Q : Type*) [Quiver Q] : Prop :=
  ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil

/-- An auxiliary predicate on a quiver representation. -/
def HasAuxiliaryProperty (ρ : AuxiliaryQuiverModuleData k Q) : Prop :=
  (∃ v, Nontrivial (ρ.obj v)) ∧
  ∀ (W : ∀ v, Submodule k (ρ.obj v)),
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, ρ.map e x ∈ W b) →
    (∀ v, W v = ⊥) ∨ (∀ v, W v = ⊤)

/-- The representation associated to a vertex satisfies the auxiliary predicate. -/
@[source_ref "Chapter3/Problem3.9.3" (role := primary)]
theorem hasAuxiliaryProperty_vertex [DecidableEq Q] (i : Q) :
    HasAuxiliaryProperty (auxiliaryObjectAtVertex (k := k) i) := by
  -- Off-vertices `v ≠ i` carry the zero space `Fin 0 → k`, which is a subsingleton.
  have hsub : ∀ v, v ≠ i → Subsingleton ((auxiliaryObjectAtVertex (k := k) i).obj v) := by
    intro v hv
    change Subsingleton (Fin (if v = i then 1 else 0) → k)
    rw [if_neg hv]
    infer_instance
  refine ⟨⟨i, ?_⟩, ?_⟩
  · -- Nontriviality at vertex `i`: the fibre there is `Fin 1 → k`.
    have hobj : ((auxiliaryObjectAtVertex (k := k) i).obj i) = (Fin 1 → k) := by
      change (Fin (if i = i then 1 else 0) → k) = (Fin 1 → k)
      rw [if_pos rfl]
    rw [hobj]
    have hne : (0 : Fin 1 → k) ≠ 1 := by
      intro h
      have := congrFun h 0
      simp only [Pi.zero_apply, Pi.one_apply] at this
      exact one_ne_zero this.symm
    exact ⟨0, 1, hne⟩
  · -- Any arrow-stable subspace family is all-`⊥` or all-`⊤`.
    intro W _
    -- The fibre at `i` is (defeq to) the 1-dimensional space `Fin 1 → k`.  Transport the
    -- submodule lattice there via the identity linear equivalence, where `Fin 1 → k` has the
    -- honest `Pi` instances that instance search can see through.
    let e : (auxiliaryObjectAtVertex (k := k) i).obj i ≃ₗ[k] (Fin (if i = i then 1 else 0) → k) :=
      { toFun := fun x => x, invFun := fun x => x, left_inv := fun _ => rfl,
        right_inv := fun _ => rfl, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    haveI : IsSimpleOrder (Submodule k (Fin (if i = i then 1 else 0) → k)) :=
      is_simple_module_of_finrank_eq_one (K := k) (A := k)
        (by simp )
    -- `W i` is `⊥` or `⊤` by transporting the simple-order dichotomy back along `e`.
    have hWi : W i = ⊥ ∨ W i = ⊤ := by
      have f := Submodule.orderIsoMapComap e
      rcases eq_bot_or_eq_top (f (W i)) with h | h
      · exact Or.inl (f.injective (by rw [h, map_bot]))
      · exact Or.inr (f.injective (by rw [h, map_top]))
    rcases hWi with hWi | hWi
    · left
      intro v
      rcases eq_or_ne v i with rfl | hv
      · exact hWi
      · have := hsub v hv
        rw [Submodule.eq_bot_iff]
        intro x _
        exact Subsingleton.elim x 0
    · right
      intro v
      rcases eq_or_ne v i with rfl | hv
      · exact hWi
      · have := hsub v hv
        rw [Submodule.eq_top_iff']
        intro x
        rw [Subsingleton.elim x (0 : (auxiliaryObjectAtVertex (k := k) i).obj v)]
        exact Submodule.zero_mem _

/-- A `k`-module whose submodule lattice satisfies `⊥ = ⊤` is a subsingleton. -/
private theorem subsingleton_of_bot_eq_top {M : Type*} [AddCommMonoid M] [Module k M]
    (h : (⊥ : Submodule k M) = ⊤) : Subsingleton M := by
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Submodule k M) := by rw [h]; trivial
  have hb : b ∈ (⊥ : Submodule k M) := by rw [h]; trivial
  rw [Submodule.mem_bot] at ha hb
  rw [ha, hb]

/-- Under the displayed finiteness and auxiliary predicates, some vertex has a nonempty associated auxiliary object. -/
@[source_ref "Chapter3/Problem3.9.3" (role := primary)]
theorem exists_vertex_nonempty_auxiliaryObject [DecidableEq Q] [Finite Q]
    (hQ : HasAuxiliaryQuiverProperty Q) (ρ : AuxiliaryQuiverModuleData k Q)
    (hρ : HasAuxiliaryProperty ρ) :
    ∃ i : Q, Nonempty (AuxiliaryQuiverEquivData k Q ρ (auxiliaryObjectAtVertex i)) := by
  -- Each carrier is an `AddCommGroup` (over a field), needed for `finrank`/simple-module API.
  -- The group structure is supplied per carrier as a class-headed local instance where needed
  -- (a `∀ v`-typed `letI` is not class-headed and so is ignored by instance synthesis).
  obtain ⟨hne, hdich⟩ := hρ
  -- The arrow relation is well-founded: a cycle would give a nontrivial path `i ⟶ i`.
  have hwf : WellFounded (fun a b : Q => Nonempty (a ⟶ b)) := by
    have hpath : ∀ {a b : Q},
        Relation.TransGen (fun a b : Q => Nonempty (a ⟶ b)) a b →
        ∃ p : Quiver.Path a b, 0 < p.length := by
      intro a b h
      induction h with
      | single hab =>
          obtain ⟨e⟩ := hab
          exact ⟨(Quiver.Path.nil).cons e, by simp [Quiver.Path.length_cons]⟩
      | tail _ hbc ih =>
          obtain ⟨p, _⟩ := ih
          obtain ⟨e⟩ := hbc
          exact ⟨p.cons e, by simp [Quiver.Path.length_cons]⟩
    have hTG : WellFounded (Relation.TransGen (fun a b : Q => Nonempty (a ⟶ b))) := by
      haveI : Std.Irrefl (Relation.TransGen (fun a b : Q => Nonempty (a ⟶ b))) := by
        constructor
        intro a hcyc
        obtain ⟨p, hp⟩ := hpath hcyc
        rw [hQ a p] at hp
        simp at hp
      haveI : IsStrictOrder Q (Relation.TransGen (fun a b : Q => Nonempty (a ⟶ b))) := {}
      rw [← Set.wellFoundedOn_univ]
      exact Set.finite_univ.wellFoundedOn
    exact Subrelation.wf (fun {a b} h => Relation.TransGen.single h) hTG
  -- Step A: every arrow map of `ρ` vanishes.
  have hzero : ∀ {a b : Q} (e : a ⟶ b), ρ.map e = 0 := by
    -- `W b` = sum of images of all arrows into `b`; arrow-stable, hence `⊥` or `⊤` everywhere.
    let W : ∀ b, Submodule k (ρ.obj b) :=
      fun b => ⨆ (p : Σ a, (a ⟶ b)), LinearMap.range (ρ.map p.2)
    have hWval : ∀ b, W b = ⨆ (p : Σ a, (a ⟶ b)), LinearMap.range (ρ.map p.2) :=
      fun _ => rfl
    have hWstable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, ρ.map e x ∈ W b := by
      intro a b e x _
      rw [hWval b]
      exact Submodule.mem_iSup_of_mem ⟨a, e⟩ (LinearMap.mem_range_self _ x)
    rcases hdich W hWstable with hbot | htop
    · -- All `W b = ⊥`: each image is `⊥`, so each arrow map is `0`.
      intro a b e
      have hle : LinearMap.range (ρ.map e) ≤ W b := by
        rw [hWval b]
        exact le_iSup (fun p : Σ a, (a ⟶ b) => LinearMap.range (ρ.map p.2)) ⟨a, e⟩
      rw [hbot b] at hle
      rw [← LinearMap.range_eq_bot]
      exact le_bot_iff.mp hle
    · -- All `W b = ⊤`: a well-founded induction shows every carrier is trivial, a contradiction.
      exfalso
      have hAllTrivial : ∀ v, (⊤ : Submodule k (ρ.obj v)) = ⊥ := by
        intro v
        refine hwf.induction (C := fun v => (⊤ : Submodule k (ρ.obj v)) = ⊥) v (fun b IH => ?_)
        have hWb : W b = ⊥ := by
          rw [hWval b, iSup_eq_bot]
          rintro ⟨a, e⟩
          have hsubA : Subsingleton (ρ.obj a) := subsingleton_of_bot_eq_top (IH a ⟨e⟩).symm
          have hmap : ρ.map e = 0 :=
            LinearMap.ext fun x => by
              rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
          rw [hmap, LinearMap.range_zero]
        exact (htop b).symm.trans hWb
      obtain ⟨v₀, hv₀⟩ := hne
      haveI := hv₀
      haveI := subsingleton_of_bot_eq_top (hAllTrivial v₀).symm
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (ρ.obj v₀)
      exact hxy (Subsingleton.elim x y)
  -- Step B: `ρ` is concentrated at a single nontrivial vertex `v₀`.
  obtain ⟨v₀, hv₀⟩ := hne
  haveI : Nontrivial (ρ.obj v₀) := hv₀
  -- Supply the `AddCommGroup` on this carrier (needed for the simple-module/`finrank` API) as a
  -- class-headed local instance. Use Mathlib's `Module.addCommMonoidToAddCommGroup`, whose
  -- `toAddCommMonoid` is defeq to the bundled `AddCommMonoid`, so the bundled `Module k` instance
  -- is still found; use `letI` (not `haveI`) so that reduction stays visible to instance synthesis.
  letI : AddCommGroup (ρ.obj v₀) := Module.addCommMonoidToAddCommGroup k
  -- Vertices `v ≠ v₀` carry the trivial space.
  have hconc : ∀ v, v ≠ v₀ → Subsingleton (ρ.obj v) := by
    intro v hv
    let E : ∀ w, Submodule k (ρ.obj w) := fun w => if w = v₀ then ⊤ else ⊥
    have hEstable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ E a, ρ.map e x ∈ E b := by
      intro a b e x _
      rw [hzero e, LinearMap.zero_apply]
      exact (E b).zero_mem
    rcases hdich E hEstable with hb | ht
    · exfalso
      have h1 : E v₀ = ⊥ := hb v₀
      have h2 : E v₀ = ⊤ := by simp only [E, if_pos rfl]
      haveI := subsingleton_of_bot_eq_top (h1.symm.trans h2)
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (ρ.obj v₀)
      exact hxy (Subsingleton.elim x y)
    · have h1 : E v = ⊤ := ht v
      have h2 : E v = ⊥ := by simp only [E, if_neg hv]
      exact subsingleton_of_bot_eq_top (h2.symm.trans h1)
  -- `ρ.obj v₀` is a simple module (only `⊥`/`⊤` submodules, and nontrivial).
  haveI hsimple : IsSimpleModule k (ρ.obj v₀) := by
    refine { eq_bot_or_eq_top := fun U => ?_ }
    let F : ∀ w, Submodule k (ρ.obj w) :=
      Function.update (fun w => (⊥ : Submodule k (ρ.obj w))) v₀ U
    have hFstable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ F a, ρ.map e x ∈ F b := by
      intro a b e x _
      rw [hzero e, LinearMap.zero_apply]
      exact (F b).zero_mem
    rcases hdich F hFstable with hb | ht
    · exact Or.inl (by have := hb v₀; simpa only [F, Function.update_self] using this)
    · exact Or.inr (by have := ht v₀; simpa only [F, Function.update_self] using this)
  -- `auxiliaryObjectAtVertex v₀` has `finrank` `1` at `v₀` and `0` elsewhere.
  have hsimpleFinrank : ∀ v,
      Module.finrank k ((auxiliaryObjectAtVertex (k := k) v₀).obj v) = if v = v₀ then 1 else 0 := by
    intro v
    change Module.finrank k (Fin (if v = v₀ then 1 else 0) → k) = _
    rw [Module.finrank_pi k, Fintype.card_fin]
  -- Step C: a vertexwise linear equivalence `ρ ≅ auxiliaryObjectAtVertex v₀`.
  have hEquiv : ∀ v, Nonempty (ρ.obj v ≃ₗ[k] (auxiliaryObjectAtVertex (k := k) v₀).obj v) := by
    intro v
    by_cases h : v = v₀
    · subst h
      letI : AddCommGroup (ρ.obj v) := Module.addCommMonoidToAddCommGroup k
      haveI : Module.Finite k (ρ.obj v) := by
        obtain ⟨x, hx⟩ := exists_ne (0 : ρ.obj v)
        exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k (ρ.obj v) x)
          (IsSimpleModule.toSpanSingleton_surjective k hx)
      haveI : Module.Finite k ((auxiliaryObjectAtVertex (k := k) v).obj v) := by
        change Module.Finite k (Fin (if v = v then 1 else 0) → k); rw [if_pos rfl]; infer_instance
      haveI : Module.Free k ((auxiliaryObjectAtVertex (k := k) v).obj v) := by
        change Module.Free k (Fin (if v = v then 1 else 0) → k); rw [if_pos rfl]; infer_instance
      apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      rw [hsimpleFinrank v, if_pos rfl, isSimpleModule_iff_finrank_eq_one.mp hsimple]
    · haveI : Subsingleton (ρ.obj v) := hconc v h
      haveI : Subsingleton ((auxiliaryObjectAtVertex (k := k) v₀).obj v) := by
        change Subsingleton (Fin (if v = v₀ then 1 else 0) → k); rw [if_neg h]; infer_instance
      exact ⟨LinearEquiv.ofBijective (0 : ρ.obj v →ₗ[k] (auxiliaryObjectAtVertex (k := k) v₀).obj v)
        ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩⟩
  -- Assemble the isomorphism. Naturality is automatic: all arrow maps vanish on both sides.
  refine ⟨v₀, ⟨{ app := fun v => (hEquiv v).some, naturality := ?_ }⟩⟩
  intro a b e x
  have h1 : ρ.map e = 0 := hzero e
  have h2 : (auxiliaryObjectAtVertex (k := k) v₀).map e = 0 := rfl
  simp only [h1, h2, LinearMap.zero_apply, map_zero]

/-- Characterizes the displayed auxiliary relation on vertices by emptiness of the quiver hom type. -/
@[source_ref "Chapter3/Problem3.9.3" (role := primary)]
theorem auxiliaryRelation_iff_isEmpty_hom [DecidableEq Q] (i j : Q) :
    auxiliaryRelation (auxiliaryObjectAtVertex (k := k) i) (auxiliaryObjectAtVertex j) ↔ IsEmpty (i ⟶ j) := by
  -- Both simple representations have all arrow maps zero, so the Ext differential is the
  -- constant zero map. Hence Ext-vanishing (surjectivity) holds iff the codomain is trivial,
  -- and the codomain component at an arrow `a ⟶ b` is `Hom(S_i(a), S_j(b))`, which is nonzero
  -- exactly when `a = i` and `b = j`, i.e. when there is an arrow `i → j`.
  have hzero : RepresentationTheory.Quiver.Auxiliary.auxiliaryElidedDefinition (auxiliaryObjectAtVertex (k := k) i) (auxiliaryObjectAtVertex j) = fun _ => 0 := by
    funext f p
    -- The subtraction uses the auxiliary group structure on the shared codomain; supply it here as a
    -- per-carrier (class-headed) local instance so `sub_self` sees the matching `AddGroup`.
    letI : AddCommGroup ((auxiliaryObjectAtVertex (k := k) j).obj p.2.1) := RepresentationTheory.Quiver.Auxiliary.addCommGroupOfModule (k := k)
    change (auxiliaryObjectAtVertex (k := k) j).map p.2.2 ∘ₗ f p.1
        - f p.2.1 ∘ₗ (auxiliaryObjectAtVertex (k := k) i).map p.2.2 = 0
    simp only [auxiliaryObjectAtVertex, RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.representationAtVertex_map_eq_zero, LinearMap.zero_comp,
      LinearMap.comp_zero]
    exact sub_self (0 : (auxiliaryObjectAtVertex (k := k) i).obj p.1 →ₗ[k] (auxiliaryObjectAtVertex (k := k) j).obj p.2.1)
  rw [auxiliaryRelation, hzero]
  constructor
  · -- Ext vanishes ⇒ no arrow `i → j`.
    intro hsurj
    rw [isEmpty_iff]
    intro e
    classical
    -- A nonzero linear map `S_i(i) →ₗ S_j(j)`: both spaces are `Fin 1 → k`.
    have hip : 0 < (if i = i then (1 : ℕ) else 0) := by rw [if_pos rfl]; norm_num
    have hjp : 0 < (if j = j then (1 : ℕ) else 0) := by rw [if_pos rfl]; norm_num
    let g : (auxiliaryObjectAtVertex (k := k) i).obj i →ₗ[k] (auxiliaryObjectAtVertex (k := k) j).obj j :=
      { toFun := fun x => fun _ => x ⟨0, hip⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hg : g ≠ 0 := by
      intro h
      have h1 : g (fun _ => (1 : k)) = 0 := by rw [h]; rfl
      have h2 := congrFun h1 ⟨0, hjp⟩
      simp only [g, LinearMap.coe_mk, AddHom.coe_mk] at h2
      exact one_ne_zero h2
    -- Surjectivity of the zero map forces the codomain element `Pi.single ⟨i,j,e⟩ g` to be 0.
    obtain ⟨f, hf⟩ := hsurj (Pi.single (⟨i, j, e⟩ : Σ a b, (a ⟶ b)) g)
    have h1 := congrFun hf.symm ⟨i, j, e⟩
    simp only [Pi.single_eq_same, Pi.zero_apply] at h1
    exact hg h1
  · -- No arrow `i → j` ⇒ Ext vanishes: every codomain element is 0.
    intro hempty y
    refine ⟨0, ?_⟩
    funext p
    obtain ⟨a, b, e⟩ := p
    simp only [Pi.zero_apply]
    by_cases hb : b = j
    · by_cases ha : a = i
      · subst ha; subst hb
        exact (hempty.false e).elim
      · -- Domain `S_i(a)` is trivial (`a ≠ i`), so any map out of it is 0.
        symm
        refine LinearMap.ext fun x => ?_
        have hsub : Subsingleton ((auxiliaryObjectAtVertex (k := k) i).obj a) := by
          change Subsingleton (Fin (if a = i then 1 else 0) → k)
          rw [if_neg ha]; infer_instance
        rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
    · -- Codomain `S_j(b)` is trivial (`b ≠ j`), so any map into it is 0.
      symm
      have hsub : Subsingleton ((auxiliaryObjectAtVertex (k := k) j).obj b) := by
        change Subsingleton (Fin (if b = j then 1 else 0) → k)
        rw [if_neg hb]; infer_instance
      exact LinearMap.ext fun x => Subsingleton.elim _ _


/-- An auxiliary construction associated to a pair of quiver representations. -/
noncomputable def auxiliaryPairing (V W : AuxiliaryQuiverModuleData k Q) :
    (∀ i, V.obj i →ₗ[k] W.obj i) →ₗ[k]
      (∀ p : (Σ i j, (i ⟶ j)), V.obj p.1 →ₗ[k] W.obj p.2.1) where
  -- The subtraction needs `AddCommGroup (W.obj p.2.1)` on the shared codomain. Supply it per `p`
  -- as a class-headed local instance (a `∀ v`-typed `letI` is not class-headed, so it is ignored by
  -- instance synthesis); the group definition is `@[reducible]`, so `Module k` over the bundled
  -- `AddCommMonoid`
  -- is still found.
  toFun f p :=
    letI : AddCommGroup (W.obj p.2.1) := RepresentationTheory.Quiver.Auxiliary.addCommGroupOfModule (k := k)
    W.map p.2.2 ∘ₗ f p.1 - f p.2.1 ∘ₗ V.map p.2.2
  map_add' f g := by
    funext p
    letI : AddCommGroup (W.obj p.2.1) := RepresentationTheory.Quiver.Auxiliary.addCommGroupOfModule (k := k)
    simp only [Pi.add_apply, LinearMap.comp_add, LinearMap.add_comp]
    abel
  map_smul' c f := by
    funext p
    letI : AddCommGroup (W.obj p.2.1) := RepresentationTheory.Quiver.Auxiliary.addCommGroupOfModule (k := k)
    simp only [Pi.smul_apply, RingHom.id_apply, LinearMap.comp_smul, LinearMap.smul_comp,
      smul_sub]

/-- An additive commutative group structure on a displayed component of a representation associated to a vertex. -/
instance (priority := 100) vertexRepresentationComponentAddCommGroup [DecidableEq Q] (j v : Q) :
    AddCommGroup ((auxiliaryObjectAtVertex (k := k) j).obj v) :=
  Module.addCommMonoidToAddCommGroup k

/-- An auxiliary type associated to an ordered pair of quiver vertices. -/
abbrev homObject [DecidableEq Q] (i j : Q) : Type _ :=
  (∀ p : (Σ a b : Q, (a ⟶ b)),
      (auxiliaryObjectAtVertex (k := k) i).obj p.1 →ₗ[k] (auxiliaryObjectAtVertex (k := k) j).obj p.2.1) ⧸
    LinearMap.range (auxiliaryPairing (auxiliaryObjectAtVertex (k := k) i) (auxiliaryObjectAtVertex (k := k) j))

/-- The auxiliary construction vanishes on the displayed representations associated to vertices. -/
theorem auxiliaryPairing_vertex [DecidableEq Q] (i j : Q) :
    auxiliaryPairing (auxiliaryObjectAtVertex (k := k) i) (auxiliaryObjectAtVertex j) = 0 := by
  refine LinearMap.ext fun f => funext fun p => ?_
  -- Match the group baked into `auxiliaryPairing`'s subtraction with a per-carrier local instance.
  letI : AddCommGroup ((auxiliaryObjectAtVertex (k := k) j).obj p.2.1) := RepresentationTheory.Quiver.Auxiliary.addCommGroupOfModule (k := k)
  change (auxiliaryObjectAtVertex (k := k) j).map p.2.2 ∘ₗ f p.1
      - f p.2.1 ∘ₗ (auxiliaryObjectAtVertex (k := k) i).map p.2.2 = 0
  simp only [auxiliaryObjectAtVertex, RepresentationTheory.QuiverRepresentation.VertexCompositionSeries.representationAtVertex_map_eq_zero, LinearMap.zero_comp,
      LinearMap.comp_zero]
  exact sub_self (0 : (auxiliaryObjectAtVertex (k := k) i).obj p.1 →ₗ[k] (auxiliaryObjectAtVertex (k := k) j).obj p.2.1)

/-- The dimension of the auxiliary type equals the cardinality of the quiver hom type. -/
@[source_ref "Chapter3/Problem3.9.3" (role := primary)]
theorem finrank_homObject [DecidableEq Q] [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]
    (i j : Q) :
    Module.finrank k (homObject (k := k) i j) = Fintype.card (i ⟶ j) := by
  -- The differential vanishes, so `Ext¹ = coker 0` is isomorphic to its whole codomain.
  have hbot : LinearMap.range (auxiliaryPairing (auxiliaryObjectAtVertex (k := k) i) (auxiliaryObjectAtVertex j)) = ⊥ := by
    rw [auxiliaryPairing_vertex, LinearMap.range_zero]
  refine (Submodule.quotEquivOfEqBot _ hbot).finrank_eq.trans ?_
  -- The `Fin _ → k` carriers are finite and free; this propagates to the Hom components, so both
  -- `finrank_pi_fintype` and `finrank_linearMap` below have the instances they need.
  haveI hobjFin : ∀ r a : Q, Module.Finite k ((auxiliaryObjectAtVertex (k := k) r).obj a) := fun r a => by
    change Module.Finite k (Fin (if a = r then 1 else 0) → k); infer_instance
  haveI hobjFree : ∀ r a : Q, Module.Free k ((auxiliaryObjectAtVertex (k := k) r).obj a) := fun r a => by
    change Module.Free k (Fin (if a = r then 1 else 0) → k); infer_instance
  -- `finrank` of the product is the sum over arrows of the finrank of each Hom component.
  rw [Module.finrank_pi_fintype k]
  -- Each Hom component has finrank `(if p.1 = i then 1 else 0) * (if p.2.1 = j then 1 else 0)`.
  have hcomp : ∀ p : (Σ a b : Q, (a ⟶ b)),
      Module.finrank k ((auxiliaryObjectAtVertex (k := k) i).obj p.1 →ₗ[k] (auxiliaryObjectAtVertex (k := k) j).obj p.2.1)
        = (if p.1 = i then 1 else 0) * (if p.2.1 = j then 1 else 0) := by
    intro p
    rw [Module.finrank_linearMap]
    congr 1
    · change Module.finrank k (Fin (if p.1 = i then 1 else 0) → k) = _
      rw [Module.finrank_pi k, Fintype.card_fin]
    · change Module.finrank k (Fin (if p.2.1 = j then 1 else 0) → k) = _
      rw [Module.finrank_pi k, Fintype.card_fin]
  simp only [hcomp]
  -- Expand the sum over `Σ a b, (a ⟶ b)` into iterated sums, then collapse: the innermost
  -- arrow-sum contributes `#(a ⟶ b)`, and the two `if`s select `a = i` and `b = j`.
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_sigma]
  simp [Finset.card_univ, Finset.card_empty, mul_ite,
    apply_ite Finset.card, Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Under the displayed quiver and dimension hypotheses, either the auxiliary predicate fails or a displayed map is bijective. -/
@[source_ref "Chapter3/Problem3.9.3" (role := supporting)]
theorem not_auxiliaryProperty_or_exists_bijective_map [DecidableEq Q] [Fintype Q]
    (hQ : HasAuxiliaryQuiverProperty Q) (ρ : AuxiliaryQuiverModuleData k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, auxiliaryVertexValue ρ v = 2) :
    (¬ ρ.AuxiliaryCondition)
      ∨ (∃ (i j : Q) (a : i ⟶ j), i ≠ j ∧ Function.Bijective (ρ.map a)) := by
  classical
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun _ => RepresentationTheory.Quiver.Auxiliary.addCommGroupOfModule (k := k)
  -- If some distinct-endpoint arrow already acts bijectively, we land in the right disjunct.
  by_cases hbij : ∃ (i j : Q) (a : i ⟶ j), i ≠ j ∧ Function.Bijective (ρ.map a)
  · exact Or.inr hbij
  push Not at hbij
  -- No self-loops: an arrow `v ⟶ v` would be a nontrivial cycle.
  have hnoloop : ∀ (v : Q), IsEmpty (v ⟶ v) := by
    intro v
    rw [isEmpty_iff]
    intro a
    have h := congrArg Quiver.Path.length (hQ v (Quiver.Path.nil.cons a))
    simp [Quiver.Path.length_cons] at h
  -- Every arrow map is zero: otherwise its endpoints would be two distinct dimension-1 vertices
  -- and the (nonzero) map between the resulting simple modules would be bijective.
  have hmaps0 : ∀ {u w : Q} (a : u ⟶ w), ρ.map a = 0 := by
    intro u w a
    by_contra hne0
    have hdu : Nontrivial (ρ.obj u) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      haveI := h
      exact hne0 (by ext x; simp [Subsingleton.elim x (0 : ρ.obj u)])
    have hcw : Nontrivial (ρ.obj w) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      haveI := h
      exact hne0 (by ext x; exact Subsingleton.elim _ _)
    have huw : u ≠ w := by rintro rfl; exact (hnoloop u).false a
    have hfu : 0 < auxiliaryVertexValue ρ u := Module.finrank_pos_iff.mpr hdu
    have hfw : 0 < auxiliaryVertexValue ρ w := Module.finrank_pos_iff.mpr hcw
    have hsum : auxiliaryVertexValue ρ u + auxiliaryVertexValue ρ w ≤ 2 := by
      rw [← h2, ← Finset.sum_pair huw]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hu1 : auxiliaryVertexValue ρ u = 1 := by omega
    have hw1 : auxiliaryVertexValue ρ w = 1 := by omega
    haveI hsu : IsSimpleModule k (ρ.obj u) := isSimpleModule_iff_finrank_eq_one.mpr hu1
    haveI hsw : IsSimpleModule k (ρ.obj w) := isSimpleModule_iff_finrank_eq_one.mpr hw1
    have hinj : Function.Injective (ρ.map a) := by
      rw [← LinearMap.ker_eq_bot]
      rcases eq_bot_or_eq_top (LinearMap.ker (ρ.map a)) with h | h
      · exact h
      · exact absurd (LinearMap.ker_eq_top.mp h) hne0
    have hsurj : Function.Surjective (ρ.map a) := by
      rw [← LinearMap.range_eq_top]
      rcases eq_bot_or_eq_top (LinearMap.range (ρ.map a)) with h | h
      · exact absurd (LinearMap.range_eq_bot.mp h) hne0
      · exact h
    exact hbij u w a huw ⟨hinj, hsurj⟩
  -- With all arrow maps zero, ρ splits: pick a nonzero vector at a nontrivial vertex and a
  -- complement; the two families of subspaces are stable and complementary, contradicting
  -- indecomposability.
  left
  intro hIndec
  obtain ⟨⟨v₀, hv₀⟩, hdecomp⟩ := hIndec
  haveI := hv₀
  obtain ⟨x, hx⟩ := exists_ne (0 : ρ.obj v₀)
  obtain ⟨C, hC⟩ := (Submodule.span k {x}).exists_isCompl
  let W₁ : ∀ v, Submodule k (ρ.obj v) :=
    Function.update (fun v => (⊥ : Submodule k (ρ.obj v))) v₀ (Submodule.span k {x})
  let W₂ : ∀ v, Submodule k (ρ.obj v) :=
    Function.update (fun v => (⊤ : Submodule k (ρ.obj v))) v₀ C
  have h1stable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₁ a, ρ.map e x ∈ W₁ b := by
    intro a b e x _; rw [hmaps0 e, LinearMap.zero_apply]; exact (W₁ b).zero_mem
  have h2stable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W₂ a, ρ.map e x ∈ W₂ b := by
    intro a b e x _; rw [hmaps0 e, LinearMap.zero_apply]; exact (W₂ b).zero_mem
  have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
    intro v
    by_cases hv : v = v₀
    · subst hv; simp only [W₁, W₂, Function.update_self]; exact hC
    · simp only [W₁, W₂, Function.update_of_ne hv]; exact isCompl_bot_top
  rcases hdecomp W₁ W₂ h1stable h2stable hcompl with hbot1 | hbot2
  · -- `W₁` is not everywhere `⊥`: `W₁ v₀ = span{x} ≠ ⊥` since `x ≠ 0`.
    have hb := hbot1 v₀
    rw [show W₁ v₀ = Submodule.span k {x} by simp only [W₁, Function.update_self],
      Submodule.span_singleton_eq_bot] at hb
    exact hx hb
  · -- `W₂` everywhere `⊥` forces total dimension `1`, contradicting `h2`.
    have hCbot : C = ⊥ := by
      have h := hbot2 v₀; rwa [show W₂ v₀ = C by simp only [W₂, Function.update_self]] at h
    have hspan : Submodule.span k {x} = ⊤ := by
      have h := hC.sup_eq_top; rwa [hCbot, sup_bot_eq] at h
    have hv0dim : auxiliaryVertexValue ρ v₀ = 1 := by
      change Module.finrank k (ρ.obj v₀) = 1
      rw [← finrank_top (R := k) (M := ρ.obj v₀), ← hspan, finrank_span_singleton hx]
    have hvdim : ∀ v, v ≠ v₀ → auxiliaryVertexValue ρ v = 0 := by
      intro v hv
      have hWv : (⊤ : Submodule k (ρ.obj v)) = ⊥ := by
        have h := hbot2 v
        rwa [show W₂ v = (⊤ : Submodule k (ρ.obj v)) by
          simp only [W₂, Function.update_of_ne hv]] at h
      change Module.finrank k (ρ.obj v) = 0
      rw [← finrank_top (R := k) (M := ρ.obj v), hWv, finrank_bot]
    have hsum1 : ∑ v, auxiliaryVertexValue ρ v = 1 := by
      rw [Finset.sum_eq_single v₀ (fun v _ hv => hvdim v hv) (fun h => absurd (Finset.mem_univ v₀) h)]
      exact hv0dim
    omega

end RepresentationTheory.Quiver.AuxiliaryConstructions
