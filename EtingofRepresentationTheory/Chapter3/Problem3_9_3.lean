import EtingofRepresentationTheory.Chapter6.Problem6_9_3
import EtingofRepresentationTheory.Chapter6.Proposition6_6_5
import EtingofRepresentationTheory.Chapter2.Theorem2_1_2

/-!
# Problem 3.9.3: Irreducible representations and `Ext¹` for path algebras

Let `Q` be a quiver without oriented cycles and `P_Q` its path algebra. This problem asks to
find the irreducible representations of `P_Q`, compute `Ext¹` between them, and classify the
2-dimensional representations.

Representations of the path algebra `P_Q` are the same as **quiver representations** of `Q`:
a vector space at each vertex together with a linear map for each arrow. We use the project's
`Etingof.QuiverRepresentation k Q` (Definition 2.8.3) and reuse the `Ext¹` differential and
simple representations from `Chapter6/Problem6_9_3` (which formalises the same
`Ext¹`/simple-representation content for Section 6.9).

* **Irreducibles.** The irreducible representations are the simple representations `S_i`
  (`simpleRep i`): one-dimensional at vertex `i`, zero elsewhere, all arrows acting by `0`.
  Every irreducible representation is isomorphic to some `S_i`.
* **`Ext¹` between irreducibles.** `Ext¹(S_i, S_j)` has dimension equal to the number of
  arrows `i → j`; in particular it vanishes iff there are no arrows `i → j`.
* **2-dimensional representations.** A representation of total dimension `2` is either
  decomposable (a sum `S_i ⊕ S_j` of two simples) or indecomposable, in which case it is the
  representation supported on a single arrow `a : i → j` with `a` acting as an isomorphism.

Statement pass: all objects are genuinely constructed (reusing the quiver-representation
infrastructure); the proofs are `sorry`.
-/

namespace Etingof.Problem3_9_3

open Etingof (QuiverRepresentation QuiverRepresentationEquiv)
open Etingof.Problem6_9_3 (simpleRep Ext1Vanishes dimVec)

variable {k Q : Type*} [Field k] [Quiver Q]

/-- A quiver has **no oriented cycles** if the only path from a vertex to itself is the
trivial (nil) path. -/
def NoOrientedCycles (Q : Type*) [Quiver Q] : Prop :=
  ∀ (i : Q) (p : Quiver.Path i i), p = Quiver.Path.nil

/-- A quiver representation is **irreducible** (simple) if it is nonzero and its only
sub-representations are `0` and the whole representation. A sub-representation is a choice of
subspace `W v ⊆ ρ.obj v` at each vertex, stable under all arrow maps. -/
def IsIrreducible (ρ : QuiverRepresentation k Q) : Prop :=
  (∃ v, Nontrivial (ρ.obj v)) ∧
  ∀ (W : ∀ v, Submodule k (ρ.obj v)),
    (∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, ρ.mapLinear e x ∈ W b) →
    (∀ v, W v = ⊥) ∨ (∀ v, W v = ⊤)

/-- **Irreducibles, existence.** The simple representation `S_i` is irreducible. -/
theorem simpleRep_isIrreducible [DecidableEq Q] (i : Q) :
    IsIrreducible (simpleRep (k := k) i) := by
  -- Off-vertices `v ≠ i` carry the zero space `Fin 0 → k`, which is a subsingleton.
  have hsub : ∀ v, v ≠ i → Subsingleton ((simpleRep (k := k) i).obj v) := by
    intro v hv
    show Subsingleton (Fin (if v = i then 1 else 0) → k)
    rw [if_neg hv]
    infer_instance
  refine ⟨⟨i, ?_⟩, ?_⟩
  · -- Nontriviality at vertex `i`: the fibre there is `Fin 1 → k`.
    have hobj : ((simpleRep (k := k) i).obj i) = (Fin 1 → k) := by
      show (Fin (if i = i then 1 else 0) → k) = (Fin 1 → k)
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
    let e : (simpleRep (k := k) i).obj i ≃ₗ[k] (Fin (if i = i then 1 else 0) → k) :=
      { toFun := fun x => x, invFun := fun x => x, left_inv := fun _ => rfl,
        right_inv := fun _ => rfl, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    haveI : IsSimpleOrder (Submodule k (Fin (if i = i then 1 else 0) → k)) :=
      is_simple_module_of_finrank_eq_one (K := k) (A := k)
        (by simp [Module.finrank_fin_fun])
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
        rw [Subsingleton.elim x (0 : (simpleRep (k := k) i).obj v)]
        exact Submodule.zero_mem _

/-- A `k`-module whose submodule lattice satisfies `⊥ = ⊤` is a subsingleton. -/
private theorem subsingleton_of_bot_eq_top {M : Type*} [AddCommMonoid M] [Module k M]
    (h : (⊥ : Submodule k M) = ⊤) : Subsingleton M := by
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ (⊥ : Submodule k M) := by rw [h]; trivial
  have hb : b ∈ (⊥ : Submodule k M) := by rw [h]; trivial
  rw [Submodule.mem_bot] at ha hb
  rw [ha, hb]

/-- **Irreducibles, classification.** For a quiver `Q` that is finite and has no oriented
cycles, every irreducible representation of `P_Q` is isomorphic to a simple representation `S_i`.

The acyclicity and finiteness hypotheses are essential: over a quiver with an oriented cycle
(e.g. a single loop `0 ⟶ 0` acting as the identity on `k`) there are irreducible
representations that are *not* isomorphic to any vertex simple `S_i`. The proof shows that,
for a finite acyclic quiver, all arrow maps of an irreducible representation must vanish (a
well-founded induction along the arrow relation), so the representation is concentrated at a
single vertex where it is a `1`-dimensional simple `k`-module. -/
theorem irreducible_isSimpleRep [DecidableEq Q] [Finite Q]
    (hQ : NoOrientedCycles Q) (ρ : QuiverRepresentation k Q)
    (hρ : IsIrreducible ρ) :
    ∃ i : Q, Nonempty (QuiverRepresentationEquiv k Q ρ (simpleRep i)) := by
  -- Each carrier is an `AddCommGroup` (over a field), needed for `finrank`/simple-module API.
  letI : ∀ v, AddCommGroup (ρ.obj v) := fun _ => Etingof.Problem6_9_3.acg (k := k)
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
  have hzero : ∀ {a b : Q} (e : a ⟶ b), ρ.mapLinear e = 0 := by
    -- `W b` = sum of images of all arrows into `b`; arrow-stable, hence `⊥` or `⊤` everywhere.
    let W : ∀ b, Submodule k (ρ.obj b) :=
      fun b => ⨆ (p : Σ a, (a ⟶ b)), LinearMap.range (ρ.mapLinear p.2)
    have hWval : ∀ b, W b = ⨆ (p : Σ a, (a ⟶ b)), LinearMap.range (ρ.mapLinear p.2) :=
      fun _ => rfl
    have hWstable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ W a, ρ.mapLinear e x ∈ W b := by
      intro a b e x _
      rw [hWval b]
      exact Submodule.mem_iSup_of_mem ⟨a, e⟩ (LinearMap.mem_range_self _ x)
    rcases hdich W hWstable with hbot | htop
    · -- All `W b = ⊥`: each image is `⊥`, so each arrow map is `0`.
      intro a b e
      have hle : LinearMap.range (ρ.mapLinear e) ≤ W b := by
        rw [hWval b]
        exact le_iSup (fun p : Σ a, (a ⟶ b) => LinearMap.range (ρ.mapLinear p.2)) ⟨a, e⟩
      rw [hbot b] at hle
      rw [← LinearMap.range_eq_bot]
      exact le_bot_iff.mp hle
    · -- All `W b = ⊤`: a well-founded induction shows every carrier is trivial — impossible.
      exfalso
      have hAllTrivial : ∀ v, (⊤ : Submodule k (ρ.obj v)) = ⊥ := by
        intro v
        refine hwf.induction (C := fun v => (⊤ : Submodule k (ρ.obj v)) = ⊥) v (fun b IH => ?_)
        have hWb : W b = ⊥ := by
          rw [hWval b, iSup_eq_bot]
          rintro ⟨a, e⟩
          have hsubA : Subsingleton (ρ.obj a) := subsingleton_of_bot_eq_top (IH a ⟨e⟩).symm
          have hmap : ρ.mapLinear e = 0 := by
            haveI := hsubA
            exact LinearMap.ext fun x => by
              have hx : x = 0 := Subsingleton.elim _ _
              subst hx; simp
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
  -- Vertices `v ≠ v₀` carry the trivial space.
  have hconc : ∀ v, v ≠ v₀ → Subsingleton (ρ.obj v) := by
    intro v hv
    let E : ∀ w, Submodule k (ρ.obj w) := fun w => if w = v₀ then ⊤ else ⊥
    have hEstable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ E a, ρ.mapLinear e x ∈ E b := by
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
    have hFstable : ∀ {a b : Q} (e : a ⟶ b), ∀ x ∈ F a, ρ.mapLinear e x ∈ F b := by
      intro a b e x _
      rw [hzero e, LinearMap.zero_apply]
      exact (F b).zero_mem
    rcases hdich F hFstable with hb | ht
    · exact Or.inl (by have := hb v₀; simpa only [F, Function.update_self] using this)
    · exact Or.inr (by have := ht v₀; simpa only [F, Function.update_self] using this)
  -- `simpleRep v₀` has `finrank` `1` at `v₀` and `0` elsewhere.
  have hsimpleFinrank : ∀ v,
      Module.finrank k ((simpleRep (k := k) v₀).obj v) = if v = v₀ then 1 else 0 := by
    intro v
    show Module.finrank k (Fin (if v = v₀ then 1 else 0) → k) = _
    rw [Module.finrank_pi k, Fintype.card_fin]
  -- Step C: a vertexwise linear equivalence `ρ ≅ simpleRep v₀`.
  have hEquiv : ∀ v, Nonempty (ρ.obj v ≃ₗ[k] (simpleRep (k := k) v₀).obj v) := by
    intro v
    by_cases h : v = v₀
    · subst h
      haveI : Module.Finite k (ρ.obj v) := by
        obtain ⟨x, hx⟩ := exists_ne (0 : ρ.obj v)
        exact Module.Finite.of_surjective (LinearMap.toSpanSingleton k (ρ.obj v) x)
          (IsSimpleModule.toSpanSingleton_surjective k hx)
      haveI : Module.Finite k ((simpleRep (k := k) v).obj v) := by
        show Module.Finite k (Fin (if v = v then 1 else 0) → k); rw [if_pos rfl]; infer_instance
      haveI : Module.Free k ((simpleRep (k := k) v).obj v) := by
        show Module.Free k (Fin (if v = v then 1 else 0) → k); rw [if_pos rfl]; infer_instance
      apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      rw [hsimpleFinrank v, if_pos rfl, isSimpleModule_iff_finrank_eq_one.mp hsimple]
    · haveI : Subsingleton (ρ.obj v) := hconc v h
      haveI : Subsingleton ((simpleRep (k := k) v₀).obj v) := by
        show Subsingleton (Fin (if v = v₀ then 1 else 0) → k); rw [if_neg h]; infer_instance
      exact ⟨LinearEquiv.ofBijective (0 : ρ.obj v →ₗ[k] (simpleRep (k := k) v₀).obj v)
        ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩⟩
  -- Assemble the isomorphism. `commutes` is automatic: all arrow maps vanish on both sides.
  refine ⟨v₀, ⟨{ equivAt := fun v => (hEquiv v).some, commutes := ?_ }⟩⟩
  intro a b e x
  have h1 : ρ.mapLinear e = 0 := hzero e
  have h2 : (simpleRep (k := k) v₀).mapLinear e = 0 := rfl
  simp only [h1, h2, LinearMap.zero_apply, map_zero]

/-- **`Ext¹` between irreducibles.** `Ext¹(S_i, S_j) = 0` if and only if there are no arrows
`i → j`. (More precisely `dim Ext¹(S_i, S_j)` equals the number of arrows `i → j`.) -/
theorem ext1_simpleRep_vanishes_iff [DecidableEq Q] (i j : Q) :
    Ext1Vanishes (simpleRep (k := k) i) (simpleRep j) ↔ IsEmpty (i ⟶ j) := by
  -- Both simple representations have all arrow maps zero, so the Ext differential is the
  -- constant zero map. Hence Ext-vanishing (surjectivity) holds iff the codomain is trivial,
  -- and the codomain component at an arrow `a ⟶ b` is `Hom(S_i(a), S_j(b))`, which is nonzero
  -- exactly when `a = i` and `b = j`, i.e. when there is an arrow `i → j`.
  have hzero : Etingof.Problem6_9_3.extDiff (simpleRep (k := k) i) (simpleRep j) = fun _ => 0 := by
    letI : ∀ v, AddCommGroup ((simpleRep (k := k) j).obj v) :=
      fun _ => Etingof.Problem6_9_3.acg (k := k)
    funext f p
    simp only [Etingof.Problem6_9_3.extDiff, simpleRep, LinearMap.zero_comp, LinearMap.comp_zero,
      Pi.zero_apply]
    exact sub_self (0 : (simpleRep (k := k) i).obj p.1 →ₗ[k] (simpleRep (k := k) j).obj p.2.1)
  rw [Ext1Vanishes, hzero]
  constructor
  · -- Ext vanishes ⇒ no arrow `i → j`.
    intro hsurj
    rw [isEmpty_iff]
    intro e
    classical
    -- A nonzero linear map `S_i(i) →ₗ S_j(j)`: both spaces are `Fin 1 → k`.
    have hip : 0 < (if i = i then (1 : ℕ) else 0) := by rw [if_pos rfl]; norm_num
    have hjp : 0 < (if j = j then (1 : ℕ) else 0) := by rw [if_pos rfl]; norm_num
    let g : (simpleRep (k := k) i).obj i →ₗ[k] (simpleRep (k := k) j).obj j :=
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
        have hsub : Subsingleton ((simpleRep (k := k) i).obj a) := by
          show Subsingleton (Fin (if a = i then 1 else 0) → k)
          rw [if_neg ha]; infer_instance
        rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
    · -- Codomain `S_j(b)` is trivial (`b ≠ j`), so any map into it is 0.
      symm
      have hsub : Subsingleton ((simpleRep (k := k) j).obj b) := by
        show Subsingleton (Fin (if b = j then 1 else 0) → k)
        rw [if_neg hb]; infer_instance
      exact LinearMap.ext fun x => Subsingleton.elim _ _

/-- **Classification of 2-dimensional representations.** For a quiver without oriented cycles,
a representation `ρ` of total dimension `2` is either decomposable — necessarily a direct sum
`S_i ⊕ S_j` of two simples — or indecomposable, in which case there is a single arrow
`a : i → j` (with `i ≠ j`, since `Q` is acyclic) acting as an isomorphism, and `ρ` is the
representation supported on `a`. -/
theorem two_dim_classification [DecidableEq Q] [Fintype Q]
    (hQ : NoOrientedCycles Q) (ρ : QuiverRepresentation k Q)
    [∀ v, Module.Free k (ρ.obj v)] [∀ v, Module.Finite k (ρ.obj v)]
    (h2 : ∑ v, dimVec ρ v = 2) :
    (¬ ρ.IsIndecomposable)
      ∨ (∃ (i j : Q) (a : i ⟶ j), i ≠ j ∧ Function.Bijective (ρ.mapLinear a)) := by
  sorry

end Etingof.Problem3_9_3
