import Mathlib
import EtingofRepresentationTheory.Chapter2.Definition2_8_3
import EtingofRepresentationTheory.Chapter2.Definition2_8_8
import EtingofRepresentationTheory.Chapter2.Definition2_8_10

/-!
# Composition series of quiver representations

This file supplies the finite-length machinery for `Etingof.QuiverRepresentation` that
Problem 6.9.3(b) needs: an order on subrepresentations, the representation underlying a
subrepresentation, the vertex simples `S i`, and a genuine notion of composition series
(a filtration by subrepresentations whose successive subquotients are vertex simples).

## The subquotient condition

Quiver representations here bundle only `AddCommMonoid` carriers (Definition 2.8.3), so a
quotient module `W' / W` is not directly available. We therefore express

> the subquotient `W' / W` is isomorphic to the vertex simple `S i`

in its first-isomorphism-theorem form: there is a homomorphism of representations
`π : W' → S i` which is **surjective at every vertex** and whose **kernel at every vertex is
exactly `W`**. This is `Etingof.IsSimpleStep`. It is equivalent to the quotient formulation
and is not satisfiable by accident: `IsSimpleStep.eq_or_eq` shows that a simple step admits no
intermediate subrepresentation, and `IsSimpleStep.ne` shows it is a proper inclusion.

## Main results

* `Etingof.QuiverSubrepresentation` order structure (`≤`, `⊥`, `⊤`), `toRep`, `restrictTo`
* `Etingof.vertexSimple` : the simple representation `S i`
* `Etingof.IsSimpleStep` : `W ≤ W'` with subquotient `S i`, and `isSimpleStep_of`, a
  construction principle from a single linear functional
* `Etingof.IsSimpleStep.eq_or_eq` : nothing lies strictly between the two terms of a simple step
* `Etingof.QuiverRepCompositionSeries` : a filtration `0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ V_N = V` with each
  successive subquotient a vertex simple
* `Etingof.exists_compositionSeries` : **every** representation of a finite quiver whose
  vertices can be ordered compatibly with the orientation (arrows decrease the order — always
  possible for an acyclic quiver, in particular for a Dynkin quiver) admits a composition
  series, of length `∑ v, dim Vᵥ`, in which `S i` occurs exactly `dim Vᵢ` times.

The ordering hypothesis is where the orientation enters: the *multiset* of factors is
orientation-independent, but the *order* in which they occur is read off from the orientation.
-/

namespace Etingof

open Module

variable {k Q : Type*} [Field k] [Quiver Q] {ρ : QuiverRepresentation k Q}

/-! ## The lattice of subrepresentations -/

namespace QuiverSubrepresentation

@[ext]
theorem ext {W W' : QuiverSubrepresentation k Q ρ}
    (h : ∀ v, W.carrier v = W'.carrier v) : W = W' := by
  obtain ⟨c, hc⟩ := W
  obtain ⟨c', hc'⟩ := W'
  have hcc : c = c' := funext h
  subst hcc
  rfl

instance : PartialOrder (QuiverSubrepresentation k Q ρ) where
  le W W' := ∀ v, W.carrier v ≤ W'.carrier v
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ v := (h₁ v).trans (h₂ v)
  le_antisymm _ _ h₁ h₂ := ext fun v => le_antisymm (h₁ v) (h₂ v)

theorem le_def {W W' : QuiverSubrepresentation k Q ρ} :
    W ≤ W' ↔ ∀ v, W.carrier v ≤ W'.carrier v := Iff.rfl

instance : OrderBot (QuiverSubrepresentation k Q ρ) where
  bot :=
    { carrier := fun _ => ⊥
      map_mem := by
        intro v w e x hx
        rw [Submodule.mem_bot] at hx ⊢
        rw [hx, map_zero] }
  bot_le _ _ := bot_le

instance : OrderTop (QuiverSubrepresentation k Q ρ) where
  top :=
    { carrier := fun _ => ⊤
      map_mem := fun _ _ _ => Submodule.mem_top }
  le_top _ _ := le_top

@[simp] theorem bot_carrier (v : Q) :
    (⊥ : QuiverSubrepresentation k Q ρ).carrier v = ⊥ := rfl

@[simp] theorem top_carrier (v : Q) :
    (⊤ : QuiverSubrepresentation k Q ρ).carrier v = ⊤ := rfl

/-- A subrepresentation, regarded as a representation in its own right.

Marked `@[reducible]` so that `W.toRep.obj v` and its module instances are transparently the
submodule `W.carrier v` and its instances; without this, linear maps out of `W.toRep.obj v`
and out of `↥(W.carrier v)` fail to unify at `instances` transparency. -/
@[reducible] def toRep (W : QuiverSubrepresentation k Q ρ) : QuiverRepresentation k Q where
  obj v := W.carrier v
  mapLinear e := (ρ.mapLinear e).restrict (fun x hx => W.map_mem e x hx)

/-- `W`, viewed as a family of subspaces of a larger subrepresentation `W'`. -/
def restrictTo (W W' : QuiverSubrepresentation k Q ρ) (v : Q) : Submodule k (W'.carrier v) :=
  (W.carrier v).comap (W'.carrier v).subtype

theorem mem_restrictTo {W W' : QuiverSubrepresentation k Q ρ} {v : Q} {x : W'.carrier v} :
    x ∈ W.restrictTo W' v ↔ (x : ρ.obj v) ∈ W.carrier v := Iff.rfl

theorem restrictTo_eq_top_iff {W W' : QuiverSubrepresentation k Q ρ} {v : Q} :
    W.restrictTo W' v = ⊤ ↔ W'.carrier v ≤ W.carrier v := by
  rw [eq_top_iff]
  constructor
  · intro h x hx
    exact (mem_restrictTo (W := W) (W' := W') (x := ⟨x, hx⟩)).1 (h Submodule.mem_top)
  · intro h x _
    exact h x.2

end QuiverSubrepresentation

/-! ## Vertex simples -/

/-- The **vertex simple** `S i = V_{αᵢ}`: a one-dimensional space at vertex `i`, zero
elsewhere, with all arrow maps zero. The vertex object is `Fin (if v = i then 1 else 0) → k`,
which branches on the dimension rather than on the type. -/
def vertexSimple [DecidableEq Q] (i : Q) : QuiverRepresentation k Q where
  obj v := Fin (if v = i then 1 else 0) → k
  mapLinear _ := 0

@[simp] theorem vertexSimple_mapLinear [DecidableEq Q] (i : Q) {v w : Q} (e : v ⟶ w) :
    (vertexSimple (k := k) i).mapLinear e = 0 := rfl

/-- At the marked vertex the index type of `vertexSimple i` is `Fin 1`. -/
@[reducible] def uniqueIndex [DecidableEq Q] (i : Q) : Unique (Fin (if i = i then 1 else 0)) := by
  rw [if_pos rfl]; infer_instance

omit [Quiver Q] in
/-- Away from the marked vertex the index type of `vertexSimple i` is empty. -/
theorem isEmptyIndex [DecidableEq Q] {u i : Q} (h : u ≠ i) :
    IsEmpty (Fin (if u = i then 1 else 0)) := by
  rw [if_neg h]; infer_instance

theorem vertexSimple_subsingleton [DecidableEq Q] {u i : Q} (h : u ≠ i) :
    Subsingleton ((vertexSimple (k := k) i).obj u) :=
  ⟨fun _ _ => funext fun x => (isEmptyIndex h).elim x⟩

/-! ## Simple steps -/

/-- `W ≤ W'` is a **simple step with factor `S i`** when the subquotient `W' / W` is isomorphic
to the vertex simple `S i`, stated in first-isomorphism-theorem form: some homomorphism
`W' → S i` is surjective at every vertex and has kernel exactly `W` at every vertex. -/
def IsSimpleStep [DecidableEq Q] (W W' : QuiverSubrepresentation k Q ρ) (i : Q) : Prop :=
  W ≤ W' ∧ ∃ π : QuiverRepresentationHom k Q W'.toRep (vertexSimple i),
    (∀ v, Function.Surjective (π.app v)) ∧
    ∀ v, LinearMap.ker (π.app v) = W.restrictTo W' v

/-- Helper: in a module over a field, `(x + (-1) • y) + y = x`, giving subtraction on carriers
that bundle only an `AddCommMonoid`. -/
theorem add_neg_one_smul_add {M : Type*} [AddCommMonoid M] [Module k M] (x y : M) :
    (x + (-1 : k) • y) + y = x := by
  rw [add_assoc]
  nth_rw 2 [show y = (1 : k) • y from (one_smul k y).symm]
  rw [← add_smul, neg_add_cancel, zero_smul, add_zero]

/-- **Construction principle for simple steps.** To exhibit `W ≤ W'` as a simple step with
factor `S i` it suffices to give a single surjective linear functional `φ` on `W'` at the
vertex `i` whose kernel is `W`, to know that `W` and `W'` agree at all other vertices, and to
know that `φ` kills the image of every arrow into `i`. -/
theorem isSimpleStep_of [DecidableEq Q] {W W' : QuiverSubrepresentation k Q ρ} {i : Q}
    (hle : W ≤ W')
    (heq : ∀ u, u ≠ i → W'.carrier u ≤ W.carrier u)
    (φ : W'.carrier i →ₗ[k] k)
    (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = W.restrictTo W' i)
    (hnat : ∀ {u : Q} (e : u ⟶ i) (x : W'.toRep.obj u), φ (W'.toRep.mapLinear e x) = 0) :
    IsSimpleStep W W' i := by
  classical
  set app : ∀ u, W'.toRep.obj u →ₗ[k] (vertexSimple (k := k) i).obj u := fun u =>
    if h : u = i then by subst h; exact LinearMap.pi (fun _ => φ) else 0 with happ_def
  have happ_self : app i = LinearMap.pi (fun _ => φ) := by
    simp only [happ_def, dif_pos rfl]
  have happ_other : ∀ u, u ≠ i → app u = 0 := by
    intro u hu; simp only [happ_def, dif_neg hu]
  have hnaturality : ∀ {v w : Q} (e : v ⟶ w) (x : W'.toRep.obj v),
      app w (W'.toRep.mapLinear e x) = (vertexSimple (k := k) i).mapLinear e (app v x) := by
    -- `S i` has zero arrow maps, so both sides vanish
    intro v w e x
    rw [vertexSimple_mapLinear, LinearMap.zero_apply]
    rcases eq_or_ne w i with rfl | hw
    · rw [happ_self]
      funext l
      exact hnat e x
    · rw [happ_other w hw]
      rfl
  have hsurj' : ∀ u, Function.Surjective (app u) := by
    intro u
    rcases eq_or_ne u i with rfl | hu
    · rw [happ_self]
      haveI := uniqueIndex u
      intro g
      obtain ⟨x, hx⟩ := hsurj (g default)
      refine ⟨x, funext fun l => ?_⟩
      rw [Subsingleton.elim l default]
      exact hx
    · haveI := vertexSimple_subsingleton (k := k) hu
      intro g
      exact ⟨0, Subsingleton.elim _ _⟩
  have hker' : ∀ u, LinearMap.ker (app u) = W.restrictTo W' u := by
    intro u
    rcases eq_or_ne u i with rfl | hu
    · rw [happ_self, ← hker]
      haveI := uniqueIndex u
      ext x
      simp only [LinearMap.mem_ker]
      constructor
      · intro h
        exact congrFun h default
      · intro h
        funext l
        exact h
    · rw [happ_other u hu, LinearMap.ker_zero]
      exact (QuiverSubrepresentation.restrictTo_eq_top_iff.2 (heq u hu)).symm
  exact ⟨hle, ⟨{ app := app, naturality := hnaturality }, hsurj', hker'⟩⟩

namespace IsSimpleStep

variable [DecidableEq Q] {W W' : QuiverSubrepresentation k Q ρ} {i : Q}

theorem le (h : IsSimpleStep W W' i) : W ≤ W' := h.1

/-- The scalar functional underlying a simple step: the component of the structure map at the
marked vertex, read through the identification of the one-dimensional space at `i` with `k`.
It is surjective and its kernel is exactly the smaller term. -/
theorem exists_functional (h : IsSimpleStep W W' i) :
    ∃ ψ : W'.toRep.obj i →ₗ[k] k,
      Function.Surjective ψ ∧ LinearMap.ker ψ = W.restrictTo W' i := by
  obtain ⟨hle, π, hsurj, hker⟩ := h
  haveI := uniqueIndex i
  refine ⟨(LinearMap.proj default) ∘ₗ (π.app i), ?_, ?_⟩
  · intro c
    obtain ⟨x, hx⟩ := hsurj i (fun _ => c)
    exact ⟨x, by rw [LinearMap.comp_apply, hx]; rfl⟩
  · rw [← hker i]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    constructor
    · intro hh
      funext l
      rw [Subsingleton.elim l default]
      exact hh
    · intro hh
      rw [hh]
      rfl

/-- Away from the marked vertex, the two terms of a simple step agree. -/
theorem carrier_eq_of_ne (h : IsSimpleStep W W' i) {u : Q} (hu : u ≠ i) :
    W.carrier u = W'.carrier u := by
  obtain ⟨hle, π, _, hker⟩ := h
  haveI := vertexSimple_subsingleton (k := k) (i := i) hu
  refine le_antisymm (hle u) ?_
  rw [← QuiverSubrepresentation.restrictTo_eq_top_iff, ← hker u]
  exact eq_top_iff.2 fun x _ => by
    simp only [LinearMap.mem_ker]
    exact Subsingleton.elim _ _

/-- A simple step is a proper inclusion. -/
theorem ne (h : IsSimpleStep W W' i) : W ≠ W' := by
  rintro rfl
  obtain ⟨ψ, hsurj, hker⟩ := h.exists_functional
  obtain ⟨x, hx⟩ := hsurj 1
  have hmem : x ∈ LinearMap.ker ψ := by
    rw [hker]
    exact (QuiverSubrepresentation.mem_restrictTo (W := W) (W' := W)).2 x.2
  rw [LinearMap.mem_ker, hx] at hmem
  exact one_ne_zero hmem

/-- **The subquotient of a simple step is simple**: no subrepresentation lies strictly between
its two terms. This is what makes `IsSimpleStep` a genuine composition-series step. -/
theorem eq_or_eq (h : IsSimpleStep W W' i) (U : QuiverSubrepresentation k Q ρ)
    (h₁ : W ≤ U) (h₂ : U ≤ W') : U = W ∨ U = W' := by
  classical
  obtain ⟨ψ, hsurj, hker⟩ := h.exists_functional
  by_cases hU : ∃ y : W'.toRep.obj i, (y : ρ.obj i) ∈ U.carrier i ∧ ψ y ≠ 0
  · -- `U` meets the subquotient nontrivially, hence exhausts `W'`
    right
    obtain ⟨y, hyU, hy0⟩ := hU
    refine le_antisymm h₂ fun u x hx => ?_
    rcases eq_or_ne u i with rfl | hu
    · -- correct `x` by a multiple of `y`, landing in the kernel, i.e. in `W ≤ U`
      set xx : W'.toRep.obj u := ⟨x, hx⟩ with hxx
      set y' : W'.toRep.obj u := (ψ xx / ψ y) • y with hy'
      set z : W'.toRep.obj u := xx + (-1 : k) • y' with hz
      have hzker : z ∈ LinearMap.ker ψ := by
        rw [LinearMap.mem_ker, hz, map_add, map_smul, hy', map_smul]
        simp only [smul_eq_mul]
        field_simp
        ring
      rw [hker] at hzker
      have hzU : (z : ρ.obj u) ∈ U.carrier u := h₁ u hzker
      have hyU' : (y' : ρ.obj u) ∈ U.carrier u := (U.carrier u).smul_mem _ hyU
      have hsum : z + y' = xx := add_neg_one_smul_add (k := k) xx y'
      have hmem : ((z + y' : W'.toRep.obj u) : ρ.obj u) ∈ U.carrier u :=
        (U.carrier u).add_mem hzU hyU'
      rw [hsum] at hmem
      exact hmem
    · rw [← h.carrier_eq_of_ne hu] at hx
      exact h₁ u hx
  · -- `U` is contained in the kernel, hence equals `W`
    left
    simp only [not_exists, not_and, not_not] at hU
    refine le_antisymm (fun u x hx => ?_) h₁
    rcases eq_or_ne u i with rfl | hu
    · have hxW' : x ∈ W'.carrier u := h₂ u hx
      have hzero : ψ ⟨x, hxW'⟩ = 0 := hU ⟨x, hxW'⟩ hx
      have hmem : (⟨x, hxW'⟩ : W'.toRep.obj u) ∈ LinearMap.ker ψ := by
        rw [LinearMap.mem_ker]; exact hzero
      rw [hker] at hmem
      exact hmem
    · rw [h.carrier_eq_of_ne hu]
      exact h₂ u hx

end IsSimpleStep

/-! ## Composition series -/

/-- A **composition series** (Jordan–Hölder series) of a quiver representation `ρ`: a chain
`0 = sub 0 ≤ sub 1 ≤ ⋯ ≤ sub length = ρ` of subrepresentations in which every successive
subquotient is the vertex simple `S (factor m)`. -/
structure QuiverRepCompositionSeries [DecidableEq Q] (ρ : QuiverRepresentation k Q) where
  /-- The length of the series. -/
  length : ℕ
  /-- The terms of the filtration. -/
  sub : ℕ → QuiverSubrepresentation k Q ρ
  /-- The vertex labelling the `m`-th factor. -/
  factor : Fin length → Q
  /-- The series starts at the zero subrepresentation. -/
  sub_zero : sub 0 = ⊥
  /-- The series ends at the whole representation. -/
  sub_length : sub length = ⊤
  /-- Each successive subquotient is a vertex simple. -/
  step : ∀ m : Fin length, IsSimpleStep (sub (m : ℕ)) (sub ((m : ℕ) + 1)) (factor m)

namespace QuiverRepCompositionSeries

variable [DecidableEq Q]

/-- The number of times `S i` occurs as a composition factor. -/
def mult (s : QuiverRepCompositionSeries ρ) (i : Q) : ℕ :=
  (Finset.univ.filter fun m => s.factor m = i).card

/-- Each inclusion in a composition series is strict. -/
theorem sub_ne (s : QuiverRepCompositionSeries ρ) (m : Fin s.length) :
    s.sub (m : ℕ) ≠ s.sub ((m : ℕ) + 1) := (s.step m).ne

end QuiverRepCompositionSeries

/-! ## Existence of composition series for an ordered quiver -/

/-- A partial-sum decomposition of `Finset.range`: every `m` below `∑_{l < n} f l` lies in
exactly one of the consecutive blocks. -/
theorem exists_range_index {f : ℕ → ℕ} {n m : ℕ} (hm : m < ∑ l ∈ Finset.range n, f l) :
    ∃ j, j < n ∧ (∑ l ∈ Finset.range j, f l) ≤ m ∧
      m < (∑ l ∈ Finset.range j, f l) + f j := by
  induction n with
  | zero => simp at hm
  | succ n ih =>
    rw [Finset.sum_range_succ] at hm
    rcases lt_or_ge m (∑ l ∈ Finset.range n, f l) with h | h
    · obtain ⟨j, hj, h₁, h₂⟩ := ih h
      exact ⟨j, by omega, h₁, h₂⟩
    · exact ⟨n, by omega, h, by omega⟩

/-- **Every representation of an ordered quiver has a composition series.**

`e` enumerates the vertices, and `hcompat` says the enumeration is compatible with the
orientation: every arrow decreases the index. (Such an enumeration is exactly a topological
sort; it exists for any acyclic quiver, in particular for any orientation of a Dynkin
diagram.) Given a basis of each vertex space, the representation admits a composition series
of length `∑ dim Vᵥ` in which the vertex simple `S i` occurs exactly `dim Vᵢ` times.

The filtration is the flag that fills up the vertex spaces one basis vector at a time, in the
order given by `e`: it is a chain of subrepresentations precisely because every arrow points
from a later vertex to an earlier one. -/
theorem exists_compositionSeries [DecidableEq Q] (ρ : QuiverRepresentation k Q)
    (n : ℕ) (e : Q ≃ Fin n) (hcompat : ∀ {v w : Q}, (v ⟶ w) → (e w : ℕ) < (e v : ℕ))
    (d : Q → ℕ) (b : ∀ v, Basis (Fin (d v)) k (ρ.obj v)) :
    ∃ s : QuiverRepCompositionSeries ρ,
      s.length = ∑ l : Fin n, d (e.symm l) ∧ ∀ i, s.mult i = d i := by
  classical
  -- `f l` is the dimension of the `l`-th vertex space, `cum v` the total dimension below `v`
  set f : ℕ → ℕ := fun l => if h : l < n then d (e.symm ⟨l, h⟩) else 0 with hf_def
  set cum : Q → ℕ := fun v => ∑ l ∈ Finset.range (e v : ℕ), f l with hcum_def
  set N : ℕ := ∑ l ∈ Finset.range n, f l with hN_def
  have hf_eq : ∀ v : Q, f (e v : ℕ) = d v := by
    intro v
    simp only [hf_def, dif_pos (e v).isLt, Fin.eta, Equiv.symm_apply_apply]
  have hcum_step : ∀ v : Q, cum v + d v = ∑ l ∈ Finset.range ((e v : ℕ) + 1), f l := by
    intro v
    rw [Finset.sum_range_succ, hf_eq]
  -- Blocks are ordered: everything below `w` plus `w` itself fits below `v`
  have hcum_le : ∀ {v w : Q}, (e w : ℕ) < (e v : ℕ) → cum w + d w ≤ cum v := by
    intro v w h
    rw [hcum_step]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
  have hcum_top : ∀ v : Q, cum v + d v ≤ N := by
    intro v
    rw [hcum_step, hN_def]
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (e v).isLt)
  -- The flag: at `v`, kill all basis coordinates `l` with `cum v + l ≥ m`
  set flag : ℕ → ∀ v : Q, Submodule k (ρ.obj v) := fun m v =>
    ⨅ l : {l : Fin (d v) // m ≤ cum v + (l : ℕ)},
      LinearMap.ker ((b v).coord (l : Fin (d v))) with hflag_def
  have hmem : ∀ (m : ℕ) (v : Q) (x : ρ.obj v),
      x ∈ flag m v ↔ ∀ l : Fin (d v), m ≤ cum v + (l : ℕ) → (b v).coord l x = 0 := by
    intro m v x
    simp [hflag_def, Submodule.mem_iInf, LinearMap.mem_ker, Subtype.forall]
  have hzero : ∀ (m : ℕ) (v : Q) (x : ρ.obj v), m ≤ cum v → x ∈ flag m v → x = 0 := by
    intro m v x hm hx
    refine (b v).ext_elem fun j => ?_
    rw [map_zero, Finsupp.zero_apply, ← Basis.coord_apply]
    exact (hmem m v x).1 hx j (by omega)
  have htop : ∀ (m : ℕ) (v : Q), cum v + d v ≤ m → flag m v = ⊤ := by
    intro m v hm
    refine eq_top_iff.2 fun x _ => (hmem m v x).2 fun l hl => ?_
    exact absurd hl (by have := l.isLt; omega)
  have hmono : ∀ {m m' : ℕ}, m ≤ m' → ∀ v, flag m v ≤ flag m' v := by
    intro m m' hmm v x hx
    exact (hmem m' v x).2 fun l hl => (hmem m v x).1 hx l (by omega)
  -- Invariance under the arrow maps
  have hinv : ∀ (m : ℕ) {v w : Q} (arr : v ⟶ w) (x : ρ.obj v),
      x ∈ flag m v → ρ.mapLinear arr x ∈ flag m w := by
    intro m v w arr x hx
    rcases le_or_gt m (cum v) with hm | hm
    · rw [hzero m v x hm hx, map_zero]
      exact Submodule.zero_mem _
    · have hle := hcum_le (hcompat arr)
      rw [htop m w (by omega)]
      exact Submodule.mem_top
  set sub : ℕ → QuiverSubrepresentation k Q ρ := fun m =>
    ⟨flag m, fun arr x hx => hinv m arr x hx⟩ with hsub_def
  have hsub_carrier : ∀ m v, (sub m).carrier v = flag m v := fun _ _ => rfl
  -- The two endpoints
  have hsub_zero : sub 0 = ⊥ := by
    refine QuiverSubrepresentation.ext fun v => eq_bot_iff.2 fun x hx => ?_
    rw [Submodule.mem_bot]
    exact hzero 0 v x (Nat.zero_le _) hx
  have hsub_N : sub N = ⊤ := by
    exact QuiverSubrepresentation.ext fun v => htop N v (hcum_top v)
  -- Every step index lies in exactly one vertex block
  have hblock : ∀ m : Fin N, ∃ v : Q, cum v ≤ (m : ℕ) ∧ (m : ℕ) < cum v + d v := by
    intro m
    obtain ⟨j, hj, h₁, h₂⟩ := exists_range_index (f := f) (n := n) (m := (m : ℕ)) m.isLt
    refine ⟨e.symm ⟨j, hj⟩, ?_, ?_⟩
    · simpa [hcum_def] using h₁
    · have hfe : f j = d (e.symm ⟨j, hj⟩) := by simp [hf_def, dif_pos hj]
      simpa [hcum_def, hfe] using h₂
  choose factor hfac₁ hfac₂ using hblock
  have huniq : ∀ (m : ℕ) (v w : Q), cum v ≤ m → m < cum v + d v → cum w ≤ m →
      m < cum w + d w → v = w := by
    intro m v w h₁ h₂ h₃ h₄
    rcases lt_trichotomy ((e v : ℕ)) ((e w : ℕ)) with h | h | h
    · exact absurd (hcum_le h) (by omega)
    · exact e.injective (Fin.ext h)
    · exact absurd (hcum_le h) (by omega)
  have hfactor_eq : ∀ (m : Fin N) (v : Q), cum v ≤ (m : ℕ) → (m : ℕ) < cum v + d v →
      factor m = v := fun m v h₁ h₂ => huniq (m : ℕ) (factor m) v (hfac₁ m) (hfac₂ m) h₁ h₂
  -- Each step is simple
  have hstep : ∀ m : Fin N, IsSimpleStep (sub (m : ℕ)) (sub ((m : ℕ) + 1)) (factor m) := by
    intro m
    set i : Q := factor m with hi_def
    have hcl : cum i ≤ (m : ℕ) := hfac₁ m
    have hcu : (m : ℕ) < cum i + d i := hfac₂ m
    -- the basis index reached at step `m`
    set r : Fin (d i) := ⟨(m : ℕ) - cum i, by omega⟩ with hr_def
    have hr_val : cum i + (r : ℕ) = (m : ℕ) := by simp only [hr_def]; omega
    -- vertices other than `i` do not change at this step
    have heq : ∀ u, u ≠ i → (sub ((m : ℕ) + 1)).carrier u ≤ (sub (m : ℕ)).carrier u := by
      intro u hu x hx
      refine (hmem (m : ℕ) u x).2 fun l hl => ?_
      rcases le_or_gt ((m : ℕ) + 1) (cum u + (l : ℕ)) with h | h
      · exact (hmem ((m : ℕ) + 1) u x).1 hx l h
      · exact absurd (hfactor_eq m u (by omega) (by have := l.isLt; omega)).symm hu
    refine isSimpleStep_of (hmono (Nat.le_succ _)) heq
      (((b i).coord r).comp ((sub ((m : ℕ) + 1)).carrier i).subtype) ?_ ?_ ?_
    · -- surjective: `c • b r` lies in the bigger term and has `r`-th coordinate `c`
      intro c
      have hmemc : c • (b i) r ∈ (sub ((m : ℕ) + 1)).carrier i := by
        refine (hmem ((m : ℕ) + 1) i _).2 fun l hl => ?_
        have hlr : l ≠ r := by rintro rfl; omega
        simp [Basis.coord_apply, hlr]
      exact ⟨⟨_, hmemc⟩, by simp [Basis.coord_apply]⟩
    · -- kernel is exactly the smaller term
      ext x
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
        QuiverSubrepresentation.mem_restrictTo, hsub_carrier]
      constructor
      · intro h
        refine (hmem (m : ℕ) i (x : ρ.obj i)).2 fun l hl => ?_
        rcases le_or_gt ((m : ℕ) + 1) (cum i + (l : ℕ)) with h' | h'
        · exact (hmem ((m : ℕ) + 1) i _).1 x.2 l h'
        · have : l = r := Fin.ext (by omega)
          rw [this]; exact h
      · intro h
        exact (hmem (m : ℕ) i _).1 h r (by omega)
    · -- arrows into `i` start from a vertex whose space is still zero
      intro u arr x
      have hlt : (e i : ℕ) < (e u : ℕ) := hcompat arr
      have hle := hcum_le hlt
      have hx0 : (x : ρ.obj u) = 0 := hzero ((m : ℕ) + 1) u _ (by omega) x.2
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [show ((sub ((m : ℕ) + 1)).toRep.mapLinear arr x : ρ.obj i) =
            ρ.mapLinear arr (x : ρ.obj u) from rfl, hx0, map_zero, map_zero]
  refine ⟨⟨N, sub, factor, hsub_zero, hsub_N, hstep⟩, ?_, ?_⟩
  · change N = ∑ l : Fin n, d (e.symm l)
    rw [hN_def, ← Fin.sum_univ_eq_sum_range (fun l => f l) n]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hf_def, dif_pos l.isLt]
  · -- multiplicities: the `m` with `factor m = i` are exactly the block of `i`
    intro i
    change (Finset.univ.filter fun m : Fin N => factor m = i).card = d i
    rw [← Finset.card_range (d i)]
    refine Finset.card_bij' (fun m _ => (m : ℕ) - cum i)
      (fun j hj => ⟨cum i + j, ?_⟩) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_range] at hj
      have := hcum_top i
      omega
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have h₁ := hfac₁ m
      have h₂ := hfac₂ m
      rw [hm.2] at h₁ h₂
      simp only [Finset.mem_range]
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfactor_eq _ i (by simp) (by simp; omega)
    · intro m hm
      simp only [Finset.mem_filter] at hm
      have h₁ := hfac₁ m
      rw [hm.2] at h₁
      exact Fin.ext (by simp; omega)
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp

end Etingof
