import EtingofRepresentationTheory.Chapter6.Problem6_1_5_OrbitSpace
import EtingofRepresentationTheory.Chapter6.DecompositionExistence
import EtingofRepresentationTheory.Chapter6.FiniteTypeDefs
import EtingofRepresentationTheory.Chapter6.Definition6_6_4
import Mathlib

/-!
# Problem 6.1.5, Step 1(b): finite type ⟹ finitely many orbits on `W(m)`

This file is part of the orbit-counting redirect for the Chapter 6 finite-type
classification (directive #4777, step 1).

The deliverable is the implication

> if the quiver has **finite representation type** (finitely many isomorphism
> classes of indecomposable representations), then for each dimension vector `m`
> the group `G(m) = ∏ᵢ GLₘᵢ(k)` acts on the representation space `W(m)` with only
> **finitely many orbits**.

The conclusion is phrased exactly as the downstream consumer
(`Problem6_1_5_DenseOrbit.lean`) needs it: `Finite (orbitRel.Quotient (repGroup k m)
(repSpace m))`.

## Strategy

By `orbit_iff_isomorphic` (S0), orbits on `W(m)` correspond to isomorphism classes
of representations of dimension vector `m`. By `exists_decomposition`
(`DecompositionExistence.lean`, #4794) every such representation is a finite direct
sum of indecomposables. Finite type provides a finite set `reps` of indecomposable
representatives, and every indecomposable summand is isomorphic to one of them. The
total dimension is `∑ᵢ mᵢ`, and each indecomposable summand contributes at least `1`
to it, so the number of summands is bounded by `∑ᵢ mᵢ`. Hence each orbit is named by
a bounded-length list of representatives drawn from the finite set `reps`, a finite
amount of data. Surjecting this finite index onto the orbit quotient gives finiteness.

Krull–Schmidt / uniqueness of the decomposition is deliberately **not** used: we only
need a surjection from a finite index, not a well-defined invariant.
-/

namespace Etingof

open Etingof.QuiverRepresentation MulAction

variable {k : Type} [Field k] {n : ℕ} [Quiver.{0} (Fin n)]

/-! ## Congruence of `directSumList` under entrywise isomorphism -/

/-- If two lists of representations are related entrywise by `AreIsomorphic`, their
iterated direct sums are isomorphic. -/
theorem areIsomorphic_directSumList_forall₂
    {L₁ L₂ : List (QuiverRepresentation k (Fin n))}
    (h : List.Forall₂ QuiverRepresentation.AreIsomorphic L₁ L₂) :
    (directSumList L₁).AreIsomorphic (directSumList L₂) := by
  induction h with
  | nil => exact AreIsomorphic.refl _
  | cons hab _ ih =>
      rw [directSumList_cons, directSumList_cons]
      exact AreIsomorphic.directSum hab ih

/-- Mapping each summand to an isomorphic representation preserves the iterated direct
sum up to isomorphism. -/
theorem areIsomorphic_directSumList_map
    {L : List (QuiverRepresentation k (Fin n))}
    {R : QuiverRepresentation k (Fin n) → QuiverRepresentation k (Fin n)}
    (hR : ∀ W ∈ L, W.AreIsomorphic (R W)) :
    (directSumList L).AreIsomorphic (directSumList (L.map R)) := by
  apply areIsomorphic_directSumList_forall₂
  induction L with
  | nil => exact List.Forall₂.nil
  | cons a L' ih =>
      refine List.Forall₂.cons (hR a (List.mem_cons_self ..)) (ih ?_)
      intro W hW
      exact hR W (List.mem_cons_of_mem _ hW)

/-! ## Realising an abstract representation as a point of `W(m)` -/

/-- **Realisation.** If a representation `V` has each vertex space linearly isomorphic
to `kᵐⁱ`, then `V` is isomorphic to `repOfPoint m x` for some point `x ∈ W(m)`. -/
theorem exists_point_areIsomorphic_of_obj_equiv (m : Fin n → ℕ)
    (V : QuiverRepresentation k (Fin n))
    (h : ∀ i, Nonempty (V.obj i ≃ₗ[k] (Fin (m i) → k))) :
    ∃ x : repSpace (k := k) m, (repOfPoint m x).AreIsomorphic V := by
  classical
  -- Vertex equivalences `e i : V.obj i ≃ₗ kᵐⁱ`.
  let e : ∀ i, V.obj i ≃ₗ[k] (Fin (m i) → k) := fun i => (h i).some
  -- Transport the edge maps into matrices over `kᵐ`.
  refine ⟨fun i j f =>
      LinearMap.toMatrix' ((e j).toLinearMap ∘ₗ V.mapLinear f ∘ₗ (e i).symm.toLinearMap), ?_⟩
  refine ⟨fun i => (e i).symm, ?_⟩
  intro a b f
  ext y
  simp [repOfPoint_mapLinear, Matrix.toLin'_toMatrix']

/-! ## Finiteness bookkeeping for `directSumList` -/

/-- A direct summand of an iterated direct sum inherits finiteness at each vertex. -/
theorem finite_of_mem_directSumList {v : Fin n}
    {L : List (QuiverRepresentation k (Fin n))}
    (hfin : Module.Finite k ((directSumList L).obj v))
    {W : QuiverRepresentation k (Fin n)} (hW : W ∈ L) :
    Module.Finite k (W.obj v) := by
  induction L with
  | nil => exact absurd hW (List.not_mem_nil)
  | cons a L' ih =>
      rw [directSumList_cons] at hfin
      -- `(directSum a (directSumList L')).obj v = a.obj v × (directSumList L').obj v`.
      have hprod : Module.Finite k (a.obj v × (directSumList L').obj v) := hfin
      haveI ha : Module.Finite k (a.obj v) :=
        Module.Finite.of_surjective (LinearMap.fst k (a.obj v) ((directSumList L').obj v))
          Prod.fst_surjective
      haveI hrest : Module.Finite k ((directSumList L').obj v) :=
        Module.Finite.of_surjective (LinearMap.snd k (a.obj v) ((directSumList L').obj v))
          Prod.snd_surjective
      rcases List.mem_cons.mp hW with h | h
      · subst h; exact ha
      · exact ih hrest h

/-- If every summand is finite at `v`, the iterated direct sum is finite at `v`. -/
theorem finite_directSumList {v : Fin n}
    {L : List (QuiverRepresentation k (Fin n))}
    (hfin : ∀ W ∈ L, Module.Finite k (W.obj v)) :
    Module.Finite k ((directSumList L).obj v) := by
  induction L with
  | nil =>
      rw [directSumList_nil]
      have : Subsingleton ((zeroRep : QuiverRepresentation k (Fin n)).obj v) := by
        change Subsingleton PUnit; infer_instance
      rw [Module.finite_def, Subsingleton.elim (⊤ : Submodule k _) ⊥]
      exact Submodule.fg_bot
  | cons a L' ih =>
      rw [directSumList_cons]
      haveI : Module.Finite k (a.obj v) := hfin a (List.mem_cons_self ..)
      haveI : Module.Finite k ((directSumList L').obj v) :=
        ih (fun W hW => hfin W (List.mem_cons_of_mem _ hW))
      exact inferInstanceAs (Module.Finite k (a.obj v × _))

/-- The total dimension of an iterated direct sum is the sum of the total dimensions. -/
theorem finrank_sum_directSumList
    {L : List (QuiverRepresentation k (Fin n))}
    (hfin : ∀ W ∈ L, ∀ v, Module.Finite k (W.obj v)) :
    (∑ i, Module.finrank k ((directSumList L).obj i))
      = (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).sum := by
  induction L with
  | nil =>
      simp only [directSumList_nil, List.map_nil, List.sum_nil]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have : Subsingleton ((zeroRep : QuiverRepresentation k (Fin n)).obj i) := by
        change Subsingleton PUnit; infer_instance
      exact Module.finrank_zero_of_subsingleton
  | cons a L' ih =>
      have hfin' : ∀ W ∈ L', ∀ v, Module.Finite k (W.obj v) :=
        fun W hW => hfin W (List.mem_cons_of_mem _ hW)
      have ha : ∀ v, Module.Finite k (a.obj v) := hfin a (List.mem_cons_self ..)
      have hrest : ∀ v, Module.Finite k ((directSumList L').obj v) :=
        fun v => finite_directSumList (fun W hW => hfin' W hW v)
      letI : ∀ v, AddCommGroup (a.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
      letI : ∀ v, AddCommGroup ((directSumList L').obj v) :=
        fun v => Etingof.addCommGroupOfRing (k := k)
      rw [directSumList_cons, List.map_cons, List.sum_cons, ← ih hfin']
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      haveI := ha i
      haveI := hrest i
      exact Module.finrank_prod

/-- An indecomposable representation that is finite at every vertex has total
dimension at least `1`. -/
theorem one_le_finrank_sum_of_isIndecomposable
    {W : QuiverRepresentation k (Fin n)}
    (hfin : ∀ v, Module.Finite k (W.obj v)) (hW : W.IsIndecomposable) :
    1 ≤ ∑ i, Module.finrank k (W.obj i) := by
  obtain ⟨v, hv⟩ := hW.1
  letI : ∀ w, AddCommGroup (W.obj w) := fun w => Etingof.addCommGroupOfRing (k := k)
  haveI := hfin v
  have hpos : 0 < Module.finrank k (W.obj v) := by
    rw [Module.finrank_pos_iff_of_free]; exact hv
  calc 1 ≤ Module.finrank k (W.obj v) := hpos
    _ ≤ ∑ i, Module.finrank k (W.obj i) :=
        Finset.single_le_sum (f := fun i => Module.finrank k (W.obj i))
          (fun i _ => Nat.zero_le _) (Finset.mem_univ v)

/-! ## Length bound -/

/-- The number of indecomposable summands of a representation of dimension vector `m`
is bounded by the total dimension `∑ᵢ mᵢ`. -/
theorem length_le_of_areIsomorphic_repOfPoint (m : Fin n → ℕ)
    (x : repSpace (k := k) m) {L : List (QuiverRepresentation k (Fin n))}
    (hiso : (directSumList L).AreIsomorphic (repOfPoint m x))
    (hind : ∀ W ∈ L, W.IsIndecomposable) :
    L.length ≤ ∑ i, m i := by
  obtain ⟨e, -⟩ := hiso
  -- Finiteness of the direct sum at each vertex (transported from `repOfPoint`).
  have hfinDS : ∀ v, Module.Finite k ((directSumList L).obj v) := by
    intro v
    haveI : Module.Finite k ((repOfPoint m x).obj v) := by
      change Module.Finite k (Fin (m v) → k); infer_instance
    exact Module.Finite.equiv (e v).symm
  have hfinW : ∀ W ∈ L, ∀ v, Module.Finite k (W.obj v) :=
    fun W hW v => finite_of_mem_directSumList (hfinDS v) hW
  -- Total dimension equals `∑ᵢ mᵢ`.
  have htd : (∑ i, Module.finrank k ((directSumList L).obj i)) = ∑ i, m i := by
    have h1 : ∀ i, Module.finrank k ((directSumList L).obj i)
        = Module.finrank k ((repOfPoint m x).obj i) := fun i => LinearEquiv.finrank_eq (e i)
    have h2 : ∀ i, Module.finrank k ((repOfPoint m x).obj i) = m i := by
      intro i; change Module.finrank k (Fin (m i) → k) = m i; exact Module.finrank_fin_fun (R := k)
    simp_rw [h1, h2]
  rw [finrank_sum_directSumList hfinW] at htd
  -- Each summand contributes at least `1`.
  have hge : L.length ≤ (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).sum := by
    have h1 : (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).length
        ≤ (L.map (fun W => ∑ i, Module.finrank k (W.obj i))).sum := by
      refine List.length_le_sum_of_one_le _ ?_
      intro y hy
      obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hy
      exact one_le_finrank_sum_of_isIndecomposable (hfinW W hW) (hind W hW)
    rwa [List.length_map] at h1
  rw [htd] at hge
  exact hge

/-! ## Realisation as a point -/

open Classical in
/-- A point of `W(m)` realising `V`, when `V` has the right dimensions; junk
(the zero point) otherwise. The realising property is `repOfPoint_realizePoint`. -/
noncomputable def realizePoint (m : Fin n → ℕ) (V : QuiverRepresentation k (Fin n)) :
    repSpace (k := k) m :=
  if h : ∀ i, Nonempty (V.obj i ≃ₗ[k] (Fin (m i) → k))
  then (exists_point_areIsomorphic_of_obj_equiv m V h).choose
  else fun _ _ _ => 0

theorem repOfPoint_realizePoint (m : Fin n → ℕ) (V : QuiverRepresentation k (Fin n))
    (h : ∀ i, Nonempty (V.obj i ≃ₗ[k] (Fin (m i) → k))) :
    (repOfPoint m (realizePoint m V)).AreIsomorphic V := by
  rw [realizePoint, dif_pos h]
  exact (exists_point_areIsomorphic_of_obj_equiv m V h).choose_spec

/-! ## The orbit-finiteness theorem -/

/-- **Finitely many orbits (core form).** If there is a finite set `reps` of
representatives such that every finite-dimensional indecomposable representation is
isomorphic to one of them, then `G(m)` acts on `W(m)` with finitely many orbits. -/
theorem orbitRel_quotient_finite_of_finite_reps (m : Fin n → ℕ)
    (reps : Set (QuiverRepresentation.{0, 0, 0, 0} k (Fin n)))
    (hrepsfin : reps.Finite)
    (hreps : ∀ (W : QuiverRepresentation.{0, 0, 0, 0} k (Fin n)),
        (∀ v, Module.Free k (W.obj v)) → (∀ v, Module.Finite k (W.obj v)) →
        W.IsIndecomposable → ∃ V ∈ reps, W.AreIsomorphic V) :
    Finite (orbitRel.Quotient (repGroup k m) (repSpace (k := k) m)) := by
  classical
  haveI : Finite reps := hrepsfin.to_subtype
  set Mtot := ∑ i, m i with hMtot
  -- The finite index: bounded-length lists of representatives.
  haveI hIdx : Finite {l : List reps | l.length ≤ Mtot} :=
    (List.finite_length_le reps Mtot).to_subtype
  -- The surjection from the finite index onto the orbit quotient.
  refine Finite.of_surjective
    (β := orbitRel.Quotient (repGroup k m) (repSpace (k := k) m))
    (fun l : {l : List reps | l.length ≤ Mtot} =>
      Quotient.mk'' (realizePoint m (directSumList (l.1.map Subtype.val)))) ?_
  -- Surjectivity.
  intro q
  induction q using Quotient.inductionOn' with
  | _ x =>
    -- Decompose `repOfPoint x` into indecomposables.
    haveI : ∀ v, Module.Finite k ((repOfPoint m x).obj v) := fun v => by
      change Module.Finite k (Fin (m v) → k); infer_instance
    obtain ⟨L, hLind, hLiso⟩ := exists_decomposition (repOfPoint m x)
    -- Each summand is finite at each vertex.
    obtain ⟨e, -⟩ := id hLiso
    have hfinW : ∀ W ∈ L, ∀ v, Module.Finite k (W.obj v) := by
      intro W hW v
      have hfinDS : Module.Finite k ((directSumList L).obj v) := Module.Finite.equiv (e v)
      exact finite_of_mem_directSumList hfinDS hW
    -- Pick a representative in `reps` for each summand.
    have hpick : ∀ W ∈ L, ∃ R ∈ reps, W.AreIsomorphic R := by
      intro W hW
      letI : ∀ v, AddCommGroup (W.obj v) := fun v => Etingof.addCommGroupOfRing (k := k)
      exact hreps W (fun v => inferInstance) (hfinW W hW) (hLind W hW)
    choose! R hRmem hRiso using hpick
    -- The list of chosen representatives, built with `pmap`.
    let L' : List reps := L.pmap (fun W hW => (⟨R W, hRmem W hW⟩ : reps)) (fun _ h => h)
    have hL'val : L'.map Subtype.val = L.map R := by
      rw [List.map_pmap]; exact List.pmap_eq_map _
    have hlen' : L'.length = L.length := List.length_pmap
    -- `directSumList (L'.map val) = directSumList (L.map R) ≅ directSumList L ≅ repOfPoint x`.
    have hbig : (directSumList (L'.map Subtype.val)).AreIsomorphic (repOfPoint m x) := by
      rw [hL'val]
      exact (areIsomorphic_directSumList_map hRiso).symm.trans hLiso.symm
    -- The list has bounded length.
    have hlen : L'.length ≤ Mtot := by
      rw [hlen', hMtot]
      exact length_le_of_areIsomorphic_repOfPoint m x hLiso.symm hLind
    refine ⟨⟨L', hlen⟩, ?_⟩
    -- The realisation hypothesis holds, so `realizePoint` produces a genuine point.
    have hH : ∀ i, Nonempty ((directSumList (L'.map Subtype.val)).obj i ≃ₗ[k] (Fin (m i) → k)) := by
      obtain ⟨e', -⟩ := id hbig
      exact fun i => ⟨e' i⟩
    -- Both points realise isomorphic representations, hence share an orbit.
    have hiso2 : (repOfPoint m x).AreIsomorphic
        (repOfPoint m (realizePoint m (directSumList (L'.map Subtype.val)))) :=
      hbig.symm.trans (repOfPoint_realizePoint m _ hH).symm
    obtain ⟨g, hg⟩ := (orbit_iff_isomorphic m x
      (realizePoint m (directSumList (L'.map Subtype.val)))).mpr hiso2
    change Quotient.mk'' (realizePoint m (directSumList (L'.map Subtype.val))) = Quotient.mk'' x
    exact Quotient.sound' (hg ▸ MulAction.mem_orbit x g)

/-! ## Wrapper: from `IsFiniteTypeQuiver` -/

end Etingof
