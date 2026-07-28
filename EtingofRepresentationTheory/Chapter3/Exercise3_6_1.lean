import EtingofRepresentationTheory.Chapter3.Theorem3_6_2

/-!
# Exercise 3.6.1: Additivity of the character on a subrepresentation

Show that if `W ⊂ V` are finite dimensional representations of `A`, then
`χ_V = χ_W + χ_{V/W}`.

Following the project convention (`Etingof.character`, see `Theorem3_6_2`), a representation
of `A` is an `A`-module `V` that is also a `k`-module with `IsScalarTower k A V`; its
character is `χ_V : A → k`, `a ↦ Tr|_V (ρ(a))`. A subrepresentation is an `A`-submodule
`W : Submodule A V`; the quotient representation is `V ⧸ W`. Over the field `k` a finite
dimensional `V` yields finite dimensional `W` and `V ⧸ W` (registered below as local
instances), so all three characters are defined, and the claim is the additivity
`χ_V = χ_W + χ_{V/W}` in the dual space `Dual k A`.

The proof is additivity of the trace along the short exact sequence `0 → W → V → V/W → 0`:
over the field `k` the sequence splits, giving a projection `pW` onto `W` and a section `s`
of the quotient map, so `ρ_V(a) = ρ_V(a) ∘ pW + ρ_V(a) ∘ (s ∘ q)`. Cyclicity of the trace
identifies the two summands with `Tr ρ_W(a)` and `Tr ρ_{V/W}(a)`.
-/

open Module

namespace Etingof

section Exercise361

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [FiniteDimensional k V]
  (W : Submodule A V)

/-- A subrepresentation of a finite dimensional representation is finite dimensional over
`k` (it is a `k`-subspace of the finite dimensional space `V`). -/
instance : Module.Finite k (W : Type _) :=
  Module.Finite.of_injective (W.subtype.restrictScalars k) Subtype.val_injective

/-- The quotient of a finite dimensional representation by a subrepresentation is finite
dimensional over `k`. -/
instance : Module.Finite k (V ⧸ W) :=
  Module.Finite.of_surjective (W.mkQ.restrictScalars k) W.mkQ_surjective

/-- Exercise 3.6.1. For a subrepresentation `W` of a finite dimensional representation `V`
of the algebra `A`, the character of `V` equals the sum of the characters of `W` and the
quotient `V ⧸ W`: `χ_V = χ_W + χ_{V/W}`. -/
theorem character_eq_character_add_character_quotient :
    Etingof.character k A V
      = Etingof.character k A (W : Type _) + Etingof.character k A (V ⧸ W) := by
  classical
  ext a
  -- The three action endomorphisms `ρ_V(a)`, `ρ_W(a)`, `ρ_{V/W}(a)`, i.e. `x ↦ a • x`.
  set fV : Module.End k V := (Algebra.lsmul k k V : A →ₐ[k] Module.End k V) a with hfV
  set fW : Module.End k (W : Type _) :=
    (Algebra.lsmul k k (W : Type _) : A →ₐ[k] Module.End k (W : Type _)) a with hfW
  set fQ : Module.End k (V ⧸ W) :=
    (Algebra.lsmul k k (V ⧸ W) : A →ₐ[k] Module.End k (V ⧸ W)) a with hfQ
  -- Unfold the characters to the corresponding traces.
  change LinearMap.trace k V fV
      = LinearMap.trace k (W : Type _) fW + LinearMap.trace k (V ⧸ W) fQ
  -- Inclusion `W ↪ V` and quotient map `V ↠ V/W`, as `k`-linear maps.
  set i : (W : Type _) →ₗ[k] V := (W.subtype).restrictScalars k with hi_def
  set q : V →ₗ[k] (V ⧸ W) := (W.mkQ).restrictScalars k with hq_def
  -- These intertwine the actions: `ρ_V(a)` restricts to `ρ_W(a)` and descends to `ρ_{V/W}(a)`.
  have hiW : i ∘ₗ fW = fV ∘ₗ i := by ext w; rfl
  have hqV : q ∘ₗ fV = fQ ∘ₗ q := by ext v; rfl
  -- Since `k` is a field, the short exact sequence `0 → W → V → V/W → 0` of `k`-spaces
  -- splits: choose a `k`-linear section `s` of `q`.
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr W.mkQ_surjective)
  -- The associated projection `pW = id - s ∘ q` onto `W` along `im s`.
  set pW : V →ₗ[k] V := LinearMap.id - s ∘ₗ q with hpW_def
  have hpW_mem : ∀ v : V, pW v ∈ W := by
    intro v
    have hqpW : q (pW v) = 0 := by
      have hqs : q (s (q v)) = q v := LinearMap.congr_fun hs (q v)
      simp only [hpW_def, LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply,
        map_sub, hqs, sub_self]
    exact (Submodule.Quotient.mk_eq_zero W).mp hqpW
  -- Corestrict `pW` to a `k`-linear retraction `r : V → W`.
  set r : V →ₗ[k] (W : Type _) :=
    { toFun := fun v => ⟨pW v, hpW_mem v⟩
      map_add' := fun x y => by apply Subtype.ext; simp
      map_smul' := fun c x => by apply Subtype.ext; simp } with hr_def
  -- `i ∘ r = pW` and `r ∘ i = id`.
  have hir : i ∘ₗ r = pW := by ext v; rfl
  have hri : r ∘ₗ i = LinearMap.id := by
    ext w
    have hqiw : q (i w) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr w.2
    change (pW (i w) : V) = (w : V)
    have hpi : pW (i w) = i w := by
      rw [hpW_def]
      simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply, hqiw,
        map_zero, sub_zero]
    rw [hpi]
    rfl
  -- Splitting identity `pW + s ∘ q = id`.
  have hid : pW + s ∘ₗ q = LinearMap.id := by rw [hpW_def]; abel
  -- The quotient block: `q ∘ ρ_V(a) ∘ s = ρ_{V/W}(a)`.
  have hqfVs : q ∘ₗ (fV ∘ₗ s) = fQ := by
    rw [← LinearMap.comp_assoc, hqV, LinearMap.comp_assoc, hs, LinearMap.comp_id]
  -- The subrepresentation block: `r ∘ ρ_V(a) ∘ i = ρ_W(a)`.
  have hrfVi : r ∘ₗ (fV ∘ₗ i) = fW := by
    rw [← hiW, ← LinearMap.comp_assoc, hri, LinearMap.id_comp]
  -- Trace of each block, via cyclicity of the trace.
  have hterm2 : LinearMap.trace k V (fV ∘ₗ (s ∘ₗ q)) = LinearMap.trace k (V ⧸ W) fQ := by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm' q (fV ∘ₗ s), hqfVs]
  have hterm1 : LinearMap.trace k V (fV ∘ₗ pW) = LinearMap.trace k (W : Type _) fW := by
    rw [← hir, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm' r (fV ∘ₗ i), hrfVi]
  -- Assemble: `Tr ρ_V(a) = Tr ρ_W(a) + Tr ρ_{V/W}(a)`.
  calc LinearMap.trace k V fV
      = LinearMap.trace k V (fV ∘ₗ LinearMap.id) := by rw [LinearMap.comp_id]
    _ = LinearMap.trace k V (fV ∘ₗ (pW + s ∘ₗ q)) := by rw [← hid]
    _ = LinearMap.trace k V (fV ∘ₗ pW + fV ∘ₗ (s ∘ₗ q)) := by rw [LinearMap.comp_add]
    _ = LinearMap.trace k V (fV ∘ₗ pW) + LinearMap.trace k V (fV ∘ₗ (s ∘ₗ q)) := by rw [map_add]
    _ = LinearMap.trace k (W : Type _) fW + LinearMap.trace k (V ⧸ W) fQ := by
        rw [hterm1, hterm2]

end Exercise361

end Etingof
