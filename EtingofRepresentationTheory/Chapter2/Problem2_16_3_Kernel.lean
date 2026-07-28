import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Bidegree


/-!
# Problem 2.16.3(b): the kernel of the loop realization of `𝔤₄`

`Problem2_16_3_Layers.lean` spans `𝔤₄` unconditionally by the `LoopIdx`-indexed family `loopFam₄`
together with the layer defects `topDefect` (`span_loopSet_eq_top`), and
`Problem2_16_3_Tower.lean` shows that `gbar` carries `loopFam₄` to a rescaling of the graded basis
of the twisted loop algebra `𝔫₊(A₂⁽²⁾)`, so that `gbar ∘ loopFam₄` is linearly independent
(`linearIndependent_gbar_comp_loopFam₄`). On the other side `Problem2_16_3_Center.lean` shows that
the loop model annihilates the centre of `𝔤₄`, and each defect is central
(`central_topDefect`), so every defect lies in the kernel.

Those two facts pin the kernel exactly:

    ker (gbar k) = span k (range (topDefect k)).

The identification is what turns the surjection `𝔤₄ ↠ range gbar = 𝔫₊(A₂⁽²⁾)` into a *central*
extension: `lie_mem_ker_gbar` shows the kernel consists of central elements, and
`ker_gbar_inf_gDeg_eq_bot` confines it to the imaginary bidegrees `(2m+2, 4m+4)`, the ray the
layer induction walks up. Every route to Gabber-Kac for `𝔤₄` has to kill this kernel, and
`gbar_injective_iff_topDefect_eq_zero` records that killing it is exactly the vanishing of all
the layer defects.

The kernel is genuinely inaccessible to the loop model itself: `gbar` is a homomorphism, so it can
witness that an element of `𝔤₄` is nonzero but never that one is zero. That is the content of
`gbar_defect_eq_zero`, and it is why the results here are an identification of the obstruction
rather than its removal.
-/

namespace Etingof.Problem2_16_3

section Kernel

variable {k : Type*} [Field k]

/-! ## The defects lie in the kernel -/

/-- Every layer defect is killed by `gbar`: it is central, and the loop model annihilates the
centre of `𝔤₄`. -/
theorem gbar_topDefect_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    gbar k (topDefect k m) = 0 :=
  gbar_eq_zero_of_central h3 (central_topDefect h2 h3 h5 m)

/-- The easy half of the kernel identification. -/
theorem span_topDefect_le_ker_gbar (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    Submodule.span k (Set.range (topDefect k)) ≤ LinearMap.ker (gbar k) := by
  rw [Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact LinearMap.mem_ker.2 (gbar_topDefect_eq_zero h2 h3 h5 m)

/-! ## `gbar` is injective on the span of `loopFam₄` -/

/-- **No nonzero combination of the spanning family lies in the kernel.** The images
`gbar (loopFam₄ I)` are the graded basis vectors of `𝔫₊(A₂⁽²⁾)` up to nonzero scalars, hence
linearly independent, so the span of `loopFam₄` meets `ker (gbar k)` only in `0`. -/
theorem disjoint_span_loopFam₄_ker_gbar (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    Disjoint (Submodule.span k (Set.range (loopFam₄ k))) (LinearMap.ker (gbar k)) :=
  Submodule.range_ker_disjoint (linearIndependent_gbar_comp_loopFam₄ h2 h3)

/-- A vector in the loop-family span and the realization kernel is zero. -/
theorem eq_zero_of_mem_span_loopFam₄_of_mem_ker (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    {u : g k 4} (hspan : u ∈ Submodule.span k (Set.range (loopFam₄ k)))
    (hker : u ∈ LinearMap.ker (gbar k)) : u = 0 :=
  Submodule.disjoint_def.1 (disjoint_span_loopFam₄_ker_gbar h2 h3) u hspan hker

/-! ## The kernel -/

/-- The unconditional spanning theorem, split along the two halves of `loopSet`. -/
theorem span_loopFam₄_sup_span_topDefect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) :
    Submodule.span k (Set.range (loopFam₄ k)) ⊔ Submodule.span k (Set.range (topDefect k)) = ⊤ := by
  rw [← Submodule.span_union]
  exact span_loopSet_eq_top h2 h3 h5

/-- **The kernel of the loop realization is the span of the layer defects.**

`⊇` is the centrality of the defects; for `⊆`, write `u ∈ ker (gbar k)` along the unconditional
decomposition `𝔤₄ = span (loopFam₄) + span (topDefect)` as `u = a + b`. The second summand is
already in the kernel, so `a` is too, and `a = 0` because `gbar` is injective on the span of
`loopFam₄`. -/
theorem ker_gbar_eq_span_topDefect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    LinearMap.ker (gbar k) = Submodule.span k (Set.range (topDefect k)) := by
  refine le_antisymm (fun u hu => ?_) (span_topDefect_le_ker_gbar h2 h3 h5)
  have hdec : u ∈ Submodule.span k (Set.range (loopFam₄ k))
      ⊔ Submodule.span k (Set.range (topDefect k)) := by
    rw [span_loopFam₄_sup_span_topDefect h2 h3 h5]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hdec
  have hbker : b ∈ LinearMap.ker (gbar k) := span_topDefect_le_ker_gbar h2 h3 h5 hb
  have haker : a ∈ LinearMap.ker (gbar k) := by
    rw [LinearMap.mem_ker] at hu hbker ⊢
    rw [map_add, hbker, add_zero] at hu
    exact hu
  rw [eq_zero_of_mem_span_loopFam₄_of_mem_ker h2 h3 ha haker, zero_add]
  exact hb

/-- **Injectivity of `gbar` is exactly the vanishing of all the layer defects.** This is the
precise sense in which the remaining gap in Problem 2.16.3(b) is a statement about one explicit
map: `gbar` is injective if and only if the Gabber-Kac vanishing holds. -/
theorem gbar_injective_iff_topDefect_eq_zero (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0) :
    Function.Injective (gbar k) ↔ ∀ m : ℕ, topDefect k m = 0 := by
  refine ⟨topDefect_eq_zero_of_gbar_injective h2 h3 h5, fun hgap => ?_⟩
  rw [← LinearMap.ker_eq_bot, ker_gbar_eq_span_topDefect h2 h3 h5, Submodule.span_eq_bot]
  rintro _ ⟨m, rfl⟩
  exact hgap m

/-! ## The kernel is a central ideal on the imaginary ray -/

/-- **The kernel is central.** It is spanned by the layer defects, each of which is central, so
`𝔤₄ ↠ range (gbar k)` is a central extension of the loop model. -/
theorem lie_mem_ker_gbar (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    {u : g k 4} (hu : u ∈ LinearMap.ker (gbar k)) (v : g k 4) : ⁅v, u⁆ = 0 := by
  rw [ker_gbar_eq_span_topDefect h2 h3 h5] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      exact central_topDefect h2 h3 h5 m v
  | zero => exact _root_.lie_zero v
  | add x y _ _ hx hy => rw [lie_add, hx, hy, add_zero]
  | smul c x _ hx => rw [lie_smul, hx, smul_zero]

/-- **The kernel meets only the imaginary bidegrees.** In every bidegree `p` off the ray
`(2m+2, 4m+4)`, the component `gDeg k 4 p` is at most one-dimensional and is spanned by a member
of `loopFam₄`, on which `gbar` is injective. -/
theorem ker_gbar_inf_gDeg_eq_bot (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (p : ℕ × ℕ) (hp : ∀ m : ℕ, p ≠ (2 * m + 2, 4 * m + 4)) :
    LinearMap.ker (gbar k) ⊓ gDeg k 4 p = ⊥ := by
  refine le_antisymm (fun u hu => ?_) bot_le
  obtain ⟨hker, hdeg⟩ := Submodule.mem_inf.1 hu
  refine (Submodule.mem_bot k).2 ?_
  by_cases hI : ∃ I : LoopIdx, I.bideg = p
  · obtain ⟨I, rfl⟩ := hI
    have hle := gDeg_le_span_singleton h2 h3 h5 I fun m => Ne.symm (hp m)
    have hsub : ({loopFam₄ k I} : Set (g k 4)) ⊆ Set.range (loopFam₄ k) :=
      Set.singleton_subset_iff.2 ⟨I, rfl⟩
    exact eq_zero_of_mem_span_loopFam₄_of_mem_ker h2 h3
      (Submodule.span_mono hsub (hle hdeg)) hker
  · have hbot : gDeg k 4 p = ⊥ :=
      gDeg_eq_bot h2 h3 h5 p (fun I hIp => hI ⟨I, hIp⟩) fun m hm => hp m hm.symm
    rw [hbot] at hdeg
    exact (Submodule.mem_bot k).1 hdeg

end Kernel

end Etingof.Problem2_16_3
