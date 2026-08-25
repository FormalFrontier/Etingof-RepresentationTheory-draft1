import EtingofRepresentationTheory.Chapter2.Problem2_16_3_Kernel
import Mathlib.LinearAlgebra.Dual.Lemmas


/-!
# Problem 2.16.3(b): Gabber–Kac for `𝔤₄` as a 2-cocycle computation on the loop model

`Problem2_16_3_Kernel.lean` identifies the obstruction to `𝔤₄ ≅ 𝔫₊(A₂⁽²⁾)`:

    K := ker (gbar k) = span k (range (topDefect k))

is a **central** subspace of `𝔤₄` (`lie_mem_ker_gbar`) confined to the imaginary bidegrees
`(2m+2, 4m+4)` (`ker_gbar_inf_gDeg_eq_bot`), and `gbar` is injective — equivalently every layer
defect vanishes — exactly when `K = 0` (`gbar_injective_iff_topDefect_eq_zero`).

So `0 → K → 𝔤₄ → 𝔫₊ → 0` is a graded central extension, and this file trades it for a statement
about `𝔫₊ = loopPos k` alone. The graded basis `loopBasis` of `𝔫₊` lifts, one basis vector at a
time, to the rescaled spanning family of `𝔤₄` (`gbar_loopFam₄`), giving a *linear* section

    loopSect : 𝔫₊ →ₗ[k] 𝔤₄,     gbar ∘ loopSect = id     (`gbar_loopSect`)

whose failure to be a Lie homomorphism is measured by the 2-cochain

    loopCocycle a b = ⁅loopSect a, loopSect b⁆ - loopSect ⁅a, b⁆ ∈ K.

Jacobi in `𝔤₄` plus centrality of `K` makes it a 2-cocycle (`isTwoCocycle_loopCocycle`), and the
bigrading makes it vanish on every pair of basis vectors whose bidegrees do not add up to an
imaginary bidegree (`loopCocycle_eq_zero_of_bideg`).

The pay-off is `topDefect_eq_zero_of_twoCocycle`: **if every `k`-valued 2-cocycle on `𝔫₊`
supported in the imaginary bidegrees is a coboundary, then every layer defect vanishes**, i.e.
Gabber–Kac holds for `𝔤₄`. The hypothesis mentions neither `𝔤₄`, nor the free Lie algebra, nor
the Serre relators: it is `H²(𝔫₊, k) = 0` in the imaginary bidegrees, a combinatorial statement
about a Lie algebra all of whose weight spaces are one-dimensional and whose structure constants
the project already knows (`loopVec`, `linearIndependent_loopVec`, `range_matHom₄_eq_loopPos`).

The reduction runs through the dual space rather than through a `K`-valued coboundary, which is
what lets the hypothesis be about `k`-valued cochains: for a functional `φ` on `𝔤₄`, correcting
`φ ∘ loopSect` by the coboundary of `φ ∘ loopCocycle` produces a functional `ψ` on `𝔫₊` with
`φ ⁅u, v⁆ = ψ ⁅gbar u, gbar v⁆` for *all* `u, v` in `𝔤₄` (`lie_eq_lie_loopSect`). Every defect is
a `k`-combination of brackets, and `gbar` kills it, so `φ` kills it too — for every `φ`, hence
the defect is `0`.

## Main statements

* `IsTwoCocycle`, `IsTwoCoboundary` — Lie algebra 2-cochain conditions (Mathlib has no Lie
  algebra cohomology);
* `loopSect`, `gbar_loopSect` — the graded linear section of `gbar`;
* `loopCocycle`, `isTwoCocycle_loopCocycle`, `loopCocycle_eq_zero_of_bideg` — the cocycle of the
  central extension and its support;
* `HasImaginaryWeight` — the precise support condition the successor computation has to assume;
* `topDefect_eq_zero_of_twoCocycle` — the reduction.
-/

namespace Etingof.Problem2_16_3

attribute [local instance] LieRing.ofAssociativeRing

/-! ## Lie algebra 2-cochains

Mathlib has no Lie algebra cohomology, so the two conditions are spelled out by hand for
coefficients in a module with the **trivial** action — the only case needed here, since the
kernel of `gbar` is central. -/

section Jacobi

variable {L : Type*} [LieRing L]

/-- The cyclic form of the Jacobi identity, the shape the 2-cocycle condition is written in. -/
theorem lie_cyclic (a b d : L) : ⁅⁅a, b⁆, d⁆ + ⁅⁅b, d⁆, a⁆ + ⁅⁅d, a⁆, b⁆ = 0 := by
  rw [← lie_skew ⁅a, b⁆ d, ← lie_skew ⁅b, d⁆ a, ← lie_skew ⁅d, a⁆ b, ← neg_add, ← neg_add,
    lie_jacobi, neg_zero]

end Jacobi

section Cochain

variable (k : Type*) {L M N : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- A **2-cocycle** on the Lie algebra `L` with coefficients in the trivial module `M`: a
`k`-bilinear alternating form satisfying the Chevalley–Eilenberg cocycle identity in its cyclic
shape. -/
structure IsTwoCocycle (c : L → L → M) : Prop where
  /-- The cocycle is additive in its first argument. -/
  add_left : ∀ a b d : L, c (a + b) d = c a d + c b d
  /-- The cocycle respects scalar multiplication in its first argument. -/
  smul_left : ∀ (r : k) (a b : L), c (r • a) b = r • c a b
  /-- The cocycle is additive in its second argument. -/
  add_right : ∀ a b d : L, c a (b + d) = c a b + c a d
  /-- The cocycle respects scalar multiplication in its second argument. -/
  smul_right : ∀ (r : k) (a b : L), c a (r • b) = r • c a b
  /-- The cocycle vanishes on the diagonal. -/
  self : ∀ a : L, c a a = 0
  /-- The cocycle satisfies the cyclic cocycle identity. -/
  jacobi : ∀ a b d : L, c ⁅a, b⁆ d + c ⁅b, d⁆ a + c ⁅d, a⁆ b = 0

/-- A **2-coboundary** on the Lie algebra `L` with coefficients in the trivial module `M`: the
composite of the bracket with a linear functional. -/
def IsTwoCoboundary (c : L → L → M) : Prop :=
  ∃ f : L →ₗ[k] M, ∀ a b : L, c a b = f ⁅a, b⁆

/-- Every coboundary is a cocycle: bilinearity and alternation come from the bracket, and the
cocycle identity is the image of the Jacobi identity. -/
theorem IsTwoCoboundary.isTwoCocycle {c : L → L → M} (h : IsTwoCoboundary k c) :
    IsTwoCocycle k c := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun a b d => ?_, fun r a b => ?_, fun a b d => ?_, fun r a b => ?_, fun a => ?_,
    fun a b d => ?_⟩
  · rw [hf, hf, hf, add_lie, map_add]
  · rw [hf, hf, smul_lie, map_smul]
  · rw [hf, hf, hf, lie_add, map_add]
  · rw [hf, hf, lie_smul, map_smul]
  · rw [hf, lie_self, map_zero]
  · rw [hf, hf, hf, ← map_add, ← map_add, lie_cyclic, map_zero]

/-- Pushing a cocycle forward along a linear map of coefficients. -/
theorem IsTwoCocycle.map {c : L → L → M} (hc : IsTwoCocycle k c) (φ : M →ₗ[k] N) :
    IsTwoCocycle k fun a b => φ (c a b) where
  add_left a b d := by rw [hc.add_left, map_add]
  smul_left r a b := by rw [hc.smul_left, map_smul]
  add_right a b d := by rw [hc.add_right, map_add]
  smul_right r a b := by rw [hc.smul_right, map_smul]
  self a := by rw [hc.self, map_zero]
  jacobi a b d := by rw [← map_add, ← map_add, hc.jacobi, map_zero]

end Cochain

/-! ## The bigrading of `𝔫₊` pulled back along `gbar` -/

section Grading

variable {k : Type*} [Field k]

/-- The bidegree carried by the graded basis vector `loopFam k J` of `𝔫₊`, pulled back from the
bigrading of `𝔤₄`: `gbar` sends the bihomogeneous element `loopFam₄ k I ∈ gDeg k 4 I.bideg` to a
nonzero multiple of `loopVec k (loopRev I)` (`gbar_loopFam₄`), so `loopVec k J` carries the
bidegree of `loopFam₄ k (loopRev J)`.

Note this is *not* `LoopIdx.bideg`: the `ad(ȳ)`-string enumerates each graded piece of `𝔤₄` in
the order opposite to `gone`/`gzero`, so the two differ by the involution `loopRev`. -/
def LoopIdx.lbideg (J : LoopIdx) : ℕ × ℕ := (loopRev J).bideg

/-- The loop bidegree formula for `lbideg_base`. -/
@[simp] theorem lbideg_base : LoopIdx.base.lbideg = (0, 1) := rfl

/-- The loop bidegree formula for `lbideg_odd`. -/
@[simp] theorem lbideg_odd (m : ℕ) (i : Fin 5) :
    (LoopIdx.odd m i).lbideg = (2 * m + 1, 4 * m + (i.rev : ℕ)) := rfl

/-- The loop bidegree formula for `lbideg_even`. -/
@[simp] theorem lbideg_even (m : ℕ) (i : Fin 3) :
    (LoopIdx.even m i).lbideg = (2 * m + 2, 4 * m + 3 + (i.rev : ℕ)) := rfl

/-- The loop bidegree formula for `lbideg_loopRev`. -/
theorem lbideg_loopRev (I : LoopIdx) : (loopRev I).lbideg = I.bideg := by
  rw [LoopIdx.lbideg, loopRev_involutive I]

/-- Distinct graded basis vectors of `𝔫₊` have distinct pulled-back bidegrees. -/
theorem lbideg_injective : Function.Injective LoopIdx.lbideg :=
  LoopIdx.bideg_injective.comp loopRev_injective

/-- The `p`-bidegree component of `𝔫₊`, in the bigrading pulled back from `𝔤₄` along `gbar`. At
most one graded basis vector carries any given bidegree (`lbideg_injective`), so this is at most
one-dimensional. -/
noncomputable def lDeg (k : Type*) [Field k] (p : ℕ × ℕ) : Submodule k (loopPos k) :=
  Submodule.span k {v | ∃ J : LoopIdx, J.lbideg = p ∧ loopFam k J = v}

/-- A loop-family vector belongs to its degree filtration. -/
theorem loopFam_mem_lDeg (J : LoopIdx) : loopFam k J ∈ lDeg k J.lbideg :=
  Submodule.subset_span ⟨J, rfl, rfl⟩

end Grading

/-! ## The graded linear section of `gbar` -/

section Section

variable {k : Type*} [Field k]

/-- **The graded linear section of `gbar`.** It sends the graded basis vector `loopFam k J` of
`𝔫₊` back to the rescaled member `(loopCoef k (loopRev J))⁻¹ • loopFam₄ k (loopRev J)` of the
spanning family of `𝔤₄`, which `gbar_loopFam₄` returns to `loopVec k J`. -/
noncomputable def loopSect (h2 : (2 : k) ≠ 0) : loopPos k →ₗ[k] g k 4 :=
  (loopBasis k h2).constr k fun J => (loopCoef k (loopRev J))⁻¹ • loopFam₄ k (loopRev J)

/-- The loop section sends a loop-family vector to its chosen lift. -/
theorem loopSect_loopFam (h2 : (2 : k) ≠ 0) (J : LoopIdx) :
    loopSect h2 (loopFam k J) = (loopCoef k (loopRev J))⁻¹ • loopFam₄ k (loopRev J) := by
  rw [loopSect, ← loopBasis_apply k h2 J, Module.Basis.constr_basis]

/-- The section is graded: it carries the basis vector of pulled-back bidegree `p` into the
bidegree-`p` component of `𝔤₄`. -/
theorem loopSect_mem_gDeg (h2 : (2 : k) ≠ 0) (J : LoopIdx) :
    loopSect h2 (loopFam k J) ∈ gDeg k 4 J.lbideg := by
  rw [loopSect_loopFam]
  exact Submodule.smul_mem _ _ (loopFam₄_mem_gDeg k (loopRev J))

/-- The loop section respects the degree filtration. -/
theorem loopSect_lDeg_le (h2 : (2 : k) ≠ 0) (p : ℕ × ℕ) {v : loopPos k} (hv : v ∈ lDeg k p) :
    loopSect h2 v ∈ gDeg k 4 p := by
  have key : ∀ w ∈ lDeg k p, loopSect h2 w ∈ gDeg k 4 p := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨J, hJ, rfl⟩ := hz
        exact hJ ▸ loopSect_mem_gDeg h2 J
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  exact key v hv

/-- **`loopSect` is a section of `gbar`.** -/
theorem gbar_loopSect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (v : loopPos k) :
    gbar k (loopSect h2 v) = (v : Matrix (Fin 3) (Fin 3) (Polynomial k)) := by
  have key : (gbar k).comp (loopSect h2) = (loopPos k).toSubmodule.subtype := by
    refine (loopBasis k h2).ext fun J => ?_
    rw [LinearMap.comp_apply, loopBasis_apply, loopSect_loopFam, map_smul, gbar_loopFam₄,
      loopRev_involutive J, smul_smul, inv_mul_cancel₀ (loopCoef_ne_zero h2 h3 _), one_smul]
    rfl
  exact congrArg (fun f : loopPos k →ₗ[k] Matrix (Fin 3) (Fin 3) (Polynomial k) => f v) key

/-- `gbar` viewed as a map into `𝔫₊`, using `gbar_mem_loopPos`. -/
noncomputable def gbarL (k : Type*) [Field k] : g k 4 →ₗ[k] loopPos k where
  toFun u := ⟨gbar k u, gbar_mem_loopPos u⟩
  map_add' u v := Subtype.ext (map_add (gbar k) u v)
  map_smul' r u := Subtype.ext (map_smul (gbar k) r u)

/-- The linear realization agrees pointwise with the Lie realization. -/
@[simp] theorem coe_gbarL (u : g k 4) :
    (gbarL k u : Matrix (Fin 3) (Fin 3) (Polynomial k)) = gbar k u := rfl

/-- The linear realization sends brackets to brackets modulo the defect. -/
theorem gbarL_lie (u v : g k 4) : gbarL k ⁅u, v⁆ = ⁅gbarL k u, gbarL k v⁆ :=
  Subtype.ext <| by rw [coe_gbarL, LieSubalgebra.coe_bracket, coe_gbarL, coe_gbarL, gbar_lie]

/-- The linear realization is a left inverse to the loop section. -/
theorem gbarL_loopSect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (v : loopPos k) :
    gbarL k (loopSect h2 v) = v :=
  Subtype.ext (gbar_loopSect h2 h3 v)

/-- The linear realization annihilates every top defect. -/
theorem gbarL_topDefect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (m : ℕ) :
    gbarL k (topDefect k m) = 0 :=
  Subtype.ext <| by rw [coe_gbarL, gbar_topDefect_eq_zero h2 h3 h5]; rfl

/-- `gbar` is graded: it carries the bidegree-`p` component of `𝔤₄` into the bidegree-`p`
component of `𝔫₊`. The bidegree-`p` component of `𝔤₄` is spanned by the members of the
unconditional spanning set that have bidegree `p` (`gDeg_le_span`); `gbar` carries `loopFam₄ k I`
to a multiple of the basis vector of pulled-back bidegree `I.bideg` and kills every defect. -/
theorem gbarL_gDeg_le (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) (p : ℕ × ℕ)
    {u : g k 4} (hu : u ∈ gDeg k 4 p) : gbarL k u ∈ lDeg k p := by
  set T : Set (g k 4) := {w | (∃ I : LoopIdx, I.bideg = p ∧ loopFam₄ k I = w) ∨
    ∃ m : ℕ, (2 * m + 2, 4 * m + 4) = p ∧ topDefect k m = w} with hT
  have hle : gDeg k 4 p ≤ Submodule.span k T :=
    gDeg_le_span h2 h3 h5 p T (fun I hI => Submodule.subset_span (Or.inl ⟨I, hI, rfl⟩))
      (fun m hm => Submodule.subset_span (Or.inr ⟨m, hm, rfl⟩))
  have key : ∀ w ∈ Submodule.span k T, gbarL k w ∈ lDeg k p := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
        rcases hz with ⟨I, hI, rfl⟩ | ⟨m, hm, rfl⟩
        · have himg : gbarL k (loopFam₄ k I) = loopCoef k I • loopFam k (loopRev I) :=
            Subtype.ext <| by rw [coe_gbarL, gbar_loopFam₄]; rfl
          rw [himg]
          refine Submodule.smul_mem _ _ ?_
          exact (lbideg_loopRev I).trans hI ▸ loopFam_mem_lDeg (loopRev I)
        · rw [gbarL_topDefect h2 h3 h5]
          exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
  exact key u (hle hu)

/-- The bracket of two graded basis vectors of `𝔫₊` is homogeneous of the sum of their
pulled-back bidegrees: lift both to `𝔤₄`, bracket there, and push back down. -/
theorem lie_loopFam_mem_lDeg (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I J : LoopIdx) : ⁅loopFam k I, loopFam k J⁆ ∈ lDeg k (I.lbideg + J.lbideg) := by
  have hrw : ⁅loopFam k I, loopFam k J⁆
      = gbarL k ⁅loopSect h2 (loopFam k I), loopSect h2 (loopFam k J)⁆ := by
    rw [gbarL_lie, gbarL_loopSect h2 h3, gbarL_loopSect h2 h3]
  rw [hrw]
  exact gbarL_gDeg_le h2 h3 h5 _
    (lie_mem_gDeg k (loopSect_mem_gDeg h2 I) (loopSect_mem_gDeg h2 J))

end Section

/-! ## The cocycle of the central extension -/

section Cocycle

variable {k : Type*} [Field k]

/-- **The 2-cocycle of the graded central extension `0 → ker gbar → 𝔤₄ → 𝔫₊ → 0`**, measured
against the linear section `loopSect`: it is the failure of the section to be a Lie
homomorphism. -/
noncomputable def loopCocycle (h2 : (2 : k) ≠ 0) (a b : loopPos k) : g k 4 :=
  ⁅loopSect h2 a, loopSect h2 b⁆ - loopSect h2 ⁅a, b⁆

/-- The section defect of a bracket is the top defect. -/
theorem lie_loopSect (h2 : (2 : k) ≠ 0) (a b : loopPos k) :
    ⁅loopSect h2 a, loopSect h2 b⁆ = loopSect h2 ⁅a, b⁆ + loopCocycle h2 a b := by
  rw [loopCocycle]; abel

/-- The cocycle takes values in the kernel: `gbar` is a Lie homomorphism and `loopSect` is a
section of it. -/
theorem loopCocycle_mem_ker (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (a b : loopPos k) :
    loopCocycle h2 a b ∈ LinearMap.ker (gbar k) := by
  rw [LinearMap.mem_ker, loopCocycle, map_sub, gbar_lie, gbar_loopSect h2 h3,
    gbar_loopSect h2 h3, gbar_loopSect h2 h3, LieSubalgebra.coe_bracket, sub_self]

/-- Kernel elements are central on the left as well as on the right. -/
theorem lie_eq_zero_of_mem_ker_gbar (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    {w : g k 4} (hw : w ∈ LinearMap.ker (gbar k)) (u : g k 4) : ⁅w, u⁆ = 0 := by
  have h := lie_mem_ker_gbar h2 h3 h5 hw u
  rw [← lie_skew u w] at h
  exact neg_eq_zero.1 h

/-- **The cocycle identity.** Jacobi in `𝔤₄`, with the correction terms `⁅loopCocycle a b, _⁆`
killed by centrality of the kernel. -/
theorem isTwoCocycle_loopCocycle (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0) :
    IsTwoCocycle k (loopCocycle h2) where
  add_left a b d := by
    simp only [loopCocycle, map_add, add_lie]
    abel
  smul_left r a b := by
    simp only [loopCocycle, map_smul, smul_lie, smul_sub]
  add_right a b d := by
    simp only [loopCocycle, map_add, lie_add]
    abel
  smul_right r a b := by
    simp only [loopCocycle, map_smul, lie_smul, smul_sub]
  self a := by
    rw [loopCocycle, lie_self, lie_self, map_zero, sub_self]
  jacobi a b d := by
    have key : ∀ x y z : loopPos k, ⁅⁅loopSect h2 x, loopSect h2 y⁆, loopSect h2 z⁆
        = loopSect h2 ⁅⁅x, y⁆, z⁆ + loopCocycle h2 ⁅x, y⁆ z := by
      intro x y z
      rw [lie_loopSect h2 x y, add_lie,
        lie_eq_zero_of_mem_ker_gbar h2 h3 h5 (loopCocycle_mem_ker h2 h3 x y) _, add_zero,
        lie_loopSect h2 ⁅x, y⁆ z]
    have h0 := lie_cyclic (loopSect h2 a) (loopSect h2 b) (loopSect h2 d)
    rw [key a b d, key b d a, key d a b] at h0
    have hL : loopSect h2 ⁅⁅a, b⁆, d⁆ + loopSect h2 ⁅⁅b, d⁆, a⁆ + loopSect h2 ⁅⁅d, a⁆, b⁆ = 0 := by
      rw [← map_add, ← map_add, lie_cyclic, map_zero]
    have e : loopCocycle h2 ⁅a, b⁆ d + loopCocycle h2 ⁅b, d⁆ a + loopCocycle h2 ⁅d, a⁆ b
        = ((loopSect h2 ⁅⁅a, b⁆, d⁆ + loopCocycle h2 ⁅a, b⁆ d)
            + (loopSect h2 ⁅⁅b, d⁆, a⁆ + loopCocycle h2 ⁅b, d⁆ a)
            + (loopSect h2 ⁅⁅d, a⁆, b⁆ + loopCocycle h2 ⁅d, a⁆ b))
          - (loopSect h2 ⁅⁅a, b⁆, d⁆ + loopSect h2 ⁅⁅b, d⁆, a⁆ + loopSect h2 ⁅⁅d, a⁆, b⁆) := by
      abel
    rw [e, h0, hL, sub_zero]

/-- **The cocycle is supported in the imaginary bidegrees.** On a pair of graded basis vectors it
is bihomogeneous of the sum of their bidegrees (both terms of `loopCocycle` are), and it lies in
the kernel; off the imaginary ray those two constraints are incompatible
(`ker_gbar_inf_gDeg_eq_bot`). -/
theorem loopCocycle_eq_zero_of_bideg (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (I J : LoopIdx) (hIJ : ∀ m : ℕ, I.lbideg + J.lbideg ≠ (2 * m + 2, 4 * m + 4)) :
    loopCocycle h2 (loopFam k I) (loopFam k J) = 0 := by
  have hker := loopCocycle_mem_ker h2 h3 (loopFam k I) (loopFam k J)
  have hdeg : loopCocycle h2 (loopFam k I) (loopFam k J) ∈ gDeg k 4 (I.lbideg + J.lbideg) := by
    refine sub_mem (lie_mem_gDeg k (loopSect_mem_gDeg h2 I) (loopSect_mem_gDeg h2 J)) ?_
    exact loopSect_lDeg_le h2 _ (lie_loopFam_mem_lDeg h2 h3 h5 I J)
  have hbot := ker_gbar_inf_gDeg_eq_bot h2 h3 h5 (I.lbideg + J.lbideg) hIJ
  rw [Submodule.eq_bot_iff] at hbot
  exact hbot _ (Submodule.mem_inf.2 ⟨hker, hdeg⟩)

/-- **The support condition on 2-cochains of `𝔫₊` that the reduction needs.** A cochain has
*imaginary weight* if it vanishes on every pair of graded basis vectors whose pulled-back
bidegrees do not add up to an imaginary bidegree `(2m+2, 4m+4)`.

This is the precise form the successor computation has to assume: `H²(𝔫₊, k)` is `2`-dimensional
in total, carried by the bidegrees `(2,1)` and `(1,5)` of the two Serre relators, and neither is
imaginary, so a cochain of imaginary weight is expected to be a coboundary. -/
def HasImaginaryWeight (c : loopPos k → loopPos k → k) : Prop :=
  ∀ I J : LoopIdx, (∀ m : ℕ, I.lbideg + J.lbideg ≠ (2 * m + 2, 4 * m + 4)) →
    c (loopFam k I) (loopFam k J) = 0

/-- **The imaginary-weight restriction is compatible with the classes `H²(𝔫₊, k)` really has.**
The two Serre relators `ad(x)²y` and `ad(y)⁵x` have bidegrees `(2, 1)` and `(1, 5)`, and neither
is imaginary; so restricting to cochains of imaginary weight removes exactly the two bidegrees in
which `H²(𝔫₊, k)` is nonzero. -/
theorem serre_bideg_not_imaginary :
    (∀ m : ℕ, ((2, 1) : ℕ × ℕ) ≠ (2 * m + 2, 4 * m + 4)) ∧
      ∀ m : ℕ, ((1, 5) : ℕ × ℕ) ≠ (2 * m + 2, 4 * m + 4) := by
  refine ⟨fun m h => ?_, fun m h => ?_⟩ <;> rw [Prod.mk.injEq] at h <;> omega

/-- **`HasImaginaryWeight` is a genuine restriction**, not a vacuous one: the pair of basis
vectors `(loopFam base, loopFam (odd 0 0))` carries bidegree `(0, 1) + (1, 4) = (1, 5)`, which is
not imaginary, so every cochain of imaginary weight kills it. -/
theorem eq_zero_of_hasImaginaryWeight_base_odd {c : loopPos k → loopPos k → k}
    (hc : HasImaginaryWeight c) : c (loopFam k .base) (loopFam k (.odd 0 0)) = 0 := by
  refine hc _ _ fun m h => ?_
  rw [lbideg_base, lbideg_odd, Prod.mk_add_mk, Prod.mk.injEq] at h
  have hrev : ((0 : Fin 5).rev : ℕ) = 4 := rfl
  rw [hrev] at h
  omega

/-- Imaginary weight is preserved by precomposition with the realization. -/
theorem hasImaginaryWeight_comp (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (φ : g k 4 →ₗ[k] k) : HasImaginaryWeight fun a b => φ (loopCocycle h2 a b) := by
  intro I J hIJ
  change φ (loopCocycle h2 (loopFam k I) (loopFam k J)) = 0
  rw [loopCocycle_eq_zero_of_bideg h2 h3 h5 I J hIJ, map_zero]

end Cocycle

/-! ## The reduction -/

section Reduction

variable {k : Type*} [Field k]

/-- **Every bracket in `𝔤₄` is a bracket of section values.** Both arguments differ from their
sections by kernel elements, which are central. This is the statement that `𝔤₄` is *generated as
a Lie algebra* by the image of `loopSect`, in the strong bracket-by-bracket form. -/
theorem lie_eq_lie_loopSect (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (u v : g k 4) : ⁅u, v⁆ = ⁅loopSect h2 (gbarL k u), loopSect h2 (gbarL k v)⁆ := by
  have hu : u - loopSect h2 (gbarL k u) ∈ LinearMap.ker (gbar k) := by
    rw [LinearMap.mem_ker, map_sub, gbar_loopSect h2 h3, coe_gbarL, sub_self]
  have hv : v - loopSect h2 (gbarL k v) ∈ LinearMap.ker (gbar k) := by
    rw [LinearMap.mem_ker, map_sub, gbar_loopSect h2 h3, coe_gbarL, sub_self]
  have e : ⁅u, v⁆ - ⁅loopSect h2 (gbarL k u), loopSect h2 (gbarL k v)⁆
      = ⁅u - loopSect h2 (gbarL k u), v⁆
        + ⁅loopSect h2 (gbarL k u), v - loopSect h2 (gbarL k v)⁆ := by
    rw [sub_lie, lie_sub]; abel
  rw [← sub_eq_zero, e, lie_eq_zero_of_mem_ker_gbar h2 h3 h5 hu v,
    lie_mem_ker_gbar h2 h3 h5 hv _, add_zero]

/-- **Gabber–Kac for `𝔤₄`, reduced to a 2-cocycle computation on the loop model.**

If every `k`-valued 2-cocycle on `𝔫₊ = loopPos k` of imaginary weight is a coboundary, then every
layer defect of `𝔤₄` vanishes — equivalently `gbar` is injective
(`gbar_injective_iff_topDefect_eq_zero`) and `𝔤₄ ≅ 𝔫₊(A₂⁽²⁾)`.

The hypothesis is a statement about `𝔫₊` alone: no `𝔤₄`, no free Lie algebra, no Serre relators.

Proof. It is enough to kill `topDefect k m` against every functional `φ` on `𝔤₄`. Apply the
hypothesis to the scalar cocycle `φ ∘ loopCocycle`, which has imaginary weight by
`hasImaginaryWeight_comp`, and let `f` be the resulting coboundary datum. Then
`ψ = φ ∘ loopSect + f` satisfies `φ ⁅u, v⁆ = ψ ⁅gbar u, gbar v⁆` for all `u, v` in `𝔤₄`, because
every bracket in `𝔤₄` is a bracket of section values (`lie_eq_lie_loopSect`) and the cocycle
correction is exactly what `f` absorbs. The defect is a `k`-combination of two brackets and
`gbar` kills it, so `φ (topDefect k m) = ψ (gbar (topDefect k m)) = 0`. -/
theorem topDefect_eq_zero_of_twoCocycle (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (H : ∀ c : loopPos k → loopPos k → k,
      IsTwoCocycle k c → HasImaginaryWeight c → IsTwoCoboundary k c)
    (m : ℕ) : topDefect k m = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k (topDefect k m)]
  intro φ
  obtain ⟨f, hf⟩ := H (fun a b => φ (loopCocycle h2 a b))
    ((isTwoCocycle_loopCocycle h2 h3 h5).map k φ) (hasImaginaryWeight_comp h2 h3 h5 φ)
  have hf' : ∀ a b : loopPos k, φ (loopCocycle h2 a b) = f ⁅a, b⁆ := hf
  set ψ : loopPos k →ₗ[k] k := φ.comp (loopSect h2) + f with hψ
  have hbr : ∀ u v : g k 4, φ ⁅u, v⁆ = ψ ⁅gbarL k u, gbarL k v⁆ := by
    intro u v
    rw [lie_eq_lie_loopSect h2 h3 h5 u v, lie_loopSect h2 (gbarL k u) (gbarL k v), map_add,
      hf' (gbarL k u) (gbarL k v), hψ]
    simp [LinearMap.comp_apply]
  have hz : ⁅gbarL k (aElt k 4 4), gbarL k (topOdd k m)⁆
      - (2 : k) • ⁅gbarL k (yb k 4), gbarL k (evenTower k m)⁆ = 0 := by
    rw [← gbarL_lie, ← gbarL_lie, ← map_smul, ← map_sub, ← dY_one, ← topDefect]
    exact gbarL_topDefect h2 h3 h5 m
  rw [topDefect, dY_one, map_sub, map_smul, hbr, hbr, ← map_smul ψ, ← map_sub ψ, hz, map_zero]

/-- **The reduction, packaged as injectivity of the loop realization.** Under the cocycle
hypothesis `gbar` is injective, so `𝔤₄` really is the twisted loop realization `𝔫₊(A₂⁽²⁾)` — this
is Problem 2.16.3(b) modulo the `𝔫₊`-internal computation left to the successor issue. -/
theorem gbar_injective_of_twoCocycle (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (H : ∀ c : loopPos k → loopPos k → k,
      IsTwoCocycle k c → HasImaginaryWeight c → IsTwoCoboundary k c) :
    Function.Injective (gbar k) :=
  (gbar_injective_iff_topDefect_eq_zero h2 h3 h5).2
    (topDefect_eq_zero_of_twoCocycle h2 h3 h5 H)

/-- The same conclusion at the level of the spanning family: under the cocycle hypothesis the
`LoopIdx`-indexed family `loopFam₄` spans `𝔤₄`, matching the graded dimensions
`1, 5, 3, 5, 3, …` of `𝔫₊(A₂⁽²⁾)`. -/
theorem span_range_loopFam₄_eq_top_of_twoCocycle (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (h5 : (5 : k) ≠ 0)
    (H : ∀ c : loopPos k → loopPos k → k,
      IsTwoCocycle k c → HasImaginaryWeight c → IsTwoCoboundary k c) :
    Submodule.span k (Set.range (loopFam₄ k)) = ⊤ :=
  span_range_loopFam₄_eq_top_of_gbar_injective h2 h3 h5
    (gbar_injective_of_twoCocycle h2 h3 h5 H)

end Reduction

end Etingof.Problem2_16_3

-- The source-numbered exercise namespace and established API contain intentional underscores.
attribute [nolint defsWithUnderscore]
  Etingof.Problem2_16_3.IsTwoCoboundary
  Etingof.Problem2_16_3.LoopIdx.lbideg
  Etingof.Problem2_16_3.lDeg
  Etingof.Problem2_16_3.loopSect
  Etingof.Problem2_16_3.gbarL
  Etingof.Problem2_16_3.loopCocycle
  Etingof.Problem2_16_3.HasImaginaryWeight
