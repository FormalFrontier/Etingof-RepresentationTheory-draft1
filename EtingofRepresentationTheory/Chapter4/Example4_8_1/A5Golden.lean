import EtingofRepresentationTheory.Chapter4.Example4_8_1.A5Lambda2

/-!
# Example 4.8.1 — `A₅`: the golden-ratio `ℂ³₊`, `ℂ³₋` and the five irreducibles

Split out of `Example4_8_1.lean` for CI memory (issue #5852); see there for the umbrella.
Contains the central class-sum `z` on `Λ²(ℂ⁴)`, its minimal polynomial `z² = 20z + 400`,
the two golden-ratio eigenspace subrepresentations, their characters and simplicity, and
the assembly of the five pairwise non-isomorphic irreducibles `irrepA5`.
-/

namespace Etingof.Example4_8_1

open Q5

namespace A5

open Equiv CategoryTheory
open scoped TensorProduct

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
/-! #### Phase B: the central 5-cycle class-sum splits `Λ²(ℂ⁴)`

The 5-cycle class-sum acts on `Λ²(ℂ⁴)` as a central element `z = Σ_{g∈A₅} ρ(g·r·g⁻¹)`
(`r` a 5-cycle, the sum running over all of `A₅`, which makes centrality immediate).  Its
minimal polynomial is `z² − 20·z − 400 = 0`, with the two roots `μ⁺ = 10 + 10√5 = 20φ` and
`μ⁻ = 10 − 10√5 = 20φ'` (`φ = (1+√5)/2`).  The two eigenspaces are the two genuine
3-dimensional icosahedral subrepresentations `ℂ³₊`, `ℂ³₋`. -/

/-- The 5-cycle class representative whose `A₅`-class-sum is the central element splitting
`Λ²(ℂ⁴)`. -/
def r5 : G := classRepA5 3

/-- The central element `z = Σ_{g∈A₅} ρ(g·r·g⁻¹)` on `Λ²(ℂ⁴)`, where `r` is a 5-cycle.
Summing over **all** of `A₅` (rather than over the conjugacy class) makes the centrality
proof a one-line reindexing.  Equal to `5·(class-sum)` since the centralizer of a 5-cycle
has order 5. -/
def zEnd : Module.End ℂ ↥lam2Sub.toSubmodule :=
  ∑ g : G, lam2Sub.toRepresentation (g * r5 * g⁻¹)

/-- **Centrality of `z`.** `z` commutes with every `ρ(h)`, by the reindexing
`h·z·h⁻¹ = Σ_g ρ((hg)·r·(hg)⁻¹) = z`. -/
lemma zEnd_central (h : G) : Commute (lam2Sub.toRepresentation h) zEnd := by
  show lam2Sub.toRepresentation h * zEnd = zEnd * lam2Sub.toRepresentation h
  rw [zEnd, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g => lam2Sub.toRepresentation h * lam2Sub.toRepresentation (g * r5 * g⁻¹))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- **Trace of `z` on `Λ²(ℂ⁴)` is `60`.**  Each summand `ρ(g·r·g⁻¹)` is a conjugate of the
5-cycle `r`, on which `χ_{Λ²} = 1` (`lam2_character 3`); the constant `1` summed over the 60
elements of `A₅` gives `60`.  Equivalently `tr z = 3·μ⁺ + 3·μ⁻ = 60`, one of the two trace
identities pinning the golden-ratio eigenvalues `μ± = 10 ± 10√5` (the second being `tr z² = 3600`,
giving `μ⁺ + μ⁻ = 20`, `μ⁺·μ⁻ = −400`, i.e. the minimal polynomial `z² − 20z − 400`). -/
lemma zEnd_trace : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) zEnd = 60 := by
  have hchar : ∀ x : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (lam2Sub.toRepresentation x)
        = lam2.character x := fun x => rfl
  have hterm : ∀ g : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (lam2Sub.toRepresentation (g * r5 * g⁻¹)) = 1 := by
    intro g
    rw [hchar, FDRep.char_conj, r5]
    simpa using lam2_character 3
  rw [zEnd, map_sum, Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : (Fintype.card G : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_G]; norm_num
  rw [hcard]

/-- The same central element realised as an **ambient** operator on `W4 ⊗ W4` (the sum of
`(ρ_V ⊗ ρ_V)(g·r·g⁻¹)` over all `g`).  It restricts to `zEnd` on `range asym`, commutes both
with the diagonal action and with the antisymmetriser `asym`, and preserves `range asym`.
Working ambiently keeps the carrier one nesting level deep (a submodule of `W4 ⊗ W4`, like
`lam2Sub`), which avoids the subtype-of-subtype typeclass diamond and sets up the minimal
polynomial computation. -/
def Zamb : Module.End ℂ (W4 ⊗[ℂ] W4) :=
  ∑ g : G, (rhoV.tprod rhoV) (g * r5 * g⁻¹)

/-- **Centrality of the ambient `Z`.** `Z` commutes with every `(ρ_V ⊗ ρ_V)(h)`, by the
reindexing `h·Z·h⁻¹ = Σ_g ρ((hg)·r·(hg)⁻¹) = Z`. -/
lemma Zamb_comm (h : G) : Commute ((rhoV.tprod rhoV) h) Zamb := by
  show (rhoV.tprod rhoV) h * Zamb = Zamb * (rhoV.tprod rhoV) h
  rw [Zamb, Finset.mul_sum, Finset.sum_mul,
    ← Equiv.sum_comp (Equiv.mulLeft h⁻¹)
      (fun g => (rhoV.tprod rhoV) h * (rhoV.tprod rhoV) (g * r5 * g⁻¹))]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [← map_mul, ← map_mul]
  congr 1
  group

/-- `Z` commutes with the antisymmetriser `asym` (each summand does, by `asym_comm`). -/
lemma Zamb_comm_asym : Commute asym Zamb := by
  show asym * Zamb = Zamb * asym
  rw [Zamb, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun g _ => asym_comm (g * r5 * g⁻¹)

/-- `Z` preserves the antisymmetric subspace `range asym = Λ²(ℂ⁴)`. -/
lemma Zamb_mapsTo : ∀ v ∈ lam2Sub.toSubmodule, Zamb v ∈ lam2Sub.toSubmodule := by
  intro v hv
  rw [Zamb, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun g _ => lam2Sub.apply_mem_toSubmodule (g * r5 * g⁻¹) hv

/-- **`z` is the restriction of the ambient `Z` to `Λ²(ℂ⁴)`.**  Both are the same 60-term group
sum `Σ_g ρ(g·r·g⁻¹)`: `zEnd` restricts each summand to `lam2Sub` (Phase B, where the traces are
computed), while `Zamb` keeps it ambient on `W4 ⊗ W4` (Phase C, where the eigenspaces defining
`ℂ³₊`, `ℂ³₋` live).  Coercing `zEnd v` back to `W4 ⊗ W4` recovers `Z` applied to the coercion —
the identity transporting the trace / minimal-polynomial data of `z` onto the `Z`-eigenspaces. -/
lemma zEnd_coe (v : ↥lam2Sub.toSubmodule) :
    ((zEnd v : ↥lam2Sub.toSubmodule) : W4 ⊗[ℂ] W4) = Zamb (v : W4 ⊗[ℂ] W4) := by
  simp only [zEnd, Zamb, LinearMap.sum_apply, Submodule.coe_sum]
  rfl

/-- **The `μ`-eigenspaces of `z` and of `Z` correspond under `Λ²(ℂ⁴) ↪ W4 ⊗ W4`.**  A vector of
`Λ²(ℂ⁴)` is a `μ`-eigenvector of the intrinsic `zEnd` iff its ambient image is a `μ`-eigenvector
of `Zamb`.  Immediate from `zEnd_coe`. -/
lemma zEnd_eigenspace_iff (μ : ℂ) (v : ↥lam2Sub.toSubmodule) :
    v ∈ Module.End.eigenspace zEnd μ
      ↔ (v : W4 ⊗[ℂ] W4) ∈ Module.End.eigenspace Zamb μ := by
  rw [Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Subtype.ext_iff, zEnd_coe,
    Submodule.coe_smul]

/-! #### The two eigenvalues and the genuine eigenspace subrepresentations -/

/-- The eigenvalue `μ⁺ = 10 + 10√5 = 20·φ` of `z` on `ℂ³₊`. -/
noncomputable def muPlus : ℂ := 10 + 10 * (Real.sqrt 5 : ℂ)

/-- The eigenvalue `μ⁻ = 10 − 10√5 = 20·φ'` of `z` on `ℂ³₋`. -/
noncomputable def muMinus : ℂ := 10 - 10 * (Real.sqrt 5 : ℂ)

/-- `ℂ³₊` as a subrepresentation of `repC4 ⊗ repC4`: the antisymmetric tensors that also lie in
the `μ⁺`-eigenspace of the central `Z`.  Invariance of the eigenspace factor is
`mapsTo_genEigenspace_of_comm` applied to the centrality of `Z`; invariance of `range asym` is
Phase A's `lam2Sub.apply_mem_toSubmodule`. -/
def repC3plusSub : Subrepresentation (rhoV.tprod rhoV) where
  toSubmodule := lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muPlus
  apply_mem_toSubmodule h v hv := by
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨lam2Sub.apply_mem_toSubmodule h hv.1,
      Module.End.mapsTo_genEigenspace_of_comm (Zamb_comm h).symm muPlus 1 hv.2⟩

/-- `ℂ³₋` as a subrepresentation of `repC4 ⊗ repC4`: the antisymmetric tensors in the
`μ⁻`-eigenspace of `Z`. -/
def repC3minusSub : Subrepresentation (rhoV.tprod rhoV) where
  toSubmodule := lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muMinus
  apply_mem_toSubmodule h v hv := by
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨lam2Sub.apply_mem_toSubmodule h hv.1,
      Module.End.mapsTo_genEigenspace_of_comm (Zamb_comm h).symm muMinus 1 hv.2⟩

/-- `ℂ³₊`, the first genuine 3-dimensional icosahedral representation of `A₅`. -/
def repC3plus : FDRep ℂ G := FDRep.of repC3plusSub.toRepresentation

/-- `ℂ³₋`, the second genuine 3-dimensional icosahedral representation of `A₅`. -/
def repC3minus : FDRep ℂ G := FDRep.of repC3minusSub.toRepresentation

/-- **The carrier of `ℂ³₊` is the image of the `μ⁺`-eigenspace of the intrinsic `z`.**  The
subrepresentation `ℂ³₊ = Λ²(ℂ⁴) ⊓ ker(Z − μ⁺)` is exactly the `μ⁺`-eigenspace of `zEnd` inside
`Λ²(ℂ⁴)`, pushed forward along the inclusion `Λ²(ℂ⁴) ↪ W4 ⊗ W4` (`zEnd_eigenspace_iff`). -/
lemma repC3plusSub_toSubmodule_eq :
    repC3plusSub.toSubmodule
      = (Module.End.eigenspace zEnd muPlus).map lam2Sub.toSubmodule.subtype := by
  ext x
  rw [show repC3plusSub.toSubmodule
      = lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muPlus from rfl,
    Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hx, hxe⟩
    exact ⟨⟨x, hx⟩, (zEnd_eigenspace_iff muPlus ⟨x, hx⟩).mpr hxe, rfl⟩
  · rintro ⟨⟨y, hy⟩, hye, rfl⟩
    exact ⟨hy, (zEnd_eigenspace_iff muPlus ⟨y, hy⟩).mp hye⟩

/-- **The carrier of `ℂ³₋` is the image of the `μ⁻`-eigenspace of the intrinsic `z`.** -/
lemma repC3minusSub_toSubmodule_eq :
    repC3minusSub.toSubmodule
      = (Module.End.eigenspace zEnd muMinus).map lam2Sub.toSubmodule.subtype := by
  ext x
  rw [show repC3minusSub.toSubmodule
      = lam2Sub.toSubmodule ⊓ Module.End.eigenspace Zamb muMinus from rfl,
    Submodule.mem_inf, Submodule.mem_map]
  constructor
  · rintro ⟨hx, hxe⟩
    exact ⟨⟨x, hx⟩, (zEnd_eigenspace_iff muMinus ⟨x, hx⟩).mpr hxe, rfl⟩
  · rintro ⟨⟨y, hy⟩, hye, rfl⟩
    exact ⟨hy, (zEnd_eigenspace_iff muMinus ⟨y, hy⟩).mp hye⟩

/-- **`dim ℂ³₊ = dim(μ⁺-eigenspace of `z`)`.**  Reduces the dimension of the icosahedral
representation `ℂ³₊` to the eigenspace dimension of the single 6-dimensional operator `z` on
`Λ²(ℂ⁴)` — the last combinatorial input still needed (`= 3`, via the minimal polynomial
`z² = 20z + 400` and `tr z = 60`) to prove `ℂ³₊` genuinely 3-dimensional. -/
lemma repC3plusSub_finrank_eq :
    Module.finrank ℂ repC3plusSub.toSubmodule
      = Module.finrank ℂ (Module.End.eigenspace zEnd muPlus) := by
  rw [repC3plusSub_toSubmodule_eq, Submodule.finrank_map_subtype_eq]

/-- **`dim ℂ³₋ = dim(μ⁻-eigenspace of `z`)`.** -/
lemma repC3minusSub_finrank_eq :
    Module.finrank ℂ repC3minusSub.toSubmodule
      = Module.finrank ℂ (Module.End.eigenspace zEnd muMinus) := by
  rw [repC3minusSub_toSubmodule_eq, Submodule.finrank_map_subtype_eq]

/-! #### The eigenspace character numerator `S(g) = tr(z ∘ ρ(g))`

The two 3-dimensional icosahedral characters are recovered from `Λ²(ℂ⁴)` by the linear system
`χ₊ + χ₋ = χ_{Λ²}` and `μ⁺·χ₊ + μ⁻·χ₋ = S`, where `S(g) := tr(z·ρ(g))` and `z` acts as the
scalar `μ⁺` on `ℂ³₊` and `μ⁻` on `ℂ³₋`.  Solving gives the golden-ratio entries
`χ₊(g) = (S(g) − μ⁻·χ_{Λ²}(g))/(μ⁺ − μ⁻)`.  Here we compute the honest 60-term group sum
`S = (60, 0, −20, 60, −40)` at the five class representatives. -/

/-- `tr(z·ρ(g))` written as the honest character sum `∑_{h∈A₅} χ_{Λ²}(h·r·h⁻¹·g)`, using that
`z = ∑_h ρ(h·r·h⁻¹)` and that `ρ` is a monoid homomorphism. -/
lemma zEnd_comp_char (g : G) :
    LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation g)
      = ∑ h : G, lam2.character (h * r5 * h⁻¹ * g) := by
  have hchar : ∀ x : G, LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (lam2Sub.toRepresentation x)
      = lam2.character x := fun _ => rfl
  rw [zEnd, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← map_mul, hchar]

-- honest `decide` of the character sum over 5×60 group elements; no `native_decide`
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- **The eigenspace character numerator `S(g) = tr(z·ρ(g))` at the five class representatives is
`(60, 0, −20, 60, −40)`.**  Each value is the honest 60-term sum `∑_h χ_{Λ²}(h·r·h⁻¹·g)`, with
`χ_{Λ²}(y) = ½·((fix₅(y) − 1)² − (fix₅(y²) − 1))` evaluated by `decide` over the 60 elements of
`A₅` (no `native_decide`).  Together with `χ_{Λ²} = (6, 0, −2, 1, 1)` and `z = μ⁺` on `ℂ³₊`,
`z = μ⁻` on `ℂ³₋`, this pins the golden-ratio characters `χ₊ = (3, 0, −1, φ, φ')`,
`χ₋ = (3, 0, −1, φ', φ)`. -/
lemma zEnd_comp_char_val (j : Fin 5) :
    LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation (classRepA5 j))
      = (![60, 0, -20, 60, -40] j : ℂ) := by
  rw [zEnd_comp_char]
  have hchar : ∀ y : G, lam2.character y
      = (2⁻¹ : ℂ) * ((((S4.fixCardM (G := G) (α := Fin 5) y : ℤ) - 1) ^ 2
          - ((S4.fixCardM (G := G) (α := Fin 5) (y * y) : ℤ) - 1) : ℤ) : ℂ) := by
    intro y
    rw [lam2_char_formula, repC4_char, repC4_char]
    push_cast; ring
  have key : ∀ i : Fin 5,
      (∑ h : G, (((S4.fixCardM (G := G) (α := Fin 5) (h * r5 * h⁻¹ * classRepA5 i) : ℤ) - 1) ^ 2
        - ((S4.fixCardM (G := G) (α := Fin 5) ((h * r5 * h⁻¹ * classRepA5 i)
            * (h * r5 * h⁻¹ * classRepA5 i)) : ℤ) - 1)))
      = ![120, 0, -40, 120, -80] i := by decide
  rw [Finset.sum_congr rfl (fun h _ => hchar _), ← Finset.mul_sum, ← Int.cast_sum, key j]
  fin_cases j <;> norm_num

/-- **`tr(z²) = 3600` on `Λ²(ℂ⁴)`.**  Since `z` is central (`zEnd_central`), each summand of
`z² = ∑_g z·ρ(g·r·g⁻¹)` has the same trace as `z·ρ(r)` (conjugation invariance of the trace):
`tr(z·ρ(g·r·g⁻¹)) = tr(ρ(g)·z·ρ(r)·ρ(g)⁻¹) = tr(z·ρ(r))`.  Summing the constant over the 60
elements of `A₅` gives `60·tr(z·ρ(r)) = 60·60 = 3600` (using `zEnd_comp_char_val 3`, as
`r = classRepA5 3`).  With `tr(z) = 60` (`zEnd_trace`) and `dim_ℂ End_G(Λ²) = 2`
(`lam2_hom_finrank`), this is the second trace identity: writing `z² = a·1 + b·z` in the
2-dimensional endomorphism algebra, `tr(z²) = 6a + 60b = 3600` and `tr(z) = 60` combine (with
`dim ℂ³₊ = dim ℂ³₋ = 3`, so `b = μ⁺ + μ⁻ = 20`) to give `a = 400`, i.e. the minimal polynomial
`z² − 20·z − 400 = 0` with roots `μ± = 10 ± 10√5`. -/
lemma zEnd_sq_trace : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * zEnd) = 3600 := by
  have hconj : ∀ g : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹))
        = LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation r5) := by
    intro g
    have hc : lam2Sub.toRepresentation g * zEnd = zEnd * lam2Sub.toRepresentation g :=
      (zEnd_central g).eq
    have hrw : zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹)
        = lam2Sub.toRepresentation g * (zEnd * lam2Sub.toRepresentation r5)
            * lam2Sub.toRepresentation g⁻¹ := by
      rw [map_mul, map_mul]
      simp only [← mul_assoc]
      rw [hc]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hz2 : zEnd * zEnd = ∑ g : G, zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹) := by
    rw [← Finset.mul_sum]; rfl
  rw [hz2, map_sum, Finset.sum_congr rfl (fun g _ => hconj g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hr5 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation r5) = 60 := by
    have h := zEnd_comp_char_val 3
    rw [show classRepA5 3 = r5 from rfl] at h
    rw [h]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have hcard : (Fintype.card G : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_G]; norm_num
  rw [hr5, hcard]; norm_num

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- honest `decide` of a single 60-term `classIdxA5`-indexed sum (no `native_decide`).  The
-- previous version decided the raw 60×60 = 3600-term character double sum under a 2·10⁹
-- heartbeat budget, which cost ~12 GB of kernel memory and OOM-killed the CI runner; the
-- class-index reduction (via `classIdxA5`, which has since landed) brings it back to the
-- same 4·10⁶ budget as the other class-indexed `decide`s in this file.
/-- **`tr(z³) = 96000` on `Λ²(ℂ⁴)`.**  Mirrors `zEnd_sq_trace` one level up: since `z²` is
central (`zEnd_central` twice), each summand of `z³ = ∑_g z²·ρ(g·r·g⁻¹)` has the same trace as
`z²·ρ(r)` (conjugation invariance of the trace), giving `tr(z³) = 60·tr(z²·ρ(r))`.  Then
`z²·ρ(r) = ∑_h z·ρ(h·r·h⁻¹·r)` (unfolding one `z`), so `tr(z²·ρ(r)) = ∑_h tr(z·ρ(h·r·h⁻¹·r))`.
Because `z` is central, `x ↦ tr(z·ρ(x))` is a class function, so each term is the
already-tabulated `zEnd_comp_char_val` value at `classIdxA5 (h·r·h⁻¹·r)`; the remaining
group-specific input is the single 60-term sum
`∑_h (60,0,−20,60,−40)_{classIdxA5 (h·r·h⁻¹·r)} = 1600`, evaluated by `decide`
(no `native_decide`).  Hence `tr(z³) = 60·1600 = 96000`.  With `tr(z) = 60` and
`tr(z²) = 3600`, the linear trace system `tr(z²) = a·tr(z) + 6b`, `tr(z³) = a·tr(z²) + b·tr(z)`
pins `a = 20`, `b = 400`, i.e. the minimal polynomial `z² − 20·z − 400 = 0` with roots
`μ± = 10 ± 10√5`. -/
lemma zEnd_cube_trace :
    LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * zEnd * zEnd) = 96000 := by
  -- `z³ = ∑_g z²·ρ(g·r·g⁻¹)`; each summand's trace equals `tr(z²·ρ(r))` since `z²` is central.
  have hconj : ∀ g : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
          (zEnd * zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹))
        = LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
          (zEnd * zEnd * lam2Sub.toRepresentation r5) := by
    intro g
    have hcomm : Commute (lam2Sub.toRepresentation g) (zEnd * zEnd) :=
      (zEnd_central g).mul_right (zEnd_central g)
    have hrw : zEnd * zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹)
        = lam2Sub.toRepresentation g * (zEnd * zEnd * lam2Sub.toRepresentation r5)
            * lam2Sub.toRepresentation g⁻¹ := by
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcomm.eq,
        mul_assoc (lam2Sub.toRepresentation g)]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have hz3 : zEnd * zEnd * zEnd
      = ∑ g : G, zEnd * zEnd * lam2Sub.toRepresentation (g * r5 * g⁻¹) := by
    rw [← Finset.mul_sum]; rfl
  rw [hz3, map_sum, Finset.sum_congr rfl (fun g _ => hconj g), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  -- `x ↦ tr(z·ρ(x))` is a class function: `z` is central, so conjugating the argument
  -- conjugates `z·ρ(x)` and the trace is conjugation invariant.
  have htr_conj : ∀ (c x : G),
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation (c * x * c⁻¹))
        = LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation x) := by
    intro c x
    have hc : lam2Sub.toRepresentation c * zEnd = zEnd * lam2Sub.toRepresentation c :=
      (zEnd_central c).eq
    have hrw : zEnd * lam2Sub.toRepresentation (c * x * c⁻¹)
        = lam2Sub.toRepresentation c * (zEnd * lam2Sub.toRepresentation x)
            * lam2Sub.toRepresentation c⁻¹ := by
      rw [map_mul, map_mul]
      simp only [← mul_assoc]
      rw [hc]
    rw [hrw, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  -- The `ℂ`-valued table of `zEnd_comp_char_val` agrees with its `ℤ`-valued literal.
  have hvec : ∀ j : Fin 5,
      (![60, 0, -20, 60, -40] j : ℂ) = (((![60, 0, -20, 60, -40] : Fin 5 → ℤ) j : ℤ) : ℂ) := by
    intro j; fin_cases j <;> norm_num
  -- Hence `tr(z·ρ(y))` is the `classIdxA5`-indexed table value, for every `y`.
  have htable : ∀ y : G,
      LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation y)
        = (((![60, 0, -20, 60, -40] : Fin 5 → ℤ) (classIdxA5 y) : ℤ) : ℂ) := by
    intro y
    obtain ⟨c, hc⟩ := classIdxA5_spec y
    -- Localise the rewrite (cf. the `FDRep.char_conj` lesson): a bare `rw [← hc]` would also
    -- rewrite the `y` inside `classIdxA5 y`.
    have key : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) (zEnd * lam2Sub.toRepresentation y)
        = LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
            (zEnd * lam2Sub.toRepresentation (classRepA5 (classIdxA5 y))) := by
      conv_lhs => rw [← hc]
      exact htr_conj c _
    rw [key, zEnd_comp_char_val, hvec]
  -- `tr(z²·ρ(r)) = 1600`: unfold one `z` so `z²·ρ(r) = ∑_h z·ρ(h·r·h⁻¹·r)`.
  have hexpand : zEnd * zEnd * lam2Sub.toRepresentation r5
      = ∑ h : G, zEnd * lam2Sub.toRepresentation (h * r5 * h⁻¹ * r5) := by
    rw [show (zEnd * zEnd : Module.End ℂ ↥lam2Sub.toSubmodule)
          = ∑ h : G, zEnd * lam2Sub.toRepresentation (h * r5 * h⁻¹) by
        rw [← Finset.mul_sum]; rfl, Finset.sum_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [mul_assoc, ← map_mul]
  have hr5 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
      (zEnd * zEnd * lam2Sub.toRepresentation r5) = 1600 := by
    have key :
        (∑ h : G, (![60, 0, -20, 60, -40] : Fin 5 → ℤ) (classIdxA5 (h * r5 * h⁻¹ * r5)))
          = 1600 := by decide
    rw [hexpand, map_sum,
      Finset.sum_congr rfl (fun h _ => htable (h * r5 * h⁻¹ * r5)),
      ← Int.cast_sum, key]
    norm_num
  have hcard : (Fintype.card G : ℂ) = 60 := by
    rw [← Nat.card_eq_fintype_card, card_G]; norm_num
  rw [hr5, hcard]; norm_num

/-- **`dim_ℂ Λ²(ℂ⁴) = 6`.**  The value of the character at the identity (`FDRep.char_one`),
equal to `lam2_character 0 = 6` since `classRepA5 0 = 1`.  This is the dimension `tr 1` that the
two eigenspaces of `z` must add up to (`3 + 3 = 6`). -/
lemma lam2_finrank : Module.finrank ℂ (↥lam2Sub.toSubmodule) = 6 := by
  have h : (Module.finrank ℂ lam2 : ℂ) = 6 := by
    rw [← FDRep.char_one lam2, show (1 : G) = classRepA5 0 from rfl, lam2_character]
    norm_num
  exact_mod_cast h

/-- **`z` is not a scalar operator on `Λ²(ℂ⁴)`.**  If `z = c·1`, then `tr z = 6c = 60` forces
`c = 10`, but then `tr z² = 6c² = 600 ≠ 3600` (`zEnd_sq_trace`).  Hence `{1, z}` are linearly
independent in the 2-dimensional endomorphism algebra `End_{A₅}(Λ²)` (`lam2_hom_finrank`), so
they are a basis: `z` satisfies a minimal polynomial of degree exactly `2` (the linchpin for the
eigenspace split `z² = 20z + 400`). -/
lemma zEnd_not_scalar (c : ℂ) : zEnd ≠ c • 1 := by
  intro hc
  have htr1 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
      (1 : Module.End ℂ ↥lam2Sub.toSubmodule) = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, lam2_finrank]; norm_num
  have h1 : c * 6 = 60 := by
    have h := zEnd_trace
    rwa [hc, map_smul, htr1, smul_eq_mul] at h
  have h2 : c * c * 6 = 3600 := by
    have h := zEnd_sq_trace
    rwa [hc, smul_mul_smul_comm, one_mul, map_smul, htr1, smul_eq_mul] at h
  have hc10 : c = 10 := by linear_combination h1 / 6
  rw [hc10] at h2; norm_num at h2

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
-- The `Action.Hom` / `FGModuleCat` composition unfolds through several category layers, so the
-- definitional-equality checks (`comm`, and the `rfl` transport lemmas) exceed the default
-- recursion depth and heartbeat budget.
/-- **THE degree-2 relation `z² = a·z + b·1` in `End_{A₅}(Λ²(ℂ⁴))`.**

Because `z = zEnd` is `A₅`-equivariant (`zEnd_central`), so is its square, so both — together with
the identity — package as morphisms in the categorical Hom-space `lam2 ⟶ lam2`, which is
`2`-dimensional (`lam2_hom_finrank`).  Three vectors `{1, z, z²}` in a `2`-dimensional space are
linearly dependent.  Pushing that dependency through the (ℂ-linear) forgetful map to
`End ℂ ↥lam2Sub.toSubmodule` gives `c₀·1 + c₁·z + c₂·z² = 0` with the `cᵢ` not all zero.  The
`z²`-coefficient `c₂` must be nonzero: otherwise `{1, z}` would be linearly dependent, contradicting
`zEnd_not_scalar`.  Dividing by `c₂` exhibits `z²` in the span of `{1, z}`, i.e. `∃ a b, z² = a·z +
b·1`.  This is the linchpin for the eigenspace split `z² = 20·z + 400·1`. -/
lemma zEnd_sq_eq_aux : ∃ a b : ℂ, zEnd * zEnd = a • zEnd + b • 1 := by
  -- Package `zEnd` as a categorical endomorphism of `lam2` (equivariant via `zEnd_central`).
  let zHom : lam2 ⟶ lam2 :=
    { hom := FGModuleCat.ofHom zEnd
      comm := fun g => by
        ext v
        exact congr_fun (congr_arg DFunLike.coe (zEnd_central g).symm) v }
  -- The forgetful "underlying linear map" functional, packaged as a ℂ-linear map.
  let Φ : (lam2 ⟶ lam2) →ₗ[ℂ] Module.End ℂ (↥lam2Sub.toSubmodule) :=
    { toFun := fun f => f.hom.hom.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hid : Φ (𝟙 lam2) = 1 := rfl
  have hz : Φ zHom = zEnd := rfl
  have hzz : Φ (zHom ≫ zHom) = zEnd * zEnd := rfl
  -- `1 ≠ 0` in the endomorphism algebra (its trace is `6 ≠ 0`).
  have hone : (1 : Module.End ℂ (↥lam2Sub.toSubmodule)) ≠ 0 := by
    intro h
    have htr : LinearMap.trace ℂ (↥lam2Sub.toSubmodule)
        (1 : Module.End ℂ (↥lam2Sub.toSubmodule)) = 6 := by
      rw [Module.End.one_eq_id, LinearMap.trace_id, lam2_finrank]; norm_num
    rw [h, map_zero] at htr; norm_num at htr
  -- Three vectors in a `2`-dimensional space are linearly dependent.
  have hdep : ¬ LinearIndependent ℂ
      (![𝟙 lam2, zHom, zHom ≫ zHom] : Fin 3 → (lam2 ⟶ lam2)) := by
    intro hli
    have h := hli.fintype_card_le_finrank
    rw [lam2_hom_finrank, Fintype.card_fin] at h; omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨c, hsum, i₀, hne⟩ := hdep
  -- Push the dependency through `Φ`.
  have himg : c 0 • (1 : Module.End ℂ (↥lam2Sub.toSubmodule)) + c 1 • zEnd
      + c 2 • (zEnd * zEnd) = 0 := by
    have hkey := congr_arg Φ hsum
    rw [map_zero, map_sum, Fin.sum_univ_three] at hkey
    simpa only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, hid, hz, hzz] using hkey
  -- The `z²`-coefficient is nonzero.
  have hc2 : c 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero] at himg
    by_cases h1 : c 1 = 0
    · rw [h1, zero_smul, add_zero] at himg
      have hc0 : c 0 = 0 := (smul_eq_zero.mp himg).resolve_right hone
      fin_cases i₀ <;> simp_all
    · refine zEnd_not_scalar (-((c 1)⁻¹ * c 0)) ?_
      -- Scale the relation by `c₁⁻¹` (avoids the `Module.End` neg/sub instance diamond).
      have hscaled := congrArg (fun x => (c 1)⁻¹ • x) himg
      simp only [smul_add, smul_zero, smul_smul, inv_mul_cancel₀ h1, one_smul] at hscaled
      apply eq_of_sub_eq_zero
      rw [← hscaled]; module
  -- Divide by `c₂` to exhibit `z²` in the span of `{1, z}`.
  refine ⟨-((c 2)⁻¹ * c 1), -((c 2)⁻¹ * c 0), ?_⟩
  have hscaled := congrArg (fun x => (c 2)⁻¹ • x) himg
  simp only [smul_add, smul_zero, smul_smul, inv_mul_cancel₀ hc2, one_smul] at hscaled
  apply eq_of_sub_eq_zero
  rw [← hscaled]; module

/-! #### The two eigenvalues `μ± = 10 ± 10√5` and the minimal polynomial `X² − 20X − 400`

The eigenvalues of `z` on the two 3-dimensional eigenspaces are `μ± = 10 ± 10√5 = 20φ, 20φ'`.
These are exactly the two roots of `X² − 20X − 400`: their sum is `20` and their product is
`−400`, and their difference is `20√5` (the `√5` that produces the golden-ratio characters).
These identities are the algebraic content of the minimal polynomial `z² − 20z − 400 = 0`. -/

/-- `μ⁺ + μ⁻ = 20` — the trace of the companion `X² − 20X − 400`, i.e. `z² = 20z + 400·1`. -/
lemma muPlus_add_muMinus : muPlus + muMinus = 20 := by
  simp only [muPlus, muMinus]; ring

/-- `√5² = 5` in `ℂ`, the single irrational identity feeding the eigenvalue arithmetic. -/
lemma sqrt5_sq : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num

/-- `μ⁺ · μ⁻ = −400` — the constant term of the companion `X² − 20X − 400`. -/
lemma muPlus_mul_muMinus : muPlus * muMinus = -400 := by
  simp only [muPlus, muMinus]; ring_nf; rw [sqrt5_sq]; norm_num

/-- `μ⁺ − μ⁻ = 20√5` — the golden-ratio-producing gap between the two eigenvalues, the
denominator in `χ₊(g) = (S(g) − μ⁻·χ_{Λ²}(g))/(μ⁺ − μ⁻)`. -/
lemma muPlus_sub_muMinus : muPlus - muMinus = 20 * (Real.sqrt 5 : ℂ) := by
  simp only [muPlus, muMinus]; ring

/-- `20√5 ≠ 0` — the denominator `μ⁺ − μ⁻` of the spectral projection is invertible. -/
lemma twentyRootFive_ne_zero : (20 * (Real.sqrt 5 : ℂ)) ≠ 0 :=
  mul_ne_zero (by norm_num) (by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-! #### The pinned minimal polynomial `z² = 20·z + 400·1` and the 3+3 eigenspace split

The linear-dependence lemma `zEnd_sq_eq_aux` only says `z² = a·z + b·1` for *some* `(a, b)`.
Taking traces of that relation and of `z·(z² = a·z + b·1)` against the three computed values
`tr z = 60`, `tr z² = 3600`, `tr z³ = 96000` gives the linear system `60a + 6b = 3600`,
`3600a + 60b = 96000`, whose unique solution is `(a, b) = (20, 400)`.  This pins the minimal
polynomial `z² − 20z − 400 = (z − μ⁺)(z − μ⁻)`, from which the two eigenspaces are the range and
kernel of the spectral projection `P⁺ = (μ⁺ − μ⁻)⁻¹(z − μ⁻)`. -/

/-- **THE pinned degree-2 relation `z² = 20·z + 400·1`.**  Solving the `2×2` trace system
`60a + 6b = tr z² = 3600`, `3600a + 60b = tr z³ = 96000` fixes the coefficients `(a, b) = (20, 400)`
in `zEnd_sq_eq_aux`.  Equivalently `z² − 20z − 400 = (z − μ⁺)(z − μ⁻) = 0`, the minimal polynomial
whose roots are the golden-ratio eigenvalues `μ± = 10 ± 10√5`. -/
lemma zEnd_sq_eq : zEnd * zEnd = (20 : ℂ) • zEnd + (400 : ℂ) • 1 := by
  obtain ⟨a, b, hab⟩ := zEnd_sq_eq_aux
  have htr1 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) 1 = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, lam2_finrank]; norm_num
  -- Trace of `z² = a·z + b·1`: `3600 = 60a + 6b`.
  have e1 : (3600 : ℂ) = a * 60 + b * 6 := by
    have h := congr_arg (LinearMap.trace ℂ (↥lam2Sub.toSubmodule)) hab
    rwa [zEnd_sq_trace, map_add, map_smul, map_smul, zEnd_trace, htr1, smul_eq_mul,
      smul_eq_mul] at h
  -- Multiply the relation by `z` and take traces: `96000 = 3600a + 60b`.
  have hcube : zEnd * zEnd * zEnd = a • (zEnd * zEnd) + b • zEnd := by
    conv_lhs => rw [hab]
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  have e2 : (96000 : ℂ) = a * 3600 + b * 60 := by
    have h := congr_arg (LinearMap.trace ℂ (↥lam2Sub.toSubmodule)) hcube
    rwa [zEnd_cube_trace, map_add, map_smul, map_smul, zEnd_sq_trace, zEnd_trace, smul_eq_mul,
      smul_eq_mul] at h
  have ha : a = 20 := by linear_combination (1 / 300 : ℂ) * e1 + (-1 / 3000 : ℂ) * e2
  have hb : b = 400 := by linear_combination (-1 / 5 : ℂ) * e1 + (1 / 300 : ℂ) * e2
  rw [ha, hb] at hab
  exact hab

/-- The **spectral projection onto the `μ⁺`-eigenspace**, `P⁺ = (μ⁺ − μ⁻)⁻¹·(z − μ⁻·1)`.  Because
`(z − μ⁺)(z − μ⁻) = 0` and `μ⁺ − μ⁻ = 20√5`, this is idempotent with range `ker(z − μ⁺)` and
kernel `ker(z − μ⁻)`, so its trace counts `dim ℂ³₊`. -/
noncomputable def zProjPlus : Module.End ℂ ↥lam2Sub.toSubmodule :=
  (20 * (Real.sqrt 5 : ℂ))⁻¹ • (zEnd - muMinus • 1)

set_option maxHeartbeats 800000 in
-- The `IsProj` obligations unfold `zProjPlus` and the eigenspace membership through several
-- submodule-coercion layers, so the definitional-equality checks exceed the default budget.
/-- `P⁺` is a projection **onto the `μ⁺`-eigenspace of `z`**: it maps every vector into that
eigenspace (`z·P⁺ = μ⁺·P⁺`, from the minimal polynomial) and fixes it pointwise (`P⁺ = 1` there,
since `(μ⁺ − μ⁻)⁻¹(μ⁺ − μ⁻) = 1`). -/
lemma zProjPlus_isProj : LinearMap.IsProj (Module.End.eigenspace zEnd muPlus) zProjPlus := by
  -- Minimal polynomial in `(μ⁺+μ⁻, μ⁺·μ⁻)` form, then the key `(z − μ⁺)(z − μ⁻) = 0` rearrangement.
  have hkey : zEnd * zEnd = (muPlus + muMinus) • zEnd - (muPlus * muMinus) • 1 := by
    rw [zEnd_sq_eq, muPlus_add_muMinus, muPlus_mul_muMinus]; module
  have hzP : zEnd * (zEnd - muMinus • 1) = muPlus • (zEnd - muMinus • 1) := by
    rw [mul_sub zEnd zEnd (muMinus • 1), mul_smul_comm, mul_one, hkey,
      smul_sub muPlus zEnd (muMinus • 1), smul_smul]
    module
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · -- `P⁺ x` lies in the `μ⁺`-eigenspace.
    rw [Module.End.mem_eigenspace_iff]
    have hop : zEnd * zProjPlus = muPlus • zProjPlus := by
      rw [zProjPlus, mul_smul_comm, hzP, smul_comm]
    have h := congr_arg (fun f : Module.End ℂ (↥lam2Sub.toSubmodule) => f x) hop
    simpa [Module.End.mul_apply] using h
  · -- `P⁺` fixes the `μ⁺`-eigenspace pointwise.
    rw [Module.End.mem_eigenspace_iff] at hx
    rw [zProjPlus, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, hx, ← sub_smul, smul_smul, muPlus_sub_muMinus,
      inv_mul_cancel₀ twentyRootFive_ne_zero, one_smul]

/-- **The kernel of `P⁺` is the `μ⁻`-eigenspace of `z`.**  Since `(μ⁺ − μ⁻)⁻¹ ≠ 0`, `P⁺ x = 0`
iff `(z − μ⁻)x = 0`, i.e. `z x = μ⁻·x`. -/
lemma ker_zProjPlus : LinearMap.ker zProjPlus = Module.End.eigenspace zEnd muMinus := by
  ext x
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, zProjPlus, LinearMap.smul_apply,
    smul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (inv_ne_zero twentyRootFive_ne_zero)
    · rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  · intro h
    refine Or.inr ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact h

/-- **`tr P⁺ = 3`.**  Linearity of the trace gives `tr P⁺ = (20√5)⁻¹(tr z − μ⁻·tr 1)
= (20√5)⁻¹(60 − 6μ⁻) = (20√5)⁻¹·60√5 = 3`.  Via `LinearMap.IsProj.trace` this equals
`dim(μ⁺-eigenspace)`. -/
lemma trace_zProjPlus : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) zProjPlus = 3 := by
  have htr1 : LinearMap.trace ℂ (↥lam2Sub.toSubmodule) 1 = 6 := by
    rw [Module.End.one_eq_id, LinearMap.trace_id, lam2_finrank]; norm_num
  rw [zProjPlus,
    LinearMap.map_smul (LinearMap.trace ℂ (↥lam2Sub.toSubmodule)) (20 * (Real.sqrt 5 : ℂ))⁻¹
      (zEnd - muMinus • 1),
    LinearMap.map_sub (LinearMap.trace ℂ (↥lam2Sub.toSubmodule)) zEnd (muMinus • 1),
    LinearMap.map_smul (LinearMap.trace ℂ (↥lam2Sub.toSubmodule)) muMinus 1,
    zEnd_trace, htr1, smul_eq_mul, smul_eq_mul, muMinus,
    show (60 : ℂ) - (10 - 10 * (Real.sqrt 5 : ℂ)) * 6 = (20 * (Real.sqrt 5 : ℂ)) * 3 from by ring,
    ← mul_assoc, inv_mul_cancel₀ twentyRootFive_ne_zero, one_mul]

set_option synthInstance.maxHeartbeats 400000 in
-- Instance synthesis for the thrice-nested eigenspace subtype (`↥(ker(z − μ⁺) ⊆ Λ²(ℂ⁴) ⊆ W4 ⊗ W4)`)
-- exceeds the default `synthInstance` budget, so `IsProj.trace`'s `Module.Free`/`Module.Finite`
-- arguments need a larger limit.
/-- **`dim(μ⁺-eigenspace of `z`) = 3`.**  `LinearMap.IsProj.trace` identifies the trace of the
projection `P⁺` with the dimension of its range; `trace_zProjPlus` computes that trace as `3`. -/
lemma eigenspace_muPlus_finrank :
    Module.finrank ℂ (Module.End.eigenspace zEnd muPlus) = 3 := by
  haveI : FiniteDimensional ℂ (↥lam2Sub.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by rw [lam2_finrank]; norm_num)
  haveI : Module.Free ℂ (↥(Module.End.eigenspace zEnd muPlus)) :=
    Module.Free.of_divisionRing ℂ (↥(Module.End.eigenspace zEnd muPlus))
  haveI : Module.Free ℂ (↥(LinearMap.ker zProjPlus)) :=
    Module.Free.of_divisionRing ℂ (↥(LinearMap.ker zProjPlus))
  have h := zProjPlus_isProj.trace
  rw [trace_zProjPlus] at h
  exact_mod_cast h.symm

/-- **The two eigenspaces are complementary**, `Λ²(ℂ⁴) = ℂ³₊ ⊕ ℂ³₋`.  `P⁺` is a projection onto
the `μ⁺`-eigenspace with kernel the `μ⁻`-eigenspace (`ker_zProjPlus`), so `LinearMap.IsProj.isCompl`
gives the direct-sum decomposition. -/
lemma eigenspace_isCompl :
    IsCompl (Module.End.eigenspace zEnd muPlus) (Module.End.eigenspace zEnd muMinus) := by
  have h := zProjPlus_isProj.isCompl
  rwa [ker_zProjPlus] at h

/-- **`dim(μ⁻-eigenspace of `z`) = 3`.**  The two eigenspaces are complementary in the
`6`-dimensional `Λ²(ℂ⁴)` (`eigenspace_isCompl`, `lam2_finrank`), and the `μ⁺`-eigenspace has
dimension `3`, so the `μ⁻`-eigenspace has dimension `6 − 3 = 3`. -/
lemma eigenspace_muMinus_finrank :
    Module.finrank ℂ (Module.End.eigenspace zEnd muMinus) = 3 := by
  haveI : FiniteDimensional ℂ (↥lam2Sub.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by rw [lam2_finrank]; norm_num)
  have hsum := Submodule.finrank_add_eq_of_isCompl eigenspace_isCompl
  rw [eigenspace_muPlus_finrank, lam2_finrank] at hsum
  omega

/-- **`dim ℂ³₊ = 3`.**  Combines `repC3plusSub_finrank_eq` (the carrier is the `μ⁺`-eigenspace of
`z`, pushed forward along `Λ²(ℂ⁴) ↪ W4 ⊗ W4`) with `eigenspace_muPlus_finrank`. -/
lemma repC3plus_finrank : Module.finrank ℂ repC3plusSub.toSubmodule = 3 := by
  rw [repC3plusSub_finrank_eq, eigenspace_muPlus_finrank]

/-- **`dim ℂ³₋ = 3`.**  Combines `repC3minusSub_finrank_eq` with `eigenspace_muMinus_finrank`. -/
lemma repC3minus_finrank : Module.finrank ℂ repC3minusSub.toSubmodule = 3 := by
  rw [repC3minusSub_finrank_eq, eigenspace_muMinus_finrank]

/-! #### `χ_{Λ²} = χ₊ + χ₋`: the honest character of `Λ²(ℂ⁴)` is the sum of the two book rows -/

/-- `Q5toC` is additive. -/
lemma Q5toC_add (a b : Q5) : Q5toC (a + b) = Q5toC a + Q5toC b := by
  simp only [Q5toC, Q5.add_re, Q5.add_im]; push_cast; ring

/-- **The character of `Λ²(ℂ⁴)` is the sum of the two golden-ratio rows `χ₊ + χ₋`.**  The honest
trace `χ_{Λ²} = (6, 0, −2, 1, 1)` (`lam2_character`) equals `chiA5 1 + chiA5 2` at every class:
row 1 is `(3, 0, −1, φ, φ')`, row 2 is `(3, 0, −1, φ', φ)`, and `φ + φ' = 1` makes the two
`√5` contributions cancel on the 5-cycle classes.  Combined with `A5_orthonormal` (rows 1 and 2
are orthonormal, and orthogonal to rows 0/3/4), this exhibits `Λ²(ℂ⁴)` as the multiplicity-free
sum of the two 3-dimensional icosahedral constituents `ℂ³₊ ⊕ ℂ³₋` — the character-level
statement underlying the eigenspace split of the central `z`. -/
lemma lam2_character_eq_sum (j : Fin 5) :
    lam2.character (classRepA5 j) = Q5toC (chiA5 1 j) + Q5toC (chiA5 2 j) := by
  rw [lam2_character, ← Q5toC_add, Q5toC]
  fin_cases j <;>
    simp only [chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;>
    norm_num [Q5.add_re, Q5.add_im, Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re,
      Q5.neg_im, Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im]

/-! #### The golden-ratio characters `χ₊, χ₋` of `ℂ³₊, ℂ³₋`

The two 3-dimensional icosahedral characters are recovered from the honest trace data on
`Λ²(ℂ⁴)` by the linear system `χ₊ + χ₋ = χ_{Λ²}` and `μ⁺·χ₊ + μ⁻·χ₋ = tr(z·ρ(g))`, using
that the central `z` acts as the scalar `μ⁺` on `ℂ³₊` and `μ⁻` on `ℂ³₋`.  Solving (the system
is invertible since `μ⁺ − μ⁻ = 20√5 ≠ 0`) gives the golden-ratio rows `χ₊ = (3,0,-1,φ,φ')`,
`χ₋ = (3,0,-1,φ',φ)`. -/

-- The doubly-nested eigenspace subtype `↥E ⊆ ↥Λ²(ℂ⁴) ⊆ W4 ⊗ W4` makes instance synthesis and
-- the definitional-equality checks in `trace_conj'` expensive, so both budgets are raised.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Trace transport across the inclusion `Λ²(ℂ⁴) ↪ W4 ⊗ W4`.**  For a subrepresentation `S`
whose carrier is the pushforward `E.map (Λ²(ℂ⁴) ↪ W4 ⊗ W4)` of a `g`-invariant subspace `E` of
`Λ²(ℂ⁴)`, the character of `S` at `g` equals the trace of the intrinsic action `ρ(g)|E`.  The
conjugating equivalence `e : E ≃ S.toSubmodule` (built by `LinearEquiv.ofBijective` from the
inclusion `E ↪ Λ²(ℂ⁴) ↪ W4 ⊗ W4` corestricted to `S`) intertwines the two actions, so
`LinearMap.trace_conj'` identifies the traces. -/
private lemma character_eq_restrict_trace
    (S : Subrepresentation (rhoV.tprod rhoV))
    (E : Submodule ℂ (↥lam2Sub.toSubmodule))
    (hSE : S.toSubmodule = E.map lam2Sub.toSubmodule.subtype)
    (g : G)
    (hmaps : Set.MapsTo (lam2Sub.toRepresentation g) E E) :
    (FDRep.of S.toRepresentation).character g
      = LinearMap.trace ℂ ↥E ((lam2Sub.toRepresentation g).restrict hmaps) := by
  -- Pin the `AddCommGroup` instance on the (doubly-nested) `↥E` so the intertwiner `e` and the
  -- traces below share it with `trace_conj'` (avoiding a `Submodule.addCommMonoid` diamond).
  letI : AddCommGroup (↥E) := E.addCommGroup
  -- The intertwiner `e : E ≃ S.toSubmodule`, the inclusion `E ↪ Λ²(ℂ⁴) ↪ W4 ⊗ W4` corestricted.
  have hmapsInto : ∀ x : ↥E,
      lam2Sub.toSubmodule.subtype (E.subtype x) ∈ S.toSubmodule := by
    intro x; rw [hSE]; exact Submodule.mem_map_of_mem x.2
  set g0 : ↥E →ₗ[ℂ] ↥S.toSubmodule :=
    (lam2Sub.toSubmodule.subtype ∘ₗ E.subtype).codRestrict S.toSubmodule hmapsInto with hg0
  have hg0_inj : Function.Injective g0 := by
    intro a b hab
    have h : (E.subtype a : ↥lam2Sub.toSubmodule) = E.subtype b := by
      apply lam2Sub.toSubmodule.injective_subtype
      simpa [hg0, LinearMap.codRestrict_apply, LinearMap.comp_apply] using Subtype.ext_iff.mp hab
    exact E.injective_subtype h
  have hg0_surj : Function.Surjective g0 := by
    intro z
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp
      (show (z : W4 ⊗[ℂ] W4) ∈ E.map lam2Sub.toSubmodule.subtype by rw [← hSE]; exact z.2)
    exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  set e : ↥E ≃ₗ[ℂ] ↥S.toSubmodule := LinearEquiv.ofBijective g0 ⟨hg0_inj, hg0_surj⟩ with he
  have hecoe : ∀ w : ↥E, ((e w : ↥S.toSubmodule) : W4 ⊗[ℂ] W4)
      = ((w : ↥lam2Sub.toSubmodule) : W4 ⊗[ℂ] W4) := by
    intro w
    simp only [he, LinearEquiv.ofBijective_apply, hg0, LinearMap.codRestrict_apply,
      LinearMap.comp_apply, Submodule.coe_subtype]
  -- `S`'s action is the conjugate of `ρ(g)|E` by the intertwiner `e`.
  have hconj : S.toRepresentation g
      = e.conj ((lam2Sub.toRepresentation g).restrict hmaps) := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    rw [LinearEquiv.conj_apply_apply]
    have hLHS : ((S.toRepresentation g y : ↥S.toSubmodule) : W4 ⊗[ℂ] W4)
        = (rhoV.tprod rhoV) g (y : W4 ⊗[ℂ] W4) := rfl
    have hRHS : ((e ((lam2Sub.toRepresentation g).restrict hmaps (e.symm y)) : ↥S.toSubmodule)
          : W4 ⊗[ℂ] W4)
        = (rhoV.tprod rhoV) g (y : W4 ⊗[ℂ] W4) := by
      rw [hecoe]
      have hcoe : (((lam2Sub.toRepresentation g).restrict hmaps (e.symm y) : ↥E)
            : ↥lam2Sub.toSubmodule)
          = lam2Sub.toRepresentation g ((e.symm y : ↥E) : ↥lam2Sub.toSubmodule) :=
        LinearMap.coe_restrict_apply hmaps (e.symm y)
      rw [hcoe]
      have hcoe2 : ((lam2Sub.toRepresentation g ((e.symm y : ↥E) : ↥lam2Sub.toSubmodule)
            : ↥lam2Sub.toSubmodule) : W4 ⊗[ℂ] W4)
          = (rhoV.tprod rhoV) g (((e.symm y : ↥E) : ↥lam2Sub.toSubmodule) : W4 ⊗[ℂ] W4) := rfl
      rw [hcoe2]
      congr 1
      have hsy := hecoe (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at hsy
      exact hsy.symm
    rw [hLHS, hRHS]
  -- Trace is invariant under the conjugation `e` (`trace_conj'`).
  show LinearMap.trace ℂ ↥S.toSubmodule (S.toRepresentation g)
      = LinearMap.trace ℂ ↥E ((lam2Sub.toRepresentation g).restrict hmaps)
  rw [hconj]
  exact LinearMap.trace_conj' _ e

/-- The intrinsic action `ρ(g)` preserves the `μ⁺`-eigenspace of `z`, since `z` is central. -/
private lemma mapsTo_eigenspace_muPlus (g : G) :
    Set.MapsTo (lam2Sub.toRepresentation g)
      (Module.End.eigenspace zEnd muPlus : Set _) (Module.End.eigenspace zEnd muPlus : Set _) :=
  Module.End.mapsTo_genEigenspace_of_comm (zEnd_central g).symm muPlus 1

/-- The intrinsic action `ρ(g)` preserves the `μ⁻`-eigenspace of `z`. -/
private lemma mapsTo_eigenspace_muMinus (g : G) :
    Set.MapsTo (lam2Sub.toRepresentation g)
      (Module.End.eigenspace zEnd muMinus : Set _) (Module.End.eigenspace zEnd muMinus : Set _) :=
  Module.End.mapsTo_genEigenspace_of_comm (zEnd_central g).symm muMinus 1

/-- `χ₊(g) = tr(ρ(g)|E⁺)`: the character of `ℂ³₊` is the trace of the intrinsic action on the
`μ⁺`-eigenspace of `z`. -/
private lemma repC3plus_character_eq_trace (g : G) :
    repC3plus.character g
      = LinearMap.trace ℂ ↥(Module.End.eigenspace zEnd muPlus)
          ((lam2Sub.toRepresentation g).restrict (mapsTo_eigenspace_muPlus g)) :=
  character_eq_restrict_trace repC3plusSub _ repC3plusSub_toSubmodule_eq g
    (mapsTo_eigenspace_muPlus g)

/-- `χ₋(g) = tr(ρ(g)|E⁻)`. -/
private lemma repC3minus_character_eq_trace (g : G) :
    repC3minus.character g
      = LinearMap.trace ℂ ↥(Module.End.eigenspace zEnd muMinus)
          ((lam2Sub.toRepresentation g).restrict (mapsTo_eigenspace_muMinus g)) :=
  character_eq_restrict_trace repC3minusSub _ repC3minusSub_toSubmodule_eq g
    (mapsTo_eigenspace_muMinus g)

-- Decomposing over the two eigenspaces of `z` and restricting `z·ρ(g)` there runs into the same
-- doubly-nested subtype, so the instance/heartbeat/recursion budgets are raised.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
/-- **The two trace equations for the eigenspace characters.**  Decomposing `Λ²(ℂ⁴)` as the
internal direct sum `E⁺ ⊕ E⁻` of the two eigenspaces of `z` (`eigenspace_isCompl`) and applying
`LinearMap.trace_eq_sum_trace_restrict` to `ρ(g)` and to `z·ρ(g)` gives, respectively,
`χ₊(g) + χ₋(g) = χ_{Λ²}(g)` and `μ⁺·χ₊(g) + μ⁻·χ₋(g) = tr(z·ρ(g))` (using that `z` acts as the
scalar `μ⁺` on `E⁺` and `μ⁻` on `E⁻`). -/
private lemma repC3_character_system (g : G) :
    repC3plus.character g + repC3minus.character g = lam2.character g
      ∧ muPlus * repC3plus.character g + muMinus * repC3minus.character g
          = LinearMap.trace ℂ ↥lam2Sub.toSubmodule (zEnd * lam2Sub.toRepresentation g) := by
  classical
  haveI : FiniteDimensional ℂ (↥lam2Sub.toSubmodule) :=
    FiniteDimensional.of_finrank_pos (by rw [lam2_finrank]; norm_num)
  set N : Fin 2 → Submodule ℂ (↥lam2Sub.toSubmodule)
    := ![Module.End.eigenspace zEnd muPlus, Module.End.eigenspace zEnd muMinus] with hN
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N zero_ne_one huniv).mpr eigenspace_isCompl
  haveI : ∀ i, Module.Finite ℂ ↥(N i) := fun i => inferInstance
  haveI : ∀ i, Module.Free ℂ ↥(N i) := fun i => Module.Free.of_divisionRing ℂ (↥(N i))
  -- `ρ(g)` preserves each eigenspace.
  have hf : ∀ i, Set.MapsTo (lam2Sub.toRepresentation g) (↑(N i)) (↑(N i)) :=
    Fin.forall_fin_two.mpr ⟨mapsTo_eigenspace_muPlus g, mapsTo_eigenspace_muMinus g⟩
  -- `z·ρ(g)` preserves each eigenspace.
  have hMmaps : ∀ i, Set.MapsTo (zEnd * lam2Sub.toRepresentation g) (↑(N i)) (↑(N i)) :=
    Fin.forall_fin_two.mpr
      ⟨fun x hx => Module.End.mapsTo_genEigenspace_of_comm (Commute.refl zEnd) muPlus 1
          (mapsTo_eigenspace_muPlus g hx),
       fun x hx => Module.End.mapsTo_genEigenspace_of_comm (Commute.refl zEnd) muMinus 1
          (mapsTo_eigenspace_muMinus g hx)⟩
  -- On `E⁺`, `z·ρ(g) = μ⁺·ρ(g)`; on `E⁻`, `z·ρ(g) = μ⁻·ρ(g)`.
  have hM0 : (zEnd * lam2Sub.toRepresentation g).restrict (hMmaps 0)
      = muPlus • (lam2Sub.toRepresentation g).restrict (hf 0) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hmem : lam2Sub.toRepresentation g (x : ↥lam2Sub.toSubmodule)
        ∈ Module.End.eigenspace zEnd muPlus := hf 0 x.2
    show zEnd (lam2Sub.toRepresentation g (x : ↥lam2Sub.toSubmodule))
        = muPlus • lam2Sub.toRepresentation g (x : ↥lam2Sub.toSubmodule)
    exact Module.End.mem_eigenspace_iff.mp hmem
  have hM1 : (zEnd * lam2Sub.toRepresentation g).restrict (hMmaps 1)
      = muMinus • (lam2Sub.toRepresentation g).restrict (hf 1) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    have hmem : lam2Sub.toRepresentation g (x : ↥lam2Sub.toSubmodule)
        ∈ Module.End.eigenspace zEnd muMinus := hf 1 x.2
    show zEnd (lam2Sub.toRepresentation g (x : ↥lam2Sub.toSubmodule))
        = muMinus • lam2Sub.toRepresentation g (x : ↥lam2Sub.toSubmodule)
    exact Module.End.mem_eigenspace_iff.mp hmem
  refine ⟨?_, ?_⟩
  · have key := LinearMap.trace_eq_sum_trace_restrict hInternal hf
    rw [Fin.sum_univ_two] at key
    rw [repC3plus_character_eq_trace, repC3minus_character_eq_trace]
    exact key.symm
  · have keyM := LinearMap.trace_eq_sum_trace_restrict hInternal hMmaps
    rw [Fin.sum_univ_two, hM0, hM1, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at keyM
    rw [repC3plus_character_eq_trace, repC3minus_character_eq_trace]
    exact keyM.symm

/-- **`χ₊`, the character of `ℂ³₊`, is the golden-ratio row `(3, 0, -1, φ, φ')`.**  Solving the
`2×2` trace system `χ₊ + χ₋ = (6,0,-2,1,1)`, `μ⁺·χ₊ + μ⁻·χ₋ = (60,0,-20,60,-40)` for `χ₊`
gives `χ₊ = (S − μ⁻·χ_{Λ²})/(μ⁺ − μ⁻)`, matching `chiA5 1` at each class (the `√5` terms
resolving via `sqrt5_sq`). (Etingof Example 4.8.1) -/
lemma repC3plus_character (j : Fin 5) :
    repC3plus.character (classRepA5 j) = Q5toC (chiA5 1 j) := by
  obtain ⟨e1, e2⟩ := repC3_character_system (classRepA5 j)
  rw [lam2_character] at e1
  rw [zEnd_comp_char_val] at e2
  have hne : muPlus - muMinus ≠ 0 := by rw [muPlus_sub_muMinus]; exact twentyRootFive_ne_zero
  refine mul_left_cancel₀ hne ?_
  rw [show (muPlus - muMinus) * repC3plus.character (classRepA5 j)
      = (![60, 0, -20, 60, -40] j : ℂ) - muMinus * (![6, 0, -2, 1, 1] j : ℂ) from by
    linear_combination e2 - muMinus * e1]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, muPlus, muMinus, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im,
      Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im]
  -- `norm_num` closes class `1`; classes `0, 2` are rational and close by `ring`, while the
  -- 5-cycle classes `3, 4` need the `√5² = 5` relation.
  · ring
  · ring
  · linear_combination (-10 : ℂ) * hs
  · linear_combination (10 : ℂ) * hs

/-- **`χ₋`, the character of `ℂ³₋`, is the golden-ratio row `(3, 0, -1, φ', φ)`.**  Solving the
same trace system for `χ₋` gives `χ₋ = (μ⁺·χ_{Λ²} − S)/(μ⁺ − μ⁻)`, matching `chiA5 2` at each
class. (Etingof Example 4.8.1) -/
lemma repC3minus_character (j : Fin 5) :
    repC3minus.character (classRepA5 j) = Q5toC (chiA5 2 j) := by
  obtain ⟨e1, e2⟩ := repC3_character_system (classRepA5 j)
  rw [lam2_character] at e1
  rw [zEnd_comp_char_val] at e2
  have hne : muPlus - muMinus ≠ 0 := by rw [muPlus_sub_muMinus]; exact twentyRootFive_ne_zero
  refine mul_left_cancel₀ hne ?_
  rw [show (muPlus - muMinus) * repC3minus.character (classRepA5 j)
      = muPlus * (![6, 0, -2, 1, 1] j : ℂ) - (![60, 0, -20, 60, -40] j : ℂ) from by
    linear_combination muPlus * e1 - e2]
  have hs := sqrt5_sq
  fin_cases j <;>
    norm_num [Q5toC, muPlus, muMinus, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im,
      Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im]
  · ring
  · ring
  · linear_combination (10 : ℂ) * hs
  · linear_combination (-10 : ℂ) * hs

/-! #### Simplicity of the golden-ratio representations `ℂ³₊`, `ℂ³₋`

Both are simple by the norm-one character criterion `FDRep.simple_iff_char_is_norm_one`.  The
norm sum `∑_g χ(g)·χ(g⁻¹)` is reduced fiberwise over the five conjugacy classes: every `g` is
conjugate to `classRepA5 (classIdxA5 g)` (`classIdxA5_spec`) and every class representative is
conjugate to its inverse (`classRepA5_inv_conj`), so each summand equals
`χ(classRepA5 (classIdxA5 g))²`.  Collecting fibers (`Finset.sum_fiberwise'`, `classIdxA5_card`)
gives `1·3² + 20·0² + 15·(−1)² + 12·φ² + 12·φ'² = 9 + 15 + 36 = 60 = |A₅|`, where the
golden-ratio squares sum to `φ² + φ'² = 3` via `√5² = 5` (`sqrt5_sq`). -/

set_option maxHeartbeats 1000000 in
-- the fiberwise reduction of the 60-term norm sum plus the golden-ratio square arithmetic
-- (`norm_num` over the five classes) exceeds the default heartbeat budget; no `native_decide`
/-- **`ℂ³₊` is simple.**  Norm-one character sum, reduced fiberwise over the five conjugacy
classes to `1·9 + 20·0 + 15·1 + 12·φ² + 12·φ'² = 60`. (Etingof Example 4.8.1) -/
lemma repC3plus_simple : Simple repC3plus := by
  rw [FDRep.simple_iff_char_is_norm_one, card_G]
  have hterm : ∀ g : G, repC3plus.character g * repC3plus.character g⁻¹
      = repC3plus.character (classRepA5 (classIdxA5 g)) ^ 2 := by
    have hclass : ∀ a b : G, (∃ c, c * a * c⁻¹ = b) →
        repC3plus.character b = repC3plus.character a := by
      rintro a b ⟨c, rfl⟩; rw [FDRep.char_conj]
    intro g
    obtain ⟨c, hc⟩ := classIdxA5_spec g
    obtain ⟨d, hd⟩ := classRepA5_inv_conj (classIdxA5 g)
    have h1 : repC3plus.character g = repC3plus.character (classRepA5 (classIdxA5 g)) :=
      hclass _ _ ⟨c, hc⟩
    have hAinv : repC3plus.character (classRepA5 (classIdxA5 g))⁻¹
        = repC3plus.character (classRepA5 (classIdxA5 g)) :=
      hclass _ _ ⟨d, hd⟩
    have hginv : repC3plus.character g⁻¹
        = repC3plus.character (classRepA5 (classIdxA5 g))⁻¹ := by
      refine hclass _ _ ⟨c, ?_⟩
      conv_rhs => rw [← hc]
      group
    rw [h1, hginv, hAinv]; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [show (∑ g : G, repC3plus.character (classRepA5 (classIdxA5 g)) ^ 2)
        = ∑ j : Fin 5, ∑ _g ∈ Finset.univ.filter (fun g => classIdxA5 g = j),
            repC3plus.character (classRepA5 j) ^ 2
      from (Finset.sum_fiberwise' Finset.univ classIdxA5
        (fun j => repC3plus.character (classRepA5 j) ^ 2)).symm]
  simp only [Finset.sum_const, classIdxA5_card, nsmul_eq_mul]
  rw [Fin.sum_univ_five, repC3plus_character 0, repC3plus_character 1, repC3plus_character 2,
    repC3plus_character 3, repC3plus_character 4]
  have hs := sqrt5_sq
  norm_num [Q5toC, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im,
    Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im]
  linear_combination (6 : ℂ) * hs

set_option maxHeartbeats 1000000 in
-- the fiberwise reduction of the 60-term norm sum plus the golden-ratio square arithmetic
-- (`norm_num` over the five classes) exceeds the default heartbeat budget; no `native_decide`
/-- **`ℂ³₋` is simple.**  Same fiberwise norm-one computation as `repC3plus_simple`, with the
golden-ratio entries on the two 5-cycle classes interchanged (the norm sum is unchanged).
(Etingof Example 4.8.1) -/
lemma repC3minus_simple : Simple repC3minus := by
  rw [FDRep.simple_iff_char_is_norm_one, card_G]
  have hterm : ∀ g : G, repC3minus.character g * repC3minus.character g⁻¹
      = repC3minus.character (classRepA5 (classIdxA5 g)) ^ 2 := by
    have hclass : ∀ a b : G, (∃ c, c * a * c⁻¹ = b) →
        repC3minus.character b = repC3minus.character a := by
      rintro a b ⟨c, rfl⟩; rw [FDRep.char_conj]
    intro g
    obtain ⟨c, hc⟩ := classIdxA5_spec g
    obtain ⟨d, hd⟩ := classRepA5_inv_conj (classIdxA5 g)
    have h1 : repC3minus.character g = repC3minus.character (classRepA5 (classIdxA5 g)) :=
      hclass _ _ ⟨c, hc⟩
    have hAinv : repC3minus.character (classRepA5 (classIdxA5 g))⁻¹
        = repC3minus.character (classRepA5 (classIdxA5 g)) :=
      hclass _ _ ⟨d, hd⟩
    have hginv : repC3minus.character g⁻¹
        = repC3minus.character (classRepA5 (classIdxA5 g))⁻¹ := by
      refine hclass _ _ ⟨c, ?_⟩
      conv_rhs => rw [← hc]
      group
    rw [h1, hginv, hAinv]; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g)]
  rw [show (∑ g : G, repC3minus.character (classRepA5 (classIdxA5 g)) ^ 2)
        = ∑ j : Fin 5, ∑ _g ∈ Finset.univ.filter (fun g => classIdxA5 g = j),
            repC3minus.character (classRepA5 j) ^ 2
      from (Finset.sum_fiberwise' Finset.univ classIdxA5
        (fun j => repC3minus.character (classRepA5 j) ^ 2)).symm]
  simp only [Finset.sum_const, classIdxA5_card, nsmul_eq_mul]
  rw [Fin.sum_univ_five, repC3minus_character 0, repC3minus_character 1, repC3minus_character 2,
    repC3minus_character 3, repC3minus_character 4]
  have hs := sqrt5_sq
  norm_num [Q5toC, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Q5.mk_re, Q5.mk_im, Q5.ofNat_re, Q5.ofNat_im, Q5.neg_re, Q5.neg_im,
    Q5.one_re, Q5.one_im, Q5.zero_re, Q5.zero_im]
  linear_combination (6 : ℂ) * hs

/-! #### The five irreducible representations of `A₅`: characters, simplicity, pairwise non-iso

Assembling the trivial `ℂ`, the two golden-ratio rotation reps `ℂ³₊`, `ℂ³₋`, and the
permutation reps `ℂ⁴`, `ℂ⁵` as the five rows of `chiA5`, in order.  These are the five distinct
irreducible characters of `A₅`. -/

/-- The five genuine irreducible representations of `A₅`, indexed `0..4` as
`ℂ, ℂ³₊, ℂ³₋, ℂ⁴, ℂ⁵` — matching the five rows of `chiA5`. -/
def irrepA5 : Fin 5 → FDRep ℂ G := ![repTriv, repC3plus, repC3minus, repC4, repC5]

/-- The rows of `chiA5` realised here are in order: `irrepA5 i` is row `i`. -/
def rowA5 : Fin 5 → Fin 5 := id

/-- Each of the five representations is simple (irreducible). -/
lemma irrepA5_simple (i : Fin 5) : Simple (irrepA5 i) := by
  fin_cases i
  · exact repTriv_simple
  · exact repC3plus_simple
  · exact repC3minus_simple
  · exact repC4_simple
  · exact repC5_simple

/-- The character of `irrepA5 i` at `classRepA5 j` equals the tabulated `Q5` value
`chiA5 (rowA5 i) j = chiA5 i j`.  Rows `0, 3, 4` bridge through the integer table `tblA5`; rows
`1, 2` are the golden-ratio characters `repC3plus_character`, `repC3minus_character`. -/
lemma irrepA5_character_book (i j : Fin 5) :
    (irrepA5 i).character (classRepA5 j) = Q5toC (chiA5 (rowA5 i) j) := by
  simp only [rowA5, id_eq]
  fin_cases i
  · exact (repTriv_character j).trans (chiA5_eq_tblA5 0 j).symm
  · exact repC3plus_character j
  · exact repC3minus_character j
  · exact (repC4_character j).trans (chiA5_eq_tblA5 1 j).symm
  · exact (repC5_character j).trans (chiA5_eq_tblA5 2 j).symm

/-- The five representations are pairwise non-isomorphic (their characters differ).  Distinct
dimensions separate every pair except `ℂ³₊, ℂ³₋`, which are told apart on the 5-cycle class
`(12345)` by the golden-ratio value `√5 ≠ 0` (`sqrt5_sq`, no irrationality machinery).
(Etingof Example 4.8.1) -/
lemma irrepA5_pairwise (i j : Fin 5) (hij : i ≠ j) : ¬ Nonempty (irrepA5 i ≅ irrepA5 j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irrepA5 i).character = (irrepA5 j).character := FDRep.char_iso e
  have hc : ∀ c : Fin 5, Q5toC (chiA5 i c) = Q5toC (chiA5 j c) := by
    intro c
    have h := congrFun hchar (classRepA5 c)
    rw [irrepA5_character_book, irrepA5_character_book] at h
    simpa only [rowA5, id_eq] using h
  -- Injectivity of `Q5toC` on the rational dimension column (class 0).
  have inj0 : ∀ a b : Fin 5, Q5toC (chiA5 a 0) = Q5toC (chiA5 b 0) → chiA5 a 0 = chiA5 b 0 := by
    intro a b h
    have ha : (chiA5 a 0).im = 0 := by fin_cases a <;> decide
    have hb : (chiA5 b 0).im = 0 := by fin_cases b <;> decide
    rw [Q5toC, Q5toC, ha, hb] at h
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact Q5.ext (by exact_mod_cast h) (ha.trans hb.symm)
  have hdim : chiA5 i 0 = chiA5 j 0 := inj0 i j (hc 0)
  -- The two 3-dimensional rows differ on the 5-cycle class `3` by `√5 ≠ 0`.
  have golden : ¬ (Q5toC (chiA5 1 3) = Q5toC (chiA5 2 3)) := by
    simp only [Q5toC, chiA5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Q5.mk_re, Q5.mk_im]
    intro h
    have hz : (Real.sqrt 5 : ℂ) = 0 := by linear_combination h
    have hsq := sqrt5_sq
    rw [hz] at hsq
    norm_num at hsq
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (revert hdim; decide)
      | exact absurd (hc 3) golden
      | exact absurd (hc 3).symm golden

end

end A5

end Etingof.Example4_8_1
