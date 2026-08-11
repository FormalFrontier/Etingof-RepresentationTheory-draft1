import EtingofRepresentationTheory.Chapter3.Problem3_9_1
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.NoncommRing

/-!
# Problem 3.9.4: Formal deformations of representations

Let `A` be an algebra and `V` a representation with structure map `ρ : A → End V`. A
**formal deformation** of `V` is a formal power series
`ρ̃ = ρ₀ + tρ₁ + ⋯ + tⁿρₙ + ⋯`, where each `ρᵢ : A →ₗ End V`, `ρ₀ = ρ`, and
`ρ̃(ab) = ρ̃(a)ρ̃(b)`. If `b(t) = 1 + b₁t + b₂t² + ⋯` with `bᵢ ∈ End V`, then `b ρ̃ b⁻¹` is
an isomorphic deformation.

* **(a)** If `Ext¹(V, V) = 0` then every deformation of `ρ` is trivial (isomorphic to `ρ`).
* **(b)** Is the converse true? (Consider the dual numbers `A = k[x]/x²`.)

We encode `ρ̃` by its coefficient sequence `coeff : ℕ → (A →ₗ[k] End_k V)`. The condition
`ρ̃(ab) = ρ̃(a)ρ̃(b)` becomes, coefficient by coefficient,
`ρₙ(ab) = ∑_{i+j=n} ρᵢ(a) ∘ ρⱼ(b)` (Cauchy product). Two deformations are isomorphic when a
power series `b(t)` with `b₀ = id` intertwines them: `b ρ̃ = ρ̃' b` coefficientwise. The base
representation is `ρ₀ = ρ`, the bundled action `A →ₗ[k] End_k V`.

`Ext¹(V, V) = 0` reuses `Etingof.Problem3_9_1.Ext1`, phrased as `Subsingleton (Ext1 …)`.

The deformation data (`FormalDeformation`, the constant deformation, the
isomorphism relation) is constructed and part (a) is proved. Part (b) has a negative answer:
for the augmentation representation of the dual numbers on a one-dimensional space, every
formal deformation is constant, while its self-`Ext¹` is nonzero.
-/

namespace Etingof.Problem3_9_4

open Etingof.Problem3_9_1 (Ext1)

variable (k : Type*) (A : Type*) (V : Type*)
  [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The base representation `ρ₀ = ρ`, the action of `A` on `V` bundled as a `k`-linear map
`A →ₗ[k] End_k V`, constructed via `Algebra.lsmul`. -/
noncomputable def baseRho : A →ₗ[k] (V →ₗ[k] V) :=
  (Algebra.lsmul k k V).toLinearMap

/-- A **formal deformation** of the representation `V`: a sequence of `k`-linear maps
`ρₙ : A →ₗ[k] End_k V` with `ρ₀` the base representation and satisfying the Cauchy-product
multiplicativity `ρₙ(ab) = ∑_{i+j=n} ρᵢ(a) ∘ ρⱼ(b)` encoding `ρ̃(ab) = ρ̃(a)ρ̃(b)`. -/
structure FormalDeformation where
  /-- The coefficient maps `ρₙ`. -/
  coeff : ℕ → (A →ₗ[k] (V →ₗ[k] V))
  /-- `ρ₀ = ρ` is the base representation. -/
  base_eq : coeff 0 = baseRho k A V
  /-- `ρ̃(ab) = ρ̃(a)ρ̃(b)`, coefficient by coefficient. -/
  isMul : ∀ (a b : A) (n : ℕ),
    coeff n (a * b)
      = ∑ p ∈ Finset.antidiagonal n, (coeff p.1 a).comp (coeff p.2 b)

/-- The **trivial (constant) deformation** `ρ̃ = ρ`: `ρ₀ = ρ` and `ρₙ = 0` for `n ≥ 1`. The
coefficient data is constructed and the multiplicativity obligation is proved. -/
noncomputable def constDeformation : FormalDeformation k A V where
  coeff n := if n = 0 then baseRho k A V else 0
  base_eq := by simp
  isMul := by
    intro a b n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      -- `baseRho` is multiplicative: `ρ(ab) = ρ(a) ∘ ρ(b)`.
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      ext v
      change (a * b) • v = a • b • v
      exact mul_smul a b v
    · -- For `n ≥ 1`, `coeff n = 0` and every antidiagonal summand vanishes.
      rw [if_neg hn.ne', LinearMap.zero_apply]
      symm
      refine Finset.sum_eq_zero ?_
      rintro ⟨i, j⟩ hp
      rw [Finset.mem_antidiagonal] at hp
      rcases Nat.eq_zero_or_pos i with hi | hi
      · have hj : j ≠ 0 := by omega
        simp [hj]
      · simp [hi.ne']

/-- Two deformations `D`, `D'` are **isomorphic** when there is a power series
`b(t) = 1 + b₁t + ⋯` with `b₀ = id` intertwining them: `b ρ̃ = ρ̃' b`, i.e.
`∑_{i+j=n} bᵢ ∘ ρⱼ(a) = ∑_{i+j=n} ρ'ᵢ(a) ∘ bⱼ` for all `a, n`. -/
def IsIsomorphic (D D' : FormalDeformation k A V) : Prop :=
  ∃ b : ℕ → (V →ₗ[k] V), b 0 = LinearMap.id ∧
    ∀ (a : A) (n : ℕ),
      ∑ p ∈ Finset.antidiagonal n, (b p.1).comp (D.coeff p.2 a)
        = ∑ p ∈ Finset.antidiagonal n, (D'.coeff p.1 a).comp (b p.2)

/-- A deformation is **trivial** if it is isomorphic to the constant deformation `ρ`. -/
def IsTrivial (D : FormalDeformation k A V) : Prop :=
  IsIsomorphic k A V D (constDeformation k A V)

/-- Every formal deformation is isomorphic to itself, using the constant identity
intertwiner. -/
theorem isIsomorphic_refl (D : FormalDeformation k A V) :
    IsIsomorphic k A V D D := by
  let b : ℕ → Module.End k V := fun n => if n = 0 then LinearMap.id else 0
  refine ⟨b, by simp [b], ?_⟩
  intro a n
  have hleft :
      ∑ p ∈ Finset.antidiagonal n, (b p.1).comp (D.coeff p.2 a) = D.coeff n a := by
    rw [Finset.sum_eq_single_of_mem (0, n) (by simp [Finset.mem_antidiagonal])]
    · simp [b]
    · rintro ⟨i, j⟩ hmem hne
      have hi : i ≠ 0 := by
        rintro rfl
        rw [Finset.mem_antidiagonal] at hmem
        apply hne
        simp_all
      simp [b, hi]
  have hright :
      ∑ p ∈ Finset.antidiagonal n, (D.coeff p.1 a).comp (b p.2) = D.coeff n a := by
    rw [Finset.sum_eq_single_of_mem (n, 0) (by simp [Finset.mem_antidiagonal])]
    · simp [b]
    · rintro ⟨i, j⟩ hmem hne
      have hj : j ≠ 0 := by
        rintro rfl
        rw [Finset.mem_antidiagonal] at hmem
        apply hne
        simp_all
      simp [b, hj]
  rw [hleft, hright]

/-! ## Construction of the trivialising intertwiner

We prove Problem 3.9.4(a) by building the intertwiner `b(t) = 1 + b₁t + ⋯` order by order.
Writing `E = End_k V` (a ring under composition), the deformation is packaged as the power
series `ρ̃(t)(a) = ∑ₙ ρₙ(a) tⁿ ∈ E⟦t⟧`; deformation multiplicativity becomes
`ρ̃(t)(ac) = ρ̃(t)(a) · ρ̃(t)(c)`. The trivialisation equation is, order by order,
`Cₙ(a) := ∑_{i+j=n} bᵢ ∘ ρⱼ(a) = ρ(a) ∘ bₙ`. At each order the obstruction
`gₙ(a) = ∑_{i<n} bᵢ ∘ ρ_{n-i}(a)` is a 1-cocycle (using the lower-order equations and
associativity of the Cauchy product), so `Ext¹(V,V) = 0` makes it the coboundary of some
`bₙ`, which closes the induction. -/

section Construction

open Etingof.Problem3_9_1

variable {k A V}
variable (D : FormalDeformation k A V)

/-- `ρ(ac) = ρ(a) ∘ ρ(c)`: the base representation is multiplicative. -/
lemma baseRho_mul (a c : A) :
    baseRho k A V (a * c) = baseRho k A V a * baseRho k A V c := by
  ext v
  change (a * c) • v = a • c • v
  exact mul_smul a c v

/-- Explicit value of the coboundary `dX` at an algebra element:
`dX(a) = ρ(a) ∘ X − X ∘ ρ(a)`. -/
lemma coboundaryOf_apply (X : Module.End k V) (a : A) :
    coboundaryOf k A V V X a = baseRho k A V a * X - X * baseRho k A V a := by
  ext w
  simp only [coboundaryOf, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.llcomp_apply,
    LinearMap.flip_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_coe, Module.End.mul_apply,
    baseRho]

lemma coboundaryOf_add (X Y : Module.End k V) :
    coboundaryOf k A V V (X + Y) = coboundaryOf k A V V X + coboundaryOf k A V V Y := by
  refine LinearMap.ext fun a => ?_
  simp only [coboundaryOf_apply, LinearMap.add_apply, mul_add, add_mul]
  abel

lemma coboundaryOf_smul (c : k) (X : Module.End k V) :
    coboundaryOf k A V V (c • X) = c • coboundaryOf k A V V X := by
  refine LinearMap.ext fun a => ?_
  simp only [coboundaryOf_apply, LinearMap.smul_apply, mul_smul_comm, smul_mul_assoc, smul_sub]

lemma coboundaryOf_zero : coboundaryOf k A V V (0 : Module.End k V) = 0 := by
  refine LinearMap.ext fun a => ?_
  simp [coboundaryOf_apply]

/-- Every element of the coboundary subspace is a coboundary `dX`
(the coboundary map is linear, so its range is already a submodule). -/
lemma exists_of_mem_coboundaries {g : A →ₗ[k] Module.End k V}
    (hg : g ∈ coboundaries k A V V) : ∃ X, coboundaryOf k A V V X = g := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
  · rintro f ⟨X, rfl⟩; exact ⟨X, rfl⟩
  · exact ⟨0, coboundaryOf_zero⟩
  · rintro f₁ f₂ _ _ ⟨X, rfl⟩ ⟨Y, rfl⟩; exact ⟨X + Y, coboundaryOf_add X Y⟩
  · rintro c f _ ⟨X, rfl⟩; exact ⟨c • X, coboundaryOf_smul c X⟩

/-- With `Ext¹(V,V) = 0`, every 1-cocycle is a coboundary. -/
lemma exists_coboundary_of_cocycle (hExt : Subsingleton (Ext1 k A V V))
    (g : A →ₗ[k] Module.End k V) (hg : IsCocycle k A V V g) :
    ∃ X, coboundaryOf k A V V X = g := by
  have hmem : g ∈ coboundaries k A V V := by
    have h0 : (Submodule.Quotient.mk (⟨g, hg⟩ : cocycles k A V V) : Ext1 k A V V) = 0 :=
      Subsingleton.elim _ _
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_comap).mp h0
  exact exists_of_mem_coboundaries hmem

/-- `ρ̃(t)(a) = ∑ₙ ρₙ(a) tⁿ`, the deformation as an `E⟦t⟧` power series (`E = End_k V`). -/
noncomputable def defSeries (a : A) : PowerSeries (Module.End k V) :=
  PowerSeries.mk fun n => D.coeff n a

@[simp] lemma defSeries_coeff (a : A) (n : ℕ) :
    PowerSeries.coeff n (defSeries D a) = D.coeff n a := by
  simp [defSeries]

/-- Deformation multiplicativity as an identity of power series. -/
lemma defSeries_mul (a c : A) :
    defSeries D (a * c) = defSeries D a * defSeries D c := by
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [defSeries_coeff]
  rw [D.isMul a c n]
  simp only [← Module.End.mul_eq_comp]

/-- Obstruction linear map at order `m` from a length-`m` prefix `prev = (b₀,…,b_{m-1})`:
`g(a) = ∑_{i<m} bᵢ ∘ ρ_{m-i}(a)`. -/
noncomputable def obstr {m : ℕ} (prev : Fin m → Module.End k V) :
    A →ₗ[k] Module.End k V :=
  ∑ i : Fin m, (LinearMap.llcomp k V V V (prev i)).comp (D.coeff (m - i))

lemma obstr_apply {m : ℕ} (prev : Fin m → Module.End k V) (a : A) :
    obstr D prev a = ∑ i : Fin m, prev i * D.coeff (m - i) a := by
  simp only [obstr, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.llcomp_apply', ← Module.End.mul_eq_comp]

open Classical in
/-- The next coefficient `b_m`: a chosen `X` with `dX = g` when one exists (else `0`). -/
noncomputable def nextCoeff {m : ℕ} (prev : Fin m → Module.End k V) : Module.End k V :=
  if h : ∃ X, coboundaryOf k A V V X = obstr D prev then h.choose else 0

/-- Length-`(n+1)` prefix `(b₀,…,bₙ)` of the intertwiner, built recursively. -/
noncomputable def bVec : (n : ℕ) → Fin (n + 1) → Module.End k V
  | 0 => fun _ => 1
  | (n + 1) => Fin.snoc (bVec n) (nextCoeff D (bVec n))

/-- The intertwiner coefficient sequence `n ↦ bₙ`. -/
noncomputable def bSeq (n : ℕ) : Module.End k V := bVec D n (Fin.last n)

lemma bSeq_zero : bSeq D 0 = 1 := rfl

lemma bSeq_succ (n : ℕ) : bSeq D (n + 1) = nextCoeff D (bVec D n) := by
  simp only [bSeq, bVec, Fin.snoc_last]

/-- Coherence: the prefix `bVec D n` restricts to the global sequence `bSeq D`. -/
lemma bVec_eq_bSeq (n : ℕ) (i : Fin (n + 1)) : bVec D n i = bSeq D (i : ℕ) := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    refine Fin.lastCases ?_ ?_ i
    · simp only [bVec, Fin.snoc_last, Fin.val_last, bSeq_succ]
    · intro j
      rw [bVec, Fin.snoc_castSucc, ih j, Fin.val_castSucc]

/-- The chosen coefficient really trivialises the obstruction (when existence holds). -/
lemma coboundaryOf_bSeq_succ (n : ℕ)
    (h : ∃ X, coboundaryOf k A V V X = obstr D (bVec D n)) :
    coboundaryOf k A V V (bSeq D (n + 1)) = obstr D (bVec D n) := by
  rw [bSeq_succ, nextCoeff, dif_pos h]
  exact h.choose_spec

/-- The order-`n` value `Cₙ(a) = ∑_{i+j=n} bᵢ ∘ ρⱼ(a)`. -/
noncomputable def Cc (n : ℕ) (a : A) : Module.End k V :=
  ∑ p ∈ Finset.antidiagonal n, bSeq D p.1 * D.coeff p.2 a

/-- The order-`n` obstruction value `gₙ(a) = ∑_{i<n} bᵢ ∘ ρ_{n-i}(a)`. -/
noncomputable def gv (n : ℕ) (a : A) : Module.End k V :=
  ∑ i ∈ Finset.range n, bSeq D i * D.coeff (n - i) a

lemma Cc_eq_coeff (n : ℕ) (a : A) :
    Cc D n a = PowerSeries.coeff n (PowerSeries.mk (bSeq D) * defSeries D a) := by
  rw [PowerSeries.coeff_mul]
  simp only [Cc, PowerSeries.coeff_mk, defSeries_coeff]

/-- `Cₙ(ac) = ∑_{r+q=n} Cᵣ(a) ∘ ρ_q(c)`: associativity of the Cauchy product. -/
lemma Cc_mul (n : ℕ) (a c : A) :
    Cc D n (a * c) = ∑ p ∈ Finset.antidiagonal n, Cc D p.1 a * D.coeff p.2 c := by
  rw [Cc_eq_coeff, defSeries_mul, ← mul_assoc, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Cc_eq_coeff, defSeries_coeff]

/-- Split off the top term: `Cₙ(a) = gₙ(a) + bₙ ∘ ρ(a)`. -/
lemma Cc_eq_gv_add (n : ℕ) (a : A) :
    Cc D n a = gv D n a + bSeq D n * baseRho k A V a := by
  rw [Cc, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ, gv,
    Nat.sub_self, D.base_eq]

lemma obstr_bVec_apply (n : ℕ) (a : A) :
    obstr D (bVec D n) a = gv D (n + 1) a := by
  rw [obstr_apply, gv, ← Fin.sum_univ_eq_sum_range fun i => bSeq D i * D.coeff (n + 1 - i) a]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bVec_eq_bSeq]

/-- The obstruction is a 1-cocycle, given the lower-order trivialisation equations. -/
lemma gv_cocycle (n : ℕ) (ih : ∀ r < n, ∀ a, Cc D r a = baseRho k A V a * bSeq D r)
    (a c : A) :
    gv D n (a * c) = baseRho k A V a * gv D n c + gv D n a * baseRho k A V c := by
  have hCc : Cc D n (a * c)
      = baseRho k A V a * gv D n c + Cc D n a * baseRho k A V c := by
    rw [Cc_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.sub_self, D.base_eq, gv, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [ih r hr a, mul_assoc]
  have hgv : gv D n (a * c) = Cc D n (a * c) - bSeq D n * baseRho k A V (a * c) := by
    rw [Cc_eq_gv_add]; abel
  rw [hgv, hCc, baseRho_mul, Cc_eq_gv_add]
  noncomm_ring

/-- **Trivialisation equation.** `Cₙ(a) = ρ(a) ∘ bₙ` for every order `n`. -/
lemma star (hExt : Subsingleton (Ext1 k A V V)) :
    ∀ n a, Cc D n a = baseRho k A V a * bSeq D n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a
    match n, ih with
    | 0, _ =>
      rw [Cc_eq_gv_add, gv, bSeq_zero]
      simp
    | (m + 1), ih =>
      -- The obstruction at order `m+1` is a cocycle, hence a coboundary `dX = d bₘ₊₁`.
      have hcoc : IsCocycle k A V V (obstr D (bVec D m)) := by
        intro a' c'
        rw [obstr_bVec_apply, obstr_bVec_apply, obstr_bVec_apply,
          ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
        exact gv_cocycle D (m + 1) (fun r hr => ih r hr) a' c'
      obtain ⟨X, hX⟩ := exists_coboundary_of_cocycle hExt _ hcoc
      have hcob : coboundaryOf k A V V (bSeq D (m + 1)) = obstr D (bVec D m) :=
        coboundaryOf_bSeq_succ D m ⟨X, hX⟩
      have key := congrArg (fun f => f a) hcob
      simp only [coboundaryOf_apply, obstr_bVec_apply] at key
      -- `key : ρ(a) bₘ₊₁ − bₘ₊₁ ρ(a) = gₘ₊₁(a)`
      rw [Cc_eq_gv_add, ← key]
      abel

end Construction

/-- **Problem 3.9.4(a).** If `Ext¹(V, V) = 0`, every formal deformation of `ρ` is trivial. -/
theorem isTrivial_of_ext1_subsingleton
    (hExt : Subsingleton (Ext1 k A V V)) (D : FormalDeformation k A V) :
    IsTrivial k A V D := by
  refine ⟨bSeq D, ?_, ?_⟩
  · rw [bSeq_zero]; exact Module.End.one_eq_id
  · intro a n
    have hL : ∑ p ∈ Finset.antidiagonal n, (bSeq D p.1).comp (D.coeff p.2 a)
        = baseRho k A V a * bSeq D n := by
      rw [← star D hExt n a, Cc]
      exact Finset.sum_congr rfl fun p _ =>
        (Module.End.mul_eq_comp (bSeq D p.1) (D.coeff p.2 a)).symm
    have hR : ∑ p ∈ Finset.antidiagonal n,
          ((constDeformation k A V).coeff p.1 a).comp (bSeq D p.2)
        = baseRho k A V a * bSeq D n := by
      rw [Finset.sum_eq_single_of_mem (0, n) (by simp [Finset.mem_antidiagonal])]
      · change ((if (0 : ℕ) = 0 then baseRho k A V else 0) a).comp (bSeq D n) = _
        rw [if_pos rfl, Module.End.mul_eq_comp]
      · rintro ⟨i, j⟩ hmem hne
        rw [Finset.mem_antidiagonal] at hmem
        have hi : i ≠ 0 := by rintro rfl; exact hne (by simp_all)
        change ((if i = 0 then baseRho k A V else 0) a).comp (bSeq D j) = 0
        rw [if_neg hi, LinearMap.zero_apply, LinearMap.zero_comp]
    rw [hL, hR]

/-- The **converse to (a)** for a fixed representation `V`: if every formal deformation of
`V` is trivial, then `Ext¹(V, V) = 0`. -/
def ConverseHolds : Prop :=
  (∀ D : FormalDeformation k A V, IsTrivial k A V D) → Subsingleton (Ext1 k A V V)

/-- **Problem 3.9.4(b).** Is the converse to (a) true? The suggested test case is the
algebra of dual numbers `A = k[x]/x²` (`DualNumber k`). This proposition is the converse
specialised to a representation `V` of the dual numbers; the exercise asks whether it holds
(the answer is expected to involve obstructions to extending first-order deformations). -/
def Problem3_9_4b (V : Type*)
    [AddCommGroup V] [Module k V] [Module (DualNumber k) V]
    [IsScalarTower k (DualNumber k) V] : Prop :=
  ConverseHolds k (DualNumber k) V

/-! ## Part (b): the dual-numbers counterexample

The dual numbers act on the one-dimensional space `k` through the augmentation
`a ↦ a.fst`; equivalently, `DualNumber.eps` acts by zero. A deformation sends `eps` to a
square-zero power series in `Endₖ(k)`. Evaluation at `1` identifies `Endₖ(k)` with `k`, so this
series vanishes because `k⟦X⟧` is a domain. The image of `1` is similarly an idempotent power
series with constant coefficient `1`, hence is `1`. Thus every positive deformation coefficient
vanishes.

On the other hand, the second coordinate `a ↦ a.snd` is a nonzero self-extension cocycle. Every
coboundary is zero because endomorphisms of a one-dimensional scalar representation commute with
the action. Therefore `Ext¹(k,k)` is nontrivial although all formal deformations are trivial. -/

section DualNumberCounterexample

variable (K : Type*) [Field K]

/-- The augmentation algebra structure of the dual numbers on their base field:
`a • x = a.fst * x`, so the nilpotent generator acts by zero.

This is deliberately a named definition rather than a global instance, since a field may carry
other algebra structures over a trivial square-zero extension. The counterexample section installs
it only locally. -/
@[reducible] noncomputable def dualNumberAugmentationAlgebra : Algebra (DualNumber K) K :=
  TrivSqZeroExt.algebraBase K K

local instance : Algebra (DualNumber K) K :=
  TrivSqZeroExt.algebraBase K K

/-- Evaluate a one-dimensional endomorphism at `1`, as an algebra map. -/
noncomputable def endScalar : Module.End K K →ₐ[K] K where
  toFun f := f 1
  map_one' := rfl
  map_mul' f g := by
    change f (g 1) = f 1 * g 1
    calc
      f (g 1) = f ((g 1) • (1 : K)) := by simp
      _ = (g 1) • f 1 := by rw [map_smul]
      _ = f 1 * g 1 := by simp [mul_comm]
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by simp

lemma endScalar_injective : Function.Injective (endScalar K) := by
  intro f g h
  change f 1 = g 1 at h
  apply LinearMap.ext
  intro x
  calc
    f x = f (x • (1 : K)) := by simp
    _ = x • f 1 := by rw [map_smul]
    _ = x • g 1 := by rw [h]
    _ = g (x • (1 : K)) := by rw [map_smul]
    _ = g x := by simp

/-- The scalar-valued power series obtained by evaluating every endomorphism coefficient at
`1`. -/
noncomputable def scalarSeries (D : FormalDeformation K (DualNumber K) K)
    (a : DualNumber K) : PowerSeries K :=
  PowerSeries.map (endScalar K).toRingHom (defSeries D a)

@[simp] lemma scalarSeries_coeff (D : FormalDeformation K (DualNumber K) K)
    (a : DualNumber K) (n : ℕ) :
    PowerSeries.coeff n (scalarSeries K D a) = endScalar K (D.coeff n a) := by
  simp [scalarSeries, defSeries_coeff]

/-- The deformed action of the nilpotent generator is zero: its scalar power series is
square-zero in the domain `K⟦X⟧`. -/
lemma scalarSeries_eps_zero (D : FormalDeformation K (DualNumber K) K) :
    scalarSeries K D DualNumber.eps = 0 := by
  have hsq : defSeries D DualNumber.eps * defSeries D DualNumber.eps = 0 := by
    rw [← defSeries_mul]
    simp only [DualNumber.eps_mul_eps]
    ext n
    simp [defSeries]
  have hsq' := congrArg (PowerSeries.map (endScalar K).toRingHom) hsq
  simp only [map_mul, map_zero] at hsq'
  exact eq_zero_of_mul_self_eq_zero hsq'

lemma scalarSeries_one_coeff_zero (D : FormalDeformation K (DualNumber K) K) :
    PowerSeries.coeff 0 (scalarSeries K D 1) = 1 := by
  rw [scalarSeries_coeff, D.base_eq]
  simp [endScalar, baseRho]

/-- The deformed action of `1` is the constant power series `1`. Although
`FormalDeformation` has no separate unitality field, multiplicativity makes this series
idempotent, and its constant coefficient rules out the zero idempotent. -/
lemma scalarSeries_one (D : FormalDeformation K (DualNumber K) K) :
    scalarSeries K D 1 = 1 := by
  let U := scalarSeries K D 1
  have hidem : U * U = U := by
    change scalarSeries K D 1 * scalarSeries K D 1 = scalarSeries K D 1
    simp only [scalarSeries, ← map_mul, ← defSeries_mul, one_mul]
  have hfac : U * (U - 1) = 0 := by rw [mul_sub, hidem, mul_one, sub_self]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with hU | hU
  · have hcoeff := congrArg (PowerSeries.coeff 0) hU
    rw [scalarSeries_one_coeff_zero] at hcoeff
    simp at hcoeff
  · exact sub_eq_zero.mp hU

lemma coeff_eps_zero (D : FormalDeformation K (DualNumber K) K) (n : ℕ) :
    D.coeff n DualNumber.eps = 0 := by
  apply endScalar_injective K
  change endScalar K (D.coeff n DualNumber.eps) = endScalar K 0
  rw [← scalarSeries_coeff]
  simp [scalarSeries_eps_zero]

lemma coeff_one_succ_zero (D : FormalDeformation K (DualNumber K) K) (n : ℕ) :
    D.coeff (n + 1) 1 = 0 := by
  apply endScalar_injective K
  change endScalar K (D.coeff (n + 1) 1) = endScalar K 0
  rw [← scalarSeries_coeff]
  simp [scalarSeries_one]

/-- Every positive coefficient of a deformation of the augmentation representation vanishes. -/
theorem dualNumber_coeff_succ_eq_zero
    (D : FormalDeformation K (DualNumber K) K) (n : ℕ) :
    D.coeff (n + 1) = 0 := by
  apply LinearMap.ext
  intro a
  rw [← a.inl_fst_add_inr_snd_eq, map_add]
  have hinl : TrivSqZeroExt.inl a.fst = a.fst • (1 : DualNumber K) := by
    ext <;> simp
  rw [hinl, DualNumber.inr_eq_smul_eps, map_smul, map_smul,
    coeff_one_succ_zero, coeff_eps_zero, smul_zero, smul_zero, add_zero]
  simp

/-- Every deformation of the augmentation representation is literally the constant deformation,
not merely isomorphic to it. -/
theorem dualNumber_deformation_eq_const
    (D : FormalDeformation K (DualNumber K) K) :
    D = constDeformation K (DualNumber K) K := by
  cases D with
  | mk coeff base_eq isMul =>
      rw [FormalDeformation.mk.injEq]
      funext n
      cases n with
      | zero =>
          rw [base_eq]
          simp [constDeformation]
      | succ n =>
          exact dualNumber_coeff_succ_eq_zero K
            ({ coeff := coeff, base_eq := base_eq, isMul := isMul } :
              FormalDeformation K (DualNumber K) K) n

/-- Every formal deformation of the one-dimensional augmentation representation is trivial. -/
theorem dualNumber_all_deformations_trivial :
    ∀ D : FormalDeformation K (DualNumber K) K,
      IsTrivial K (DualNumber K) K D := by
  intro D
  rw [dualNumber_deformation_eq_const K D]
  exact isIsomorphic_refl K (DualNumber K) K _

/-- The second-coordinate derivation `a ↦ a.snd`, regarded as an endomorphism-valued
one-cocycle of the augmentation representation. -/
noncomputable def epsCocycle :
    DualNumber K →ₗ[K] Module.End K K :=
  (Algebra.lsmul K K K).toLinearMap.comp (TrivSqZeroExt.sndHom K K)

lemma epsCocycle_isCocycle :
    Etingof.Problem3_9_1.IsCocycle K (DualNumber K) K K (epsCocycle K) := by
  intro a b
  apply LinearMap.ext
  intro x
  simp only [epsCocycle, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply]
  have hlsmul (c y : K) :
      ((Algebra.lsmul K K K).toLinearMap c) y = c * y := rfl
  have hsnd (c : DualNumber K) :
      (TrivSqZeroExt.sndHom K K) c = c.snd := rfl
  have hrho (c : DualNumber K) (y : K) :
      Etingof.Problem3_9_1.rho K (DualNumber K) K c y = c.fst * y := rfl
  rw [hlsmul, hsnd, hrho, hlsmul, hsnd, hrho, hlsmul, hsnd, DualNumber.snd_mul]
  ring

lemma coboundary_eq_zero (X : Module.End K K) :
    Etingof.Problem3_9_1.coboundaryOf K (DualNumber K) K K X = 0 := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro x
  rw [Etingof.Problem3_9_1.coboundaryOf_apply]
  change a.fst * X x - X (a.fst * x) = 0
  rw [show a.fst * x = a.fst • x by rfl, map_smul]
  simp

lemma epsCocycle_ne_zero : epsCocycle K ≠ 0 := by
  intro h
  have h' := LinearMap.congr_fun (LinearMap.congr_fun h DualNumber.eps) 1
  simp [epsCocycle] at h'

lemma epsCocycle_not_mem_coboundaries :
    epsCocycle K ∉
      Etingof.Problem3_9_1.coboundaries K (DualNumber K) K K := by
  intro hmem
  rw [Etingof.Problem3_9_1.mem_coboundaries_iff] at hmem
  obtain ⟨X, hX⟩ := hmem
  apply epsCocycle_ne_zero K
  exact hX.symm.trans (coboundary_eq_zero K X)

/-- The augmentation representation has a nonzero self-extension, represented by
`epsCocycle`. -/
theorem dualNumber_ext1_not_subsingleton :
    ¬ Subsingleton (Ext1 K (DualNumber K) K K) := by
  letI : AddCommGroup (Etingof.Problem3_9_1.cocycles K (DualNumber K) K K) :=
    @Submodule.addCommGroup K
      (DualNumber K →ₗ[K] Module.End K K) _ _ _
      (Etingof.Problem3_9_1.cocycles K (DualNumber K) K K)
  intro h
  rw [Etingof.Problem3_9_1.Ext1, Submodule.Quotient.subsingleton_iff,
    Submodule.eq_top_iff'] at h
  have hmem := h
    (⟨epsCocycle K, epsCocycle_isCocycle K⟩ :
      Etingof.Problem3_9_1.cocycles K (DualNumber K) K K)
  exact epsCocycle_not_mem_coboundaries K ((Submodule.mem_comap).mp hmem)

/-- **Problem 3.9.4(b), negative answer.** For the augmentation representation of the dual
numbers on `K`, every formal deformation is trivial, but `Ext¹(K,K)` is nonzero. Hence the
converse to part (a) is false. -/
theorem not_problem3_9_4b_dualNumber :
    ¬ Problem3_9_4b K K := by
  intro h
  exact dualNumber_ext1_not_subsingleton K (h (dualNumber_all_deformations_trivial K))

end DualNumberCounterexample

end Etingof.Problem3_9_4
