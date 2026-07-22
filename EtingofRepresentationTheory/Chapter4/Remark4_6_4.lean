import Mathlib
import EtingofRepresentationTheory.Chapter2.Example2_3_14

/-!
# Remark 4.6.4: Infinite groups may lack a unitary structure

Theorem 4.6.3 shows that a finite dimensional *unitary* representation of any group is completely
reducible. Remark 4.6.4 observes that, for an infinite group `G`, a finite dimensional
representation may fail to admit a unitary structure: there exist finite dimensional
representations (for example for `G = ℤ`) that are **indecomposable but not irreducible**, hence
not completely reducible, hence (by Theorem 4.6.3) not unitarizable.

The witness is the classical one: the infinite group `G = ℤ` (written multiplicatively as
`Multiplicative ℤ`) acting on `ℂ²` through powers of the unipotent Jordan block
`J_{1,2} = [[1,1],[0,1]]`. Because `J_{1,2}` is unipotent it is invertible, so its powers form a
genuine group representation of `ℤ`. The `ℤ`-invariant subspaces of `ℂ²` are exactly the
`J_{1,2}`-invariant subspaces, and the analysis of `Etingof.Example_2_3_14` applies verbatim:

* every nonzero invariant subspace contains the eigenvector `e₀` (`e0_mem_of_invariant`), so two
  nonzero invariant subspaces always meet — the representation is **indecomposable**;
* the eigenline `ℂ·e₀` is a proper nonzero invariant subspace — the representation is **not
  irreducible**.

## Mathlib correspondence

We use Mathlib's `Representation`, `Subrepresentation`, and `Representation.IsIrreducible`
(`= IsSimpleOrder (Subrepresentation ρ)`). Indecomposability is not in Mathlib; we record it as a
local definition mirroring `Etingof.Example_2_3_14.IsIndecomposable`.
-/

open Etingof.Example_2_3_14

namespace Etingof.Remark4_6_4

/-- A representation is *indecomposable* if it has more than one subrepresentation and is not the
internal direct sum of two proper subrepresentations: any complementary pair of subrepresentations
has one of them trivial. -/
def IsIndecomposable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : Prop :=
  Nontrivial (Subrepresentation ρ) ∧
    ∀ S T : Subrepresentation ρ, IsCompl S T → S = ⊥ ∨ T = ⊥

/-- The shift `N` on `ℂ²` is `2`-nilpotent: `N² = 0`. -/
lemma shift_two_sq : (shift 2 : Module.End ℂ (Fin 2 → ℂ)) ^ 2 = 0 := by
  apply LinearMap.ext; intro v; funext i
  rw [shift_pow_apply, dif_neg (by omega)]
  simp

/-- The shift kills the eigenvector `e₀`. -/
lemma shift_two_e0 : shift 2 (e0 2 : Fin 2 → ℂ) = 0 := by
  funext i
  simp only [shift_apply, Pi.zero_apply]
  split
  · apply Pi.single_eq_of_ne
    intro hh; rw [Fin.ext_iff] at hh; simp at hh
  · rfl

/-- The Jordan block `J_{1,2}` as a unit of `Module.End ℂ ℂ²`. It is unipotent
(`J = 1 + N`, `N² = 0`), so its inverse is `1 - N`. -/
noncomputable def jUnit : (Module.End ℂ (Fin 2 → ℂ))ˣ where
  val := jordanBlock 1 2
  inv := 1 - shift 2
  val_inv := by
    have hjb : jordanBlock (1 : ℂ) 2 = 1 + shift 2 := by
      rw [jordanBlock, one_smul, ← Module.End.one_eq_id]
    have : jordanBlock (1 : ℂ) 2 * (1 - shift 2) = 1 - shift 2 ^ 2 := by rw [hjb]; noncomm_ring
    rw [this, shift_two_sq, sub_zero]
  inv_val := by
    have hjb : jordanBlock (1 : ℂ) 2 = 1 + shift 2 := by
      rw [jordanBlock, one_smul, ← Module.End.one_eq_id]
    have : (1 - shift 2) * jordanBlock (1 : ℂ) 2 = 1 - shift 2 ^ 2 := by rw [hjb]; noncomm_ring
    rw [this, shift_two_sq, sub_zero]

lemma jUnit_coe : (jUnit : Module.End ℂ (Fin 2 → ℂ)) = jordanBlock 1 2 := rfl

/-- `J_{1,2}` fixes the eigenvector `e₀` (its eigenvalue is `1`). -/
lemma jUnit_apply_e0 : (jUnit : Module.End ℂ (Fin 2 → ℂ)) (e0 2) = e0 2 := by
  rw [jUnit_coe, jordanBlock_e0, one_smul]

/-- The inverse `J_{1,2}⁻¹ = 1 - N` also fixes `e₀`. -/
lemma jUnit_inv_apply_e0 :
    ((jUnit⁻¹ : (Module.End ℂ (Fin 2 → ℂ))ˣ) : Module.End ℂ (Fin 2 → ℂ)) (e0 2) = e0 2 := by
  change (1 - shift 2 : Module.End ℂ (Fin 2 → ℂ)) (e0 2) = e0 2
  rw [LinearMap.sub_apply, shift_two_e0, Module.End.one_apply, sub_zero]

/-- **The representation of `ℤ` on `ℂ²` by powers of the Jordan block `J_{1,2}`.**
Realized as a monoid homomorphism `Multiplicative ℤ →* Module.End ℂ ℂ²` sending the generator to
`J_{1,2}`; this is well defined precisely because `J_{1,2}` is invertible. -/
noncomputable def repZ : Representation ℂ (Multiplicative ℤ) (Fin 2 → ℂ) :=
  (Units.coeHom _).comp (zpowersHom _ jUnit)

lemma repZ_apply (n : Multiplicative ℤ) :
    repZ n = ((jUnit ^ Multiplicative.toAdd n : (Module.End ℂ (Fin 2 → ℂ))ˣ) :
      Module.End ℂ (Fin 2 → ℂ)) := rfl

/-- The generator `1 ∈ ℤ` acts by the Jordan block `J_{1,2}`. -/
lemma repZ_ofAdd_one : repZ (Multiplicative.ofAdd (1 : ℤ)) = jordanBlock 1 2 := by
  rw [repZ_apply, toAdd_ofAdd, zpow_one, jUnit_coe]

/-- Every group element fixes the eigenvector `e₀`: `ρ(n) e₀ = e₀` for all `n ∈ ℤ`. -/
lemma repZ_fix_e0 (n : Multiplicative ℤ) : repZ n (e0 2 : Fin 2 → ℂ) = e0 2 := by
  rw [repZ_apply]
  generalize Multiplicative.toAdd n = m
  induction m using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, Module.End.one_apply]
  | succ k ih => rw [zpow_add_one, Units.val_mul, Module.End.mul_apply, jUnit_apply_e0, ih]
  | pred k ih => rw [zpow_sub_one, Units.val_mul, Module.End.mul_apply, jUnit_inv_apply_e0, ih]

/-- The eigenline `ℂ·e₀` as a subrepresentation of `repZ`: it is invariant because every group
element fixes `e₀`. -/
noncomputable def eigenLine : Subrepresentation repZ where
  toSubmodule := Submodule.span ℂ {(e0 2 : Fin 2 → ℂ)}
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_span_singleton] at hv ⊢
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, by rw [map_smul, repZ_fix_e0]⟩

lemma eigenLine_toSubmodule :
    eigenLine.toSubmodule = Submodule.span ℂ {(e0 2 : Fin 2 → ℂ)} := rfl

lemma eigenLine_ne_bot : eigenLine ≠ ⊥ := by
  intro h
  have h2 : eigenLine.toSubmodule = ⊥ := by rw [h]; rfl
  rw [eigenLine_toSubmodule, Submodule.span_singleton_eq_bot] at h2
  exact e0_ne_zero 2 h2

lemma eigenLine_ne_top : eigenLine ≠ ⊤ := by
  intro h
  have h2 : eigenLine.toSubmodule = ⊤ := by rw [h]; rfl
  have he1 : (Pi.single (1 : Fin 2) (1 : ℂ)) ∈ Submodule.span ℂ {(e0 2 : Fin 2 → ℂ)} := by
    rw [← eigenLine_toSubmodule, h2]; exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at he1
  obtain ⟨c, hc⟩ := he1
  have hco := congrFun hc (1 : Fin 2)
  rw [Pi.single_eq_same] at hco
  have hne : (1 : Fin 2) ≠ 0 := by decide
  simp only [e0, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hne, mul_zero] at hco
  exact one_ne_zero hco.symm

/-- **`repZ` is not irreducible.** The eigenline `ℂ·e₀` is a proper nonzero subrepresentation. -/
theorem repZ_not_irreducible : ¬ Representation.IsIrreducible repZ := by
  intro h
  haveI := h
  rcases eq_bot_or_eq_top eigenLine with hb | ht
  · exact eigenLine_ne_bot hb
  · exact eigenLine_ne_top ht

/-- A nonzero subrepresentation of `repZ` is `J_{1,2}`-invariant, hence contains `e₀`. -/
lemma e0_mem_of_ne_bot {S : Subrepresentation repZ} (hS : S ≠ ⊥) :
    (e0 2 : Fin 2 → ℂ) ∈ S.toSubmodule := by
  have hinv : ∀ m ∈ S.toSubmodule, jordanBlock (1 : ℂ) 2 m ∈ S.toSubmodule := by
    intro m hm
    have := S.apply_mem_toSubmodule (Multiplicative.ofAdd 1) hm
    rwa [repZ_ofAdd_one] at this
  have hbot : S.toSubmodule ≠ ⊥ := by
    intro h; exact hS (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
  exact e0_mem_of_invariant 1 2 hbot hinv

/-- **`repZ` is indecomposable.** Any two nonzero subrepresentations both contain `e₀`, so they
cannot be complementary. -/
theorem repZ_indecomposable : IsIndecomposable repZ := by
  refine ⟨⟨eigenLine, ⊥, eigenLine_ne_bot⟩, ?_⟩
  intro S T hcompl
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hS, hT⟩ := hcon
  have hSe0 : (e0 2 : Fin 2 → ℂ) ∈ S.toSubmodule := e0_mem_of_ne_bot hS
  have hTe0 : (e0 2 : Fin 2 → ℂ) ∈ T.toSubmodule := e0_mem_of_ne_bot hT
  have hmem : (e0 2 : Fin 2 → ℂ) ∈ (S ⊓ T).toSubmodule := by
    rw [Subrepresentation.toSubmodule_inf]; exact Submodule.mem_inf.mpr ⟨hSe0, hTe0⟩
  rw [hcompl.inf_eq_bot] at hmem
  rw [show (⊥ : Subrepresentation repZ).toSubmodule = (⊥ : Submodule ℂ (Fin 2 → ℂ)) from rfl,
    Submodule.mem_bot] at hmem
  exact e0_ne_zero 2 hmem

end Etingof.Remark4_6_4

open Etingof.Remark4_6_4 in
/-- **Remark 4.6.4.** For the infinite group `G = ℤ` there exists a finite dimensional complex
representation (on `ℂ²`, through powers of the Jordan block `J_{1,2}`) that is indecomposable but
not irreducible. Such a representation is therefore not completely reducible, and by
Theorem 4.6.3 cannot admit a unitary structure. -/
theorem Etingof.Remark4_6_4 :
    Infinite (Multiplicative ℤ) ∧
      ∃ ρ : Representation ℂ (Multiplicative ℤ) (Fin 2 → ℂ),
        IsIndecomposable ρ ∧ ¬ Representation.IsIrreducible ρ :=
  ⟨inferInstance, repZ, repZ_indecomposable, repZ_not_irreducible⟩
