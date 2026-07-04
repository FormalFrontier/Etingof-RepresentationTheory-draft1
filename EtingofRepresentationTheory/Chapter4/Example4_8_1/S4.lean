import EtingofRepresentationTheory.Chapter4.Example4_8_1.Q8

/-!
# Example 4.8.1 — the `S₄` character table

Split out of `Example4_8_1.lean` so each character-table section elaborates in its own
process: the combined file accumulated ~13 GB of kernel-`decide` memory, OOM-killing the
16 GB CI runner (issue #5852).  See `Example4_8_1.lean` for the umbrella and the
public wrappers.
-/

namespace Etingof.Example4_8_1

open Q5
/-! ## `S₄`

Classes (in order): `Id` (1), transpositions `(12)` (6), double transpositions `(12)(34)`
(3), 3-cycles `(123)` (8), 4-cycles `(1234)` (6); `|S₄| = 24`.  Irreducibles `ℂ₊` (trivial),
`ℂ₋` (sign), `ℂ²`, `ℂ³₊` (cube-rotation / standard), `ℂ³₋` (standard ⊗ sign). -/

/-- Class sizes of `S₄`. -/
def sizesS4 : Fin 5 → ℚ := ![1, 6, 3, 8, 6]

/-- Character table of `S₄`, exactly as in the book.  The `ℂ³₊` row `(3, -1, -1, 0, 1)` is
the cube-rotation character (`trace = 1 + 2cos φ`); `ℂ³₋` is `ℂ³₊ ⊗ sign`. -/
def chiS4 : Fin 5 → Fin 5 → Q5 :=
  ![![1,  1,  1,  1,  1],
    ![1, -1,  1,  1, -1],
    ![2,  0,  2, -1,  0],
    ![3, -1, -1,  0,  1],
    ![3,  1, -1,  0, -1]]

/-! ### Genuine `S₄` character table via real representations and traces

Each row of `chiS4` is realised as the character (trace) of an actual representation of
`S₄ = Equiv.Perm (Fin 4)`: the trivial `ℂ₊`, the sign `ℂ₋`, the standard deleted permutation
representation `ℂ³₋`, its sign twist `ℂ³₊ = ℂ³₋ ⊗ sign`, and the 2-dimensional `ℂ²` obtained
from the conjugation action of `S₄` on the three pair-partitions of `Fin 4` (the surjection
`S₄ → S₃` with kernel the Klein four-group).  Simplicity of each is proved via
`FDRep.simple_iff_char_is_norm_one` (the norm-one character sum, evaluated by honest `decide`
over the 24 group elements — no `native_decide`), the five rows are pairwise distinct
characters, hence the representations are pairwise non-isomorphic, and together with the five
conjugacy classes this exhibits the complete character table. -/

namespace S4

open CategoryTheory MonoidalCategory Module

noncomputable section

-- The generic deleted-permutation-rep helpers carry `[Fintype α] [DecidableEq α]` instances
-- that several specialised lemmas do not mention in their statement; silence the style linters.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.dupNamespace false

/-! ## Carrier-level helpers (depend only on the index type `α`) -/
section Carrier
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The sum functional `(α → ℂ) →ₗ[ℂ] ℂ`. -/
def sumLM : (α → ℂ) →ₗ[ℂ] ℂ := ∑ a, LinearMap.proj a

@[simp] lemma sumLM_apply (f : α → ℂ) : sumLM f = ∑ a, f a := by
  simp [sumLM, Finset.sum_apply]

/-- The all-ones vector. -/
def onesVecM : α → ℂ := fun _ => 1

lemma onesVecM_ne_zero [Nonempty α] : (onesVecM : α → ℂ) ≠ 0 := by
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  intro h; have := congrFun h a; simp [onesVecM] at this

/-- The line of constant vectors. -/
def constLineM : Submodule ℂ (α → ℂ) := Submodule.span ℂ {(onesVecM : α → ℂ)}

lemma mem_constLineM {x : α → ℂ} : x ∈ (constLineM : Submodule ℂ (α → ℂ)) ↔
    ∃ c : ℂ, c • (onesVecM : α → ℂ) = x := Submodule.mem_span_singleton

lemma sumLM_onesVecM : sumLM (onesVecM : α → ℂ) = (Fintype.card α : ℂ) := by
  rw [sumLM_apply]
  simp only [onesVecM, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end Carrier

/-! ## Generic deleted permutation representation of a `MulAction` -/
section Generic
variable {G : Type} [Group G] {α : Type} [Fintype α] [DecidableEq α] [Nonempty α] [MulAction G α]

/-- The permutation representation of `G` on `α → ℂ` attached to a `MulAction G α`:
`g` acts by `f ↦ (a ↦ f (g⁻¹ • a))`. -/
def permRepM : Representation ℂ G (α → ℂ) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun a => g⁻¹ • a)
  map_one' := by
    refine LinearMap.ext fun f => ?_; funext a; simp [LinearMap.funLeft_apply]
  map_mul' a b := by
    refine LinearMap.ext fun f => ?_; funext i
    simp only [Module.End.mul_apply, LinearMap.funLeft_apply, mul_inv_rev, mul_smul]

@[simp] lemma permRepM_apply (g : G) (f : α → ℂ) (a : α) :
    permRepM g f a = f (g⁻¹ • a) := rfl

/-- The sum-zero subrepresentation. -/
def stdSubM : Subrepresentation (permRepM : Representation ℂ G (α → ℂ)) where
  toSubmodule := LinearMap.ker sumLM
  apply_mem_toSubmodule g f hf := by
    simp only [LinearMap.mem_ker, sumLM_apply] at hf ⊢
    calc ∑ a, permRepM g f a = ∑ a, f (g⁻¹ • a) := by
            refine Finset.sum_congr rfl fun a _ => ?_; rw [permRepM_apply]
      _ = ∑ a, f ((MulAction.toPerm (g⁻¹ : G)) a) := rfl
      _ = ∑ a, f a := Equiv.sum_comp (MulAction.toPerm (g⁻¹ : G)) f
      _ = 0 := hf

/-- The deleted permutation representation as an `FDRep`. -/
def stdRepM : FDRep ℂ G := FDRep.of (stdSubM (G := G) (α := α)).toRepresentation

/-- Number of fixed points of the action of `g`. -/
def fixCardM (g : G) : ℕ := (Finset.univ.filter (fun a : α => g • a = a)).card

@[simp] lemma permRepM_onesVec (g : G) :
    permRepM (α := α) g (onesVecM : α → ℂ) = onesVecM := by
  funext a; simp [onesVecM]

lemma permRepM_eq_toLin' (g : G) :
    (permRepM (G := G) (α := α) g) = ((MulAction.toPerm (g⁻¹ : G)).permMatrix ℂ).toLin' := by
  apply LinearMap.ext; intro f; funext a
  rw [Matrix.toLin'_apply, Matrix.permMatrix_mulVec, permRepM_apply]; rfl

lemma trace_permRepM (g : G) :
    LinearMap.trace ℂ (α → ℂ) (permRepM (G := G) (α := α) g)
      = (Function.fixedPoints ⇑(MulAction.toPerm (g⁻¹ : G) : Equiv.Perm α)).ncard := by
  rw [permRepM_eq_toLin', Matrix.trace_toLin'_eq, Matrix.trace_permutation]

lemma fixedPoints_inv_ncard (g : G) :
    (Function.fixedPoints ⇑(MulAction.toPerm (g⁻¹ : G) : Equiv.Perm α)).ncard
      = fixCardM (α := α) g := by
  rw [fixCardM, ← Set.ncard_coe_finset]
  congr 1; ext a
  simp only [Function.fixedPoints, Function.IsFixedPt, Set.mem_setOf_eq, Finset.coe_filter,
    Finset.mem_univ, true_and, MulAction.toPerm_apply]
  constructor
  · intro h; rw [inv_smul_eq_iff] at h; exact h.symm
  · intro h; rw [inv_smul_eq_iff, h]

@[simp] lemma fixCardM_inv (g : G) : fixCardM (α := α) g⁻¹ = fixCardM (α := α) g := by
  rw [fixCardM, fixCardM]; congr 1; ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [inv_smul_eq_iff] at h; exact h.symm
  · intro h; rw [inv_smul_eq_iff, h]

/-- **Character of the deleted permutation representation.** `χ(g) = #fix(g) − 1`. -/
lemma stdRepM_character (g : G) :
    (stdRepM (G := G) (α := α)).character g = (fixCardM (α := α) g : ℂ) - 1 := by
  classical
  set N : Fin 2 → Submodule ℂ (α → ℂ) :=
    ![(stdSubM (G := G) (α := α)).toSubmodule, constLineM] with hN
  have hsurj : Function.Surjective (sumLM (α := α)) := by
    obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
    intro c; refine ⟨Pi.single a₀ c, ?_⟩
    rw [sumLM_apply, Finset.sum_pi_single']; simp
  have hcardpos : 1 ≤ Fintype.card α := Fintype.card_pos
  have hkerdim : Module.finrank ℂ (LinearMap.ker (sumLM (α := α))) = Fintype.card α - 1 := by
    have h := (sumLM (α := α)).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_pi] at h
    omega
  have hcompl : IsCompl (stdSubM (G := G) (α := α)).toSubmodule constLineM := by
    have hone : Module.finrank ℂ (constLineM : Submodule ℂ (α → ℂ)) = 1 :=
      finrank_span_singleton onesVecM_ne_zero
    have hdim : Module.finrank ℂ (α → ℂ) ≤
        Module.finrank ℂ (stdSubM (G := G) (α := α)).toSubmodule
          + Module.finrank ℂ (constLineM : Submodule ℂ (α → ℂ)) := by
      have hk : Module.finrank ℂ (stdSubM (G := G) (α := α)).toSubmodule
          = Fintype.card α - 1 := hkerdim
      rw [hk, hone, Module.finrank_pi]; omega
    refine (Submodule.isCompl_iff_disjoint _ _ hdim).mpr ?_
    rw [Submodule.disjoint_def]
    rintro x hxk hxc
    rw [mem_constLineM] at hxc
    obtain ⟨c, rfl⟩ := hxc
    have h0 : sumLM (c • (onesVecM : α → ℂ)) = 0 := hxk
    rw [map_smul, sumLM_onesVecM, smul_eq_mul] at h0
    have hc : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h (Nat.cast_ne_zero.mpr (by omega))
    simp [hc]
  have huniv : (Set.univ : Set (Fin 2)) = {0, 1} := by
    ext i; simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]; omega
  have hInternal : DirectSum.IsInternal N :=
    (DirectSum.isInternal_submodule_iff_isCompl N (zero_ne_one) huniv).mpr hcompl
  have hf0 : Set.MapsTo (permRepM (α := α) g) (N 0) (N 0) := fun x hx =>
    (stdSubM (G := G) (α := α)).apply_mem_toSubmodule g hx
  have hf1 : Set.MapsTo (permRepM (α := α) g) (N 1) (N 1) := by
    intro x hx
    change x ∈ (constLineM : Submodule ℂ (α → ℂ)) at hx
    change permRepM g x ∈ (constLineM : Submodule ℂ (α → ℂ))
    rw [mem_constLineM] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by rw [map_smul, permRepM_onesVec]⟩
  have hf : ∀ i, Set.MapsTo (permRepM (α := α) g) (N i) (N i) := Fin.forall_fin_two.mpr ⟨hf0, hf1⟩
  have htr := LinearMap.trace_eq_sum_trace_restrict hInternal hf
  rw [trace_permRepM, fixedPoints_inv_ncard, Fin.sum_univ_two] at htr
  have hN0 : LinearMap.trace ℂ ↥(N 0) ((permRepM g).restrict (hf 0))
      = (stdRepM (G := G) (α := α)).character g := by
    change LinearMap.trace ℂ ↥((stdSubM (G := G) (α := α)).toSubmodule)
        ((stdSubM (G := G) (α := α)).toRepresentation g)
      = LinearMap.trace ℂ ↥((stdSubM (G := G) (α := α)).toSubmodule)
        ((FDRep.of (stdSubM (G := G) (α := α)).toRepresentation).ρ g)
    rw [FDRep.of_ρ']
  have hN1 : LinearMap.trace ℂ ↥(N 1) ((permRepM g).restrict (hf 1)) = 1 := by
    have hid : (permRepM g).restrict (hf 1) = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext
      have hx : (x : α → ℂ) ∈ (constLineM : Submodule ℂ (α → ℂ)) := x.2
      rw [mem_constLineM] at hx
      obtain ⟨c, hc⟩ := hx
      change permRepM g (x : α → ℂ) = (x : α → ℂ)
      rw [← hc, map_smul, permRepM_onesVec]
    have hfin : Module.finrank ℂ ↥(N 1) = 1 := finrank_span_singleton onesVecM_ne_zero
    rw [hid, LinearMap.trace_id, hfin]; norm_num
  rw [hN0, hN1] at htr
  rw [eq_sub_iff_add_eq]; exact htr.symm

/-- The fixed-point count is a class function: conjugate elements have the same number of
fixed points, since `a ↦ c • a` bijects `Fix(g)` onto `Fix(c·g·c⁻¹)`. -/
lemma fixCardM_conj (c g : G) :
    fixCardM (α := α) (c * g * c⁻¹) = fixCardM (α := α) g := by
  rw [fixCardM, fixCardM,
    show (Finset.univ.filter fun a : α => (c * g * c⁻¹) • a = a)
        = (Finset.univ.filter fun a : α => g • a = a).image (c • ·) by
      ext b
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hb
        refine ⟨c⁻¹ • b, ?_, smul_inv_smul c b⟩
        rw [mul_smul, mul_smul] at hb
        refine MulAction.injective c ?_
        show c • (g • (c⁻¹ • b)) = c • (c⁻¹ • b)
        rw [smul_inv_smul]
        exact hb
      · rintro ⟨a, ha, rfl⟩
        rw [mul_smul, mul_smul, inv_smul_smul, ha],
    Finset.card_image_of_injective _ (MulAction.injective c)]

end Generic

/-! ## The character table of `S₄` -/

open Equiv

abbrev S4 := Equiv.Perm (Fin 4)

/-- One-dimensional representation attached to a character `χ : G →* ℂˣ`. -/
def charRep {G : Type} [Group G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by
    apply LinearMap.ext; intro x
    change ((χ (a * b) : ℂˣ) : ℂ) * x = ((χ a : ℂˣ) : ℂ) * (((χ b : ℂˣ) : ℂ) * x)
    rw [map_mul, Units.val_mul, mul_assoc]

@[simp] lemma charRep_character {G : Type} [Group G] (χ : G →* ℂˣ) (g : G) :
    (FDRep.of (charRep χ)).character g = (χ g : ℂ) := by
  change LinearMap.trace ℂ ℂ ((FDRep.of (charRep χ)).ρ g) = (χ g : ℂ)
  rw [FDRep.of_ρ', show charRep χ g = ((χ g : ℂˣ) : ℂ) • LinearMap.id from rfl,
    map_smul, LinearMap.trace_id]; simp

lemma charRep_simple {G : Type} [Group G] [Finite G] (χ : G →* ℂˣ) :
    Simple (FDRep.of (charRep χ)) := by
  haveI : Fintype G := Fintype.ofFinite G
  rw [FDRep.simple_iff_char_is_norm_one]
  have : ∀ g : G, (FDRep.of (charRep χ)).character g
      * (FDRep.of (charRep χ)).character g⁻¹ = 1 := by
    intro g
    rw [charRep_character, charRep_character, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Nat.card_eq_fintype_card]

/-- The trivial representation `ℂ₊`. -/
def trivRepS4 : FDRep ℂ S4 := FDRep.of (charRep (1 : S4 →* ℂˣ))
/-- The sign character `S₄ →* ℂˣ`. -/
def signHomS4 : S4 →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign
/-- The sign representation `ℂ₋`. -/
def signRepS4 : FDRep ℂ S4 := FDRep.of (charRep signHomS4)

/-! ### The conjugation action of `S₄` on the three pair-partitions of `Fin 4` -/

/-- The three fixed-point-free involutions of `Fin 4` (the pair-partitions). -/
def involS4 : Fin 3 → S4 :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

lemma involS4_injective : Function.Injective involS4 := by decide

/-- The index of `g · ιₐ · g⁻¹` among the three involutions. -/
def conjIdxS4 (g : S4) (a : Fin 3) : Fin 3 :=
  if g * involS4 a * g⁻¹ = involS4 0 then 0
  else if g * involS4 a * g⁻¹ = involS4 1 then 1 else 2

set_option maxHeartbeats 4000000 in
-- honest `decide` over the 24×3 conjugation table (no `native_decide`); the raised limit
-- covers kernel reduction of the permutation multiplications.
lemma conjIdxS4_spec (g : S4) (a : Fin 3) : involS4 (conjIdxS4 g a) = g * involS4 a * g⁻¹ := by
  revert g a; decide

/-- `S₄` acts on the three pair-partitions (`Fin 3`) by conjugation of involutions. -/
instance conjActionS4 : MulAction S4 (Fin 3) where
  smul := conjIdxS4
  one_smul a := involS4_injective (by
    change involS4 (conjIdxS4 1 a) = involS4 a
    rw [conjIdxS4_spec]; simp)
  mul_smul g h a := involS4_injective (by
    change involS4 (conjIdxS4 (g * h) a) = involS4 (conjIdxS4 g (conjIdxS4 h a))
    rw [conjIdxS4_spec, conjIdxS4_spec, conjIdxS4_spec]; group)

/-! ### The five irreducible representations -/

/-- `ℂ³₋`, the deleted natural permutation representation. -/
def repStd : FDRep ℂ S4 := stdRepM (G := S4) (α := Fin 4)
/-- `ℂ²`, the deleted conjugation-on-partitions representation. -/
def repC2 : FDRep ℂ S4 := stdRepM (G := S4) (α := Fin 3)
/-- `ℂ³₊ = ℂ³₋ ⊗ sign`. -/
def repStdPlus : FDRep ℂ S4 := repStd ⊗ signRepS4

/-- The five irreducibles, indexed as the rows of `chiS4`: `ℂ₊, ℂ₋, ℂ², ℂ³₊, ℂ³₋`. -/
def irrepS4 : Fin 5 → FDRep ℂ S4 := ![trivRepS4, signRepS4, repC2, repStdPlus, repStd]

/-- The five class representatives `Id, (12), (12)(34), (123), (1234)`. -/
def classRepS4 : Fin 5 → S4 :=
  ![1, Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 1 * Equiv.swap 1 2, finRotate 4]

/-- The integer character table (book values). -/
def tbl : Fin 5 → Fin 5 → ℤ :=
  ![![1,  1,  1,  1,  1],
    ![1, -1,  1,  1, -1],
    ![2,  0,  2, -1,  0],
    ![3, -1, -1,  0,  1],
    ![3,  1, -1,  0, -1]]

/-! ### Character values -/

lemma trivRepS4_char (j : Fin 5) : trivRepS4.character (classRepS4 j) = (tbl 0 j : ℂ) := by
  rw [trivRepS4, charRep_character]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma signRepS4_char (j : Fin 5) : signRepS4.character (classRepS4 j) = (tbl 1 j : ℂ) := by
  have hs : ∀ k, (Equiv.Perm.sign (classRepS4 k) : ℤ) = ![1, -1, 1, 1, -1] k := by decide
  rw [signRepS4, charRep_character]
  have hbridge : ((signHomS4 (classRepS4 j) : ℂˣ) : ℂ)
      = ((Equiv.Perm.sign (classRepS4 j) : ℤ) : ℂ) := by
    simp [signHomS4]
  rw [hbridge, hs j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma repStd_char (j : Fin 5) : repStd.character (classRepS4 j) = (tbl 4 j : ℂ) := by
  have hf : ∀ k, fixCardM (G := S4) (α := Fin 4) (classRepS4 k) = ![4, 2, 0, 1, 0] k := by decide
  rw [repStd, stdRepM_character, hf j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma repC2_char (j : Fin 5) : repC2.character (classRepS4 j) = (tbl 2 j : ℂ) := by
  have hf : ∀ k, fixCardM (G := S4) (α := Fin 3) (classRepS4 k) = ![3, 1, 3, 0, 1] k := by decide
  rw [repC2, stdRepM_character, hf j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

lemma hstd_char (g : S4) :
    repStd.character g = (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1 : ℂ)) := by
  rw [repStd, stdRepM_character]; push_cast; ring

lemma hsgn_char (g : S4) : signRepS4.character g = (signHomS4 g : ℂ) := by
  rw [signRepS4, charRep_character]

lemma repStdPlus_char_eq (g : S4) :
    repStdPlus.character g
      = (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1 : ℂ)) * (signHomS4 g : ℂ) := by
  have hchar : repStdPlus.character = repStd.character * signRepS4.character := by
    rw [repStdPlus]; exact FDRep.char_tensor repStd signRepS4
  have h := congrFun hchar g
  rw [Pi.mul_apply, hstd_char, hsgn_char] at h
  exact h

lemma repStdPlus_char (j : Fin 5) : repStdPlus.character (classRepS4 j) = (tbl 3 j : ℂ) := by
  rw [repStdPlus_char_eq]
  have hf : ∀ k, fixCardM (G := S4) (α := Fin 4) (classRepS4 k) = ![4, 2, 0, 1, 0] k := by decide
  have hs : ∀ k, (Equiv.Perm.sign (classRepS4 k) : ℤ) = ![1, -1, 1, 1, -1] k := by decide
  rw [hf j]
  have hbridge : ((signHomS4 (classRepS4 j) : ℂˣ) : ℂ)
      = ((Equiv.Perm.sign (classRepS4 j) : ℤ) : ℂ) := by simp [signHomS4]
  rw [hbridge, hs j]
  fin_cases j <;>
    norm_num [tbl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- The character of `irrepS4 i` at the class representative `classRepS4 j` equals `tbl i j`. -/
lemma irrepS4_character (i j : Fin 5) :
    (irrepS4 i).character (classRepS4 j) = (tbl i j : ℂ) := by
  fin_cases i
  · exact trivRepS4_char j
  · exact signRepS4_char j
  · exact repC2_char j
  · exact repStdPlus_char j
  · exact repStd_char j

/-! ### Simplicity -/

lemma trivRepS4_simple : Simple trivRepS4 := charRep_simple _
lemma signRepS4_simple : Simple signRepS4 := charRep_simple _

lemma repStd_simple : Simple repStd := by
  rw [repStd, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4,
      (stdRepM (G := S4) (α := Fin 4)).character g
        * (stdRepM (G := S4) (α := Fin 4)).character g⁻¹
      = ((((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [stdRepM_character, stdRepM_character, fixCardM_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

lemma repC2_simple : Simple repC2 := by
  rw [repC2, FDRep.simple_iff_char_is_norm_one]
  have hterm : ∀ g : S4,
      (stdRepM (G := S4) (α := Fin 3)).character g
        * (stdRepM (G := S4) (α := Fin 3)).character g⁻¹
      = ((((fixCardM (G := S4) (α := Fin 3) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [stdRepM_character, stdRepM_character, fixCardM_inv]; push_cast; ring
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCardM (G := S4) (α := Fin 3) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

lemma repStdPlus_simple : Simple repStdPlus := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hsign : ∀ g : S4, (signHomS4 g : ℂ) * (signHomS4 g⁻¹ : ℂ) = 1 := by
    intro g; rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hterm : ∀ g : S4, repStdPlus.character g * repStdPlus.character g⁻¹
      = ((((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2 : ℤ) : ℂ) := by
    intro g
    rw [repStdPlus_char_eq, repStdPlus_char_eq, fixCardM_inv]
    push_cast
    linear_combination (((fixCardM (G := S4) (α := Fin 4) g : ℂ) - 1) ^ 2) * hsign g
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Int.cast_sum]
  have hsum : ∑ g : S4, (((fixCardM (G := S4) (α := Fin 4) g : ℤ) - 1) ^ 2) = 24 := by decide
  rw [hsum, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; norm_num

lemma irrepS4_simple (i : Fin 5) : Simple (irrepS4 i) := by
  fin_cases i
  · exact trivRepS4_simple
  · exact signRepS4_simple
  · exact repC2_simple
  · exact repStdPlus_simple
  · exact repStd_simple

/-! ### Pairwise non-isomorphism -/

lemma tbl_injective : Function.Injective tbl := by decide

lemma irrepS4_pairwise (i j : Fin 5) (hij : i ≠ j) : ¬ Nonempty (irrepS4 i ≅ irrepS4 j) := by
  rintro ⟨e⟩
  apply hij
  have hchar : (irrepS4 i).character = (irrepS4 j).character := FDRep.char_iso e
  have hrow : ∀ c, tbl i c = tbl j c := fun c => by
    have h2 : ((tbl i c : ℤ) : ℂ) = ((tbl j c : ℤ) : ℂ) := by
      rw [← irrepS4_character, ← irrepS4_character, hchar]
    exact_mod_cast h2
  exact tbl_injective (funext hrow)


/-! ### Bridge to the tabulated `Q5` values -/

/-- Every entry of the `S₄` table is rational (`im = 0`), and its rational part is the
corresponding integer of `tbl`; hence `Q5toC (chiS4 i j) = tbl i j`. -/
lemma chiS4_eq_tbl (i j : Fin 5) : Q5toC (chiS4 i j) = (tbl i j : ℂ) := by
  have him : (chiS4 i j).im = 0 := by fin_cases i <;> fin_cases j <;> decide
  have hre : (chiS4 i j).re = ((tbl i j : ℤ) : ℚ) := by fin_cases i <;> fin_cases j <;> decide
  rw [Q5toC, him, hre]; push_cast; ring

/-- The character of `irrepS4 i` at `classRepS4 j` equals the tabulated `Q5` value
`chiS4 i j`. -/
lemma irrepS4_character_book (i j : Fin 5) :
    (irrepS4 i).character (classRepS4 j) = Q5toC (chiS4 i j) := by
  rw [irrepS4_character, chiS4_eq_tbl]

end

end S4

end Etingof.Example4_8_1
