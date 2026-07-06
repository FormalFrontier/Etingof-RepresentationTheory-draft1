import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import EtingofRepresentationTheory.Chapter2.Theorem2_1_1
import EtingofRepresentationTheory.Chapter2.Problem2_15_1_complete_reducibility

/-!
# Semisimple decomposition of a finite-dimensional `sl(2)`-module (Problem 2.15.1(l), piece 1)

The *uniqueness* half of Etingof Problem 2.15.1(l) recovers the `sl(2)`-isomorphism type of a
finite-dimensional module from its raising operator. Its structural core is the **semisimple
decomposition theorem**: every finite-dimensional complex `sl(2)`-module is isomorphic, as a Lie
module, to a block-diagonal sum of standard irreducibles

```
V ≃ₗ⁅ℂ,sl2⁆ ∀ i : Fin m, (Fin (n i + 1) → ℂ).
```

This is proved by strong induction on `Module.finrank ℂ V`. When `V` is nonzero we pick a minimal
nonzero `sl(2)`-submodule `S` (an atom of the submodule lattice, hence irreducible), classify it as
a standard irreducible `V_{n₀} = Fin (n₀ + 1) → ℂ` via `Problem_2_15_1_f`, split off an
`sl(2)`-complement `C` using complete reducibility (`complete_reducibility`), recurse on `C`
(`finrank C < finrank V`), and reassemble `V ≃ S ⊕ C ≃ V_{n₀} ⊕ (∀ i, V_{n i})`.

To phrase the product of standard irreducibles as an `sl(2)`-module we equip an arbitrary product
`∀ i, M i` (and binary product `M × N`) of `sl(2)`-modules with the componentwise Lie action; the
reassembly step uses the block-cons equivalence
`(V_{n₀} × ∀ i, V_{n i}) ≃ₗ⁅ℂ,sl2⁆ ∀ j : Fin (m+1), V_{(Fin.cons n₀ n) j}`.

This is the reusable structural piece of the uniqueness program; the nullity-invariant core lives in
`Chapter2/Sl2NullitySequence.lean`, and the final reindexing assembly is tracked separately.
-/

open Etingof Etingof.Sl2Irrep
open LieModule Module

namespace Etingof.Sl2Irrep

universe u

/-! ## Componentwise `sl(2)`-action on products of modules -/

section PiLie

variable {L : Type*} [LieRing L] {ι : Type*} {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, LieRingModule L (M i)]

/-- Componentwise Lie action on a product of Lie modules: `⁅x, v⁆ i = ⁅x, v i⁆`. -/
instance instPiLieRingModule : LieRingModule L (∀ i, M i) where
  bracket x v := fun i => ⁅x, v i⁆
  add_lie x y v := by funext i; exact add_lie x y (v i)
  lie_add x u v := by funext i; exact lie_add x (u i) (v i)
  leibniz_lie x y v := by funext i; exact leibniz_lie x y (v i)

@[simp] theorem pi_bracket_apply (x : L) (v : ∀ i, M i) (i : ι) :
    ⁅x, v⁆ i = ⁅x, v i⁆ := rfl

variable {R : Type*} [CommRing R] [LieAlgebra R L]
  [∀ i, Module R (M i)] [∀ i, LieModule R L (M i)]

instance instPiLieModule : LieModule R L (∀ i, M i) where
  smul_lie t x v := by funext i; exact smul_lie t x (v i)
  lie_smul t x v := by funext i; exact lie_smul t x (v i)

end PiLie

section ProdLie

variable {L : Type*} [LieRing L] {M N : Type*}
  [AddCommGroup M] [AddCommGroup N] [LieRingModule L M] [LieRingModule L N]

/-- Componentwise Lie action on a binary product of Lie modules. -/
instance instProdLieRingModule : LieRingModule L (M × N) where
  bracket x p := (⁅x, p.1⁆, ⁅x, p.2⁆)
  add_lie x y p := by ext <;> exact add_lie x y _
  lie_add x p q := by ext <;> exact lie_add x _ _
  leibniz_lie x y p := by ext <;> exact leibniz_lie x y _

@[simp] theorem prod_bracket_fst (x : L) (p : M × N) : (⁅x, p⁆ : M × N).1 = ⁅x, p.1⁆ := rfl
@[simp] theorem prod_bracket_snd (x : L) (p : M × N) : (⁅x, p⁆ : M × N).2 = ⁅x, p.2⁆ := rfl

variable {R : Type*} [CommRing R] [LieAlgebra R L]
  [Module R M] [Module R N] [LieModule R L M] [LieModule R L N]

instance instProdLieModule : LieModule R L (M × N) where
  smul_lie t x p := by ext <;> exact smul_lie t x _
  lie_smul t x p := by ext <;> exact lie_smul t x _

end ProdLie

/-! ## Lie-module equivalences for assembling products -/

section Assembly

variable {M M' N N' : Type*}
  [AddCommGroup M] [Module ℂ M] [LieRingModule sl2 M] [LieModule ℂ sl2 M]
  [AddCommGroup M'] [Module ℂ M'] [LieRingModule sl2 M'] [LieModule ℂ sl2 M']
  [AddCommGroup N] [Module ℂ N] [LieRingModule sl2 N] [LieModule ℂ sl2 N]
  [AddCommGroup N'] [Module ℂ N'] [LieRingModule sl2 N'] [LieModule ℂ sl2 N']

/-- A pair of `sl(2)`-module equivalences assemble into an equivalence of binary products. -/
def prodCongrLie (eM : M ≃ₗ⁅ℂ,sl2⁆ M') (eN : N ≃ₗ⁅ℂ,sl2⁆ N') :
    (M × N) ≃ₗ⁅ℂ,sl2⁆ (M' × N') where
  toFun p := (eM p.1, eN p.2)
  map_add' p q := by ext <;> simp
  map_smul' t p := by ext <;> simp
  map_lie' := by
    intro x p
    ext
    · exact (eM : M →ₗ⁅ℂ,sl2⁆ M').map_lie x p.1
    · exact (eN : N →ₗ⁅ℂ,sl2⁆ N').map_lie x p.2
  invFun p := (eM.symm p.1, eN.symm p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

end Assembly

/-- **Block-cons assembly.** The product of the first standard irreducible `V_{n₀}` with a
`Fin m`-indexed product of standard irreducibles `V_{n i}` is, as an `sl(2)`-module, the
`Fin (m+1)`-indexed product with block sizes `Fin.cons n₀ n`. -/
def consBlockLieEquiv {m : ℕ} (n₀ : ℕ) (n : Fin m → ℕ) :
    ((Fin (n₀ + 1) → ℂ) × ∀ i : Fin m, (Fin (n i + 1) → ℂ)) ≃ₗ⁅ℂ,sl2⁆
      ∀ j : Fin (m + 1), (Fin ((Fin.cons n₀ n : Fin (m + 1) → ℕ) j + 1) → ℂ) where
  toFun p := Fin.cons (α := fun j => Fin ((Fin.cons n₀ n : Fin (m + 1) → ℕ) j + 1) → ℂ) p.1 p.2
  invFun w := (w 0, fun i => w i.succ)
  map_add' p q := by
    funext j; rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> rfl
  map_smul' t p := by
    funext j; rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> rfl
  map_lie' := by
    intro x p
    funext j; rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩ <;> rfl
  left_inv p := rfl
  right_inv w := Fin.cons_self_tail w

/-! ## Splitting off a complementary submodule -/

section Split

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule sl2 V] [LieModule ℂ sl2 V]

/-- **The internal direct sum from a complemented submodule.** If `S` and `C` are complementary
`sl(2)`-submodules of `V`, then `↥S × ↥C ≃ₗ⁅ℂ,sl2⁆ V` via `(s, c) ↦ s + c`. -/
noncomputable def lieProdEquivOfIsCompl (S C : LieSubmodule ℂ sl2 V) (h : IsCompl S C) :
    (↥S × ↥C) ≃ₗ⁅ℂ,sl2⁆ V :=
  { Submodule.prodEquivOfIsCompl (S : Submodule ℂ V) (C : Submodule ℂ V)
      (LieSubmodule.isCompl_toSubmodule.mpr h) with
    map_lie' := by
      intro x p
      change ((⁅x, p.1⁆ : ↥S) : V) + ((⁅x, p.2⁆ : ↥C) : V)
        = ⁅x, ((p.1 : ↥S) : V) + ((p.2 : ↥C) : V)⁆
      rw [LieSubmodule.coe_bracket, LieSubmodule.coe_bracket, ← lie_add] }

end Split

/-! ## Existence of an irreducible submodule -/

section Irreducible

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule sl2 V] [LieModule ℂ sl2 V]

omit [LieModule ℂ sl2 V] in
/-- Every nonzero finite-dimensional `sl(2)`-module has a minimal nonzero submodule (an atom of the
lattice of Lie submodules). -/
theorem exists_atom_lieSubmodule [FiniteDimensional ℂ V] [Nontrivial V] :
    ∃ W : LieSubmodule ℂ sl2 V, IsAtom W := by
  have : (⊤ : LieSubmodule ℂ sl2 V) ≠ ⊥ := by
    intro h
    have hsub := (LieSubmodule.eq_bot_iff (N := (⊤ : LieSubmodule ℂ sl2 V))).mp h
    exact absurd (⟨fun a b => by simp [hsub a (LieSubmodule.mem_top a),
      hsub b (LieSubmodule.mem_top b)]⟩ : Subsingleton V) (not_subsingleton V)
  exact (eq_bot_or_exists_atom_le (⊤ : LieSubmodule ℂ sl2 V)).resolve_left this
    |>.imp fun W ⟨hW, _⟩ => hW

omit [LieModule ℂ sl2 V] in
/-- An atom of the lattice of Lie submodules is irreducible as a Lie module. -/
theorem isAtom_isIrreducible {W : LieSubmodule ℂ sl2 V} (hW : IsAtom W) :
    LieModule.IsIrreducible ℂ sl2 ↥W := by
  haveI : Nontrivial ↥W :=
    (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := V)).mpr hW.1
  exact LieModule.IsIrreducible.mk fun M hM => by
    set M' := LieSubmodule.map W.incl M
    have hM'_le : M' ≤ W := by
      intro v hv
      rw [LieSubmodule.mem_map] at hv
      obtain ⟨m, _, rfl⟩ := hv; exact m.property
    have hM'_ne : M' ≠ ⊥ := by
      intro h; apply hM; rw [eq_bot_iff]; intro m hm
      have : W.incl m ∈ (⊥ : LieSubmodule ℂ sl2 V) := h ▸ LieSubmodule.mem_map_of_mem hm
      rw [LieSubmodule.mem_bot] at this
      rw [LieSubmodule.mem_bot]; exact Subtype.val_injective this
    have hM'_eq : M' = W := (hW.le_iff.mp hM'_le).resolve_left hM'_ne
    rw [eq_top_iff]; intro m _
    suffices hmem : (m : V) ∈ M' by
      rw [LieSubmodule.mem_map] at hmem
      obtain ⟨m', hm', hm'_eq⟩ := hmem
      exact (Subtype.val_injective hm'_eq) ▸ hm'
    rw [hM'_eq]; exact m.property

end Irreducible

/-! ## The semisimple decomposition -/

/-- Strong-induction workhorse for `sl2Module_decomposition`, quantifying over all modules of a
fixed dimension `d`. -/
private theorem decomp_aux (d : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      [LieRingModule sl2 V] [LieModule ℂ sl2 V],
      Module.finrank ℂ V = d →
      ∃ (m : ℕ) (n : Fin m → ℕ),
        Nonempty (V ≃ₗ⁅ℂ,sl2⁆ ∀ i : Fin m, (Fin (n i + 1) → ℂ)) := by
  induction d using Nat.strongRecOn with | ind d ih => ?_
  intro V _ _ _ _ _ hdim
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- Trivial module: the empty product.
    subst hd0
    haveI : Subsingleton V := by
      rw [← not_nontrivial_iff_subsingleton]
      intro hnt
      haveI := hnt
      have : 0 < Module.finrank ℂ V := (finrank_pos_iff (R := ℂ)).mpr hnt
      omega
    refine ⟨0, Fin.elim0, ⟨?_⟩⟩
    exact
      { toFun := fun _ => (fun i => i.elim0)
        map_add' := fun _ _ => by funext i; exact i.elim0
        map_smul' := fun _ _ => by funext i; exact i.elim0
        map_lie' := by intro x v; funext i; exact i.elim0
        invFun := fun _ => 0
        left_inv := fun v => Subsingleton.elim _ _
        right_inv := fun w => by funext i; exact i.elim0 }
  · -- Nonzero module: split off an irreducible submodule.
    haveI hnt : Nontrivial V := by
      rw [← finrank_pos_iff (R := ℂ)]; omega
    obtain ⟨S, hS⟩ := exists_atom_lieSubmodule (V := V)
    have hirr : LieModule.IsIrreducible ℂ sl2 ↥S := isAtom_isIrreducible hS
    haveI : Nontrivial ↥S := (LieSubmodule.nontrivial_iff_ne_bot ℂ sl2 (M := V)).mpr hS.1
    -- `S` is a standard irreducible `V_{n₀}`.
    obtain ⟨n₀, hn₀⟩ : ∃ n₀, Module.finrank ℂ ↥S = n₀ + 1 := by
      have : 0 < Module.finrank ℂ ↥S := finrank_pos
      exact ⟨Module.finrank ℂ ↥S - 1, by omega⟩
    obtain ⟨eS⟩ := Etingof.Problem_2_15_1_f n₀ hn₀ hirr
    -- Split off an `sl(2)`-complement.
    obtain ⟨C, hC⟩ := complete_reducibility S
    -- The complement has strictly smaller dimension.
    have hsum : Module.finrank ℂ ↥S + Module.finrank ℂ ↥C = d := by
      have := Submodule.finrank_add_eq_of_isCompl (LieSubmodule.isCompl_toSubmodule.mpr hC)
      rw [← hdim]; exact this
    have hClt : Module.finrank ℂ ↥C < d := by omega
    obtain ⟨m, n, ⟨eC⟩⟩ := ih _ hClt ↥C rfl
    -- Reassemble.
    refine ⟨m + 1, Fin.cons n₀ n, ⟨?_⟩⟩
    exact (lieProdEquivOfIsCompl S C hC).symm.trans
      ((prodCongrLie eS eC).trans (consBlockLieEquiv n₀ n))

/-- **Semisimple decomposition of a finite-dimensional `sl(2)`-module** (Problem 2.15.1(l),
piece 1).
Every finite-dimensional complex `sl(2)`-module `V` is isomorphic, as a Lie module, to a
block-diagonal sum of standard irreducibles `V_{n i} = Fin (n i + 1) → ℂ`.

The proof is by strong induction on `Module.finrank ℂ V`: a nonzero `V` has a minimal nonzero
submodule `S` (`exists_atom_lieSubmodule`), which is irreducible (`isAtom_isIrreducible`) and hence
a standard `V_{n₀}` (`Problem_2_15_1_f`); complete reducibility (`complete_reducibility`) splits off
a smaller-dimensional complement `C`, and the inductive decomposition of `C` reassembles with
`S`. -/
theorem sl2Module_decomposition (V : Type u) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [LieRingModule sl2 V] [LieModule ℂ sl2 V] :
    ∃ (m : ℕ) (n : Fin m → ℕ),
      Nonempty (V ≃ₗ⁅ℂ,sl2⁆ ∀ i : Fin m, (Fin (n i + 1) → ℂ)) :=
  decomp_aux (Module.finrank ℂ V) V rfl

end Etingof.Sl2Irrep
