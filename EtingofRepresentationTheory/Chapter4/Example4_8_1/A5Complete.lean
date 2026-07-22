import EtingofRepresentationTheory.Chapter4.Example4_9_1
import EtingofRepresentationTheory.Chapter4.Corollary4_2_2

/-!
# `A₅`: completeness of the irreducible list `irrepA5`

The five representations `irrepA5 0..4 : Fin 5 → FDRep ℂ A₅` are simple
(`irrepA5_simple`) and pairwise non-isomorphic (`irrepA5_pairwise`). Since `A₅` has exactly
`5` conjugacy classes (`Etingof.Example4_8_1_A5_conj_classes`), Corollary 4.2.2, which
produces a complete list of `|ConjClasses G|` simple representations, forces `irrepA5` to be
a complete list: every simple `FDRep ℂ A₅` is isomorphic to some `irrepA5 i`.

* `simple_iso_irrepA5`: every simple `V : FDRep ℂ A₅` satisfies `V ≅ irrepA5 i` for some `i`.
* `exists_char_eq_chiA5`: hence its character is the `i`-th row `chiA5 i` of the `A₅`
  character table (evaluated at the conjugacy class of `g`).

This is the reusable completeness input for the icosahedral decomposition theorems of
Problem 4.12.5.
-/

open CategoryTheory

namespace Etingof.Example4_8_1.A5

/-- `|A₅| = 60` is invertible in `ℂ`, so Corollary 4.2.2 applies. -/
private noncomputable instance : Invertible (Fintype.card (alternatingGroup (Fin 5)) : ℂ) :=
  invertibleOfNonzero (by rw [Etingof.Example4_8_1_A5_card]; norm_num)

/-- **Completeness of `irrepA5`.** Every simple complex representation of `A₅` is isomorphic
to one of the five `irrepA5 i`. The five are pairwise non-isomorphic simples and there are
exactly `5 = |ConjClasses A₅|` isomorphism classes of simples (Corollary 4.2.2), so they
exhaust them. -/
theorem simple_iso_irrepA5 (V : FDRep ℂ (alternatingGroup (Fin 5))) [Simple V] :
    ∃ i : Fin 5, Nonempty (V ≅ irrepA5 i) := by
  obtain ⟨n, W, _hWsimp, _hWinj, hWsurj, hn⟩ :=
    Etingof.Corollary4_2_2 (k := ℂ) (G := alternatingGroup (Fin 5))
  rw [Etingof.Example4_8_1_A5_conj_classes] at hn
  subst hn
  -- Each `irrepA5 i` is isomorphic to some `W (c i)`.
  choose c hc using fun i => hWsurj (irrepA5 i) (irrepA5_simple i)
  -- `c` is injective: distinct `irrepA5` are non-isomorphic, so land in distinct `W`.
  have hcinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    refine irrepA5_pairwise i j hne ?_
    obtain ⟨αi⟩ := hc i
    obtain ⟨αj⟩ := hc j
    exact ⟨αi ≪≫ eqToIso (congrArg W hij) ≪≫ αj.symm⟩
  -- `c : Fin 5 → Fin 5` injective, hence surjective.
  have hcsurj : Function.Surjective c := Finite.surjective_of_injective hcinj
  -- `V` is simple, so `V ≅ W k` for some `k = c i`.
  obtain ⟨k, hk⟩ := hWsurj V ‹Simple V›
  obtain ⟨i, hi⟩ := hcsurj k
  refine ⟨i, ?_⟩
  obtain ⟨αV⟩ := hk
  obtain ⟨αi⟩ := hc i
  exact ⟨αV ≪≫ eqToIso (congrArg W hi.symm) ≪≫ αi.symm⟩

/-- **Character of a simple `A₅`-representation.** The character of any simple `V : FDRep ℂ A₅`
equals one of the five rows `chiA5 i` of the `A₅` character table, read off at the conjugacy
class `classIdxA5 g` of `g`. -/
theorem exists_char_eq_chiA5 (V : FDRep ℂ (alternatingGroup (Fin 5))) [Simple V] :
    ∃ i : Fin 5, ∀ g, V.character g = Q5toC (chiA5 i (classIdxA5 g)) := by
  obtain ⟨i, ⟨α⟩⟩ := simple_iso_irrepA5 V
  refine ⟨i, fun g => ?_⟩
  rw [FDRep.char_iso α, Etingof.Example4_9_1.irrepA5_char_eq i g]

end Etingof.Example4_8_1.A5
