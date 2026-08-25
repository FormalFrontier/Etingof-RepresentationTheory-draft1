import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Lemma 3.1.6: Surjective Map from Direct Sum of Irreducibles Splits

Etingof Lemma 3.1.6. Given a surjection `f : V → U` and a decomposition
`V = ⨁_{i ∈ I} Vᵢ` into irreducible submodules, there is a subset `J ⊆ I` such that the
concrete sub-sum `V_J := ⨆_{i ∈ J} Vᵢ` is mapped *isomorphically* by `f` onto `U`.

The book's proof selects a maximal subset `J` such that `f` is injective on `V_J`; if
`f(V_J) ≠ U`, some `Vᵢ` maps nonzero into `U / f(V_J)`, hence (being simple, by Schur) injective,
so `J ∪ {i}` still keeps `f` injective, contradicting maximality.

The main content is `Etingof.exists_subfamily_isCompl_ker`: the selected sub-sum is a genuine
complement of `ker f` built from members of the *given* family. From it we read off that the
restriction of `f` to `V_J` is bijective (`Etingof.exists_subfamily_bijective`) and package the
resulting isomorphism (`Etingof.exists_subfamily_linearEquiv`, and its direct-sum-hypothesis form
`Etingof.exists_subfamily_linearEquiv_of_isInternal`).

The earlier declaration `Etingof.surjective_map_splits` records only the *existence* of an
arbitrary complement of `ker f`; the theorems below refine it by producing a complement chosen
from the given decomposition.
-/

namespace Etingof

open LinearMap Submodule

/-- A surjective map from a semisimple module splits: there exists a complement of the kernel
that maps isomorphically onto the target. Etingof Lemma 3.1.6 (weak, complement-only form). -/
theorem surjective_map_splits (A : Type*) (V U : Type*)
    [Ring A] [AddCommGroup V] [Module A V] [AddCommGroup U] [Module A U]
    [IsSemisimpleModule A V] (f : V →ₗ[A] U) (_hf : Function.Surjective f) :
    ∃ (W : Submodule A V), Disjoint W (LinearMap.ker f) ∧ W ⊔ LinearMap.ker f = ⊤ := by
  obtain ⟨W, hW⟩ := exists_isCompl (LinearMap.ker f)
  exact ⟨W, hW.symm.disjoint, hW.symm.sup_eq_top⟩

/-- If `W` is disjoint from `K` and `W'` is disjoint from `W ⊔ K`, then `W ⊔ W'` is disjoint
from `K`. This is the algebraic core of enlarging the selected subfamily by one simple summand. -/
theorem disjoint_sup_of_disjoint {A V : Type*}
    [Ring A] [AddCommGroup V] [Module A V]
    {W W' K : Submodule A V} (h1 : Disjoint W K) (h2 : Disjoint W' (W ⊔ K)) :
    Disjoint (W ⊔ W') K := by
  rw [Submodule.disjoint_def]
  intro x hx hxK
  rw [Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have hb_mem : b ∈ W ⊔ K := by
    have hb_eq : b = (a + b) - a := by abel
    rw [hb_eq]
    exact sub_mem (Submodule.mem_sup_right hxK) (Submodule.mem_sup_left ha)
  have hb0 : b = 0 := (Submodule.disjoint_def.mp h2) b hb hb_mem
  have haK : a ∈ K := by rwa [hb0, add_zero] at hxK
  have ha0 : a = 0 := (Submodule.disjoint_def.mp h1) a ha haK
  rw [ha0, hb0, add_zero]

variable {A V U : Type*} [Ring A] [AddCommGroup V] [Module A V] [AddCommGroup U] [Module A U]
  {ι : Type*}

/-- **Lemma 3.1.6 (subfamily complement).** Let `p : ι → Submodule A V` be a family of simple
submodules spanning `V`, and `f : V →ₗ[A] U` any linear map. Then there is a subset `J ⊆ ι`
such that the concrete sub-sum `⨆ i ∈ J, p i` is a complement of `ker f`.

Independence of the family is not needed; a spanning family of simples suffices. -/
theorem exists_subfamily_isCompl_ker (p : ι → Submodule A V)
    (hsimple : ∀ i, IsSimpleModule A (p i)) (hspan : ⨆ i, p i = ⊤) (f : V →ₗ[A] U) :
    ∃ J : Set ι, IsCompl (⨆ i ∈ J, p i) (LinearMap.ker f) := by
  set K := LinearMap.ker f
  -- Chain condition: the union of a chain of injective subsets is again injective.
  have hchain_cond : ∀ c ⊆ { J : Set ι | Disjoint (⨆ i ∈ J, p i) K }, IsChain (· ⊆ ·) c →
      ∃ ub ∈ { J : Set ι | Disjoint (⨆ i ∈ J, p i) K }, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hchain
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    rw [Set.mem_setOf_eq, Submodule.disjoint_def]
    intro x hx hxK
    rcases c.eq_empty_or_nonempty with rfl | hcne
    · rw [Set.sUnion_empty] at hx
      simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Submodule.mem_bot] at hx
      exact hx
    · have : Nonempty ↥c := hcne.to_subtype
      set g : ↥c → Submodule A V := fun J => ⨆ i ∈ (J : Set ι), p i
      have hdir : Directed (· ≤ ·) g := by
        intro J1 J2
        rcases hchain.total J1.2 J2.2 with h | h
        · exact ⟨J2, biSup_mono (fun _ hmem => h hmem), le_refl _⟩
        · exact ⟨J1, le_refl _, biSup_mono (fun _ hmem => h hmem)⟩
      have hTeq : (⨆ i ∈ ⋃₀ c, p i) = ⨆ J : ↥c, g J := by
        apply le_antisymm
        · refine iSup₂_le fun i hi => ?_
          obtain ⟨J, hJc, hiJ⟩ := hi
          exact le_trans (le_iSup₂ (f := fun i (_ : i ∈ (J : Set ι)) => p i) i hiJ)
            (le_iSup g ⟨J, hJc⟩)
        · exact iSup_le fun J => biSup_mono fun _ hmem => Set.mem_sUnion_of_mem hmem J.2
      rw [hTeq, Submodule.mem_iSup_of_directed g hdir] at hx
      obtain ⟨J, hxJ⟩ := hx
      have hJS : Disjoint (⨆ i ∈ (J : Set ι), p i) K := hcS J.2
      exact (Submodule.disjoint_def.mp hJS) x hxJ hxK
  obtain ⟨m, hm⟩ := zorn_subset { J : Set ι | Disjoint (⨆ i ∈ J, p i) K } hchain_cond
  -- `m` is a maximal subset on which `f` is injective; show its span complements `ker f`.
  have hmD : Disjoint (⨆ i ∈ m, p i) K := hm.1
  refine ⟨m, hmD, ?_⟩
  rw [codisjoint_iff]
  by_contra hne
  -- Some simple summand `p i` is not contained in `V_m ⊔ K`.
  have hex : ∃ i, ¬ (p i ≤ (⨆ i ∈ m, p i) ⊔ K) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hle : (⨆ i, p i) ≤ (⨆ i ∈ m, p i) ⊔ K := iSup_le hall
    rw [hspan] at hle
    exact hne (top_le_iff.mp hle)
  obtain ⟨i, hi⟩ := hex
  -- By Schur (`p i` is an atom), `p i` is disjoint from `V_m ⊔ K`.
  have hatom : IsAtom (p i) := isSimpleModule_iff_isAtom.mp (hsimple i)
  have hdisj_i : Disjoint (p i) ((⨆ i ∈ m, p i) ⊔ K) := hatom.not_le_iff_disjoint.mp hi
  -- Hence `insert i m` still keeps `f` injective, contradicting maximality of `m`.
  have hins : (⨆ j ∈ insert i m, p j) = (⨆ j ∈ m, p j) ⊔ p i := by
    rw [iSup_insert]; exact sup_comm _ _
  have hdisj_ins : Disjoint (⨆ j ∈ insert i m, p j) K := by
    rw [hins]; exact disjoint_sup_of_disjoint hmD hdisj_i
  have hi_in : i ∈ m := hm.mem_of_prop_insert hdisj_ins
  exact hi (le_trans (le_iSup₂ (f := fun i (_ : i ∈ m) => p i) i hi_in) le_sup_left)

/-- The restriction of `f` to the selected sub-sum `⨆ i ∈ J, p i` is bijective: this is the
"maps isomorphically onto `U`" content of Lemma 3.1.6. -/
theorem exists_subfamily_bijective (p : ι → Submodule A V)
    (hsimple : ∀ i, IsSimpleModule A (p i)) (hspan : ⨆ i, p i = ⊤)
    (f : V →ₗ[A] U) (hf : Function.Surjective f) :
    ∃ J : Set ι, Function.Bijective (f.domRestrict (⨆ i ∈ J, p i)) := by
  obtain ⟨J, hJ⟩ := exists_subfamily_isCompl_ker p hsimple hspan f
  refine ⟨J, ?_, ?_⟩
  · exact injective_domRestrict_iff.mpr hJ.disjoint
  · -- Surjective: the image of `V_J` is all of `U`.
    have hkermap : (LinearMap.ker f).map f = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨x, hx, rfl⟩
      rw [Submodule.mem_bot]
      exact LinearMap.mem_ker.mp hx
    have hmap : (⨆ i ∈ J, p i).map f = ⊤ := by
      have hcod : (⨆ i ∈ J, p i) ⊔ LinearMap.ker f = ⊤ := codisjoint_iff.mp hJ.codisjoint
      calc (⨆ i ∈ J, p i).map f
          = ((⨆ i ∈ J, p i) ⊔ LinearMap.ker f).map f := by
              rw [Submodule.map_sup, hkermap, sup_bot_eq]
        _ = (⊤ : Submodule A V).map f := by rw [hcod]
        _ = ⊤ := by rw [Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    rw [← LinearMap.range_eq_top, range_domRestrict]
    exact hmap

/-- **Lemma 3.1.6 (source form).** Given a spanning family of simple submodules `p i` and a
surjection `f : V → U`, some sub-sum `⨆ i ∈ J, p i` is carried isomorphically onto `U` by `f`:
the returned equivalence `e` agrees with `f` on the sub-sum. -/
theorem exists_subfamily_linearEquiv (p : ι → Submodule A V)
    (hsimple : ∀ i, IsSimpleModule A (p i)) (hspan : ⨆ i, p i = ⊤)
    (f : V →ₗ[A] U) (hf : Function.Surjective f) :
    ∃ J : Set ι, ∃ e : ↥(⨆ i ∈ J, p i) ≃ₗ[A] U, ∀ x, e x = f x := by
  obtain ⟨J, hbij⟩ := exists_subfamily_bijective p hsimple hspan f hf
  exact ⟨J, LinearEquiv.ofBijective (f.domRestrict _) hbij, fun _ => rfl⟩

/-- **Lemma 3.1.6 (book form with `V = ⨁ᵢ Vᵢ`).** When the simple submodules `p i` form an
internal direct sum decomposing all of `V`, any surjection `f : V → U` restricts to an
isomorphism from some concrete sub-direct-sum `⨆ i ∈ J, p i` onto `U`. -/
theorem exists_subfamily_linearEquiv_of_isInternal [DecidableEq ι] (p : ι → Submodule A V)
    (hInt : DirectSum.IsInternal p) (hsimple : ∀ i, IsSimpleModule A (p i))
    (f : V →ₗ[A] U) (hf : Function.Surjective f) :
    ∃ J : Set ι, ∃ e : ↥(⨆ i ∈ J, p i) ≃ₗ[A] U, ∀ x, e x = f x :=
  exists_subfamily_linearEquiv p hsimple hInt.submodule_iSup_eq_top f hf

end Etingof
