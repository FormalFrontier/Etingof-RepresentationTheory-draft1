import Mathlib

/-!
# Proposition 5.3.2: Character Values Yield Algebraic Integers

For an irreducible representation `V` of a finite group `G`, and a conjugacy class `C`
with representative `g`, the number `λ = χ_V(g) · |C| / dim(V)` is an algebraic integer.

**Book proof (Etingof Proposition 5.3.2).** Let `C` be the conjugacy class of `g` and
`P = ∑_{h ∈ C} h ∈ ℤ[G]`. Then `P` is central in `ℤ[G]`, so it acts on `V` by a scalar
`λ`, which is an algebraic integer (since `ℤ[G]` is a finitely generated `ℤ`-module,
every element is integral over `ℤ`). Taking the trace of `P` on `V` gives
`|C| · χ_V(g) = λ · dim V`, so `λ = |C| · χ_V(g) / dim V`.

## Mathlib correspondence

Uses `IsIntegral ℤ`, `MonoidAlgebra`, Schur's lemma for `FDRep`
(`FDRep.finrank_hom_simple_simple`), and `IsIntegral.of_finite` (the integral group
ring is module-finite over `ℤ`).
-/

open CategoryTheory

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Proposition 5.3.2.** For an irreducible representation `V` and conjugacy class
of `g`, the product `λ = |C| · χ_V(g) / dim(V)` is an algebraic integer.

The class sum `σ = ∑_{h ∈ C(g)} ρ(h)` commutes with the `G`-action, hence acts as a
scalar `λ · id` on `V` by Schur's lemma. Taking the trace gives `λ = |C| · χ(g) / dim V`.
The scalar `λ` is an algebraic integer because `σ` lies in the image of the integral
group ring `ℤ[G]`, which is module-finite over `ℤ`. -/
theorem Etingof.Proposition5_3_2
    (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (V : FDRep ℂ G) [Simple V]
    (g : G)
    (hn : 0 < Module.finrank ℂ V) :
    IsIntegral ℤ ((Fintype.card { h : G // IsConj g h } : ℂ) * V.character g /
      (Module.finrank ℂ V : ℂ)) := by
  set C := Fintype.card { h : G // IsConj g h }
  set d := Module.finrank ℂ V
  -- Step 1: The class sum σ = ∑_{h conj g} ρ(h)
  set σ := ∑ h : { h : G // IsConj g h }, V.ρ (h : G) with hσ_def
  -- Step 2: σ = c • id for some scalar c (Schur's lemma for FDRep)
  -- σ commutes with V.ρ, hence is a G-equivariant endomorphism of V.
  -- Since V is simple and ℂ is algebraically closed, End_G(V) ≅ ℂ.
  have ⟨c, hc⟩ : ∃ c : ℂ, σ = c • (LinearMap.id : V.V.obj →ₗ[ℂ] V.V.obj) := by
    -- σ commutes with all V.ρ a (conjugation permutes the conjugacy class)
    have hσ_comm : ∀ a : G, σ.comp (V.ρ a) = (V.ρ a).comp σ := by
      intro a
      ext v
      simp only [hσ_def, LinearMap.sum_apply, LinearMap.comp_apply]
      -- Goal: ∑_h V.ρ h (V.ρ a v) = V.ρ a (∑_h V.ρ h v)
      rw [map_sum]
      -- Goal: ∑_h V.ρ h (V.ρ a v) = ∑_h V.ρ a (V.ρ h v)
      -- Rewrite using V.ρ h (V.ρ a v) = V.ρ (h * a) v and V.ρ a (V.ρ h v) = V.ρ (a * h) v
      simp_rw [← Module.End.mul_apply, ← map_mul]
      -- Goal: ∑_h V.ρ (h * a) v = ∑_h V.ρ (a * h) v
      -- Conjugation by a⁻¹ is bijection on conjugacy class: e(h) = a⁻¹ha, so a·e(h) = h·a
      let e : { h : G // IsConj g h } ≃ { h : G // IsConj g h } :=
        { toFun := fun ⟨h, hh⟩ => ⟨a⁻¹ * h * a, by
            obtain ⟨k, rfl⟩ := isConj_iff.mp hh
            exact isConj_iff.mpr ⟨a⁻¹ * k, by group⟩⟩
          invFun := fun ⟨h, hh⟩ => ⟨a * h * a⁻¹, by
            obtain ⟨k, rfl⟩ := isConj_iff.mp hh
            exact isConj_iff.mpr ⟨a * k, by group⟩⟩
          left_inv := fun ⟨h, _⟩ => by ext; simp; group
          right_inv := fun ⟨h, _⟩ => by ext; simp; group }
      exact Fintype.sum_equiv e _ _ (fun x => by
        dsimp [e]; congr 1; group)
    -- Construct σ as a G-equivariant endomorphism (Action.Hom)
    -- Since V is simple and ℂ is alg closed, End_G(V) has rank 1, so σ_hom = c • 𝟙 V
    have hrank : Module.finrank ℂ (V ⟶ V) = 1 := by
      rw [FDRep.finrank_hom_simple_simple V V, if_pos ⟨Iso.refl V⟩]
    -- 𝟙 V is nonzero
    have hid_ne : (𝟙 V : V ⟶ V) ≠ 0 := by
      intro h
      apply id_nonzero V
      exact_mod_cast h
    -- Build Action.Hom from σ
    let σ_hom : V ⟶ V :=
      { hom := FGModuleCat.ofHom σ
        comm := fun g => by
          ext v
          exact congr_fun (congr_arg DFunLike.coe (hσ_comm g)) v }
    -- Every element of End_G(V) is a scalar multiple of 𝟙 V
    obtain ⟨c, hc_eq⟩ := (finrank_eq_one_iff_of_nonzero' (𝟙 V) hid_ne).mp hrank σ_hom
    refine ⟨c, ?_⟩
    -- Extract: from hc_eq (categorical), get linear map equality
    have h1 : σ_hom.hom = (c • 𝟙 V).hom := congr_arg Action.Hom.hom hc_eq.symm
    -- Extract .hom.hom to get ModuleCat.Hom equality, then .hom for LinearMap
    have h2 := congr_arg (fun f : V.V ⟶ V.V => InducedCategory.Hom.hom f |>.hom) h1
    -- h2 relates σ to c • id at the LinearMap level
    apply LinearMap.ext
    intro v
    have := congr_arg (fun f : V.V.obj →ₗ[ℂ] V.V.obj => f v) h2
    exact this
  -- Step 3: c = C * χ(g) / d via trace computation
  have hc_val : c = (C : ℂ) * V.character g / (d : ℂ) := by
    have hdim_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    -- trace(σ) = ∑_{h conj g} χ(h) = C * χ(g)
    have ht1 : LinearMap.trace ℂ V.V.obj σ = (C : ℂ) * V.character g := by
      simp only [hσ_def, map_sum]
      -- Character is constant on conjugacy classes
      have : ∀ h : { h : G // IsConj g h },
          (LinearMap.trace ℂ V.V.obj) (V.ρ (h : G)) = V.character g := by
        intro ⟨h, hh⟩
        -- V.character h = V.character g since h is conjugate to g
        show V.character h = V.character g
        obtain ⟨c, rfl⟩ := isConj_iff.mp hh
        exact V.char_conj g c
      simp_rw [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
    -- trace(c • id) = c * d
    rw [hc] at ht1
    simp only [map_smul, LinearMap.trace_id, smul_eq_mul] at ht1
    have hd_eq : (Module.finrank ℂ (V.V.obj) : ℂ) = (d : ℂ) := by rfl
    rw [hd_eq] at ht1
    exact eq_div_of_mul_eq hdim_ne ht1
  -- Step 4: c is integral over ℤ
  -- σ is in the image of MonoidAlgebra ℤ G (module-finite over ℤ), hence integral.
  -- Since σ = algebraMap ℂ End(V) c and this map is injective, c is integral.
  rw [← hc_val]
  -- The class sum element in ℤ[G]
  set e : MonoidAlgebra ℤ G := ∑ h : { h : G // IsConj g h }, MonoidAlgebra.of ℤ G h
  -- e is integral over ℤ (MonoidAlgebra ℤ G is module-finite over ℤ)
  have he : IsIntegral ℤ e := IsIntegral.of_finite ℤ e
  -- The representation ring hom: ℤ[G] → End(V)
  let φ : MonoidAlgebra ℤ G →+* Module.End ℂ V.V.obj :=
    ((Representation.asAlgebraHom V.ρ).toRingHom).comp
      (MonoidAlgebra.mapRingHom G (Int.castRingHom ℂ))
  -- φ(e) = σ = c • id
  have hφe : φ e = c • LinearMap.id := by
    have hφ_of : ∀ h : G, φ (MonoidAlgebra.of ℤ G h) = V.ρ h := by
      intro h; simp [φ]
    show φ (∑ h : { h : G // IsConj g h }, MonoidAlgebra.of ℤ G h) = c • LinearMap.id
    rw [map_sum]; simp_rw [hφ_of]; exact hc
  -- φ(e) is integral over ℤ; transfer via ring hom
  have hφe_int : IsIntegral ℤ (φ e) := he.map φ.toIntAlgHom
  rw [hφe] at hφe_int
  -- Extract c from c • id using injectivity of algebraMap ℂ → End(V)
  haveI : Nontrivial V.V.obj := Module.nontrivial_of_finrank_pos hn
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom ℤ ℂ (Module.End ℂ V.V.obj))
    (FaithfulSMul.algebraMap_injective ℂ (Module.End ℂ V.V.obj))).mp
    (by convert hφe_int using 2; simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id])
