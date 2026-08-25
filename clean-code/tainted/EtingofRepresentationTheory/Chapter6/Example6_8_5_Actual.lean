import EtingofRepresentationTheory.Chapter6.Example6_8_5
import EtingofRepresentationTheory.Chapter6.OrientationDefs
import EtingofRepresentationTheory.Chapter6.CoxeterInfrastructure
import EtingofRepresentationTheory.Chapter6.Corollary6_8_4
import EtingofRepresentationTheory.Infrastructure.QuiverCompositionSeries

/-!
# The actual D₄ reflection-functor computation

This file upgrades the root-lattice calculation in `Example6_8_5` to a chain of actual
quiver representations.  The original D₄ orientation has its three arms pointing into the
central vertex.  Successively reflecting the three arms and then the centre produces the
representations occurring in the source example.
-/

namespace Etingof.Example6_8_5

abbrev Q₀ : Quiver (Fin 4) := Etingof.standardOrientation Etingof.D₄_adj
noncomputable abbrev Q₁ : Quiver (Fin 4) := @Etingof.reversedAtVertex (Fin 4) _ Q₀ 0
noncomputable abbrev Q₂ : Quiver (Fin 4) := @Etingof.reversedAtVertex (Fin 4) _ Q₁ 1
noncomputable abbrev Q₃ : Quiver (Fin 4) := @Etingof.reversedAtVertex (Fin 4) _ Q₂ 2
noncomputable abbrev Q₄ : Quiver (Fin 4) := @Etingof.reversedAtVertex (Fin 4) _ Q₃ 3

local instance Q₁_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) Q₁ a b) :=
  @Etingof.subsingleton_hom_reversedAtVertex 4 _ Q₀
    (fun x y => Etingof.standardOrientation_subsingleton Etingof.D₄_adj x y) 0 a b

local instance Q₂_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) Q₂ a b) :=
  @Etingof.subsingleton_hom_reversedAtVertex 4 _ Q₁ (fun x y => Q₁_subsingleton x y) 1 a b

instance Q₃_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) Q₃ a b) :=
  @Etingof.subsingleton_hom_reversedAtVertex 4 _ Q₂ (fun x y => Q₂_subsingleton x y) 2 a b

noncomputable local instance arrowsOut₀ :
    Fintype (@Etingof.ArrowsOutOf (Fin 4) Q₀ 0) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) Q₀ 0 b) :=
    fun b => @Etingof.fintypeHomOfSubsingleton (Fin 4) Q₀
      (fun x y => Etingof.standardOrientation_subsingleton Etingof.D₄_adj x y) 0 b
  exact Sigma.instFintype

noncomputable local instance arrowsOut₁ :
    Fintype (@Etingof.ArrowsOutOf (Fin 4) Q₁ 1) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) Q₁ 1 b) :=
    fun b => @Etingof.fintypeHomOfSubsingleton (Fin 4) Q₁
      (fun x y => Q₁_subsingleton x y) 1 b
  exact Sigma.instFintype

noncomputable local instance arrowsOut₂ :
    Fintype (@Etingof.ArrowsOutOf (Fin 4) Q₂ 2) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) Q₂ 2 b) :=
    fun b => @Etingof.fintypeHomOfSubsingleton (Fin 4) Q₂
      (fun x y => Q₂_subsingleton x y) 2 b
  exact Sigma.instFintype

noncomputable local instance arrowsOut₃ :
    Fintype (@Etingof.ArrowsOutOf (Fin 4) Q₃ 3) := by
  haveI : ∀ b : Fin 4, Fintype (@Quiver.Hom (Fin 4) Q₃ 3 b) :=
    fun b => @Etingof.fintypeHomOfSubsingleton (Fin 4) Q₃
      (fun x y => Q₃_subsingleton x y) 3 b
  exact Sigma.instFintype

private theorem source₀ : @Etingof.IsSource (Fin 4) Q₀ 0 := by
  intro j
  constructor
  rintro ⟨⟨_, hj⟩⟩
  omega

private theorem source₁ : @Etingof.IsSource (Fin 4) Q₁ 1 := by
  intro j
  constructor
  intro e
  change @Etingof.ReversedAtVertexHom (Fin 4) _ Q₀ 0 j 1 at e
  by_cases hj : j = 0
  · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 4) _ Q₀ 0 j 1 hj
      (by decide : (1 : Fin 4) ≠ 0)] at e
    exact (source₀ 1).false e
  · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 4) _ Q₀ 0 j 1 hj
      (by decide : (1 : Fin 4) ≠ 0)] at e
    rcases e with ⟨⟨_, hlt⟩⟩
    omega

private theorem source₂ : @Etingof.IsSource (Fin 4) Q₂ 2 := by
  intro j
  constructor
  intro e
  change @Etingof.ReversedAtVertexHom (Fin 4) _ Q₁ 1 j 2 at e
  by_cases hj : j = 1
  · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 4) _ Q₁ 1 j 2 hj
      (by decide : (2 : Fin 4) ≠ 1)] at e
    exact (source₁ 2).false e
  · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 4) _ Q₁ 1 j 2 hj
      (by decide : (2 : Fin 4) ≠ 1)] at e
    change @Etingof.ReversedAtVertexHom (Fin 4) _ Q₀ 0 j 2 at e
    by_cases hj0 : j = 0
    · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 4) _ Q₀ 0 j 2 hj0
        (by decide : (2 : Fin 4) ≠ 0)] at e
      exact (source₀ 2).false e
    · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 4) _ Q₀ 0 j 2 hj0
        (by decide : (2 : Fin 4) ≠ 0)] at e
      rcases e with ⟨⟨_, hlt⟩⟩
      omega

theorem source₃ : @Etingof.IsSource (Fin 4) Q₃ 3 := by
  intro j
  constructor
  intro e
  change @Etingof.ReversedAtVertexHom (Fin 4) _ Q₂ 2 j 3 at e
  by_cases hj : j = 2
  · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 4) _ Q₂ 2 j 3 hj
      (by decide : (3 : Fin 4) ≠ 2)] at e
    exact (source₂ 3).false e
  · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 4) _ Q₂ 2 j 3 hj
      (by decide : (3 : Fin 4) ≠ 2)] at e
    change @Etingof.ReversedAtVertexHom (Fin 4) _ Q₁ 1 j 3 at e
    by_cases hj1 : j = 1
    · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 4) _ Q₁ 1 j 3 hj1
        (by decide : (3 : Fin 4) ≠ 1)] at e
      exact (source₁ 3).false e
    · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 4) _ Q₁ 1 j 3 hj1
        (by decide : (3 : Fin 4) ≠ 1)] at e
      change @Etingof.ReversedAtVertexHom (Fin 4) _ Q₀ 0 j 3 at e
      by_cases hj0 : j = 0
      · rw [@Etingof.ReversedAtVertexHom_eq_ne (Fin 4) _ Q₀ 0 j 3 hj0
          (by decide : (3 : Fin 4) ≠ 0)] at e
        exact (source₀ 3).false e
      · rw [@Etingof.ReversedAtVertexHom_ne_ne (Fin 4) _ Q₀ 0 j 3 hj0
          (by decide : (3 : Fin 4) ≠ 0)] at e
        rcases e with ⟨⟨_, hlt⟩⟩
        omega

/-- The simple representation `V_{α₄}` on the inward D₄ orientation. -/
noncomputable abbrev V₀ : @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₀ :=
  Etingof.simpleRepresentation ℂ 3

/-- The actual result after applying `F⁻₁`. -/
noncomputable abbrev V₁ : @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₁ :=
  @Etingof.reflectionFunctorMinus ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀ arrowsOut₀

/-- The actual result after applying `F⁻₂ F⁻₁`. -/
noncomputable abbrev V₂ : @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₂ :=
  @Etingof.reflectionFunctorMinus ℂ _ (Fin 4) _ Q₁ 1 source₁ V₁ arrowsOut₁

/-- The actual result after applying `F⁻₃ F⁻₂ F⁻₁`. -/
noncomputable abbrev V₃ : @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₃ :=
  @Etingof.reflectionFunctorMinus ℂ _ (Fin 4) _ Q₂ 2 source₂ V₂ arrowsOut₂

/-- The actual result after applying `F⁻₄ F⁻₃ F⁻₂ F⁻₁`. -/
noncomputable abbrev V₄ : @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₄ :=
  @Etingof.reflectionFunctorMinus ℂ _ (Fin 4) _ Q₃ 3 source₃ V₃ arrowsOut₃

private lemma reflected_free_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation ℂ Q)
    [∀ v, Module.Free ℂ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Free ℂ (@Etingof.QuiverRepresentation.obj ℂ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v) :=
  Module.Free.of_equiv (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).symm

private lemma reflected_finite_ne
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation ℂ Q)
    [∀ v, Module.Finite ℂ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)]
    (v : Q) (hv : v ≠ i) :
    Module.Finite ℂ (@Etingof.QuiverRepresentation.obj ℂ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) v) :=
  Module.Finite.equiv (Etingof.reflFunctorMinus_equivAt_ne hi ρ v hv).symm

set_option linter.unusedFintypeInType false in
private lemma reflected_free_eq
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation ℂ Q)
    [∀ v, Module.Free ℂ (ρ.obj v)] [∀ v, Module.Finite ℂ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    Module.Free ℂ (@Etingof.QuiverRepresentation.obj ℂ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := ℂ)
  exact Module.Free.of_equiv (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm

set_option linter.unusedFintypeInType false in
private lemma reflected_finite_eq
    {Q : Type*} [DecidableEq Q] [Quiver Q]
    {i : Q} (hi : Etingof.IsSource Q i)
    (ρ : Etingof.QuiverRepresentation ℂ Q)
    [∀ v, Module.Free ℂ (ρ.obj v)] [∀ v, Module.Finite ℂ (ρ.obj v)]
    [Fintype (Etingof.ArrowsOutOf Q i)] :
    Module.Finite ℂ (@Etingof.QuiverRepresentation.obj ℂ Q _
      (Etingof.reversedAtVertex Q i)
      (Etingof.reflectionFunctorMinus Q i hi ρ) i) := by
  letI : AddCommGroup (DirectSum (Etingof.ArrowsOutOf Q i) (fun a => ρ.obj a.1)) :=
    Etingof.addCommGroupOfRing (k := ℂ)
  exact Module.Finite.equiv (Etingof.reflFunctorMinus_equivAt_eq hi ρ).symm

noncomputable local instance V₁_free (v : Fin 4) : Module.Free ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₁ V₁ v) := by
  by_cases hv : v = 0
  · subst v
    exact @reflected_free_eq (Fin 4) _ Q₀ 0 source₀ V₀
      (fun w => inferInstance) (fun w => inferInstance) arrowsOut₀
  · exact @reflected_free_ne (Fin 4) _ Q₀ 0 source₀ V₀
      (fun w => inferInstance) arrowsOut₀ v hv

noncomputable local instance V₁_finite (v : Fin 4) : Module.Finite ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₁ V₁ v) := by
  by_cases hv : v = 0
  · subst v
    exact @reflected_finite_eq (Fin 4) _ Q₀ 0 source₀ V₀
      (fun w => inferInstance) (fun w => inferInstance) arrowsOut₀
  · exact @reflected_finite_ne (Fin 4) _ Q₀ 0 source₀ V₀
      (fun w => inferInstance) arrowsOut₀ v hv

noncomputable local instance V₂_free (v : Fin 4) : Module.Free ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₂ V₂ v) := by
  by_cases hv : v = 1
  · subst v
    exact @reflected_free_eq (Fin 4) _ Q₁ 1 source₁ V₁
      (fun w => V₁_free w) (fun w => V₁_finite w) arrowsOut₁
  · exact @reflected_free_ne (Fin 4) _ Q₁ 1 source₁ V₁
      (fun w => V₁_free w) arrowsOut₁ v hv

noncomputable local instance V₂_finite (v : Fin 4) : Module.Finite ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₂ V₂ v) := by
  by_cases hv : v = 1
  · subst v
    exact @reflected_finite_eq (Fin 4) _ Q₁ 1 source₁ V₁
      (fun w => V₁_free w) (fun w => V₁_finite w) arrowsOut₁
  · exact @reflected_finite_ne (Fin 4) _ Q₁ 1 source₁ V₁
      (fun w => V₁_finite w) arrowsOut₁ v hv

noncomputable instance V₃_free (v : Fin 4) : Module.Free ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ v) := by
  by_cases hv : v = 2
  · subst v
    exact @reflected_free_eq (Fin 4) _ Q₂ 2 source₂ V₂
      (fun w => V₂_free w) (fun w => V₂_finite w) arrowsOut₂
  · exact @reflected_free_ne (Fin 4) _ Q₂ 2 source₂ V₂
      (fun w => V₂_free w) arrowsOut₂ v hv

noncomputable instance V₃_finite (v : Fin 4) : Module.Finite ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ v) := by
  by_cases hv : v = 2
  · subst v
    exact @reflected_finite_eq (Fin 4) _ Q₂ 2 source₂ V₂
      (fun w => V₂_free w) (fun w => V₂_finite w) arrowsOut₂
  · exact @reflected_finite_ne (Fin 4) _ Q₂ 2 source₂ V₂
      (fun w => V₂_finite w) arrowsOut₂ v hv

noncomputable local instance V₄_free (v : Fin 4) : Module.Free ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₄ V₄ v) := by
  by_cases hv : v = 3
  · subst v
    exact @reflected_free_eq (Fin 4) _ Q₃ 3 source₃ V₃
      (fun w => V₃_free w) (fun w => V₃_finite w) arrowsOut₃
  · exact @reflected_free_ne (Fin 4) _ Q₃ 3 source₃ V₃
      (fun w => V₃_free w) arrowsOut₃ v hv

noncomputable local instance V₄_finite (v : Fin 4) : Module.Finite ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₄ V₄ v) := by
  by_cases hv : v = 3
  · subst v
    exact @reflected_finite_eq (Fin 4) _ Q₃ 3 source₃ V₃
      (fun w => V₃_free w) (fun w => V₃_finite w) arrowsOut₃
  · exact @reflected_finite_ne (Fin 4) _ Q₃ 3 source₃ V₃
      (fun w => V₃_finite w) arrowsOut₃ v hv

/-- At a source of a simply-laced orientation, the outgoing-arrow reflection used by
Proposition 6.6.8 is the Cartan-matrix simple reflection.  Unlike the global Dynkin
version, this concrete helper needs only symmetry and the `0/1` adjacency property. -/
private lemma reflectionDim_eq_cartan
    {n : ℕ} {adj : Matrix (Fin n) (Fin n) ℤ}
    (hsymm : adj.IsSymm) (hzeroone : ∀ i j, adj i j = 0 ∨ adj i j = 1)
    {Q : Quiver (Fin n)} (hOrient : Etingof.IsOrientationOf Q adj)
    [hSS : ∀ (a b : Fin n), Subsingleton (@Quiver.Hom (Fin n) Q a b)]
    (p : Fin n) (hp : @Etingof.IsSource (Fin n) Q p)
    (d : Fin n → ℤ) [hArrows : Fintype (@Etingof.ArrowsOutOf (Fin n) Q p)] :
    Etingof.simpleReflectionDimVector
        (fun (a : @Etingof.ArrowsOutOf (Fin n) Q p) => a.1) p d =
      Etingof.simpleReflection n (Etingof.cartanMatrix n adj) p d := by
  haveI : ∀ (a b : Fin n), Fintype (@Quiver.Hom (Fin n) Q a b) :=
    fun a b => Etingof.fintypeHomOfSubsingleton a b
  ext v
  unfold Etingof.simpleReflectionDimVector Etingof.simpleReflection Etingof.rootReflection
  by_cases hv : v = p
  · subst v
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one,
      if_true]
    have hdot : dotProduct d
        ((Etingof.cartanMatrix n adj).mulVec (Pi.single p 1)) =
          2 * d p - ∑ j : Fin n, adj p j * d j := by
      simp only [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp only [Etingof.cartanMatrix]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      simp_rw [mul_comm (d _) (adj _ _)]
      simp_rw [show ∀ x, adj x p = adj p x from fun x => by
        exact congr_fun (congr_fun hsymm p) x]
      ring
    have hcard : ∀ j : Fin n,
        (Fintype.card (@Quiver.Hom (Fin n) Q p j) : ℤ) = adj p j := by
      intro j
      rcases hzeroone p j with h0 | h1
      · haveI : IsEmpty (@Quiver.Hom (Fin n) Q p j) := hOrient.1 p j (by omega)
        rw [Fintype.card_eq_zero]
        omega
      · rcases hOrient.2.1 p j h1 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · haveI : Unique (@Quiver.Hom (Fin n) Q p j) :=
            { default := e, uniq := fun a => Subsingleton.elim a e }
          simp [Fintype.card_unique, h1]
        · exact ((hp j).false e).elim
    have hsum : (∑ a : @Etingof.ArrowsOutOf (Fin n) Q p, d a.fst) =
        ∑ j : Fin n, adj p j * d j := by
      letI sigmaFT : Fintype (Σ j : Fin n, @Quiver.Hom (Fin n) Q p j) := Sigma.instFintype
      have h_unfold : (∑ a : @Etingof.ArrowsOutOf (Fin n) Q p, d a.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ sigmaFT) (fun a => d a.fst) := by
        apply Finset.sum_congr
        · ext x
          exact iff_of_true (Finset.mem_univ x) (@Finset.mem_univ _ sigmaFT x)
        · intros
          rfl
      rw [h_unfold, Fintype.sum_sigma]
      congr 1
      ext j
      change (∑ _ : @Quiver.Hom (Fin n) Q p j, d j) = adj p j * d j
      rw [Finset.sum_const, nsmul_eq_mul]
      have h : (Finset.univ (α := @Quiver.Hom (Fin n) Q p j)).card = Fintype.card _ := rfl
      rw [h, show (Fintype.card (@Quiver.Hom (Fin n) Q p j) : ℤ) = adj p j from hcard j]
    have hsame : ∀ (inst1 inst2 : Fintype (@Etingof.ArrowsOutOf (Fin n) Q p)),
        @Finset.sum _ _ _ (@Finset.univ _ inst1) (fun x => d x.fst) =
          @Finset.sum _ _ _ (@Finset.univ _ inst2) (fun x => d x.fst) := by
      intro i1 i2
      apply Finset.sum_congr
      · ext x
        exact iff_of_true (@Finset.mem_univ _ i1 x) (@Finset.mem_univ _ i2 x)
      · intros
        rfl
    linarith [hsame hArrows inferInstance, hsum, hdot]
  · simp only [hv, ite_false, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_zero, sub_zero]

private theorem adj_symm : Etingof.D₄_adj.IsSymm := by decide
private theorem adj_diag : ∀ i, Etingof.D₄_adj i i = 0 := by decide
private theorem adj_zero_one : ∀ i j, Etingof.D₄_adj i j = 0 ∨ Etingof.D₄_adj i j = 1 := by
  decide

private theorem orient₀ : Etingof.IsOrientationOf Q₀ Etingof.D₄_adj :=
  Etingof.standardOrientation_isOrientationOf Etingof.D₄_adj adj_symm adj_diag

private theorem orient₁ : Etingof.IsOrientationOf Q₁ Etingof.D₄_adj :=
  Etingof.reversedAtVertex_isOrientationOf adj_symm adj_diag orient₀ 0

private theorem orient₂ : Etingof.IsOrientationOf Q₂ Etingof.D₄_adj :=
  Etingof.reversedAtVertex_isOrientationOf adj_symm adj_diag orient₁ 1

theorem orient₃ : Etingof.IsOrientationOf Q₃ Etingof.D₄_adj :=
  Etingof.reversedAtVertex_isOrientationOf adj_symm adj_diag orient₂ 2

private theorem sourceMap₀_injective : Function.Injective
    (@Etingof.QuiverRepresentation.sourceMap ℂ _ (Fin 4) Q₀ V₀ 0 arrowsOut₀) := by
  intro x y _
  change (Fin 0 → ℂ) at x y
  exact funext fun z => z.elim0

private theorem sourceMap₁_injective : Function.Injective
    (@Etingof.QuiverRepresentation.sourceMap ℂ _ (Fin 4) Q₁ V₁ 1 arrowsOut₁) := by
  intro x y _
  apply (@Etingof.reflFunctorMinus_equivAt_ne ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀
    arrowsOut₀ 1 (by decide)).injective
  have hsub : Subsingleton
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 1) := by
    change Subsingleton (Fin 0 → ℂ)
    infer_instance
  exact hsub.elim _ _

private theorem sourceMap₂_injective : Function.Injective
    (@Etingof.QuiverRepresentation.sourceMap ℂ _ (Fin 4) Q₂ V₂ 2 arrowsOut₂) := by
  intro x y _
  apply (@Etingof.reflFunctorMinus_equivAt_ne ℂ _ (Fin 4) _ Q₁ 1 source₁ V₁
    arrowsOut₁ 2 (by decide)).injective
  apply (@Etingof.reflFunctorMinus_equivAt_ne ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀
    arrowsOut₀ 2 (by decide)).injective
  have hsub : Subsingleton
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 2) := by
    change Subsingleton (Fin 0 → ℂ)
    infer_instance
  exact hsub.elim _ _

private theorem V₀_dimensionVector (v : Fin 4) :
    (Module.finrank ℂ (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ v) : ℤ) =
      Etingof.D₄_α₄ v := by
  change (Module.finrank ℂ (Fin (if v = 3 then 1 else 0) → ℂ) : ℤ) = _
  rw [Module.finrank_pi_fintype]
  by_cases hv : v = 3
  · subst v
    simp [Etingof.D₄_α₄, Etingof.simpleRoot]
  · simp [Etingof.D₄_α₄, Etingof.simpleRoot, hv]

/-- The first actual reflection has dimension vector `(1,0,0,1)`. -/
theorem V₁_dimensionVector (v : Fin 4) :
    ((@Etingof.QuiverRepresentation.finrankAt' ℂ _ (Fin 4) Q₁ V₁ v : ℕ) : ℤ) =
      ![1, 0, 0, 1] v := by
  have h := @Etingof.Proposition6_6_8_source ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀
    (fun w => inferInstance) (fun w => inferInstance) arrowsOut₀ sourceMap₀_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₀ 0 source₀] at h
  have hd : (fun w => (Module.finrank ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ w) : ℤ)) = Etingof.D₄_α₄ := by
    ext w
    exact V₀_dimensionVector w
  rw [hd] at h
  have href : Etingof.simpleReflection 4
      (Etingof.cartanMatrix 4 Etingof.D₄_adj) 0 Etingof.D₄_α₄ =
      ![1, 0, 0, 1] := by decide
  rw [href] at h
  exact h

/-- The second actual reflection has dimension vector `(1,1,0,1)`. -/
theorem V₂_dimensionVector (v : Fin 4) :
    ((@Etingof.QuiverRepresentation.finrankAt' ℂ _ (Fin 4) Q₂ V₂ v : ℕ) : ℤ) =
      ![1, 1, 0, 1] v := by
  have h := @Etingof.Proposition6_6_8_source ℂ _ (Fin 4) _ Q₁ 1 source₁ V₁
    (fun w => V₁_free w) (fun w => V₁_finite w) arrowsOut₁ sourceMap₁_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₁ 1 source₁] at h
  have hd : (fun w => (Module.finrank ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₁ V₁ w) : ℤ)) = ![1, 0, 0, 1] := by
    ext w
    exact V₁_dimensionVector w
  rw [hd] at h
  have href : Etingof.simpleReflection 4
      (Etingof.cartanMatrix 4 Etingof.D₄_adj) 1 ![1, 0, 0, 1] =
      ![1, 1, 0, 1] := by decide
  rw [href] at h
  exact h

/-- Applying the three arm reflections to the actual simple representation gives an actual
representation with dimension vector `(1,1,1,1)`. -/
theorem V₃_dimensionVector (v : Fin 4) :
    ((@Etingof.QuiverRepresentation.finrankAt' ℂ _ (Fin 4) Q₃ V₃ v : ℕ) : ℤ) =
      ![1, 1, 1, 1] v := by
  have h := @Etingof.Proposition6_6_8_source ℂ _ (Fin 4) _ Q₂ 2 source₂ V₂
    (fun w => V₂_free w) (fun w => V₂_finite w) arrowsOut₂ sourceMap₂_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₂ 2 source₂] at h
  have hd : (fun w => (Module.finrank ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₂ V₂ w) : ℤ)) = ![1, 1, 0, 1] := by
    ext w
    exact V₂_dimensionVector w
  rw [hd] at h
  have href : Etingof.simpleReflection 4
      (Etingof.cartanMatrix 4 Etingof.D₄_adj) 2 ![1, 1, 0, 1] =
      ![1, 1, 1, 1] := by decide
  rw [href] at h
  exact h

set_option maxHeartbeats 400000 in
-- The one-dimensional complement argument unfolds four bundled vertex spaces.
private theorem simpleRepresentation_indecomposable_local
    (k : Type*) [Field k] {n : ℕ} (p : Fin n) {Q : Quiver (Fin n)} :
    (Etingof.simpleRepresentation k p (Q := Q)).IsIndecomposable := by
  refine ⟨⟨p, ?_⟩, fun W₁ W₂ _ _ hcompl => ?_⟩
  · change Nontrivial (Fin (if p = p then 1 else 0) → k)
    simp only [ite_true]
    exact Pi.nontrivial
  · have hbot : ∀ v, v ≠ p → W₁ v = ⊥ ∧ W₂ v = ⊥ := by
      intro v hv
      have hempty : IsEmpty (Fin (if v = p then 1 else 0)) := by
        simp only [hv, ite_false]
        exact Fin.isEmpty
      haveI : Subsingleton ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
        show Subsingleton (Fin (if v = p then 1 else 0) → k) from inferInstance
      exact ⟨Submodule.eq_bot_of_subsingleton, Submodule.eq_bot_of_subsingleton⟩
    have hdim : Module.finrank k (Fin (if p = p then 1 else 0) → k) = 1 := by simp
    have hcompl_p := hcompl p
    have hcentre : W₁ p = ⊥ ∨ W₂ p = ⊥ := by
      letI : ∀ v, AddCommGroup ((Etingof.simpleRepresentation k p (Q := Q)).obj v) :=
        fun v => Etingof.addCommGroupOfRing (k := k)
      by_contra h
      push Not at h
      obtain ⟨h₁, h₂⟩ := h
      have hr₁ := Submodule.one_le_finrank_iff.mpr h₁
      have hr₂ := Submodule.one_le_finrank_iff.mpr h₂
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq (W₁ p) (W₂ p)
      rw [hcompl_p.sup_eq_top, hcompl_p.inf_eq_bot, finrank_top, finrank_bot] at hsum
      have hdim' : Module.finrank k
          ((Etingof.simpleRepresentation k p (Q := Q)).obj p) = 1 := hdim
      omega
    rcases hcentre with h | h
    · left
      intro v
      by_cases hv : v = p
      · subst v
        exact h
      · exact (hbot v hv).1
    · right
      intro v
      by_cases hv : v = p
      · subst v
        exact h
      · exact (hbot v hv).2

private theorem V₀_indecomposable :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) Q₀ V₀ :=
  simpleRepresentation_indecomposable_local ℂ 3

theorem V₁_indecomposable :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) Q₁ V₁ := by
  rcases @Etingof.Proposition6_6_7_source ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀
      (fun w => inferInstance) (fun w => inferInstance) arrowsOut₀ V₀_indecomposable with h | hz
  · exact h
  · exfalso
    have hsub₁ := hz 3
    let e := @Etingof.reflFunctorMinus_equivAt_ne ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀
      arrowsOut₀ 3 (by decide)
    have hsub₀ : Subsingleton
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 3) :=
      ⟨fun x y => e.symm.injective (hsub₁.elim _ _)⟩
    letI : Nontrivial (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 3) := by
      change Nontrivial (Fin 1 → ℂ)
      infer_instance
    obtain ⟨x, hx⟩ := exists_ne (0 : @Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 3)
    exact hx (hsub₀.elim x 0)

theorem V₂_indecomposable :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) Q₂ V₂ := by
  rcases @Etingof.Proposition6_6_7_source ℂ _ (Fin 4) _ Q₁ 1 source₁ V₁
      (fun w => V₁_free w) (fun w => V₁_finite w) arrowsOut₁ V₁_indecomposable with h | hz
  · exact h
  · exfalso
    have hsub₂ := hz 3
    let e₁ := @Etingof.reflFunctorMinus_equivAt_ne ℂ _ (Fin 4) _ Q₁ 1 source₁ V₁
      arrowsOut₁ 3 (by decide)
    let e₀ := @Etingof.reflFunctorMinus_equivAt_ne ℂ _ (Fin 4) _ Q₀ 0 source₀ V₀
      arrowsOut₀ 3 (by decide)
    have hsub₀ : Subsingleton
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 3) :=
      ⟨fun x y => e₀.symm.injective (e₁.symm.injective (hsub₂.elim _ _))⟩
    letI : Nontrivial (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 3) := by
      change Nontrivial (Fin 1 → ℂ)
      infer_instance
    obtain ⟨x, hx⟩ := exists_ne (0 : @Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ V₀ 3)
    exact hx (hsub₀.elim x 0)

theorem V₃_indecomposable :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) Q₃ V₃ := by
  rcases @Etingof.Proposition6_6_7_source ℂ _ (Fin 4) _ Q₂ 2 source₂ V₂
      (fun w => V₂_free w) (fun w => V₂_finite w) arrowsOut₂ V₂_indecomposable with h | hz
  · exact h
  · exfalso
    have hdim := V₃_dimensionVector 3
    letI : Subsingleton
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3) := hz 3
    have hzero : Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3) = 0 :=
      Module.finrank_zero_of_subsingleton
    unfold Etingof.QuiverRepresentation.finrankAt' at hdim
    have hone : Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3) = 1 := by
      have hdim' : (Module.finrank ℂ
          (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 3) : ℤ) = 1 := by
        simpa using hdim
      exact_mod_cast hdim'
    omega

private theorem sourceMap₃_injective : Function.Injective
    (@Etingof.QuiverRepresentation.sourceMap ℂ _ (Fin 4) Q₃ V₃ 3 arrowsOut₃) := by
  rcases @Etingof.Proposition6_6_5_source ℂ _ (Fin 4) _ Q₃ V₃ 3
      (fun w => V₃_free w) (fun w => V₃_finite w) arrowsOut₃ source₃ V₃_indecomposable with
    hsimple | hinj
  · have hzero := hsimple.2 0 (by decide)
    have hone := V₃_dimensionVector 0
    unfold Etingof.QuiverRepresentation.finrankAt' at hone
    norm_num at hone
    have hone' : Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ 0) = 1 := by
      exact_mod_cast hone
    omega
  · exact hinj

/-- The fourth actual reflection has the book's maximal-root dimension vector
`(1,1,1,2)`. -/
theorem V₄_dimensionVector (v : Fin 4) :
    ((@Etingof.QuiverRepresentation.finrankAt' ℂ _ (Fin 4) Q₄ V₄ v : ℕ) : ℤ) =
      ![1, 1, 1, 2] v := by
  have h := @Etingof.Proposition6_6_8_source ℂ _ (Fin 4) _ Q₃ 3 source₃ V₃
    (fun w => V₃_free w) (fun w => V₃_finite w) arrowsOut₃ sourceMap₃_injective v
  rw [reflectionDim_eq_cartan adj_symm adj_zero_one orient₃ 3 source₃] at h
  have hd : (fun w => (Module.finrank ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₃ V₃ w) : ℤ)) = ![1, 1, 1, 1] := by
    ext w
    exact V₃_dimensionVector w
  rw [hd] at h
  have href : Etingof.simpleReflection 4
      (Etingof.cartanMatrix 4 Etingof.D₄_adj) 3 ![1, 1, 1, 1] =
      ![1, 1, 1, 2] := by decide
  rw [href] at h
  exact h

theorem V₄_indecomposable :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) Q₄ V₄ := by
  rcases @Etingof.Proposition6_6_7_source ℂ _ (Fin 4) _ Q₃ 3 source₃ V₃
      (fun w => V₃_free w) (fun w => V₃_finite w) arrowsOut₃ V₃_indecomposable with h | hz
  · exact h
  · exfalso
    have hdim := V₄_dimensionVector 3
    letI : Subsingleton
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₄ V₄ 3) := hz 3
    have hzero : Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₄ V₄ 3) = 0 :=
      Module.finrank_zero_of_subsingleton
    unfold Etingof.QuiverRepresentation.finrankAt' at hdim
    have htwo : Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₄ V₄ 3) = 2 := by
      have hdim' : (Module.finrank ℂ
          (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₄ V₄ 3) : ℤ) = 2 := by
        simpa using hdim
      exact_mod_cast hdim'
    omega

/-- Reversing once at each of the four vertices restores the original inward orientation. -/
theorem Q₄_eq_Q₀ : Q₄ = Q₀ := by
  change Etingof.iteratedReversedAtVertices Q₀ [0, 1, 2, 3] = Q₀
  apply Etingof.iteratedReversedAtVertices_perm_eq
  decide

private theorem transport_finrank
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @Etingof.QuiverRepresentation ℂ (Fin 4) _ inst₁) (v : Fin 4) :
    Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ inst₂ (h ▸ X) v) =
      Module.finrank ℂ
        (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ inst₁ X v) := by
  cases h
  rfl

private theorem transport_free
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @Etingof.QuiverRepresentation ℂ (Fin 4) _ inst₁)
    (hfree : ∀ v, Module.Free ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ inst₁ X v)) (v : Fin 4) :
    Module.Free ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ inst₂ (h ▸ X) v) := by
  cases h
  exact hfree v

private theorem transport_finite
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @Etingof.QuiverRepresentation ℂ (Fin 4) _ inst₁)
    (hfinite : ∀ v, Module.Finite ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ inst₁ X v)) (v : Fin 4) :
    Module.Finite ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ inst₂ (h ▸ X) v) := by
  cases h
  exact hfinite v

private theorem transport_indecomposable
    {inst₁ inst₂ : Quiver (Fin 4)} (h : inst₁ = inst₂)
    (X : @Etingof.QuiverRepresentation ℂ (Fin 4) _ inst₁)
    (hind : @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) inst₁ X) :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) inst₂ (h ▸ X) := by
  cases h
  exact hind

/-- The final reflected representation, transported back to the original D₄ orientation. -/
noncomputable abbrev finalRepresentation :
    @Etingof.QuiverRepresentation ℂ (Fin 4) _ Q₀ := Q₄_eq_Q₀ ▸ V₄

noncomputable instance finalRepresentation_free (v : Fin 4) : Module.Free ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
  transport_free Q₄_eq_Q₀ V₄ (fun w => V₄_free w) v

noncomputable instance finalRepresentation_finite (v : Fin 4) : Module.Finite ℂ
    (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) :=
  transport_finite Q₄_eq_Q₀ V₄ (fun w => V₄_finite w) v

/-- The transported final representation has one-dimensional arms and a two-dimensional
central space. -/
theorem finalRepresentation_dimensionVector (v : Fin 4) :
    (Module.finrank ℂ
      (@Etingof.QuiverRepresentation.obj ℂ (Fin 4) _ Q₀ finalRepresentation v) : ℤ) =
      ![1, 1, 1, 2] v := by
  rw [transport_finrank Q₄_eq_Q₀ V₄ v]
  exact V₄_dimensionVector v

theorem finalRepresentation_indecomposable :
    @Etingof.QuiverRepresentation.IsIndecomposable ℂ _ (Fin 4) Q₀
      finalRepresentation := by
  exact transport_indecomposable Q₄_eq_Q₀ V₄ V₄_indecomposable

end Etingof.Example6_8_5
