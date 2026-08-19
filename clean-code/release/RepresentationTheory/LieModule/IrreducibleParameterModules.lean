/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations
import Mathlib.FieldTheory.Finite.Basic
import RepresentationTheory.Alignment.Attribute

namespace RepresentationTheory.LieModule.IrreducibleParameterModules

open scoped Matrix

                                                           
attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (k : Type u) [Field k]

                                                

                                                                                        
                                                               
/-- Auxiliary parameter data for a field and a natural-number characteristic index. -/
@[source_ref "Chapter2/Problem2.16.4" (role := supporting)]
inductive ModuleParameter (p : ℕ) where
  /-- A restricted parameter determined by an index below the characteristic. -/
  | restricted (n : Fin p)
  /-- A highest-weight parameter with its simplicity condition. -/
  | highest (β lam : k) (simple : β ≠ 0 ∨ lam ^ p ≠ lam)
  /-- A cyclic parameter whose first scalar is nonzero. -/
  | cyclic (α lam q : k) (alpha_ne : α ≠ 0)

                                                                      
/-- The natural-number dimension associated with a module parameter. -/
def ModuleParameter.dimension {p : ℕ} : ModuleParameter k p → ℕ
  | .restricted n => n + 1
  | .highest _ _ _ => p
  | .cyclic _ _ _ _ => p

                                                                   
/-- The vector-space type associated with a module parameter. -/
abbrev parameterModule {p : ℕ} (a : ModuleParameter k p) := Fin a.dimension → k

/-- The dimension of a parameter module equals the natural number stored in its parameter. -/
@[simp]
theorem finrank_parameterModule {p : ℕ} (a : ModuleParameter k p) :
    Module.finrank k (parameterModule k a) = a.dimension := by
  simp [parameterModule]

                                     

section Verma

variable {d : ℕ} [NeZero d]

                                                               
/-- A scalar-parameterized third endomorphism on a finite coordinate space. -/
noncomputable def standardThirdEndomorphism (lam : k) : Module.End k (Fin d → k) where
  toFun v i := (lam - 2 * (i : ℕ)) * v i
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_assoc, mul_comm c]

                                         
                           
/-- A scalar-parameterized endomorphism of a finite coordinate space with weighted backward behavior. -/
noncomputable def standardBackwardEndomorphism (lam : k) : Module.End k (Fin d → k) where
  toFun v i := ((i : ℕ) + 1) * (lam - (i : ℕ)) *
    if hi : (i : ℕ) + 1 < d then v ⟨i + 1, hi⟩ else 0
  map_add' v w := by ext i; simp only [Pi.add_apply]; split <;> ring
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

                                                                                    
                                                          
/-- A scalar-parameterized endomorphism of a finite coordinate space with cyclic forward behavior. -/
noncomputable def standardCyclicForwardEndomorphism (β : k) : Module.End k (Fin d → k) where
  toFun v i := if hi : 0 < (i : ℕ) then v ⟨i - 1, by omega⟩
    else β * v ⟨d - 1, by have := NeZero.pos d; omega⟩
  map_add' v w := by ext i; simp only [Pi.add_apply]; split <;> ring
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

omit [NeZero d] in
/-- The bracket of the standard third endomorphism with the standard backward endomorphism is twice the latter. -/
theorem bracket_standardThird_backward (lam : k) :
    ⁅standardThirdEndomorphism (d := d) k lam, standardBackwardEndomorphism (d := d) k lam⁆ =
      (2 : k) • standardBackwardEndomorphism (d := d) k lam := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, standardThirdEndomorphism, standardBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hi : (i : ℕ) + 1 < d
  · simp only [hi, dite_true]
    push_cast
    ring
  · simp only [hi, dite_false, mul_zero, sub_zero]

/-- Under the displayed scalar condition, the bracket of the standard third endomorphism with the cyclic forward endomorphism is negative twice the latter. -/
theorem bracket_standardThird_cyclicForward (lam β : k) (boundary : (d : k) * β = 0) :
    ⁅standardThirdEndomorphism (d := d) k lam, standardCyclicForwardEndomorphism (d := d) k β⁆ =
      -((2 : k) • standardCyclicForwardEndomorphism (d := d) k β) := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    standardThirdEndomorphism, standardCyclicForwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hi : 0 < (i : ℕ)
  · simp only [hi, dite_true]
    simp only [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
    push_cast
    ring
  · have hi0 : (i : ℕ) = 0 := by omega
    simp only [hi, dite_false]
    have hd : d - 1 < d := by have := NeZero.pos d; omega
    push_cast [Nat.cast_sub (show 1 ≤ d by exact NeZero.pos d)] at boundary ⊢
    simp only [hi0, Nat.cast_zero, mul_zero, sub_zero]
    linear_combination 2 * boundary * v ⟨d - 1, hd⟩

                                                                                        
                                                                                         
                                       
/-- Under the displayed scalar condition, the bracket of the standard backward and cyclic forward endomorphisms is the standard third endomorphism. -/
theorem bracket_standardBackward_cyclicForward (lam β : k) (boundary : (d : k) * (lam - (d - 1 : ℕ)) = 0) :
    ⁅standardBackwardEndomorphism (d := d) k lam, standardCyclicForwardEndomorphism (d := d) k β⁆ = standardThirdEndomorphism (d := d) k lam := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply, standardThirdEndomorphism, standardBackwardEndomorphism, standardCyclicForwardEndomorphism,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hfin : ∀ (h : (i : ℕ) < d), (⟨(i : ℕ), h⟩ : Fin d) = i :=
    fun _ => Fin.ext rfl
  by_cases htop : (i : ℕ) + 1 < d <;> by_cases hzero : 0 < (i : ℕ)
  · simp only [htop, hzero, dite_true,
      show 0 < (i : ℕ) + 1 by omega,
      show (i : ℕ) + 1 - 1 = (i : ℕ) by omega,
      show (i : ℕ) - 1 + 1 = (i : ℕ) by omega,
      i.isLt, hfin i.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
    push_cast
    ring
  · have hi0 : (i : ℕ) = 0 := by omega
    have hdpos : 0 < d := NeZero.pos d
    have hdlast : d - 1 + 1 = d := by omega
    have hnlast : ¬d - 1 + 1 < d := by omega
    simp only [htop, hzero, dite_true, dite_false,
      show 0 < (i : ℕ) + 1 by omega,
      show (i : ℕ) + 1 - 1 = (i : ℕ) by omega,
      hfin i.isLt, hnlast]
    simp [hi0]
  · have hitop : (i : ℕ) + 1 = d := by omega
    simp only [htop, hzero, dite_false, dite_true, mul_zero, zero_sub,
      show (i : ℕ) - 1 + 1 = (i : ℕ) by omega, i.isLt, hfin i.isLt]
    simp only [Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
    have hb := boundary
    push_cast [Nat.cast_sub (show 1 ≤ d by exact NeZero.pos d)] at hb ⊢
    rw [← hitop] at hb
    push_cast at hb
    have hb' : ((i : ℕ) : k) * lam + lam - (((i : ℕ) : k) ^ 2 + (i : ℕ)) = 0 := by
      linear_combination hb
    have hbv := congrArg (fun x : k => x * v i) hb'
    simp only [zero_mul] at hbv
    ring_nf at hbv ⊢
    linear_combination -hbv
  · have hi0 : (i : ℕ) = 0 := by omega
    have hd1 : d = 1 := by omega
    subst d
    fin_cases i
    simp only [Nat.cast_zero, Nat.cast_one, zero_add, sub_zero, one_mul, lt_self_iff_false,
      dite_false, mul_zero, tsub_self, sub_self, Fin.zero_eta, zero_eq_mul] at boundary ⊢
    exact Or.inl boundary

end Verma

section Cyclic

variable {p : ℕ} [NeZero p] [CharP k p]

                                                     
/-- A scalar-parameterized third endomorphism on the finite coordinate space. -/
noncomputable def parameterThirdEndomorphism (lam : k) : Module.End k (Fin p → k) where
  toFun v i := (lam + 2 * (i : ℕ)) * v i
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_assoc, mul_comm c]

                                               
/-- A parameterized endomorphism of the coordinate space with cyclic forward behavior. -/
noncomputable def cyclicForwardEndomorphism (α : k) : Module.End k (Fin p → k) where
  toFun v i := if hi : 0 < (i : ℕ) then v ⟨i - 1, by omega⟩
    else α * v ⟨p - 1, by have := NeZero.pos p; omega⟩
  map_add' v w := by ext i; simp only [Pi.add_apply]; split <;> ring
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

                                                                           
/-- A field-valued coefficient depending on three scalars and a natural-number index. -/
noncomputable def recurrenceCoefficient (α lam q : k) (i : ℕ) : k :=
  α * q - (i : k) * lam - (i : k) * ((i : k) - 1)

                                                                                    
                                                                        
/-- A three-scalar endomorphism of the coordinate space with weighted backward behavior. -/
noncomputable def weightedBackwardEndomorphism (α lam q : k) : Module.End k (Fin p → k) where
  toFun v i := if hi : (i : ℕ) + 1 < p then
      recurrenceCoefficient k α lam q (i + 1) * v ⟨i + 1, hi⟩
    else q * v ⟨0, NeZero.pos p⟩
  map_add' v w := by ext i; simp only [Pi.add_apply]; split <;> ring
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> ring

/-- The bracket of the third parameter endomorphism with the cyclic forward endomorphism is twice the latter. -/
theorem bracket_parameterThird_cyclicForward (α lam : k) :
    ⁅parameterThirdEndomorphism (p := p) k lam, cyclicForwardEndomorphism (p := p) k α⁆ =
      (2 : k) • cyclicForwardEndomorphism (p := p) k α := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, parameterThirdEndomorphism, cyclicForwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hi : 0 < (i : ℕ)
  · simp only [hi, dite_true, Nat.cast_sub (show 1 ≤ (i : ℕ) by omega)]
    push_cast
    ring
  · have hi0 : (i : ℕ) = 0 := by omega
    simp only [hi, dite_false]
    push_cast [Nat.cast_sub (show 1 ≤ p by exact NeZero.pos p)]
    have hp0 : (p : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
    rw [hp0]
    simp only [hi0, Nat.cast_zero, mul_zero]
    ring

/-- The bracket of the third parameter endomorphism with the weighted backward endomorphism is negative twice the latter. -/
theorem bracket_parameterThird_weightedBackward (α lam q : k) :
    ⁅parameterThirdEndomorphism (p := p) k lam, weightedBackwardEndomorphism (p := p) k α lam q⁆ =
      -((2 : k) • weightedBackwardEndomorphism (p := p) k α lam q) := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    parameterThirdEndomorphism, weightedBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hi : (i : ℕ) + 1 < p
  · simp only [hi, dite_true]
    push_cast
    ring
  · have hitop : (i : ℕ) + 1 = p := by omega
    simp only [hi, dite_false]
    have hp0 : (p : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
    rw [← hitop] at hp0
    push_cast at hp0
    linear_combination 2 * hp0 * q * v ⟨0, NeZero.pos p⟩

/-- Under the characteristic and size hypotheses, the bracket of the cyclic forward and weighted backward endomorphisms is the third endomorphism. -/
theorem bracket_cyclicForward_weightedBackward (α lam q : k) (hp : 2 < p) :
    ⁅cyclicForwardEndomorphism (p := p) k α, weightedBackwardEndomorphism (p := p) k α lam q⁆ =
      parameterThirdEndomorphism (p := p) k lam := by
  apply LinearMap.ext
  intro v
  funext i
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, Pi.sub_apply, parameterThirdEndomorphism, cyclicForwardEndomorphism, weightedBackwardEndomorphism,
    recurrenceCoefficient, LinearMap.coe_mk, AddHom.coe_mk]
  have hfin : ∀ (h : (i : ℕ) < p), (⟨(i : ℕ), h⟩ : Fin p) = i :=
    fun _ => Fin.ext rfl
  by_cases htop : (i : ℕ) + 1 < p <;> by_cases hzero : 0 < (i : ℕ)
  · simp only [htop, hzero, dite_true,
      show 0 < (i : ℕ) + 1 by omega,
      show (i : ℕ) + 1 - 1 = (i : ℕ) by omega,
      show (i : ℕ) - 1 + 1 = (i : ℕ) by omega,
      i.isLt, hfin i.isLt]
    push_cast
    ring
  · have hi0 : (i : ℕ) = 0 := by omega
    have hnlast : ¬p - 1 + 1 < p := by omega
    have hieq : i = ⟨0, by omega⟩ := Fin.ext hi0
    simp only [htop, hzero, dite_true, dite_false,
      show 0 < (i : ℕ) + 1 by omega,
      show (i : ℕ) + 1 - 1 = (i : ℕ) by omega,
      hfin i.isLt, hnlast]
    rw [hieq]
    ring
  · have hitop : (i : ℕ) + 1 = p := by omega
    simp only [htop, hzero, dite_false, dite_true,
      show (i : ℕ) - 1 + 1 = (i : ℕ) by omega,
      i.isLt, hfin i.isLt]
    have hp0 : (p : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
    rw [← hitop] at hp0
    push_cast at hp0
    have hival : (i : ℕ) = p - 1 := by omega
    have hilast : (⟨p - 1, by omega⟩ : Fin p) = i := Fin.ext hival.symm
    simp only [show ¬0 < (0 : ℕ) by omega, dite_false, hilast]
    linear_combination (-lam - (i : ℕ)) * hp0 * v i
  · exfalso
    omega

end Cyclic

                                                    

                                                                   
/-- Data of three linear endomorphisms used to define a representation of the designated Lie algebra. -/
structure LieEndomorphismTriple (V : Type*) [AddCommGroup V] [Module k V] where
  /-- The first endomorphism in a Lie-endomorphism triple. -/
  first : Module.End k V
  /-- The second endomorphism in a Lie-endomorphism triple. -/
  second : Module.End k V
  /-- The third endomorphism in a Lie-endomorphism triple. -/
  third : Module.End k V
  /-- The bracket of the third endomorphism with the first is twice the first. -/
  bracket_third_first : ⁅third, first⁆ = (2 : k) • first
  /-- The bracket of the third endomorphism with the second is negative twice the second. -/
  bracket_third_second : ⁅third, second⁆ = -((2 : k) • second)
  /-- The bracket of the first and second endomorphisms is the third. -/
  bracket_first_second : ⁅first, second⁆ = third

private theorem sl2ValAdd (X Y : RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (i j : Fin 2) :
    (X + Y).val i j = X.val i j + Y.val i j := rfl

private theorem sl2ValSMul (c : k) (X : RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (i j : Fin 2) :
    (c • X).val i j = c * X.val i j := rfl

                                                                         
/-- The Lie homomorphism from the designated Lie algebra to endomorphisms defined by a Lie-endomorphism triple. -/
noncomputable def LieEndomorphismTriple.toLieHom {V : Type*} [AddCommGroup V] [Module k V]
    (T : LieEndomorphismTriple k V) : RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k →ₗ⁅k⁆ Module.End k V where
  toFun X := X.val 0 0 • T.third + X.val 0 1 • T.first + X.val 1 0 • T.second
  map_add' X Y := by
    simp only [sl2ValAdd, add_smul]
    abel
  map_smul' c X := by
    simp only [sl2ValSMul, mul_smul, RingHom.id_apply, smul_add]
  map_lie' {X Y} := by
    have htX : X.val 1 1 = -X.val 0 0 := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.entry_one_one_eq_neg_entry_zero_zero k X
    have htY : Y.val 1 1 = -Y.val 0 0 := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.entry_one_one_eq_neg_entry_zero_zero k Y
    have hEH : ⁅T.first, T.third⁆ = -((2 : k) • T.first) := by
      rw [← lie_skew, T.bracket_third_first]
    have hFH : ⁅T.second, T.third⁆ = (2 : k) • T.second := by
      rw [← lie_skew, T.bracket_third_second, neg_neg]
    have hFE : ⁅T.second, T.first⁆ = -T.third := by
      rw [← lie_skew, T.bracket_first_second]
    have hbr00 : ⁅X, Y⁆.val 0 0 =
        X.val 0 1 * Y.val 1 0 - Y.val 0 1 * X.val 1 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hbr01 : ⁅X, Y⁆.val 0 1 =
        2 * X.val 0 0 * Y.val 0 1 - 2 * Y.val 0 0 * X.val 0 1 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]
      ring
    have hbr10 : ⁅X, Y⁆.val 1 0 =
        2 * X.val 1 0 * Y.val 0 0 - 2 * Y.val 1 0 * X.val 0 0 := by
      simp [show ⁅X, Y⁆.val = X.val * Y.val - Y.val * X.val from rfl,
        Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, htX, htY]
      ring
    have smul_lie' : ∀ (c : k) (a b : Module.End k V),
        ⁅c • a, b⁆ = c • ⁅a, b⁆ := fun c a b => smul_lie c a b
    have lie_smul' : ∀ (c : k) (a b : Module.End k V),
        ⁅a, c • b⁆ = c • ⁅a, b⁆ := fun c a b => lie_smul c a b
    simp only [add_lie, lie_add, smul_lie', lie_smul', lie_self, smul_zero,
      add_zero, zero_add, T.bracket_third_first, T.bracket_third_second, T.bracket_first_second,
      hEH, hFH, hFE, smul_neg, smul_smul, hbr00, hbr01, hbr10]
    module

/-- The Lie homomorphism sends the first designated Lie-algebra element to the first endomorphism. -/
@[simp]
theorem LieEndomorphismTriple.toLieHom_firstElement {V : Type*} [AddCommGroup V] [Module k V] (T : LieEndomorphismTriple k V) :
    LieEndomorphismTriple.toLieHom k T (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) = T.first := by
  apply LinearMap.ext
  intro v
  simp [LieEndomorphismTriple.toLieHom, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement,
    LieAlgebra.SpecialLinear.val_single, Matrix.single]

/-- The Lie homomorphism sends the second designated Lie-algebra element to the second endomorphism. -/
@[simp]
theorem LieEndomorphismTriple.toLieHom_secondElement {V : Type*} [AddCommGroup V] [Module k V] (T : LieEndomorphismTriple k V) :
    LieEndomorphismTriple.toLieHom k T (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) = T.second := by
  apply LinearMap.ext
  intro v
  simp [LieEndomorphismTriple.toLieHom, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement,
    LieAlgebra.SpecialLinear.val_single, Matrix.single]

/-- The Lie homomorphism sends the third designated Lie-algebra element to the third endomorphism. -/
@[simp]
theorem LieEndomorphismTriple.toLieHom_thirdElement {V : Type*} [AddCommGroup V] [Module k V] (T : LieEndomorphismTriple k V) :
    LieEndomorphismTriple.toLieHom k T (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) = T.third := by
  apply LinearMap.ext
  intro v
  simp [LieEndomorphismTriple.toLieHom, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement,
    LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.single]

                                   

section Family

variable {p : ℕ} [Fact p.Prime] [CharP k p] [Fact (2 < p)]

                                                                             
/-- The Lie-endomorphism triple associated with a module parameter. -/
noncomputable def parameterLieEndomorphismTriple (a : ModuleParameter k p) :
    LieEndomorphismTriple k (parameterModule k a) := by
  have hp : 2 < p := Fact.out
  cases a with
  | restricted n =>
      let d := (n : ℕ) + 1
      haveI : NeZero d := ⟨by omega⟩
      let lam : k := (n : ℕ)
      exact
        { first := standardBackwardEndomorphism (d := d) k lam
          second := standardCyclicForwardEndomorphism (d := d) k 0
          third := standardThirdEndomorphism (d := d) k lam
          bracket_third_first := bracket_standardThird_backward (d := d) k lam
          bracket_third_second := bracket_standardThird_cyclicForward (d := d) k lam 0 (by simp)
          bracket_first_second := bracket_standardBackward_cyclicForward (d := d) k lam 0 (by
            dsimp [d, lam]
            push_cast
            ring) }
  | highest β lam hsimple =>
      haveI : NeZero p := ⟨by omega⟩
      have hp0 : (p : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
      exact
        { first := standardBackwardEndomorphism (d := p) k lam
          second := standardCyclicForwardEndomorphism (d := p) k β
          third := standardThirdEndomorphism (d := p) k lam
          bracket_third_first := bracket_standardThird_backward (d := p) k lam
          bracket_third_second := bracket_standardThird_cyclicForward (d := p) k lam β (by rw [hp0, zero_mul])
          bracket_first_second := bracket_standardBackward_cyclicForward (d := p) k lam β (by rw [hp0, zero_mul]) }
  | cyclic α lam q halpha =>
      haveI : NeZero p := ⟨by omega⟩
      exact
        { first := cyclicForwardEndomorphism (p := p) k α
          second := weightedBackwardEndomorphism (p := p) k α lam q
          third := parameterThirdEndomorphism (p := p) k lam
          bracket_third_first := bracket_parameterThird_cyclicForward (p := p) k α lam
          bracket_third_second := bracket_parameterThird_weightedBackward (p := p) k α lam q
          bracket_first_second := bracket_cyclicForward_weightedBackward (p := p) k α lam q hp }

                                                  
/-- The Lie homomorphism defining the action on a parameter module. -/
@[source_ref "Chapter2/Problem2.16.4" (role := supporting)]
noncomputable def parameterModuleLieHom (a : ModuleParameter k p) :
    RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k →ₗ⁅k⁆ Module.End k (parameterModule k a) :=
  LieEndomorphismTriple.toLieHom k (parameterLieEndomorphismTriple k a)

omit [Fact p.Prime] in
/-- The parameter-module Lie homomorphism sends the first designated Lie-algebra element to the first endomorphism of its associated triple. -/
@[simp]
theorem parameterModuleLieHom_firstElement (a : ModuleParameter k p) :
    parameterModuleLieHom k a (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) = (parameterLieEndomorphismTriple k a).first :=
  LieEndomorphismTriple.toLieHom_firstElement k (parameterLieEndomorphismTriple k a)

omit [Fact p.Prime] in
/-- The parameter-module Lie homomorphism sends the second designated Lie-algebra element to the second endomorphism of its associated triple. -/
@[simp]
theorem parameterModuleLieHom_secondElement (a : ModuleParameter k p) :
    parameterModuleLieHom k a (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) = (parameterLieEndomorphismTriple k a).second :=
  LieEndomorphismTriple.toLieHom_secondElement k (parameterLieEndomorphismTriple k a)

omit [Fact p.Prime] in
/-- The parameter-module Lie homomorphism sends the third designated Lie-algebra element to the third endomorphism of its associated triple. -/
@[simp]
theorem parameterModuleLieHom_thirdElement (a : ModuleParameter k p) :
    parameterModuleLieHom k a (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) = (parameterLieEndomorphismTriple k a).third :=
  LieEndomorphismTriple.toLieHom_thirdElement k (parameterLieEndomorphismTriple k a)

                                                        
/-- The parameter module carries the Lie-ring module structure. -/
noncomputable instance lieRingModule_parameterModule (a : ModuleParameter k p) :
    LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) :=
  LieRingModule.compLieHom (parameterModule k a) (parameterModuleLieHom k a)

                                                              
/-- The parameter module carries the compatible Lie-module structure. -/
noncomputable instance lieModule_parameterModule (a : ModuleParameter k p) :
    @LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) _ _ _ _ _
      (lieRingModule_parameterModule k a) :=
  LieModule.compLieHom (parameterModule k a) (parameterModuleLieHom k a)

                                                                                           
                                                                                             
/-- An auxiliary witness type associated with two module parameters. -/
abbrev parameterEquivWitness (a b : ModuleParameter k p) :=
  @LieModuleEquiv k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) (parameterModule k b)
    _ _ _ _ _ _ (lieRingModule_parameterModule k a) (lieRingModule_parameterModule k b)

end Family

                                               

section Irreducibility

variable {p : ℕ} [Fact p.Prime] [CharP k p] [Fact (2 < p)]

                                  
/-- The coordinate vector indexed by a finite index. -/
def coordinateVector (d : ℕ) (i : Fin d) : Fin d → k := Pi.single i 1

/-- A coordinate vector is one at its selected index and zero at every other index. -/
@[simp]
theorem coordinateVector_apply (d : ℕ) (i j : Fin d) :
    coordinateVector k d i j = if j = i then 1 else 0 := by
  simp [coordinateVector, Pi.single_apply]

private theorem basis_ne_zero {d : ℕ} [NeZero d] (i : Fin d) : coordinateVector k d i ≠ 0 := by
  intro h
  have hi := congrFun h i
  rw [coordinateVector_apply, if_pos rfl, Pi.zero_apply] at hi
  exact one_ne_zero hi

private theorem vermaH_basis {d : ℕ} [NeZero d] (lam : k) (i : Fin d) :
    standardThirdEndomorphism (d := d) k lam (coordinateVector k d i) =
      (lam - 2 * (i : ℕ)) • coordinateVector k d i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [standardThirdEndomorphism, coordinateVector_apply, mul_comm]
  · simp [standardThirdEndomorphism, coordinateVector_apply, hji]

omit [Fact p.Prime] [CharP k p] [Fact (2 < p)] in
private theorem cyclicH_basis (lam : k) (i : Fin p) :
    parameterThirdEndomorphism (p := p) k lam (coordinateVector k p i) =
      (lam + 2 * (i : ℕ)) • coordinateVector k p i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [parameterThirdEndomorphism, coordinateVector_apply, mul_comm]
  · simp [parameterThirdEndomorphism, coordinateVector_apply, hji]

omit [Fact p.Prime] [Fact (2 < p)] in
private theorem natCastInjLt {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : k) = (b : k)) : a = b := by
  rcases le_total a b with hab | hab
  · have hz : ((b - a : ℕ) : k) = 0 := by rw [Nat.cast_sub hab, h, sub_self]
    rw [CharP.cast_eq_zero_iff k p] at hz
    have := Nat.eq_zero_of_dvd_of_lt hz (by omega)
    omega
  · have hz : ((a - b : ℕ) : k) = 0 := by rw [Nat.cast_sub hab, h, sub_self]
    rw [CharP.cast_eq_zero_iff k p] at hz
    have := Nat.eq_zero_of_dvd_of_lt hz (by omega)
    omega

omit [Fact p.Prime] [Fact (2 < p)] in
private theorem natCastNeZeroLt {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    (n : k) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff k p]
  intro hdvd
  have := Nat.eq_zero_of_dvd_of_lt hdvd hn
  omega

omit [Fact p.Prime] [Fact (2 < p)] in
private theorem twoNeZero (hp : 2 < p) : (2 : k) ≠ 0 := by
  exact natCastNeZeroLt k (p := p) (by norm_num) hp

omit [Fact p.Prime] in
private theorem subWeightsPairwise {d : ℕ} (hd : d ≤ p) (lam : k) :
    Pairwise fun i j : Fin d => lam - 2 * (i : ℕ) ≠ lam - 2 * (j : ℕ) := by
  intro i j hij heq
  have hmul : (2 : k) * ((i : ℕ) - (j : ℕ)) = 0 := by
    linear_combination -heq
  have hsub : ((i : ℕ) : k) - (j : ℕ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (twoNeZero k Fact.out)
  apply hij
  apply Fin.ext
  exact natCastInjLt k (p := p) (i.isLt.trans_le hd) (j.isLt.trans_le hd)
    (sub_eq_zero.mp hsub)

omit [Fact p.Prime] in
private theorem addWeightsPairwise (lam : k) :
    Pairwise fun i j : Fin p => lam + 2 * (i : ℕ) ≠ lam + 2 * (j : ℕ) := by
  intro i j hij heq
  have hmul : (2 : k) * ((i : ℕ) - (j : ℕ)) = 0 := by
    linear_combination heq
  have hsub : ((i : ℕ) : k) - (j : ℕ) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (twoNeZero k Fact.out)
  apply hij
  apply Fin.ext
  exact natCastInjLt k (p := p) i.isLt j.isLt (sub_eq_zero.mp hsub)

                                                                                       
                                                                                       
                                                
private theorem exists_basis_mem_of_diagonal {d : ℕ} (weight : Fin d → k)
    (hweight : Pairwise fun i j => weight i ≠ weight j)
    (N : Submodule k (Fin d → k)) (H : Module.End k (Fin d → k))
    (hdiag : ∀ (v : Fin d → k) i, H v i = weight i * v i)
    (hstable : ∀ v ∈ N, H v ∈ N) (hne : N ≠ ⊥) :
    ∃ i, coordinateVector k d i ∈ N := by
  classical
  rw [ne_eq, Submodule.eq_bot_iff] at hne
  push Not at hne
  obtain ⟨w, hwN, hw0⟩ := hne
  have smul_extract : ∀ (c : k) (v : Fin d → k), c ≠ 0 → c • v ∈ N → v ∈ N := by
    intro c v hc hcv
    have h := N.smul_mem c⁻¹ hcv
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  suffices ∀ (n : ℕ) (v : Fin d → k), v ∈ N → v ≠ 0 →
      (Finset.univ.filter fun i => v i ≠ 0).card ≤ n →
      ∃ i, coordinateVector k d i ∈ N by
    exact this _ w hwN hw0 le_rfl
  intro n
  induction n with
  | zero =>
      intro v _ hv0 hn
      exfalso
      apply hv0
      ext i
      by_contra hi
      have himem : i ∈ Finset.univ.filter fun j => v j ≠ 0 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      exact absurd (Finset.card_pos.mpr ⟨i, himem⟩) (by omega)
  | succ n ih =>
      intro v hvN hv0 hn
      by_cases hone : (Finset.univ.filter fun i => v i ≠ 0).card ≤ 1
      · have hcard := Finset.card_le_one.mp hone
        have hsupport : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          apply hv0
          ext i
          by_contra hi
          have : i ∈ (∅ : Finset (Fin d)) :=
            hempty ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
          simp at this
        obtain ⟨i, hi⟩ := hsupport
        have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
        refine ⟨i, ?_⟩
        have hv : v = v i • coordinateVector k d i := by
          ext j
          simp only [Pi.smul_apply, coordinateVector_apply, smul_eq_mul]
          by_cases hji : j = i
          · subst j
            simp
          · have hvj : v j = 0 := by
              by_contra hj
              exact hji (hcard j
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) i hi)
            simp [hji, hvj]
        rw [hv] at hvN
        exact smul_extract _ _ hvi hvN
      · push Not at hone
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hone
        have hvi : v i ≠ 0 := (Finset.mem_filter.mp hi).2
        have hvj : v j ≠ 0 := (Finset.mem_filter.mp hj).2
        let c := weight i
        let v' : Fin d → k := H v - c • v
        have hv'N : v' ∈ N := N.sub_mem (hstable v hvN) (N.smul_mem c hvN)
        have hv'val : ∀ l, v' l = (weight l - weight i) * v l := by
          intro l
          simp only [v', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, c, hdiag]
          ring
        have hv'0 : v' ≠ 0 := by
          intro hz
          have hzj := congr_fun hz j
          rw [hv'val] at hzj
          simp only [Pi.zero_apply] at hzj
          rcases mul_eq_zero.mp hzj with hwt | hv
          · exact hweight hij.symm (sub_eq_zero.mp hwt)
          · exact hvj hv
        have hfewer : (Finset.univ.filter fun l => v' l ≠ 0).card ≤ n := by
          have hssub : (Finset.univ.filter fun l => v' l ≠ 0) ⊂
              (Finset.univ.filter fun l => v l ≠ 0) := by
            constructor
            · intro l hl
              rw [Finset.mem_filter] at hl ⊢
              refine ⟨Finset.mem_univ l, ?_⟩
              rw [hv'val] at hl
              exact (mul_ne_zero_iff.mp hl.2).2
            · intro hsub
              have hii := hsub hi
              rw [Finset.mem_filter] at hii
              apply hii.2
              rw [hv'val]
              simp
          linarith [Finset.card_lt_card hssub]
        exact ih v' hv'N hv'0 hfewer

/-- Away from the last index, the standard cyclic forward endomorphism sends each coordinate vector to its successor. -/
theorem standardCyclicForwardEndomorphism_apply_lt_last {d : ℕ} [NeZero d] (β : k) (i : ℕ) (hi : i + 1 < d) :
    standardCyclicForwardEndomorphism (d := d) k β (coordinateVector k d ⟨i, by omega⟩) =
      coordinateVector k d ⟨i + 1, hi⟩ := by
  classical
  ext j
  simp only [standardCyclicForwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply]
  by_cases hj : 0 < (j : ℕ)
  · simp only [hj, dite_true]
    simp only [Fin.ext_iff]
    by_cases hji : (j : ℕ) = i + 1
    · simp [hji]
    · have hpred : (j : ℕ) - 1 ≠ i := by omega
      simp [hji, hpred]
  · have hj0 : (j : ℕ) = 0 := by omega
    have hlast : d - 1 ≠ i := by omega
    simp [Fin.ext_iff, hj0, hlast]

/-- The standard cyclic forward endomorphism sends the last coordinate vector to the first scaled by its parameter. -/
theorem standardCyclicForwardEndomorphism_apply_last {d : ℕ} [NeZero d] (β : k) :
    standardCyclicForwardEndomorphism (d := d) k β (coordinateVector k d ⟨d - 1, by have := NeZero.pos d; omega⟩) =
      β • coordinateVector k d ⟨0, NeZero.pos d⟩ := by
  classical
  ext j
  simp only [standardCyclicForwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hj : 0 < (j : ℕ)
  · simp only [hj, dite_true]
    have hjne : (j : ℕ) - 1 ≠ d - 1 := by omega
    have hj0 : (j : ℕ) ≠ 0 := by omega
    simp [Fin.ext_iff, hjne, hj0]
  · have hj0 : (j : ℕ) = 0 := by omega
    simp [Fin.ext_iff, hj0]

/-- At a positive index, the standard backward endomorphism moves to the predecessor with coefficient given by the index and scalar parameter. -/
theorem standardBackwardEndomorphism_apply_pos {d : ℕ} [NeZero d] (lam : k) (i : ℕ)
    (hi0 : 0 < i) (hid : i < d) :
    standardBackwardEndomorphism (d := d) k lam (coordinateVector k d ⟨i, hid⟩) =
      ((i : k) * (lam - (i : k) + 1)) • coordinateVector k d ⟨i - 1, by omega⟩ := by
  classical
  ext j
  simp only [standardBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) + 1 < d
  · simp only [hj, dite_true]
    simp only [Fin.ext_iff]
    by_cases hji : (j : ℕ) + 1 = i
    · have hjpred : (j : ℕ) = i - 1 := by omega
      have hisub : i - 1 + 1 = i := by omega
      simp only [hjpred]
      split
      · rw [Nat.cast_sub (by omega : 1 ≤ i)]
        push_cast
        ring
      · omega
    · have hjpred : (j : ℕ) ≠ i - 1 := by omega
      simp [hji, hjpred]
  · have hjpred : (j : ℕ) ≠ i - 1 := by omega
    simp [hj, Fin.ext_iff, hjpred]

omit [CharP k p] [Fact (2 < p)] in
/-- Away from the last index, the cyclic forward endomorphism sends a coordinate vector to its successor. -/
theorem cyclicForwardEndomorphism_apply_lt_last (α : k) (i : ℕ) (hi : i + 1 < p) :
    cyclicForwardEndomorphism (p := p) k α (coordinateVector k p ⟨i, by omega⟩) =
      coordinateVector k p ⟨i + 1, hi⟩ := by
  classical
  ext j
  simp only [cyclicForwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply]
  by_cases hj : 0 < (j : ℕ)
  · simp only [hj, dite_true]
    simp only [Fin.ext_iff]
    by_cases hji : (j : ℕ) = i + 1
    · simp [hji]
    · have hpred : (j : ℕ) - 1 ≠ i := by omega
      simp [hji, hpred]
  · have hj0 : (j : ℕ) = 0 := by omega
    have hlast : p - 1 ≠ i := by omega
    simp [Fin.ext_iff, hj0, hlast]

omit [CharP k p] [Fact (2 < p)] in
/-- The cyclic forward endomorphism sends the last coordinate vector to the first scaled by its parameter. -/
theorem cyclicForwardEndomorphism_apply_last (α : k) (hp : 2 < p) :
    cyclicForwardEndomorphism (p := p) k α (coordinateVector k p ⟨p - 1, by omega⟩) =
      α • coordinateVector k p ⟨0, by omega⟩ := by
  classical
  ext j
  simp only [cyclicForwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hj : 0 < (j : ℕ)
  · simp only [hj, dite_true]
    have hjne : (j : ℕ) - 1 ≠ p - 1 := by omega
    have hj0 : (j : ℕ) ≠ 0 := by omega
    simp [Fin.ext_iff, hjne, hj0]
  · have hj0 : (j : ℕ) = 0 := by omega
    simp [Fin.ext_iff, hj0]

omit [CharP k p] [Fact (2 < p)] in
/-- At a positive index, the weighted backward endomorphism moves to the predecessor with the displayed recurrence coefficient. -/
theorem weightedBackwardEndomorphism_apply_pos (α lam q : k) (i : ℕ) (hi0 : 0 < i) (hip : i < p) :
    weightedBackwardEndomorphism (p := p) k α lam q (coordinateVector k p ⟨i, hip⟩) =
      recurrenceCoefficient k α lam q i • coordinateVector k p ⟨i - 1, by omega⟩ := by
  classical
  ext j
  simp only [weightedBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) + 1 < p
  · simp only [hj, dite_true]
    by_cases hji : (j : ℕ) + 1 = i
    · have hjpred : (j : ℕ) = i - 1 := by omega
      simp only [Fin.ext_iff, hjpred]
      rw [show i - 1 + 1 = i by omega]
      simp
    · have hjpred : (j : ℕ) ≠ i - 1 := by omega
      simp [Fin.ext_iff, hji, hjpred]
  · have hjpred : (j : ℕ) ≠ i - 1 := by omega
    simp only [hj, dite_false, Fin.ext_iff]
    rw [if_neg (by omega : (0 : ℕ) ≠ i), if_neg hjpred]
    ring

omit [CharP k p] [Fact (2 < p)] in
/-- At index zero, the weighted backward endomorphism sends the coordinate vector to the last one scaled by the third parameter. -/
theorem weightedBackwardEndomorphism_apply_zero (α lam q : k) :
    weightedBackwardEndomorphism (p := p) k α lam q (coordinateVector k p ⟨0, NeZero.pos p⟩) =
      q • coordinateVector k p ⟨p - 1, by have := NeZero.pos p; omega⟩ := by
  classical
  ext j
  simp only [weightedBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) + 1 < p
  · simp only [hj, dite_true]
    have hjlast : (j : ℕ) ≠ p - 1 := by omega
    simp only [Fin.ext_iff]
    rw [if_neg (by omega : (j : ℕ) + 1 ≠ 0), if_neg hjlast]
    ring
  · have hjlast : (j : ℕ) = p - 1 := by omega
    simp only [hj, dite_false, Fin.ext_iff]
    simp only [if_true, if_pos hjlast]

private theorem smulExtract {d : ℕ} (N : Submodule k (Fin d → k))
    (c : k) (v : Fin d → k) (hc : c ≠ 0) (hcv : c • v ∈ N) : v ∈ N := by
  have h := N.smul_mem c⁻¹ hcv
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h

private theorem allBasisOfVermaF {d : ℕ} [NeZero d] (β : k)
    (N : Submodule k (Fin d → k))
    (hF : ∀ v ∈ N, standardCyclicForwardEndomorphism (d := d) k β v ∈ N)
    (h0 : coordinateVector k d ⟨0, NeZero.pos d⟩ ∈ N) :
    ∀ i, coordinateVector k d i ∈ N := by
  intro i
  suffices ∀ (j : ℕ) (hj : j < d), coordinateVector k d ⟨j, hj⟩ ∈ N from this i i.isLt
  intro j hj
  induction j with
  | zero => exact h0
  | succ j ih =>
      have hprev := ih (by omega)
      have himage := hF _ hprev
      rwa [standardCyclicForwardEndomorphism_apply_lt_last k β j hj] at himage

private theorem zeroBasisOfVermaE {d : ℕ} [NeZero d] (lam : k)
    (N : Submodule k (Fin d → k))
    (hE : ∀ v ∈ N, standardBackwardEndomorphism (d := d) k lam v ∈ N)
    (hcoeff : ∀ i : ℕ, 0 < i → i < d → (i : k) * (lam - (i : k) + 1) ≠ 0)
    {i : Fin d} (hi : coordinateVector k d i ∈ N) :
    coordinateVector k d ⟨0, NeZero.pos d⟩ ∈ N := by
  suffices ∀ (j : ℕ) (hj : j < d), coordinateVector k d ⟨j, hj⟩ ∈ N →
      coordinateVector k d ⟨0, NeZero.pos d⟩ ∈ N from this i i.isLt hi
  intro j hj
  induction j with
  | zero => exact id
  | succ j ih =>
      intro hmem
      have himage := hE _ hmem
      rw [standardBackwardEndomorphism_apply_pos k lam (j + 1) (by omega) hj] at himage
      exact ih (by omega) (smulExtract k N _ _ (hcoeff (j + 1) (by omega) hj) himage)

private theorem zeroBasisOfCyclicVermaF {d : ℕ} [NeZero d] (β : k) (hβ : β ≠ 0)
    (N : Submodule k (Fin d → k))
    (hF : ∀ v ∈ N, standardCyclicForwardEndomorphism (d := d) k β v ∈ N)
    {i : Fin d} (hi : coordinateVector k d i ∈ N) :
    coordinateVector k d ⟨0, NeZero.pos d⟩ ∈ N := by
  have reach : ∀ (r : ℕ) (hr : (i : ℕ) + r < d),
      coordinateVector k d ⟨(i : ℕ) + r, hr⟩ ∈ N := by
    intro r hr
    induction r with
    | zero => simpa using hi
    | succ r ih =>
        have hprev := ih (by omega)
        have himage := hF _ hprev
        rw [standardCyclicForwardEndomorphism_apply_lt_last k β ((i : ℕ) + r) (by omega)] at himage
        simpa [Nat.add_assoc] using himage
  have hlast : coordinateVector k d ⟨d - 1, Nat.sub_lt (NeZero.pos d) (by omega)⟩ ∈ N := by
    have h := reach (d - 1 - (i : ℕ)) (by omega)
    have heq : (⟨d - 1, Nat.sub_lt (NeZero.pos d) (by omega)⟩ : Fin d) =
        ⟨(i : ℕ) + (d - 1 - (i : ℕ)), by omega⟩ := by
      apply Fin.ext
      change d - 1 = (i : ℕ) + (d - 1 - (i : ℕ))
      omega
    simpa [heq] using h
  have himage := hF _ hlast
  rw [standardCyclicForwardEndomorphism_apply_last k β] at himage
  exact smulExtract k N _ _ hβ himage

omit [CharP k p] in
private theorem zeroBasisOfCyclicE (α : k) (hα : α ≠ 0)
    (N : Submodule k (Fin p → k))
    (hE : ∀ v ∈ N, cyclicForwardEndomorphism (p := p) k α v ∈ N)
    {i : Fin p} (hi : coordinateVector k p i ∈ N) :
    coordinateVector k p ⟨0, Nat.zero_lt_of_lt (Fact.out : 2 < p)⟩ ∈ N := by
  have hp : 2 < p := Fact.out
  have reach : ∀ (r : ℕ) (hr : (i : ℕ) + r < p),
      coordinateVector k p ⟨(i : ℕ) + r, hr⟩ ∈ N := by
    intro r hr
    induction r with
    | zero => simpa using hi
    | succ r ih =>
        have hprev := ih (by omega)
        have himage := hE _ hprev
        rw [cyclicForwardEndomorphism_apply_lt_last k α ((i : ℕ) + r) (by omega)] at himage
        simpa [Nat.add_assoc] using himage
  have hlast : coordinateVector k p ⟨p - 1, by omega⟩ ∈ N := by
    have h := reach (p - 1 - (i : ℕ)) (by omega)
    have heq : (⟨p - 1, by omega⟩ : Fin p) =
        ⟨(i : ℕ) + (p - 1 - (i : ℕ)), by omega⟩ := by
      apply Fin.ext
      change p - 1 = (i : ℕ) + (p - 1 - (i : ℕ))
      omega
    simpa [heq] using h
  have himage := hE _ hlast
  rw [cyclicForwardEndomorphism_apply_last k α hp] at himage
  exact smulExtract k N _ _ hα himage

private theorem eqTopOfAllBasis {d : ℕ}
    (N : Submodule k (Fin d → k))
    (hbasis : ∀ i, coordinateVector k d i ∈ N) : N = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = Finset.univ.sum fun i : Fin d => v i • coordinateVector k d i := by
    ext j
    simp [Finset.sum_apply, coordinateVector_apply]
  rw [hv]
  exact Submodule.sum_smul_mem N _ fun i _ => hbasis i

private theorem toSubmoduleNeBot {d : ℕ}
    (N : LieSubmodule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (Fin d → k)) (hN : N ≠ ⊥) :
    N.toSubmodule ≠ ⊥ := by
  intro hbot
  apply hN
  apply LieSubmodule.toSubmodule_injective
  simpa using hbot

                                                                         
/-- Under the prime characteristic hypotheses, every parameter module is irreducible. -/
@[source_ref "Chapter2/Problem2.16.4" (role := supporting)]
theorem isIrreducible_parameterModule (a : ModuleParameter k p) :
    LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) := by
  classical
  cases a with
  | restricted n =>
      haveI : NeZero ((n : ℕ) + 1) := ⟨by omega⟩
      haveI : Nontrivial (parameterModule k (.restricted n)) := by
        change Nontrivial (Fin ((n : ℕ) + 1) → k)
        infer_instance
      apply LieModule.IsIrreducible.mk
      intro N hN
      let Nlin : Submodule k (Fin ((n : ℕ) + 1) → k) := N.toSubmodule
      have hNlin : Nlin ≠ ⊥ := by
        intro hbot
        apply hN
        change N.toSubmodule = (⊥ : Submodule k (parameterModule k (.restricted n))) at hbot
        exact (LieSubmodule.toSubmodule_eq_bot N).mp hbot
      have hH : ∀ v ∈ N, standardThirdEndomorphism (d := (n : ℕ) + 1) k (n : k) v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) hv
        change parameterModuleLieHom k (.restricted n) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) v ∈ N at h
        rw [parameterModuleLieHom_thirdElement] at h
        exact h
      obtain ⟨i, hi⟩ := exists_basis_mem_of_diagonal k
        (fun j : Fin ((n : ℕ) + 1) => (n : k) - 2 * (j : ℕ))
        (subWeightsPairwise k (by omega) (n : k)) Nlin
        (standardThirdEndomorphism (d := (n : ℕ) + 1) k (n : k)) (fun _ _ => rfl) hH
        hNlin
      have hE : ∀ v ∈ N, standardBackwardEndomorphism (d := (n : ℕ) + 1) k (n : k) v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) hv
        change parameterModuleLieHom k (.restricted n) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) v ∈ N at h
        rw [parameterModuleLieHom_firstElement] at h
        exact h
      have hcoeff : ∀ j : ℕ, 0 < j → j < (n : ℕ) + 1 →
          (j : k) * ((n : k) - (j : k) + 1) ≠ 0 := by
        intro j hj0 hj
        apply mul_ne_zero
        · exact natCastNeZeroLt k hj0 (by omega)
        · have heq : (n : k) - (j : k) + 1 = ((n : ℕ) - j + 1 : ℕ) := by
            rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega : j ≤ (n : ℕ))]
          rw [heq]
          exact natCastNeZeroLt k (by omega) (by omega)
      have h0 := zeroBasisOfVermaE k (n : k) Nlin hE hcoeff hi
      have hF : ∀ v ∈ N, standardCyclicForwardEndomorphism (d := (n : ℕ) + 1) k 0 v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) hv
        change parameterModuleLieHom k (.restricted n) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) v ∈ N at h
        rw [parameterModuleLieHom_secondElement] at h
        exact h
      have htop := eqTopOfAllBasis k Nlin (allBasisOfVermaF k 0 Nlin hF h0)
      change N.toSubmodule = (⊤ : Submodule k (parameterModule k (.restricted n))) at htop
      exact (LieSubmodule.toSubmodule_eq_top N).mp htop
  | highest β lam hsimple =>
      haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
      haveI : Nontrivial (parameterModule k (.highest β lam hsimple)) := by
        change Nontrivial (Fin p → k)
        infer_instance
      apply LieModule.IsIrreducible.mk
      intro N hN
      let Nlin : Submodule k (Fin p → k) := N.toSubmodule
      have hNlin : Nlin ≠ ⊥ := by
        intro hbot
        apply hN
        change N.toSubmodule = (⊥ : Submodule k (parameterModule k (.highest β lam hsimple))) at hbot
        exact (LieSubmodule.toSubmodule_eq_bot N).mp hbot
      have hH : ∀ v ∈ N, standardThirdEndomorphism (d := p) k lam v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) hv
        change parameterModuleLieHom k (.highest β lam hsimple) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) v ∈ N at h
        rw [parameterModuleLieHom_thirdElement] at h
        exact h
      obtain ⟨i, hi⟩ := exists_basis_mem_of_diagonal k
        (fun j : Fin p => lam - 2 * (j : ℕ)) (subWeightsPairwise k le_rfl lam)
        Nlin (standardThirdEndomorphism (d := p) k lam) (fun _ _ => rfl) hH hNlin
      have hF : ∀ v ∈ N, standardCyclicForwardEndomorphism (d := p) k β v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) hv
        change parameterModuleLieHom k (.highest β lam hsimple) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) v ∈ N at h
        rw [parameterModuleLieHom_secondElement] at h
        exact h
      rcases hsimple with hβ | hlam
      · have h0 := zeroBasisOfCyclicVermaF k β hβ Nlin hF hi
        have htop := eqTopOfAllBasis k Nlin (allBasisOfVermaF k β Nlin hF h0)
        change N.toSubmodule =
          (⊤ : Submodule k (parameterModule k (.highest β lam (Or.inl hβ)))) at htop
        exact (LieSubmodule.toSubmodule_eq_top N).mp htop
      · have hE : ∀ v ∈ N, standardBackwardEndomorphism (d := p) k lam v ∈ N := by
          intro v hv
          have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) hv
          change parameterModuleLieHom k (.highest β lam (Or.inr hlam))
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) v ∈ N at h
          rw [parameterModuleLieHom_firstElement] at h
          exact h
        have hcoeff : ∀ j : ℕ, 0 < j → j < p →
            (j : k) * (lam - (j : k) + 1) ≠ 0 := by
          intro j hj0 hjp
          apply mul_ne_zero (natCastNeZeroLt k hj0 hjp)
          intro hz
          have hlamcast : lam = ((j - 1 : ℕ) : k) := by
            calc
              lam = (j : k) - 1 := by linear_combination hz
              _ = ((j - 1 : ℕ) : k) := by
                rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
          apply hlam
          rw [hlamcast]
          exact (Subfield.mem_bot_iff_pow_eq_self k p).mp (by simp)
        have h0 := zeroBasisOfVermaE k lam Nlin hE hcoeff hi
        have htop := eqTopOfAllBasis k Nlin (allBasisOfVermaF k β Nlin hF h0)
        change N.toSubmodule =
          (⊤ : Submodule k (parameterModule k (.highest β lam (Or.inr hlam)))) at htop
        exact (LieSubmodule.toSubmodule_eq_top N).mp htop
  | cyclic α lam q hα =>
      haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
      haveI : Nontrivial (parameterModule k (.cyclic α lam q hα)) := by
        change Nontrivial (Fin p → k)
        infer_instance
      apply LieModule.IsIrreducible.mk
      intro N hN
      let Nlin : Submodule k (Fin p → k) := N.toSubmodule
      have hNlin : Nlin ≠ ⊥ := by
        intro hbot
        apply hN
        change N.toSubmodule = (⊥ : Submodule k (parameterModule k (.cyclic α lam q hα))) at hbot
        exact (LieSubmodule.toSubmodule_eq_bot N).mp hbot
      have hH : ∀ v ∈ N, parameterThirdEndomorphism (p := p) k lam v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) hv
        change parameterModuleLieHom k (.cyclic α lam q hα) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) v ∈ N at h
        rw [parameterModuleLieHom_thirdElement] at h
        exact h
      obtain ⟨i, hi⟩ := exists_basis_mem_of_diagonal k
        (fun j : Fin p => lam + 2 * (j : ℕ)) (addWeightsPairwise k lam)
        Nlin (parameterThirdEndomorphism (p := p) k lam) (fun _ _ => rfl) hH hNlin
      have hE : ∀ v ∈ N, cyclicForwardEndomorphism (p := p) k α v ∈ N := by
        intro v hv
        have h := N.lie_mem (x := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) hv
        change parameterModuleLieHom k (.cyclic α lam q hα) (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) v ∈ N at h
        rw [parameterModuleLieHom_firstElement] at h
        exact h
      have h0 := zeroBasisOfCyclicE k α hα Nlin hE hi
      have hall : ∀ j, coordinateVector k p j ∈ N := by
        intro j
        suffices ∀ (m : ℕ) (hm : m < p), coordinateVector k p ⟨m, hm⟩ ∈ N from this j j.isLt
        intro m hm
        induction m with
        | zero => exact h0
        | succ m ih =>
            have himage := hE _ (ih (by omega))
            rwa [cyclicForwardEndomorphism_apply_lt_last k α m hm] at himage
      have htop := eqTopOfAllBasis k Nlin hall
      change N.toSubmodule = (⊤ : Submodule k (parameterModule k (.cyclic α lam q hα))) at htop
      exact (LieSubmodule.toSubmodule_eq_top N).mp htop

end Irreducibility

                                                          

/-- Every parameter module is finite-dimensional over the field. -/
theorem finiteDimensional_parameterModule (a : ModuleParameter k p) :
    FiniteDimensional k (parameterModule k a) := by
  infer_instance

section NormalForm

variable [IsAlgClosed k]
variable {M : Type u} [AddCommGroup M] [Module k M]

                                                                                         
                                                                                         
private structure HighestNormalForm (E F H : Module.End k M) (p : ℕ) where
  beta : k
  lam : k
  v0 : M
  v0_ne : v0 ≠ 0
  e_v0 : E v0 = 0
  h_v0 : H v0 = lam • v0
  f_pow : F ^ p = beta • 1
  orbit_top : Submodule.span k (Set.range fun i : Fin p => (F ^ (i : ℕ)) v0) = ⊤

                                                   
private structure CyclicNormalForm (E F H : Module.End k M) (p : ℕ) where
  alpha : k
  alpha_ne : alpha ≠ 0
  lam : k
  q : k
  v0 : M
  v0_ne : v0 ≠ 0
  e_pow : E ^ p = alpha • 1
  h_v0 : H v0 = lam • v0
  f_v0 : F v0 = q • (E ^ (p - 1)) v0
  orbit_top : Submodule.span k (Set.range fun i : Fin p => (E ^ (i : ℕ)) v0) = ⊤

private inductive NormalForm (E F H : Module.End k M) (p : ℕ) where
  | highest (data : HighestNormalForm k E F H p)
  | cyclic (data : CyclicNormalForm k E F H p)

                                                                                  
                                                                                     
private theorem exists_normalForm (p : ℕ) [Fact p.Prime] [CharP k p] (hp : 2 < p)
    (M : Type u) [AddCommGroup M] [Module k M] [LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M]
    [LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M] [FiniteDimensional k M]
    [LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M] :
    Nonempty (NormalForm k
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)) p) := by
  haveI : Nontrivial M := LieModule.nontrivial_of_isIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M
                                         
  set E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) with hEdef
  set F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) with hFdef
  set H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) with hHdef
                                                                  
  have hEe : ∀ m : M, ⁅RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k, m⁆ = E m := fun _ => rfl
  have hFf : ∀ m : M, ⁅RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k, m⁆ = F m := fun _ => rfl
  have hHh : ∀ m : M, ⁅RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k, m⁆ = H m := fun _ => rfl
                                                                   
  have hHE : H * E = E * H + (2 : k) • E := by
    have h1 : (⁅H, E⁆ : Module.End k M) = (2 : k) • E := by
      rw [hHdef, hEdef, ← (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M).map_lie, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.bracket_weight_raising, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1, add_comm]
  have hHF : H * F = F * H - (2 : k) • F := by
    have h1 : (⁅H, F⁆ : Module.End k M) = -((2 : k) • F) := by
      rw [hHdef, hFdef, ← (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M).map_lie, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.bracket_weight_lowering, map_neg, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1]; abel
  have hEF : E * F - F * E = H := by
    have h1 : (⁅E, F⁆ : Module.End k M) = H := by
      rw [hEdef, hFdef, ← (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M).map_lie, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.bracket_raising_lowering]
    rwa [LieRing.of_associative_ring_bracket] at h1
                                 
  have hHEpow : ∀ i : ℕ, H * E ^ i = E ^ i * H + ((2 * i : ℕ) : k) • E ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hsc : ((2 : k) + ((2 * n : ℕ) : k)) = ((2 * (n + 1) : ℕ) : k) := by push_cast; ring
      calc H * E ^ (n + 1)
          = (H * E ^ n) * E := by rw [pow_succ, ← mul_assoc]
        _ = (E ^ n * H + ((2 * n : ℕ) : k) • E ^ n) * E := by rw [ih]
        _ = E ^ n * (H * E) + ((2 * n : ℕ) : k) • (E ^ n * E) := by
              rw [add_mul, mul_assoc, smul_mul_assoc]
        _ = E ^ n * (E * H + (2 : k) • E) + ((2 * n : ℕ) : k) • (E ^ n * E) := by rw [hHE]
        _ = (E ^ n * E) * H + ((2 : k) + ((2 * n : ℕ) : k)) • (E ^ n * E) := by
              rw [mul_add, ← mul_assoc, mul_smul_comm, add_assoc, ← add_smul]
        _ = E ^ (n + 1) * H + ((2 * (n + 1) : ℕ) : k) • E ^ (n + 1) := by rw [hsc, ← pow_succ]
                                                     
  have hrec : ∀ m : ℕ, F * E ^ (m + 1) - E ^ (m + 1) * F
      = (F * E ^ m - E ^ m * F) * E - E ^ m * H := by
    intro m
    have hEFc : E * F = F * E + H := by rw [← hEF]; abel
    calc F * E ^ (m + 1) - E ^ (m + 1) * F
        = F * E ^ m * E - E ^ m * (E * F) := by rw [pow_succ]; noncomm_ring
      _ = F * E ^ m * E - E ^ m * (F * E + H) := by rw [hEFc]
      _ = F * E ^ m * E - E ^ m * (F * E) - E ^ m * H := by noncomm_ring
      _ = (F * E ^ m - E ^ m * F) * E - E ^ m * H := by noncomm_ring
  have hFEpow : ∀ n : ℕ, F * E ^ (n + 1) - E ^ (n + 1) * F
      = -(((n + 1 : ℕ) : k)) • (E ^ n * H) - (((n + 1) * n : ℕ) : k) • E ^ n := by
    intro n
    induction n with
    | zero =>
      have hlhs : F * E ^ (0 + 1) - E ^ (0 + 1) * F = -H := by
        rw [zero_add, pow_one, ← hEF]; abel
      have hrhs : -(((0 + 1 : ℕ) : k)) • (E ^ 0 * H) - (((0 + 1) * 0 : ℕ) : k) • E ^ 0 = -H := by
        simp
      rw [hlhs, hrhs]
    | succ n ih =>
      rw [hrec (n + 1), ih]
      have hHErw : E ^ (n + 1) * H = E ^ n * (H * E) - (2 : k) • E ^ (n + 1) := by
        rw [hHE]; noncomm_ring
                           
      have hsc1 : (((n + 1 : ℕ) : k) + 1) = (((n + 1) + 1 : ℕ) : k) := by push_cast; ring
      have hsc2 : ((2 : k) * ((n + 1 : ℕ) : k) + (((n + 1) * n : ℕ) : k))
          = ((((n + 1) + 1) * (n + 1) : ℕ) : k) := by push_cast; ring
      rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hHE, mul_add, mul_smul_comm,
        ← pow_succ]
                                                                              
      rw [show (E ^ n * (E * H)) = E ^ (n + 1) * H from by rw [pow_succ]; noncomm_ring]
      module
                                                
  have hcharp : ((p : ℕ) : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k p
  have hcomm_to_schur : ∀ (φ : Module.End k M), φ * E = E * φ → φ * F = F * φ →
      φ * H = H * φ → ∀ (x : RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (m : M), φ ⁅x, m⁆ = ⁅x, φ m⁆ := by
    intro φ hcE hcF hcH x m
    have hxdecomp : (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x)
        = x.val 0 1 • E + x.val 1 0 • F + x.val 0 0 • H := by
      conv_lhs => rw [RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.eq_linearCombination_raising_lowering_weight x]
      rw [map_add, map_add, map_smul, map_smul, map_smul, ← hEdef, ← hFdef, ← hHdef]
    have hgen : φ * (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x) = (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x) * φ := by
      rw [hxdecomp, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, hcE, hcF, hcH,
        ← smul_mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, ← add_mul, ← add_mul]
    calc φ ⁅x, m⁆ = φ ((LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x) m) := rfl
      _ = (φ * (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x)) m := rfl
      _ = ((LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x) * φ) m := by rw [hgen]
      _ = ⁅x, φ m⁆ := rfl
                 
  have hEpFcomm : E ^ p * F = F * E ^ p := by
    have hp1 : p - 1 + 1 = p := by omega
    have h := hFEpow (p - 1)
    have hz1 : (((p - 1 + 1 : ℕ) : k)) = 0 := by rw [hp1]; exact hcharp
    have hz2 : ((((p - 1 + 1) * (p - 1) : ℕ) : k)) = 0 := by
      rw [hp1]; push_cast [hcharp]; ring
    rw [hz1, hz2] at h
    simp only [neg_zero, zero_smul, sub_zero] at h
    rw [hp1] at h
    exact (sub_eq_zero.mp h).symm
  have hEpHcomm : E ^ p * H = H * E ^ p := by
    have h := hHEpow p
    have hz : (((2 * p : ℕ) : k)) = 0 := by push_cast [hcharp]; ring
    rw [hz, zero_smul, add_zero] at h
    exact h.symm
  have hEpEcomm : E ^ p * E = E * E ^ p := by rw [← pow_succ, ← pow_succ']
  obtain ⟨α, hα'⟩ := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.exists_scalar_action_eq_of_commutes_lieAction (E ^ p) (hcomm_to_schur (E ^ p) hEpEcomm hEpFcomm hEpHcomm)
  have hα : E ^ p = α • 1 := by ext m; rw [hα' m]; simp
                             
  have hFpEcomm : F ^ p * E = E * F ^ p := by
                                                                
    have hHF' : (-H) * F = F * (-H) + (2 : k) • F := by
      rw [neg_mul, mul_neg, hHF]; abel
    have hFE' : F * E - E * F = -H := by rw [← hEF]; abel
                                               
    have hrec' : ∀ m : ℕ, E * F ^ (m + 1) - F ^ (m + 1) * E
        = (E * F ^ m - F ^ m * E) * F - F ^ m * (-H) := by
      intro m
      have hFEc : F * E = E * F + (-H) := by rw [← hFE']; abel
      calc E * F ^ (m + 1) - F ^ (m + 1) * E
          = E * F ^ m * F - F ^ m * (F * E) := by rw [pow_succ]; noncomm_ring
        _ = E * F ^ m * F - F ^ m * (E * F + (-H)) := by rw [hFEc]
        _ = E * F ^ m * F - F ^ m * (E * F) - F ^ m * (-H) := by noncomm_ring
        _ = (E * F ^ m - F ^ m * E) * F - F ^ m * (-H) := by noncomm_ring
    have hFFpow : ∀ n : ℕ, E * F ^ (n + 1) - F ^ (n + 1) * E
        = -(((n + 1 : ℕ) : k)) • (F ^ n * (-H)) - (((n + 1) * n : ℕ) : k) • F ^ n := by
      intro n
      induction n with
      | zero =>
        have hlhs : E * F ^ (0 + 1) - F ^ (0 + 1) * E = -(-H) := by
          rw [zero_add, pow_one, ← hFE']; abel
        have hrhs : -(((0 + 1 : ℕ) : k)) • (F ^ 0 * (-H)) - (((0 + 1) * 0 : ℕ) : k) • F ^ 0
            = -(-H) := by simp
        rw [hlhs, hrhs]
      | succ n ih =>
        rw [hrec' (n + 1), ih]
        rw [sub_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, hHF', mul_add, mul_smul_comm,
          ← pow_succ]
        rw [show (F ^ n * (F * (-H))) = F ^ (n + 1) * (-H) from by rw [pow_succ]; noncomm_ring]
        module
    have hp1 : p - 1 + 1 = p := by omega
    have hh := hFFpow (p - 1)
    have hz1 : (((p - 1 + 1 : ℕ) : k)) = 0 := by rw [hp1]; exact hcharp
    have hz2 : ((((p - 1 + 1) * (p - 1) : ℕ) : k)) = 0 := by rw [hp1]; push_cast [hcharp]; ring
    rw [hz1, hz2] at hh
    simp only [neg_zero, zero_smul, sub_zero] at hh
    rw [hp1] at hh
    exact (sub_eq_zero.mp hh).symm
  have hFpHcomm : F ^ p * H = H * F ^ p := by
                                  
    have hHFpow : ∀ i : ℕ, H * F ^ i = F ^ i * H - ((2 * i : ℕ) : k) • F ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ n ih =>
        have hsc : (((2 * (n + 1) : ℕ) : k)) = ((2 * n : ℕ) : k) + (2 : k) := by push_cast; ring
        calc H * F ^ (n + 1)
            = (H * F ^ n) * F := by rw [pow_succ, ← mul_assoc]
          _ = (F ^ n * H - ((2 * n : ℕ) : k) • F ^ n) * F := by rw [ih]
          _ = F ^ n * (H * F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by
                rw [sub_mul, mul_assoc, smul_mul_assoc]
          _ = F ^ n * (F * H - (2 : k) • F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by rw [hHF]
          _ = F ^ (n + 1) * H - ((2 * (n + 1) : ℕ) : k) • F ^ (n + 1) := by
                rw [mul_sub, ← mul_assoc, mul_smul_comm, ← pow_succ, hsc, add_smul]
                abel
    have h := hHFpow p
    have hz : (((2 * p : ℕ) : k)) = 0 := by push_cast [hcharp]; ring
    rw [hz, zero_smul, sub_zero] at h
    exact h.symm
  have hFpFcomm : F ^ p * F = F * F ^ p := by rw [← pow_succ, ← pow_succ']
  obtain ⟨β, hβ'⟩ := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.exists_scalar_action_eq_of_commutes_lieAction (F ^ p) (hcomm_to_schur (F ^ p) hFpEcomm hFpFcomm hFpHcomm)
  have hβ : F ^ p = β • 1 := by ext m; rw [hβ' m]; simp
                                            
                                 
  have hHFpow : ∀ i : ℕ, H * F ^ i = F ^ i * H - ((2 * i : ℕ) : k) • F ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hsc : (((2 * (n + 1) : ℕ) : k)) = ((2 * n : ℕ) : k) + (2 : k) := by push_cast; ring
      calc H * F ^ (n + 1)
          = (H * F ^ n) * F := by rw [pow_succ, ← mul_assoc]
        _ = (F ^ n * H - ((2 * n : ℕ) : k) • F ^ n) * F := by rw [ih]
        _ = F ^ n * (H * F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by
              rw [sub_mul, mul_assoc, smul_mul_assoc]
        _ = F ^ n * (F * H - (2 : k) • F) - ((2 * n : ℕ) : k) • (F ^ n * F) := by rw [hHF]
        _ = F ^ (n + 1) * H - ((2 * (n + 1) : ℕ) : k) • F ^ (n + 1) := by
              rw [mul_sub, ← mul_assoc, mul_smul_comm, ← pow_succ, hsc, add_smul]
              abel
  by_cases hα0 : α = 0
  ·                                                           
    have hEnil : E ^ p = 0 := by rw [hα, hα0, zero_smul]
                                                                                               
    have hKne : LinearMap.ker E ≠ ⊥ := by
      rw [Ne, LinearMap.ker_eq_bot]
      intro hEinj
      have hEpinj : Function.Injective (E ^ p) := by
        rw [Module.End.coe_pow]; exact hEinj.iterate p
      rw [hEnil] at hEpinj
      obtain ⟨a, b, hab⟩ := exists_pair_ne M
      exact hab (hEpinj (by simp))
                                
    have hHK : ∀ v ∈ LinearMap.ker E, H v ∈ LinearMap.ker E := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hEH : E * H = H * E - (2 : k) • E := by rw [hHE]; abel
      have hEHv : E (H v) = (E * H) v := rfl
      rw [hEHv, hEH]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hv]
      simp
                                                                
    haveI : Nontrivial (LinearMap.ker E) := (Submodule.nontrivial_iff_ne_bot).mpr hKne
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (H.restrict hHK)
    obtain ⟨w, hw⟩ := hlam.exists_hasEigenvector
    set v0 : M := (w : M) with hv0def
    have hv0ne : v0 ≠ 0 := by rw [hv0def, Ne, Submodule.coe_eq_zero]; exact hw.2
    have hEv0 : E v0 = 0 := LinearMap.mem_ker.mp w.2
    have hHv0 : H v0 = lam • v0 := by
      have h1 : (H.restrict hHK) w = lam • w := (Module.End.mem_eigenspace_iff).mp hw.1
      have := congrArg (Subtype.val) h1
      simpa [LinearMap.restrict_apply, hv0def, Submodule.coe_smul] using this
                                       
    set g : ℕ → M := fun j => (F ^ j) v0 with hgdef
    set W : Submodule k M := Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) with hWdef
    have hg0 : g 0 = v0 := by simp [hgdef]
    have hmemgen : ∀ j : ℕ, j < p → g j ∈ W := fun j hj =>
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
                   
    have hFW : ∀ w ∈ W, F w ∈ W := by
      refine fun w hw => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span F _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hFg : F (g (i : ℕ)) = g ((i : ℕ) + 1) := by
        simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
      rw [hFg]
      by_cases hip : (i : ℕ) + 1 < p
      · exact hmemgen _ hip
      · have hip1 : (i : ℕ) + 1 = p := by omega
        have hval : g ((i : ℕ) + 1) = β • v0 := by
          simp only [hgdef, hip1, hβ, LinearMap.smul_apply, Module.End.one_apply]
        rw [hval]
        exact W.smul_mem β (hg0 ▸ hmemgen 0 (by omega))
    have hgW : ∀ j, g j ∈ W := by
      intro j
      induction j with
      | zero => exact hg0 ▸ hmemgen 0 (by omega)
      | succ j ih =>
        have hFg : g (j + 1) = F (g j) := by
          simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
        rw [hFg]; exact hFW _ ih
                   
    have hHW : ∀ w ∈ W, H w ∈ W := by
      refine fun w hw => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span H _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hval : H (g (i : ℕ)) = lam • g (i : ℕ) - ((2 * (i : ℕ) : ℕ) : k) • g (i : ℕ) := by
        simp only [hgdef]
        rw [← Module.End.mul_apply, hHFpow (i : ℕ)]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, hHv0, map_smul]
      rw [hval]
      exact W.sub_mem (W.smul_mem _ (hmemgen _ i.isLt)) (W.smul_mem _ (hmemgen _ i.isLt))
                   
    have hEW : ∀ w ∈ W, E w ∈ W := by
      have hEorbit : ∀ j : ℕ, E (g j) ∈ W := by
        intro j
        induction j with
        | zero =>
          have hz : E (g 0) = 0 := by rw [hg0]; exact hEv0
          rw [hz]; exact W.zero_mem
        | succ j ih =>
          have hEF' : E * F = F * E + H := by rw [← hEF]; abel
          have hstep : E (g (j + 1)) = F (E (g j)) + H (g j) := by
            have hFg : g (j + 1) = F (g j) := by
              simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
            rw [hFg, ← Module.End.mul_apply, hEF']
            simp only [LinearMap.add_apply, Module.End.mul_apply]
          rw [hstep]
          exact W.add_mem (hFW _ ih) (hHW _ (hgW j))
      refine fun w hw => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span E _ ?_ hw
      rintro s ⟨i, rfl⟩
      exact hEorbit (i : ℕ)
                                                                                          
    have hlie := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.lieStable_of_stable_generators W
      (fun m hm => by rw [hEe]; exact hEW m hm)
      (fun m hm => by rw [hFf]; exact hFW m hm)
      (fun m hm => by rw [hHh]; exact hHW m hm)
    have htop : W = ⊤ := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.eq_top_of_lieStable_of_exists_ne_zero W hlie ⟨v0, hg0 ▸ hgW 0, hv0ne⟩
    refine ⟨.highest
      { beta := β, lam := lam, v0 := v0, v0_ne := hv0ne, e_v0 := hEv0,
        h_v0 := hHv0, f_pow := hβ, orbit_top := ?_ }⟩
    simpa [W, g] using htop
  ·                                                                  
    have hEinj : Function.Injective E := by
      have hEpinj : Function.Injective (E ^ p) := by
        rw [hα]
        intro a b hab
        simp only [LinearMap.smul_apply, Module.End.one_apply] at hab
        exact smul_right_injective M hα0 hab
      intro a b hab
      apply hEpinj
      have hsplit : E ^ p = E ^ (p - 1) * E := by rw [← pow_succ]; congr 1; omega
      rw [hsplit, Module.End.mul_apply, Module.End.mul_apply, hab]
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue H
                                                                         
    have hFEmaps : ∀ v ∈ H.eigenspace lam, (F * E) v ∈ H.eigenspace lam := by
      intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have hcomm : H * (F * E) = (F * E) * H := by
        calc H * (F * E) = (H * F) * E := by rw [mul_assoc]
          _ = (F * H - (2 : k) • F) * E := by rw [hHF]
          _ = F * (H * E) - (2 : k) • (F * E) := by rw [sub_mul, mul_assoc, smul_mul_assoc]
          _ = F * (E * H + (2 : k) • E) - (2 : k) • (F * E) := by rw [hHE]
          _ = (F * E) * H := by rw [mul_add, mul_smul_comm, ← mul_assoc]; abel
      calc H ((F * E) v) = (H * (F * E)) v := rfl
        _ = ((F * E) * H) v := by rw [hcomm]
        _ = (F * E) (H v) := rfl
        _ = (F * E) (lam • v) := by rw [hv]
        _ = lam • (F * E) v := by rw [map_smul]
    haveI : Nontrivial (H.eigenspace lam) := (Submodule.nontrivial_iff_ne_bot).mpr hlam
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((F * E).restrict hFEmaps)
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    set v0 : M := (w : M) with hv0def
    have hv0ne : v0 ≠ 0 := by rw [hv0def, Ne, Submodule.coe_eq_zero]; exact hw.2
    have hHv0 : H v0 = lam • v0 := by
      have hmem := w.2
      rw [Module.End.mem_eigenspace_iff] at hmem
      exact hmem
    have hFEv0 : (F * E) v0 = c • v0 := by
      have h1 : ((F * E).restrict hFEmaps) w = c • w := (Module.End.mem_eigenspace_iff).mp hw.1
      have h2 := congrArg (Subtype.val) h1
      simpa [LinearMap.restrict_apply, hv0def, Submodule.coe_smul] using h2
                                   
    have hEFv0 : E (F v0) = (c + lam) • v0 := by
      have hEF' : E * F = F * E + H := by rw [← hEF]; abel
      have he : E (F v0) = (E * F) v0 := rfl
      rw [he, hEF', LinearMap.add_apply, hFEv0, hHv0, ← add_smul]
                                                                             
    have hFv0 : F v0 = (c + lam) • α⁻¹ • (E ^ (p - 1)) v0 := by
      apply hEinj
      rw [hEFv0, map_smul, map_smul]
      have hEp : E ((E ^ (p - 1)) v0) = α • v0 := by
        have hmul : E * E ^ (p - 1) = E ^ p := by rw [← pow_succ']; congr 1; omega
        rw [← Module.End.mul_apply, hmul, hα, LinearMap.smul_apply, Module.End.one_apply]
      rw [hEp, smul_smul α⁻¹ α v0, inv_mul_cancel₀ hα0, one_smul]
                                       
    set g : ℕ → M := fun j => (E ^ j) v0 with hgdef
    set W : Submodule k M := Submodule.span k (Set.range (fun i : Fin p => g (i : ℕ))) with hWdef
    have hg0 : g 0 = v0 := by simp [hgdef]
    have hmemgen : ∀ j : ℕ, j < p → g j ∈ W := fun j hj =>
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
                   
    have hEW : ∀ w ∈ W, E w ∈ W := by
      refine fun w hw => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span E _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hEg : E (g (i : ℕ)) = g ((i : ℕ) + 1) := by
        simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
      rw [hEg]
      by_cases hip : (i : ℕ) + 1 < p
      · exact hmemgen _ hip
      · have hip1 : (i : ℕ) + 1 = p := by omega
        have hval : g ((i : ℕ) + 1) = α • v0 := by
          simp only [hgdef, hip1, hα, LinearMap.smul_apply, Module.End.one_apply]
        rw [hval]
        exact W.smul_mem α (hg0 ▸ hmemgen 0 (by omega))
    have hgW : ∀ j, g j ∈ W := by
      intro j
      induction j with
      | zero => exact hg0 ▸ hmemgen 0 (by omega)
      | succ j ih =>
        have hEg : g (j + 1) = E (g j) := by
          simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
        rw [hEg]; exact hEW _ ih
                   
    have hHW : ∀ w ∈ W, H w ∈ W := by
      refine fun w hw => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span H _ ?_ hw
      rintro s ⟨i, rfl⟩
      have hval : H (g (i : ℕ)) = lam • g (i : ℕ) + ((2 * (i : ℕ) : ℕ) : k) • g (i : ℕ) := by
        simp only [hgdef]
        rw [← Module.End.mul_apply, hHEpow (i : ℕ)]
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, hHv0, map_smul]
      rw [hval]
      exact W.add_mem (W.smul_mem _ (hmemgen _ i.isLt)) (W.smul_mem _ (hmemgen _ i.isLt))
                   
    have hFW : ∀ w ∈ W, F w ∈ W := by
      have hForbit : ∀ j : ℕ, F (g j) ∈ W := by
        intro j
        induction j with
        | zero =>
          rw [hg0, hFv0]
          have hEp1 : (E ^ (p - 1)) v0 = g (p - 1) := by simp only [hgdef]
          rw [hEp1, smul_smul]
          exact W.smul_mem _ (hmemgen (p - 1) (by omega))
        | succ j ih =>
          have hFE' : F * E = E * F - H := by rw [← hEF]; abel
          have hstep : F (g (j + 1)) = E (F (g j)) - H (g j) := by
            have hEg : g (j + 1) = E (g j) := by
              simp only [hgdef]; rw [← Module.End.mul_apply, ← pow_succ']
            rw [hEg, ← Module.End.mul_apply, hFE']
            simp only [LinearMap.sub_apply, Module.End.mul_apply]
          rw [hstep]
          exact W.sub_mem (hEW _ ih) (hHW _ (hgW j))
      refine fun w hw => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span F _ ?_ hw
      rintro s ⟨i, rfl⟩
      exact hForbit (i : ℕ)
                                                                                          
    have hlie := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.lieStable_of_stable_generators W
      (fun m hm => by rw [hEe]; exact hEW m hm)
      (fun m hm => by rw [hFf]; exact hFW m hm)
      (fun m hm => by rw [hHh]; exact hHW m hm)
    have htop : W = ⊤ := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.eq_top_of_lieStable_of_exists_ne_zero W hlie ⟨v0, hg0 ▸ hgW 0, hv0ne⟩
    refine ⟨.cyclic
      { alpha := α, alpha_ne := hα0, lam := lam, q := (c + lam) * α⁻¹,
        v0 := v0, v0_ne := hv0ne, e_pow := hα, h_v0 := hHv0,
        f_v0 := ?_, orbit_top := ?_ }⟩
    · simpa only [smul_smul] using hFv0
    · simpa [W, g] using htop


                                                                   
private noncomputable def coordinateMap {d : ℕ} (v : Fin d → M) :
    (Fin d → k) →ₗ[k] M where
  toFun c := ∑ i, c i • v i
  map_add' c c' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
      Finset.smul_sum]

omit [IsAlgClosed k] in
@[simp]
private theorem coordinateMap_basis {d : ℕ} (v : Fin d → M) (i : Fin d) :
    coordinateMap k v (coordinateVector k d i) = v i := by
  simp [coordinateMap, coordinateVector_apply]

omit [IsAlgClosed k] in
private theorem coordinateMap_surjective {d : ℕ} (v : Fin d → M)
    (htop : Submodule.span k (Set.range v) = ⊤) :
    Function.Surjective (coordinateMap k v) := by
  rw [← LinearMap.range_eq_top]
  apply le_antisymm le_top
  rw [← htop]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨coordinateVector k d i, coordinateMap_basis k v i⟩

omit [IsAlgClosed k] in
private theorem h_f_pow (_E F H : Module.End k M)
    (hHF : H * F = F * H - (2 : k) • F) (lam : k) (v : M)
    (hv : H v = lam • v) : ∀ n : ℕ,
    H ((F ^ n) v) = (lam - 2 * (n : ℕ)) • (F ^ n) v := by
  intro n
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply, hHF,
        LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, ih, map_smul]
      push_cast
      module

omit [IsAlgClosed k] in
private theorem e_f_pow_succ (E F H : Module.End k M)
    (hEF : E * F - F * E = H) (hHF : H * F = F * H - (2 : k) • F)
    (lam : k) (v : M) (hEv : E v = 0) (hHv : H v = lam • v) : ∀ n : ℕ,
    E ((F ^ (n + 1)) v) =
      (((n + 1 : ℕ) : k) * (lam - (n : k))) • (F ^ n) v := by
  intro n
  induction n with
  | zero =>
      have hEF' : E * F = F * E + H := by rw [← hEF]; abel
      rw [zero_add, pow_one, ← Module.End.mul_apply, hEF', LinearMap.add_apply,
        Module.End.mul_apply, hEv, hHv]
      simp
  | succ n ih =>
      have hEF' : E * F = F * E + H := by rw [← hEF]; abel
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ',
        Module.End.mul_apply, ← Module.End.mul_apply, hEF', LinearMap.add_apply,
        Module.End.mul_apply, ih, map_smul, h_f_pow k E F H hHF lam v hHv (n + 1)]
      push_cast
      rw [← Module.End.mul_apply, ← pow_succ']
      module

omit [IsAlgClosed k] in
private theorem h_e_pow (E _F H : Module.End k M)
    (hHE : H * E = E * H + (2 : k) • E) (lam : k) (v : M)
    (hv : H v = lam • v) : ∀ n : ℕ,
    H ((E ^ n) v) = (lam + 2 * (n : ℕ)) • (E ^ n) v := by
  intro n
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply, hHE,
        LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, ih, map_smul]
      push_cast
      module

omit [IsAlgClosed k] in
private theorem f_e_pow_succ (E F H : Module.End k M) (p : ℕ)
    (hFE : F * E = E * F - H) (hHE : H * E = E * H + (2 : k) • E)
    (alpha lam q : k) (v : M) (hEp : E ^ p = alpha • 1)
    (hFv : F v = q • (E ^ (p - 1)) v) (hHv : H v = lam • v)
    (hp : 0 < p) : ∀ n : ℕ,
    F ((E ^ (n + 1)) v) = recurrenceCoefficient k alpha lam q (n + 1) • (E ^ n) v := by
  intro n
  induction n with
  | zero =>
      rw [zero_add, pow_one, ← Module.End.mul_apply, hFE, LinearMap.sub_apply,
        Module.End.mul_apply, hFv, map_smul, hHv]
      have hmul : E * E ^ (p - 1) = E ^ p := by
        rw [← pow_succ']
        congr 1
        omega
      rw [← Module.End.mul_apply, hmul, hEp, LinearMap.smul_apply, Module.End.one_apply]
      simp [recurrenceCoefficient, smul_smul, mul_comm, sub_smul]
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ',
        Module.End.mul_apply, ← Module.End.mul_apply, hFE, LinearMap.sub_apply,
        Module.End.mul_apply, ih, map_smul, h_e_pow k E F H hHE lam v hHv (n + 1)]
      simp only [recurrenceCoefficient]
      push_cast
      rw [← Module.End.mul_apply, ← pow_succ']
      module

end NormalForm

section Intertwiners

variable {p : ℕ} [Fact p.Prime] [CharP k p] [Fact (2 < p)]
variable [IsAlgClosed k]
variable {M : Type u} [AddCommGroup M] [Module k M]
  [LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M] [LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M]

                                                                                             
private noncomputable def lieHomOfEFH (a : ModuleParameter k p)
    (φ : parameterModule k a →ₗ[k] M)
    (hE : ∀ v, φ ((parameterLieEndomorphismTriple k a).first v) =
      ⁅RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k, φ v⁆)
    (hF : ∀ v, φ ((parameterLieEndomorphismTriple k a).second v) =
      ⁅RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k, φ v⁆)
    (hH : ∀ v, φ ((parameterLieEndomorphismTriple k a).third v) =
      ⁅RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k, φ v⁆) :
    parameterModule k a →ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M where
  toLinearMap := φ
  map_lie' := by
    intro x v
    change φ (parameterModuleLieHom k a x v) =
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M x) (φ v)
    rw [RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.eq_linearCombination_raising_lowering_weight x]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      parameterModuleLieHom_firstElement, parameterModuleLieHom_secondElement, parameterModuleLieHom_thirdElement]
    rw [hE, hF, hH]
    rfl

omit [IsAlgClosed k] [LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M] in
private theorem lieHom_injective_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module k V]
    [LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) V]
    [LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) V]
    (φ : V →ₗ⁅k,RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M) {v : V} (hv : φ v ≠ 0) :
    Function.Injective φ := by
  rw [← LieModuleHom.ker_eq_bot]
  rcases IsSimpleOrder.eq_bot_or_eq_top φ.ker with hbot | htop
  · exact hbot
  · exfalso
    apply hv
    apply LieModuleHom.mem_ker.mp
    rw [htop]
    trivial

private noncomputable def lieEquivOfBijective
    {V : Type*} [AddCommGroup V] [Module k V]
    [LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) V]
    (φ : V →ₗ⁅k,RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M) (hφ : Function.Bijective φ) :
    V ≃ₗ⁅k,RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M := by
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  exact LieModuleEquiv.mk φ e.symm e.left_inv e.right_inv

omit [IsAlgClosed k] in
private theorem target_relations :
    let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
    let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
    let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
    H * E = E * H + (2 : k) • E ∧
      H * F = F * H - (2 : k) • F ∧ E * F - F * E = H := by
  dsimp only
  constructor
  · have h1 : (⁅(LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
        (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k),
        (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
          (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)⁆ : Module.End k M) =
        (2 : k) • (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
          (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) := by
      rw [← (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M).map_lie,
        RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.bracket_weight_raising, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1, add_comm]
  constructor
  · have h1 : (⁅(LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
        (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k),
        (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
          (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)⁆ : Module.End k M) =
        -((2 : k) • (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
          (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)) := by
      rw [← (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M).map_lie,
        RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.bracket_weight_lowering, map_neg, map_smul]
    rw [LieRing.of_associative_ring_bracket, sub_eq_iff_eq_add] at h1
    rw [h1]
    abel
  · have h1 : (⁅(LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
        (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k),
        (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
          (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)⁆ : Module.End k M) =
        (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M)
          (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) := by
      rw [← (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M).map_lie,
        RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.bracket_raising_lowering]
    rwa [LieRing.of_associative_ring_bracket] at h1

omit [IsAlgClosed k] in
private theorem highestNormalForm_equiv
    (data : HighestNormalForm k
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)) p)
    (simple : data.beta ≠ 0 ∨ data.lam ^ p ≠ data.lam) :
    Nonempty (parameterModule k (.highest data.beta data.lam simple) ≃ₗ⁅k,
      RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M) := by
  classical
  have hp : 2 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
  let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
  let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
  obtain ⟨hHE, hHF, hEF⟩ := target_relations (k := k) (M := M)
  let orbit : Fin p → M := fun i => (F ^ (i : ℕ)) data.v0
  let φ := coordinateMap k orbit
  have hE : ∀ v, φ (standardBackwardEndomorphism (d := p) k data.lam v) = E (φ v) := by
    intro v
    have hop : φ.comp (standardBackwardEndomorphism (d := p) k data.lam) = E.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin p))
      intro i
      rw [show (Pi.basisFun k (Fin p)) i = coordinateVector k p i by
        ext j
        simp [coordinateVector, Pi.single_apply, eq_comm]]
      simp only [LinearMap.comp_apply]
      change φ (standardBackwardEndomorphism (d := p) k data.lam (coordinateVector k p i)) =
        E (φ (coordinateVector k p i))
      by_cases hi : 0 < (i : ℕ)
      · rw [standardBackwardEndomorphism_apply_pos k data.lam (i : ℕ) hi i.isLt,
          map_smul, coordinateMap_basis, coordinateMap_basis]
        have he := e_f_pow_succ k E F H hEF hHF data.lam data.v0 data.e_v0
          data.h_v0 ((i : ℕ) - 1)
        rw [show (i : ℕ) - 1 + 1 = (i : ℕ) by omega] at he
        rw [he]
        congr 1
        push_cast [Nat.cast_sub (by omega : 1 ≤ (i : ℕ))]
        ring
      · let z : Fin p := ⟨0, by omega⟩
        have hi0 : i = z := by
          apply Fin.ext
          dsimp [z]
          omega
        rw [hi0]
        have hz : standardBackwardEndomorphism (d := p) k data.lam (coordinateVector k p z) = 0 := by
          ext j
          simp only [standardBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
            Pi.zero_apply]
          split
          · rename_i hj
            have hne : (⟨(j : ℕ) + 1, hj⟩ : Fin p) ≠ z := by
              intro heq
              have hval := congrArg Fin.val heq
              dsimp [z] at hval
              omega
            rw [if_neg hne]
            ring
          · ring
        rw [hz, map_zero, coordinateMap_basis]
        simp [orbit, E, z, data.e_v0]
    exact LinearMap.congr_fun hop v
  have hF : ∀ v, φ (standardCyclicForwardEndomorphism (d := p) k data.beta v) = F (φ v) := by
    intro v
    have hop : φ.comp (standardCyclicForwardEndomorphism (d := p) k data.beta) = F.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin p))
      intro i
      rw [show (Pi.basisFun k (Fin p)) i = coordinateVector k p i by
        ext j
        simp [coordinateVector, Pi.single_apply, eq_comm]]
      simp only [LinearMap.comp_apply]
      change φ (standardCyclicForwardEndomorphism (d := p) k data.beta (coordinateVector k p i)) =
        F (φ (coordinateVector k p i))
      by_cases hi : (i : ℕ) + 1 < p
      · rw [standardCyclicForwardEndomorphism_apply_lt_last k data.beta (i : ℕ) hi,
          coordinateMap_basis, coordinateMap_basis]
        change (F ^ ((i : ℕ) + 1)) data.v0 = F ((F ^ (i : ℕ)) data.v0)
        rw [pow_succ', Module.End.mul_apply]
      · have hitop : (i : ℕ) = p - 1 := by omega
        have hieq : i = ⟨p - 1, by omega⟩ := Fin.ext hitop
        rw [hieq]
        rw [standardCyclicForwardEndomorphism_apply_last k data.beta, map_smul,
          coordinateMap_basis, coordinateMap_basis]
        change data.beta • data.v0 = F ((F ^ (p - 1)) data.v0)
        rw [← Module.End.mul_apply, ← pow_succ', show p - 1 + 1 = p by omega,
          data.f_pow, LinearMap.smul_apply, Module.End.one_apply]
    exact LinearMap.congr_fun hop v
  have hH : ∀ v, φ (standardThirdEndomorphism (d := p) k data.lam v) = H (φ v) := by
    intro v
    have hop : φ.comp (standardThirdEndomorphism (d := p) k data.lam) = H.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin p))
      intro i
      rw [show (Pi.basisFun k (Fin p)) i = coordinateVector k p i by
        ext j
        simp [coordinateVector, Pi.single_apply, eq_comm]]
      simp only [LinearMap.comp_apply]
      change φ (standardThirdEndomorphism (d := p) k data.lam (coordinateVector k p i)) =
        H (φ (coordinateVector k p i))
      have hh := h_f_pow k E F H hHF data.lam data.v0 data.h_v0 (i : ℕ)
      rw [coordinateMap_basis, hh]
      have hsource : standardThirdEndomorphism (d := p) k data.lam (coordinateVector k p i) =
          (data.lam - 2 * (i : ℕ)) • coordinateVector k p i := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [standardThirdEndomorphism, coordinateVector_apply, mul_comm]
        · simp [standardThirdEndomorphism, coordinateVector_apply, hji]
      rw [hsource, map_smul, coordinateMap_basis]
    exact LinearMap.congr_fun hop v
  let a : ModuleParameter k p := .highest data.beta data.lam simple
  let ψ : parameterModule k a →ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M :=
    lieHomOfEFH k a φ hE hF hH
  letI : LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) :=
    isIrreducible_parameterModule k a
  have hψ0 : ψ (coordinateVector k p ⟨0, by omega⟩) ≠ 0 := by
    change φ (coordinateVector k p ⟨0, by omega⟩) ≠ 0
    rw [coordinateMap_basis]
    exact data.v0_ne
  have hinj : Function.Injective ψ := lieHom_injective_of_ne_zero k ψ hψ0
  have hsurj : Function.Surjective ψ := by
    change Function.Surjective φ
    exact coordinateMap_surjective k orbit (by simpa [orbit] using data.orbit_top)
  exact ⟨lieEquivOfBijective k ψ ⟨hinj, hsurj⟩⟩

omit [IsAlgClosed k] in
private theorem cyclicNormalForm_equiv
    (data : CyclicNormalForm k
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)) p) :
    Nonempty (parameterModule k ((.cyclic data.alpha data.lam data.q data.alpha_ne) : ModuleParameter k p) ≃ₗ⁅k,
      RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M) := by
  classical
  have hp : 2 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
  let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
  let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
  obtain ⟨hHE, _, hEF⟩ := target_relations (k := k) (M := M)
  change H * E = E * H + (2 : k) • E at hHE
  change E * F - F * E = H at hEF
  have hFE : F * E = E * F - H := by rw [← hEF]; abel
  let orbit : Fin p → M := fun i => (E ^ (i : ℕ)) data.v0
  let φ := coordinateMap k orbit
  have hbasis (i : Fin p) : (Pi.basisFun k (Fin p)) i = coordinateVector k p i := by
    ext j
    simp [coordinateVector, Pi.single_apply, eq_comm]
  have hE : ∀ v, φ (cyclicForwardEndomorphism (p := p) k data.alpha v) = E (φ v) := by
    intro v
    have hop : φ.comp (cyclicForwardEndomorphism (p := p) k data.alpha) = E.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin p))
      intro i
      rw [hbasis i]
      simp only [LinearMap.comp_apply]
      change φ (cyclicForwardEndomorphism (p := p) k data.alpha (coordinateVector k p i)) =
        E (φ (coordinateVector k p i))
      by_cases hi : (i : ℕ) + 1 < p
      · rw [cyclicForwardEndomorphism_apply_lt_last k data.alpha (i : ℕ) hi,
          coordinateMap_basis, coordinateMap_basis]
        change (E ^ ((i : ℕ) + 1)) data.v0 = E ((E ^ (i : ℕ)) data.v0)
        rw [pow_succ', Module.End.mul_apply]
      · have hitop : (i : ℕ) = p - 1 := by omega
        have hieq : i = ⟨p - 1, by omega⟩ := Fin.ext hitop
        rw [hieq, cyclicForwardEndomorphism_apply_last k data.alpha hp, map_smul,
          coordinateMap_basis, coordinateMap_basis]
        change data.alpha • data.v0 = E ((E ^ (p - 1)) data.v0)
        rw [← Module.End.mul_apply, ← pow_succ', show p - 1 + 1 = p by omega,
          data.e_pow, LinearMap.smul_apply, Module.End.one_apply]
    exact LinearMap.congr_fun hop v
  have hF : ∀ v, φ (weightedBackwardEndomorphism (p := p) k data.alpha data.lam data.q v) = F (φ v) := by
    intro v
    have hop : φ.comp (weightedBackwardEndomorphism (p := p) k data.alpha data.lam data.q) = F.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin p))
      intro i
      rw [hbasis i]
      simp only [LinearMap.comp_apply]
      change φ (weightedBackwardEndomorphism (p := p) k data.alpha data.lam data.q (coordinateVector k p i)) =
        F (φ (coordinateVector k p i))
      by_cases hi : 0 < (i : ℕ)
      · rw [weightedBackwardEndomorphism_apply_pos k data.alpha data.lam data.q (i : ℕ) hi i.isLt,
          map_smul, coordinateMap_basis, coordinateMap_basis]
        have hf := f_e_pow_succ k E F H p hFE hHE data.alpha data.lam data.q
          data.v0 data.e_pow data.f_v0 data.h_v0 (by omega) ((i : ℕ) - 1)
        rw [show (i : ℕ) - 1 + 1 = (i : ℕ) by omega] at hf
        rw [hf]
      · let z : Fin p := ⟨0, by omega⟩
        have hi0 : i = z := by
          apply Fin.ext
          dsimp [z]
          omega
        rw [hi0, weightedBackwardEndomorphism_apply_zero k data.alpha data.lam data.q,
          map_smul, coordinateMap_basis, coordinateMap_basis]
        change data.q • (E ^ (p - 1)) data.v0 = F data.v0
        exact data.f_v0.symm
    exact LinearMap.congr_fun hop v
  have hH : ∀ v, φ (parameterThirdEndomorphism (p := p) k data.lam v) = H (φ v) := by
    intro v
    have hop : φ.comp (parameterThirdEndomorphism (p := p) k data.lam) = H.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin p))
      intro i
      rw [hbasis i]
      simp only [LinearMap.comp_apply]
      change φ (parameterThirdEndomorphism (p := p) k data.lam (coordinateVector k p i)) =
        H (φ (coordinateVector k p i))
      have hh := h_e_pow k E F H hHE data.lam data.v0 data.h_v0 (i : ℕ)
      rw [coordinateMap_basis, hh]
      have hsource : parameterThirdEndomorphism (p := p) k data.lam (coordinateVector k p i) =
          (data.lam + 2 * (i : ℕ)) • coordinateVector k p i := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [parameterThirdEndomorphism, coordinateVector_apply, mul_comm]
        · simp [parameterThirdEndomorphism, coordinateVector_apply, hji]
      rw [hsource, map_smul, coordinateMap_basis]
    exact LinearMap.congr_fun hop v
  let a : ModuleParameter k p := .cyclic data.alpha data.lam data.q data.alpha_ne
  let ψ : parameterModule k a →ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M :=
    lieHomOfEFH k a φ hE hF hH
  letI : LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) :=
    isIrreducible_parameterModule k a
  have hψ0 : ψ (coordinateVector k p ⟨0, by omega⟩) ≠ 0 := by
    change φ (coordinateVector k p ⟨0, by omega⟩) ≠ 0
    rw [coordinateMap_basis]
    exact data.v0_ne
  have hinj : Function.Injective ψ := lieHom_injective_of_ne_zero k ψ hψ0
  have hsurj : Function.Surjective ψ := by
    change Function.Surjective φ
    exact coordinateMap_surjective k orbit (by simpa [orbit] using data.orbit_top)
  exact ⟨lieEquivOfBijective k ψ ⟨hinj, hsurj⟩⟩

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem restricted_tail_zero
    [FiniteDimensional k M] [LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M]
    (data : HighestNormalForm k
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)) p)
    (n : Fin p) (hlam : data.lam = (n : k)) (hbeta : data.beta = 0) :
    ((LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M
      (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)) ^ ((n : ℕ) + 1)) data.v0 = 0 := by
  classical
  have hp : 2 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
  let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
  let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
  change (F ^ ((n : ℕ) + 1)) data.v0 = 0
  by_cases hnlast : (n : ℕ) + 1 = p
  · rw [hnlast, data.f_pow, hbeta, zero_smul]
    rfl
  have hnlt : (n : ℕ) + 1 < p := by omega
  obtain ⟨hHE, hHF, hEF⟩ := target_relations (k := k) (M := M)
  change H * E = E * H + (2 : k) • E at hHE
  change H * F = F * H - (2 : k) • F at hHF
  change E * F - F * E = H at hEF
  let orbit : Fin p → M := fun i => (F ^ (i : ℕ)) data.v0
  let nz := {i : Fin p // orbit i ≠ 0}
  have hweight : Function.Injective (fun i : nz => data.lam - 2 * ((i : Fin p) : ℕ)) := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact (subWeightsPairwise k le_rfl data.lam hne) hij
  have heigen : ∀ i : nz,
      H.HasEigenvector (data.lam - 2 * ((i : Fin p) : ℕ)) (orbit i) := by
    intro i
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      exact h_f_pow k E F H hHF data.lam data.v0 data.h_v0 (i : Fin p)
    · exact i.property
  have hli : LinearIndependent k (fun i : nz => orbit i) :=
    H.eigenvectors_linearIndependent' _ hweight _ heigen
  let zfin : Fin p := ⟨0, by omega⟩
  have horbit0 : orbit zfin = data.v0 := by simp [orbit, zfin]
  have hzmem : orbit zfin ≠ 0 := horbit0.trans_ne data.v0_ne
  let z : nz := ⟨zfin, hzmem⟩
  let tail : Fin (p - ((n : ℕ) + 1)) → M := fun j =>
    orbit ⟨(n : ℕ) + 1 + (j : ℕ), by omega⟩
  let W : Submodule k M := Submodule.span k (Set.range tail)
  have hWproper : W ≠ ⊤ := by
    intro htop
    have hv0W : data.v0 ∈ W := by rw [htop]; trivial
    have hWle : W ≤ Submodule.span k ((fun i : nz => orbit i) '' {z}ᶜ) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      by_cases hjzero : tail j = 0
      · rw [hjzero]
        exact Submodule.zero_mem _
      · let tfin : Fin p := ⟨(n : ℕ) + 1 + (j : ℕ), by omega⟩
        let t : nz := ⟨tfin, by simpa [tail, tfin] using hjzero⟩
        apply Submodule.subset_span
        refine ⟨t, ?_, ?_⟩
        · intro htz
          have hval := congrArg (fun x : nz => ((x : Fin p) : ℕ)) htz
          dsimp [t, tfin, z, zfin] at hval
          omega
        · simp [t, tfin, tail]
    have hv0large : data.v0 ∈
        Submodule.span k ((fun i : nz => orbit i) '' {z}ᶜ) := hWle hv0W
    apply hli.notMem_span z
    simpa [z, horbit0] using hv0large
  let w := (F ^ ((n : ℕ) + 1)) data.v0
  by_contra hw
  have hwW : w ∈ W := by
    apply Submodule.subset_span
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [tail, orbit, w]
  have hFW : ∀ v ∈ W, F v ∈ W := by
    refine fun v hv => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span F _ ?_ hv
    rintro _ ⟨j, rfl⟩
    let r := (n : ℕ) + 1 + (j : ℕ)
    by_cases hr : r + 1 < p
    · apply Submodule.subset_span
      refine ⟨⟨(j : ℕ) + 1, by dsimp [r] at hr ⊢; omega⟩, ?_⟩
      simp only [tail, orbit]
      change (F ^ (r + 1)) data.v0 = F ((F ^ r) data.v0)
      rw [pow_succ', Module.End.mul_apply]
    · have hrp : r + 1 = p := by dsimp [r] at hr ⊢; omega
      change F ((F ^ r) data.v0) ∈ W
      rw [← Module.End.mul_apply, ← pow_succ', hrp, data.f_pow, hbeta,
        zero_smul]
      exact W.zero_mem
  have hHW : ∀ v ∈ W, H v ∈ W := by
    refine fun v hv => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span H _ ?_ hv
    rintro _ ⟨j, rfl⟩
    let r := (n : ℕ) + 1 + (j : ℕ)
    change H ((F ^ r) data.v0) ∈ W
    rw [h_f_pow k E F H hHF data.lam data.v0 data.h_v0 r]
    exact W.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hEW : ∀ v ∈ W, E v ∈ W := by
    refine fun v hv => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span E _ ?_ hv
    rintro _ ⟨j, rfl⟩
    let r := (n : ℕ) + 1 + (j : ℕ)
    have hr0 : 0 < r := by dsimp [r]; omega
    have he := e_f_pow_succ k E F H hEF hHF data.lam data.v0 data.e_v0
      data.h_v0 (r - 1)
    rw [show r - 1 + 1 = r by omega] at he
    change E ((F ^ r) data.v0) ∈ W
    rw [he]
    by_cases hj0 : (j : ℕ) = 0
    · have hcoeff : (((r : k) * (data.lam - ((r - 1 : ℕ) : k))) : k) = 0 := by
        rw [hlam]
        dsimp [r]
        rw [Nat.cast_sub (by omega : 1 ≤ (n : ℕ) + 1 + (j : ℕ))]
        push_cast
        rw [hj0]
        ring
      rw [hcoeff, zero_smul]
      exact W.zero_mem
    · apply W.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨(j : ℕ) - 1, by omega⟩, ?_⟩
      simp only [tail, orbit]
      congr 2
      dsimp [r]
      omega
  have hlie := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.lieStable_of_stable_generators W
    (fun m hm => by change E m ∈ W; exact hEW m hm)
    (fun m hm => by change F m ∈ W; exact hFW m hm)
    (fun m hm => by change H m ∈ W; exact hHW m hm)
  have htop := RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.eq_top_of_lieStable_of_exists_ne_zero W hlie ⟨w, hwW, hw⟩
  exact hWproper htop

omit [IsAlgClosed k] in
private theorem restrictedNormalForm_equiv
    [FiniteDimensional k M] [LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M]
    (data : HighestNormalForm k
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k))
      (LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)) p)
    (n : Fin p) (hlam : data.lam = (n : k)) (hbeta : data.beta = 0) :
    Nonempty (parameterModule k (.restricted n) ≃ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M) := by
  classical
  have hp : 2 < p := Fact.out
  let d := (n : ℕ) + 1
  have hd : 0 < d := by dsimp [d]; omega
  haveI : NeZero d := ⟨by omega⟩
  let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
  let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
  let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
  obtain ⟨hHE, hHF, hEF⟩ := target_relations (k := k) (M := M)
  change H * E = E * H + (2 : k) • E at hHE
  change H * F = F * H - (2 : k) • F at hHF
  change E * F - F * E = H at hEF
  have htail : (F ^ d) data.v0 = 0 := by
    simpa [d] using restricted_tail_zero k data n hlam hbeta
  let orbit : Fin d → M := fun i => (F ^ (i : ℕ)) data.v0
  have horbit_top : Submodule.span k (Set.range orbit) = ⊤ := by
    apply le_antisymm le_top
    rw [← data.orbit_top]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (F ^ (i : ℕ)) data.v0 ∈ Submodule.span k (Set.range orbit)
    by_cases hi : (i : ℕ) < d
    · apply Submodule.subset_span
      exact ⟨⟨i, hi⟩, rfl⟩
    · have hieq : (i : ℕ) = ((i : ℕ) - d) + d := by omega
      have hzero : (F ^ (i : ℕ)) data.v0 = 0 := by
        rw [hieq, pow_add, Module.End.mul_apply, htail, map_zero]
      rw [hzero]
      exact Submodule.zero_mem _
  let φ := coordinateMap k orbit
  have hbasis (i : Fin d) : (Pi.basisFun k (Fin d)) i = coordinateVector k d i := by
    ext j
    simp [coordinateVector, Pi.single_apply, eq_comm]
  have hE : ∀ v, φ (standardBackwardEndomorphism (d := d) k (n : k) v) = E (φ v) := by
    intro v
    have hop : φ.comp (standardBackwardEndomorphism (d := d) k (n : k)) = E.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin d))
      intro i
      rw [hbasis i]
      simp only [LinearMap.comp_apply]
      change φ (standardBackwardEndomorphism (d := d) k (n : k) (coordinateVector k d i)) =
        E (φ (coordinateVector k d i))
      by_cases hi : 0 < (i : ℕ)
      · rw [standardBackwardEndomorphism_apply_pos k (n : k) (i : ℕ) hi i.isLt,
          map_smul, coordinateMap_basis, coordinateMap_basis]
        have he := e_f_pow_succ k E F H hEF hHF data.lam data.v0 data.e_v0
          data.h_v0 ((i : ℕ) - 1)
        rw [show (i : ℕ) - 1 + 1 = (i : ℕ) by omega, hlam] at he
        rw [he]
        congr 1
        push_cast [Nat.cast_sub (by omega : 1 ≤ (i : ℕ))]
        ring
      · let z : Fin d := ⟨0, hd⟩
        have hi0 : i = z := by apply Fin.ext; dsimp [z]; omega
        rw [hi0]
        have hz : standardBackwardEndomorphism (d := d) k (n : k) (coordinateVector k d z) = 0 := by
          ext j
          simp only [standardBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
            Pi.zero_apply]
          split
          · rename_i hj
            have hne : (⟨(j : ℕ) + 1, hj⟩ : Fin d) ≠ z := by
              intro heq
              have hval := congrArg Fin.val heq
              dsimp [z] at hval
              omega
            rw [if_neg hne]
            ring
          · ring
        rw [hz, map_zero, coordinateMap_basis]
        simp [orbit, E, z, data.e_v0]
    exact LinearMap.congr_fun hop v
  have hF : ∀ v, φ (standardCyclicForwardEndomorphism (d := d) k 0 v) = F (φ v) := by
    intro v
    have hop : φ.comp (standardCyclicForwardEndomorphism (d := d) k 0) = F.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin d))
      intro i
      rw [hbasis i]
      simp only [LinearMap.comp_apply]
      change φ (standardCyclicForwardEndomorphism (d := d) k 0 (coordinateVector k d i)) = F (φ (coordinateVector k d i))
      by_cases hi : (i : ℕ) + 1 < d
      · rw [standardCyclicForwardEndomorphism_apply_lt_last k 0 (i : ℕ) hi,
          coordinateMap_basis, coordinateMap_basis]
        change (F ^ ((i : ℕ) + 1)) data.v0 = F ((F ^ (i : ℕ)) data.v0)
        rw [pow_succ', Module.End.mul_apply]
      · have hitop : (i : ℕ) = d - 1 := by omega
        have hieq : i = ⟨d - 1, by omega⟩ := Fin.ext hitop
        rw [hieq, standardCyclicForwardEndomorphism_apply_last k (0 : k), zero_smul, map_zero,
          coordinateMap_basis]
        change 0 = F ((F ^ (d - 1)) data.v0)
        rw [← Module.End.mul_apply, ← pow_succ', show d - 1 + 1 = d by omega,
          htail]
    exact LinearMap.congr_fun hop v
  have hH : ∀ v, φ (standardThirdEndomorphism (d := d) k (n : k) v) = H (φ v) := by
    intro v
    have hop : φ.comp (standardThirdEndomorphism (d := d) k (n : k)) = H.comp φ := by
      apply Module.Basis.ext (Pi.basisFun k (Fin d))
      intro i
      rw [hbasis i]
      simp only [LinearMap.comp_apply]
      change φ (standardThirdEndomorphism (d := d) k (n : k) (coordinateVector k d i)) =
        H (φ (coordinateVector k d i))
      have hh := h_f_pow k E F H hHF data.lam data.v0 data.h_v0 (i : ℕ)
      rw [hlam] at hh
      rw [coordinateMap_basis, hh]
      have hsource : standardThirdEndomorphism (d := d) k (n : k) (coordinateVector k d i) =
          ((n : k) - 2 * (i : ℕ)) • coordinateVector k d i := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [standardThirdEndomorphism, coordinateVector_apply, mul_comm]
        · simp [standardThirdEndomorphism, coordinateVector_apply, hji]
      rw [hsource, map_smul, coordinateMap_basis]
    exact LinearMap.congr_fun hop v
  let a : ModuleParameter k p := .restricted n
  let ψ : parameterModule k a →ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M :=
    lieHomOfEFH k a φ hE hF hH
  letI : LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k a) :=
    isIrreducible_parameterModule k a
  have hψ0 : ψ (coordinateVector k d ⟨0, hd⟩) ≠ 0 := by
    change φ (coordinateVector k d ⟨0, hd⟩) ≠ 0
    rw [coordinateMap_basis]
    exact data.v0_ne
  have hinj : Function.Injective ψ := lieHom_injective_of_ne_zero k ψ hψ0
  have hsurj : Function.Surjective ψ := by
    change Function.Surjective φ
    exact coordinateMap_surjective k orbit horbit_top
  exact ⟨lieEquivOfBijective k ψ ⟨hinj, hsurj⟩⟩

end Intertwiners

                        

                                                                                    
                                      
/-- Every finite-dimensional irreducible module for the designated Lie algebra over the given field is equivalent to a parameter module. -/
@[source_ref "Chapter2/Problem2.16.4" (role := primary)]
theorem exists_parameterModule_equiv [IsAlgClosed k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Fact (2 < p)]
    (M : Type u) [AddCommGroup M] [Module k M]
    [LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M] [LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) M] :
    ∃ a : ModuleParameter k p,
      Nonempty (parameterModule k a ≃ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ M) := by
  classical
  have hp : 2 < p := Fact.out
  obtain ⟨form⟩ := exists_normalForm k p hp M
  cases form with
  | cyclic data =>
      exact ⟨.cyclic data.alpha data.lam data.q data.alpha_ne,
        cyclicNormalForm_equiv k data⟩
  | highest data =>
      by_cases hsimple : data.beta ≠ 0 ∨ data.lam ^ p ≠ data.lam
      · exact ⟨.highest data.beta data.lam hsimple,
          highestNormalForm_equiv k data hsimple⟩
      · push Not at hsimple
        have hmem : data.lam ∈ (⊥ : Subfield k) :=
          (Subfield.mem_bot_iff_pow_eq_self k p).mpr hsimple.2
        obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p k).mp hmem
        haveI : NeZero p := ⟨by omega⟩
        let z : ZMod p := m
        let n : Fin p := ⟨z.val, z.val_lt⟩
        have hzcast : (ZMod.cast z : k) = data.lam := by
          dsimp [z]
          rw [ZMod.cast_intCast']
          exact hm
        have hlam : data.lam = (n : k) := by
          symm
          change (z.val : k) = data.lam
          rw [ZMod.natCast_val]
          exact hzcast
        exact ⟨.restricted n,
          restrictedNormalForm_equiv k data n hlam hsimple.1⟩

                               

namespace ModuleParameter

                                  
/-- The first field-valued scalar associated with a module parameter. -/
def firstScalar {p : ℕ} : ModuleParameter k p → k
  | .restricted _ | .highest _ _ _ => 0
  | .cyclic alpha _ _ _ => alpha

                                                                                        
                                                        
/-- The second field-valued scalar associated with a module parameter. -/
def secondScalar {p : ℕ} : ModuleParameter k p → k
  | .restricted _ => 0
  | .highest beta _ _ => beta
  | .cyclic _ _ _ _ => 0

                                                                

                                                                                     
                                                                                      
                                                                                         
                                                                                   
                                                                                       
/-- A designated predicate on two module parameters used in the witness nonemptiness criterion. -/
def parameterEquivCondition {p : ℕ} : ModuleParameter k p → ModuleParameter k p → Prop
  | .restricted n, .restricted m => n = m
  | .highest beta lam _, .highest beta' mu _ =>
      beta = beta' ∧ ∃ j : Fin p,
        lam = mu - 2 * (j : ℕ) ∧
          (j : k) * (mu - (j : k) + 1) = 0
  | .cyclic alpha lam q _, .cyclic alpha' mu q' _ =>
      alpha = alpha' ∧ ∃ j : Fin p,
        lam = mu + 2 * (j : ℕ) ∧
          if (j : ℕ) = 0 then q = q'
          else recurrenceCoefficient k alpha mu q' (j : ℕ) = alpha * q
  | _, _ => False

end ModuleParameter

section OperatorInvariants

variable {p : ℕ} [Fact p.Prime] [CharP k p] [Fact (2 < p)]

private theorem vermaF_pow_dimension {d : ℕ} [NeZero d] (beta : k) :
    standardCyclicForwardEndomorphism (d := d) k beta ^ d = beta • 1 := by
  classical
  let F := standardCyclicForwardEndomorphism (d := d) k beta
  have hpath : ∀ (i r : ℕ) (h : i + r < d),
      (F ^ r) (coordinateVector k d ⟨i, by omega⟩) = coordinateVector k d ⟨i + r, h⟩ := by
    intro i r h
    induction r with
    | zero =>
        simp only [pow_zero, Module.End.one_apply, Nat.add_zero]
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply, ih (by omega)]
        exact standardCyclicForwardEndomorphism_apply_lt_last k beta (i + r) (by omega)
  apply Module.Basis.ext (Pi.basisFun k (Fin d))
  intro i
  rw [show (Pi.basisFun k (Fin d)) i = coordinateVector k d i by
    ext j
    simp [coordinateVector, Pi.single_apply, eq_comm]]
  simp only [LinearMap.smul_apply, Module.End.one_apply]
  by_cases hi0 : (i : ℕ) = 0
  · have hieq : i = ⟨0, NeZero.pos d⟩ := Fin.ext hi0
    rw [hieq]
    have hpow : F ^ d = F * F ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [show standardCyclicForwardEndomorphism (d := d) k beta = F from rfl, hpow, Module.End.mul_apply,
      hpath 0 (d - 1) (by omega)]
    have hlast : (⟨0 + (d - 1), by omega⟩ : Fin d) = ⟨d - 1, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hlast, standardCyclicForwardEndomorphism_apply_last k beta]
  · have hi : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
    have hwrap : (F ^ (d - (i : ℕ))) (coordinateVector k d i) =
        beta • coordinateVector k d ⟨0, NeZero.pos d⟩ := by
      have hpow : F ^ (d - (i : ℕ)) = F * F ^ (d - (i : ℕ) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hpow, Module.End.mul_apply,
        hpath (i : ℕ) (d - (i : ℕ) - 1) (by omega)]
      have hlast : (⟨(i : ℕ) + (d - (i : ℕ) - 1), by omega⟩ : Fin d) =
          ⟨d - 1, by omega⟩ := by
        apply Fin.ext
        change (i : ℕ) + (d - (i : ℕ) - 1) = d - 1
        omega
      rw [hlast, standardCyclicForwardEndomorphism_apply_last k beta]
    have hpow : F ^ d = F ^ (i : ℕ) * F ^ (d - (i : ℕ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [show standardCyclicForwardEndomorphism (d := d) k beta = F from rfl, hpow,
      Module.End.mul_apply, hwrap, map_smul, hpath 0 (i : ℕ) (by omega)]
    congr 2
    apply Fin.ext
    simp

omit [CharP k p] in
private theorem cyclicE_pow_char (alpha : k) :
    cyclicForwardEndomorphism (p := p) k alpha ^ p = alpha • 1 := by
  classical
  haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
  let E := cyclicForwardEndomorphism (p := p) k alpha
  have hpath : ∀ (i r : ℕ) (h : i + r < p),
      (E ^ r) (coordinateVector k p ⟨i, by omega⟩) = coordinateVector k p ⟨i + r, h⟩ := by
    intro i r h
    induction r with
    | zero => simp only [pow_zero, Module.End.one_apply, Nat.add_zero]
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply, ih (by omega)]
        exact cyclicForwardEndomorphism_apply_lt_last k alpha (i + r) (by omega)
  apply Module.Basis.ext (Pi.basisFun k (Fin p))
  intro i
  rw [show (Pi.basisFun k (Fin p)) i = coordinateVector k p i by
    ext j
    simp [coordinateVector, Pi.single_apply, eq_comm]]
  simp only [LinearMap.smul_apply, Module.End.one_apply]
  by_cases hi0 : (i : ℕ) = 0
  · have hieq : i = ⟨0, by have hp : 2 < p := Fact.out; omega⟩ := Fin.ext hi0
    rw [hieq]
    have hpow : E ^ p = E * E ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      have hp : 2 < p := Fact.out
      omega
    rw [show cyclicForwardEndomorphism (p := p) k alpha = E from rfl, hpow, Module.End.mul_apply,
      hpath 0 (p - 1) (by have hp : 2 < p := Fact.out; omega)]
    have hlast : (⟨0 + (p - 1), by have hp : 2 < p := Fact.out; omega⟩ : Fin p) =
        ⟨p - 1, by have hp : 2 < p := Fact.out; omega⟩ := by
      apply Fin.ext
      simp
    rw [hlast, cyclicForwardEndomorphism_apply_last k alpha Fact.out]
  · have hi : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
    have hwrap : (E ^ (p - (i : ℕ))) (coordinateVector k p i) =
        alpha • coordinateVector k p ⟨0, by have hp : 2 < p := Fact.out; omega⟩ := by
      have hpow : E ^ (p - (i : ℕ)) = E * E ^ (p - (i : ℕ) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hpow, Module.End.mul_apply,
        hpath (i : ℕ) (p - (i : ℕ) - 1) (by omega)]
      have hlast : (⟨(i : ℕ) + (p - (i : ℕ) - 1), by omega⟩ : Fin p) =
          ⟨p - 1, by omega⟩ := by
        apply Fin.ext
        change (i : ℕ) + (p - (i : ℕ) - 1) = p - 1
        omega
      rw [hlast, cyclicForwardEndomorphism_apply_last k alpha Fact.out]
    have hpow : E ^ p = E ^ (i : ℕ) * E ^ (p - (i : ℕ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [show cyclicForwardEndomorphism (p := p) k alpha = E from rfl, hpow,
      Module.End.mul_apply, hwrap, map_smul, hpath 0 (i : ℕ) (by omega)]
    congr 2
    apply Fin.ext
    simp

private theorem vermaE_pow_dimension_zero {d : ℕ} [NeZero d] (lam : k) :
    standardBackwardEndomorphism (d := d) k lam ^ d = 0 := by
  classical
  let E := standardBackwardEndomorphism (d := d) k lam
  have hzero : E (coordinateVector k d ⟨0, NeZero.pos d⟩) = 0 := by
    ext j
    simp only [E, standardBackwardEndomorphism, LinearMap.coe_mk, AddHom.coe_mk, coordinateVector_apply,
      Pi.zero_apply]
    split
    · rename_i hj
      have hne : (⟨(j : ℕ) + 1, hj⟩ : Fin d) ≠ ⟨0, NeZero.pos d⟩ := by
        intro heq
        have hval := congrArg Fin.val heq
        simp at hval
      rw [if_neg hne]
      ring
    · ring
  have hv : ∀ (i : ℕ) (hi : i < d),
      (E ^ (i + 1)) (coordinateVector k d ⟨i, hi⟩) = 0 := by
    intro i hi
    induction i with
    | zero => simpa [E] using hzero
    | succ i ih =>
        have hpow : E ^ (i + 1 + 1) = E ^ (i + 1) * E := by rw [pow_succ]
        rw [hpow, Module.End.mul_apply,
          standardBackwardEndomorphism_apply_pos k lam (i + 1) (by omega) hi, map_smul]
        have heq : (⟨i + 1 - 1, by omega⟩ : Fin d) = ⟨i, by omega⟩ := by
          apply Fin.ext
          simp
        rw [heq, ih (by omega), smul_zero]
  apply Module.Basis.ext (Pi.basisFun k (Fin d))
  intro i
  rw [show (Pi.basisFun k (Fin d)) i = coordinateVector k d i by
    ext j
    simp [coordinateVector, Pi.single_apply, eq_comm]]
  simp only [LinearMap.zero_apply]
  have hpow : E ^ d = E ^ (d - ((i : ℕ) + 1)) * E ^ ((i : ℕ) + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [show standardBackwardEndomorphism (d := d) k lam = E from rfl, hpow, Module.End.mul_apply,
    hv (i : ℕ) i.isLt, map_zero]

private theorem parameter_e_pow (a : ModuleParameter k p) :
    (parameterLieEndomorphismTriple k a).first ^ p = a.firstScalar • 1 := by
  cases a with
  | restricted n =>
      have hd : (n : ℕ) + 1 ≤ p := by omega
      haveI : NeZero ((n : ℕ) + 1) := ⟨by omega⟩
      have hzero := vermaE_pow_dimension_zero (d := (n : ℕ) + 1) k (n : k)
      calc
        (parameterLieEndomorphismTriple k (.restricted n)).first ^ p =
            (parameterLieEndomorphismTriple k (.restricted n)).first ^ ((n : ℕ) + 1) *
              (parameterLieEndomorphismTriple k (.restricted n)).first ^ (p - ((n : ℕ) + 1)) := by
                rw [← pow_add]
                congr 1
                omega
        _ = 0 := by
          change standardBackwardEndomorphism (d := (n : ℕ) + 1) k (n : k) ^ ((n : ℕ) + 1) * _ = 0
          rw [hzero, zero_mul]
        _ = (ModuleParameter.restricted n : ModuleParameter k p).firstScalar • 1 := by
          simp [ModuleParameter.firstScalar]
  | highest beta lam simple =>
      haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
      change standardBackwardEndomorphism (d := p) k lam ^ p = (0 : k) • 1
      rw [vermaE_pow_dimension_zero, zero_smul]
  | cyclic alpha lam q alpha_ne =>
      change cyclicForwardEndomorphism (p := p) k alpha ^ p = alpha • 1
      exact cyclicE_pow_char k alpha

omit [Fact p.Prime] in
private theorem parameter_f_pow_of_eScalar_eq_zero (a : ModuleParameter k p)
    (ha : a.firstScalar = 0) :
    (parameterLieEndomorphismTriple k a).second ^ p = a.secondScalar • 1 := by
  cases a with
  | restricted n =>
      haveI : NeZero ((n : ℕ) + 1) := ⟨by omega⟩
      have hzero := vermaF_pow_dimension (d := (n : ℕ) + 1) k 0
      calc
        (parameterLieEndomorphismTriple k (.restricted n)).second ^ p =
            (parameterLieEndomorphismTriple k (.restricted n)).second ^ ((n : ℕ) + 1) *
              (parameterLieEndomorphismTriple k (.restricted n)).second ^ (p - ((n : ℕ) + 1)) := by
                rw [← pow_add]
                congr 1
                omega
        _ = 0 := by
          change standardCyclicForwardEndomorphism (d := (n : ℕ) + 1) k 0 ^ ((n : ℕ) + 1) * _ = 0
          rw [hzero, zero_smul, zero_mul]
        _ = (ModuleParameter.restricted n : ModuleParameter k p).secondScalar • 1 := by
          simp [ModuleParameter.secondScalar]
  | highest beta lam simple =>
      haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
      change standardCyclicForwardEndomorphism (d := p) k beta ^ p = beta • 1
      exact vermaF_pow_dimension k beta
  | cyclic alpha lam q alpha_ne =>
      exact (alpha_ne ha).elim

omit [CharP k p] in
private theorem vermaF_orbit_top (beta : k) (j : Fin p)
    (hwrap : (j : ℕ) = 0 ∨ beta ≠ 0) :
    Submodule.span k (Set.range fun i : Fin p =>
      (standardCyclicForwardEndomorphism (d := p) k beta ^ (i : ℕ)) (coordinateVector k p j)) = ⊤ := by
  classical
  haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
  let F := standardCyclicForwardEndomorphism (d := p) k beta
  let orbit : Fin p → (Fin p → k) := fun i => (F ^ (i : ℕ)) (coordinateVector k p j)
  let N := Submodule.span k (Set.range orbit)
  have hj : coordinateVector k p j ∈ N := by
    have h := Submodule.subset_span (R := k) (s := Set.range orbit)
      (show orbit ⟨0, by have hp : 2 < p := Fact.out; omega⟩ ∈ Set.range orbit from
        ⟨⟨0, by have hp : 2 < p := Fact.out; omega⟩, rfl⟩)
    simpa [orbit] using h
  have hF : ∀ v ∈ N, F v ∈ N := by
    refine fun v hv => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span F _ ?_ hv
    rintro _ ⟨i, rfl⟩
    by_cases hi : (i : ℕ) + 1 < p
    · apply Submodule.subset_span
      refine ⟨⟨(i : ℕ) + 1, hi⟩, ?_⟩
      simp only [orbit]
      rw [pow_succ', Module.End.mul_apply]
    · have hip : (i : ℕ) + 1 = p := by omega
      change F ((F ^ (i : ℕ)) (coordinateVector k p j)) ∈ N
      rw [← Module.End.mul_apply, ← pow_succ', hip,
        show F = standardCyclicForwardEndomorphism (d := p) k beta from rfl, vermaF_pow_dimension,
        LinearMap.smul_apply, Module.End.one_apply]
      exact N.smul_mem beta hj
  have h0 : coordinateVector k p ⟨0, by have hp : 2 < p := Fact.out; omega⟩ ∈ N := by
    rcases hwrap with hj0 | hbeta
    · have : j = ⟨0, by have hp : 2 < p := Fact.out; omega⟩ := Fin.ext hj0
      simpa [this] using hj
    · exact zeroBasisOfCyclicVermaF k beta hbeta N hF hj
  exact eqTopOfAllBasis k N (allBasisOfVermaF k beta N hF h0)

omit [CharP k p] in
private theorem cyclicE_orbit_top (alpha : k) (halpha : alpha ≠ 0) (j : Fin p) :
    Submodule.span k (Set.range fun i : Fin p =>
      (cyclicForwardEndomorphism (p := p) k alpha ^ (i : ℕ)) (coordinateVector k p j)) = ⊤ := by
  classical
  haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
  let E := cyclicForwardEndomorphism (p := p) k alpha
  let orbit : Fin p → (Fin p → k) := fun i => (E ^ (i : ℕ)) (coordinateVector k p j)
  let N := Submodule.span k (Set.range orbit)
  have hj : coordinateVector k p j ∈ N := by
    have h := Submodule.subset_span (R := k) (s := Set.range orbit)
      (show orbit ⟨0, by have hp : 2 < p := Fact.out; omega⟩ ∈ Set.range orbit from
        ⟨⟨0, by have hp : 2 < p := Fact.out; omega⟩, rfl⟩)
    simpa [orbit] using h
  have hE : ∀ v ∈ N, E v ∈ N := by
    refine fun v hv => RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.map_mem_span_of_forall_mem_span E _ ?_ hv
    rintro _ ⟨i, rfl⟩
    by_cases hi : (i : ℕ) + 1 < p
    · apply Submodule.subset_span
      refine ⟨⟨(i : ℕ) + 1, hi⟩, ?_⟩
      simp only [orbit]
      rw [pow_succ', Module.End.mul_apply]
    · have hip : (i : ℕ) + 1 = p := by omega
      change E ((E ^ (i : ℕ)) (coordinateVector k p j)) ∈ N
      rw [← Module.End.mul_apply, ← pow_succ', hip,
        show E = cyclicForwardEndomorphism (p := p) k alpha from rfl, cyclicE_pow_char,
        LinearMap.smul_apply, Module.End.one_apply]
      exact N.smul_mem alpha hj
  have h0 := zeroBasisOfCyclicE k alpha halpha N hE hj
  have hall : ∀ i, coordinateVector k p i ∈ N := by
    intro i
    suffices ∀ (m : ℕ) (hm : m < p), coordinateVector k p ⟨m, hm⟩ ∈ N from this i i.isLt
    intro m hm
    induction m with
    | zero => exact h0
    | succ m ih =>
        have himage := hE _ (ih (by omega))
        rwa [show E = cyclicForwardEndomorphism (p := p) k alpha from rfl,
          cyclicForwardEndomorphism_apply_lt_last k alpha m hm] at himage
  exact eqTopOfAllBasis k N hall

omit [CharP k p] in
private theorem cyclicE_pow_pred_basis (alpha : k) (j : Fin p) :
    (cyclicForwardEndomorphism (p := p) k alpha ^ (p - 1)) (coordinateVector k p j) =
      if (j : ℕ) = 0 then coordinateVector k p ⟨p - 1, by have hp : 2 < p := Fact.out; omega⟩
      else alpha • coordinateVector k p ⟨(j : ℕ) - 1, by omega⟩ := by
  classical
  have hp : 2 < p := Fact.out
  haveI : NeZero p := ⟨by omega⟩
  let E := cyclicForwardEndomorphism (p := p) k alpha
  have hpath : ∀ (i r : ℕ) (h : i + r < p),
      (E ^ r) (coordinateVector k p ⟨i, by omega⟩) = coordinateVector k p ⟨i + r, h⟩ := by
    intro i r h
    induction r with
    | zero => simp
    | succ r ih =>
        rw [pow_succ', Module.End.mul_apply, ih (by omega)]
        exact cyclicForwardEndomorphism_apply_lt_last k alpha (i + r) (by omega)
  split
  · rename_i hj0
    have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hj]
    simpa using hpath 0 (p - 1) (by omega)
  · rename_i hj0
    have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj0
    have hwrap : (E ^ (p - (j : ℕ))) (coordinateVector k p j) =
        alpha • coordinateVector k p ⟨0, by omega⟩ := by
      have hpow : E ^ (p - (j : ℕ)) = E * E ^ (p - (j : ℕ) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hpow, Module.End.mul_apply,
        hpath (j : ℕ) (p - (j : ℕ) - 1) (by omega)]
      have hlast : (⟨(j : ℕ) + (p - (j : ℕ) - 1), by omega⟩ : Fin p) =
          ⟨p - 1, by omega⟩ := by
        apply Fin.ext
        change (j : ℕ) + (p - (j : ℕ) - 1) = p - 1
        omega
      rw [hlast, show E = cyclicForwardEndomorphism (p := p) k alpha from rfl,
        cyclicForwardEndomorphism_apply_last k alpha hp]
    have hpow : E ^ (p - 1) = E ^ ((j : ℕ) - 1) * E ^ (p - (j : ℕ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [show cyclicForwardEndomorphism (p := p) k alpha = E from rfl, hpow,
      Module.End.mul_apply, hwrap, map_smul,
      hpath 0 ((j : ℕ) - 1) (by omega)]
    congr 2
    apply Fin.ext
    simp

end OperatorInvariants

section ClassificationAPI

variable {p : ℕ} [Fact p.Prime] [CharP k p] [Fact (2 < p)] [IsAlgClosed k]

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_map_E {a b : ModuleParameter k p} (e : parameterEquivWitness k a b)
    (v : parameterModule k a) :
    e ((parameterLieEndomorphismTriple k a).first v) = (parameterLieEndomorphismTriple k b).first (e v) := by
  have h := e.toLieModuleHom.map_lie (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) v
  change e (parameterModuleLieHom k a (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) v) =
    parameterModuleLieHom k b (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) (e v) at h
  simpa only [parameterModuleLieHom_firstElement] using h

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_map_F {a b : ModuleParameter k p} (e : parameterEquivWitness k a b)
    (v : parameterModule k a) :
    e ((parameterLieEndomorphismTriple k a).second v) = (parameterLieEndomorphismTriple k b).second (e v) := by
  have h := e.toLieModuleHom.map_lie (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) v
  change e (parameterModuleLieHom k a (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) v) =
    parameterModuleLieHom k b (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) (e v) at h
  simpa only [parameterModuleLieHom_secondElement] using h

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_map_H {a b : ModuleParameter k p} (e : parameterEquivWitness k a b)
    (v : parameterModule k a) :
    e ((parameterLieEndomorphismTriple k a).third v) = (parameterLieEndomorphismTriple k b).third (e v) := by
  have h := e.toLieModuleHom.map_lie (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) v
  change e (parameterModuleLieHom k a (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) v) =
    parameterModuleLieHom k b (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) (e v) at h
  simpa only [parameterModuleLieHom_thirdElement] using h

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_map_E_pow {a b : ModuleParameter k p} (e : parameterEquivWitness k a b) :
    ∀ (r : ℕ) (v : parameterModule k a),
      e (((parameterLieEndomorphismTriple k a).first ^ r) v) = ((parameterLieEndomorphismTriple k b).first ^ r) (e v) := by
  intro r v
  induction r with
  | zero => simp
  | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [familyEquiv_map_E k e, ih]

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_map_F_pow {a b : ModuleParameter k p} (e : parameterEquivWitness k a b) :
    ∀ (r : ℕ) (v : parameterModule k a),
      e (((parameterLieEndomorphismTriple k a).second ^ r) v) = ((parameterLieEndomorphismTriple k b).second ^ r) (e v) := by
  intro r v
  induction r with
  | zero => simp
  | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply]
      rw [familyEquiv_map_F k e, ih]

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_dimension_eq {a b : ModuleParameter k p} (e : parameterEquivWitness k a b) :
    a.dimension = b.dimension := by
  simpa only [finrank_parameterModule] using e.toLinearEquiv.finrank_eq

omit [IsAlgClosed k] in
private theorem familyEquiv_eScalar_eq {a b : ModuleParameter k p} (e : parameterEquivWitness k a b) :
    a.firstScalar = b.firstScalar := by
  have hp : 2 < p := Fact.out
  have hpos : 0 < a.dimension := by cases a <;> simp [ModuleParameter.dimension] <;> omega
  let z : Fin a.dimension := ⟨0, hpos⟩
  let v := coordinateVector k a.dimension z
  have hv : v ≠ 0 := by
    intro hz
    have := congrFun hz z
    simp [v, coordinateVector_apply] at this
  have h := familyEquiv_map_E_pow k e p v
  rw [parameter_e_pow k a, parameter_e_pow k b,
    LinearMap.smul_apply, Module.End.one_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_smul] at h
  have hev : e v ≠ 0 := by simpa using e.injective.ne hv
  exact smul_left_injective k hev h

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem familyEquiv_fScalar_eq_of_eScalar_eq_zero
    {a b : ModuleParameter k p} (e : parameterEquivWitness k a b)
    (ha : a.firstScalar = 0) (hb : b.firstScalar = 0) : a.secondScalar = b.secondScalar := by
  have hp : 2 < p := Fact.out
  have hpos : 0 < a.dimension := by cases a <;> simp [ModuleParameter.dimension] <;> omega
  let z : Fin a.dimension := ⟨0, hpos⟩
  let v := coordinateVector k a.dimension z
  have hv : v ≠ 0 := by
    intro hz
    have := congrFun hz z
    simp [v, coordinateVector_apply] at this
  have h := familyEquiv_map_F_pow k e p v
  rw [parameter_f_pow_of_eScalar_eq_zero k a ha,
    parameter_f_pow_of_eScalar_eq_zero k b hb,
    LinearMap.smul_apply, Module.End.one_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_smul] at h
  have hev : e v ≠ 0 := by simpa using e.injective.ne hv
  exact smul_left_injective k hev h

omit [IsAlgClosed k] in
private theorem diagonal_eigenvector_eq_smul_basis {d : ℕ}
    (weight : Fin d → k) (hweight : Pairwise fun i j => weight i ≠ weight j)
    (H : Module.End k (Fin d → k))
    (hdiag : ∀ v i, H v i = weight i * v i)
    {lam : k} {w : Fin d → k} (hw : w ≠ 0) (heigen : H w = lam • w) :
    ∃ i : Fin d, lam = weight i ∧ w = w i • coordinateVector k d i ∧ w i ≠ 0 := by
  classical
  have hex : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    exact h i
  obtain ⟨i, hwi⟩ := hex
  have hi := congrFun heigen i
  rw [hdiag] at hi
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  have hlam : lam = weight i := by
    symm
    exact mul_right_cancel₀ hwi hi
  refine ⟨i, hlam, ?_, hwi⟩
  ext j
  simp only [Pi.smul_apply, coordinateVector_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst j
    simp
  · have hj := congrFun heigen j
    rw [hdiag] at hj
    simp only [Pi.smul_apply, smul_eq_mul] at hj
    have hwj : w j = 0 := by
      by_contra hwj
      have hjweight : weight j = lam := mul_right_cancel₀ hwj hj
      exact hweight hji (hjweight.trans hlam)
    simp [hji, hwj]

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem verma_highest_eigenvector_index (mu lam : k) (w : Fin p → k)
    (hw : w ≠ 0) (heigen : standardThirdEndomorphism (d := p) k mu w = lam • w)
    (hkilled : standardBackwardEndomorphism (d := p) k mu w = 0) :
    ∃ j : Fin p, lam = mu - 2 * (j : ℕ) ∧
      (j : k) * (mu - (j : k) + 1) = 0 := by
  classical
  haveI : NeZero p := ⟨by have hp : 2 < p := Fact.out; omega⟩
  obtain ⟨j, hlam, hshape, hwj⟩ := diagonal_eigenvector_eq_smul_basis k
    (fun i : Fin p => mu - 2 * (i : ℕ)) (subWeightsPairwise k le_rfl mu)
    (standardThirdEndomorphism (d := p) k mu) (by intro v i; rfl) hw heigen
  refine ⟨j, hlam, ?_⟩
  by_cases hj0 : (j : ℕ) = 0
  · simp [hj0]
  · rw [hshape, map_smul,
      standardBackwardEndomorphism_apply_pos k mu (j : ℕ) (Nat.pos_of_ne_zero hj0) j.isLt,
      smul_smul] at hkilled
    have hcoord := congrFun hkilled ⟨(j : ℕ) - 1, by omega⟩
    simp only [Pi.smul_apply, coordinateVector_apply, if_true, Pi.zero_apply, smul_eq_mul,
      mul_one] at hcoord
    have hproduct : w j * ((j : k) * (mu - (j : k) + 1)) = 0 := by
      simpa only [mul_assoc] using hcoord
    exact (mul_eq_zero.mp hproduct).resolve_left hwj

omit [Fact p.Prime] [IsAlgClosed k] in
private theorem cyclic_eigenvector_index (mu lam : k) (w : Fin p → k)
    (hw : w ≠ 0) (heigen : parameterThirdEndomorphism (p := p) k mu w = lam • w) :
    ∃ j : Fin p, lam = mu + 2 * (j : ℕ) ∧
      w = w j • coordinateVector k p j ∧ w j ≠ 0 := by
  exact diagonal_eigenvector_eq_smul_basis k
    (fun i : Fin p => mu + 2 * (i : ℕ)) (addWeightsPairwise k mu)
    (parameterThirdEndomorphism (p := p) k mu) (by intro v i; rfl) hw heigen

omit [IsAlgClosed k] in
private theorem sameInvariant_equiv (a b : ModuleParameter k p)
    (h : ModuleParameter.parameterEquivCondition k a b) : Nonempty (parameterEquivWitness k a b) := by
  classical
  have hp : 2 < p := Fact.out
  cases a with
  | restricted n =>
      cases b with
      | restricted m =>
          change n = m at h
          subst m
          exact ⟨LieModuleEquiv.refl⟩
      | highest beta mu simple => exact h.elim
      | cyclic alpha mu q halpha => exact h.elim
  | highest beta lam simple =>
      cases b with
      | restricted m => exact h.elim
      | highest beta' mu simple' =>
          change beta = beta' ∧ ∃ j : Fin p,
            lam = mu - 2 * (j : ℕ) ∧
              (j : k) * (mu - (j : k) + 1) = 0 at h
          obtain ⟨hbeta, j, hlam, hkill⟩ := h
          subst beta'
          haveI : NeZero p := ⟨by omega⟩
          let target : ModuleParameter k p := .highest beta mu simple'
          letI : LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target) :=
            lieRingModule_parameterModule k target
          letI : LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target) :=
            lieModule_parameterModule k target
          let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target)
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
          let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target)
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
          let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target)
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
          have hEdef : E = standardBackwardEndomorphism (d := p) k mu := by
            change parameterModuleLieHom k target (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) = _
            rw [parameterModuleLieHom_firstElement]
            rfl
          have hFdef : F = standardCyclicForwardEndomorphism (d := p) k beta := by
            change parameterModuleLieHom k target (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) = _
            rw [parameterModuleLieHom_secondElement]
            rfl
          have hHdef : H = standardThirdEndomorphism (d := p) k mu := by
            change parameterModuleLieHom k target (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) = _
            rw [parameterModuleLieHom_thirdElement]
            rfl
          have hv0 : coordinateVector k p j ≠ 0 := by
            intro hz
            have := congrFun hz j
            simp [coordinateVector_apply] at this
          have he : E (coordinateVector k p j) = 0 := by
            rw [hEdef]
            change standardBackwardEndomorphism (d := p) k mu (coordinateVector k p j) = 0
            by_cases hj0 : (j : ℕ) = 0
            · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
              rw [hj]
              ext i
              simp [standardBackwardEndomorphism, coordinateVector_apply]
            · rw [standardBackwardEndomorphism_apply_pos k mu (j : ℕ) (Nat.pos_of_ne_zero hj0) j.isLt,
                hkill, zero_smul]
          have hh : H (coordinateVector k p j) = lam • coordinateVector k p j := by
            rw [hHdef]
            change standardThirdEndomorphism (d := p) k mu (coordinateVector k p j) = lam • coordinateVector k p j
            ext i
            by_cases hij : i = j
            · subst i
              simp [standardThirdEndomorphism, coordinateVector_apply, hlam]
            · simp [standardThirdEndomorphism, coordinateVector_apply, hij]
          have hf : F ^ p = beta • 1 := by
            rw [hFdef]
            change standardCyclicForwardEndomorphism (d := p) k beta ^ p = beta • 1
            exact vermaF_pow_dimension k beta
          have hwrap : (j : ℕ) = 0 ∨ beta ≠ 0 := by
            by_cases hj0 : (j : ℕ) = 0
            · exact Or.inl hj0
            · right
              rcases simple' with hbeta | hmu
              · exact hbeta
              · exfalso
                apply hmu
                have hjcast : (j : k) ≠ 0 :=
                  natCastNeZeroLt k (Nat.pos_of_ne_zero hj0) j.isLt
                have hroot : mu - (j : k) + 1 = 0 :=
                  (mul_eq_zero.mp hkill).resolve_left hjcast
                have hmucast : mu = ((j : ℕ) - 1 : ℕ) := by
                  rw [Nat.cast_sub (by omega : 1 ≤ (j : ℕ))]
                  push_cast
                  linear_combination hroot
                rw [hmucast]
                exact (Subfield.mem_bot_iff_pow_eq_self k p).mp (natCast_mem _ _)
          have horbit : Submodule.span k (Set.range fun i : Fin p =>
              (F ^ (i : ℕ)) (coordinateVector k p j)) = ⊤ := by
            rw [hFdef]
            change Submodule.span k (Set.range fun i : Fin p =>
              (standardCyclicForwardEndomorphism (d := p) k beta ^ (i : ℕ)) (coordinateVector k p j)) = ⊤
            exact vermaF_orbit_top k beta j hwrap
          let data : HighestNormalForm k E F H p :=
            { beta := beta
              lam := lam
              v0 := coordinateVector k p j
              v0_ne := hv0
              e_v0 := he
              h_v0 := hh
              f_pow := hf
              orbit_top := horbit }
          simpa [target, data] using highestNormalForm_equiv k data simple
      | cyclic alpha mu q halpha => exact h.elim
  | cyclic alpha lam q halpha =>
      cases b with
      | restricted m => exact h.elim
      | highest beta mu simple => exact h.elim
      | cyclic alpha' mu q' halpha' =>
          change alpha = alpha' ∧ ∃ j : Fin p,
            lam = mu + 2 * (j : ℕ) ∧
              (if (j : ℕ) = 0 then q = q'
              else recurrenceCoefficient k alpha mu q' (j : ℕ) = alpha * q) at h
          obtain ⟨halphaeq, j, hlam, hq⟩ := h
          subst alpha'
          haveI : NeZero p := ⟨by omega⟩
          let target : ModuleParameter k p := .cyclic alpha mu q' halpha'
          letI : LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target) :=
            lieRingModule_parameterModule k target
          letI : LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target) :=
            lieModule_parameterModule k target
          let E := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target)
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k)
          let F := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target)
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k)
          let H := LieModule.toEnd k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) (parameterModule k target)
            (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k)
          have hEdef : E = cyclicForwardEndomorphism (p := p) k alpha := by
            change parameterModuleLieHom k target (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.raisingElement k) = _
            rw [parameterModuleLieHom_firstElement]
            rfl
          have hFdef : F = weightedBackwardEndomorphism (p := p) k alpha mu q' := by
            change parameterModuleLieHom k target (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.loweringElement k) = _
            rw [parameterModuleLieHom_secondElement]
            rfl
          have hHdef : H = parameterThirdEndomorphism (p := p) k mu := by
            change parameterModuleLieHom k target (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.weightElement k) = _
            rw [parameterModuleLieHom_thirdElement]
            rfl
          have hv0 : coordinateVector k p j ≠ 0 := by
            intro hz
            have := congrFun hz j
            simp [coordinateVector_apply] at this
          have hep : E ^ p = alpha • 1 := by
            rw [hEdef]
            change cyclicForwardEndomorphism (p := p) k alpha ^ p = alpha • 1
            exact cyclicE_pow_char k alpha
          have hh : H (coordinateVector k p j) = lam • coordinateVector k p j := by
            rw [hHdef]
            change parameterThirdEndomorphism (p := p) k mu (coordinateVector k p j) = lam • coordinateVector k p j
            ext i
            by_cases hij : i = j
            · subst i
              simp [parameterThirdEndomorphism, coordinateVector_apply, hlam]
            · simp [parameterThirdEndomorphism, coordinateVector_apply, hij]
          have hf : F (coordinateVector k p j) = q • (E ^ (p - 1)) (coordinateVector k p j) := by
            rw [hFdef, hEdef]
            change weightedBackwardEndomorphism (p := p) k alpha mu q' (coordinateVector k p j) =
              q • (cyclicForwardEndomorphism (p := p) k alpha ^ (p - 1)) (coordinateVector k p j)
            by_cases hj0 : (j : ℕ) = 0
            · have hj : j = ⟨0, by omega⟩ := Fin.ext hj0
              rw [hj] at hq ⊢
              simp only [if_pos] at hq
              rw [weightedBackwardEndomorphism_apply_zero k alpha mu q', cyclicE_pow_pred_basis]
              simp only [if_pos, hq]
            · rw [if_neg hj0] at hq
              rw [weightedBackwardEndomorphism_apply_pos k alpha mu q' (j : ℕ)
                (Nat.pos_of_ne_zero hj0) j.isLt, cyclicE_pow_pred_basis,
                if_neg hj0, hq, smul_smul]
              congr 1
              ring
          have horbit : Submodule.span k (Set.range fun i : Fin p =>
              (E ^ (i : ℕ)) (coordinateVector k p j)) = ⊤ := by
            rw [hEdef]
            change Submodule.span k (Set.range fun i : Fin p =>
              (cyclicForwardEndomorphism (p := p) k alpha ^ (i : ℕ)) (coordinateVector k p j)) = ⊤
            exact cyclicE_orbit_top k alpha halpha j
          let data : CyclicNormalForm k E F H p :=
            { alpha := alpha
              alpha_ne := halpha
              lam := lam
              q := q
              v0 := coordinateVector k p j
              v0_ne := hv0
              e_pow := hep
              h_v0 := hh
              f_v0 := hf
              orbit_top := horbit }
          simpa [target, data] using cyclicNormalForm_equiv k data

omit [IsAlgClosed k] in
private theorem restricted_highest_not_equiv (n : Fin p) (beta mu : k)
    (simple : beta ≠ 0 ∨ mu ^ p ≠ mu)
    (e : parameterEquivWitness k (.restricted n) (.highest beta mu simple)) : False := by
  classical
  have hp : 2 < p := Fact.out
  haveI : NeZero ((n : ℕ) + 1) := ⟨by omega⟩
  haveI : NeZero p := ⟨by omega⟩
  have hbeta := familyEquiv_fScalar_eq_of_eScalar_eq_zero k e (by rfl) (by rfl)
  change (0 : k) = beta at hbeta
  let z : Fin ((n : ℕ) + 1) := ⟨0, by omega⟩
  let v : parameterModule k (.restricted n) := coordinateVector k ((n : ℕ) + 1) z
  have hv : v ≠ 0 := by
    change coordinateVector k ((n : ℕ) + 1) z ≠ 0
    exact basis_ne_zero k z
  have hvE : (parameterLieEndomorphismTriple k (.restricted n)).first v = 0 := by
    change standardBackwardEndomorphism (d := (n : ℕ) + 1) k (n : k) v = 0
    ext i
    simp [standardBackwardEndomorphism, v, z, coordinateVector_apply]
  have hvH : (parameterLieEndomorphismTriple k (.restricted n)).third v = (n : k) • v := by
    change standardThirdEndomorphism (d := (n : ℕ) + 1) k (n : k)
      (coordinateVector k ((n : ℕ) + 1) z) = (n : k) • coordinateVector k ((n : ℕ) + 1) z
    simpa [z] using vermaH_basis k (d := (n : ℕ) + 1) (n : k) z
  have hw : e v ≠ 0 := by
    intro h
    have ez : e (0 : parameterModule k (.restricted n)) = 0 := e.map_zero
    exact hv (e.injective (h.trans ez.symm))
  have hwE : standardBackwardEndomorphism (d := p) k mu (e v) = 0 := by
    calc
      _ = e ((parameterLieEndomorphismTriple k (.restricted n)).first v) :=
        (familyEquiv_map_E k e v).symm
      _ = e (0 : parameterModule k (.restricted n)) := congrArg e hvE
      _ = 0 := map_zero e
  have hwH : standardThirdEndomorphism (d := p) k mu (e v) = (n : k) • e v := by
    calc
      _ = e ((parameterLieEndomorphismTriple k (.restricted n)).third v) :=
        (familyEquiv_map_H k e v).symm
      _ = e ((n : k) • v) := congrArg e hvH
      _ = (n : k) • e v := map_smul e (n : k) v
  obtain ⟨j, hlam, _⟩ := verma_highest_eigenvector_index k (p := p)
    mu (n : k) (e v) hw hwH hwE
  rcases simple with hbeta_ne | hmu
  · exact hbeta_ne hbeta.symm
  · apply hmu
    apply (Subfield.mem_bot_iff_pow_eq_self k p).mp
    have hmueq : mu = (n : k) + 2 * (j : ℕ) := by
      calc
        mu = (mu - 2 * (j : ℕ)) + 2 * (j : ℕ) := by ring
        _ = (n : k) + 2 * (j : ℕ) := by rw [← hlam]
    rw [hmueq]
    exact add_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (natCast_mem _ _))

omit [IsAlgClosed k] in
private theorem familyEquiv_sameInvariant {a b : ModuleParameter k p}
    (e : parameterEquivWitness k a b) : ModuleParameter.parameterEquivCondition k a b := by
  classical
  have hp : 2 < p := Fact.out
  cases a with
  | restricted n =>
      cases b with
      | restricted m =>
          change n = m
          apply Fin.ext
          have hdim := familyEquiv_dimension_eq k e
          simp [ModuleParameter.dimension] at hdim
          omega
      | highest beta mu simple =>
          exact (restricted_highest_not_equiv k n beta mu simple e).elim
      | cyclic alpha mu q halpha =>
          have h := familyEquiv_eScalar_eq k e
          change (0 : k) = alpha at h
          exact (halpha h.symm).elim
  | highest beta lam simple =>
      cases b with
      | restricted m =>
          exact (restricted_highest_not_equiv k m beta lam simple e.symm).elim
      | highest beta' mu simple' =>
          change beta = beta' ∧ ∃ j : Fin p,
            lam = mu - 2 * (j : ℕ) ∧
              (j : k) * (mu - (j : k) + 1) = 0
          have hbeta := familyEquiv_fScalar_eq_of_eScalar_eq_zero k e (by rfl) (by rfl)
          change beta = beta' at hbeta
          refine ⟨hbeta, ?_⟩
          haveI : NeZero p := ⟨by omega⟩
          let z : Fin p := ⟨0, by omega⟩
          let v : parameterModule k (.highest beta lam simple) := coordinateVector k p z
          have hv : v ≠ 0 := by
            change coordinateVector k p z ≠ 0
            exact basis_ne_zero k z
          have hvE : (parameterLieEndomorphismTriple k (.highest beta lam simple)).first v = 0 := by
            change standardBackwardEndomorphism (d := p) k lam v = 0
            ext i
            simp [standardBackwardEndomorphism, v, z, coordinateVector_apply]
          have hvH : (parameterLieEndomorphismTriple k (.highest beta lam simple)).third v = lam • v := by
            change standardThirdEndomorphism (d := p) k lam (coordinateVector k p z) = lam • coordinateVector k p z
            simpa [z] using vermaH_basis k (d := p) lam z
          have hw : e v ≠ 0 := by
            intro h
            have ez : e (0 : parameterModule k (.highest beta lam simple)) = 0 := e.map_zero
            exact hv (e.injective (h.trans ez.symm))
          have hwE : standardBackwardEndomorphism (d := p) k mu (e v) = 0 := by
            calc
              _ = e ((parameterLieEndomorphismTriple k (.highest beta lam simple)).first v) :=
                (familyEquiv_map_E k e v).symm
              _ = e (0 : parameterModule k (.highest beta lam simple)) := congrArg e hvE
              _ = 0 := map_zero e
          have hwH : standardThirdEndomorphism (d := p) k mu (e v) = lam • e v := by
            calc
              _ = e ((parameterLieEndomorphismTriple k (.highest beta lam simple)).third v) :=
                (familyEquiv_map_H k e v).symm
              _ = e (lam • v) := congrArg e hvH
              _ = lam • e v := map_smul e lam v
          exact verma_highest_eigenvector_index k (p := p) mu lam (e v) hw hwH hwE
      | cyclic alpha mu q halpha =>
          have h := familyEquiv_eScalar_eq k e
          change (0 : k) = alpha at h
          exact (halpha h.symm).elim
  | cyclic alpha lam q halpha =>
      cases b with
      | restricted m =>
          have h := familyEquiv_eScalar_eq k e
          change alpha = (0 : k) at h
          exact (halpha h).elim
      | highest beta mu simple =>
          have h := familyEquiv_eScalar_eq k e
          change alpha = (0 : k) at h
          exact (halpha h).elim
      | cyclic alpha' mu q' halpha' =>
          change alpha = alpha' ∧ ∃ j : Fin p,
            lam = mu + 2 * (j : ℕ) ∧
              (if (j : ℕ) = 0 then q = q'
              else recurrenceCoefficient k alpha mu q' (j : ℕ) = alpha * q)
          have halphaeq := familyEquiv_eScalar_eq k e
          change alpha = alpha' at halphaeq
          refine ⟨halphaeq, ?_⟩
          haveI : NeZero p := ⟨by omega⟩
          let z : Fin p := ⟨0, by omega⟩
          let v : parameterModule k (.cyclic alpha lam q halpha) := coordinateVector k p z
          have hv : v ≠ 0 := by
            change coordinateVector k p z ≠ 0
            exact basis_ne_zero k z
          have hvH : (parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).third v = lam • v := by
            change parameterThirdEndomorphism (p := p) k lam (coordinateVector k p z) = lam • coordinateVector k p z
            simpa [z] using cyclicH_basis k (p := p) lam z
          have hvF : (parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).second v =
              q • ((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).first ^ (p - 1)) v := by
            change weightedBackwardEndomorphism (p := p) k alpha lam q v =
              q • (cyclicForwardEndomorphism (p := p) k alpha ^ (p - 1)) v
            rw [show v = coordinateVector k p z from rfl, weightedBackwardEndomorphism_apply_zero,
              cyclicE_pow_pred_basis]
            simp [z]
          let w : Fin p → k := e v
          have hw : w ≠ 0 := by
            change e v ≠ 0
            intro h
            have ez : e (0 : parameterModule k (.cyclic alpha lam q halpha)) = 0 := e.map_zero
            exact hv (e.injective (h.trans ez.symm))
          have hwH : parameterThirdEndomorphism (p := p) k mu w = lam • w := by
            change parameterThirdEndomorphism (p := p) k mu (e v) = lam • e v
            calc
              _ = e ((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).third v) :=
                (familyEquiv_map_H k e v).symm
              _ = e (lam • v) := congrArg e hvH
              _ = lam • e v := map_smul e lam v
          obtain ⟨j, hlam, hshape, hwj⟩ :=
            cyclic_eigenvector_index k (p := p) mu lam w hw hwH
          refine ⟨j, hlam, ?_⟩
          have hmapF := (familyEquiv_map_F k e v).symm
          change weightedBackwardEndomorphism (p := p) k alpha' mu q' (e v) =
            e ((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).second v) at hmapF
          have hmapE := familyEquiv_map_E_pow k e (p - 1) v
          change e (((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).first ^
              (p - 1)) v) =
            (cyclicForwardEndomorphism (p := p) k alpha' ^ (p - 1)) (e v) at hmapE
          have hlast : e (q • ((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).first ^
                (p - 1)) v) =
              q • (cyclicForwardEndomorphism (p := p) k alpha' ^ (p - 1)) (e v) := by
            rw [map_smul]
            exact congrArg (fun x : Fin p → k => q • x) hmapE
          have hvFmap :
              (e ((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).second v) : Fin p → k) =
                (e (q • ((parameterLieEndomorphismTriple k (.cyclic alpha lam q halpha)).first ^
                  (p - 1)) v) : Fin p → k) := congrArg e hvF
          have hrel : weightedBackwardEndomorphism (p := p) k alpha' mu q' w =
              q • (cyclicForwardEndomorphism (p := p) k alpha' ^ (p - 1)) w := by
            change weightedBackwardEndomorphism (p := p) k alpha' mu q' (e v) =
              q • (cyclicForwardEndomorphism (p := p) k alpha' ^ (p - 1)) (e v)
            exact hmapF.trans (hvFmap.trans hlast)
          have hcancel : weightedBackwardEndomorphism (p := p) k alpha' mu q' (coordinateVector k p j) =
              q • (cyclicForwardEndomorphism (p := p) k alpha' ^ (p - 1)) (coordinateVector k p j) := by
            have hscaled := hrel
            rw [hshape, map_smul, map_smul] at hscaled
            exact smul_right_injective (Fin p → k) hwj <| by
              simpa only [smul_smul, mul_comm q] using hscaled
          by_cases hj0 : (j : ℕ) = 0
          · simp only [hj0, if_pos]
            have hj : j = z := Fin.ext hj0
            rw [hj, weightedBackwardEndomorphism_apply_zero, cyclicE_pow_pred_basis] at hcancel
            have hcoord := congrFun hcancel ⟨p - 1, by omega⟩
            simpa [z, coordinateVector_apply] using hcoord.symm
          · simp only [hj0, if_false]
            rw [weightedBackwardEndomorphism_apply_pos k alpha' mu q' (j : ℕ)
              (Nat.pos_of_ne_zero hj0) j.isLt, cyclicE_pow_pred_basis,
              if_neg hj0] at hcancel
            have hcoord := congrFun hcancel ⟨(j : ℕ) - 1, by omega⟩
            simpa [halphaeq, coordinateVector_apply, smul_smul, mul_comm] using hcoord

                                                                 
/-- A designated relation between two module parameters. -/
def ModuleParameter.parameterRelated (a b : ModuleParameter k p) : Prop :=
  ModuleParameter.parameterEquivCondition k a b

omit [IsAlgClosed k] in
                                                                                        
                                                       
/-- The auxiliary witness type is nonempty exactly when the two parameters satisfy the designated condition. -/
@[source_ref "Chapter2/Problem2.16.4" (role := supporting)]
theorem nonempty_parameterEquivWitness_iff (a b : ModuleParameter k p) :
    Nonempty (parameterEquivWitness k a b) ↔
      ModuleParameter.parameterEquivCondition k a b :=
  ⟨fun ⟨e⟩ => familyEquiv_sameInvariant k e,
    sameInvariant_equiv k a b⟩

omit [IsAlgClosed k] in
private theorem parameterIsomorphic_refl (a : ModuleParameter k p) :
    ModuleParameter.parameterRelated k a a :=
  familyEquiv_sameInvariant k LieModuleEquiv.refl

omit [IsAlgClosed k] in
private theorem parameterIsomorphic_symm {a b : ModuleParameter k p} :
    ModuleParameter.parameterRelated k a b → ModuleParameter.parameterRelated k b a := by
  intro h
  obtain ⟨e⟩ := sameInvariant_equiv k a b h
  exact familyEquiv_sameInvariant k e.symm

omit [IsAlgClosed k] in
private theorem parameterIsomorphic_trans {a b c : ModuleParameter k p} :
    ModuleParameter.parameterRelated k a b → ModuleParameter.parameterRelated k b c →
      ModuleParameter.parameterRelated k a c := by
  intro hab hbc
  obtain ⟨e⟩ := sameInvariant_equiv k a b hab
  obtain ⟨f⟩ := sameInvariant_equiv k b c hbc
  exact familyEquiv_sameInvariant k (e.trans f)

/-- The setoid on module parameters in positive prime characteristic. -/
noncomputable instance parameterSetoid : Setoid (ModuleParameter k p) where
  r := ModuleParameter.parameterRelated k
  iseqv := ⟨parameterIsomorphic_refl k, parameterIsomorphic_symm k,
    parameterIsomorphic_trans k⟩

                                                                
/-- Auxiliary data carrying a finite-dimensional irreducible module for the designated Lie algebra. -/
structure IrreducibleModuleData where
  /-- The carrier type of irreducible-module data. -/
  carrier : Type u
  /-- The additive commutative group structure on the carrier of irreducible-module data. -/
  [addCommGroup : AddCommGroup carrier]
  /-- The field-module structure on the carrier of irreducible-module data. -/
  [moduleStructure : Module k carrier]
  /-- The Lie-ring module structure on the carrier of irreducible-module data. -/
  [lieRingModule : LieRingModule (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) carrier]
  /-- The compatible Lie-module structure on the carrier of irreducible-module data. -/
  [lieModule : LieModule k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) carrier]
  /-- The carrier of irreducible-module data is finite-dimensional over the field. -/
  [finiteDimensional : FiniteDimensional k carrier]
  /-- The Lie module carried by irreducible-module data is irreducible. -/
  [isIrreducible : LieModule.IsIrreducible k (RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k) carrier]

namespace IrreducibleModuleData

attribute [instance] addCommGroup moduleStructure lieRingModule lieModule finiteDimensional isIrreducible

                                                              
/-- A relation between two irreducible-module data. -/
def moduleDataRelated (S T : IrreducibleModuleData k) : Prop :=
  Nonempty (S.carrier ≃ₗ⁅k, RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.twoByTwoMatrixLieSubalgebra k⁆ T.carrier)

omit [IsAlgClosed k] in
private theorem isomorphic_refl (S : IrreducibleModuleData k) : moduleDataRelated k S S :=
  ⟨LieModuleEquiv.refl⟩

omit [IsAlgClosed k] in
private theorem isomorphic_symm {S T : IrreducibleModuleData k} :
    moduleDataRelated k S T → moduleDataRelated k T S := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

omit [IsAlgClosed k] in
private theorem isomorphic_trans {S T U : IrreducibleModuleData k} :
    moduleDataRelated k S T → moduleDataRelated k T U → moduleDataRelated k S U := by
  rintro ⟨e⟩ ⟨f⟩
  exact ⟨e.trans f⟩

/-- A setoid on irreducible-module data. -/
noncomputable instance setoid : Setoid (IrreducibleModuleData k) where
  r := moduleDataRelated k
  iseqv := ⟨isomorphic_refl k, isomorphic_symm k, isomorphic_trans k⟩

end IrreducibleModuleData

                                                                                         
/-- Irreducible-module data associated with a module parameter. -/
noncomputable def moduleDataOfParameter (a : ModuleParameter k p) : IrreducibleModuleData k where
  carrier := parameterModule k a
  addCommGroup := inferInstance
  moduleStructure := inferInstance
  lieRingModule := lieRingModule_parameterModule k a
  lieModule := lieModule_parameterModule k a
  finiteDimensional := finiteDimensional_parameterModule k a
  isIrreducible := isIrreducible_parameterModule k a

omit [IsAlgClosed k] in
private theorem familyBundle_respects {a b : ModuleParameter k p} (h : a ≈ b) :
    moduleDataOfParameter k a ≈ moduleDataOfParameter k b := by
  obtain ⟨e⟩ := sameInvariant_equiv k a b h
  exact ⟨e⟩

                                                                                        
                                          
/-- A map from parameter equivalence classes to irreducible-module data classes. -/
noncomputable def parameterQuotientToModuleData :
    Quotient (parameterSetoid (k := k) (p := p)) →
      Quotient (IrreducibleModuleData.setoid (k := k)) :=
  Quotient.map (moduleDataOfParameter k) fun _ _ => familyBundle_respects k

private theorem classificationMap_bijective :
    Function.Bijective (parameterQuotientToModuleData (k := k) (p := p)) := by
  constructor
  · intro A B hAB
    induction A using Quotient.inductionOn with
    | _ a =>
      induction B using Quotient.inductionOn with
      | _ b =>
        apply Quotient.sound
        change (⟦moduleDataOfParameter k a⟧ :
          Quotient (IrreducibleModuleData.setoid (k := k))) = ⟦moduleDataOfParameter k b⟧ at hAB
        obtain ⟨e⟩ := Quotient.exact hAB
        exact familyEquiv_sameInvariant k e
  · intro S
    induction S using Quotient.inductionOn with
    | _ S =>
      letI := S.addCommGroup
      letI := S.moduleStructure
      letI := S.lieRingModule
      letI := S.lieModule
      letI := S.finiteDimensional
      letI := S.isIrreducible
      obtain ⟨a, ⟨e⟩⟩ := exists_parameterModule_equiv k S.carrier
      refine ⟨⟦a⟧, ?_⟩
      apply Quotient.sound
      exact ⟨e⟩

                                                                                         
                                                                                        
/-- Over an algebraically closed field, parameter equivalence classes are equivalent to irreducible-module data classes. -/
@[source_ref "Chapter2/Problem2.16.4" (role := supporting)]
noncomputable def parameterQuotientEquivModuleData :
    Quotient (parameterSetoid (k := k) (p := p)) ≃
      Quotient (IrreducibleModuleData.setoid (k := k)) :=
  Equiv.ofBijective (parameterQuotientToModuleData (k := k) (p := p))
    (classificationMap_bijective (k := k) (p := p))

end ClassificationAPI

                                                                                                 
                                                                                              
                                            
attribute [-instance] lieRingModule_parameterModule lieModule_parameterModule

end RepresentationTheory.LieModule.IrreducibleParameterModules
