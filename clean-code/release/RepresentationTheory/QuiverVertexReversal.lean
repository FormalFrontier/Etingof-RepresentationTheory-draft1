/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import Mathlib.Combinatorics.Quiver.Basic
import RepresentationTheory.Alignment.Attribute

/-!
# Quiver Vertex Reversal

Arrow types and the quiver obtained by reversing arrows incident to a selected vertex.
-/

/-- The arrow type obtained by reversing arrows incident to a distinguished vertex. -/
@[source_ref "Chapter6/Definition6.6.2" (role := supporting)]
def RepresentationTheory.QuiverVertexReversal.reversedAtHom
    (V : Type*) [inst : DecidableEq V] [Quiver V] (i : V) (a b : V) : Type _ :=
  @Decidable.casesOn _ (fun _ => Type _) (inst a i)
    (fun _ =>
      @Decidable.casesOn _ (fun _ => Type _) (inst b i)
        (fun _ => (a ⟶ b))
        (fun _ => (i ⟶ a)))
    (fun _ =>
      @Decidable.casesOn _ (fun _ => Type _) (inst b i)
        (fun _ => (b ⟶ i))
        (fun _ => (a ⟶ b)))

/-- The reversed arrow type agrees with the original arrow type when neither endpoint is distinguished. -/
theorem RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_ne
    {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a ≠ i) (hb : b ≠ i) :
    RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b = (a ⟶ b) := by
  unfold reversedAtHom
  cases inst a i with
  | isTrue h => exact absurd h ha
  | isFalse _ => cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl

/-- The reversed arrow type points into the distinguished vertex when only the source is distinguished. -/
theorem RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_ne
    {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a = i) (hb : b ≠ i) :
    RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b = (b ⟶ i) := by
  unfold reversedAtHom
  cases inst a i with
  | isFalse h => exact absurd ha h
  | isTrue _ => cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl

/-- The reversed arrow type points out of the distinguished vertex when only the target is distinguished. -/
theorem RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_ne_eq
    {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a ≠ i) (hb : b = i) :
    RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b = (i ⟶ a) := by
  unfold reversedAtHom
  cases inst a i with
  | isTrue h => exact absurd h ha
  | isFalse _ => cases inst b i with
    | isFalse h => exact absurd hb h
    | isTrue _ => rfl

/-- The reversed arrow type agrees with the original arrow type when both endpoints are distinguished. -/
theorem RepresentationTheory.QuiverVertexReversal.reversedAtHom_eq_of_eq_eq
    {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a = i) (hb : b = i) :
    RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b = (a ⟶ b) := by
  unfold reversedAtHom
  cases inst a i with
  | isFalse h => exact absurd ha h
  | isTrue _ => cases inst b i with
    | isFalse h => exact absurd hb h
    | isTrue _ => rfl

/-- The quiver obtained by reversing arrows incident to a chosen vertex. -/
noncomputable def RepresentationTheory.QuiverVertexReversal.reverseAtVertex
    (V : Type*) [DecidableEq V] [Quiver V] (i : V) : Quiver V :=
  ⟨fun a b => RepresentationTheory.QuiverVertexReversal.reversedAtHom V i a b⟩
