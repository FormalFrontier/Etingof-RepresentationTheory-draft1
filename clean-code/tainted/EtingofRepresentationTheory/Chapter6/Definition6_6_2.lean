import Mathlib.Combinatorics.Quiver.Basic

/-!
# Definition 6.6.2: Reversed Quiver at a Vertex

Given a quiver Q and a vertex i, Q̄ᵢ is the quiver obtained from Q
by reversing all arrows incident to i (i.e., arrows where exactly one endpoint is i).

## Mathlib correspondence

Mathlib has `Quiver.reverse` which reverses ALL edges, but not vertex-local reversal.
This requires a custom definition that selectively reverses edges at a single vertex.
-/

/-- The type of arrows in the quiver obtained by reversing all arrows incident to vertex `i`.
For arrows not touching `i`, the type is unchanged. For arrows from `i` to `b` (with `b ≠ i`),
the type is `Hom_Q(b, i)` (reversed). For arrows from `a` to `i` (with `a ≠ i`),
the type is `Hom_Q(i, a)` (reversed). Self-loops at `i` are unchanged. -/
def Etingof.ReversedAtVertexHom (V : Type*) [inst : DecidableEq V] [Quiver V] (i : V)
    (a b : V) : Type _ :=
  -- Use @Decidable.casesOn rather than ite so that matching on `inst a i` / `inst b i`
  -- reduces both the arrow type and the object type in proofs about the reflection functor.
  @Decidable.casesOn _ (fun _ => Type _) (inst a i)
    (fun _ => -- a ≠ i
      @Decidable.casesOn _ (fun _ => Type _) (inst b i)
        (fun _ => (a ⟶ b))   -- a ≠ i, b ≠ i: unchanged
        (fun _ => (i ⟶ a)))  -- a ≠ i, b = i: was i→a in Q
    (fun _ => -- a = i
      @Decidable.casesOn _ (fun _ => Type _) (inst b i)
        (fun _ => (b ⟶ i))   -- a = i, b ≠ i: was b→i in Q
        (fun _ => (a ⟶ b)))  -- a = i, b = i: self-loop, unchanged

/-! ## API lemmas for `ReversedAtVertexHom`

These reduce `ReversedAtVertexHom` to the underlying arrow type once the
relationship between vertices `a`, `b`, and `i` is known. They avoid the need
to `unfold` the definition and manually reduce `Decidable.casesOn`. -/

theorem Etingof.ReversedAtVertexHom_ne_ne {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a ≠ i) (hb : b ≠ i) :
    Etingof.ReversedAtVertexHom V i a b = (a ⟶ b) := by
  unfold ReversedAtVertexHom
  cases inst a i with
  | isTrue h => exact absurd h ha
  | isFalse _ => cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl

theorem Etingof.ReversedAtVertexHom_eq_ne {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a = i) (hb : b ≠ i) :
    Etingof.ReversedAtVertexHom V i a b = (b ⟶ i) := by
  unfold ReversedAtVertexHom
  cases inst a i with
  | isFalse h => exact absurd ha h
  | isTrue _ => cases inst b i with
    | isTrue h => exact absurd h hb
    | isFalse _ => rfl

theorem Etingof.ReversedAtVertexHom_ne_eq {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a ≠ i) (hb : b = i) :
    Etingof.ReversedAtVertexHom V i a b = (i ⟶ a) := by
  unfold ReversedAtVertexHom
  cases inst a i with
  | isTrue h => exact absurd h ha
  | isFalse _ => cases inst b i with
    | isFalse h => exact absurd hb h
    | isTrue _ => rfl

theorem Etingof.ReversedAtVertexHom_eq_eq {V : Type*} [inst : DecidableEq V] [Quiver V]
    {i a b : V} (ha : a = i) (hb : b = i) :
    Etingof.ReversedAtVertexHom V i a b = (a ⟶ b) := by
  unfold ReversedAtVertexHom
  cases inst a i with
  | isFalse h => exact absurd ha h
  | isTrue _ => cases inst b i with
    | isFalse h => exact absurd hb h
    | isTrue _ => rfl

/-- The quiver obtained by reversing all arrows incident to vertex `i`.
For a sink, this reverses all incoming arrows; for a source, all outgoing arrows.
(Etingof Definition 6.6.2) -/
noncomputable def Etingof.reversedAtVertex
    (V : Type*) [DecidableEq V] [Quiver V] (i : V) : Quiver V :=
  ⟨fun a b => Etingof.ReversedAtVertexHom V i a b⟩
