/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Strip

/-!
# Soundness of parity and face-switch wires

The parity tool has one sealed strip; the face-switch tool has two disjoint
one-cell strips. In a successful physical trajectory each strip must remain
logically open. Chaining their inequalities proves signal propagation even when
the intermediate box of a face switch occupies a noncanonical position.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness



variable {w h : ℕ}

/-- Take two neighboring physical labels from the existing three-label tracker. -/
def leftPair (S : AND.Configuration w h) : Configuration w h := ⟨S.state, S.a, S.b⟩

def rightPair (S : AND.Configuration w h) : Configuration w h := ⟨S.state, S.b, S.c⟩

private theorem leftPair_tracked {B : Board w h} {S T : AND.Configuration w h}
    (ht : AND.TrackedStep B S T) : TrackedStep B (leftPair S) (leftPair T) := by
  obtain ⟨d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨hboxes, ha, hb, _⟩ := hwalk
    exact ⟨d, hm, Or.inl ⟨hboxes, ha, hb⟩⟩
  · obtain ⟨q, hp, hq, he, hboxes, ha, hb, _⟩ := hpush
    exact ⟨d, hm, Or.inr ⟨q, hp, hq, he, hboxes, ha, hb⟩⟩

private theorem rightPair_tracked {B : Board w h} {S T : AND.Configuration w h}
    (ht : AND.TrackedStep B S T) : TrackedStep B (rightPair S) (rightPair T) := by
  obtain ⟨d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨hboxes, _, hb, hc⟩ := hwalk
    exact ⟨d, hm, Or.inl ⟨hboxes, hb, hc⟩⟩
  · obtain ⟨q, hp, hq, he, hboxes, _, hb, hc⟩ := hpush
    exact ⟨d, hm, Or.inr ⟨q, hp, hq, he, hboxes, hb, hc⟩⟩

/-- All three physical labels stay on their ordered horizontal track. -/
def TripleShape (y : ℕ) (S : AND.Configuration w h) : Prop :=
  Shape y (leftPair S) ∧ Shape y (rightPair S)

def TripleStep (B : Board w h) (y : ℕ) (S T : AND.Configuration w h) : Prop :=
  TripleShape y S ∧ TripleShape y T ∧ AND.TrackedStep B S T

theorem leftPair_geometric {B : Board w h} {y : ℕ} {S T : AND.Configuration w h}
    (ht : TripleStep B y S T) : GeometricStep B y (leftPair S) (leftPair T) :=
  ⟨ht.1.1, ht.2.1.1, leftPair_tracked ht.2.2⟩

theorem rightPair_geometric {B : Board w h} {y : ℕ} {S T : AND.Configuration w h}
    (ht : TripleStep B y S T) : GeometricStep B y (rightPair S) (rightPair T) :=
  ⟨ht.1.2, ht.2.1.2, rightPair_tracked ht.2.2⟩

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
