/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteWireFrame
public import PushFS.Isometry

/-! Compose nested physical placements while retaining every layer's stationary stock. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteWireFrame

open PushFS

variable {a b n m W H : ℕ}

/-- A nested placement maps local fixed boxes before adjoining the ambient fixed inventory. -/
private theorem extend_extend (inner : GridEmbedding a b n m) (outer : GridEmbedding n m W H)
    (localFixed : Finset (Cell n m)) (extra : Finset (Cell W H)) (s : State a b) :
    outer.extend extra (inner.extend localFixed s) =
      (inner.trans outer).extend (localFixed.map outer.cells ∪ extra) s := by
  apply State.ext
  · rfl
  · simp only [GridEmbedding.extend, GridEmbedding.trans, Finset.map_union,
      Finset.map_map, Finset.union_assoc]

/-- Replay through two placements, constraining only the original active footprint. -/
theorem Frame.replay_nested {active goals : Finset (Cell a b)}
    {inner : GridEmbedding a b n m} {outer : GridEmbedding n m W H} {B : Board W H}
    {localFixed : Finset (Cell n m)} {extra : Finset (Cell W H)}
    (F : Frame active (inner.trans outer) B (localFixed.map outer.cells ∪ extra))
    {s t : State a b} (hr : Reachable (board active goals) (some 1) s t) :
    Reachable B (some 1) (outer.extend extra (inner.extend localFixed s))
      (outer.extend extra (inner.extend localFixed t)) := by
  simpa only [extend_extend] using F.replay hr

/-- Isolate one moving actor while retaining the mapped local and ambient fixed inventories. -/
theorem extend_insert (e : GridEmbedding n m W H) (localFixed : Finset (Cell n m))
    (extra : Finset (Cell W H)) (player actor : Cell n m) :
    e.extend (localFixed.map e.cells ∪ extra) ⟨player, {actor}⟩ =
      e.extend extra ⟨player, insert actor localFixed⟩ := by
  apply State.ext
  · rfl
  · simp only [GridEmbedding.extend, Finset.map_singleton, Finset.map_insert,
      Finset.singleton_union, Finset.insert_union]

end PushPuzzle.PushS.FiniteWireFrame
