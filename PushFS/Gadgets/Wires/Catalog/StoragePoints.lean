/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RotatedChainSignal

/-! True reference-point thresholds and source order compose through actual complete storage images. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.StorageImage

open Soundness

variable {I J K : Instance} {L A D : Type} [Fintype L] [Fintype A] [Fintype D]
    {M : SlotMatching I L} {N : SlotMatching J A} {P : SlotMatching K D}

theorem source_directional_order (g : StorageImage M N) (d : Direction) (i j : A)
    (ho : DirectionalOrder d ((N.source i).1.val,(N.source i).2.val) ((N.source j).1.val,(N.source j).2.val)) :
    DirectionalOrder d ((M.source (g.labels i)).1.val,(M.source (g.labels i)).2.val)
      ((M.source (g.labels j)).1.val,(M.source (g.labels j)).2.val) := by
  rw [g.sources,g.sources]
  cases d
  · change g.dy+(N.source j).2.val<g.dy+(N.source i).2.val
    exact Nat.add_lt_add_left ho _
  · change g.dx+(N.source i).1.val<g.dx+(N.source j).1.val
    exact Nat.add_lt_add_left ho _
  · change g.dy+(N.source i).2.val<g.dy+(N.source j).2.val
    exact Nat.add_lt_add_left ho _
  · change g.dx+(N.source j).1.val<g.dx+(N.source i).1.val
    exact Nat.add_lt_add_left ho _

theorem directional_step (g : StorageImage M N) (d : Direction) (p q : PushFS.Cell J.width J.height)
    (hs : DirectionalStep d (p.1.val,p.2.val) (q.1.val,q.2.val)) :
    DirectionalStep d
      (((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells p).1.val,
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells p).2.val)
      (((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells q).1.val,
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells q).2.val) := by
  cases d <;> dsimp only [DirectionalStep] at hs
  · change g.dy+q.2.val+2=g.dy+p.2.val
    omega
  · change g.dx+p.1.val+2=g.dx+q.1.val
    omega
  · change g.dy+p.2.val+2=g.dy+q.2.val
    omega
  · change g.dx+q.1.val+2=g.dx+p.1.val
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.StorageImage
