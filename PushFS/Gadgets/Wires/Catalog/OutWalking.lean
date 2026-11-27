/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutTransport
public import PushFS.Gadgets.Wires.Catalog.OutWalkingGeometry

/-! Full real player navigation between the three L-piece hubs for every phase assignment. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out


variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

def topTurnPoint : C m n := (⟨43,by clear hn; omega⟩,⟨2,by clear hm hn; omega⟩)
def topInPoint : C m n := (⟨39,by clear hm hn; omega⟩,⟨1,by clear hm hn; omega⟩)
def tailTurnPoint : C m n := (⟨43,by clear hn; omega⟩,⟨40,by clear hm hn; omega⟩)
def tailOutPoint : C m n := (⟨19,by clear hm hn; omega⟩,⟨40,by clear hm hn; omega⟩)

theorem turn_corner1 : (turnRect m n hm hn).cells (Turn.corner 1)=topTurnPoint m n hm := by
  apply Prod.ext <;> apply Fin.ext <;> rfl
theorem turn_corner3 : (turnRect m n hm hn).cells (Turn.corner 3)=tailTurnPoint m n hm := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem in_corner1 : (inEmbed m n hm hn).cells (Chain.corner m 1)=topInPoint m n := by
  apply Prod.ext <;> apply Fin.ext
  · rw [in_x]
    change 38+(m+4-(m+3))=39
    omega
  · rw [in_y]
    rfl

theorem out_corner0 : (outEmbed m n hm hn).cells (Tail.corner n 0)=tailOutPoint m n := by
  apply Prod.ext <;> apply Fin.ext
  · rw [out_x]
    rfl
  · rw [out_y]
    rfl

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out
