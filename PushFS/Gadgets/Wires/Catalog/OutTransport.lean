/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutFrames
public import PushFS.Gadgets.Wires.Polyline.Transport

/-! Actual local hubs and corner paths inside the complete independently phased L board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out


variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

def atIn (a : Phases) : State (m+43) (n+64) :=
  ⟨(inEmbed m n hm hn).cells (Chain.hub m hm),boxes m n hm hn a⟩
def atOut (a : Phases) : State (m+43) (n+64) :=
  ⟨(outEmbed m n hm hn).cells (Tail.hub n hn),boxes m n hm hn a⟩

theorem place_in (a : Phases) (p : Chain.C m) :
    (inEmbed m n hm hn).extend (inExternal m n hm hn a) ⟨p,Chain.boxes m hm (Chain.uniform m (a 0))⟩ =
      ⟨(inEmbed m n hm hn).cells p,boxes m n hm hn a⟩ := by
  apply State.ext
  · rfl
  change inBoxes m n hm hn (a 0) ∪ (turnBoxes m n hm hn (a 1) ∪ outBoxes m n hm hn (a 2)) =
    (inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1)) ∪ outBoxes m n hm hn (a 2)
  ac_rfl

theorem place_turn (a : Phases) (p : Turn.C) :
    (turnRect m n hm hn).extend (turnExternal m n hm hn a) ⟨p,Turn.template.boxes (a 1)⟩ =
      ⟨(turnRect m n hm hn).cells p,boxes m n hm hn a⟩ := by
  apply State.ext
  · rfl
  change turnBoxes m n hm hn (a 1) ∪ (inBoxes m n hm hn (a 0) ∪ outBoxes m n hm hn (a 2)) =
    (inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1)) ∪ outBoxes m n hm hn (a 2)
  ac_rfl

theorem place_out (a : Phases) (p : Tail.C n) :
    (outEmbed m n hm hn).extend (outExternal m n hm hn a) ⟨p,Tail.boxes n hn (Tail.uniform n (a 2))⟩ =
      ⟨(outEmbed m n hm hn).cells p,boxes m n hm hn a⟩ := by
  apply State.ext
  · rfl
  change outBoxes m n hm hn (a 2) ∪ (inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1)) =
    (inBoxes m n hm hn (a 0) ∪ turnBoxes m n hm hn (a 1)) ∪ outBoxes m n hm hn (a 2)
  ac_rfl

theorem turn_hub : (turnRect m n hm hn).cells Turn.hub=player m n := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out
