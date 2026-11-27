/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Occupancy
public import PushFS.Walking

/-! Each block update and every trip along the common hub row is a real
Push-1FS trajectory on the constructed chain board. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096
set_option maxHeartbeats 500000

def board (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) : Board (n+5) 21 := ⟨walls n hn,goals⟩
def hub (n : ℕ) (hn : 2301 ≤ n) : C n := (⟨20,by omega⟩,3)
def state (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) : State (n+5) 21 := ⟨hub n hn,boxes n hn a⟩
def stateAt (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) : State (n+5) 21 :=
  ⟨embed n hn i (Tile.hub (kind n i)),boxes n hn a⟩

theorem walk_row (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a : Phases n)
    (p q : C n) (hp : p.2.val = 3) (hq : q.2.val = 3) :
    Reachable (board n hn goals) (some 1) ⟨p,boxes n hn a⟩ ⟨q,boxes n hn a⟩ := by
  have hp' : p = (p.1,(3 : Fin 21)) := Prod.ext rfl (Fin.ext hp)
  have hq' : q = (q.1,(3 : Fin 21)) := Prod.ext rfl (Fin.ext hq)
  rw [hp',hq']
  apply walk_horizontal (boxes_floor n hn a)
  intro x _hlo _hhi
  constructor
  · intro hw
    have hh := walls_rows n hn (x,3) hw
    norm_num at hh
  · intro hb
    have hh := boxes_row n hn a hb
    norm_num at hh

theorem hub_to_block (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a : Phases n) (i : Block n) :
    Reachable (board n hn goals) (some 1) (state n hn a) (stateAt n hn a i) :=
  walk_row n hn goals a _ _ rfl (by simp only [embed_y,Tile.hub_y])

theorem block_to_hub (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n)) (a : Phases n) (i : Block n) :
    Reachable (board n hn goals) (some 1) (stateAt n hn a i) (state n hn a) :=
  walk_row n hn goals a _ _ (by simp only [embed_y,Tile.hub_y]) rfl

theorem place_state (n : ℕ) (hn : 2301 ≤ n) (a : Phases n) (i : Block n) :
    (Tile.state (kind n i) (a i)).place (placement n hn i) (external n hn a i) = stateAt n hn a i := by
  apply State.ext
  · rfl
  · exact boxes_split n hn a i

end PushPuzzle.PushFS.Gadgets.Wires.Chain
