/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.TrainAdapter

/-! The same actual flipped train with its four walking-corner names adapted to the incoming vertical reflection. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Head


abbrev C:=Tail.C
abbrev Label:=Tail.Label
abbrev uniform:=Tail.uniform
abbrev position:=Tail.position
abbrev boxes:=Tail.boxes
abbrev state:=Tail.state
abbrev walls:=Tail.walls
abbrev board:=Tail.board
abbrev hub:=Tail.hub
abbrev neighbors:=Tail.neighbors
abbrev allNeighbors:=Tail.allNeighbors
abbrev boxes_floor:=Tail.boxes_floor
abbrev position_row:=Tail.position_row
abbrev phase_bounds:=Tail.phase_bounds
abbrev walls_rows:=Tail.walls_rows
abbrev transition_placed {W H : ℕ}:=Tail.transition_placed (W:=W) (H:=H)

def cornerIndex (i : Fin 4) : Fin 4 := ![2,3,0,1] i
def corner (n : ℕ) (i : Fin 4) := FlippedChain.corner n (cornerIndex i)

/-- Both actual near-terminal false identities retain their precise last-pair coordinates. -/
theorem right_low (n : ℕ) (hn : 2301≤n) (l : Label n)
    (hx : n+20≤(Tail.position n hn false l).1.val+2) :
    (Tail.position n hn false l).1.val=n+20 ∨
    (Tail.position n hn false l).1.val+2=n+20 := by
  rcases l with ⟨i,l⟩
  have cases2 (i : Fin 2) : i=0∨i=1 := by have := i.isLt; simp only [Fin.ext_iff]; omega
  rcases cases2 i with rfl|rfl
  · change n+20≤(FlippedChain.position n hn false ⟨0,l⟩).1.val+2 at hx
    rw [FlippedChain.position0 n hn false l,FlippedChain.chain_x] at hx
    have hh:=Polyline.chain_phase_bounds n hn false l
    simp only [Bool.toNat_false,Nat.add_zero] at hh
    omega
  · change n+20≤(FlippedChain.position n hn false ⟨1,l⟩).1.val+2 at hx
    change (FlippedChain.position n hn false ⟨1,l⟩).1.val=n+20 ∨
      (FlippedChain.position n hn false ⟨1,l⟩).1.val+2=n+20
    rw [FlippedChain.position1 n hn false l,FlippedChain.flip_x] at hx ⊢
    have check : ∀l : Fin 9, 20≤(Flip.template.position false l).1.val+2 →
      (Flip.template.position false l).1.val=20 ∨ (Flip.template.position false l).1.val+2=20 := by decide +kernel
    have hh:=check l (by omega)
    omega

/-- The renamed corner is reached by the existing genuine FlippedChain walk, preserving all actual boxes. -/
theorem corners_placed_allNeighbors {W H : ℕ} (n : ℕ) (hn : 2301≤n) (a : Bool) (i : Fin 4)
    (fixed : Finset (C n)) (hf : fixed⊆allNeighbors n) (e : GridEmbedding (n+25) 21 W H)
    {B : Board W H} {outside : Finset (PushFS.Cell W H)} (hw : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀p,e.cells p∈outside →p∈fixed) (hfixed : ∀p∈fixed,e.cells p∈outside) (he : Disjoint outside B.walls) :
    Reachable B (some 1) ((state n hn a).place e outside) ((⟨corner n i,boxes n hn a⟩ : State (n+25) 21).place e outside) ∧
    Reachable B (some 1) ((⟨corner n i,boxes n hn a⟩ : State (n+25) 21).place e outside) ((state n hn a).place e outside) :=
  Tail.corners_placed_allNeighbors n hn a (cornerIndex i) fixed hf e hw hinside hfixed he

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Head
