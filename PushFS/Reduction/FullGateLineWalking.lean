/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateLineFrames

/-! Every complete actual annular long line connects its real hub to all four corners in every independent primitive profile. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem raw_line_corners (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b choice : Bool) (i : Fin 4)
    {W H : ℕ} (e : GridEmbedding (lineBase flip n hn a b).width (lineBase flip n hn a b).height W H)
    {B : Board W H} {outside : Finset (Cell W H)}
    (hw : e.WallsAgree (lineBase flip n hn a b).board B) (hf : Disjoint outside B.walls)
    (hc : Polyline.Frame.fixed e outside⊆lineAllNeighbors flip n hn a b) :
    let boxes:=if choice then (lineBase flip n hn a b).board.goals else (lineBase flip n hn a b).initial.boxes
    Reachable B (some 1) (e.extend outside ⟨lineBaseHub flip n hn a b,boxes⟩)
      (e.extend outside ⟨lineBaseCorner flip n hn a b i,boxes⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨lineBaseCorner flip n hn a b i,boxes⟩)
      (e.extend outside ⟨lineBaseHub flip n hn a b,boxes⟩) := by
  cases flip
  · cases choice
    · exact Chain.corners_placed_allNeighbors n hn (Chain.uniform n a) i (Polyline.Frame.fixed e outside) hc e hw
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf
    · exact Chain.corners_placed_allNeighbors n hn (Chain.uniform n b) i (Polyline.Frame.fixed e outside) hc e hw
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf
  · have hw' : e.WallsAgree (FlippedChain.board n hn ∅) B := by
      intro p
      have hm:=hw p
      change e.cells p∈B.walls ↔p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls at hm
      rw [FlippedChain.atlas_walls] at hm
      exact hm
    cases choice
    · change Reachable B (some 1) (e.extend outside ⟨FlippedChain.player n,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).initial.boxes⟩)
        (e.extend outside ⟨FlippedChain.corner n i,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).initial.boxes⟩) ∧
        Reachable B (some 1) (e.extend outside ⟨FlippedChain.corner n i,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).initial.boxes⟩)
        (e.extend outside ⟨FlippedChain.player n,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).initial.boxes⟩)
      rw [FlippedChain.initial_boxes]
      exact FlippedChain.corners_placed n hn (FlippedChain.uniform a) i (Polyline.Frame.fixed e outside) hc e hw'
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf
    · change Reachable B (some 1) (e.extend outside ⟨FlippedChain.player n,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals⟩)
        (e.extend outside ⟨FlippedChain.corner n i,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals⟩) ∧
        Reachable B (some 1) (e.extend outside ⟨FlippedChain.corner n i,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals⟩)
        (e.extend outside ⟨FlippedChain.player n,(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.goals⟩)
      rw [FlippedChain.goals_eq]
      exact FlippedChain.corners_placed n hn (FlippedChain.uniform b) i (Polyline.Frame.fixed e outside) hc e hw'
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
        (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hf

attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profileOutside

end PushPuzzle.PushFS.Reduction.GateTileRouting
