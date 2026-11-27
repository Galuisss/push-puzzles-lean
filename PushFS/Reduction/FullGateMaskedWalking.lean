/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateMaskedFrames

/-! Primitive player travel with all real neighboring endpoint boxes fixed. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

theorem masked_line_corners (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (j : Fin (curve (key g r)).length) (i : Fin 4) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineHub g r j)))
      (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineCorner g r j i))) ∧
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineCorner g r j i)))
      (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineHub g r j))) := by
  have hh:=raw_line_corners (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
    (filler_shape (key g r) j.val j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r)
    (f (lineIndex g r j)) i (lineEmbedding g r j) (line_walls g r j)
    (masked_outside_floor g f fixed hm (lineIndex g r j)) (masked_line_collar g f fixed hm r j)
  change Reachable (fullPuzzle g).board (some 1)
    ((lineEmbedding g r j).extend ((profileOutside g f (lineIndex g r j)∪fixed))
      ⟨lineHub g r j,if f (lineIndex g r j) then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes⟩)
    ((lineEmbedding g r j).extend ((profileOutside g f (lineIndex g r j)∪fixed))
      ⟨lineCorner g r j i,if f (lineIndex g r j) then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes⟩) ∧
    Reachable (fullPuzzle g).board (some 1)
    ((lineEmbedding g r j).extend ((profileOutside g f (lineIndex g r j)∪fixed))
      ⟨lineCorner g r j i,if f (lineIndex g r j) then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes⟩)
    ((lineEmbedding g r j).extend ((profileOutside g f (lineIndex g r j)∪fixed))
      ⟨lineHub g r j,if f (lineIndex g r j) then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes⟩) at hh
  rw [masked_line_place,masked_line_place] at hh
  exact hh


theorem masked_buffer_corners (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (i : Fin 4) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g f fixed ((bufferLeadEmbedding g r).cells (Chain.corner 2301 i))) ∧
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((bufferLeadEmbedding g r).cells (Chain.corner 2301 i)))
      (maskedProfile g f fixed (fullAtlas g).player) := by
  let atCorner : State 200007 198068:=(bufferRect g.core.isAND).extend (annularProfileBoxes g f∪fixed)
    ⟨(frontierLeadPlacement g.core.isAND 2301 r).cells (Chain.corner 2301 i),
      GateLead.boxes g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f)⟩
  have hh : Reachable (fullPuzzle g).board (some 1)
      ((bufferRect g.core.isAND).extend (annularProfileBoxes g f∪fixed)
        (GateLead.state g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f))) atCorner ∧
      Reachable (fullPuzzle g).board (some 1) atCorner
      ((bufferRect g.core.isAND).extend (annularProfileBoxes g f∪fixed)
        (GateLead.state g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f))) := by
    fin_cases r
    · exact (maskedBufferShell g f fixed hm).west_corners (masked_buffer_collar g f fixed hm 0) _ _ i
    · exact (maskedBufferShell g f fixed hm).north_corners (masked_buffer_collar g f fixed hm 1) _ _ i
    · exact (maskedBufferShell g f fixed hm).east_corners (masked_buffer_collar g f fixed hm 2) _ _ i
  have he : atCorner=maskedProfile g f fixed ((bufferLeadEmbedding g r).cells (Chain.corner 2301 i)) :=
    masked_buffer_place g f fixed _
  rw [masked_buffer_state,he] at hh
  exact hh

private theorem line_wall_rows (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hp : p∈(lineBase flip n hn a b).board.walls) : p.2.val=8 ∨p.2.val=9 ∨p.2.val=11 ∨p.2.val=12 := by
  cases flip
  · exact Chain.walls_rows n hn p hp
  · change p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board.walls at hp
    unfold StorageAtlas.board at hp
    rw [FlippedChain.atlas_walls] at hp
    exact FlippedChain.walls_rows n hn hp

private theorem line_marks_row (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b goal : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hp : p∈(if goal then (lineBase flip n hn a b).board.goals else (lineBase flip n hn a b).initial.boxes)) : p.2.val=10 := by
  cases goal
  · change p∈(lineBase flip n hn a b).initial.boxes at hp
    rw [←(lineMatching flip n hn a b).source_image] at hp
    obtain ⟨l,_,rfl⟩:=Finset.mem_map.mp hp
    exact (line_source_bounds flip n hn a b l).2.2
  · change p∈(lineBase flip n hn a b).board.goals at hp
    rw [←(lineMatching flip n hn a b).target_image] at hp
    obtain ⟨l,_,rfl⟩:=Finset.mem_map.mp hp
    exact (line_target_bounds flip n hn a b l).2.2

private theorem masked_line_outer_row (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin (curve (key g r)).length)
    (p q : Cell (lineInput g r j).width (lineInput g r j).height) (hp : p.2.val=1) (hq : q.2.val=1) :
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((lineEmbedding g r j).cells p)) (maskedProfile g f fixed ((lineEmbedding g r j).cells q)) := by
  let I:=lineInput g r j
  let e:=lineEmbedding g r j
  let outside:=profileOutside g f (lineIndex g r j)∪fixed
  let actual : Finset (Cell I.width I.height):=
    if f (lineIndex g r j) then I.board.goals else I.initial.boxes
  let localFixed:=Polyline.Frame.fixed e outside
  have hw:=line_walls g r j
  have hout:=masked_outside_floor g f fixed hm (lineIndex g r j)
  have hactual : Disjoint actual I.board.walls := by
    dsimp only [actual]
    split
    · exact I.goals_floor.symm
    · exact I.initial_valid.2.1
  have hfixed : Disjoint localFixed I.board.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hw'
    exact Finset.disjoint_left.mp hout ((Polyline.Frame.mem_fixed _ _ p).mp hp) ((hw p).mpr hw')
  have hrow (p : Cell I.width I.height) (hmem : p∈actual∪localFixed) : p.2.val=10 := by
    rcases Finset.mem_union.mp hmem with hmem|hmem
    · exact line_marks_row (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape _ _ j.isLt).2.1
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) (f (lineIndex g r j)) p hmem
    · have hc:=masked_line_collar g f fixed hm r j hmem
      exact ((lineAllNeighbors_iff _ _ _ _ _ p).mp hc).1
  have hpath : Reachable I.board (some 1) ⟨p,actual∪localFixed⟩ ⟨q,actual∪localFixed⟩ := by
    have he : q=(q.1,p.2):=Prod.ext rfl (Fin.ext (hq.trans hp.symm))
    rw [he]
    apply walk_horizontal (Finset.disjoint_union_left.mpr ⟨hactual,hfixed⟩)
    intro x _ _
    constructor
    · intro hwall
      have hh:=line_wall_rows (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape _ _ j.isLt).2.1
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) (x,p.2) hwall
      dsimp only at hh
      omega
    · intro hbox
      have hh:=hrow (x,p.2) hbox
      dsimp only at hh
      omega
  have hwalk:=e.reachable_withFixed hw (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) hout (s:=⟨p,actual⟩) (t:=⟨q,actual⟩) hpath
  have he (p : Cell I.width I.height) : e.extend outside ⟨p,actual⟩=maskedProfile g f fixed (e.cells p) :=
    masked_line_place g f fixed r j p
  rw [he,he] at hwalk
  exact hwalk

theorem masked_first_line_portal_walk (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) :
    let j : Fin (curve (key g r)).length:=⟨0,frontier_first_valid _⟩
    let p:=frontierLinePortal (fillerFlip (key g r) 0) (fillerSpan (key g r) 0) (filler_shape _ _ j.isLt).2.1
      (Inventory.initialPhase g r) (Inventory.targetPhase g r)
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineCorner g r j 0)))
      (maskedProfile g f fixed ((lineEmbedding g r j).cells p)) ∧
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells p))
      (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineCorner g r j 0))) := by
  dsimp only
  have hcorner : (lineCorner g r ⟨0,frontier_first_valid _⟩ 0).2.val=1 := by
    change (lineBaseCorner (fillerFlip (key g r) 0) (fillerSpan (key g r) 0) _ _ _ 0).2.val=1
    generalize hf : fillerFlip (key g r) 0=flip
    cases flip <;> rfl
  exact ⟨masked_line_outer_row g f fixed hm r _ _ _ hcorner rfl,masked_line_outer_row g f fixed hm r _ _ _ rfl hcorner⟩

theorem masked_corner_near (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) :
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub))
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.nearPortal (cornerKind (key g r) j.val)))) ∧
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.nearPortal (cornerKind (key g r) j.val))))
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub)) := by
  have hh:=(masked_corner_frame g f fixed hm r j).near_portal _
    ((ShortCorners.checked (cornerKind (key g r) j.val)).boxes_reserved (armPhase g f r (cornerIndex g r j)))
  rw [masked_corner_place,masked_corner_place] at hh
  exact hh

theorem masked_corner_far (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) :
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub))
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.farPortal (cornerKind (key g r) j.val)))) ∧
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.farPortal (cornerKind (key g r) j.val))))
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub)) := by
  have hh:=(masked_corner_frame g f fixed hm r j).far_portal _
    ((ShortCorners.checked (cornerKind (key g r) j.val)).boxes_reserved (armPhase g f r (cornerIndex g r j)))
  rw [masked_corner_place,masked_corner_place] at hh
  exact hh


end PushPuzzle.PushFS.Reduction.GateTileRouting
