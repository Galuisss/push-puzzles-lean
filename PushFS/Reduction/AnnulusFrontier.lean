/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusFrontierBuffer
public import PushFS.Reduction.AnnulusFrontierContract
public import PushFS.Reduction.AnnulusLineEndpoints

/-! Complete wall agreement and physical ownership at every actual buffered lead/first-line seam. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

private theorem frontier_walls (g : GateTileState) (role : Fin 3)
    (p : Cell ((bufferAtlas g).piece (frontierBufferIndex role)).width
      ((bufferAtlas g).piece (frontierBufferIndex role)).height)
    (q : Cell (linePiece (key g role) 0 (frontier_first_valid _)
      (Inventory.initialPhase g role) (Inventory.targetPhase g role)).width
      (linePiece (key g role) 0 (frontier_first_valid _)
        (Inventory.initialPhase g role) (Inventory.targetPhase g role)).height)
    (he : ((frontierBufferOffset g role).1+p.1.val,(frontierBufferOffset g role).2+p.2.val)=
      ((lineOffset (key g role) 0).1+q.1.val,(lineOffset (key g role) 0).2+q.2.val)) :
    p∈((bufferAtlas g).piece (frontierBufferIndex role)).board.walls ↔
      q∈(linePiece (key g role) 0 (frontier_first_valid _)
        (Inventory.initialPhase g role) (Inventory.targetPhase g role)).board.walls := by
  obtain ⟨r,hr,hw⟩:=frontier_buffer_preimage g role p
  let a:=Inventory.initialPhase g role
  let b:=Inventory.targetPhase g role
  let B:=lineBase (fillerFlip (key g role) 0) (fillerSpan (key g role) 0)
    (filler_shape (key g role) 0 (frontier_first_valid _)).2.1 a b
  let o:=lineOrientation (original (key g role) 0).travel (fillerFlip (key g role) 0)
  let e:=(o.axis B.width B.height).geometry
  obtain ⟨s,rfl⟩:=e.cells.surjective q
  have hs : (frontierOrientation g.core.isAND role).coordinates 2306 21
      (frontierBufferOffset g role).1 (frontierBufferOffset g role).2 r=
      o.coordinates B.width B.height (lineOffset (key g role) 0).1 (lineOffset (key g role) 0).2 s :=
    hr.symm.trans he
  dsimp only [o] at hs
  rw [frontier_first_orientation] at hs
  have hrel:=frontier_relative (fillerFlip (key g role) 0) a b
    (frontierOrientation g.core.isAND role)
    (frontierBufferOffset g role).1 (frontierBufferOffset g role).2
    (lineOffset (key g role) 0).1 (lineOffset (key g role) 0).2 r s hs
    (frontier_shared_anchor g role a b)
  exact hw.trans ((frontier_walls_of_relative 2301 (fillerSpan (key g role) 0) (by omega)
    (filler_shape (key g role) 0 (frontier_first_valid _)).2.1
    (fillerFlip (key g role) 0) a b r s hrel.1 hrel.2).trans (e.mem_walls B.board s).symm)

private theorem frontier_sources (g : GateTileState) (role : Fin 3) (l : Chain.Label 2301)
    (k : lineLabels (fillerFlip (key g role) 0) (fillerSpan (key g role) 0)) :
    ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).source l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).source l).2.val)≠
    ((lineOffset (key g role) 0).1+((lineSlotMatching (key g role) 0 (frontier_first_valid _)
      (Inventory.initialPhase g role) (Inventory.targetPhase g role)).source k).1.val,
      (lineOffset (key g role) 0).2+((lineSlotMatching (key g role) 0 (frontier_first_valid _)
        (Inventory.initialPhase g role) (Inventory.targetPhase g role)).source k).2.val) := by
  rw [frontier_buffer_source_coordinates,line_source_coordinates,frontier_first_orientation]
  exact frontier_disjoint (fillerFlip (key g role) 0) (Inventory.initialPhase g role)
    (Inventory.targetPhase g role) (Inventory.initialPhase g role)
    (frontierOrientation g.core.isAND role)
    (frontierBufferOffset g role).1 (frontierBufferOffset g role).2
    (lineOffset (key g role) 0).1 (lineOffset (key g role) 0).2 _ _
    (Polyline.chain_phase_bounds 2301 (by omega) (Inventory.initialPhase g role) l).2
    (line_source_bounds _ _ _ _ _ k).1 (frontier_shared_anchor g role _ _)

private theorem frontier_targets (g : GateTileState) (role : Fin 3) (l : Chain.Label 2301)
    (k : lineLabels (fillerFlip (key g role) 0) (fillerSpan (key g role) 0)) :
    ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).2.val)≠
    ((lineOffset (key g role) 0).1+((lineSlotMatching (key g role) 0 (frontier_first_valid _)
      (Inventory.initialPhase g role) (Inventory.targetPhase g role)).target k).1.val,
      (lineOffset (key g role) 0).2+((lineSlotMatching (key g role) 0 (frontier_first_valid _)
        (Inventory.initialPhase g role) (Inventory.targetPhase g role)).target k).2.val) := by
  rw [frontier_buffer_target_coordinates,line_target_coordinates,frontier_first_orientation]
  exact frontier_disjoint (fillerFlip (key g role) 0) (Inventory.initialPhase g role)
    (Inventory.targetPhase g role) (Inventory.targetPhase g role)
    (frontierOrientation g.core.isAND role)
    (frontierBufferOffset g role).1 (frontierBufferOffset g role).2
    (lineOffset (key g role) 0).1 (lineOffset (key g role) 0).2 _ _
    (Polyline.chain_phase_bounds 2301 (by omega) (Inventory.targetPhase g role) l).2
    (line_target_bounds _ _ _ _ _ k).1 (frontier_shared_anchor g role _ _)

namespace Inventory

/-- Every actual buffered-lead/first-line contact has equal walls and distinct complete inventories. -/
theorem frontierContactProofs (g : GateTileState) : FrontierContactProofs g where
  walls i role j hi hj p q he := by
    have hi' : i=frontierBufferIndex role := Fin.ext hi
    have hj' : j=⟨0,frontier_first_valid _⟩ := Fin.ext hj
    subst i
    subst j
    exact frontier_walls g role p q he
  sources i role j hi hj l k := by
    have hi' : i=frontierBufferIndex role := Fin.ext hi
    have hj' : j=⟨0,frontier_first_valid _⟩ := Fin.ext hj
    subst i
    subst j
    exact frontier_sources g role l k
  targets i role j hi hj l k := by
    have hi' : i=frontierBufferIndex role := Fin.ext hi
    have hj' : j=⟨0,frontier_first_valid _⟩ := Fin.ext hj
    subst i
    subst j
    exact frontier_targets g role l k

end Inventory
end PushPuzzle.PushFS.Reduction.GateTileRouting
