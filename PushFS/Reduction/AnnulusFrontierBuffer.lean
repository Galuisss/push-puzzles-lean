/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusFrontierGeometry

/-! True primitive coordinates, all owned labels and exact shared anchors of each actual buffered lead. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- Every actual lead pixel has its genuine primitive chain preimage and wall marker. -/
private theorem frontier_lead_preimage (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (role : Fin 3)
    (p : Cell (GateLead.piece kind n hn a b (frontierBufferIndex role)).width
      (GateLead.piece kind n hn a b (frontierBufferIndex role)).height) :
    ∃r : Chain.C n,
      (GateLead.dx kind n (frontierBufferIndex role)+p.1.val,
        GateLead.dy kind n (frontierBufferIndex role)+p.2.val)=
        (frontierOrientation kind role).coordinates (n+5) 21
          (GateLead.dx kind n (frontierBufferIndex role)) (GateLead.dy kind n (frontierBufferIndex role)) r ∧
      (p∈(GateLead.piece kind n hn a b (frontierBufferIndex role)).board.walls ↔r∈Chain.walls n hn) := by
  let o:=frontierOrientation kind role
  let pa:=gateClaim a role
  let pb:=gateClaim b role
  fin_cases role <;> cases kind
  all_goals
    obtain ⟨r,rfl⟩:=(o.axis (n+5) 21).geometry.cells.surjective p
    refine ⟨r,rfl,?_⟩
    exact (o.axis (n+5) 21).geometry.mem_walls (Chain.puzzle n hn pa pb).board r

private theorem frontier_lead_source_coordinates (kind : Bool) (n : ℕ) (hn : 2301≤n)
    (a b : Gates.Signals)
    (role : Fin 3) (l : Chain.Label n) :
    (GateLead.dx kind n (frontierBufferIndex role)+((GateLead.matching kind n hn a b (frontierBufferIndex role)).source l).1.val,
      GateLead.dy kind n (frontierBufferIndex role)+((GateLead.matching kind n hn a b (frontierBufferIndex role)).source l).2.val)=
      (frontierOrientation kind role).coordinates (n+5) 21
        (GateLead.dx kind n (frontierBufferIndex role)) (GateLead.dy kind n (frontierBufferIndex role))
        (Chain.position n hn (Chain.uniform n (gateClaim a role)) l) := by
  fin_cases role <;> cases kind <;> rfl

private theorem frontier_lead_target_coordinates (kind : Bool) (n : ℕ) (hn : 2301≤n)
    (a b : Gates.Signals)
    (role : Fin 3) (l : Chain.Label n) :
    (GateLead.dx kind n (frontierBufferIndex role)+((GateLead.matching kind n hn a b (frontierBufferIndex role)).target l).1.val,
      GateLead.dy kind n (frontierBufferIndex role)+((GateLead.matching kind n hn a b (frontierBufferIndex role)).target l).2.val)=
      (frontierOrientation kind role).coordinates (n+5) 21
        (GateLead.dx kind n (frontierBufferIndex role)) (GateLead.dy kind n (frontierBufferIndex role))
        (Chain.position n hn (Chain.uniform n (gateClaim b role)) l) := by
  fin_cases role <;> cases kind <;> rfl

def frontierBufferOffset (g : GateTileState) (role : Fin 3) : ℕ×ℕ :=
  ((bufferAtlas g).dx (frontierBufferIndex role),(bufferAtlas g).dy (frontierBufferIndex role))

theorem frontier_buffer_preimage (g : GateTileState) (role : Fin 3)
    (p : Cell ((bufferAtlas g).piece (frontierBufferIndex role)).width
      ((bufferAtlas g).piece (frontierBufferIndex role)).height) :
    ∃r : Chain.C 2301,
      ((frontierBufferOffset g role).1+p.1.val,(frontierBufferOffset g role).2+p.2.val)=
        (frontierOrientation g.core.isAND role).coordinates 2306 21
          (frontierBufferOffset g role).1 (frontierBufferOffset g role).2 r ∧
      (p∈((bufferAtlas g).piece (frontierBufferIndex role)).board.walls ↔r∈Chain.walls 2301 (by omega)) := by
  obtain ⟨r,hr,hw⟩:=frontier_lead_preimage g.core.isAND 2301 (by omega) g.core.initial g.core.target role p
  refine ⟨r,?_,hw⟩
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  apply Prod.ext
  · change (bufferOffset g.core.isAND).1+GateLead.dx g.core.isAND 2301 (frontierBufferIndex role)+p.1.val=
      (bufferOffset g.core.isAND).1+GateLead.dx g.core.isAND 2301 (frontierBufferIndex role)+
        (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells r).1.val
    change GateLead.dx g.core.isAND 2301 (frontierBufferIndex role)+p.1.val=
      GateLead.dx g.core.isAND 2301 (frontierBufferIndex role)+
        (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells r).1.val at hx
    omega
  · change (bufferOffset g.core.isAND).2+GateLead.dy g.core.isAND 2301 (frontierBufferIndex role)+p.2.val=
      (bufferOffset g.core.isAND).2+GateLead.dy g.core.isAND 2301 (frontierBufferIndex role)+
        (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells r).2.val
    change GateLead.dy g.core.isAND 2301 (frontierBufferIndex role)+p.2.val=
      GateLead.dy g.core.isAND 2301 (frontierBufferIndex role)+
        (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells r).2.val at hy
    omega

theorem frontier_buffer_source_coordinates (g : GateTileState) (role : Fin 3) (l : Chain.Label 2301) :
    ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).source l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).source l).2.val)=
      (frontierOrientation g.core.isAND role).coordinates 2306 21
        (frontierBufferOffset g role).1 (frontierBufferOffset g role).2
        (Chain.position 2301 (by omega) (Chain.uniform 2301 (gateClaim g.core.initial role)) l) := by
  have hh:=frontier_lead_source_coordinates g.core.isAND 2301 (by omega) g.core.initial g.core.target role l
  have hs:=congrArg (fun p : ℕ×ℕ=>((bufferOffset g.core.isAND).1+p.1,(bufferOffset g.core.isAND).2+p.2)) hh
  convert hs using 1 <;>
    simp only [frontierBufferOffset,bufferAtlas,StorageAtlas.translate,GateLead.atlas,
      RectOrientation.coordinates,Nat.add_assoc]; rfl

theorem frontier_buffer_target_coordinates (g : GateTileState) (role : Fin 3) (l : Chain.Label 2301) :
    ((frontierBufferOffset g role).1+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).1.val,
      (frontierBufferOffset g role).2+(((bufferAtlas g).matching (frontierBufferIndex role)).target l).2.val)=
      (frontierOrientation g.core.isAND role).coordinates 2306 21
        (frontierBufferOffset g role).1 (frontierBufferOffset g role).2
        (Chain.position 2301 (by omega) (Chain.uniform 2301 (gateClaim g.core.target role)) l) := by
  have hh:=frontier_lead_target_coordinates g.core.isAND 2301 (by omega) g.core.initial g.core.target role l
  have hs:=congrArg (fun p : ℕ×ℕ=>((bufferOffset g.core.isAND).1+p.1,(bufferOffset g.core.isAND).2+p.2)) hh
  convert hs using 1 <;>
    simp only [frontierBufferOffset,bufferAtlas,StorageAtlas.translate,GateLead.atlas,
      RectOrientation.coordinates,Nat.add_assoc]; rfl

/-- The actual placed buffered endpoint is the literal start anchor of its first annular line. -/
private theorem frontier_buffer_anchor (g : GateTileState) (role : Fin 3) :
    (frontierOrientation g.core.isAND role).coordinates 2306 21
      (frontierBufferOffset g role).1 (frontierBufferOffset g role).2 (frontierLeadAnchor 2301)=bufferedEnd (g.key role) := by
  have hh:=frontier_lead_coordinates g.core.isAND 2301 role (frontierLeadAnchor 2301)
  rw [frontier_lead_anchor] at hh
  have hx:=congrArg Prod.fst hh
  have hy:=congrArg Prod.snd hh
  apply Prod.ext
  · change (bufferOffset g.core.isAND).1+GateLead.dx g.core.isAND 2301 (frontierBufferIndex role)+
      (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells (frontierLeadAnchor 2301)).1.val=
      (bufferOffset g.core.isAND).1+(GateLead.portAnchor g.core.isAND 2301 role).1.val
    change GateLead.dx g.core.isAND 2301 (frontierBufferIndex role)+
      (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells (frontierLeadAnchor 2301)).1.val=
      (GateLead.portAnchor g.core.isAND 2301 role).1.val at hx
    omega
  · change (bufferOffset g.core.isAND).2+GateLead.dy g.core.isAND 2301 (frontierBufferIndex role)+
      (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells (frontierLeadAnchor 2301)).2.val=
      (bufferOffset g.core.isAND).2+(GateLead.portAnchor g.core.isAND 2301 role).2.val
    change GateLead.dy g.core.isAND 2301 (frontierBufferIndex role)+
      (((frontierOrientation g.core.isAND role).axis 2306 21).geometry.cells (frontierLeadAnchor 2301)).2.val=
      (GateLead.portAnchor g.core.isAND 2301 role).2.val at hy
    omega

/-- Both complete true frontier rectangles share exactly their far/near semantic anchors. -/
theorem frontier_shared_anchor (g : GateTileState) (role : Fin 3) (a b : Bool) :
    (frontierOrientation g.core.isAND role).coordinates 2306 21
      (frontierBufferOffset g role).1 (frontierBufferOffset g role).2 (frontierLeadAnchor 2301)=
      (frontierOrientation g.core.isAND role).coordinates
        (lineBase (fillerFlip (key g role) 0) (fillerSpan (key g role) 0)
          (filler_shape (key g role) 0 (frontier_first_valid _)).2.1 a b).width
        (lineBase (fillerFlip (key g role) 0) (fillerSpan (key g role) 0)
          (filler_shape (key g role) 0 (frontier_first_valid _)).2.1 a b).height
        (lineOffset (key g role) 0).1 (lineOffset (key g role) 0).2
        (lineNearAnchor (fillerFlip (key g role) 0) (fillerSpan (key g role) 0)
          (filler_shape (key g role) 0 (frontier_first_valid _)).2.1 a b) := by
  have hh:=line_near_anchor_coordinates (key g role) 0 (frontier_first_valid _) a b
  rw [frontier_first_orientation] at hh
  change (frontierOrientation g.core.isAND role).coordinates _ _ _ _ _=bufferedEnd (g.key role) at hh
  exact (frontier_buffer_anchor g role).trans hh.symm

end PushPuzzle.PushFS.Reduction.GateTileRouting
