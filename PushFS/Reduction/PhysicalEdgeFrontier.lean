/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
public import PushFS.Reduction.PhysicalEdgePhases
public import PushFS.Reduction.PhysicalWirePrepared
public import PushFS.Reduction.PhysicalGatePrepared

/-! The true source-path frontier supplies every ordinary and gate macro's actual selected neighboring phases. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes

/-- The one canonical physical wire phase of the original edge. -/
def edgePhase (v : CellPlan.Source) (e : ℕ) (goal : Bool) : Bool:=!(PhysicalTiles.bits v goal).getD e false

private theorem wire_on_edge (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped
    [] [])
    (e : ℕ) (j : Index v) (a : Catalog.Bitmap.Args) (htile : tile j=.inr a)
    (hp : HasPoint (Route.edgeSegments (refinedProgram v.1,e)) (position j)) :
    CellPlan.cell (v,position j)=some (.inr (e,a)) ∧Raster.wireAt (v.1,(e,position j))=some a.1 ∧
      ∀goal,PhysicalTiles.wirePhase a goal=edgePhase v e goal := by
  have hk:=key_eq j
  rw [htile] at hk
  obtain ⟨d,hc⟩:=PhysicalTiles.wire_code hk
  obtain ⟨hv,ho,hw,ha,hb⟩:=CellPlan.wire_sound hc
  have he : d=e:=Option.some.inj (ho.symm.trans
    (Raster.owner_unique hP hT ((Raster.vertexAt_none_iff _ _).mp hv) ((Route.edgeSegments_trace _ _ _).mp hp)))
  subst d
  refine ⟨hc,hw,?_⟩
  intro goal
  cases goal
  · exact ha
  · exact hb

theorem gate_record (v : CellPlan.Source) (j : Index v) (a : GateTileState) (htile : tile j=.inl a) :
    ∃g∈vertexRecords v.1,a=gateTileState (g,v.2) ∧position j=refinePoint g.point := by
  have hk:=key_eq j
  rw [htile] at hk
  obtain ⟨g,hc⟩:=PhysicalTiles.gate_code hk
  obtain ⟨hv,ha⟩:=CellPlan.gate_sound hc
  obtain ⟨hg,hpos⟩:=Raster.vertexAt_sound hv
  exact ⟨g,hg,ha,hpos.symm⟩

private theorem gate_edge_phase (v : CellPlan.Source) (g : VertexData) (r : Fin 3) (e : ℕ)
    (he : (g.ports.port r).edge=e) (goal : Bool) :
    PhysicalTiles.gatePhase (gateTileState (g,v.2)) goal r=
      if (g.ports.port r).dir then !(edgePhase v e goal) else edgePhase v e goal := by
  have hh:=gateSignals_wire_phase g.ports (PhysicalTiles.bits v goal) r
  rw [he] at hh
  cases goal <;> simpa only [PhysicalTiles.gatePhase,gateTileState,GateTileRouting.Inventory.initialPhase,
    GateTileRouting.Inventory.targetPhase,PhysicalTiles.bits,edgePhase,Bool.not_not,Bool.false_eq_true,ite_false,ite_true] using hh

private theorem wire_source_step {w : Word} {e : ℕ} {p q : GridRouting.Point} {k : Catalog.Kind}
    (hk : Raster.wireAt (w,(e,p))=some k) (hn : neighbor (Catalog.sourceDirection k).opposite p=some q) :
    UnitStep (Route.edgeSegments (refinedProgram w,e)) q p := by
  obtain ⟨q',hq,ha⟩:=(Raster.incoming_named _ _ _ _).mp (Raster.wireAt_source_arc hk)
  have he : q'=q:=Option.some.inj (hq.symm.trans hn)
  rw [he] at ha
  exact ⟨(Catalog.sourceDirection k),by simpa only [Direction.opposite_opposite] using ha,
    by simpa only [Direction.opposite_opposite] using neighbor_reverse hn⟩

private theorem wire_target_step {w : Word} {e : ℕ} {p q : GridRouting.Point} {k : Catalog.Kind}
    (hk : Raster.wireAt (w,(e,p))=some k) (hn : neighbor (Catalog.targetDirection k) p=some q) :
    UnitStep (Route.edgeSegments (refinedProgram w,e)) p q :=
  ⟨Catalog.targetDirection k,(Raster.outgoing_named _ _ _ _).mp (Raster.wireAt_target_arc hk),hn⟩

private theorem gate_role_step (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped
    [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) (e : ℕ) (he : (g.ports.port r).edge=e)
    (q : GridRouting.Point) (hn : neighbor (g.portDirection r) (refinePoint g.point)=some q) :
    if (g.ports.port r).dir then UnitStep (Route.edgeSegments (refinedProgram v.1,e)) q (refinePoint g.point)
      else UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (refinePoint g.point) q := by
  have ht:=vertexRecord_tangent hP hT hg r
  dsimp only at ht
  rw [he] at ht
  cases hd : (g.ports.port r).dir
  · simp only [hd,Bool.false_eq_true,ite_false] at ht ⊢
    exact ⟨g.portDirection r,ht,hn⟩
  · simp only [hd,ite_true] at ht ⊢
    obtain ⟨q',hq,ha⟩:=ht
    have heq : q'=q:=Option.some.inj (hq.symm.trans hn)
    rw [heq] at ha
    exact ⟨(g.portDirection r).opposite,ha,neighbor_reverse hn⟩

/-- The physical edge phase is low behind the current tile and high ahead of it. -/
structure EdgeFrontier (v : CellPlan.Source) (e : ℕ) (f : Fin (Fintype.card (Index v))→Bool)
    (current : Index v) : Prop where
  point : HasPoint (Route.edgeSegments (refinedProgram v.1,e)) (position current)
  fresh : f (numbering v current)=false
  previous : ∀j : Index v,UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (position j) (position current)→
    edgePhase v e (f (numbering v j))=false
  next : ∀j : Index v,UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (position current) (position j)→
    edgePhase v e (f (numbering v j))=true

/-- The exact source-path phase invariant supplies all literal ordinary preparation conditions. -/
theorem EdgeFrontier.wire_prepared {v : CellPlan.Source} {e : ℕ} {f : Fin (Fintype.card (Index v))→Bool}
    {current : Index v} (frontier : EdgeFrontier v e f current)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (htile : tile current=.inr a) (hpos : position current=(p.1.val,p.2.val)) : WirePrepared v f p a := by
  obtain ⟨hcode,hk,_⟩:=wire_on_edge v hP hT e current a htile frontier.point
  constructor
  · intro j b hj hn
    rw [←hpos] at hn
    have hs:=wire_source_step hk hn
    exact ((wire_on_edge v hP hT e j b hj hs.left_mem).2.2 _).trans (frontier.previous j hs)
  · intro j b hj hn
    rw [←hpos] at hn
    have hs:=wire_target_step hk hn
    exact ((wire_on_edge v hP hT e j b hj hs.right_mem).2.2 _).trans (frontier.next j hs)
  · intro j b hj r hn
    obtain ⟨g,hg,hb,hpoint⟩:=gate_record v j b hj
    subst b
    change neighbor (g.portDirection r) (position j)=some (p.1.val,p.2.val) at hn
    rw [hpoint,←hpos] at hn
    have he:=(CellPlan.gate_adjacent v hP hT hg r hn hcode).1
    have hs:=gate_role_step v hP hT g hg r e he (position current) hn
    rw [gate_edge_phase v g r e he]
    cases hd : (g.ports.port r).dir
    · simp only [hd,Bool.false_eq_true,ite_false] at hs ⊢
      rw [←hpoint] at hs
      exact frontier.previous j hs
    · simp only [hd,ite_true] at hs ⊢
      rw [←hpoint] at hs
      rw [frontier.next j hs]
      rfl

/-- The same literal frontier releases the changing gate port's real ordinary neighbor. -/
theorem EdgeFrontier.gate_released {v : CellPlan.Source} {e : ℕ} {f : Fin (Fintype.card (Index v))→Bool}
    {current : Index v} (frontier : EdgeFrontier v e f current)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (g : VertexData) (hg : g∈vertexRecords v.1)
    (hpos : position current=refinePoint g.point) (r : Fin 3) (he : (g.ports.port r).edge=e) :
    GatePortReleased v f g r := by
  intro j a htile hn
  have hs:=gate_role_step v hP hT g hg r e he (position j) hn
  rw [gateTileState_incoming]
  cases hd : (g.ports.port r).dir
  · simp only [hd,Bool.false_eq_true,ite_false] at hs ⊢
    rw [←hpos] at hs
    exact ((wire_on_edge v hP hT e j a htile hs.right_mem).2.2 _).trans (frontier.next j hs)
  · simp only [hd,ite_true] at hs ⊢
    rw [←hpos] at hs
    exact ((wire_on_edge v hP hT e j a htile hs.left_mem).2.2 _).trans (frontier.previous j hs)

namespace EdgeOrder
variable {v : CellPlan.Source} {e : ℕ} (order : EdgeOrder v e)

private theorem forward_predecessor (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) (j : Index v)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (position j) (position (order.index hP hT i))) :
    order.forwardMask hP hT i.val (numbering v j)=true := by
  obtain ⟨k,hk,hval⟩:=order.predecessor hP hT i j h
  rw [←hk]
  exact order.forward_before hP hT i k (by omega)

private theorem forward_successor (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) (j : Index v)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (position (order.index hP hT i)) (position j)) :
    order.forwardMask hP hT i.val (numbering v j)=false := by
  obtain ⟨k,hk,hval⟩:=order.successor hP hT i j h
  rw [←hk]
  exact order.forward_after hP hT i k (by omega)

private theorem backward_predecessor (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) (j : Index v)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (position j) (position (order.index hP hT i.rev))) :
    order.backwardMask hP hT i.val (numbering v j)=false := by
  obtain ⟨k,hk,hval⟩:=order.predecessor hP hT i.rev j h
  rw [←hk]
  exact order.backward_before hP hT i k (by omega)

private theorem backward_successor (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (order.sequence.length+1)) (j : Index v)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (position (order.index hP hT i.rev)) (position j)) :
    order.backwardMask hP hT i.val (numbering v j)=true := by
  obtain ⟨k,hk,hval⟩:=order.successor hP hT i.rev j h
  rw [←hk]
  exact order.backward_after hP hT i k (by omega)

/-- The forward physical traversal carries the strict phase frontier at every true tile. -/
theorem forward_frontier (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (ha : edgePhase v e false=true) (hb : edgePhase v e true=false) (i : Fin (order.sequence.length+1)) :
    EdgeFrontier v e (order.forwardMask hP hT i.val) (order.index hP hT i) where
  point:=by rw [order.index_position]; exact order.node_mem i
  fresh:=order.forward_current hP hT i
  previous j hs:=by rw [forward_predecessor order hP hT i j hs]; exact hb
  next j hs:=by rw [forward_successor order hP hT i j hs]; exact ha

/-- The reverse physical traversal carries the very same strict phase frontier. -/
theorem backward_frontier (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (ha : edgePhase v e false=false) (hb : edgePhase v e true=true) (i : Fin (order.sequence.length+1)) :
    EdgeFrontier v e (order.backwardMask hP hT i.val) (order.index hP hT i.rev) where
  point:=by rw [order.index_position]; exact order.node_mem i.rev
  fresh:=order.backward_current hP hT i
  previous j hs:=by rw [backward_predecessor order hP hT i j hs]; exact ha
  next j hs:=by rw [backward_successor order hP hT i j hs]; exact hb

end EdgeOrder
end PushPuzzle.PushFS.Reduction.PhysicalInventory
