/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreRailFloor
public import PushS.FiniteSourceFloor

/-! Every literal core normal-slot rail and support is floor in the complete emitted source board. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateMatching
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem core_local_clear (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (g : GateTileState)
    (hc : .core g ∈ localCodes w code)
    (a : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hfloor : a ∉ ((PrimitiveCode.core g).instanceOf w hw).board.walls)
    (hlane : ∀ role, Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).world w hw a) →
      SameLane (PortAnnulus.innerDirection role)
        (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
        ((PrimitiveCode.core g).world w hw a))
    (d : PrimitiveCode) (hd : d ∈ localCodes w code)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    (PrimitiveCode.core g).world w hw a ≠ d.world w hw p := by
  cases code with
  | none => simp [localCodes] at hc
  | some code =>
    cases code with
    | inl h =>
      have he := gate_core_origin w g h.2 hc
      subst g
      exact core_cell_gate_wall_clear w hw h.2 a hfloor hlane d hd p hp
    | inr q => exact ((wireSpec w q.2).core_not_mem g hc).elim

private theorem primitive_core_cell_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (a : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hfloor : a ∉ ((PrimitiveCode.core g).instanceOf w hw).board.walls)
    (hlane : ∀ role, Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).world w hw a) →
      SameLane (PortAnnulus.innerDirection role)
        (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
        ((PrimitiveCode.core g).world w hw a))
    (t : GridRouting.Point × PrimitiveCode) (ht : t ∈ codes w v)
    (p : Cell (t.2.instanceOf w hw).width (t.2.instanceOf w hw).height)
    (hp : p ∈ (t.2.instanceOf w hw).board.walls) :
    macroShift w pos ((PrimitiveCode.core g).world w hw a) ≠ macroShift w t.1 (t.2.world w hw p) := by
  have hcl := code_local w v (pos,.core g) hc
  have htl := code_local w v t ht
  apply macro_actor_wall_ne w pos t.1 _ _
    (local_world_bounds w hw (.core g) (localCodes_fits w hw _ hcl) a)
    (local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) p)
    (fun face hf => ((interior_not_collar w face (core_window_interior w hw g a)) hf).elim)
    (local_wall_collar_off_lane w hw _ t.2 htl p hp)
  intro hpos
  apply core_local_clear w hw (CellPlan.cell (v,pos)) g hcl a hfloor hlane t.2 _ p hp
  simpa only [hpos] using htl

private theorem core_cell_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (a : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height)
    (hfloor : a ∉ ((PrimitiveCode.core g).instanceOf w hw).board.walls)
    (hlane : ∀ role, Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
      ((PrimitiveCode.core g).world w hw a) →
      SameLane (PortAnnulus.innerDirection role)
        (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
        ((PrimitiveCode.core g).world w hw a))
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos ((PrimitiveCode.core g).world w hw a)) :
    q ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  have he' := congrArg coordinates he
  rw [placed_wall_coordinates,hq] at he'
  exact primitive_core_cell_wall_ne w hw v pos g hc a hfloor hlane _ (List.get_mem _ _) p hp he'.symm

theorem andRail_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (hg : g.core.isAND = true) (l : AndLabel w) (i : Fin (andTravel l+3))
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (coreWorld w (andLine w l i))) :
    q ∉ (inventory w hw v).walls := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · cases hg
  · exact core_cell_floor w hw v pos _ hc (andLine w l i) (andLine_floor w hw l i)
      (fun role h => andRail_outward_lane w hw role l i h) q hq

theorem orRail_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (hg : g.core.isAND = false) (l : OrLabel w) (i : Fin 4)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (coreWorld w (orLine w l i))) :
    q ∉ (inventory w hw v).walls := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · exact core_cell_floor w hw v pos _ hc (orLine w l i) (orLine_floor w hw l i)
      (fun role h => orRail_outward_lane w hw role l i h) q hq
  · cases hg

/-- The first arm's inward support is the actual outer core box's inner support cell. -/
theorem core_port_support_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (role : Fin 3) (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos
      (Line.along w (PortAnnulus.innerDirection role).opposite (corePort w g.core.isAND role) 1)) :
    q ∉ (inventory w hw v).walls := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · apply orRail_floor w hw v pos _ hc rfl (orPortLabel w role) (orPortSupportIndex role) q
    exact hq.trans (congrArg (macroShift w pos) (orPortSupport_world w hw role).symm)
  · apply andRail_floor w hw v pos _ hc rfl (andPortLabel w role) (andPortSupportIndex w role) q
    exact hq.trans (congrArg (macroShift w pos) (andPortSupport_world w hw role).symm)

theorem andFullRail_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (hg : g.core.isAND = true) (r : FiniteCoreRails.AndRail) (i : Fin (r.count w))
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (coreWorld w (r.cell w i))) :
    q ∉ (inventory w hw v).walls := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · cases hg
  · exact core_cell_floor w hw v pos _ hc (r.cell w i) (FiniteCoreRails.andRail_floor w hw r i)
      (fun role h => andFullRail_outward_lane w hw role r i h) q hq

theorem orFullRail_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos : GridRouting.Point) (g : GateTileState) (hc : (pos,PrimitiveCode.core g) ∈ codes w v)
    (hg : g.core.isAND = false) (r : FiniteCoreRails.OrRail) (i : Fin (r.count w))
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w pos (coreWorld w (r.cell w i))) :
    q ∉ (inventory w hw v).walls := by
  rcases g with ⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩
  cases kind
  · exact core_cell_floor w hw v pos _ hc (r.cell w i) (FiniteCoreRails.orRail_floor w hw r i)
      (fun role h => orFullRail_outward_lane w hw role r i h) q hq
  · cases hg

end PushPuzzle.PushS.FiniteSourceInventory
