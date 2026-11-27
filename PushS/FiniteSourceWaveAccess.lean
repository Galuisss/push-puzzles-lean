/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathDockAccess

/-! Actual propagation waves have player-zero access to every physical event dock. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PathSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

theorem normal_arm_waveAccess {g : GateTileState} {role : Fin 3}
    (s : PathSite w hw v (armSpec w g role))
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (base : Fin (codes w v).length → Bool) :
    s.WaveAccess (armSpec_geometry w g role) base (inventory w hw v).board (inventory w hw v).player :=
  ⟨fun cut _ a _ => (s.arm_event_dock_access hP hT (s.wave base cut) a).1,
   fun cut _ a _ => (s.arm_event_dock_access hP hT (s.wave base (cut+1)) a).2⟩

theorem normal_wire_waveAccess {args : Gadgets.Wires.Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w args))
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (base : Fin (codes w v).length → Bool) :
    s.WaveAccess (wireSpec_geometry w args) base (inventory w hw v).board (inventory w hw v).player :=
  ⟨fun cut _ a _ => (s.wire_event_dock_access hP hT (s.wave base cut) a).1,
   fun cut _ a _ => (s.wire_event_dock_access hP hT (s.wave base (cut+1)) a).2⟩

theorem WaveAccess.retarget {P : PathSpec} {s : PathSite w hw v P} {G : P.Geometry w}
    {base : Fin (codes w v).length → Bool} {B B' : Board (width w v) (height w v)}
    {anchor : Cell (width w v) (height w v)} (W : s.WaveAccess G base B anchor)
    (hB : B.walls = B'.walls) : s.WaveAccess G base B' anchor :=
  ⟨fun cut hc a ha => (W.enter cut hc a ha).of_walls_eq hB,
   fun cut hc a ha => (W.leave cut hc a ha).of_walls_eq hB⟩

end PushPuzzle.PushS.FiniteSourceInventory.PathSite
