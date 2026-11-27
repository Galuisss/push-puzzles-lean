/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceWaveAccess
public import PushS.FiniteSourceDockGeometry

/-! Every actual core dock is reached through its real B arm from player zero. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height FiniteGeometry.side

namespace CoreSite

private theorem core_arm_local_member (w : ℕ) (code : CellPlan.Code) (g : GateTileState)
    (hc : .core g ∈ localCodes w code) (role : Fin 3) (d : PrimitiveCode)
    (hd : d ∈ (armSpec w g role).codes) : d ∈ localCodes w code := by
  cases code with
  | none => simp [localCodes] at hc
  | some code =>
    cases code with
    | inl h =>
      have he := gate_core_origin w g h.2 hc
      subst g
      exact arm_code_mem_gateCodes w h.2 role d hd
    | inr q => exact ((wireSpec w q.2).core_not_mem g hc).elim

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

private def armPath (role : Fin 3) : PathSite w hw v (armSpec w c.gate role) where
  location := ((codes w v).get c.index).1
  member d hd := code_mem_of_local w v _ d
    (core_arm_local_member w _ c.gate (code_local w v _ c.mem_codes) role d hd)

private theorem normal_dock_access (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player)
      (PrimitiveProfile.state w hw v phase c.dockCell) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase c.dockCell)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  let p := c.armPath 1
  let i : Fin (armSpec w c.gate 1).segments.length := ⟨0,ArmBoundary.length_pos (w := w) (g := c.gate) (role := 1)⟩
  have ha := p.arm_event_dock_access hP hT phase (.line i)
  have he := c.dock_eq_B_arm_hub p i rfl rfl
  change Reachable _ _ _ (PrimitiveProfile.state w hw v phase
    ((p.line i).actualEmbedding.cells (Line.outerHub w (p.line i).atoms))) ∧
    Reachable _ _ (PrimitiveProfile.state w hw v phase
    ((p.line i).actualEmbedding.cells (Line.outerHub w (p.line i).atoms))) _ at ha
  rw [←he] at ha
  exact ha

theorem normal_anchorAccess (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) :
    c.AnchorAccess phase (inventory w hw v).board (inventory w hw v).player :=
  ⟨(c.normal_dock_access hP hT phase).1,
   (c.normal_dock_access hP hT (Function.update phase c.index true)).2⟩

theorem AnchorAccess.retarget {s : CoreSite w hw v} {phase : Fin (codes w v).length → Bool}
    {B B' : Board (width w v) (height w v)} {anchor : Cell (width w v) (height w v)}
    (W : s.AnchorAccess phase B anchor) (hB : B.walls = B'.walls) : s.AnchorAccess phase B' anchor :=
  ⟨W.enter.of_walls_eq hB,W.leave.of_walls_eq hB⟩

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
