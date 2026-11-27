/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RectImages
public import PushFS.Gadgets.Wires.Catalog.SignalJoins

/-! Actual directional half-plane thresholds agree with native axial comparisons after ambient inverse D4. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


theorem undo_west_iff {W H : ℕ} (o : RectOrientation) (a p : PushFS.Cell W H) :
    ((o.undo W H).cells p).1.val≤((o.undo W H).cells a).1.val ↔
      TravelHigh (o.direction .west) (a.1.val,a.2.val) (p.1.val,p.2.val) := by
  have ha:=(congrArg Prod.fst (o.inverse.point_cells W H a)).symm
  have hp:=(congrArg Prod.fst (o.inverse.point_cells W H p)).symm
  rw [show ((o.undo W H).cells p).1.val=(o.inverse.point W H (p.1.val,p.2.val)).1 from hp,
    show ((o.undo W H).cells a).1.val=(o.inverse.point W H (a.1.val,a.2.val)).1 from ha]
  have haX:=a.1.isLt
  have haY:=a.2.isLt
  have hpX:=p.1.isLt
  have hpY:=p.2.isLt
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp [RectOrientation.inverse,RectOrientation.point,RectOrientation.width,RectOrientation.height,
      TravelHigh,RectOrientation.direction,RectOrientation.axis,AxisIsometry.refl,AxisIsometry.reflectX,
      AxisIsometry.reflectY,AxisIsometry.transpose,AxisIsometry.trans,GridIsometry.refl,GridIsometry.reflectX,
      GridIsometry.transpose,GridIsometry.trans,GridIsometry.transposeDirection,
      GridIsometry.reflectDirection] <;> omega

theorem undo_south_iff {W H : ℕ} (o : RectOrientation) (a p : PushFS.Cell W H) :
    ((o.undo W H).cells a).2.val≤((o.undo W H).cells p).2.val ↔
      TravelHigh (o.direction .south) (a.1.val,a.2.val) (p.1.val,p.2.val) := by
  have ha:=(congrArg Prod.snd (o.inverse.point_cells W H a)).symm
  have hp:=(congrArg Prod.snd (o.inverse.point_cells W H p)).symm
  rw [show ((o.undo W H).cells p).2.val=(o.inverse.point W H (p.1.val,p.2.val)).2 from hp,
    show ((o.undo W H).cells a).2.val=(o.inverse.point W H (a.1.val,a.2.val)).2 from ha]
  have haX:=a.1.isLt
  have haY:=a.2.isLt
  have hpX:=p.1.isLt
  have hpY:=p.2.isLt
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp [RectOrientation.inverse,RectOrientation.point,RectOrientation.width,RectOrientation.height,
      TravelHigh,RectOrientation.direction,RectOrientation.axis,AxisIsometry.refl,AxisIsometry.reflectX,
      AxisIsometry.reflectY,AxisIsometry.transpose,AxisIsometry.trans,GridIsometry.refl,GridIsometry.reflectX,
      GridIsometry.transpose,GridIsometry.trans,GridIsometry.transposeDirection,
      GridIsometry.reflectDirection] <;> omega

theorem undo_east_iff {W H : ℕ} (o : RectOrientation) (a p : PushFS.Cell W H) :
    ((o.undo W H).cells a).1.val≤((o.undo W H).cells p).1.val ↔
      TravelHigh (o.direction .east) (a.1.val,a.2.val) (p.1.val,p.2.val) := by
  have h:=undo_west_iff o p a
  apply h.trans
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> rfl

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
