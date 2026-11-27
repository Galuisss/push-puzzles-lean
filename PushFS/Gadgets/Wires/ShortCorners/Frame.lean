/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Geometry
public import PushFS.Gadgets.Wires.Polyline.ThinFrame

/-! Exact whole-template macros and mixed-buffer corner walks under literal physical collars. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners


set_option maxHeartbeats 0
set_option maxRecDepth 65536

theorem reserved_floor (k : Kind) : ∀p, (template k).reserved p=true→(template k).wall p=false := by
  cases k <;> decide +kernel

variable (k : Kind) {W H : ℕ}

/-- Only actual short-glyph walls and real prepared neighbor boxes constrain the ambient replay. -/
structure ThinFrame (e : GridEmbedding (width k) (height k) W H) (B : Board W H)
    (outside : Finset (Cell W H)) : Prop where
  walls : e.WallsAgree ((template k).board ∅) B
  outside_floor : Disjoint outside B.walls
  collar : Polyline.Frame.fixed e outside⊆(template k).neighbors

namespace ThinFrame
variable {k} {e : GridEmbedding (width k) (height k) W H} {B : Board W H}
    {outside : Finset (Cell W H)} (f : ThinFrame k e B outside)

include f

/-- Every owned box changes phase and the player returns to the exact ambient hub; all foreign boxes stay fixed. -/
theorem transition (a b : Bool) : Reachable B (some 1)
    (e.extend outside ((template k).state a)) (e.extend outside ((template k).state b)) :=
  e.reachable_withFixed f.walls
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor
    ((checked k).transition a b ∅ (Polyline.Frame.fixed e outside) f.collar)

theorem fixed_reserved : Polyline.Frame.fixed e outside⊆(template k).reservedCells := by
  intro p hp
  exact ((template k).mem_reserved _).mpr ((checked k).neighbors_reserved p (f.collar hp))

/-- The four exterior corner walks retain every actual owned or foreign box, including arbitrary mixed buffer phases. -/
theorem corners (actual : Finset (Cell (width k) (height k)))
    (ha : actual⊆(template k).reservedCells) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside ⟨(template k).hub,actual⟩)
      (e.extend outside ⟨(template k).corner i,actual⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(template k).corner i,actual⟩)
      (e.extend outside ⟨(template k).hub,actual⟩) := by
  let fixed:=Polyline.Frame.fixed e outside
  have hr : actual∪fixed⊆(template k).reservedCells := Finset.union_subset ha f.fixed_reserved
  have hw : Disjoint (actual∪fixed) (template k).walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hw
    have hc:=reserved_floor k p (((template k).mem_reserved _).mp (hr hp))
    exact Bool.noConfusion (hc.symm.trans (((template k).mem_walls _).mp hw))
  have hb:=(checked k).corner_reachable i ∅ (actual∪fixed) hr hw
  have ha':=(checked k).corner_to_hub i ∅ (actual∪fixed) hr hw
  exact ⟨e.reachable_withFixed f.walls
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor hb,
    e.reachable_withFixed f.walls
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mpr hp)
      (fun p hp=>(Polyline.Frame.mem_fixed e outside p).mp hp) f.outside_floor ha'⟩

end ThinFrame
end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
