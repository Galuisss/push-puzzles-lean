/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutCorner
public import PushPush.Doors.PhysicalState

/-! The five actual private wire corners have their full-stock two-way readout. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem wire_private_corner_geometry (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (corner : Fin 8)
    (hlo : 0 < corner.val) (hhi : corner.val < 6) :
    let hi := (List.mem_zipIdx' hei).1
    let he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
    let here : Fin 7 := ⟨corner.val, by omega⟩
    let before : Fin 7 := ⟨corner.val - 1, by omega⟩
    Wire.Corner (wireDirection (layout storage I) i e here)
      (wirePosition storage I i hi e he corner)
      (wireStop storage I i hi e he before)
      (wireStop storage I i hi e he here) := by
  intro hi he here before
  let j : Fin 5 := ⟨corner.val - 1, by omega⟩
  have hj : j.val + 1 = corner.val := by dsimp [j]; omega
  have hc := Wire.layout_private_corner (layout storage I) i e hi
    (wires_fit storage I he).1 (wires_fit storage I he).2 j
    (wirePosition storage I i hi e he corner)
    (wireStop storage I i hi e he before) (wireStop storage I i hi e he here)
  have hsource : ((wirePosition storage I i hi e he corner).1.val,
      (wirePosition storage I i hi e he corner).2.val) =
      ((layout storage I).wirePath i e).getD (j.val + 1) (0, 0) := by rw [hj]; rfl
  have hprevious : ((wireStop storage I i hi e he before).1.val,
      (wireStop storage I i hi e he before).2.val) =
      ((layout storage I).wirePins i e).getD j.val (0, 0) := by
    rw [wireStop_raw]
    simp only [wireStopRaw, show before.val < 6 by dsimp [before]; omega, ite_true]
    rfl
  have hstop : ((wireStop storage I i hi e he here).1.val,
      (wireStop storage I i hi e he here).2.val) =
      ((layout storage I).wirePins i e).getD (j.val + 1) (0, 0) := by
    rw [wireStop_raw, hj]
    simp only [wireStopRaw, show here.val < 6 by exact hhi, ite_true]
    rfl
  have hdir : Wire.privateDirection (layout storage I) i e j =
      wireDirection (layout storage I) i e here := by
    rcases corner with ⟨c, hc⟩
    change 0 < c at hlo
    change c < 6 at hhi
    have hcases : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [← hdir]
  exact hc hsource hprevious hstop

namespace Stock

variable {I : Instance}

/-- This classification is instantiated on the original indexed source wire and its actual pins. -/
theorem wire_internal_slide (storage : Bool) (S : Stock I) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (corner : Fin 8)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
    (hsignal : S.signal = wirePositionRaw (layout storage I) i e corner)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) {d : Direction} {n k : ℕ} (r : Slide d s n k)
    (hn : 0 < n) (hk : 0 < k) (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins ∨
      ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal) :
    let hi := (List.mem_zipIdx' hei).1
    let he : e ∈ (layout storage I).wires := (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem hi
    let here : Fin 7 := ⟨corner.val, by omega⟩
    let signal := wirePosition storage I i hi e he corner
    let stop := wireStop storage I i hi e he here
    n = 1 ∧
      ((d = wireDirection (layout storage I) i e here ∧ r.cell ⟨1, by omega⟩ = signal ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) stop) ∨
        (d = (wireDirection (layout storage I) i e here).opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) signal)) := by
  intro hi he here signal stop
  let before : Fin 7 := ⟨corner.val - 1, by omega⟩
  let previous := wireStop storage I i hi e he before
  have hprevpin : (previous.1.val, previous.2.val) ∈ (layout storage I).pins := by
    rw [show (previous.1.val, previous.2.val) = wireStopRaw (layout storage I) i e before from rfl]
    exact wireStopRaw_pin_mem storage I hei before (by dsimp [before]; omega)
  have hstoppin : (stop.1.val, stop.2.val) ∈ (layout storage I).pins := by
    rw [show (stop.1.val, stop.2.val) = wireStopRaw (layout storage I) i e here from rfl]
    exact wireStopRaw_pin_mem storage I hei here hhi
  exact S.normal_corner_slide storage hs r hn hk hinterior signal previous stop
    (by exact hsignal.symm) (wire_private_corner_geometry storage I hei corner hlo hhi)
    hprevpin hstoppin hfirst

end Stock
end PushPuzzle.PushPush.Doors.Source
