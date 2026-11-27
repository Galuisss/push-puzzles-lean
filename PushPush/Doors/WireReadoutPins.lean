/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutRows

/-! Every moving original pin slides singly towards the unique active signal. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

theorem pin_line_readout (storage : Bool) (S : Stock I)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) (d : Direction)
    (pin p : Cell (layout storage I).width (layout storage I).height)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hlane : d.lane p = d.lane pin) :
    p ∈ s.boxes ↔ p = pin ∨ (p.1.val, p.2.val) = S.signal := by
  rw [hs, boxes, (layout storage I).mem_raster]
  have hread : (p.1.val, p.2.val) ∈ S.rawBoxes storage ↔
      (p.1.val, p.2.val) = (pin.1.val, pin.2.val) ∨ (p.1.val, p.2.val) = S.signal := by
    cases d
    · exact S.raw_column_at_pin storage hpin hlane
    · exact S.raw_row_at_pin storage hpin hlane
    · exact S.raw_column_at_pin storage hpin hlane
    · exact S.raw_row_at_pin storage hpin hlane
  have heq : (p.1.val, p.2.val) = (pin.1.val, pin.2.val) ↔ p = pin := by
    constructor
    · intro he
      exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
    · rintro rfl
      rfl
  simpa only [heq] using hread

/-- Any successful-prefix push of an original routing pin consumes that pin in one
single-box slide and stops next to the unique signal. -/
theorem pin_slide (storage : Bool) (S : Stock I)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) {d : Direction} {n k : ℕ} (r : Slide d s n k)
    (hn : 0 < n) (hk : 0 < k) (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (pin : Cell (layout storage I).width (layout storage I).height)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hfirst : r.cell ⟨1, by omega⟩ = pin) :
    n = 1 ∧ ∃ signal : Cell (layout storage I).width (layout storage I).height,
      (signal.1.val, signal.2.val) = S.signal ∧
      Adjacent d (r.cell ⟨n + k, by omega⟩) signal ∧
      r.boxes = insert (r.cell ⟨n + k, by omega⟩) (s.boxes.erase pin) := by
  obtain ⟨signal, hbox, ha⟩ := r.exists_stopper hn hinterior
  have hfirstlane := r.lane ⟨1, by omega⟩
  rw [hfirst] at hfirstlane
  have hsignallane : d.lane signal = d.lane pin :=
    ha.lane.trans ((r.lane _).trans hfirstlane.symm)
  have hread := (S.pin_line_readout storage hs d pin signal hpin hsignallane).mp hbox
  have hfirstpos := r.position ⟨1, by omega⟩
  change d.position (r.cell ⟨1, by omega⟩) = d.position s.player + (1 : ℕ) at hfirstpos
  rw [hfirst] at hfirstpos
  have hlastpos := r.position ⟨n + k, by omega⟩
  change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hlastpos
  have hsignalpos := ha.position
  have hsignal : (signal.1.val, signal.2.val) = S.signal := by
    rcases hread with rfl | hread
    · omega
    · exact hread
  have hn1 : n = 1 := by
    apply Doors.slide_length_one r hn
    intro q hq hqb
    have hqlane : d.lane q = d.lane pin := by simpa only [hfirst] using hq.lane
    rcases (S.pin_line_readout storage hs d pin q hpin hqlane).mp hqb with rfl | hqsig
    · have hp := hq.position
      rw [hfirst] at hp
      omega
    · have heq : q = signal := by
        have he := hqsig.trans hsignal.symm
        exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
      subst q
      have hp := hq.position
      rw [hfirst] at hp
      omega
  subst n
  refine ⟨rfl, signal, hsignal, ha, ?_⟩
  have hb := Doors.single_slide_boxes r
  have he : (⟨k + 1, by omega⟩ : Fin (1 + k + 1)) = ⟨1 + k, by omega⟩ :=
    Fin.ext (by change k + 1 = 1 + k; omega)
  rw [he, hfirst] at hb
  exact hb

end PushPuzzle.PushPush.Doors.Source.Stock
