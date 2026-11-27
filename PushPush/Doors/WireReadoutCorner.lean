/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutPins
public import PushPush.Doors.WireSourceForwardGeometry

/-! Full-stock readout at a normal private routing corner. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

private theorem cell_eq_of_raw {w h : ℕ} {p q : Cell w h}
    (he : (p.1.val, p.2.val) = (q.1.val, q.2.val)) : p = q :=
  Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

/-- The two original pins of a private corner close both lines through the real signal. -/
theorem corner_lineClosed (storage : Bool) (S : Stock I)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) (forward : Direction)
    (signal previous stop : Cell (layout storage I).width (layout storage I).height)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hc : Wire.Corner forward signal previous stop)
    (hprevious : (previous.1.val, previous.2.val) ∈ (layout storage I).pins)
    (hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins) :
    Wire.LineClosed {signal, previous, stop} s.boxes := by
  have hread : ∀ (d : Direction) (pin : Cell (layout storage I).width (layout storage I).height),
      (pin.1.val, pin.2.val) ∈ (layout storage I).pins →
      ∀ q ∈ s.boxes, d.lane q = d.lane pin → q = pin ∨ q = signal := by
    intro d pin hpin q hq hl
    rcases (S.pin_line_readout storage hs d pin q hpin hl).mp hq with he | he
    · exact Or.inl he
    · exact Or.inr (cell_eq_of_raw (he.trans hsignal.symm))
  intro d p hp q hq hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp ⊢
  rcases hp with he | he | he
  · subst p
    rcases Wire.corner_lane_cover hc d with hp | hp
    · rcases hread d previous hprevious q hq (hl.trans hp) with rfl | rfl <;> simp
    · rcases hread d stop hstop q hq (hl.trans hp) with rfl | rfl <;> simp
  · subst p
    rcases hread d previous hprevious q hq hl with rfl | rfl <;> simp
  · subst p
    rcases hread d stop hstop q hq hl with rfl | rfl <;> simp

/-- All genuine signal/pin slides at an internal corner have the two intended meanings. -/
theorem normal_corner_slide (storage : Bool) (S : Stock I)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) {d forward : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (signal previous stop : Cell (layout storage I).width (layout storage I).height)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hc : Wire.Corner forward signal previous stop)
    (hprevious : (previous.1.val, previous.2.val) ∈ (layout storage I).pins)
    (hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins ∨
      ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal) :
    n = 1 ∧
      ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) stop) ∨
        (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) signal)) := by
  have hclosed := S.corner_lineClosed storage hs forward signal previous stop hsignal hc hprevious hstop
  have hmember : r.cell ⟨1, by omega⟩ ∈ ({signal, previous, stop} : Finset _) := by
    rcases hfirst with hpin | hsig
    · obtain ⟨_, blocker, hblocker, ha, _⟩ := S.pin_slide storage hs r hn hk hinterior _ hpin rfl
      have hblockereq : blocker = signal := cell_eq_of_raw (hblocker.trans hsignal.symm)
      have hfirstlane : d.lane (r.cell ⟨1, by omega⟩) = d.lane signal := by
        rw [← hblockereq]
        exact (r.lane _).trans ((ha.lane.trans (r.lane _)).symm)
      rcases Wire.corner_lane_cover hc d with hp | hp
      · have he := pin_lane_unique storage I d _ previous hpin hprevious (hfirstlane.trans hp)
        simp [he]
      · have he := pin_lane_unique storage I d _ stop hpin hstop (hfirstlane.trans hp)
        simp [he]
    · have he := cell_eq_of_raw (hsig.trans hsignal.symm)
      simp [he]
  exact Wire.corner_slide r hn hk hinterior signal previous stop hc hclosed hmember

end PushPuzzle.PushPush.Doors.Source.Stock
