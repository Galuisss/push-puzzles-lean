/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutEndpointsLaunch

/-! Horizontal motion on an original pin row has one exact signal landing. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

theorem stationary_at_pin_row (storage : Bool) (S : Stock I)
    {pin p : Cell (layout storage I).width (layout storage I).height}
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins) (hy : p.2 = pin.2)
    (hp : p ∈ S.stationary storage) : p = pin := by
  have hp := ((layout storage I).mem_raster _ _).mp hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · have he := pins_same_row storage I hp hpin (congrArg Fin.val hy)
        exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
      · exact False.elim (S.pin_row_nonpin_empty storage hpin (congrArg Fin.val hy)
          (Finset.mem_union_left _ (Finset.mem_union_left _ hp)))
    · exact False.elim (S.pin_row_nonpin_empty storage hpin (congrArg Fin.val hy)
        (Finset.mem_union_left _ (Finset.mem_union_right _ hp)))
  · exact False.elim (S.pin_row_nonpin_empty storage hpin (congrArg Fin.val hy)
      (Finset.mem_union_right _ hp))

theorem row_signal_slide (storage : Bool) (S : Stock I)
    (signal pin : Cell (layout storage I).width (layout storage I).height)
    (hsignal : (signal.1.val, signal.2.val) = S.signal)
    (hpin : (pin.1.val, pin.2.val) ∈ (layout storage I).pins)
    (hrow : signal.2 = pin.2) (hgap : pin.1.val + 3 ≤ signal.1.val)
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : S.Realizes storage s) {d : Direction} {n k : ℕ} (r : Slide d s n k)
    (hn : 0 < n) (hk : 0 < k) (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hfirst : r.cell ⟨1, by omega⟩ = signal) (hd : d = .east ∨ d = .west) :
    n = 1 ∧ d = .west ∧ Adjacent d (r.cell ⟨n + k, by omega⟩) pin := by
  have hsignallane : d.lane signal = d.lane pin := by
    rcases hd with rfl | rfl <;> exact congrArg Fin.val hrow
  obtain ⟨stop, hstop, ha⟩ := r.exists_stopper hn hinterior
  have hfirstlane : d.lane s.player = d.lane signal := by
    simpa only [hfirst] using (r.lane ⟨1, by omega⟩).symm
  have hstoplane : d.lane stop = d.lane pin :=
    ha.lane.trans ((r.lane _).trans (hfirstlane.trans hsignallane))
  have hp := r.position ⟨1, by omega⟩
  rw [hfirst] at hp
  change d.position signal = d.position s.player + (1 : ℕ) at hp
  have hl := r.position ⟨n + k, by omega⟩
  change d.position (r.cell ⟨n + k, by omega⟩) = d.position s.player + (n + k : ℕ) at hl
  have hstoppos := ha.position
  have hstopcell : stop = pin := by
    rcases (S.pin_line_readout storage hs d pin stop hpin hstoplane).mp hstop with hh | hh
    · exact hh
    · have hh : stop = signal := by
        have hh := hh.trans hsignal.symm
        exact Prod.ext (Fin.ext (congrArg Prod.fst hh)) (Fin.ext (congrArg Prod.snd hh))
      subst stop
      omega
  rw [hstopcell] at hstoppos ha
  have hdw : d = .west := by
    rcases hd with rfl | hd
    · simp only [Direction.position] at hp hl hstoppos
      omega
    · exact hd
  have hn1 : n = 1 := by
    apply Doors.slide_length_one r hn
    intro q haq hq
    have hqline : d.lane q = d.lane pin := by
      rw [hfirst] at haq
      exact haq.lane.trans hsignallane
    rcases (S.pin_line_readout storage hs d pin q hpin hqline).mp hq with hh | hh
    · subst q
      have hqa := haq.position
      rw [hfirst, hdw] at hqa
      simp only [Direction.position] at hqa
      omega
    · have hqx := congrArg Prod.fst (hh.trans hsignal.symm)
      have hqa := haq.position
      rw [hfirst, hdw] at hqa
      simp only [Direction.position] at hqa
      change q.1.val = signal.1.val at hqx
      omega
  exact ⟨hn1, hdw, ha⟩

end PushPuzzle.PushPush.Doors.Source.Stock
