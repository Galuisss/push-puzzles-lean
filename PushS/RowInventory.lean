/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.RowLabels

/-! Constant line inventories imply the occupancy-label dynamics used for signal trains. -/

@[expose] public section
namespace PushPuzzle.PushS.RowLabels

open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ}
  {d axis : Direction} {lane : ℕ} {s t : State w h}

private theorem run_on_line {n : ℕ} (run : Run B d s n) (hn : 0 < n)
    (hq : axis.lane (run.cell 1) = lane)
    (hz : axis.lane (run.cell ⟨n + 1, by omega⟩) = lane) (i : Fin (n + 2)) :
    axis.lane (run.cell i) = lane := by
  have hp := run.position 1
  have he := run.position ⟨n + 1, by omega⟩
  have hi := run.position i
  have lp := run.lane 1
  have le := run.lane ⟨n + 1, by omega⟩
  have li := run.lane i
  cases axis <;> cases d <;>
    simp only [Direction.lane, Direction.position, Fin.val_one] at * <;> omega

/-- A real move preserving the rail's box count changes its occupancy only by a full on-rail
push. Transverse moves retain its occupied set and may exchange physical box identities. -/
private theorem move_admissible_of_card (hm : Move B cap d s t)
    (hcard : (lineBoxes axis lane t).card = (lineBoxes axis lane s).card) :
    LineAdmissible B cap axis lane s t := by
  cases hm with
  | walk hv ha hf he hb =>
    exact ⟨d, .walk hv ha hf he hb, Or.inl (congrArg (fun boxes => boxes.filter
      (fun p => axis.lane p = lane)) hb)⟩
  | @push n hv hn hc run hp hb =>
    refine ⟨d, .push hv hn hc run hp hb, ?_⟩
    let q := run.cell 1
    let z := run.cell ⟨n + 1, by omega⟩
    have hqbox : q ∈ s.boxes := run.first_occupied hn
    have hzbox : z ∉ s.boxes := run.empty
    by_cases hq : axis.lane q = lane
    · by_cases hz : axis.lane z = lane
      · exact Or.inr ⟨⟨n, hn, run, hp, hb, run_on_line run hn hq hz⟩⟩
      · have hf : lineBoxes axis lane t = (lineBoxes axis lane s).erase q := by
          change t.boxes.filter _ = (s.boxes.filter _).erase q
          change t.boxes = insert z (s.boxes.erase q) at hb
          rw [hb, Finset.filter_insert, ite_eq_right hz, Finset.filter_erase]
        have hqm : q ∈ lineBoxes axis lane s := Finset.mem_filter.mpr ⟨hqbox, hq⟩
        rw [hf, Finset.card_erase_of_mem hqm] at hcard
        have := Finset.card_pos.mpr ⟨q, hqm⟩
        omega
    · have hqoff : q ∉ lineBoxes axis lane s :=
        fun h => hq (Finset.mem_filter.mp h).2
      change q ∉ s.boxes.filter (fun p => axis.lane p = lane) at hqoff
      by_cases hz : axis.lane z = lane
      · have hf : lineBoxes axis lane t = insert z (lineBoxes axis lane s) := by
          change t.boxes.filter _ = insert z (s.boxes.filter _)
          change t.boxes = insert z (s.boxes.erase q) at hb
          rw [hb, Finset.filter_insert, ite_eq_left hz, Finset.filter_erase,
            Finset.erase_eq_of_notMem hqoff]
        have hzm : z ∉ lineBoxes axis lane s :=
          fun h => hzbox (Finset.mem_filter.mp h).1
        rw [hf, Finset.card_insert_of_notMem hzm] at hcard
        omega
      · left
        change t.boxes.filter _ = s.boxes.filter _
        change t.boxes = insert z (s.boxes.erase q) at hb
        rw [hb, Finset.filter_insert, ite_eq_right hz, Finset.filter_erase,
          Finset.erase_eq_of_notMem hqoff]

/-- Every step with constant line inventory admits the occupancy update. -/
theorem step_admissible_of_card (hm : Step B cap s t)
    (hcard : (lineBoxes axis lane t).card = (lineBoxes axis lane s).card) :
    LineAdmissible B cap axis lane s t :=
  move_admissible_of_card hm.choose_spec hcard

end PushPuzzle.PushS.RowLabels
