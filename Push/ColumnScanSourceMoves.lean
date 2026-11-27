/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSourceCrop

/-! Real source steps crop exactly; reader excursions preserve the entire cropped source state. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

private theorem embed_adjacent (d : Direction) (p q : Cell r.width r.height) :
    Adjacent d (r.embed p) (r.embed q) ↔ Adjacent d p q := by
  cases d <;> simp only [Adjacent, embed, Fin.ext_iff]

private theorem crop_boxes_eq {s t : State r.outputWidth r.outputHeight} (hb : t.boxes = s.boxes) :
    (r.cropState t).boxes = (r.cropState s).boxes := by
  ext p
  simp only [r.cropState_mem_boxes, hb]

private theorem source_exit_east {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hs : r.SourceInside s) (ht : r.width ≤ t.player.1.val) (ha : Adjacent d s.player t.player) :
    d = .east ∧ t.player.2.val = s.player.2.val := by
  have hsx := hs.1
  cases d <;> simp only [Adjacent] at ha
  all_goals first | omega | exact ⟨rfl, congrArg Fin.val ha.2⟩

private theorem source_entry_west {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hs : r.width ≤ s.player.1.val) (ht : r.SourceInside t) (ha : Adjacent d s.player t.player) :
    d = .west ∧ s.player.2.val = t.player.2.val := by
  have htx := ht.1
  cases d <;> simp only [Adjacent] at ha
  all_goals first | omega | exact ⟨rfl, (congrArg Fin.val ha.2).symm⟩

private theorem before_south_walk_crop
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hv : s.Valid r.compile.board) (ha : Adjacent d s.player t.player)
    (hf : t.player ∉ r.compile.board.walls) (he : t.player ∉ s.boxes) (hb : t.boxes = s.boxes)
    (htN : North r.width r.targetLevel t) (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hcrop : (r.cropState s).Valid r.sourceBoard) :
    r.cropState t = r.cropState s ∨ Step r.sourceBoard none (r.cropState s) (r.cropState t) := by
  have hmove : Move r.compile.board none d s t := .walk hv ha hf he hb
  have hstep : Step r.compile.board none s t := ⟨d, hmove⟩
  have hsf := (Relation.ReflTransGen.single hstep).trans htf
  have hboxes := r.crop_boxes_eq hb
  by_cases hs : r.SourceInside s
  · by_cases ht : r.SourceInside t
    · right
      refine ⟨d, .walk hcrop ?_ (by simp [sourceBoard]) ?_ hboxes⟩
      · apply (r.embed_adjacent d _ _).mp
        simpa only [r.cropPlayer_inside hs, r.cropPlayer_inside ht] using ha
      · rw [r.cropState_mem_boxes, r.cropPlayer_inside ht]
        exact he
    · left
      have htx := r.before_south_player_east (hr.tail ⟨hstep, htN⟩) htf hfx hfy hmove.valid_target ht
      obtain ⟨rfl, hy⟩ := r.source_exit_east hs htx ha
      have htDoor := r.before_south_outside_on_source_row (hr.tail ⟨hstep, htN⟩)
        htf hfx hfy hmove.valid_target ht (by have := hs.2; omega)
      have hplayer : (r.cropState s).player = r.sourceCorner := by
        apply r.embed_injective
        rw [r.cropPlayer_inside hs]
        apply Prod.ext <;> apply Fin.ext
        · have hx := congrArg (fun p => p.1.val) htDoor
          have ha' := ha.1
          change s.player.1.val = r.width - 1
          change t.player.1.val = r.width at hx
          omega
        · have hy' := congrArg (fun p => p.2.val) htDoor
          change s.player.2.val = r.height - 1
          change t.player.2.val = r.height - 1 at hy'
          omega
      exact State.ext ((r.cropPlayer_outside ht).trans hplayer.symm) hboxes
  · by_cases ht : r.SourceInside t
    · left
      have hsx := r.before_south_player_east hr hsf hfx hfy hv hs
      obtain ⟨rfl, hy⟩ := r.source_entry_west hsx ht ha
      have hsDoor := r.before_south_outside_on_source_row hr hsf hfx hfy hv hs
        (by have := ht.2; omega)
      have hplayer : (r.cropState t).player = r.sourceCorner := by
        apply r.embed_injective
        rw [r.cropPlayer_inside ht]
        apply Prod.ext <;> apply Fin.ext
        · have hx := congrArg (fun p => p.1.val) hsDoor
          have ha' := ha.1
          change t.player.1.val = r.width - 1
          change s.player.1.val = r.width at hx
          omega
        · have hy' := congrArg (fun p => p.2.val) hsDoor
          change t.player.2.val = r.height - 1
          change s.player.2.val = r.height - 1 at hy'
          omega
      exact State.ext (hplayer.trans (r.cropPlayer_outside hs).symm) hboxes
    · exact Or.inl (State.ext ((r.cropPlayer_outside ht).trans (r.cropPlayer_outside hs).symm) hboxes)

private theorem outside_run_avoids_source
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hv : s.Valid r.compile.board) (hn : 0 < n)
    (run : @Run r.outputWidth r.outputHeight r.compile.board d s n) (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : ¬r.SourceInside s) (hcrop : (r.cropState s).Valid r.sourceBoard)
    (i : Fin (n + 2)) : ¬((run.cell i).1.val < r.width ∧ (run.cell i).2.val < r.height) := by
  intro hi
  have hstep : Step r.compile.board none s t := ⟨d, .push hv hn trivial run hp hb⟩
  have hsf := (Relation.ReflTransGen.single hstep).trans htf
  have hsx := r.before_south_player_east hr hsf hfx hfy hv hs
  have hpos := run.position i
  have hlane := run.lane i
  have hd : d = .west := by
    have hix := hi.1
    cases d <;> simp only [Direction.position, Direction.lane] at hpos hlane <;> first | rfl | omega
  subst d
  simp only [Direction.lane, Direction.position] at hpos hlane
  have hsDoor := r.before_south_outside_on_source_row hr hsf hfx hfy hv hs
    (by have := hi.2; omega)
  have hfirst := run.position 1
  have hfirstlane := run.lane 1
  simp only [Direction.lane, Direction.position, Fin.val_one] at hfirst hfirstlane
  have hfirstCorner : run.cell 1 = r.embed r.sourceCorner := by
    have hx := congrArg (fun p => p.1.val) hsDoor
    have hy := congrArg (fun p => p.2.val) hsDoor
    change s.player.1.val = r.width at hx
    change s.player.2.val = r.height - 1 at hy
    apply Prod.ext <;> apply Fin.ext
    · change (run.cell 1).1.val = r.width - 1
      omega
    · exact hfirstlane.trans hy
  have hcorner : r.embed r.sourceCorner ∉ s.boxes := by
    have hempty := hcrop.2.2
    rw [r.cropPlayer_outside hs, r.cropState_mem_boxes] at hempty
    exact hempty
  exact hcorner (hfirstCorner ▸ run.first_occupied hn)

private theorem before_south_inside_push_crop
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hv : s.Valid r.compile.board) (hn : 0 < n)
    (run : @Run r.outputWidth r.outputHeight r.compile.board d s n) (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : r.SourceInside s) (hcrop : (r.cropState s).Valid r.sourceBoard) :
    Step r.sourceBoard none (r.cropState s) (r.cropState t) := by
  have hin := r.before_south_push_run_inside hr hv hn run hp hb htf hfx hfy hs
  let cell (i : Fin (n + 2)) : Cell r.width r.height :=
    (⟨(run.cell i).1.val, (hin i).1⟩, ⟨(run.cell i).2.val, (hin i).2⟩)
  have hcell (i : Fin (n + 2)) : r.embed (cell i) = run.cell i := by
    apply Prod.ext <;> apply Fin.ext <;> rfl
  have ht : r.SourceInside t := by
    change t.player.1.val < r.width ∧ t.player.2.val < r.height
    rw [hp]
    exact hin 1
  let small : Run r.sourceBoard d (r.cropState s) n := {
    cell := cell
    start := r.embed_injective ((hcell 0).trans (run.start.trans (r.cropPlayer_inside hs).symm))
    adjacent := fun i => (r.embed_adjacent d _ _).mp (by
      simpa only [hcell] using run.adjacent i)
    occupied := fun i => (r.cropState_mem_boxes s _).mpr (by rw [hcell]; exact run.occupied i)
    empty := fun hm => run.empty (by simpa only [hcell] using (r.cropState_mem_boxes s _).mp hm)
    floor := fun _ => Finset.notMem_empty _ }
  refine ⟨d, .push hcrop hn trivial small ?_ ?_⟩
  · apply r.embed_injective
    exact (r.cropPlayer_inside ht).trans (hp.trans (hcell 1).symm)
  · ext p
    simp only [r.cropState_mem_boxes, Finset.mem_insert, Finset.mem_erase]
    change (r.embed p ∈ t.boxes) ↔ p = cell ⟨n + 1, by omega⟩ ∨ p ≠ cell 1 ∧ r.embed p ∈ s.boxes
    rw [hb]
    simp only [Finset.mem_insert, Finset.mem_erase, ← hcell, r.embed_injective.eq_iff]
    have hne : r.embed p ≠ r.embed (cell 1) ↔ p ≠ cell 1 := not_congr r.embed_injective.eq_iff
    tauto

/-- Each real successful prefix step crops to a source step or an unchanged source state. -/
theorem before_south_step_crop
    {s t finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hm : NorthStep r.compile.board none r.width r.targetLevel s t)
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hcrop : (r.cropState s).Valid r.sourceBoard) :
    r.cropState t = r.cropState s ∨ Step r.sourceBoard none (r.cropState s) (r.cropState t) := by
  have hm0 : @Step r.outputWidth r.outputHeight r.compile.board none s t := hm.1
  obtain ⟨d, hmove⟩ := hm0
  cases hmove with
  | walk hv ha hf he hb => exact r.before_south_walk_crop hr hv ha hf he hb hm.2 htf hfx hfy hcrop
  | @push n hv hn _ run hp hb =>
    by_cases hs : r.SourceInside s
    · exact Or.inr (r.before_south_inside_push_crop hr hv hn run hp hb htf hfx hfy hs hcrop)
    · left
      have hout := r.outside_run_avoids_source hr hv hn run hp hb htf hfx hfy hs hcrop
      have ht : ¬r.SourceInside t := by
        intro ht
        change t.player.1.val < r.width ∧ t.player.2.val < r.height at ht
        exact hout 1 (by simpa only [← hp] using ht)
      apply State.ext ((r.cropPlayer_outside ht).trans (r.cropPlayer_outside hs).symm)
      ext p
      have hn1 : r.embed p ≠ run.cell 1 := by
        intro he
        have hsmall : (r.embed p).1.val < r.width ∧ (r.embed p).2.val < r.height :=
          ⟨p.1.isLt, p.2.isLt⟩
        exact hout 1 (he ▸ hsmall)
      have hnlast : r.embed p ≠ run.cell ⟨n + 1, by omega⟩ := by
        intro he
        have hsmall : (r.embed p).1.val < r.width ∧ (r.embed p).2.val < r.height :=
          ⟨p.1.isLt, p.2.isLt⟩
        exact hout _ (he ▸ hsmall)
      simp only [r.cropState_mem_boxes, hb, Finset.mem_insert, Finset.mem_erase, hnlast, false_or]
      exact ⟨And.right, fun hp => ⟨hn1, hp⟩⟩

end PushPuzzle.Push.ColumnScan.Input
