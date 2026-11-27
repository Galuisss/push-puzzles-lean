/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.UnitExpansion
public import Push.ColumnScanSourceMoves
import all Push.ColumnScanSourceMoves

/-! Crop complete maximum-slide rays while preserving their full stopping condition. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State Direction Adjacent)
open Push.StripFrontier

variable (r : Push.ColumnScan.Input)
variable {s t : State r.outputWidth r.outputHeight} {d : Direction} {n k : ℕ}

/-- The source embedding preserves the four labelled adjacencies. -/
theorem embed_adjacent (d : Direction) (p q : Cell r.width r.height) :
    Adjacent d (r.embed p) (r.embed q) ↔ Adjacent d p q := by
  cases d <;> simp only [Adjacent, Push.ColumnScan.Input.embed, Fin.ext_iff]

/-- Restrict every cell of one actual full ray to the original source rectangle. -/
def cropSlide (slide : Slide d s n k)
    (hin : ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height) :
    Slide d (r.cropState s) n k where
  cell i := (⟨(slide.cell i).1.val, (hin i).1⟩, ⟨(slide.cell i).2.val, (hin i).2⟩)
  start := by
    have hs : r.SourceInside s := by
      change s.player.1.val < r.width ∧ s.player.2.val < r.height
      rw [← slide.start]
      exact hin 0
    apply r.embed_injective
    exact slide.start.trans (r.cropPlayer_inside hs).symm
  adjacent i := by
    apply (embed_adjacent r d _ _).mp
    exact slide.adjacent i
  occupied i := (r.cropState_mem_boxes s _).mpr (slide.occupied i)
  clear i hi := slide.clear i ((r.cropState_mem_boxes s _).mp hi)
  stopped q hq := (r.cropState_mem_boxes s q).mpr (slide.stopped (r.embed q)
    ((embed_adjacent r d _ _).mpr hq))

private theorem cropSlide_embed (slide : Slide d s n k)
    (hin : ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height) (i) :
    r.embed ((cropSlide r slide hin).cell i) = slide.cell i := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

theorem cropSlide_before (slide : Slide d s n k)
    (hin : ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height)
    (p : Cell r.width r.height) :
    p ∈ (cropSlide r slide hin).before ↔ r.embed p ∈ slide.before := by
  simp only [Slide.before, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (cropSlide_embed r slide hin _).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, r.embed_injective ((cropSlide_embed r slide hin _).trans hi)⟩

theorem cropSlide_after (slide : Slide d s n k)
    (hin : ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height)
    (p : Cell r.width r.height) :
    p ∈ (cropSlide r slide hin).after ↔ r.embed p ∈ slide.after := by
  simp only [Slide.after, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (cropSlide_embed r slide hin _).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, r.embed_injective ((cropSlide_embed r slide hin _).trans hi)⟩

private theorem cropSlide_boxes (slide : Slide d s n k)
    (hin : ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height)
    (hb : t.boxes = slide.boxes) : (r.cropState t).boxes = (cropSlide r slide hin).boxes := by
  ext p
  simp only [r.cropState_mem_boxes, hb, Slide.boxes, Finset.mem_union, Finset.mem_sdiff,
    cropSlide_before, cropSlide_after]

/-- The cropped action remains a maximum slide, with the same run and travel lengths. -/
theorem crop_push (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hp : t.player = slide.cell ⟨1, by omega⟩)
    (hb : t.boxes = slide.boxes)
    (hin : ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height) :
    Move d (r.cropState s) (r.cropState t) := by
  have hs : r.SourceInside s := by
    change s.player.1.val < r.width ∧ s.player.2.val < r.height
    rw [← slide.start]
    exact hin 0
  have ht : r.SourceInside t := by
    change t.player.1.val < r.width ∧ t.player.2.val < r.height
    rw [hp]
    exact hin ⟨1, by omega⟩
  refine Move.push ?_ hn hk (cropSlide r slide hin) ?_ ?_
  · intro hc
    have hc := (r.cropState_mem_boxes s _).mp hc
    rw [r.cropPlayer_inside hs] at hc
    exact hv hc
  · apply r.embed_injective
    exact (r.cropPlayer_inside ht).trans (hp.trans (cropSlide_embed r slide hin _).symm)
  · exact cropSlide_boxes r slide hin hb

private theorem stage_run_inside {finish : State r.outputWidth r.outputHeight}
    (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hp : t.player = slide.cell ⟨1, by omega⟩) (hb : t.boxes = slide.boxes)
    (htf : PushFS.Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (j : Fin k)
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState (slide.stage j.castSucc))
    (hs : r.SourceInside (slide.stage j.castSucc)) :
    ∀ i, ((slide.stageRun hv j r.compile.board.goals).cell i).1.val < r.width ∧
      ((slide.stageRun hv j r.compile.board.goals).cell i).2.val < r.height := by
  have hv0 : s.Valid r.compile.board := ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩
  have hvj := (slide.stage_reachable hn hv r.compile.board.goals j.castSucc).valid hv0
  have hend : (⟨slide.cell ⟨1, by omega⟩, slide.boxes⟩ : State _ _) = t :=
    State.ext hp.symm hb.symm
  have hsf := (slide.stage_finish hn hk hv r.compile.board.goals j.succ).trans (hend ▸ htf)
  apply r.before_south_push_run_inside hpre hvj hn (slide.stageRun hv j r.compile.board.goals)
    rfl ?_ hsf hfx hfy hs
  change slide.stageBoxes j.succ =
    insert (slide.cell ⟨j.val + (n + 1), by omega⟩)
      ((slide.stageBoxes j.castSucc).erase (slide.cell ⟨j.val + 1, by omega⟩))
  have he := slide.stage_update hn hv j
  convert he using 1

/-- Every stage of a successful source-internal maximum slide stays in the original rectangle. -/
theorem inside_slide {finish : State r.outputWidth r.outputHeight}
    (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hp : t.player = slide.cell ⟨1, by omega⟩) (hb : t.boxes = slide.boxes)
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (htf : PushFS.Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : r.SourceInside s) :
    ∀ i, (slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height := by
  have hstage (j : Fin (k + 1)) :
      Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
        r.initialState.toState (slide.stage j) ∧ r.SourceInside (slide.stage j) := by
    induction j using Fin.induction with
    | zero => simpa only [slide.stage_zero] using And.intro hpre hs
    | succ j ih =>
      have hi := stage_run_inside r slide hn hk hv hp hb htf hfx hfy j ih.1 ih.2 1
      have hinside : r.SourceInside (slide.stage j.succ) := by
        change (slide.stage j.succ).player.1.val < r.width ∧
          (slide.stage j.succ).player.2.val < r.height
        simpa only [Slide.stage, Slide.stageRun, Fin.val_one, Fin.val_succ] using hi
      have hN : North r.width r.targetLevel (slide.stage j.succ) := by
        intro _
        have := r.targetLevel_lower
        have := hinside.2
        omega
      exact ⟨ih.1.tail ⟨⟨d, slide.stage_move hn hv j r.compile.board.goals⟩, hN⟩, hinside⟩
  let j : Fin k := ⟨k - 1, by omega⟩
  have hlast := stage_run_inside r slide hn hk hv hp hb htf hfx hfy j
    (hstage j.castSucc).1 (hstage j.castSucc).2 ⟨n + 1, by omega⟩
  have he : ((slide.stageRun hv j r.compile.board.goals).cell ⟨n + 1, by omega⟩) =
      slide.cell ⟨n + k, by omega⟩ := by
    apply congrArg slide.cell
    apply Fin.ext
    change k - 1 + (n + 1) = n + k
    omega
  rw [he] at hlast
  intro i
  have hip := slide.position i
  have hil := slide.lane i
  have hep := slide.position ⟨n + k, by omega⟩
  have hel := slide.lane ⟨n + k, by omega⟩
  have hi := i.isLt
  have hsx := hs.1
  have hsy := hs.2
  cases d <;> simp only [Direction.position, Direction.lane] at hip hil hep hel <;> omega

/-- A successful outside push cannot reach any original-source cell along its full ray. -/
theorem outside_slide_avoids {finish : State r.outputWidth r.outputHeight}
    (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hp : t.player = slide.cell ⟨1, by omega⟩) (hb : t.boxes = slide.boxes)
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (htf : PushFS.Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : ¬r.SourceInside s) (hcrop : (r.cropState s).player ∉ (r.cropState s).boxes) :
    ∀ i, ¬((slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height) := by
  have hm : Move d s t := .push hv hn hk slide hp hb
  have hsf := (hm.unit_expansion r.compile.board rfl).trans htf
  have hv0 : s.Valid r.compile.board := ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩
  have hsx := r.before_south_player_east hpre hsf hfx hfy hv0 hs
  intro i hi
  have hip := slide.position i
  have hil := slide.lane i
  have hd : d = .west := by
    cases d <;> simp only [Direction.position, Direction.lane] at hip hil <;> first | rfl | omega
  subst d
  have hy : s.player.2.val < r.height := by
    change (slide.cell i).2.val = s.player.2.val at hil
    exact hil ▸ hi.2
  have hdoor := r.before_south_outside_on_source_row hpre hsf hfx hfy hv0 hs hy
  have hf : slide.cell ⟨1, by omega⟩ = r.embed r.sourceCorner := by
    have hp1 := slide.position ⟨1, by omega⟩
    have hl1 := slide.lane ⟨1, by omega⟩
    rw [hdoor] at hp1 hl1
    apply Prod.ext <;> apply Fin.ext
    · change -((slide.cell ⟨1, by omega⟩).1.val : ℤ) = -(r.width : ℤ) + (1 : ℕ) at hp1
      change (slide.cell ⟨1, by omega⟩).1.val = r.width - 1
      omega
    · exact hl1
  have hfree : r.embed r.sourceCorner ∉ s.boxes := by
    rw [r.cropPlayer_outside hs, r.cropState_mem_boxes] at hcrop
    exact hcrop
  have hbox := slide.occupied ⟨0, hn⟩
  change slide.cell ⟨1, by omega⟩ ∈ s.boxes at hbox
  exact hfree (hf ▸ hbox)

/-- Reader excursions leave the source's exact player and entire box bitmap unchanged. -/
theorem outside_push_crop {finish : State r.outputWidth r.outputHeight}
    (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hp : t.player = slide.cell ⟨1, by omega⟩) (hb : t.boxes = slide.boxes)
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (htf : PushFS.Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : ¬r.SourceInside s) (hcrop : (r.cropState s).player ∉ (r.cropState s).boxes) :
    r.cropState t = r.cropState s := by
  have hout := outside_slide_avoids r slide hn hk hv hp hb hpre htf hfx hfy hs hcrop
  have ht : ¬r.SourceInside t := by
    intro ht
    change t.player.1.val < r.width ∧ t.player.2.val < r.height at ht
    rw [hp] at ht
    exact hout ⟨1, by omega⟩ ht
  apply State.ext ((r.cropPlayer_outside ht).trans (r.cropPlayer_outside hs).symm)
  ext p
  have hbefore : r.embed p ∉ slide.before := by
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    apply hout _
    rw [he]
    exact ⟨p.1.isLt, p.2.isLt⟩
  have hafter : r.embed p ∉ slide.after := by
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    apply hout _
    rw [he]
    exact ⟨p.1.isLt, p.2.isLt⟩
  simp only [r.cropState_mem_boxes, hb, Slide.boxes, Finset.mem_union, Finset.mem_sdiff,
    hbefore, hafter, not_false_eq_true, and_true, or_false]

/-- Every unit-expansion stage of a source-avoiding slide has the same cropped source. -/
theorem crop_stage (slide : Slide d s n k) (hs : ¬r.SourceInside s)
    (hout : ∀ i, ¬((slide.cell i).1.val < r.width ∧ (slide.cell i).2.val < r.height))
    (j : Fin (k + 1)) : r.cropState (slide.stage j) = r.cropState s := by
  have ht : ¬r.SourceInside (slide.stage j) := hout ⟨j.val, by omega⟩
  apply State.ext ((r.cropPlayer_outside ht).trans (r.cropPlayer_outside hs).symm)
  ext p
  have hbefore : r.embed p ∉ slide.before := by
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    apply hout _
    rw [he]
    exact ⟨p.1.isLt, p.2.isLt⟩
  have hsegment : r.embed p ∉ slide.segment j := by
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    apply hout _
    rw [he]
    exact ⟨p.1.isLt, p.2.isLt⟩
  simp only [r.cropState_mem_boxes, Slide.stage, Slide.stageBoxes, Finset.mem_union,
    Finset.mem_sdiff, hbefore, hsegment, not_false_eq_true, and_true, or_false]

/-- A full source-internal maximum slide expands entirely before the first southern visit. -/
theorem inside_slide_north {finish : State r.outputWidth r.outputHeight}
    (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hp : t.player = slide.cell ⟨1, by omega⟩) (hb : t.boxes = slide.boxes)
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (htf : PushFS.Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : r.SourceInside s) :
    Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel) s t := by
  have hin := inside_slide r slide hn hk hv hp hb hpre htf hfx hfy hs
  have hr := slide.unit_expansion_player hn hk hv r.compile.board.goals
    (fun p => p.1.val < r.width → p.2.val < r.targetLevel) (by
      intro i _
      have := (hin i).2
      have := r.targetLevel_lower
      omega)
  have he : (⟨slide.cell ⟨1, by omega⟩, slide.boxes⟩ : State _ _) = t := State.ext hp.symm hb.symm
  exact he ▸ hr

/-- An actual pre-needle action crops to one maximum-game action or the same source state. -/
theorem step_crop {finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (hm : Step s t) (htN : North r.width r.targetLevel t)
    (htf : PushFS.Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hcrop : (r.cropState s).player ∉ (r.cropState s).boxes) :
    r.cropState t = r.cropState s ∨ Step (r.cropState s) (r.cropState t) := by
  obtain ⟨d, hm⟩ := hm
  cases hm with
  | walk hv ha he hb =>
    have hv0 : s.Valid r.compile.board := ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩
    have hvc : (r.cropState s).Valid r.sourceBoard :=
      ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hcrop⟩
    have hc := r.before_south_walk_crop hpre hv0 ha (Finset.notMem_empty _) he hb htN
      htf hfx hfy hvc
    rcases hc with heq | hstep
    · exact Or.inl heq
    · right
      apply Step.of_unit_boxes hstep
      ext p
      simp only [r.cropState_mem_boxes, hb]
  | push hv hn hk slide hp hb =>
    by_cases hs : r.SourceInside s
    · exact Or.inr ⟨d, crop_push r slide hn hk hv hp hb
        (inside_slide r slide hn hk hv hp hb hpre htf hfx hfy hs)⟩
    · exact Or.inl (outside_push_crop r slide hn hk hv hp hb hpre htf hfx hfy hs hcrop)

end PushPuzzle.PushPush.ColumnReader
