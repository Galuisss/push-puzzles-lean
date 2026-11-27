/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockSource
import all Push.CornerDockReverse

/-! Maximum-slide cropping of a dock prefix whose entry remains open. -/

@[expose] public section
namespace PushPuzzle.PushPush.CornerDock

open PushFS (Cell State Direction Adjacent)

variable (r : Push.CornerDock.Input)
variable {s t : State r.outputWidth r.outputHeight} {d : Direction} {n k : ℕ}

theorem sourceState_boxes (s : State r.outputWidth r.outputHeight) (p : Cell r.width r.height) :
    p ∈ (r.sourceState s).boxes ↔ r.embed p ∈ s.boxes := by
  simpa only [PushS.mem_holes, not_not] using not_congr (r.sourceState_hole s p)

theorem embed_adjacent (d : Direction) (p q : Cell r.width r.height) :
    Adjacent d (r.embed p) (r.embed q) ↔ Adjacent d p q := by
  cases d <;> simp only [Adjacent, Push.CornerDock.Input.embed, Fin.ext_iff] <;> omega

/-- Invert the literal two-column source translation. -/
def cropCell (p : Cell r.outputWidth r.outputHeight) (hp : 2 ≤ p.1.val ∧ p.2.val < r.height) :
    Cell r.width r.height :=
  (⟨p.1.val - 2, by have := p.1.isLt; change p.1.val < r.width + 2 at this; omega⟩,
    ⟨p.2.val, hp.2⟩)

theorem embed_cropCell (p : Cell r.outputWidth r.outputHeight)
    (hp : 2 ≤ p.1.val ∧ p.2.val < r.height) : r.embed (cropCell r p hp) = p := by
  apply Prod.ext <;> apply Fin.ext
  · change p.1.val - 2 + 2 = p.1.val
    have := hp.1
    omega
  · rfl

def cropSlide (slide : Slide d s n k)
    (hin : ∀ i, 2 ≤ (slide.cell i).1.val ∧ (slide.cell i).2.val < r.height) :
    Slide d (r.sourceState s) n k where
  cell i := cropCell r (slide.cell i) (hin i)
  start := by
    have hs : r.SourceInside s := by
      change 2 ≤ s.player.1.val ∧ s.player.2.val < r.height
      rw [← slide.start]
      exact hin 0
    apply r.embed_injective
    rw [embed_cropCell]
    exact slide.start.trans (r.sourceState_player hs).symm
  adjacent i := (embed_adjacent r d _ _).mp (by
    simpa only [embed_cropCell] using slide.adjacent i)
  occupied i := (sourceState_boxes r s _).mpr (by rw [embed_cropCell]; exact slide.occupied i)
  clear i hi := slide.clear i (by simpa only [embed_cropCell] using (sourceState_boxes r s _).mp hi)
  stopped q hq := (sourceState_boxes r s q).mpr (slide.stopped (r.embed q)
    (by simpa only [embed_cropCell] using (embed_adjacent r d _ _).mpr hq))

private theorem cropSlide_boxes (slide : Slide d s n k)
    (hin : ∀ i, 2 ≤ (slide.cell i).1.val ∧ (slide.cell i).2.val < r.height)
    (hb : t.boxes = slide.boxes) : (r.sourceState t).boxes = (cropSlide r slide hin).boxes := by
  have hbefore (p : Cell r.width r.height) :
      p ∈ (cropSlide r slide hin).before ↔ r.embed p ∈ slide.before := by
    simp only [Slide.before, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (embed_cropCell r _ (hin _)).symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, r.embed_injective ((embed_cropCell r _ (hin _)).trans hi)⟩
  have hafter (p : Cell r.width r.height) :
      p ∈ (cropSlide r slide hin).after ↔ r.embed p ∈ slide.after := by
    simp only [Slide.after, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (embed_cropCell r _ (hin _)).symm⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, r.embed_injective ((embed_cropCell r _ (hin _)).trans hi)⟩
  ext p
  simp only [sourceState_boxes, hb, Slide.boxes, Finset.mem_union, Finset.mem_sdiff, hbefore, hafter]

/-- Every actual open-entry source action crops to one genuine maximum-game action. -/
private theorem sourceState_step
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (hm : SourceStep r s t) (he : r.entry ∈ PushS.holes t) :
    Step (r.sourceState s) (r.sourceState t) := by
  have hs := r.sourceInside_prefix hpre
  have ht := hm.2
  obtain ⟨⟨d, hm⟩, _⟩ := hm
  cases hm with
  | walk hv ha he0 hb =>
    have hm0 : r.SourceStep s t := ⟨⟨d, .walk
      ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩ ha (Finset.notMem_empty _) he0 hb⟩, ht⟩
    apply Step.of_unit_boxes (r.sourceState_step hpre hm0 he)
    change (r.sourceState t).boxes = (r.sourceState s).boxes
    ext p
    simp only [sourceState_boxes, hb]
  | push hv hn hk slide hp hb =>
    have hin := slide_inside r slide hn hk hpre hs hb ((PushS.mem_holes _).mp he)
    refine ⟨d, Move.push ?_ hn hk (cropSlide r slide hin) ?_ ?_⟩
    · intro hi
      have hi := (sourceState_boxes r s _).mp hi
      rw [r.sourceState_player hs] at hi
      exact hv hi
    · apply r.embed_injective
      exact (r.sourceState_player ht).trans (hp.trans (embed_cropCell r _ (hin _)).symm)
    · exact cropSlide_boxes r slide hin hb

theorem sourceState_between
    (hpre : Relation.ReflTransGen (SourceStep r) r.compile.initial s)
    (hr : Relation.ReflTransGen (SourceStep r) s t) (he : r.entry ∈ PushS.holes t) :
    Reachable (r.sourceState s) (r.sourceState t) := by
  revert he
  induction hr with
  | refl => intro _; exact .refl
  | tail hsu hm ih =>
    intro he
    have hprefix := source_prefix_expansion r (hpre.trans hsu)
    have hunit := source_step_expansion r hprefix hm
    have heu := r.entry_hole_source hunit he
    exact (ih heu).tail (sourceState_step r hprefix hm he)

end PushPuzzle.PushPush.CornerDock
