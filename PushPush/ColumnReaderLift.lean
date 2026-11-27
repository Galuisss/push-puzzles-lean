/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderCrop
public import PushPush.Corners
public import Push.ColumnScanSourceLiftLayout
import all Push.ColumnScanForward
import all Push.ColumnScanForwardColumns

/-! Lift source maximum slides into the fixed reader extension with unchanged stopping cells. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State Direction Adjacent)

variable (r : Push.ColumnScan.Input)

/-- The extension outside the copied source has the same inventory for every source state. -/
private theorem liftState_outside (s t : State r.width r.height)
    (q : Cell r.outputWidth r.outputHeight)
    (hq : ¬(q.1.val < r.width ∧ q.2.val < r.height)) :
    q ∈ (r.liftState s).boxes ↔ q ∈ (r.liftState t).boxes := by
  have hoff (u : State r.width r.height) : q ∉ (PushS.holes u).image r.embed := by
    intro hp
    obtain ⟨p, _, he⟩ := Finset.mem_image.mp hp
    apply hq
    rw [← he]
    exact ⟨p.1.isLt, p.2.isLt⟩
  simp only [Push.ColumnScan.Input.liftState, Finset.mem_compl, Push.ColumnScan.Input.liftEmpty,
    Finset.mem_union, hoff, false_or]

/-- Every new neighbour of a noncorner source endpoint is a fixed full cell of the extension. -/
theorem outside_neighbor_full (s : State r.width r.height) {p : Cell r.width r.height}
    {q : Cell r.outputWidth r.outputHeight} {d : Direction} (hp : p ≠ r.sourceCorner)
    (ha : Adjacent d (r.embed p) q) (hq : ¬(q.1.val < r.width ∧ q.2.val < r.height)) :
    q ∈ (r.liftState s).boxes := by
  apply Finset.mem_compl.mpr
  intro hh
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨z, _, he⟩ := Finset.mem_image.mp hh
    apply hq
    rw [← he]
    exact ⟨z.1.isLt, z.2.isLt⟩
  · have hE := (Finset.mem_sdiff.mp hh).1
    have hpx := p.1.isLt
    have hpy := p.2.isLt
    cases d with
    | north =>
      simp only [Adjacent, Push.ColumnScan.Input.embed, Fin.ext_iff] at ha
      apply hq
      constructor <;> omega
    | west =>
      simp only [Adjacent, Push.ColumnScan.Input.embed, Fin.ext_iff] at ha
      apply hq
      constructor <;> omega
    | south =>
      simp only [Adjacent, Push.ColumnScan.Input.embed, Fin.ext_iff] at ha
      have hy : q.2.val = r.height := by
        by_contra hn
        apply hq
        constructor <;> omega
      have hf := r.needle_far_south p.1
      change r.height + max r.sourceHoles r.width < r.needleLevel p.1 at hf
      apply r.column_gap p.1 q ha.1 (by omega) (by omega) hE
    | east =>
      simp only [Adjacent, Push.ColumnScan.Input.embed, Fin.ext_iff] at ha
      have hx : q.1.val = r.width := by
        by_contra hn
        apply hq
        constructor <;> omega
      rcases (r.separator_holes q hx).mp hE with he | he | he
      · have hy := congrArg (fun z => z.2.val) he
        change q.2.val = r.height - 1 at hy
        apply hp
        apply Prod.ext <;> apply Fin.ext
        · change p.1.val = r.width - 1
          omega
        · exact ha.2.symm.trans hy
      · have hy := congrArg (fun z => z.2.val) he
        change q.2.val = r.height at hy
        omega
      · have hy := congrArg (fun z => z.2.val) he
        change q.2.val = r.outputHeight - 1 at hy
        have := r.length_ge_seven
        unfold Push.ColumnScan.Input.outputHeight at hy
        omega

variable {s t : State r.width r.height} {d : Direction} {n k : ℕ}

/-- A complete source ray lifts without extending its maximum sliding distance. -/
def liftSlide (slide : Slide d s n k)
    (hlast : slide.cell ⟨n + k, by omega⟩ ≠ r.sourceCorner) :
    Slide d (r.liftState s) n k where
  cell i := r.embed (slide.cell i)
  start := congrArg r.embed slide.start
  adjacent i := (embed_adjacent r d _ _).mpr (slide.adjacent i)
  occupied i := (r.liftState_mem_boxes s _).mpr (slide.occupied i)
  clear i hi := slide.clear i ((r.liftState_mem_boxes s _).mp hi)
  stopped q hq := by
    by_cases hi : q.1.val < r.width ∧ q.2.val < r.height
    · let p : Cell r.width r.height := (⟨q.1.val, hi.1⟩, ⟨q.2.val, hi.2⟩)
      have he : r.embed p = q := by apply Prod.ext <;> apply Fin.ext <;> rfl
      have ha : Adjacent d (slide.cell ⟨n + k, by omega⟩) p :=
        (embed_adjacent r d _ _).mp (he ▸ hq)
      exact he ▸ (r.liftState_mem_boxes s p).mpr (slide.stopped p ha)
    · exact outside_neighbor_full r s hlast hq hi

private theorem liftSlide_before (slide : Slide d s n k)
    (hlast : slide.cell ⟨n + k, by omega⟩ ≠ r.sourceCorner) :
    (liftSlide r slide hlast).before = slide.before.image r.embed := by
  simp only [Slide.before, liftSlide, Finset.image_image, Function.comp_def]

private theorem liftSlide_after (slide : Slide d s n k)
    (hlast : slide.cell ⟨n + k, by omega⟩ ≠ r.sourceCorner) :
    (liftSlide r slide hlast).after = slide.after.image r.embed := by
  simp only [Slide.after, liftSlide, Finset.image_image, Function.comp_def]

theorem liftSlide_boxes (slide : Slide d s n k)
    (hlast : slide.cell ⟨n + k, by omega⟩ ≠ r.sourceCorner) (hb : t.boxes = slide.boxes) :
    (r.liftState t).boxes = (liftSlide r slide hlast).boxes := by
  ext q
  by_cases hi : q.1.val < r.width ∧ q.2.val < r.height
  · let p : Cell r.width r.height := (⟨q.1.val, hi.1⟩, ⟨q.2.val, hi.2⟩)
    have he : r.embed p = q := by apply Prod.ext <;> apply Fin.ext <;> rfl
    rw [← he]
    simp only [r.liftState_mem_boxes, Slide.boxes, Finset.mem_union, Finset.mem_sdiff,
      liftSlide_before, liftSlide_after, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right, hb]
  · have hoff (S : Finset (Cell r.width r.height)) : q ∉ S.image r.embed := by
      intro hm
      obtain ⟨p, _, he⟩ := Finset.mem_image.mp hm
      apply hi
      rw [← he]
      exact ⟨p.1.isLt, p.2.isLt⟩
    simp only [Slide.boxes, Finset.mem_union, Finset.mem_sdiff, liftSlide_before,
      liftSlide_after, hoff, not_false_eq_true, and_true, or_false]
    exact liftState_outside r t s q hi

/-- A source action lifts with its full original sliding distance when its target corner is free. -/
private theorem lift_source_move (hm : Move d s t) (ht : r.sourceCorner ∉ t.boxes) :
    Move d (r.liftState s) (r.liftState t) := by
  cases hm with
  | walk hv ha he hb =>
    refine .walk (fun hp => hv ((r.liftState_mem_boxes s _).mp hp))
      ((embed_adjacent r d _ _).mpr ha) (fun hp => he ((r.liftState_mem_boxes s _).mp hp)) ?_
    simp only [Push.ColumnScan.Input.liftState, Push.ColumnScan.Input.liftEmpty, PushS.holes, hb]
  | @push n k hv hn hk slide hp hb =>
    have hlast : slide.cell ⟨n + k, by omega⟩ ≠ r.sourceCorner := by
      intro he
      apply ht
      rw [hb, ← he]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      congr 1
      apply Fin.ext
      change k + (n - 1) + 1 = n + k
      omega
    refine Move.push (fun hp => hv ((r.liftState_mem_boxes s _).mp hp)) hn hk
      (liftSlide r slide hlast) (congrArg r.embed hp) ?_
    exact liftSlide_boxes r slide hlast hb

/-- Any source trajectory whose final corner is empty lifts to the literal fixed reader board. -/
private theorem lift_source_reachable (hr : Reachable s t) (ht : r.sourceCorner ∉ t.boxes) :
    Reachable (r.liftState s) (r.liftState t) := by
  have hx : r.sourceCorner.1.val + 1 = r.width := by
    change r.width - 1 + 1 = r.width
    have := r.width_pos
    omega
  have hy : r.sourceCorner.2.val + 1 = r.height := by
    change r.height - 1 + 1 = r.height
    have := r.height_pos
    omega
  revert ht
  induction hr with
  | refl => intro _; exact .refl
  | tail _ hm ih =>
    intro ht
    have hu := Reachable.southeast_empty (Relation.ReflTransGen.single hm) hx hy ht
    exact (ih hu).tail ⟨hm.choose, lift_source_move r hm.choose_spec ht⟩

/-- A genuine source computation to its corner embeds unchanged before reader commitment. -/
theorem lift_source_initial {t : State r.width r.height}
    (hr : Reachable r.initial.toState t) (hp : t.player = r.sourceCorner) :
    Reachable r.compile.initial (r.liftState t) := by
  have ht := hr.valid (Finset.notMem_compl.mpr r.initial.player_empty)
  rw [hp] at ht
  change @Reachable r.outputWidth r.outputHeight r.compile.initial (r.liftState t)
  have h := lift_source_reachable r hr ht
  rw [r.liftState_initial] at h
  exact h

end PushPuzzle.PushPush.ColumnReader
