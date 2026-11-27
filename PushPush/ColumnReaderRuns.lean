/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderSource
public import PushPush.SlideHoles
public import Push.ColumnScanResidualOrder

/-! Actual maximum slides preserve complete hole components in the committed data region. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State Direction Adjacent)
open Push.ReflectedFrontier Push.ReaderResidual
open Push.StripFrontier

variable {w h : ℕ}

/-- The lower deleted part never ends in the middle of an original vertical hole run. -/
def NoNorthSplit (E F : Finset (Cell w h)) : Prop :=
  ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent .north p q

theorem NoNorthSplit.refl (E : Finset (Cell w h)) : NoNorthSplit E E := by
  simp [NoNorthSplit]

theorem NoNorthSplit.trans {E F G : Finset (Cell w h)} (hEF : NoNorthSplit E F)
    (hFG : NoNorthSplit F G) (hGF : G ⊆ F) : NoNorthSplit E G := by
  intro p hp q hq ha
  obtain ⟨hpE, hpG⟩ := Finset.mem_sdiff.mp hp
  by_cases hpF : p ∈ F
  · exact hFG p (Finset.mem_sdiff.mpr ⟨hpF, hpG⟩) q hq ha
  · exact hEF p (Finset.mem_sdiff.mpr ⟨hpE, hpF⟩) q (hGF hq) ha

variable (r : Push.ColumnScan.Input)

/-- A single maximum action below the source consumes a union of whole source-hole runs. -/
private theorem move_no_split {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hm : Move d s t) (hbelow : r.height ≤ s.player.2.val) :
    NoNorthSplit (source r.width r.height s) (source r.width r.height t) := by
  cases hm with
  | walk _ _ _ hb => simp [NoNorthSplit, source, PushS.holes, hb]
  | @push n k _ _ _ slide _ hb =>
    intro p hp q hq ha
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpEmpty, hpx, hpy⟩ := Finset.mem_filter.mp hp
    have hpBox : p ∈ t.boxes := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨(PushS.mem_holes _).mpr hn, hpx, hpy⟩)
    have hpAfter : p ∈ slide.after := by
      rw [hb] at hpBox
      rcases Finset.mem_union.mp hpBox with hpBox | hpBox
      · exact False.elim ((PushS.mem_holes _).mp hpEmpty (Finset.mem_sdiff.mp hpBox).1)
      · exact hpBox
    have hd : d = .north := by
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hpAfter
      have hy := slide.position ⟨k + i.val + 1, by omega⟩
      have hx := slide.lane ⟨k + i.val + 1, by omega⟩
      rw [he] at hy hx
      dsimp only at hy
      cases d <;> simp only [Direction.position, Direction.lane] at hy hx <;> first | rfl | omega
    subst d
    have hfull : q ∈ t.boxes := by rw [hb]; exact slide.after_forward_full hpAfter ha
    exact (PushS.mem_holes _).mp (Finset.mem_filter.mp hq).1 hfull

section Committed

variable {start finish : State r.outputWidth r.outputHeight}
  (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
    r.initialState.toState start)
  (hsf : PushFS.Reachable r.compile.board none start finish)
  (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
  (hland : start.player = r.landing)

include hpre hsf hfx hfy hland

private theorem source_subset_after {s t : State r.outputWidth r.outputHeight}
    (hst : PushFS.Reachable r.compile.board none start s) (hr : Reachable s t) :
    source r.width r.height t ⊆ source r.width r.height s := by
  apply Push.ReaderResidual.reachable_source_subset
  apply Push.Path.enrich (hr.unit_expansion r.compile.board rfl)
  intro a b hsa hm _
  exact ⟨hm, r.landing_no_return hpre hsf hfx hfy hland ((hst.trans hsa).tail hm)⟩

/-- Any actual committed suffix deletes complete original hole components. -/
private theorem whole_runs_after {s t : State r.outputWidth r.outputHeight}
    (hst : PushFS.Reachable r.compile.board none start s) (hr : Reachable s t) :
    NoNorthSplit (source r.width r.height s) (source r.width r.height t) := by
  induction hr with
  | refl => exact .refl _
  | tail hsu hm ih =>
    have hnow := hst.trans (Reachable.unit_expansion hsu r.compile.board rfl)
    have hbelow := r.landing_player_below_source hpre hsf hfx hfy hland hnow
    have hsub := source_subset_after r hpre hsf hfx hfy hland hnow (Relation.ReflTransGen.single hm)
    exact ih.trans (move_no_split r hm.choose_spec hbelow) hsub

end Committed

private theorem source_eq_of_crop {s t : State r.outputWidth r.outputHeight}
    (he : r.cropState s = r.cropState t) : source r.width r.height s = source r.width r.height t := by
  rw [← r.cropState_holes_image s, ← r.cropState_holes_image t, he]

/-- Actual maximum sliding strengthens the ordinary northern-prefix certificate by whole runs. -/
structure WholeBottomRemainder (E F : Finset (Cell w h)) : Prop extends BottomRemainder E F where
  no_split : NoNorthSplit E F

theorem SourceWitness.whole_remainder {finish : State r.outputWidth r.outputHeight}
    (w : SourceWitness r finish) (hfx : finish.player.1.val = 0)
    (hfy : r.targetLevel ≤ finish.player.2.val) :
    WholeBottomRemainder (Push.ReflectedFrontier.source r.width r.height w.state)
      (Push.ReflectedFrontier.source r.width r.height finish) := by
  refine ⟨r.landing_source_remainder w.before w.suffix hfx hfy w.landing w.suffix, ?_⟩
  have hr := whole_runs_after r w.before w.suffix hfx hfy w.landing w.bridge w.tailPath
  rwa [source_eq_of_crop r w.tailCrop] at hr

end PushPuzzle.PushPush.ColumnReader
