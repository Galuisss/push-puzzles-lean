/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockLift
public import PushPush.ColumnReaderLift
public import Push.Cyclic

/-! Replay an original maximum-game computation inside both reader and dock. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell State Direction)
open Push.Cyclic

variable (r : Push.ColumnScan.Input)

def sourceLift (s : State r.width r.height) :
    State (dock r).outputWidth (dock r).outputHeight :=
  (dock r).liftState ((wideReader r).liftState s)

private theorem sourceLift_valid {s : State r.width r.height} (hs : s.player ∉ s.boxes) :
    (sourceLift r s).player ∉ (sourceLift r s).boxes := by
  intro hh
  apply hs
  exact ((wideReader r).liftState_mem_boxes s _).mp
    ((CornerDock.liftState_mem_boxes (dock r) ((wideReader r).liftState s) _).mp hh)

private theorem sourceLift_step {s t : State r.width r.height} {d : Direction}
    (hm : Move d s t) (ht : r.sourceCorner ∉ t.boxes) : Step (sourceLift r s) (sourceLift r t) := by
  cases hm with
  | walk hv ha he hb =>
    have hb' : ((wideReader r).liftState t).boxes = ((wideReader r).liftState s).boxes := by
      simp only [Push.ColumnScan.Input.liftState, Push.ColumnScan.Input.liftEmpty, PushS.holes, hb]
    refine ⟨d, .walk (sourceLift_valid r hv)
      ((CornerDock.embed_adjacent (dock r) d _ _).mpr
        ((ColumnReader.embed_adjacent (wideReader r) d _ _).mpr ha)) ?_ ?_⟩
    · intro hh
      exact he (((wideReader r).liftState_mem_boxes s _).mp
        ((CornerDock.liftState_mem_boxes (dock r) ((wideReader r).liftState s) _).mp hh))
    · simp only [sourceLift, Push.CornerDock.Input.liftState, PushFS.GridEmbedding.extend, hb']
  | @push n k hv hn hk slide hp hb =>
    have hlast : slide.cell (Fin.last _) ≠ r.sourceCorner := by
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
    let first := ColumnReader.liftSlide (wideReader r) slide hlast
    have hb1 := ColumnReader.liftSlide_boxes (wideReader r) slide hlast hb
    have hsafe : d = .west → first.cell (Fin.last _) ≠ (dock r).sourceGoal := by
      intro _ he
      have hy := congrArg (fun p => p.2.val) he
      have hbound := (slide.cell (Fin.last _)).2.isLt
      have hlo := (wideReader r).targetLevel_lower
      change (slide.cell (Fin.last _)).2.val = (wideReader r).targetLevel at hy
      change r.height + max r.sourceHoles r.width < (wideReader r).targetLevel at hlo
      omega
    exact ⟨d, .push (sourceLift_valid r hv) hn hk (CornerDock.liftSlide (dock r) first hsafe)
      (congrArg (fun p => (dock r).embed ((wideReader r).embed p)) hp)
      (CornerDock.liftSlide_boxes (dock r) first hsafe hb1)⟩

/-- A computation to the original southeast corner lifts into the complete cyclic extension. -/
theorem sourceLift_reachable {s t : State r.width r.height}
    (hr : Reachable s t) (ht : r.sourceCorner ∉ t.boxes) :
    Reachable (sourceLift r s) (sourceLift r t) := by
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
    exact (ih hu).tail (sourceLift_step r hm.choose_spec ht)

theorem sourceLift_initial : sourceLift r r.initial.toState = (dock r).compile.initial := by
  change (dock r).liftState ((wideReader r).liftState (wideReader r).initial.toState) = _
  rw [(wideReader r).liftState_initial]
  exact (dock r).liftState_toState (dock r).initial

end PushPuzzle.PushPush.Cyclic
