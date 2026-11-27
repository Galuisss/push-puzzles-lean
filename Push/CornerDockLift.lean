/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockForward
public import PushFS.Placement

/-! Replay the whole live source trajectory before entering the southwest dock. -/

@[expose] public section
namespace PushPuzzle.Push.CornerDock.Input

open PushFS PushS

variable (r : Input)

/-- The actual two-column translation of the source rectangle. -/
def placement : GridEmbedding r.width r.height r.outputWidth r.outputHeight where
  cells := ⟨r.embed, r.embed_injective⟩
  direction := id
  adjacent d p q ha := by
    change Adjacent d (r.embed p) (r.embed q)
    cases d <;> simp only [Adjacent, embed, Fin.ext_iff] at ha ⊢ <;> constructor <;> omega

/-- The fixed ambient boxes outside the translated source rectangle. -/
def outsideBoxes : Finset (Cell r.outputWidth r.outputHeight) :=
  (Finset.univ.image r.embed ∪ r.auxiliaryHoles)ᶜ

private theorem embed_not_outside (q : Cell r.width r.height) : r.embed q ∉ r.outsideBoxes := by
  simp only [outsideBoxes, Finset.mem_compl, not_not, Finset.mem_union]
  exact Or.inl (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)

/-- Replay a live source state while keeping every dock box fixed. -/
def liftState (s : PushFS.State r.width r.height) : PushFS.State r.outputWidth r.outputHeight :=
  r.placement.extend r.outsideBoxes s

private theorem lift_mem_boxes (s : PushFS.State r.width r.height) (q : Cell r.width r.height) :
    r.embed q ∈ (r.liftState s).boxes ↔ q ∈ s.boxes := by
  simp only [liftState, GridEmbedding.extend, Finset.mem_union, Finset.mem_map,
    placement, r.embed_not_outside, or_false]
  change (∃ a ∈ s.boxes, r.embed a = r.embed q) ↔ q ∈ s.boxes
  simp only [r.embed_injective.eq_iff, exists_eq_right]

private theorem lift_valid {s : PushFS.State r.width r.height} (hs : @State.Valid r.width r.height r.source.board s) :
    (r.liftState s).Valid r.compile.board := by
  apply GridEmbedding.extend_valid (e := r.placement) (outside := r.outsideBoxes)
    (sourceBoard := r.source.board) ?_
    (r.embed_not_outside) (by rw [r.compile.walls_empty]; exact Finset.disjoint_empty_right _) hs
  intro q
  simp only [Push.Instance.walls_empty]
  exact iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _)

private def liftRun {s : PushFS.State r.width r.height} {d : Direction} {n : ℕ}
    (run : @Run r.width r.height r.source.board d s n) : Run r.compile.board d (r.liftState s) n where
  cell i := r.embed (run.cell i)
  start := congrArg r.embed run.start
  adjacent i := r.placement.adjacent d _ _ (run.adjacent i)
  occupied i := (r.lift_mem_boxes s _).mpr (run.occupied i)
  empty hm := run.empty ((r.lift_mem_boxes s _).mp hm)
  floor _ := by rw [r.compile.walls_empty]; exact Finset.notMem_empty _

/-- Every complete source run, including arbitrary push lengths, replays inside the expansion. -/
theorem lift_move {s t : PushFS.State r.width r.height} {d : Direction}
    (hm : @Move r.width r.height r.source.board none d s t) :
    Move r.compile.board none d (r.liftState s) (r.liftState t) := by
  cases hm with
  | walk hv ha hf he hb =>
    exact .walk (r.lift_valid hv) (r.placement.adjacent _ _ _ ha) (by simp)
      (fun hm => he ((r.lift_mem_boxes s _).mp hm)) (by
        simp only [liftState, GridEmbedding.extend, hb]
        rfl)
  | @push n hv hn hc run hp hb =>
    apply Move.push (r.lift_valid hv) hn hc (r.liftRun run)
    · exact congrArg r.embed hp
    · change t.boxes.map r.placement.cells ∪ r.outsideBoxes =
        insert (r.embed (run.cell ⟨n + 1, by omega⟩))
          ((s.boxes.map r.placement.cells ∪ r.outsideBoxes).erase (r.embed (run.cell 1)))
      rw [hb, Finset.map_insert, Finset.map_erase, Finset.erase_union_distrib,
        Finset.erase_eq_of_notMem (r.embed_not_outside _), Finset.insert_union]
      rfl

theorem lift_reachable {s t : PushFS.State r.width r.height}
    (hr : @Reachable r.width r.height r.source.board none s t) :
    Reachable r.compile.board none (r.liftState s) (r.liftState t) :=
  hr.lift r.liftState (fun _ _ ⟨d, hm⟩ => ⟨d, r.lift_move hm⟩)

/-- Replaying a hole-set state gives exactly the literal dock recipe for that source state. -/
theorem liftState_toState (s : HoleState r.width r.height) :
    r.liftState s.toState = (r.extend s).toState := by
  apply State.ext
  · rfl
  ext q
  by_cases hsource : q ∈ Finset.univ.image r.embed
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hsource
    change r.embed a ∈ (r.liftState s.toState).boxes ↔ r.embed a ∈ (r.extend s).emptyᶜ
    rw [Finset.mem_compl, r.lift_mem_boxes, r.embed_mem_extend]
    exact Finset.mem_compl
  · have hbox : q ∉ s.toState.boxes.map r.placement.cells := by
      intro hb
      obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hb
      exact hsource (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩)
    have hhole : q ∉ s.empty.image r.embed := fun hh =>
      hsource (Finset.image_subset_image (Finset.subset_univ _) hh)
    change q ∉ s.emptyᶜ.map r.placement.cells at hbox
    simp only [liftState, GridEmbedding.extend, HoleState.toState, extend, Finset.mem_union,
      hbox, false_or, outsideBoxes, Finset.mem_compl, hsource, hhole]

/-- Reaching the original left-boundary player target yields a real run to the new southwest corner. -/
theorem compile_solvable_of_source (hs : r.source.Solvable) : r.compile.Solvable := by
  change ∃ t : PushFS.State r.width r.height,
    @Reachable r.width r.height r.source.board none r.initial.toState t ∧ t.player = r.sourceGoal at hs
  obtain ⟨t, hr, ht⟩ := hs
  let live : HoleState r.width r.height :=
    ⟨t.player, holes t, player_mem_holes (hr.valid r.source.initial_valid)⟩
  have hlive : live.toState = t := by
    apply State.ext
    · rfl
    simp only [HoleState.toState, live, holes, compl_compl]
  have hrun := r.lift_reachable hr
  change Reachable r.compile.board none (r.liftState r.initial.toState) (r.liftState t) at hrun
  rw [← hlive, r.liftState_toState r.initial, r.liftState_toState live] at hrun
  obtain ⟨u, hu, hup⟩ := r.extend_goal_to_corner live ht
  exact ⟨u.toState, hrun.trans hu, hup⟩

end PushPuzzle.Push.CornerDock.Input
