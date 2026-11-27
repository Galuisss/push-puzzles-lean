/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSource
public import Push.ColumnScanForwardColumns

/-! Every real source computation lifts to the unchanged reader extension. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS

variable (r : Input)

/-- Fixed auxiliary holes outside the copied source rectangle. -/
def auxiliaryHoles : Finset (Cell r.outputWidth r.outputHeight) := r.empty \ r.sourceEmpty

private theorem embed_not_auxiliary (p : Cell r.width r.height) : r.embed p ∉ r.auxiliaryHoles := by
  intro hp
  obtain ⟨he, hs⟩ := Finset.mem_sdiff.mp hp
  exact hs (Finset.mem_image.mpr ⟨p, (r.embed_mem_empty p).mp he, rfl⟩)

/-- Replace only the live source bitmap; all auxiliary reader holes remain fixed. -/
def liftEmpty (s : State r.width r.height) : Finset (Cell r.outputWidth r.outputHeight) :=
  (holes s).image r.embed ∪ r.auxiliaryHoles

/-- The physical extension of an exact source configuration. -/
def liftState (s : State r.width r.height) : State r.outputWidth r.outputHeight :=
  ⟨r.embed s.player, (r.liftEmpty s)ᶜ⟩

@[simp] theorem liftEmpty_embed_mem (s : State r.width r.height) (p : Cell r.width r.height) :
    r.embed p ∈ r.liftEmpty s ↔ p ∈ holes s := by
  simp only [liftEmpty, Finset.mem_union, Finset.mem_image, r.embed_injective.eq_iff,
    exists_eq_right, r.embed_not_auxiliary, or_false]

/-- Source box membership is copied literally. -/
@[simp] theorem liftState_mem_boxes (s : State r.width r.height) (p : Cell r.width r.height) :
    r.embed p ∈ (r.liftState s).boxes ↔ p ∈ s.boxes := by
  simp only [liftState, Finset.mem_compl, liftEmpty_embed_mem, mem_holes, not_not]

private theorem embed_adjacent_forward (d : Direction) {p q : Cell r.width r.height}
    (ha : Adjacent d p q) : Adjacent d (r.embed p) (r.embed q) := by
  cases d <;> simpa only [Adjacent, embed, Fin.ext_iff] using ha

private def liftHoleState (s : State r.width r.height) (hs : s.Valid r.sourceBoard) :
    HoleState r.outputWidth r.outputHeight :=
  ⟨r.embed s.player, r.liftEmpty s, (r.liftEmpty_embed_mem s s.player).mpr (player_mem_holes hs)⟩

private theorem liftState_valid {s : State r.width r.height} (hs : s.Valid r.sourceBoard) :
    (r.liftState s).Valid r.compile.board :=
  (r.liftHoleState s hs).valid r.compile.board r.compile.walls_empty

/-- The original emitted initial state is the source initial state with those fixed auxiliary holes. -/
theorem liftState_initial : r.liftState r.initial.toState = r.compile.initial := by
  change r.liftState r.initial.toState = r.initialState.toState
  apply State.ext
  · rfl
  change (r.liftEmpty r.initial.toState)ᶜ = r.emptyᶜ
  congr 1
  rw [liftEmpty, r.initial.holes_toState]
  exact Finset.union_sdiff_of_subset (Finset.subset_union_left)

/-- Every source walk or complete occupied-run push lifts with its original exact player position. -/
private theorem lift_source_move {s t : State r.width r.height} {d : Direction}
    (hm : Move r.sourceBoard none d s t) :
    Move r.compile.board none d (r.liftState s) (r.liftState t) := by
  cases hm with
  | walk hv ha _ he hb =>
    refine .walk (r.liftState_valid hv) (r.embed_adjacent_forward d ha)
      (by simp) ?_ ?_
    · exact fun hh => he ((r.liftState_mem_boxes s t.player).mp hh)
    · simp only [liftState, liftEmpty, holes, hb]
      rfl
  | @push n hv hn _ run hp hb =>
    let S := r.liftHoleState s hv
    let push : S.Push d := {
      length := n
      positive := hn
      cell i := r.embed (run.cell i)
      start := congrArg r.embed run.start
      adjacent i := r.embed_adjacent_forward d (run.adjacent i)
      occupied i := fun hi => (mem_holes _).mp ((r.liftEmpty_embed_mem s _).mp hi) (run.occupied i)
      destination := (r.liftEmpty_embed_mem s _).mpr ((mem_holes _).mpr run.empty) }
    have htarget : push.target.toState = r.liftState t := by
      apply State.ext
      · exact congrArg r.embed hp.symm
      · change (insert (r.embed (run.cell 1)) ((r.liftEmpty s).erase
          (r.embed (run.cell ⟨n + 1, by omega⟩))))ᶜ = (r.liftEmpty t)ᶜ
        congr 1
        rw [liftEmpty, liftEmpty, holes_push run hn hb, Finset.image_insert,
          Finset.image_erase r.embed_injective, Finset.erase_union_distrib,
          Finset.erase_eq_of_notMem (r.embed_not_auxiliary _), Finset.insert_union]
    exact htarget ▸ push.move r.compile.board r.compile.walls_empty none trivial

/-- Any original source trajectory lifts step for step on the fixed compiled reader board. -/
private theorem lift_source_reachable {s t : State r.width r.height}
    (hr : Reachable r.sourceBoard none s t) :
    Reachable r.compile.board none (r.liftState s) (r.liftState t) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail ⟨hm.choose, r.lift_source_move hm.choose_spec⟩

/-- A source computation starts at the actual compiled initial state and retains all reader auxiliaries. -/
theorem lift_source_initial_reachable {t : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState t) :
    Reachable r.compile.board none r.compile.initial (r.liftState t) := by
  simpa only [r.liftState_initial] using r.lift_source_reachable hr

end PushPuzzle.Push.ColumnScan.Input
