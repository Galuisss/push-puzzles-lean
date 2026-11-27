/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlocksSource
public import Push.CyclicRounds
import all Push.CyclicRounds

/-! Complete future whole-block executions transport through the translated source rectangle. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell Direction)
open Push.AcceptanceProgram Push.Cyclic

variable (r : Push.ColumnScan.Input)

private theorem sourceRounds_instructions (rounds : List Round) :
    instructions (w := (dock r).outputWidth) (h := (dock r).outputHeight)
      (rounds.map Push.Cyclic.sourceRound) =
        (instructions (w := r.width) (h := r.height) rounds).map (sourceInstruction r) := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
    simp only [List.map_cons, instructions, List.flatMap_cons, List.map_append]
    rw [Push.Cyclic.sourceRound_instructions r round]
    exact congrArg (List.append _) ih

theorem sourceRounds_bounded (rounds : List Round)
    (H : Push.Scan.Bounded (instructions (w := r.width) (h := r.height) rounds)) :
    Push.Scan.Bounded (instructions (w := (dock r).outputWidth) (h := (dock r).outputHeight)
      (rounds.map Push.Cyclic.sourceRound)) := by
  rw [sourceRounds_instructions]
  intro i hi
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
  exact sourceInstruction_bounded r old ((sourceBounded_iff_bounded r old).mpr (H old hold))

theorem Exec.source (rounds : List Round)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : Exec (rounds.map Push.Cyclic.sourceRound) E F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hoff : SourceOrthogonal r (auxData r E)) :
    Exec rounds (sourceData r E) (sourceData r F) := by
  induction rounds generalizing E with
  | nil => cases H; exact .nil _
  | cons round rounds ih =>
    cases round with
    | clear side lanes => cases H
    | read side requests =>
      cases H with
      | @cons _ _ _ _ G _ head tail =>
        have hsub := head.characterization.subset
        refine .cons (head.source_orthogonal r hrows hoff) (ih tail ?_ ?_)
        · intro q hq hy
          exact hrows q (hsub hq) hy
        · intro q hq
          exact hoff q (Finset.mem_filter.mpr
            ⟨hsub (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩)

theorem Exec.source_lift (rounds : List Round)
    {E F : Finset (Cell r.width r.height)} (H : Exec rounds E F)
    (hbound : Push.Scan.Bounded (instructions (w := r.width) (h := r.height) rounds))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hoff : SourceOrthogonal r A) :
    Exec (rounds.map Push.Cyclic.sourceRound)
      (E.map (sourceEmbedding r) ∪ A) (F.map (sourceEmbedding r) ∪ A) := by
  revert hbound
  induction H with
  | nil => exact fun _ => .nil _
  | @cons side requests rounds E G F head tail ih =>
    intro hbound
    have hrequest : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side r.width r.height := by
      intro a ha
      exact hbound _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    have htail : Push.Scan.Bounded (instructions (w := r.width) (h := r.height) rounds) :=
      fun i hi => hbound i (List.mem_append_right _ hi)
    exact .cons (head.source_lift_orthogonal r hrequest A hoff) (ih htail)

end PushPuzzle.PushPush.WholeBlocks
