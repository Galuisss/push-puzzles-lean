/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicPeelingCorrectness
public import Push.ScanNormalizeRequests
public import Push.AcceptanceProgramSkeleton
public import Push.CyclicEraseInventoryProgram

/-! Compact read/clear blocks transported through the actual cyclic source geometry. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS AcceptanceProgram

/-- Source-bound validity is the standard actual-lane validity for the same rectangle. -/
theorem sourceBounded_iff_bounded (r : ColumnScan.Input) (i : Scan.Instruction r.width r.height) :
    SourceBounded r i ↔ i.Bounded := by
  cases i with
  | read side lane quota => cases side <;> rfl
  | clear side lanes => cases side <;> rfl

/-- Translate a complete compact block to the actual shifted source rectangle. -/
def sourceRound : Round → Round
  | .read side requests => .read side (sourceRequests side requests)
  | .clear side lanes => .clear side (lanes.image (sourceLane side))

/-- Turn one complete compact block, retaining every positive quota. -/
def turnRound (w : ℕ) : Round → Round
  | .read side requests => .read (turnSide side) (turnRequests w side requests)
  | .clear side lanes => .clear (turnSide side) (turnLanes w side lanes)

/-- Future source blocks after the actual translation and quarter turn. -/
def nextRounds (r : ColumnScan.Input) (rounds : List Round) : List Round :=
  rounds.map fun block => turnRound (dock r).outputWidth (sourceRound block)

private theorem sourceRound_instructions (r : ColumnScan.Input) (block : Round) :
    (sourceRound block).instructions = (block.instructions (w := r.width) (h := r.height)).map
      (sourceInstruction r) := by
  cases block <;> simp only [sourceRound, Round.instructions, sourceRequests, List.map_map,
    List.map_cons, List.map_nil]
  all_goals rfl

private theorem turnRound_instructions {w h : ℕ} (block : Round) :
    (turnRound w block).instructions (w := h) (h := w) =
      turnProgram (block.instructions (w := w) (h := h)) := by
  cases block <;> simp only [turnRound, Round.instructions, turnRequests, turnProgram,
    List.map_map, List.map_cons, List.map_nil]
  all_goals rfl

/-- Expanding transported compact blocks gives the exact already-proved static source continuation. -/
theorem nextRounds_instructions (r : ColumnScan.Input) (rounds : List Round) :
    instructions (w := (dock r).outputHeight) (h := (dock r).outputWidth) (nextRounds r rounds) =
      nextTail r (instructions rounds) := by
  induction rounds with
  | nil => rfl
  | cons block rounds ih =>
    simp only [nextRounds, List.map_cons, instructions, List.flatMap_cons] at ih ⊢
    rw [turnRound_instructions, sourceRound_instructions]
    change _ = turnProgram (((block.instructions (w := r.width) (h := r.height)) ++
      instructions rounds).map (sourceInstruction r))
    simp only [turnProgram, List.map_append]
    exact congrArg (List.append _) ih

/-- The transformed blocks have the same read/clear tags and the physically turned sides. -/
theorem nextRounds_shapes (r : ColumnScan.Input) (rounds : List Round) :
    (nextRounds r rounds).map Round.shape =
      (rounds.map Round.shape).map (fun shape => (shape.1, turnSide shape.2)) := by
  induction rounds with
  | nil => rfl
  | cons block rounds ih =>
    cases block <;> simp only [nextRounds, List.map_cons, sourceRound, turnRound, Round.shape] at ih ⊢
    all_goals exact congrArg (List.cons _) ih

/-- Every transformed block selects only actual next-source lanes. -/
theorem nextRounds_bounded (r : ColumnScan.Input) (rounds : List Round)
    (hb : ∀ i ∈ instructions rounds, SourceBounded r i) :
    Scan.Bounded (instructions (w := (dock r).outputHeight) (h := (dock r).outputWidth) (nextRounds r rounds)) := by
  rw [nextRounds_instructions]
  apply turnProgram_bounded
  intro i hi
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
  exact sourceInstruction_bounded r old (hb old hold)

/-- Source translation and turning preserve all positive quotas of the compact future program. -/
theorem nextRounds_quota (r : ColumnScan.Input) (rounds : List Round) :
    Scan.quota (instructions (w := (dock r).outputHeight) (h := (dock r).outputWidth) (nextRounds r rounds)) =
      Scan.quota (instructions (w := r.width) (h := r.height) rounds) := by
  rw [nextRounds_instructions, nextTail, turnProgram_quota, sourceProgram_quota]

/-- Compact future blocks and their exact static transport accept the same prefixed bitmap. -/
theorem nextRounds_accepts_prefix (r : ColumnScan.Input) (rounds : List Round)
    (head : List (Scan.Instruction (dock r).outputHeight (dock r).outputWidth))
    (E : Finset (Cell (dock r).outputHeight (dock r).outputWidth)) :
    Scan.Accepts (head ++ instructions (nextRounds r rounds)) E ↔
      Scan.Accepts (head ++ nextTail r (instructions rounds)) E := by
  rw [nextRounds_instructions]

/-- A live source computation paying the first dense column vector and all remaining compact blocks. -/
def Language (r : ColumnScan.Input) (rounds : List Round) : Prop :=
  ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
    s.player = r.sourceCorner ∧
      Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++ instructions rounds) (holes s)

/-- Total positive payment of the current first round and every future compact block. -/
def Budget (r : ColumnScan.Input) (rounds : List Round) : Prop :=
  r.quotas.sum + Scan.quota (instructions (w := r.width) (h := r.height) rounds) ≤ r.sourceHoles

end PushPuzzle.Push.Cyclic
