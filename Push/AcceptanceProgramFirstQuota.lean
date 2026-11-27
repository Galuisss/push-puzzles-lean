/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramBounded
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFrame

/-! The actual clipped acceptance program's first south read pays at least one full frame column. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem left_frame_front_card (W H : ℕ) (E : Finset (Cell (W + 1) (H + 1)))
    (hframe : Boundary.frame ⊆ E) :
    (E.filter fun q => q ∈ (Scan.lineCells .south 0).take (H + 1)).card = H + 1 := by
  rw [column_full W H 0 (Nat.zero_le _)]
  have he : (E.filter fun q => q ∈ Scan.lineCells .south 0) =
      ({0} : Finset (Fin (W + 1))) ×ˢ (Finset.univ : Finset (Fin (H + 1))) := by
    ext q
    simp only [Finset.mem_filter, Scan.mem_lineCells, Direction.lane, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_univ, and_true]
    constructor
    · intro hq
      exact Fin.ext hq.2
    · intro hx
      have hx' : q.1.val = 0 := congrArg Fin.val hx
      refine ⟨hframe ((Boundary.mem_frame q).mpr ?_), hx'⟩
      exact ⟨.west, by simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] using hx'⟩
  rw [he, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin, Nat.one_mul]

/-- The literal first output block begins with the full left-frame column quota `H+1`. -/
private theorem program_first_south (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    ∃ quota rest, (program l p target).rounds = .read .south [(0, p.H + 1), (p.W, quota)] :: rest := by
  have hfront := left_frame_front_card p.W p.H (targetHoles l p target)
    (l.encodedSegments_frame_subset p (l.canonical target))
  have hs : ∃ tail, schedule l p (targetHoles l p target \ Boundary.frame).card =
      .read .south [(0, p.H + 1), (p.W, p.H + 1)] :: tail := by
    unfold schedule preparation frameSchedule
    exact ⟨_, rfl⟩
  obtain ⟨tail, hs⟩ := hs
  rw [program, hs]
  dsimp only [emit, emitReads]
  rw [hfront]
  exact ⟨_, _, rfl⟩

/-- Restriction to actual lanes preserves the genuine first south block and its full-column payment. -/
theorem bounded_program_first_south (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    ∃ requests rest,
      boundedRounds (p.W + 1) (p.H + 1) (program l p target).rounds = .read .south requests :: rest ∧
      p.H + 1 ≤ (requests.map Prod.snd).sum := by
  obtain ⟨quota, rest, he⟩ := program_first_south l p target
  refine ⟨[(0, p.H + 1), (p.W, quota)], boundedRounds (p.W + 1) (p.H + 1) rest, ?_, ?_⟩
  · rw [he]
    simp [boundedRounds, Round.bounded, Scan.laneCount]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

end PushPuzzle.Push.AcceptanceProgram
