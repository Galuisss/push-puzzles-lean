/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportRankBound
public import Push.ScanNormalize
import all Push.ScanColumns
import all Push.ScanNormalize

/-! Exact per-lane quota conservation for real and reference reads, including repeated columns. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- A whole same-direction word pays the sum of all its requests on each lane, including repetitions. -/
private theorem lines_lane_card {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ)) (x : ℕ)
    {E F : Finset (Cell w h)} (he : Scan.eval (Scan.lines side requests) E = some F) :
    (F.filter fun q => side.lane q = x).card + Scan.quotaAt requests x =
      (E.filter fun q => side.lane q = x).card := by
  induction requests generalizing E with
  | nil =>
    have hEF : E = F := Option.some.inj he
    simp only [Scan.quotaAt, List.filter_nil, List.map_nil, List.sum_nil, Nat.add_zero, hEF]
  | cons request rest ih =>
    obtain ⟨G, hhead, htail⟩ := Option.bind_eq_some_iff.mp he
    have ht := ih htail
    rw [Scan.quotaAt_cons]
    by_cases hx : request.1 = x
    · have hh := Scan.Instruction.read_line_card hhead
      simp only [hx] at hh
      rw [ite_eq_left hx]
      omega
    · have hh := Scan.other_lane hhead (Ne.symm hx)
      rw [ite_eq_right hx, Nat.zero_add]
      rw [hh] at ht
      exact ht

/-- Reference and real executions of one emitted round have exactly the same loss on each lane. -/
theorem round_reference_lane_loss {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T E F : Finset (Cell w h)) (x : ℕ)
    (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F) :
    (E.filter fun q => side.lane q = x).card +
        ((emit [.read side requests] T).remaining.filter fun q => side.lane q = x).card =
      (F.filter fun q => side.lane q = x).card + (T.filter fun q => side.lane q = x).card := by
  let quotas := (emitReads side requests T).quotas
  have hactual : Scan.eval (Scan.lines side quotas) E = some F := by
    simpa only [emit, instructions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Round.instructions, Scan.lines] using he
  have htarget : Scan.eval (Scan.lines side quotas) T = some (emitReads side requests T).remaining :=
    emitReads_eval side requests T
  have hA := lines_lane_card side quotas x hactual
  have hT := lines_lane_card side quotas x htarget
  change (E.filter fun q => side.lane q = x).card +
      ((emitReads side requests T).remaining.filter fun q => side.lane q = x).card = _
  omega

/-- A retained real hole bounds the corresponding canonical trim loss by its physical rank. -/
theorem round_retained_reference_loss_bound {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T E F : Finset (Cell w h))
    (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    {a : Cell w h} (ha : a ∈ F) :
    (T.filter fun q => side.lane q = side.lane a).card ≤
      ((emit [.read side requests] T).remaining.filter fun q => side.lane q = side.lane a).card +
        prefixRank side a := by
  have hsame := round_reference_lane_loss side requests T E F (side.lane a) he
  have hbound := round_retained_lane_loss_bound side requests T E F he ha
  omega

end PushPuzzle.Push.AcceptanceSoundness
