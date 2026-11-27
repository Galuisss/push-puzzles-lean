/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanNormalize
import all Push.Scan
import all Push.ScanColumns

/-! Parallel reads project exactly to a single physical lane, including repeated requests. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

private theorem consume_restrict {α : Type*} [DecidableEq α] (P : α → Prop) [DecidablePred P]
    {cells : List α} {quota : ℕ} {E F : Finset α}
    (inside : ∀ a ∈ cells, P a) (run : consume cells quota E = some F) :
    consume cells quota (E.filter P) = some (F.filter P) := by
  induction cells generalizing quota E with
  | nil =>
    cases quota with
    | zero => cases Option.some.inj run; rfl
    | succ quota => cases run
  | cons a cells ih =>
    cases quota with
    | zero => cases Option.some.inj run; rfl
    | succ quota =>
      have pa := inside a (List.mem_cons_self)
      have rest : ∀ b ∈ cells, P b := fun b hb => inside b (List.mem_cons_of_mem _ hb)
      by_cases ha : a ∈ E
      · have haP : a ∈ E.filter P := Finset.mem_filter.mpr ⟨ha, pa⟩
        simp only [consume, ite_eq_left ha] at run
        simp only [consume, ite_eq_left haP]
        rw [← Finset.filter_erase]
        exact ih rest run
      · have haP : a ∉ E.filter P := fun h => ha (Finset.mem_filter.mp h).1
        simp only [consume, ite_eq_right ha] at run
        simp only [consume, ite_eq_right haP]
        exact ih rest run

/-- Restricting a successful line read to its physical lane keeps precisely the same remainder. -/
theorem read_lane_restrict {w h : ℕ} {side : Direction} {lane quota : ℕ} {E F : Finset (Cell w h)}
    (run : (Instruction.read side lane quota).eval E = some F) :
    consume (lineCells side lane) quota (E.filter fun q => side.lane q = lane) =
      some (F.filter fun q => side.lane q = lane) :=
  consume_restrict _ (fun q hq => (mem_lineCells side lane q).mp hq) run

/-- Every successful parallel block reads its summed quota on each actual lane independently. -/
theorem lines_lane_projection {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    {E F : Finset (Cell w h)} (lane : ℕ) (run : eval (lines side requests) E = some F) :
    consume (lineCells side lane) (quotaAt requests lane) (E.filter fun q => side.lane q = lane) =
      some (F.filter fun q => side.lane q = lane) := by
  induction requests generalizing E with
  | nil =>
    cases Option.some.inj run
    simp only [quotaAt, List.filter_nil, List.map_nil, List.sum_nil, consume]
  | cons request rest ih =>
    obtain ⟨G, head, tail⟩ := Option.bind_eq_some_iff.mp run
    have projected := ih tail
    have quota : quotaAt (request :: rest) lane = (if request.1 = lane then request.2 else 0) + quotaAt rest lane := by
      by_cases he : request.1 = lane <;> simp [quotaAt, he]
    rw [quota]
    by_cases he : request.1 = lane
    · have first := read_lane_restrict head
      rw [he] at first
      simp only [ite_eq_left he]
      rw [consume_add, first, Option.bind_some]
      exact projected
    · have unchanged : (G.filter fun q => side.lane q = lane) = E.filter fun q => side.lane q = lane :=
        other_lane head (Ne.symm he)
      simp only [ite_eq_right he, Nat.zero_add]
      rw [← unchanged]
      exact projected

end PushPuzzle.Push.Scan
