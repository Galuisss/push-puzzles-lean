/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanLaneProjection
public import Push.AcceptanceSoundnessSupportResidual
import all Push.AcceptanceProgramRounds
import all Push.Scan

/-! The actual lane payment determines its literal first-hole consumption, independently of other lanes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS AcceptanceProgram

/-- A real compact block with known lane loss performs exactly that many physical first-hole reads on the lane. -/
theorem round_lane_projection {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T : Finset (Cell w h)) {E F : Finset (Cell w h)} (lane quota : ℕ)
    (run : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    (loss : (F.filter fun q => side.lane q = lane).card + quota =
      (E.filter fun q => side.lane q = lane).card) :
    Scan.consume (Scan.lineCells side lane) quota (E.filter fun q => side.lane q = lane) =
      some (F.filter fun q => side.lane q = lane) := by
  let quotas := (emitReads side requests T).quotas
  have actual : Scan.eval (Scan.lines side quotas) E = some F := by
    simpa only [emit, instructions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Round.instructions, Scan.lines] using run
  have projected := Scan.lines_lane_projection side quotas lane actual
  have count := Scan.consume_card projected
  have same : Scan.quotaAt quotas lane = quota := by omega
  simpa only [same] using projected

end PushPuzzle.Push.AcceptanceSoundness
