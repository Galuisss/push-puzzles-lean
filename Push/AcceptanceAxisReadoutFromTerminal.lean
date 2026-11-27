/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisTerminalShape
public import Push.AcceptanceMainCut

/-! An arbitrary genuine terminal ordinary-axis word supplies all real prefix words and shared train motions. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceAxisReadout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {upper lower : Endpoint}
  (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hu in
private theorem terminal_cut {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = p.x upper.port → q.2.val = p.D → q ∉ holes t := by
  intro q hx hy hole
  exact (mem_holes q).mp hole
    (canonical_main_central_occupied l p hl hM haxes initial target (l.endpoints_port_lt hl hu) hx
      (by rw [hy]; omega) run .refl accepted)

include hgate hu hlow hsuSide hslSide hport

/-- Complete complementary words at the actual endpoint restore every prefix's genuine shared-axis word. -/
theorem canonical_ordinaryAxis_readout_of_terminal_word {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {terminal : OrdinaryAxisPlacement} (word : OrdinaryAxisReadout p upper lower t terminal) :
    ∃ placement, OrdinaryAxisReadout p upper lower u placement := by
  have cut := terminal_cut l p hl hM haxes initial target hu (hsu.trans hut) accepted
  have upperDepth := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have lowerDepth := readDepth_ge p (l.endpoints_level_bounds p hl hM hlow).1 (l.endpoints_level_bounds p hl hM hlow).2
  have port := (l.endpoints_port_lt hl hu).trans_le haxes
  have finalShape := ordinary_shape_of_readout word port (by omega) (by omega) cut
  have inventory := ordinary_readout_card word port (by omega) (by omega) hsuSide hslSide hport cut
  obtain ⟨blocks, shape⟩ := canonical_ordinaryAxis_shape_of_terminal_shape l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu hut accepted inventory finalShape
  have positive : blocks.Positive := by
    change 0 < blocks.firstLength ∧ 0 < blocks.middleLength ∧ 0 < blocks.lastLength
    rw [shape.first_length, shape.middle_length, shape.last_length]
    exact l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  exact ⟨ordinaryAxisPlacement p upper blocks, ordinary_readout_of_shape shape positive⟩

/-- The same arbitrary terminal word supplies every actual ordinary-axis train motion on the accepted source run. -/
theorem canonical_ordinaryAxis_motion_of_terminal_word {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {terminal : OrdinaryAxisPlacement} (word : OrdinaryAxisReadout p upper lower t terminal) :
    ∃ before after, OrdinaryAxisMotion p upper lower u v before after := by
  have cut := terminal_cut l p hl hM haxes initial target hu (hsu.tail step |>.trans hvt) accepted
  have upperDepth := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have lowerDepth := readDepth_ge p (l.endpoints_level_bounds p hl hM hlow).1 (l.endpoints_level_bounds p hl hM hlow).2
  have port := (l.endpoints_port_lt hl hu).trans_le haxes
  have finalShape := ordinary_shape_of_readout word port (by omega) (by omega) cut
  have inventory := ordinary_readout_card word port (by omega) (by omega) hsuSide hslSide hport cut
  exact canonical_ordinaryAxis_motion_of_terminal_shape l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu step hvt accepted inventory finalShape

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
