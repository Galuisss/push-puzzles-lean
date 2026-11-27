/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportPrivate
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramColumns

/-! The actual four-position private payment certifies the gate's work-row sample at offset four. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The private work-row sample of every actual gate is a terminal hole. -/
theorem canonical_gate_four_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 4) (hy : q.2.val = p.H - readDepth p 1) : q ∈ holes t := by
  apply canonical_private_slot_terminal l p hl hM haxes initial target hr accepted
  · rw [hx]
    exact gate_private_column l p hi
  · have hY := readDepth_add_lt_H p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hy hY
    have hd : pageDepth p .lower q = p.Y 1 := by change p.H - q.2.val = p.Y 1; omega
    simp only [hd, privateDepths, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

end PushPuzzle.Push.AcceptanceSoundness
