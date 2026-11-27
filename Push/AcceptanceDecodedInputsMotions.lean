/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceDecodedInputs
public import Push.AcceptanceAxisReadoutMotion

/-! Both ends of genuine shared-axis motion supply the static joint words used for input decoding. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout.AxisMotions

open PushFS PushS PushS.PortLayout AcceptanceDecodedInputs

variable {l : PortLayout} {p : Scales.Parameters} {u v : State (p.W + 1) (p.H + 1)}

/-- All genuine ordinary shared-axis motions supply the same source state's exact endpoint words. -/
theorem before_shared (motions : AxisMotions l p u v) : SharedAxisReadouts l p u := by
  constructor
  intro upper lower hu hl hsu hsl hp
  obtain ⟨before, _, motion⟩ := motions.ordinary upper lower hu hl hsu hsl hp
  exact ⟨_, motion.before_readout⟩

/-- All genuine ordinary shared-axis motions supply the same target state's exact endpoint words. -/
theorem after_shared (motions : AxisMotions l p u v) : SharedAxisReadouts l p v := by
  constructor
  intro upper lower hu hl hsu hsl hp
  obtain ⟨_, after, motion⟩ := motions.ordinary upper lower hu hl hsu hsl hp
  exact ⟨_, motion.after_readout⟩

end PushPuzzle.Push.AcceptanceAxisReadout.AxisMotions
