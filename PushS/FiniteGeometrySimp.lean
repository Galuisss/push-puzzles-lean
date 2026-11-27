/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public meta import Lean.Meta.Tactic.Simp

/-! Named local simp sets for the finite compiler's literal coordinate calculations. -/

meta section
namespace PushPuzzle.PushS

initialize
  discard <| Lean.Meta.registerSimpAttr `finite_line_coords "Local routed-line rotations, anchors and offsets"
initialize
  discard <| Lean.Meta.Simp.registerSimprocAttr `finite_line_coords_proc "Local routed-line rotations, anchors and offsets" none

initialize
  discard <| Lean.Meta.registerSimpAttr `finite_core_coords "Local core anchors, rectangles and outward coordinate bands"
initialize
  discard <| Lean.Meta.Simp.registerSimprocAttr `finite_core_coords_proc "Local core anchors, rectangles and outward coordinate bands" none

initialize
  discard <| Lean.Meta.registerSimpAttr `finite_gate_tool_coords "Local embedded A tools and straight-line endpoints"
initialize
  discard <| Lean.Meta.Simp.registerSimprocAttr `finite_gate_tool_coords_proc "Local embedded A tools and straight-line endpoints" none

initialize
  discard <| Lean.Meta.registerSimpAttr `finite_gate_access_coords "Local core access corridors and literal endpoints"
initialize
  discard <| Lean.Meta.Simp.registerSimprocAttr `finite_gate_access_coords_proc "Local core access corridors and literal endpoints" none

initialize
  discard <| Lean.Meta.registerSimpAttr `finite_gate_readout_coords "Local thick-core physical readout ports"
initialize
  discard <| Lean.Meta.Simp.registerSimprocAttr `finite_gate_readout_coords_proc "Local thick-core physical readout ports" none

end PushPuzzle.PushS
