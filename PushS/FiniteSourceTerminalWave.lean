/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceSuccessorSignals
public import PushS.FiniteSourceEdgeGateForward

/-! Every real path wave retains its genuinely prepared downstream consuming port. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical

attribute [local irreducible] codes width height Raster.width Raster.height

variable {w : ℕ} {hw : 2 ≤ w} {word : Word}
  {f : Fin word.compile.edgeCount → Bool} {e : Fin word.compile.edgeCount}

theorem wire_wave_consumer_low (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    {a : Catalog.Bitmap.Args} (d : ℕ) (t : PathSite w hw (oneEdgeSource word f e) (wireSpec w a))
    (hc : CellPlan.cell (oneEdgeSource word f e,t.location) = some (.inr (d,a)))
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase t.location)
    (cut : ℕ) (i : Fin (codes w (oneEdgeSource word f e)).length)
    (hn : neighbor (Catalog.targetDirection a.1) t.location = some ((codes w (oneEdgeSource word f e)).get i).1) :
    ConsumerLow (CellPlan.cell (oneEdgeSource word f e,((codes w (oneEdgeSource word f e)).get i).1))
      (Catalog.targetDirection a.1).opposite (t.wave (tilePhases phase) cut i) := by
  rw [t.wave_outside (tilePhases phase) cut i (by
    intro b hb
    have hh := congrArg (fun j => ((codes w (oneEdgeSource word f e)).get j).1) hb
    rw [b.owner_location] at hh
    exact FiniteRouting.neighbor_ne hn hh)]
  exact wire_successor_consumer_low word hP hT f e phase t.location _ H d a hc hn

theorem arm_wave_consumer_low (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (hloc : p.location = ((codes w (oneEdgeSource word f e)).get c.index).1)
    (vertex : VertexData) (hc : CellPlan.cell (oneEdgeSource word f e,p.location) = some (.inl (vertex,c.gate)))
    (he : (vertex.ports.port role).edge = e.val) (hin : c.gate.incoming.get role = false)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location)
    (cut : ℕ) (i : Fin (codes w (oneEdgeSource word f e)).length)
    (hn : neighbor (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)) p.location =
      some ((codes w (oneEdgeSource word f e)).get i).1) :
    ConsumerLow (CellPlan.cell (oneEdgeSource word f e,((codes w (oneEdgeSource word f e)).get i).1))
      (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)).opposite
      (p.wave (c.preparedArmBase role (tilePhases phase)) cut i) := by
  rw [p.wave_outside _ cut i (by
    intro b hb
    have hh := congrArg (fun j => ((codes w (oneEdgeSource word f e)).get j).1) hb
    rw [b.owner_location] at hh
    exact FiniteRouting.neighbor_ne hn hh)]
  rw [c.preparedArmBase_external role _ i (by
    intro hi
    have hh : p.location = ((codes w (oneEdgeSource word f e)).get i).1 := by rw [hi]; exact hloc
    exact FiniteRouting.neighbor_ne hn hh)]
  exact gate_successor_consumer_low word hP hT f e phase p.location _ H vertex c.gate hc role he hin hn

end PushPuzzle.PushS.FiniteSourceInventory
