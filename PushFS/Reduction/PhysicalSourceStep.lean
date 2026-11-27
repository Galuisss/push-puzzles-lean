/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
public import PushFS.Reduction.PhysicalEdgeLocal
public import PushFS.Reduction.PhysicalEdgeSweep
public import PushFS.Reduction.PhysicalPlayerWalking

/-! A legal original NCL step is a complete canonical Push-1FS trajectory on the original fixed physical board. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires SourceCanonical
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes

private theorem edge_tile_update (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount)
    (hc : (Word.compile w).graph.Legal c) (hd : (Word.compile w).graph.Legal (reverse c e))
    (f : Fin (Fintype.card (Index (edgeSource w c e)))→Bool) (i : Index (edgeSource w c e))
    (frontier : EdgeFrontier (edgeSource w c e) e.val f i) :
    Reachable (atlas (edgeSource w c e) hP hT).board (some 1)
      ((atlas (edgeSource w c e) hP hT).profileAt f (atlas (edgeSource w c e) hP hT).player)
      ((atlas (edgeSource w c e) hP hT).profileAt (Function.update f (numbering (edgeSource w c e) i) true)
        (atlas (edgeSource w c e) hP hT).player) :=
  (profile_hubs _ hP hT f i).1.trans ((edge_tile_update_at w hw hP hT c e hc hd f i frontier).trans
    (profile_hubs _ hP hT (Function.update f (numbering (edgeSource w c e) i) true) i).2)

/-- Every legal original source reversal is realized by complete canonical configurations on its original physical board. -/
theorem canonical_step (v : CellPlan.Source) (hw : (Word.compile v.1).Valid) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    {c d : Fin (Word.compile v.1).edgeCount→Bool} (hstep : (Word.compile v.1).graph.Step c d) :
    Reachable (atlas v hP hT).board (some 1) (canonical v hP hT (configBits c)) (canonical v hP hT (configBits d)) := by
  obtain ⟨hc,hd,e,rfl⟩:=hstep
  exact canonical_of_profile_replay v hP hT (configBits c) (configBits (reverse c e))
    (edge_replay v.1 hw hP hT c e (edge_tile_update v.1 hw hP hT c e hc hd))

end PushPuzzle.PushFS.Reduction.PhysicalInventory
