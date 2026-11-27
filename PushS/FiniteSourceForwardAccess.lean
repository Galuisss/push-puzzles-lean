/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreDockAccess
public import PushS.FiniteSourceForward

/-! Actual anchor access on the one fixed target board used by the complete NCL replay. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical

attribute [local irreducible] codes

theorem canonical_walls (w : ℕ) (hw : 2 ≤ w) (word : Word) (a b target : List Bool) :
    (canonicalBoard w hw word target).walls = (inventory w hw (word,(a,b))).walls :=
  walls_rephase w hw word target target a b

variable {w : ℕ} {hw : 2 ≤ w} {word : Word}
  {f : Fin word.compile.edgeCount → Bool} {e : Fin word.compile.edgeCount}

theorem PathSite.canonical_arm_waveAccess {g : GateTileState} {role : Fin 3}
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w g role))
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (base : Fin (codes w (oneEdgeSource word f e)).length → Bool) :
    p.WaveAccess (armSpec_geometry w g role) base (canonicalBoard w hw word target)
      (inventory w hw (oneEdgeSource word f e)).player :=
  (p.normal_arm_waveAccess hP hT base).retarget
    (canonical_walls w hw word (configBits f) (configBits (reverse f e)) target).symm

theorem PathSite.canonical_wire_waveAccess {args : Catalog.Bitmap.Args}
    (p : PathSite w hw (oneEdgeSource word f e) (wireSpec w args))
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (base : Fin (codes w (oneEdgeSource word f e)).length → Bool) :
    p.WaveAccess (wireSpec_geometry w args) base (canonicalBoard w hw word target)
      (inventory w hw (oneEdgeSource word f e)).player :=
  (p.normal_wire_waveAccess hP hT base).retarget
    (canonical_walls w hw word (configBits f) (configBits (reverse f e)) target).symm

theorem CoreSite.canonical_anchorAccess (c : CoreSite w hw (oneEdgeSource word f e))
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (phase : Fin (codes w (oneEdgeSource word f e)).length → Bool) :
    c.AnchorAccess phase (canonicalBoard w hw word target)
      (inventory w hw (oneEdgeSource word f e)).player :=
  (c.normal_anchorAccess hP hT phase).retarget
    (canonical_walls w hw word (configBits f) (configBits (reverse f e)) target).symm

end PushPuzzle.PushS.FiniteSourceInventory
