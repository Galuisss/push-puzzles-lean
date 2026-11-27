/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Classifier
public import PushFS.Reduction.FullGateStatics.Linear

/-! The true central gate's canonical slots retain their own literal axis names in the complete annular classifier. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def coreLevelTest (g : GateTileState) (p : Gates.C) : Bool :=
  let s:=shape (chart g (.inl (.inl 0)))
  let u:=s.global (p.1.val,p.2.val)
  (chartIndices g).all fun c=>
    let t:=shape (chart g c)
    if t.Contains u then decide ((t.name (t.local u)).level≤(Gates.axisName g.core.isAND p).level) else true

def coreLevelsTest (g : GateTileState) : Bool :=
  (Gates.slots g.core.isAND).all fun s=>coreLevelTest g s.zero &&coreLevelTest g s.one

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
