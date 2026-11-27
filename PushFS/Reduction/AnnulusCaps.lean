/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusLines

/-! Actual zero-box wall caps complete the third exterior padding column of output gate ports. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


/-- Two guard walls and their actual free rail cell, with no owned storage identities. -/
def capBase : Instance where
  width := 1
  height := 3
  board := ⟨{(0,1),(0,2)},∅⟩
  initial := ⟨(0,0),∅⟩
  goals_floor := by decide +kernel
  initial_valid := by
    refine ⟨?_,?_,?_⟩ <;> decide +kernel
  boxes_eq_goals := rfl

def capMatching : SlotMatching capBase (Fin 0) where
  source := ⟨Fin.elim0,by intro l; exact l.elim0⟩
  target := ⟨Fin.elim0,by intro l; exact l.elim0⟩
  source_image := by simp [capBase]
  target_image := by simp [capBase]
  connected l := l.elim0

def capOrientation : Direction→RectOrientation
  | .west | .east => ⟨false,false,false⟩
  | .north | .south => ⟨true,true,false⟩

def capIso (k : GateAnnulus.Key) := (capOrientation (PortAnnulus.outerDirection k.2)).axis 1 3

def capPiece (k : GateAnnulus.Key) : Instance := GridIsometry.reorientInstance capBase (capIso k).geometry

def capSlotMatching (k : GateAnnulus.Key) : SlotMatching (capPiece k) (Fin 0) :=
  capMatching.reorient (capIso k).geometry

def capOffset (k : GateAnnulus.Key) : ℕ×ℕ :=
  let p := boundary k
  match PortAnnulus.outerDirection k.2 with
  | .east => (p.1+3,p.2)
  | .west => (p.1-3,p.2)
  | .south => (p.1-2,p.2+3)
  | .north => (p.1-2,p.2-3)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem cap_fits : ∀ k : GateAnnulus.Key,
    (capOffset k).1+(capOrientation (PortAnnulus.outerDirection k.2)).width 1 3≤200007 ∧
    (capOffset k).2+(capOrientation (PortAnnulus.outerDirection k.2)).height 1 3≤198068 := by decide +kernel

end PushPuzzle.PushFS.Reduction.GateTileRouting
