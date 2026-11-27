/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateLips

/-! Every selected thick-gate branch has its complete real-board physical step. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.GatePhysicalContext

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateSelected FiniteGateFaceGeometry FiniteGateFaceBridge
open FiniteGateAStraight FiniteGateVertical FiniteGateInputs FiniteGateOutputs FiniteGateBTemporary
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {c : CoreSite w hw v}
  {B : Board (width w v) (height w v)}

theorem and_left_on {p : PathSite w hw v (armSpec w c.gate 0)}
    (C : GatePhysicalContext c 0 p B) (hg : c.gate.core.isAND = true) (b : Bool) :
    AndStep w c.embedding B C.outside ⟨false,b,false⟩ ⟨true,b,false⟩ := by
  refine .left_on b
    (c.and_A_frames hg p C.location C.admissible C.phase C.fresh C.reversed b false B C.walls)
    (c.and_A_forward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed b B C.walls) ?_
  have A := C.andAccess hg (stage w b false 7)
  have he : (Segment.guard.sweep w).hub = point w 1 1 := rfl
  rw [he]
  simpa only [GridEmbedding.extend] using A.left_right _ _
    (point_left_mem w hw true 1 1 (by decide) (by omega))
    (point_right_mem w hw true (w+4) (by dsimp [column]; omega))

theorem and_left_off {p : PathSite w hw v (armSpec w c.gate 0)}
    (C : GatePhysicalContext c 0 p B) (hg : c.gate.core.isAND = true) (b d : Bool) :
    AndStep w c.embedding B C.outside ⟨true,b,d⟩ ⟨false,b,d⟩ :=
  .left_off b d
    (c.and_A_frames hg p C.location C.admissible C.phase C.fresh C.reversed b d B C.walls)
    (c.and_A_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed b d B C.walls)

theorem and_upper_on_open {p : PathSite w hw v (armSpec w c.gate 1)}
    (C : GatePhysicalContext c 1 p B) (hg : c.gate.core.isAND = true) :
    AndStep w c.embedding B C.outside ⟨true,false,false⟩ ⟨true,true,false⟩ := by
  refine .upper_on_open
    (c.and_B_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed true false B C.walls)
    (c.and_B_entry_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls)
    (c.and_B_raise_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed false B C.walls)
    (c.and_B_exit_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed true false B C.walls) ?_
  have A := C.andAccess hg (andBPhases w true false true)
  simpa only [GridEmbedding.extend,andMixedBoxes_B] using A.left_right _ _
    (point_left_mem w hw true 2 2 (by decide) (by omega))
    (point_right_mem w hw true (w+4) (by dsimp [column]; omega))

theorem and_upper_on_closed {p : PathSite w hw v (armSpec w c.gate 1)}
    (C : GatePhysicalContext c 1 p B) (hg : c.gate.core.isAND = true) :
    AndStep w c.embedding B C.outside ⟨false,false,false⟩ ⟨false,true,false⟩ := by
  refine .upper_on_closed
    (c.and_B_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false B C.walls)
    (c.and_B_closed_approach_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls)
    (c.and_B_closed_A_push_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls)
    (c.and_B_temporary_raise_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls)
    (c.and_B_temporary_exit_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls)
    (c.and_B_restore_A_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls) ?_
  have A := C.andAccess hg (andTemporaryPhases w)
  simpa only [GridEmbedding.extend,andMixedBoxes_temporary w hw] using A.left_right _ _
    (point_left_mem w hw true 2 1 (by decide) (by omega))
    (point_right_mem w hw true (w+4) (by dsimp [column]; omega))

theorem and_upper_off {p : PathSite w hw v (armSpec w c.gate 1)}
    (C : GatePhysicalContext c 1 p B) (hg : c.gate.core.isAND = true) (a d : Bool) :
    AndStep w c.embedding B C.outside ⟨a,true,d⟩ ⟨a,false,d⟩ :=
  .upper_off a d
    (c.and_B_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed a d B C.walls)
    (c.and_B_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed a d B C.walls)

theorem and_right_on {p : PathSite w hw v (armSpec w c.gate 2)}
    (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = true) (a b : Bool) :
    AndStep w c.embedding B C.outside ⟨a,b,false⟩ ⟨a,b,true⟩ :=
  .right_on a b
    (c.and_C_forward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed a b B C.walls)
    (c.and_C_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed a b B C.walls)

theorem and_right_off {p : PathSite w hw v (armSpec w c.gate 2)}
    (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = true) :
    AndStep w c.embedding B C.outside ⟨true,true,true⟩ ⟨true,true,false⟩ := by
  refine .right_off
    (c.and_C_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed true true B C.walls)
    (c.and_C_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed B C.walls) ?_
  have A := C.andAccess hg (andOutputPhases w true true false)
  have hf := A.right_left _ _
    (point_right_mem w hw true (w+6) (by dsimp [column]; omega))
    (point_left_mem w hw true 2 1 (by decide) (by omega))
  rw [andMixedBoxes_output] at hf
  exact hf.trans (FiniteAtomFrames.walk_ambient _ _ c.embedding (C.and_output_lip hg))

theorem or_left_on_closed {p : PathSite w hw v (armSpec w c.gate 0)}
    (C : GatePhysicalContext c 0 p B) (hg : c.gate.core.isAND = false) :
    OrStep w c.embedding B C.outside ⟨false,false,false⟩ ⟨true,false,false⟩ := by
  refine .left_on_closed
    (c.or_A_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false B C.walls)
    (c.or_A_forward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false
      (w+5) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (by simp) B C.walls) ?_
  have A := C.orAccess hg (orInputPhases w false false true)
  simpa only [GridEmbedding.extend,orMixedBoxes_input] using A.left_right _ _
    (point_left_mem w hw false 1 1 (by decide) (by omega))
    (point_right_mem w hw false (w+5) (by dsimp [column]; omega))

theorem or_left_on_open {p : PathSite w hw v (armSpec w c.gate 0)}
    (C : GatePhysicalContext c 0 p B) (hg : c.gate.core.isAND = false) (d : Bool) :
    OrStep w c.embedding B C.outside ⟨false,true,d⟩ ⟨true,true,d⟩ := by
  have hd := Bool.toNat_le d
  exact .left_on_open d
    (c.or_A_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed true d B C.walls)
    (c.or_A_forward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed true d
      4 (by omega) (by omega) (Or.inl (by omega)) (Or.inr rfl) (by omega) B C.walls)
    (c.or_A_open_walk_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed d B C.walls)

theorem or_left_off {p : PathSite w hw v (armSpec w c.gate 0)}
    (C : GatePhysicalContext c 0 p B) (hg : c.gate.core.isAND = false) (b d : Bool) :
    OrStep w c.embedding B C.outside ⟨true,b,d⟩ ⟨false,b,d⟩ :=
  .left_off b d
    (c.or_A_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed b d B C.walls)
    (c.or_A_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed b d B C.walls)

theorem or_upper_on_closed {p : PathSite w hw v (armSpec w c.gate 1)}
    (C : GatePhysicalContext c 1 p B) (hg : c.gate.core.isAND = false) :
    OrStep w c.embedding B C.outside ⟨false,false,false⟩ ⟨false,true,false⟩ := by
  refine .upper_on_closed
    (c.or_B_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false B C.walls)
    (c.or_B_entry_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false (w+5)
      (by omega) (by simp)
      (by simp) (Or.inr (by omega)) (by omega) B C.walls)
    (c.or_B_raise_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false B C.walls)
    (c.or_B_exit_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed false false B C.walls) ?_
  have A := C.orAccess hg (orBPhases w false false true)
  simpa only [GridEmbedding.extend,orMixedBoxes_B] using A.left_right _ _
    (point_left_mem w hw false 3 2 (by decide) (by omega))
    (point_right_mem w hw false (w+5) (by dsimp [column]; omega))

theorem or_upper_on_open {p : PathSite w hw v (armSpec w c.gate 1)}
    (C : GatePhysicalContext c 1 p B) (hg : c.gate.core.isAND = false) (d : Bool) :
    OrStep w c.embedding B C.outside ⟨true,false,d⟩ ⟨true,true,d⟩ := by
  have hd := Bool.toNat_le d
  exact .upper_on_open d
    (c.or_B_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed true d B C.walls)
    (c.or_B_entry_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed true d 3
      (by omega) (by decide) (by norm_num; omega) (Or.inl (by omega)) (by omega) B C.walls)
    (c.or_B_raise_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed true d B C.walls)
    (c.or_B_exit_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed true d B C.walls)
    (c.or_B_open_walk_actual_frame hg p C.location C.admissible C.phase C.fresh C.reversed d B C.walls)

theorem or_upper_off {p : PathSite w hw v (armSpec w c.gate 1)}
    (C : GatePhysicalContext c 1 p B) (hg : c.gate.core.isAND = false) (a d : Bool) :
    OrStep w c.embedding B C.outside ⟨a,true,d⟩ ⟨a,false,d⟩ :=
  .upper_off a d
    (c.or_B_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed a d B C.walls)
    (c.or_B_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed a d B C.walls)

theorem or_right_on {p : PathSite w hw v (armSpec w c.gate 2)}
    (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = false) (a b : Bool) :
    OrStep w c.embedding B C.outside ⟨a,b,false⟩ ⟨a,b,true⟩ :=
  .right_on a b
    (c.or_C_forward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed a b B C.walls)
    (c.or_C_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed a b B C.walls)

theorem or_right_off_A {p : PathSite w hw v (armSpec w c.gate 2)}
    (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = false) (b : Bool) :
    OrStep w c.embedding B C.outside ⟨true,b,true⟩ ⟨true,b,false⟩ := by
  refine .right_off_A b
    (c.or_C_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed true b B C.walls)
    (c.or_C_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed true b 3
      (by omega) (by decide) (Or.inl (by omega)) B C.walls) ?_
  have A := C.orAccess hg (orOutputPhases w true b false)
  simpa only [GridEmbedding.extend,orMixedBoxes_output] using A.right_left _ _
    (point_right_mem w hw false (w+7) (by dsimp [column]; omega))
    (point_left_mem w hw false 3 1 (by decide) (by omega))

theorem or_right_off_B {p : PathSite w hw v (armSpec w c.gate 2)}
    (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = false) :
    OrStep w c.embedding B C.outside ⟨false,true,true⟩ ⟨false,true,false⟩ := by
  refine .right_off_B
    (c.or_C_sweep_frame hg p C.location C.admissible C.phase C.fresh C.reversed false true B C.walls)
    (c.or_C_backward_trigger_frame hg p C.location C.admissible C.phase C.fresh C.reversed false true 4
      (by omega) (by decide) (Or.inr rfl) B C.walls) ?_
  have A := C.orAccess hg (orOutputPhases w false true false)
  have hf := A.right_left _ _
    (point_right_mem w hw false (w+7) (by dsimp [column]; omega))
    (point_left_mem w hw false 3 1 (by decide) (by omega))
  rw [orMixedBoxes_output] at hf
  exact hf.trans (FiniteAtomFrames.walk_ambient _ _ c.embedding (C.or_output_lip hg))

end PushPuzzle.PushS.FiniteSourceInventory.GatePhysicalContext
