/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.AxisGeometry
public import PushFS.Gadgets.Gates.Triggers
public import PushFS.Gadgets.Wires.Soundness
public import PushFS.AxisCharts

/-! Literal wall and trigger-slot facts of the complete long-wall AND/OR gates. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness


open Wires.Soundness

set_option maxRecDepth 65536
set_option maxHeartbeats 0

def junction (kind : Bool) : ℕ := if kind then 43 else 44

def triggerD (kind : Bool) : Fin (slots kind).length :=
  ⟨0,by rw [slots_length]; cases kind <;> decide⟩

theorem trigger_axes (kind : Bool) (b : Signals) :
    axisName kind (position kind b (triggerA kind)) = .horizontal 90 ∧
    axisName kind (position kind b (triggerB kind)) = .vertical (junction kind) ∧
    axisName kind (position kind b (triggerC kind)) = .horizontal 90 ∧
    (kind=true → axisName kind (position kind b (triggerD kind)) = .horizontal 90) := by
  have hh : ∀ (kind a b c : Bool),
      axisName kind (position kind ⟨a,b,c⟩ (triggerA kind)) = .horizontal 90 ∧
      axisName kind (position kind ⟨a,b,c⟩ (triggerB kind)) = .vertical (junction kind) ∧
      axisName kind (position kind ⟨a,b,c⟩ (triggerC kind)) = .horizontal 90 ∧
      (kind=true → axisName kind (position kind ⟨a,b,c⟩ (triggerD kind)) = .horizontal 90) := by decide +kernel
  exact hh kind b.left b.upper b.right

theorem trigger_order (kind : Bool) (b : Signals) :
    (position kind b (triggerA kind)).1.val < (position kind b (triggerC kind)).1.val ∧
    (position kind b (triggerB kind)).2.val < 90 ∧
    (kind=true → 39 < (position kind b (triggerD kind)).1.val ∧
      (position kind b (triggerD kind)).1.val < (position kind b (triggerA kind)).1.val) := by
  have hh : ∀ (kind a b c : Bool),
      (position kind ⟨a,b,c⟩ (triggerA kind)).1.val < (position kind ⟨a,b,c⟩ (triggerC kind)).1.val ∧
      (position kind ⟨a,b,c⟩ (triggerB kind)).2.val < 90 ∧
      (kind=true → 39 < (position kind ⟨a,b,c⟩ (triggerD kind)).1.val ∧
        (position kind ⟨a,b,c⟩ (triggerD kind)).1.val < (position kind ⟨a,b,c⟩ (triggerA kind)).1.val) := by decide +kernel
  exact hh kind b.left b.upper b.right

/-- The protected D/A pair is joined by two actual east/west static displacements. -/
theorem da_component (b : Signals) : SameComponent (board true ∅)
    (position true b (triggerD true)) (position true b (triggerA true)) := by
  have hh : ∀ (a b c : Bool),
      Gates.staticRun (wallTest true) (position true ⟨a,b,c⟩ (triggerD true)) [.east,.east] =
        some (position true ⟨a,b,c⟩ (triggerA true)) ∧
      Gates.staticRun (wallTest true) (position true ⟨a,b,c⟩ (triggerA true)) [.west,.west] =
        some (position true ⟨a,b,c⟩ (triggerD true)) := by decide +kernel
  have hb := hh b.left b.upper b.right
  exact ⟨Gates.staticRun_sound (wallTest_correct true ∅) hb.1,
    Gates.staticRun_sound (wallTest_correct true ∅) hb.2⟩

/-- All five literal cavity wall cells are present in either actual long-wall gate. -/
theorem cavity_walls (kind : Bool) : AND.CavityWalls (board kind ∅) (junction kind) 90 := by
  have below : ∀ (kind : Bool) (p : C), p.2.val=91 → junction kind ≤ p.1.val →
      p.1.val ≤ junction kind+2 → wallTest kind p=true := by decide +kernel
  have roof : ∀ (kind : Bool) (p : C), p.2.val+1=90 →
      (p.1.val=junction kind+1 ∨ p.1.val=junction kind+2) → wallTest kind p=true := by decide +kernel
  exact ⟨fun p hy hl hh => (wallTest_correct kind ∅ p).mp (below kind p hy hl hh),
    fun p hy hx => (wallTest_correct kind ∅ p).mp (roof kind p hy hx)⟩

end PushPuzzle.PushFS.Gadgets.Gates.Soundness
