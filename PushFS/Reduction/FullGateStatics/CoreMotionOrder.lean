/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.MotionOrder

/-! Disjoint central-core slot motions preserve every common-row or common-column source order. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Gadgets
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem core_apart_checked : ∀kind : Bool,(Gates.slots kind).all fun s=>(Gates.slots kind).all fun t=>
    decide (s=t ∨(Envelope.motionSlot s 0 0).MotionApart (Envelope.motionSlot t 0 0)) := by decide +kernel

private theorem slot_contains (s : Gates.Slot) (a : Gates.Signals) :
    (Envelope.motionSlot s 0 0).Contains ((s.position a).1.val,(s.position a).2.val) := by
  simp only [Envelope.motionSlot,Nat.zero_add]
  unfold Gates.Slot.position
  split
  · exact Envelope.join_contains_right _ _ _ (Envelope.point_contains _)
  · exact Envelope.join_contains_left _ _ _ (Envelope.point_contains _)

/-- Central-core identities retain both source rail orders without a local SCC premise. -/
theorem core_slot_rail_order (kind : Bool) (a b : Gates.Signals) (s t : Gates.Slot)
    (hs : s∈Gates.slots kind) (ht : t∈Gates.slots kind) :
    ((s.position a).2=(t.position a).2 →(s.position a).1.val<(t.position a).1.val →(s.position b).1.val<(t.position b).1.val) ∧
    ((s.position a).1=(t.position a).1 →(s.position a).2.val<(t.position a).2.val →(s.position b).2.val<(t.position b).2.val) := by
  have hh:=of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (core_apart_checked kind) s hs) t ht)
  rcases hh with rfl|hh
  · exact ⟨fun _ ho=>False.elim (Nat.lt_irrefl _ ho),fun _ ho=>False.elim (Nat.lt_irrefl _ ho)⟩
  · have ho:=interval_order (Envelope.motionSlot s 0 0) (Envelope.motionSlot t 0 0) _ _ _ _
      (slot_contains s a) (slot_contains t a) (slot_contains s b) (slot_contains t b) hh
    exact ⟨fun he hx=>ho.1 (congrArg Fin.val he) hx,fun he hy=>ho.2 (congrArg Fin.val he) hy⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
