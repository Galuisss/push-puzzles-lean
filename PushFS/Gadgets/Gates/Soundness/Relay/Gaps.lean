/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.AxisStrip

/-! Real static SCCs and actual successful-path gaps for every enumerated gate rail. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


open Wires.Soundness
set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- Each adjacent pair is connected in both directions by its true wall-supported local unit displacements. -/
private theorem pair_component (kind : Bool) (r : Rail) (s : Signals) (p : Label kind×Label kind)
    (hp : p∈pairs kind r) :
    SameComponent (board kind ∅) (position kind s p.1) (position kind s p.2) := by
  have check : ∀ (kind a b c : Bool) (r : Rail), ((pairs kind r).all fun p=>
      decide (staticRun (wallTest kind) (position kind ⟨a,b,c⟩ p.1)
          (Wires.Template.slotDirections (position kind ⟨a,b,c⟩ p.1) (position kind ⟨a,b,c⟩ p.2))=
        some (position kind ⟨a,b,c⟩ p.2)) &&
      decide (staticRun (wallTest kind) (position kind ⟨a,b,c⟩ p.2)
          (Wires.Template.slotDirections (position kind ⟨a,b,c⟩ p.2) (position kind ⟨a,b,c⟩ p.1))=
        some (position kind ⟨a,b,c⟩ p.1)))=true := by
    intro kind a b c r
    cases r <;> revert kind a b c <;> decide +kernel
  have hh:=List.all_eq_true.mp (check kind s.left s.upper s.right r) p hp
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨staticRun_sound (wallTest_correct kind ∅) hh.1,staticRun_sound (wallTest_correct kind ∅) hh.2⟩

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay

namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph

open Relay Wires.Soundness

variable {I : Instance} {L : Type} [Fintype L]

variable {M : SlotMatching I L} {A : AxisTracks I} {kind : Bool} (g : GateGlyph M A kind)

def offset (axis : Bool) : ℕ := if axis then g.dx else g.dy

/-- Local physical coordinates retain their exact global translation. -/
theorem source_coord (axis : Bool) (l : Label kind) : coord axis (M.source (g.labels l))=
    g.offset axis+(if axis then (position kind g.initialSignals l).1.val else (position kind g.initialSignals l).2.val) := by
  rw [g.sources]
  cases axis <;> rfl

theorem target_coord (axis : Bool) (l : Label kind) : coord axis (M.target (g.labels l))=
    g.offset axis+(if axis then (position kind g.targetSignals l).1.val else (position kind g.targetSignals l).2.val) := by
  rw [g.targets]
  cases axis <;> rfl

/-- Every physical rail member has its true global axis name. -/
private theorem rail_track (r : Rail) (l : Label kind) (hl : axisName kind
    (position kind g.initialSignals l)=r.tag kind) :
    A.name (M.source (g.labels l))=lineTag r.axis (g.offset (!r.axis)+r.line kind) := by
  rw [g.tracks,hl]
  cases r <;> simp [Rail.tag,Rail.axis,Rail.line,lineTag,AxisTrack.shift,offset]

/-- All finite adjacent-identity pairs have the real two-cell separation at every intermediate successful state. -/
theorem rail_gap {S final : LabelledState L I.width I.height} (h : Successful M S final) (cert : Certificate I)
    (r : Rail) (p : Label kind×Label kind) (hp : p∈pairs kind r) :
    coord r.axis (S.position (g.labels p.1))+2≤coord r.axis (S.position (g.labels p.2)) := by
  have hf:=pair_facts kind r g.initialSignals p hp
  have hc:=pair_component kind r g.initialSignals p hp
  have hcG : component I.board (M.source (g.labels p.1))=component I.board (M.source (g.labels p.2)) := by
    rw [g.sources,g.sources]
    exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hc.1,GridEmbedding.staticReach g.walls hc.2⟩
  apply h.gap cert A r.axis (g.offset (!r.axis)+r.line kind) (g.labels p.1) (g.labels p.2)
    (g.rail_track r p.1 hf.1) (g.rail_track r p.2 hf.2.1) hcG
  rw [g.source_coord,g.source_coord]
  exact Nat.add_lt_add_left hf.2.2 _

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph
