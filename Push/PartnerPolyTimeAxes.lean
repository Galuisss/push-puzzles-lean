/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerPolyTimeFold

/-! Polynomial-time execution of the complete direction words through the actual repair. -/

public section
namespace PushPuzzle.Push.Partner

open PushS Turing.MultiTapeTM
open scoped PushPuzzle.PushS PushPuzzle.Push.Partner

private theorem axes_length (axes : List Bool) : (encAxes axes).length = 3 * axes.length := by
  induction axes with
  | nil => rfl
  | cons a axes ih => simp [encAxes, encList_cons, encBool_apply] at *; omega

private theorem state_portCount (s : BufferState) :
    s.layout.portCount ≤ (encBufferState s).length + 2 :=
  (Resources.labels_of_code s.layout).portCount.trans
    (Nat.add_le_add_right (Resources.state_code_fields s).1 2)

private theorem scanAxes_length_or (s : BufferState) (positions : List ℕ) (axes : List Bool) :
    (scanAxes s positions axes).length = axes.length ∨
      (scanAxes s positions axes).length = (s.scan positions).layout.portCount := by
  induction positions generalizing s axes with
  | nil => exact Or.inl rfl
  | cons first rest ih =>
    have hstep : (bufferAtAxes s first axes).length = axes.length ∨
        (bufferAtAxes s first axes).length = (s.bufferAt first).layout.portCount := by
      unfold bufferAtAxes BufferState.bufferAt
      split_ifs <;> simp [earExtend, earState_length, BufferState.insertEar, ear]
    rcases hstep with hsame | hgood
    · rcases ih (s.bufferAt first) (bufferAtAxes s first axes) with h | h
      · exact Or.inl (h.trans hsame)
      · exact Or.inr h
    · exact Or.inr (scanAxes_length (s.bufferAt first) rest _ hgood)

namespace Cuts

private theorem scanAxes_length_or (s : BufferState) (positions : List ℕ) (axes : List Bool) :
    (scanAxes s positions axes).length = axes.length ∨
      (scanAxes s positions axes).length = (scan s positions).layout.portCount := by
  induction positions generalizing s axes with
  | nil => exact Or.inl rfl
  | cons cut rest ih =>
    have hstep : (cutAtAxes s cut axes).length = axes.length ∨
        (cutAtAxes s cut axes).length = (cutAt s cut).layout.portCount := by
      unfold cutAtAxes cutAt
      split_ifs <;> simp [cutExtend, cutState_length]
    rcases hstep with hsame | hgood
    · rcases ih (cutAt s cut) (cutAtAxes s cut axes) with h | h
      · exact Or.inl (h.trans hsame)
      · exact Or.inr h
    · exact Or.inr (scanAxes_length (cutAt s cut) rest _ hgood)

end Cuts

private theorem paired_code_le (s : BufferState) (axes original : List Bool)
    (h : axes.length = original.length ∨ axes.length = s.layout.portCount) :
    (encScanState (s, axes)).length ≤ 5 * (encBufferState s).length + (encAxes original).length + 7 := by
  have hn := state_portCount s
  simp only [encScanState, length_encPair, axes_length]
  rcases h with h | h <;> omega

namespace BufferState

@[fun_prop] theorem scanPair_polyTime : ComputableInPolyTime
    (fun p : (BufferState × List Bool) × List ℕ => p.2.foldl scanStep p.1)
    (encPair encScanState (encList encUnary)) encScanState := by
  have hl : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.2)
      (encPair encScanState (encList encUnary)) (encList encUnary) := by fun_prop
  have hs : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.1.1)
      (encPair encScanState (encList encUnary)) encBufferState := by unfold encScanState; fun_prop
  have ha : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.1.2)
      (encPair encScanState (encList encUnary)) encAxes := by unfold encScanState; fun_prop
  have hinit : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.1)
      (encPair encScanState (encList encUnary)) encScanState := by fun_prop
  have hsize := hs.polyBounded_length
  have hlist := hl.polyBounded_length
  have haxes := ha.polyBounded_length
  refine ComputableInPolyTime.foldl' hl hinit scanStep_polyTime
    (B := fun p => 5 * (100 * ((encBufferState p.1.1).length +
      2 * (encList encUnary p.2).length + 3) ^ 2) + (encAxes p.1.2).length + 7) ?_ ?_
  · exact (((PolyBounded.const 5).mul ((PolyBounded.const 100).mul
      (((hsize.add ((PolyBounded.const 2).mul hlist)).add (PolyBounded.const 3)).pow 2))).add
        haxes).add (PolyBounded.const 7)
  · intro p i _
    rw [scanStep_fold]
    exact (paired_code_le _ _ _ (Partner.scanAxes_length_or _ _ _)).trans
      (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left 5 (Resources.internal_prefix_code p.1.1 p.2 i)) _) _)

end BufferState
namespace Cuts

@[fun_prop] theorem scanPair_polyTime : ComputableInPolyTime
    (fun p : (BufferState × List Bool) × List ℕ => p.2.foldl scanStep p.1)
    (encPair encScanState (encList encUnary)) encScanState := by
  have hl : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.2)
      (encPair encScanState (encList encUnary)) (encList encUnary) := by fun_prop
  have hs : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.1.1)
      (encPair encScanState (encList encUnary)) encBufferState := by unfold encScanState; fun_prop
  have ha : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.1.2)
      (encPair encScanState (encList encUnary)) encAxes := by unfold encScanState; fun_prop
  have hinit : ComputableInPolyTime (fun p : (BufferState × List Bool) × List ℕ => p.1)
      (encPair encScanState (encList encUnary)) encScanState := by fun_prop
  have hsize := hs.polyBounded_length
  have hlist := hl.polyBounded_length
  have haxes := ha.polyBounded_length
  refine ComputableInPolyTime.foldl' hl hinit scanStep_polyTime
    (B := fun p => 5 * (100 * ((encBufferState p.1.1).length +
      2 * (encBufferState p.1.1).length * (encList encUnary p.2).length + 3) ^ 2) +
        (encAxes p.1.2).length + 7) ?_ ?_
  · exact (((PolyBounded.const 5).mul ((PolyBounded.const 100).mul
      (((hsize.add (((PolyBounded.const 2).mul hsize).mul hlist)).add (PolyBounded.const 3)).pow 2))).add
        haxes).add (PolyBounded.const 7)
  · intro p i _
    rw [scanStep_fold]
    exact (paired_code_le _ _ _ (scanAxes_length_or _ _ _)).trans
      (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left 5 (Resources.cut_prefix_code p.1.1 p.2 i)) _) _)

end Cuts

@[fun_prop] theorem scanAxes_polyTime : ComputableInPolyTime
    (fun p : BufferState × List ℕ × List Bool => scanAxes p.1 p.2.1 p.2.2)
    (encPair encBufferState (encPair (encList encUnary) encAxes)) encAxes := by
  have hargs : ComputableInPolyTime
      (fun p : BufferState × List ℕ × List Bool => ((p.1, p.2.2), p.2.1))
      (encPair encBufferState (encPair (encList encUnary) encAxes))
      (encPair encScanState (encList encUnary)) := by unfold encScanState; fun_prop
  have hraw := (ComputableInPolyTime.snd encBufferState encAxes).comp
    (BufferState.scanPair_polyTime.comp hargs)
  exact hraw.of_enc_eq (by intro p; simp only [Function.comp_def, BufferState.scanStep_fold])

@[fun_prop] theorem internalAxes_polyTime : ComputableInPolyTime
    (fun p : PortLayout × List Bool => internalAxes p.1 p.2)
    (encPair encPortLayout encAxes) encAxes := by
  unfold internalAxes
  fun_prop

namespace Cuts

@[fun_prop] theorem scanAxes_polyTime : ComputableInPolyTime
    (fun p : BufferState × List ℕ × List Bool => scanAxes p.1 p.2.1 p.2.2)
    (encPair encBufferState (encPair (encList encUnary) encAxes)) encAxes := by
  have hargs : ComputableInPolyTime
      (fun p : BufferState × List ℕ × List Bool => ((p.1, p.2.2), p.2.1))
      (encPair encBufferState (encPair (encList encUnary) encAxes))
      (encPair encScanState (encList encUnary)) := by unfold encScanState; fun_prop
  have hraw := (ComputableInPolyTime.snd encBufferState encAxes).comp
    (scanPair_polyTime.comp hargs)
  exact hraw.of_enc_eq (by intro p; simp only [Function.comp_def, scanStep_fold])

@[fun_prop] theorem repairAxes_polyTime : ComputableInPolyTime
    (fun p : PortLayout × List Bool => repairAxes p.1 p.2)
    (encPair encPortLayout encAxes) encAxes := by
  unfold repairAxes
  fun_prop

end Cuts
end PushPuzzle.Push.Partner
