/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateNormalAtomFrames
public import PushS.FiniteGatePreparedPhases

/-! Exact narrow cavity frames while the prepared tails retain every normal auxiliary. -/

public section
namespace PushPuzzle.PushS.FiniteGateCavityStockFrames

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateState
open FiniteGateVertical FiniteGateInputs FiniteGateOutputs FiniteGateBTriggers FiniteGateBForward
open scoped Classical

attribute [local irreducible] FiniteGeometry.side

private theorem frame_of_free {N : ℕ} (active : Finset (Cell N N)) (B : Board N N)
    (stock : Finset (Cell N N)) (hd : Disjoint stock B.walls)
    (hf : ∀ p ∈ active,Free B stock p) :
    FiniteWireFrame.Frame active (GridIsometry.refl N N).embedding B stock :=
  ⟨fun p hp => (hf p hp).1,fun p hp => (hf p hp).2,hd⟩

/-- B's exit is the two-cell horizontal interval on the row just above the cavity. -/
@[expose] def BExitShape (w col : ℕ) (p : Cell (side w) (side w)) : Prop :=
  p.2.val+1 = origin w ∧ origin w+col-1 ≤ p.1.val ∧ p.1.val ≤ origin w+col

theorem b_exit_shape (w col : ℕ) (hc : 3 ≤ col ∧ col ≤ 4)
    (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateBAmbient.exitActive w col hc) :
    BExitShape w col p := by
  simp only [FiniteGateBAmbient.exitActive,FiniteAtomFrames.mem_walkActive,point] at hp
  dsimp [BExitShape]
  unfold origin at *
  omega

theorem and_B_exit_frame (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 3 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅) (andBoxes w a true c) := by
  apply frame_of_free _ _ _ (andBoxes_disjoint_walls w hw a true c)
  intro p hp
  have hs := b_exit_shape w 3 (by omega) p hp
  apply and_near_B_free w hw a c ∅ p
  all_goals dsimp [BExitShape] at hs; omega

theorem or_B_exit_frame (w : ℕ) (hw : 2 ≤ w) (a c : Bool) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.exitActive w 4 (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅) (orBoxes w a true c) := by
  apply frame_of_free _ _ _ (orBoxes_disjoint_walls w hw a true c)
  intro p hp
  have hs := b_exit_shape w 4 (by omega) p hp
  apply or_near_B_free w hw a c ∅ p
  all_goals dsimp [BExitShape] at hs; omega

/-- B's mouth entry uses its closed row interval and the single cell above the mouth. -/
@[expose] def BEntryShape (w mouth col : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.2.val = origin w ∧ origin w+min mouth col ≤ p.1.val ∧ p.1.val ≤ origin w+max mouth col) ∨
    (p.2.val+1 = origin w ∧ p.1.val = origin w+mouth)

theorem b_entry_shape (w mouth col : ℕ) (hm : mouth ≤ w+8) (hc : col ≤ 4)
    (p : Cell (side w) (side w)) (hp : p ∈ FiniteGateBAmbient.entryActive w mouth col hm hc) :
    BEntryShape w mouth col p := by
  simp only [FiniteGateBAmbient.entryActive,Finset.mem_union,FiniteAtomFrames.mem_walkActive,point] at hp
  dsimp [BEntryShape]
  unfold origin at *
  omega

theorem and_B_entry_frame (w : ℕ) (hw : 2 ≤ w) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w (w+4) 3 (by omega) (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (andBoard w ∅) (andBBoxes w true false true) := by
  apply frame_of_free _ _ _ (andBBoxes_floor w hw true false ∅)
  intro p hp
  have hs := b_entry_shape w (w+4) 3 (by omega) (by omega) p hp
  apply andBBoxes_free w hw true false ∅
  · rcases hs with hs | hs
    · apply and_row_free w hw true true false ∅ p
      all_goals first | omega | (norm_num at *; omega)
    · apply and_above_free w hw true true false ∅ p
      all_goals omega
  · intro he
    have hx := congrArg (fun z => z.1.val) he
    have hy := congrArg (fun z => z.2.val) he
    dsimp [BEntryShape,point] at hs hx hy
    unfold origin at *
    omega

theorem or_B_entry_frame (w : ℕ) (hw : 2 ≤ w) (a c : Bool) (mouth : ℕ)
    (hm : mouth ≤ w+8) (hleft : 3 < min mouth 4+a.toNat)
    (hright : max mouth 4+c.toNat < w+6) (hopen : mouth ≤ 4 ∨ w+5 ≤ mouth) (hne : mouth ≠ 4) :
    FiniteWireFrame.Frame (FiniteGateBAmbient.entryActive w mouth 4 hm (by omega))
      (GridIsometry.refl (side w) (side w)).embedding (orBoard w ∅) (orBBoxes w a c true) := by
  apply frame_of_free _ _ _ (orBBoxes_floor w hw a c ∅)
  intro p hp
  have hs := b_entry_shape w mouth 4 hm (by omega) p hp
  have ha := Bool.toNat_le a
  have hc := Bool.toNat_le c
  apply orBBoxes_free w hw a c ∅
  · rcases hs with hs | hs
    · apply or_row_free w hw a true c ∅ p
      all_goals omega
    · apply or_above_free w hw a true c ∅ p
      all_goals omega
  · intro he
    have hx := congrArg (fun z => z.1.val) he
    have hy := congrArg (fun z => z.2.val) he
    dsimp [BEntryShape,point] at hs hx hy
    unfold origin at *
    omega

end PushPuzzle.PushS.FiniteGateCavityStockFrames
