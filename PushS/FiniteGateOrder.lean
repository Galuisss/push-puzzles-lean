/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateTracks

/-! The complete normal source and target inventories retain every order on a physical core rail. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateTracks

open PushFS FiniteGeometry PushFS.Gadgets

attribute [local irreducible] side

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- Normal AND phases keep the literal order on each rail. -/
theorem andTrack_order (w : ℕ) (hw : 2 ≤ w) (s t : Gates.Signals) (l m : AndLabel w)
    (ht : andTrack w l = andTrack w m) :
    ((andCell w s.left s.upper s.right l).1.val < (andCell w s.left s.upper s.right m).1.val →
      (andCell w t.left t.upper t.right l).1.val < (andCell w t.left t.upper t.right m).1.val) ∧
    ((andCell w s.left s.upper s.right l).2.val < (andCell w s.left s.upper s.right m).2.val →
      (andCell w t.left t.upper t.right l).2.val < (andCell w t.left t.upper t.right m).2.val) := by
  have hsa := Bool.toNat_le s.left
  have hsb := Bool.toNat_le s.upper
  have hsc := Bool.toNat_le s.right
  have hta := Bool.toNat_le t.left
  have htb := Bool.toNat_le t.upper
  have htc := Bool.toNat_le t.right
  cases l <;> cases m <;> simp [andTrack,origin] at ht
  all_goals constructor <;> intro ho
  all_goals simp only [andCell,andPoint] at ho ⊢
  all_goals unfold origin at *
  all_goals omega

set_option maxRecDepth 8192 in
theorem orTrack_order (w : ℕ) (hw : 2 ≤ w) (s t : Gates.Signals) (l m : OrLabel w)
    (ht : orTrack w l = orTrack w m) :
    ((orCell w s.left s.upper s.right l).1.val < (orCell w s.left s.upper s.right m).1.val →
      (orCell w t.left t.upper t.right l).1.val < (orCell w t.left t.upper t.right m).1.val) ∧
    ((orCell w s.left s.upper s.right l).2.val < (orCell w s.left s.upper s.right m).2.val →
      (orCell w t.left t.upper t.right l).2.val < (orCell w t.left t.upper t.right m).2.val) := by
  have hsa := Bool.toNat_le s.left
  have hsb := Bool.toNat_le s.upper
  have hsc := Bool.toNat_le s.right
  have hta := Bool.toNat_le t.left
  have htb := Bool.toNat_le t.upper
  have htc := Bool.toNat_le t.right
  cases l <;> cases m <;> simp [orTrack,origin] at ht
  all_goals constructor <;> intro ho
  all_goals simp only [orCell,orPoint] at ho ⊢
  all_goals unfold origin at *
  all_goals omega

end PushPuzzle.PushS.FiniteGateTracks
