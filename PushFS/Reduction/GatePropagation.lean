/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Collar

/-! Composition of actual core and buffer macros in any physical board. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction

open Gadgets

namespace GatePropagation

variable {W H : ℕ} {kind : Bool} {B : Board W H} {S : Gates.Signals → Gates.Signals → State W H}

/-- Propagate one canonical left change using only the actual core and that one lead. -/
theorem change_left (hgate : ∀ a b, Gates.legal kind a → Gates.legal kind b → Gates.singleChange a b →
      Reachable B (some 1) (S a (Gates.neighborSignals a b)) (S b (Gates.neighborSignals a b)))
    (hwire : ∀ a c, a.left=false → ∀ b, Reachable B (some 1) (S a c) (S a ⟨b,c.upper,c.right⟩)) (x y u r : Bool) (hxy : x≠y) (ha : Gates.legal kind ⟨x,u,r⟩) (hb : Gates.legal kind ⟨y,u,r⟩) :
    Reachable B (some 1) (S ⟨x,u,r⟩ ⟨x,u,r⟩)
      (S ⟨y,u,r⟩ ⟨y,u,r⟩) := by
  cases x <;> cases y
  · exact False.elim (hxy rfl)
  · have hg := hgate ⟨false,u,r⟩ ⟨true,u,r⟩ ha hb (by simp [Gates.singleChange])
    have hw := hwire ⟨false,u,r⟩ ⟨false,u,r⟩ rfl true
    apply hw.trans
    simpa [Gates.neighborSignals,Gates.changingPort] using hg
  · have hg := hgate ⟨true,u,r⟩ ⟨false,u,r⟩ ha hb (by simp [Gates.singleChange])
    have hw := hwire ⟨false,u,r⟩ ⟨true,u,r⟩ rfl false
    apply Relation.ReflTransGen.trans (b := S ⟨false,u,r⟩ ⟨true,u,r⟩) ?_ hw
    simpa [Gates.neighborSignals,Gates.changingPort] using hg
  · exact False.elim (hxy rfl)

/-- Propagate one canonical upper change using only the actual core and that one lead. -/
theorem change_upper (hgate : ∀ a b, Gates.legal kind a → Gates.legal kind b → Gates.singleChange a b →
      Reachable B (some 1) (S a (Gates.neighborSignals a b)) (S b (Gates.neighborSignals a b)))
    (hwire : ∀ a c, a.upper=false → ∀ b, Reachable B (some 1) (S a c) (S a ⟨c.left,b,c.right⟩)) (l x y r : Bool) (hxy : x≠y) (ha : Gates.legal kind ⟨l,x,r⟩) (hb : Gates.legal kind ⟨l,y,r⟩) :
    Reachable B (some 1) (S ⟨l,x,r⟩ ⟨l,x,r⟩)
      (S ⟨l,y,r⟩ ⟨l,y,r⟩) := by
  cases x <;> cases y
  · exact False.elim (hxy rfl)
  · have hg := hgate ⟨l,false,r⟩ ⟨l,true,r⟩ ha hb (by simp [Gates.singleChange])
    have hw := hwire ⟨l,false,r⟩ ⟨l,false,r⟩ rfl true
    apply hw.trans
    simpa [Gates.neighborSignals,Gates.changingPort] using hg
  · have hg := hgate ⟨l,true,r⟩ ⟨l,false,r⟩ ha hb (by simp [Gates.singleChange])
    have hw := hwire ⟨l,false,r⟩ ⟨l,true,r⟩ rfl false
    apply Relation.ReflTransGen.trans (b := S ⟨l,false,r⟩ ⟨l,true,r⟩) ?_ hw
    simpa [Gates.neighborSignals,Gates.changingPort] using hg
  · exact False.elim (hxy rfl)

/-- Propagate one canonical right change using only the actual core and that one lead. -/
theorem change_right (hgate : ∀ a b, Gates.legal kind a → Gates.legal kind b → Gates.singleChange a b →
      Reachable B (some 1) (S a (Gates.neighborSignals a b)) (S b (Gates.neighborSignals a b)))
    (hwire : ∀ a c, a.right=true → ∀ b, Reachable B (some 1) (S a c) (S a ⟨c.left,c.upper,b⟩)) (l u x y : Bool) (hxy : x≠y) (ha : Gates.legal kind ⟨l,u,x⟩) (hb : Gates.legal kind ⟨l,u,y⟩) :
    Reachable B (some 1) (S ⟨l,u,x⟩ ⟨l,u,x⟩)
      (S ⟨l,u,y⟩ ⟨l,u,y⟩) := by
  cases x <;> cases y
  · exact False.elim (hxy rfl)
  · have hg := hgate ⟨l,u,false⟩ ⟨l,u,true⟩ ha hb (by simp [Gates.singleChange])
    have hw := hwire ⟨l,u,true⟩ ⟨l,u,false⟩ rfl true
    apply Relation.ReflTransGen.trans (b := S ⟨l,u,true⟩ ⟨l,u,false⟩) ?_ hw
    simpa [Gates.neighborSignals,Gates.changingPort] using hg
  · have hg := hgate ⟨l,u,true⟩ ⟨l,u,false⟩ ha hb (by simp [Gates.singleChange])
    have hw := hwire ⟨l,u,true⟩ ⟨l,u,true⟩ rfl false
    apply hw.trans
    simpa [Gates.neighborSignals,Gates.changingPort] using hg
  · exact False.elim (hxy rfl)

end GatePropagation
end PushPuzzle.PushFS.Reduction
