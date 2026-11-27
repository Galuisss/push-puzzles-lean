/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingConsumerLow
public import PushS.FiniteRoutingActorBounds

/-! The producer's last support lies just outside its own macrocell stock. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

theorem producer_cap_collar_face (w : ℕ) (face other : Direction)
    (hf : InCollar w other (Line.along w face (boundaryPoint w face) 2)) : other = face := by
  have hm0 : 2*padding w+2 < padding w+25*spacing w := by unfold padding spacing; omega
  have hm1 : padding w+25*spacing w+2 < tileStride w := by unfold padding tileStride spacing; omega
  have ht : 2*padding w+2 < tileStride w := by unfold padding tileStride spacing; omega
  cases face <;> cases other <;> first
    | rfl
    | (dsimp [InCollar,Line.along,boundaryPoint] at hf; omega)

theorem producer_cap_collar_lane (w : ℕ) (face other : Direction)
    (hf : InCollar w other (Line.along w face (boundaryPoint w face) 2)) :
    SameLane other (Line.along w other (boundaryPoint w other) 0)
      (Line.along w face (boundaryPoint w face) 2) := by
  rw [producer_cap_collar_face w face other hf]
  cases face <;> rfl

theorem producer_cap_ne_inner_actor (w : ℕ) (face : Direction) (a : ℕ × ℕ) (ha : ActorBounds w a) :
    Line.along w face (boundaryPoint w face) 2 ≠ a := by
  have hpad : 2 ≤ padding w := by unfold padding; omega
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  cases face <;> dsimp [Line.along,boundaryPoint] at hx hy <;> dsimp [ActorBounds] at ha <;> omega

theorem LinePort.producer_cap (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (hport : LinePort w c face false) :
    c.capWorld w hw false = Line.along w face (boundaryPoint w face) 2 := by
  rcases hport with ⟨hd,he,_,_⟩ | ⟨h,_⟩
  · rw [c.capWorld_eq w hw hc false]
    simp only [Bool.false_eq_true,↓reduceIte,hd,he,Bool.toNat_false,advance_zero]
  · cases h

end PushPuzzle.PushS.FiniteRouting
