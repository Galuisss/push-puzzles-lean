/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActorBounds
public import PushS.FiniteRoutingMacroContacts
public import PushS.FiniteRoutingSpacing

/-! Adjacent normal actors in distinct source macrocells must lie on reciprocal boundary ports. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

private theorem macro_axis_near_close (w x y a b : ℕ)
    (ha : padding w ≤ a+1) (hb : b ≤ tileStride w+padding w+1)
    (he : tileStride w*x+a ≤ tileStride w*y+b+1) : x ≤ y+1 := by
  by_contra hn
  have hh : y+2 ≤ x := by omega
  have hm := Nat.mul_le_mul_left (tileStride w) hh
  simp only [Nat.mul_add,Nat.mul_two] at hm
  have hs : 3 < tileStride w := by unfold tileStride spacing; omega
  omega

private theorem macro_axis_near_collar (w x y a b : ℕ)
    (ha : padding w ≤ a+1 ∧ a ≤ tileStride w+padding w+1)
    (hb : padding w ≤ b+1 ∧ b ≤ tileStride w+padding w+1)
    (he : tileStride w*x+a ≤ tileStride w*y+b+1 ∧ tileStride w*y+b ≤ tileStride w*x+a+1)
    (hne : x ≠ y) :
    (y = x+1 ∧ tileStride w ≤ a ∧ b ≤ 2*padding w) ∨
      (x = y+1 ∧ a ≤ 2*padding w ∧ tileStride w ≤ b) := by
  have hxy := macro_axis_near_close w x y a b ha.1 hb.2 he.1
  have hyx := macro_axis_near_close w y x b a hb.1 ha.2 he.2
  have hp : 3 ≤ padding w := by unfold padding; omega
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : y = x+1 := by omega
    rw [hs,Nat.mul_add,Nat.mul_one] at he
    exact Or.inl ⟨hs,by omega,by omega⟩
  · have hs : x = y+1 := by omega
    rw [hs,Nat.mul_add,Nat.mul_one] at he
    exact Or.inr ⟨hs,by omega,by omega⟩

theorem macro_near_contact (w : ℕ) (p r a b : ℕ × ℕ)
    (ha : ActorBounds w a) (hb : ActorBounds w b)
    (hactor : ∀ face, InCollar w face a → SameLane face (Line.along w face (boundaryPoint w face) 0) a)
    (hne : p ≠ r) (he : Nearby 1 (macroShift w p a) (macroShift w r b)) :
    ∃ d, neighbor d p = some r ∧ InCollar w d a ∧ InCollar w d.opposite b := by
  change padding w ≤ a.1+1 ∧ a.1 ≤ tileStride w+padding w+1 ∧
    padding w ≤ a.2+1 ∧ a.2 ≤ tileStride w+padding w+1 at ha
  change padding w ≤ b.1+1 ∧ b.1 ≤ tileStride w+padding w+1 ∧
    padding w ≤ b.2+1 ∧ b.2 ≤ tileStride w+padding w+1 at hb
  change tileStride w*p.1+a.1 ≤ tileStride w*r.1+b.1+1 ∧
    tileStride w*r.1+b.1 ≤ tileStride w*p.1+a.1+1 ∧
    tileStride w*p.2+a.2 ≤ tileStride w*r.2+b.2+1 ∧
    tileStride w*r.2+b.2 ≤ tileStride w*p.2+a.2+1 at he
  by_cases hpx : p.1 = r.1
  · have hpy : p.2 ≠ r.2 := fun h => hne (Prod.ext hpx h)
    rcases macro_axis_near_collar w p.2 r.2 a.2 b.2 ha.2.2 hb.2.2 he.2.2 hpy with h | h
    · exact ⟨.south,travels_neighbor (show Travels .south p r 1 from ⟨hpx,h.1⟩),h.2⟩
    · exact ⟨.north,travels_neighbor (show Travels .north p r 1 from ⟨hpx,h.1⟩),h.2⟩
  · rcases macro_axis_near_collar w p.1 r.1 a.1 b.1 ⟨ha.1,ha.2.1⟩ ⟨hb.1,hb.2.1⟩ ⟨he.1,he.2.1⟩ hpx with h | h
    · have hla := hactor .east h.2.1
      dsimp [SameLane,Line.along,boundaryPoint] at hla
      have hpy : p.2 = r.2 := by
        by_contra hpy
        rcases macro_axis_near_collar w p.2 r.2 a.2 b.2 ha.2.2 hb.2.2 he.2.2 hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
      exact ⟨.east,travels_neighbor (show Travels .east p r 1 from ⟨hpy,h.1⟩),h.2⟩
    · have hla := hactor .west h.2.1
      dsimp [SameLane,Line.along,boundaryPoint] at hla
      have hpy : p.2 = r.2 := by
        by_contra hpy
        rcases macro_axis_near_collar w p.2 r.2 a.2 b.2 ha.2.2 hb.2.2 he.2.2 hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
      exact ⟨.west,travels_neighbor (show Travels .west p r 1 from ⟨hpy,h.1⟩),h.2⟩

end PushPuzzle.PushS.FiniteRouting
