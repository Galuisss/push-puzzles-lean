/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMeshBands
public import PushS.FiniteRoutingMacroContacts

/-! Bounded transverse port bands rule out diagonal macrocell contact. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

/-- Equality after macrocell placement is exactly equality of its two translated coordinates. -/
theorem macroShift_eq_iff (w : ℕ) (p r a b : ℕ × ℕ) :
    macroShift w p a = macroShift w r b ↔
      tileStride w*p.1+a.1 = tileStride w*r.1+b.1 ∧ tileStride w*p.2+a.2 = tileStride w*r.2+b.2 := by
  simp only [macroShift,Prod.mk.injEq]

private theorem column_contact (w : ℕ) (p r a b : ℕ × ℕ)
    (ha : a.2 < tileSide w) (hb : b.2 < tileSide w) (hpx : p.1 = r.1)
    (hne : p ≠ r) (hy : tileStride w*p.2+a.2 = tileStride w*r.2+b.2) :
    ∃ d, neighbor d p = some r ∧ InCollar w d a ∧ InCollar w d.opposite b := by
  have hpy : p.2 ≠ r.2 := fun h => hne (Prod.ext hpx h)
  rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha hb hy hpy with h | h
  · exact ⟨.south,travels_neighbor (show Travels .south p r 1 from ⟨hpx,h.1⟩),h.2⟩
  · exact ⟨.north,travels_neighbor (show Travels .north p r 1 from ⟨hpx,h.1⟩),h.2⟩

theorem macro_band_contact (w margin : ℕ) (hm : margin ≤ padding w) (p r a b : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w) (hb : b.1 < tileSide w ∧ b.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w margin face a)
    (hne : p ≠ r) (he : macroShift w p a = macroShift w r b) :
    ∃ d, neighbor d p = some r ∧ InCollar w d a ∧ InCollar w d.opposite b := by
  obtain ⟨hx,hy⟩ := (macroShift_eq_iff w p r a b).mp he
  by_cases hpx : p.1 = r.1
  · exact column_contact w p r a b ha.2 hb.2 hpx hne hy
  · rcases macro_axis_collar w p.1 r.1 a.1 b.1 ha.1 hb.1 hx hpx with h | h
    · have hla := hband .east h.2.1
      dsimp [PortBand] at hla
      have hpy : p.2 = r.2 := by
        by_contra hpy
        rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
      exact ⟨.east,travels_neighbor (show Travels .east p r 1 from ⟨hpy,h.1⟩),h.2⟩
    · have hla := hband .west h.2.1
      dsimp [PortBand] at hla
      have hpy : p.2 = r.2 := by
        by_contra hpy
        rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
      exact ⟨.west,travels_neighbor (show Travels .west p r 1 from ⟨hpy,h.1⟩),h.2⟩

end PushPuzzle.PushS.FiniteRouting
