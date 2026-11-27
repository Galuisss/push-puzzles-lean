/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnActionCoordinates

/-! The four real normal slot pairs bounding the turn's open action quadrant. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteTools

namespace Turn

/-- Normal coordinates of the incoming P/F and outgoing G/Q turn stock. -/
@[expose]
def normalPoint (w : ℕ) (q : Bool) : TurnLabel → ℕ × ℕ
  | .predecessor => (FiniteTools.radius w-4+q.toNat,FiniteTools.radius w)
  | .horizontal => (FiniteTools.radius w-2+q.toNat,FiniteTools.radius w)
  | .vertical => (FiniteTools.radius w,FiniteTools.radius w+1+q.toNat)
  | .successor => (FiniteTools.radius w,FiniteTools.radius w+3+q.toNat)

/-- A literal normal slot of one of the four actual turn identities. -/
@[expose]
def normalCell (w : ℕ) (q : Bool) (l : TurnLabel) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (⟨(normalPoint w q l).1,by have hq := Bool.toNat_le q; cases l <;> dsimp [normalPoint,FiniteTools.side,FiniteTools.radius] <;> omega⟩,
   ⟨(normalPoint w q l).2,by have hq := Bool.toNat_le q; cases l <;> dsimp [normalPoint,FiniteTools.side,FiniteTools.radius] <;> omega⟩)

/-- The open turn quadrant together with its empty corner center. -/
@[expose]
def OpenGap (w : ℕ) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) : Prop :=
  (p.1.val < FiniteTools.radius w ∧ FiniteTools.radius w < p.2.val) ∨ (p.1.val = FiniteTools.radius w ∧ p.2.val = FiniteTools.radius w)

theorem normal_adjacent (w : ℕ) (l : TurnLabel) :
    Adjacent (if l = .predecessor ∨ l = .horizontal then .east else .south)
      (normalCell w false l) (normalCell w true l) := by
  cases l <;> simp [Adjacent,normalCell,normalPoint]

private theorem normal_cell_ext (w : ℕ) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (l : TurnLabel) (q : Bool)
    (hx : p.1.val = (normalPoint w q l).1) (hy : p.2.val = (normalPoint w q l).2) : p = normalCell w q l :=
  Prod.ext (Fin.ext hx) (Fin.ext hy)

theorem active_cases (w : ℕ) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ turnActive w) :
    (∃ l q, p = normalCell w q l) ∨ OpenGap w p := by
  have hb := (FiniteGeometry.Rectangle.mem_cells _ _ _ _).mp hp
  change FiniteTools.radius w-4 ≤ p.1.val ∧ p.1.val < FiniteTools.radius w-4+5 ∧ FiniteTools.radius w ≤ p.2.val ∧ p.2.val < FiniteTools.radius w+5 at hb
  by_cases hy : p.2.val = FiniteTools.radius w
  · by_cases hpre : p.1.val ≤ FiniteTools.radius w-3
    · left
      by_cases hx : p.1.val = FiniteTools.radius w-4
      · exact ⟨.predecessor,false,normal_cell_ext w p .predecessor false (by simpa [normalPoint]) hy⟩
      · refine ⟨.predecessor,true,normal_cell_ext w p .predecessor true ?_ hy⟩
        dsimp [normalPoint]
        unfold FiniteTools.radius at *
        omega
    · by_cases hhor : p.1.val < FiniteTools.radius w
      · left
        by_cases hx : p.1.val = FiniteTools.radius w-2
        · exact ⟨.horizontal,false,normal_cell_ext w p .horizontal false (by simpa [normalPoint]) hy⟩
        · refine ⟨.horizontal,true,normal_cell_ext w p .horizontal true ?_ hy⟩
          dsimp [normalPoint]
          unfold FiniteTools.radius at *
          omega
      · right
        exact Or.inr ⟨by unfold FiniteTools.radius at *; omega,hy⟩
  · by_cases hx : p.1.val < FiniteTools.radius w
    · exact Or.inr (Or.inl ⟨hx,by omega⟩)
    · have hx' : p.1.val = FiniteTools.radius w := by unfold FiniteTools.radius at *; omega
      left
      by_cases hlow : p.2.val ≤ FiniteTools.radius w+2
      · by_cases h1 : p.2.val = FiniteTools.radius w+1
        · exact ⟨.vertical,false,normal_cell_ext w p .vertical false hx' (by simpa [normalPoint])⟩
        · refine ⟨.vertical,true,normal_cell_ext w p .vertical true hx' ?_⟩
          dsimp [normalPoint]
          omega
      · by_cases h3 : p.2.val = FiniteTools.radius w+3
        · exact ⟨.successor,false,normal_cell_ext w p .successor false hx' (by simpa [normalPoint])⟩
        · refine ⟨.successor,true,normal_cell_ext w p .successor true hx' ?_⟩
          dsimp [normalPoint]
          omega

end Turn

theorem TurnCode.normal_world (w : ℕ) (hw : 2 ≤ w) (t : TurnCode) (ht : Perpendicular t.incoming t.outgoing)
    (q : Bool) (l : TurnLabel) : t.actionWorld w hw (Turn.normalCell w q l) =
      match l with
      | .predecessor => Line.along w t.incoming.opposite t.corner (4-q.toNat)
      | .horizontal => Line.along w t.incoming.opposite t.corner (2-q.toNat)
      | .vertical => Line.along w t.outgoing t.corner (1+q.toNat)
      | .successor => Line.along w t.outgoing t.corner (3+q.toNat) := by
  rw [t.actionWorld_eq w hw]
  cases di : t.incoming <;> cases do' : t.outgoing <;>
    simp [di,do',Perpendicular,rightTurn,Direction.opposite] at ht ⊢ <;>
    cases q <;> cases l <;>
    dsimp [Turn.quarterCoordinates,Turn.normalCell,Turn.normalPoint,coordinates,Turn.offsetX,Turn.offsetY,Line.along,Direction.opposite] <;>
    apply Prod.ext <;> simp only [FiniteTools.side,FiniteTools.radius,padding] <;> omega

end PushPuzzle.PushS.FiniteRouting
