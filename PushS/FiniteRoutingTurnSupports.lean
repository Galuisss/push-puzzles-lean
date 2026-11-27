/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnCenters

/-! Four literal floor cells support both normal slots of each actual turn box. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Turn

open PushFS

attribute [local irreducible] FiniteTools.side

def support (w : ℕ) (role : Fin 2) (i : Fin 4) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  if role = 0 then
    (⟨FiniteTools.radius w-3+i.val,by unfold FiniteTools.side FiniteTools.radius; have h := i.isLt; omega⟩,
     ⟨FiniteTools.radius w,by unfold FiniteTools.side; omega⟩)
  else
    (⟨FiniteTools.radius w,by unfold FiniteTools.side; omega⟩,
     ⟨FiniteTools.radius w+i.val,by unfold FiniteTools.side FiniteTools.radius; have h := i.isLt; omega⟩)

theorem support_adjacent (w : ℕ) (role : Fin 2) (i : Fin 3) :
    Adjacent (if role = 0 then .east else .south) (support w role i.castSucc) (support w role i.succ) := by
  fin_cases role <;> dsimp [support,Adjacent] <;> constructor <;> rfl

def supportIndex (phase : Bool) : Fin 4 := ⟨phase.toNat+1,by have h := Bool.toNat_le phase; omega⟩

theorem support_slot (w : ℕ) (phase : Bool) (role : Fin 2) :
    support w role (supportIndex phase) = cell w phase role := by
  fin_cases role <;> cases phase <;> apply Prod.ext <;> apply Fin.ext <;>
    dsimp [support,supportIndex,cell,label,FiniteTools.turnMixedCell,FiniteTools.turnMixedPoint] <;>
    unfold FiniteTools.radius <;> omega

end PushPuzzle.PushS.FiniteRouting.Turn

namespace PushPuzzle.PushS.FiniteRouting.TurnCode

open PushFS PushFS.Reduction

attribute [local irreducible] FiniteTools.side

def supportSlot (w : ℕ) (c : TurnCode) (role : Fin 2) (i : Fin 4) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (Turn.orientation w c.incoming c.outgoing).cells (Turn.support w role i)

def supportWorld (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (role : Fin 2) (i : Fin 4) : ℕ × ℕ :=
  (PrimitiveCode.turn c).world w hw (c.supportSlot w role i)

theorem supportWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (hc : Perpendicular c.incoming c.outgoing)
    (role : Fin 2) (i : Fin 4) :
    c.supportWorld w hw role i = Line.along w (if role = 0 then c.incoming.opposite else c.outgoing)
      c.corner (if role = 0 then 3-i.val else i.val) := by
  have hr := Turn.orientation_coordinates w c.incoming c.outgoing (Turn.support w role i)
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only [coordinates] at hx hy
  change (Turn.offsetX w c.corner+((Turn.orientation w c.incoming c.outgoing).cells (Turn.support w role i)).1.val,
    Turn.offsetY w c.corner+((Turn.orientation w c.incoming c.outgoing).cells (Turn.support w role i)).2.val) = _
  rw [hx,hy]
  have hi := i.isLt
  fin_cases role <;> cases hd : c.incoming <;> cases he : c.outgoing <;>
    simp [hd,he,Perpendicular,rightTurn,Direction.opposite] at hc <;>
    dsimp [Turn.support,Turn.quarterCoordinates,coordinates,rightTurn,Turn.offsetX,Turn.offsetY,Line.along,Direction.opposite] <;>
    apply Prod.ext <;> simp only [FiniteTools.side,FiniteTools.radius,padding] <;> omega

end PushPuzzle.PushS.FiniteRouting.TurnCode
