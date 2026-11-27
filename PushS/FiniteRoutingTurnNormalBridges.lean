/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTurnNormalSlots
public import PushS.FiniteRoutingNeighborSlots

/-! Both normal phases of the real neighboring P/Q identities meet the turn's literal normal slots. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteTools

theorem JunctionContract.predecessor_normal (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) (q : Bool) :
    c.penultimateWorld w hw q = t.actionWorld w hw (Turn.normalCell w q .predecessor) := by
  rw [LineCode.penultimateWorld_eq w hw c H.incoming_good q,TurnCode.normal_world w hw t H.perpendicular q .predecessor]
  rw [H.incoming_direction,H.incoming_finish]
  have ht := segment_travels c.segment H.incoming_good.1
  have hl := H.incoming_good.2.1
  rw [H.incoming_direction,H.incoming_finish] at ht
  have hq := Bool.toNat_le q
  cases hd : t.incoming <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem JunctionContract.successor_normal (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) (q : Bool) :
    e.secondWorld w hw q = t.actionWorld w hw (Turn.normalCell w q .successor) := by
  rw [LineCode.secondWorld_eq w hw e H.outgoing_good q,TurnCode.normal_world w hw t H.perpendicular q .successor]
  rw [H.outgoing_direction,H.outgoing_start]
  have ht := segment_travels e.segment H.outgoing_good.1
  have hl := H.outgoing_good.2.1
  rw [H.outgoing_direction,H.outgoing_start] at ht
  have hq := Bool.toNat_le q
  cases hd : t.outgoing <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

end PushPuzzle.PushS.FiniteRouting
