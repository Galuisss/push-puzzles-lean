/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingProducerCap
public import PushS.FiniteSourcePrimitiveProfile
public import PushS.FiniteSourceLineConnectivity

/-! Actual prepared consuming neighbors leave the producer's final support empty in the whole inventory. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem producer_cap_empty (phase : Fin (codes w v).length → Bool) (face : Direction)
    (hport : LinePort w s.code face false)
    (hlow : ∀ i : Fin (codes w v).length,
      neighbor face ((codes w v).get s.index).1 = some ((codes w v).get i).1 →
      ConsumerLow (CellPlan.cell (v,((codes w v).get i).1)) face.opposite (phase i))
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = macroShift w ((codes w v).get s.index).1 (s.code.capWorld w hw false)) :
    q ∉ PrimitiveProfile.boxes w hw v phase := by
  have hcl := code_local w v _ s.code_mem
  have hecap := hport.producer_cap w hw s.code s.good face
  intro hm
  obtain ⟨⟨i,l⟩,_,he⟩ := Finset.mem_image.mp hm
  have hdl := code_local w v _ (List.get_mem (codes w v) i)
  have hcoord : coordinates (PrimitiveProfile.position w hw v phase ⟨i,l⟩) =
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw (phase i) l) := by
    cases hphase : phase i
    · simp only [PrimitiveProfile.position,hphase,Bool.false_eq_true,ite_false]
      exact placed_source_coordinates w hw v i l
    · simp only [PrimitiveProfile.position,hphase,ite_true]
      exact placed_target_coordinates w hw v i l
  have heq := (congrArg coordinates he).symm
  rw [hq,hcoord] at heq
  by_cases hpos : ((codes w v).get s.index).1 = ((codes w v).get i).1
  · have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    rw [hecap] at hx hy
    simp only [macroShift,hpos] at hx hy
    exact producer_cap_ne_inner_actor w face _
      (local_actor_inner_bounds w hw _ _ hdl (phase i) l) (Prod.ext (by omega) (by omega))
  · obtain ⟨other,hn,hfa,hfb⟩ := macro_contact w ((codes w v).get s.index).1 ((codes w v).get i).1
      (s.code.capWorld w hw false) (((codes w v).get i).2.actor w hw (phase i) l)
      (local_world_bounds w hw (.line s.code) (localCodes_fits w hw _ hcl) (s.code.capSlot w hw false))
      (local_actor_bounds w hw _ (localCodes_fits w hw _ hdl) (phase i) l)
      (by intro other hf; rw [hecap] at hf ⊢; exact producer_cap_collar_lane w face other hf) hpos heq
    have ho : other = face := producer_cap_collar_face w face other (hecap ▸ hfa)
    subst other
    have hb := consumerLow_actor_bound w hw _ face.opposite (phase i) (hlow i hn) _ hdl l hfb
    exact hport.terminal_ne w hw s.code s.good _ _ _ face hn hb heq

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
