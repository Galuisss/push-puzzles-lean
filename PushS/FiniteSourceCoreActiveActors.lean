/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCoreActiveActors
public import PushS.FiniteSourceCoreActiveFloor
public import PushS.FiniteSourceGateForward

/-! Real prepared arm stock clears every selected-core active cell in the complete source board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateActiveRegion
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

/-- The complete current global identity occupies its actual source or target actor coordinates. -/
private theorem current_actor_coordinates (phase : Fin (codes w v).length → Bool) (l : (inventory w hw v).PhysicalLabel) :
    coordinates (PrimitiveProfile.position w hw v phase l) =
      macroShift w ((codes w v).get l.1).1 (((codes w v).get l.1).2.actor w hw (phase l.1) l.2) := by
  rcases l with ⟨i,l⟩
  cases h : phase i
  · simpa only [PrimitiveProfile.position,h,Bool.false_eq_true,ite_false] using placed_source_coordinates w hw v i l
  · simpa only [PrimitiveProfile.position,h,ite_true] using placed_target_coordinates w hw v i l

namespace CoreSite

variable (c : CoreSite w hw v)

/-- Every real instruction at this core's source-grid coordinate belongs to its actual gate-code table. -/
private theorem local_code_mem (i : Fin (codes w v).length) (hi : ((codes w v).get i).1 = ((codes w v).get c.index).1) :
    ((codes w v).get i).2 ∈ gateCodes w c.gate := by
  have hs := code_local w v (_,PrimitiveCode.core c.gate) c.mem_codes
  have ht := code_local w v ((codes w v).get i) (List.get_mem _ _)
  rw [hi] at ht
  cases he : CellPlan.cell (v,((codes w v).get c.index).1) with
  | none => simp only [he,localCodes,Option.elim_none,List.not_mem_nil] at hs
  | some tile =>
    cases tile with
    | inl g =>
      rw [he] at hs ht
      have hh := gate_core_origin w c.gate g.2 hs
      simpa only [hh,localCodes,Option.elim_some,Sum.elim_inl] using ht
    | inr a =>
      rw [he] at hs
      exact ((wireSpec w a.2).core_not_mem c.gate hs).elim

/-- Every selected arm instruction is physically high when the selected actual core macro executes. -/
private theorem selected_arm_high (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate role).target = !(armSpec w c.gate role).initial)
    (i : Fin (codes w v).length) (hi : ((codes w v).get i).1 = p.location)
    (hc : ((codes w v).get i).2 ∈ (armSpec w c.gate role).codes) :
    (if c.corePhase role p (tilePhases phase) i then (armSpec w c.gate role).target else (armSpec w c.gate role).initial) = true := by
  cases hp : (armSpec w c.gate role).initial
  · have ht : (armSpec w c.gate role).target = true := by simpa only [hp,Bool.not_false] using hb
    obtain ⟨a,hai⟩ := p.owner_covers ha i hi hc
    have hflag : p.wave (tilePhases phase) (PathSite.waveLength (P := armSpec w c.gate role)) i = true := by
      rw [p.wave_final]
      exact ite_eq_left ⟨a,hai⟩
    simp only [corePhase,hp,Bool.false_eq_true,ite_false,hflag,ite_true,ht]
  · have hflag : tilePhases phase i = false := by unfold tilePhases; rw [hi]; exact fresh
    simp only [corePhase,hp,ite_true,hflag,Bool.false_eq_true,ite_false]

/-- The exact actual stock outside the emitted core owner. -/
@[expose] noncomputable def remaining (phase : Fin (codes w v).length → Bool) : Finset (Cell (width w v) (height w v)) :=
  PrimitiveProfile.outside w hw v phase ((inventory w hw v).pieceLabels c.index)

private theorem foreign_actor_ne (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
    (i : Fin (codes w v).length) (hpos : ((codes w v).get i).1 ≠ ((codes w v).get c.index).1)
    (goal : Bool) (l : ((codes w v).get i).2.Labels w) :
    macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw goal l) ≠
      macroShift w ((codes w v).get c.index).1 (coreWorld w a) := by
  intro he
  have hc := code_local w v ((codes w v).get i) (List.get_mem _ _)
  have hsrc := code_local w v (_,PrimitiveCode.core c.gate) c.mem_codes
  have hbounds := local_world_bounds w hw (.core c.gate) (localCodes_fits w hw _ hsrc) (coreCell w hw c.gate a)
  rw [coreCell_world] at hbounds
  have hinterior := core_window_interior w hw c.gate (coreCell w hw c.gate a)
  rw [coreCell_world] at hinterior
  have hcollar : ∀ face,InCollar w face (coreWorld w a) →
      SameLane face (Line.along w face (boundaryPoint w face) 0) (coreWorld w a) := by
    intro face hf
    exact ((interior_not_collar w face hinterior) hf).elim
  obtain ⟨face,_,hf,_⟩ := macro_contact w _ _ _ _ hbounds
    (local_actor_bounds w hw _ (localCodes_fits w hw _ hc) _ l) hcollar (Ne.symm hpos) he.symm
  exact (interior_not_collar w face hinterior) hf

/-- Every real foreign identity avoids the selected-core region at the exact core execution phase. -/
theorem remaining_avoids_region (selected : Fin 3) (p : PathSite w hw v (armSpec w c.gate selected))
    (hloc : p.location = ((codes w v).get c.index).1) (ha : (inventory w hw v).Admissible)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (a : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hregion : Region w c.gate.core.isAND selected a) :
    c.embedding.cells a ∉ c.remaining (c.corePhase selected p (tilePhases phase)) := by
  intro hm
  obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hm
  have howner : l.1 ≠ c.index := by
    intro hi
    exact (Finset.mem_sdiff.mp hl).2 ((inventory w hw v).mem_pieceLabels c.index l |>.mpr hi)
  have hh := congrArg coordinates he
  rw [current_actor_coordinates,c.embedding_coordinates] at hh
  by_cases hpos : ((codes w v).get l.1).1 = ((codes w v).get c.index).1
  · rw [hpos] at hh
    have hlocal := c.local_code_mem l.1 hpos
    rw [gateCodes_eq_specs] at hlocal
    rcases List.mem_cons.mp hlocal with hcore | hlocal
    · apply howner
      apply code_get_injective ha
      exact Prod.ext hpos (hcore.trans c.code_eq.symm)
    · obtain ⟨role,_,hr⟩ := List.mem_flatMap.mp hlocal
      apply core_arm_actor_clear w hw c.gate selected a hregion role _ hr _ l.2 ?_
        ((macroShift_injective w _) hh).symm
      intro hrole
      subst role
      exact c.selected_arm_high selected p ha phase fresh hb l.1 (hpos.trans hloc.symm) hr
  · exact c.foreign_actor_ne a l.1 hpos _ l.2 hh

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
