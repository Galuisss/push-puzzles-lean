/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTurnNormalSlots
public import PushS.FiniteSourceTurnOpenStock
public import PushS.FiniteSourceActionStock

/-! The actual four selected turn identities reserve its complete action footprint. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteTools
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height FiniteTools.side FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

namespace TurnStep

variable (s : TurnStep w hw v P)

private theorem normal_pair_outside_avoids (hb : P.target = !P.initial)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (l : TurnLabel) (q : Bool) :
    s.site.actualEmbedding.cells (Turn.normalCell w q l) ∉
      PrimitiveProfile.outside w hw v phase (Finset.univ.map s.labels) := by
  have hlocal := Turn.normal_adjacent w l
  have hstep : ∃ d, Adjacent d ((inventory w hw v).source (s.labels l)) ((inventory w hw v).target (s.labels l)) := by
    rw [s.normal_slot_source,s.normal_slot_target,hb]
    cases hi : P.initial
    · exact ⟨s.site.actualEmbedding.direction _,s.site.actualEmbedding.adjacent _ _ _ hlocal⟩
    · exact ⟨s.site.actualEmbedding.direction _,s.site.actualEmbedding.adjacent _ _ _ hlocal.reverse⟩
  obtain ⟨d,hd⟩ := hstep
  apply PrimitiveProfile.endpoint_pair_avoids (admissible w hw v hP hT) hP hT phase _ (s.labels l)
    (Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩) d hd
  have hphase : q = P.initial ∨ q = P.target := by rw [hb]; cases q <;> cases P.initial <;> decide
  rcases hphase with hq | hq
  · left
    rw [s.normal_slot_source,hq]
  · right
    rw [s.normal_slot_target,hq]

private theorem fixed_avoids (hb : P.target = !P.initial)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ turnActive w) :
    s.site.actualEmbedding.cells p ∉ PrimitiveProfile.outside w hw v phase (Finset.univ.map s.labels) := by
  rcases Turn.active_cases w p hp with ⟨l,q,hp⟩ | hgap
  · rw [hp]
    exact s.normal_pair_outside_avoids hb hP hT phase l q
  · exact fun h => s.site.open_gap_empty phase p hp hgap (PrimitiveProfile.outside_subset_boxes phase _ h)

end TurnStep

namespace PathSite

variable (s : PathSite w hw v P) (G : P.Geometry w)

theorem turn_fixed_avoids (hb : P.target = !P.initial)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val) :
    ∀ p ∈ turnActive w, (s.turn G i hi).actualEmbedding.cells p ∉
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (TurnStep.mk s G i hi).labels) :=
  (TurnStep.mk s G i hi).fixed_avoids hb hP hT phase

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
