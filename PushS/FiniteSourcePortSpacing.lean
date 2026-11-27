/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePortPhases
public import PushS.FiniteRoutingNearContacts

/-! Actual normal source actors across distinct source tiles leave a full empty cell. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires Plan
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem wire_neighbor_actor_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (e f : ℕ) (a b : Catalog.Bitmap.Args)
    (hca : CellPlan.cell (v,p) = some (.inr (e,a))) (hcb : CellPlan.cell (v,r) = some (.inr (f,b)))
    (c t : PrimitiveCode) (hc : c ∈ wireCodes w a) (ht : t ∈ wireCodes w b)
    (goal : Bool) (l : c.Labels w) (s : t.Labels w)
    (hfa : InCollar w face (c.actor w hw goal l)) (hfb : InCollar w face.opposite (t.actor w hw goal s)) :
    ¬Nearby 1 (macroShift w p (c.actor w hw goal l)) (macroShift w r (t.actor w hw goal s)) := by
  have hu : CellPlan.Used (CellPlan.cell (v,p)) face := by
    rw [hca]
    rcases wire_actor_collar_bound w hw a c hc goal l face hfa with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hphase := wire_neighbor_phase v hP hT p r face hn e f a b hca hcb hu goal
  rcases (CellPlan.wire_adjacent v hP hT hn hca hcb hu).2 with h | h
  · have ha := wire_output_phase_bound w hw a c hc goal l face hfa h.1.symm
    have hb := wire_input_phase_bound w hw b t ht goal s face.opposite hfb (by rw [h.2])
    change PortPhaseBound w face.opposite true (!(PhysicalTiles.wirePhase b goal)) (t.actor w hw goal s) at hb
    rw [←hphase] at hb
    exact macro_port_phase_sparse w face p r _ _ false (PhysicalTiles.wirePhase a goal) hn ha hb
  · have ha := wire_input_phase_bound w hw a c hc goal l face hfa (by rw [h.1,Direction.opposite_opposite])
    have hb := wire_output_phase_bound w hw b t ht goal s face.opposite hfb h.2.symm
    change PortPhaseBound w face.opposite false (PhysicalTiles.wirePhase b goal) (t.actor w hw goal s) at hb
    rw [←hphase] at hb
    apply macro_port_phase_sparse w face p r _ _ true (!(PhysicalTiles.wirePhase a goal)) hn ha
    simpa only [Bool.not_true,Bool.not_not] using hb

private theorem gate_wire_neighbor_actor_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (vertex : VertexData) (g : GateTileState) (e : ℕ) (a : Catalog.Bitmap.Args)
    (hcg : CellPlan.cell (v,p) = some (.inl (vertex,g))) (hcw : CellPlan.cell (v,r) = some (.inr (e,a)))
    (c t : PrimitiveCode) (hc : c ∈ gateCodes w g) (ht : t ∈ wireCodes w a)
    (goal : Bool) (l : c.Labels w) (s : t.Labels w)
    (hfg : InCollar w face (c.actor w hw goal l)) (hfw : InCollar w face.opposite (t.actor w hw goal s)) :
    ¬Nearby 1 (macroShift w p (c.actor w hw goal l)) (macroShift w r (t.actor w hw goal s)) := by
  obtain ⟨role,hd,hbound⟩ := gate_actor_phase_bound w hw g c hc goal l face hfg
  have hkeyg : PhysicalTiles.key (CellPlan.cell (v,p)) = some (.inl g) := by rw [hcg]; rfl
  have hkeyw : PhysicalTiles.key (CellPlan.cell (v,r)) = some (.inr a) := by rw [hcw]; rfl
  have hflow := PhysicalTiles.gate_neighbor_flow v hP hT hkeyg hkeyw role hd hn
  have hphase := gate_wire_port_phase v hP hT p r face hn vertex g e a hcg hcw role hd goal
  rw [hphase] at hbound
  cases hi : g.incoming.get role
  · simp only [hi,Bool.false_eq_true,↓reduceIte] at hflow hbound
    exact macro_port_phase_sparse w face p r _ _ false (PhysicalTiles.wirePhase a goal) hn hbound
      (wire_input_phase_bound w hw a t ht goal s face.opposite hfw (by rw [hflow]))
  · simp only [hi,↓reduceIte] at hflow hbound
    have hb := wire_output_phase_bound w hw a t ht goal s face.opposite hfw hflow.symm
    apply macro_port_phase_sparse w face p r _ _ true (!(PhysicalTiles.wirePhase a goal)) hn hbound
    simpa only [Bool.not_true,Bool.not_not,PhysicalTiles.wirePhase] using hb

private theorem neighbors_actor_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (c t : PrimitiveCode) (hc : c ∈ localCodes w (CellPlan.cell (v,p)))
    (ht : t ∈ localCodes w (CellPlan.cell (v,r))) (goal : Bool) (l : c.Labels w) (s : t.Labels w)
    (hfa : InCollar w face (c.actor w hw goal l)) (hfb : InCollar w face.opposite (t.actor w hw goal s)) :
    ¬Nearby 1 (macroShift w p (c.actor w hw goal l)) (macroShift w r (t.actor w hw goal s)) := by
  cases hca : CellPlan.cell (v,p) with
  | none => simp [hca,localCodes] at hc
  | some ca =>
    cases hcb : CellPlan.cell (v,r) with
    | none => simp [hcb,localCodes] at ht
    | some cb =>
      rw [hca] at hc
      rw [hcb] at ht
      rcases ca with ⟨a,g⟩ | ⟨e,k⟩ <;> rcases cb with ⟨b,h⟩ | ⟨f,z⟩
      · exact (neighboring_gates_impossible v p r face hn a b g h hca hcb).elim
      · exact gate_wire_neighbor_actor_sparse w hw v hP hT p r face hn a g f z hca hcb c t hc ht goal l s hfa hfb
      · intro hadj
        apply gate_wire_neighbor_actor_sparse w hw v hP hT r p face.opposite (neighbor_reverse hn) b h e k hcb hca
          t c ht hc goal s l hfb (by simpa only [Direction.opposite_opposite] using hfa)
        unfold Nearby at *
        omega
      · exact wire_neighbor_actor_sparse w hw v hP hT p r face hn e f k z hca hcb c t hc ht goal l s hfa hfb

theorem foreign_actor_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (q t : GridRouting.Point × PrimitiveCode) (hq : q ∈ codes w v) (ht : t ∈ codes w v)
    (hpos : q.1 ≠ t.1) (goal : Bool) (l : q.2.Labels w) (s : t.2.Labels w) :
    ¬Nearby 1 (macroShift w q.1 (q.2.actor w hw goal l)) (macroShift w t.1 (t.2.actor w hw goal s)) := by
  have hql := code_local w v q hq
  have htl := code_local w v t ht
  intro he
  obtain ⟨face,hn,hfa,hfb⟩ := macro_near_contact w q.1 t.1 _ _
    (local_actor_inner_bounds w hw _ q.2 hql goal l)
    (local_actor_inner_bounds w hw _ t.2 htl goal s)
    (local_actor_collar_lane w hw _ q.2 hql goal l) hpos he
  exact neighbors_actor_sparse w hw v hP hT q.1 t.1 face hn q.2 t.2 hql htl goal l s hfa hfb he

end PushPuzzle.PushS.FiniteSourceInventory
