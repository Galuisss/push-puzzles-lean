/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceFloor
public import PushS.FiniteRoutingMacroContacts
public import PushFS.Reduction.PhysicalGateForeignGeometry

/-! Source adjacency and the actual consuming endpoint gaps separate foreign normal boxes. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Plan
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem wire_neighbor_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (e f : ℕ) (a b : Catalog.Bitmap.Args)
    (hca : CellPlan.cell (v,p) = some (.inr (e,a))) (hcb : CellPlan.cell (v,r) = some (.inr (f,b)))
    (c d : PrimitiveCode) (hc : c ∈ wireCodes w a) (hd : d ∈ wireCodes w b)
    (goal : Bool) (l : c.Labels w) (s : d.Labels w)
    (hfa : InCollar w face (c.actor w hw goal l)) (hfb : InCollar w face.opposite (d.actor w hw goal s)) :
    macroShift w p (c.actor w hw goal l) ≠ macroShift w r (d.actor w hw goal s) := by
  have hu : CellPlan.Used (CellPlan.cell (v,p)) face := by
    rw [hca]
    rcases wire_actor_collar_bound w hw a c hc goal l face hfa with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hflow := (CellPlan.wire_adjacent v hP hT hn hca hcb hu).2
  rcases hflow with h | h
  · exact macro_port_owned_ne w face p r _ _ false hn
      (wire_output_actor_bound w hw a c hc goal l face hfa h.1.symm)
      (wire_input_actor_bound w hw b d hd goal s face.opposite hfb (by rw [h.2]))
  · exact macro_port_owned_ne w face p r _ _ true hn
      (wire_input_actor_bound w hw a c hc goal l face hfa (by rw [h.1,Direction.opposite_opposite]))
      (wire_output_actor_bound w hw b d hd goal s face.opposite hfb h.2.symm)

private theorem gate_wire_neighbor_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (vertex : VertexData) (g : GateTileState) (e : ℕ) (a : Catalog.Bitmap.Args)
    (hcg : CellPlan.cell (v,p) = some (.inl (vertex,g))) (hcw : CellPlan.cell (v,r) = some (.inr (e,a)))
    (c d : PrimitiveCode) (hc : c ∈ gateCodes w g) (hd : d ∈ wireCodes w a)
    (goal : Bool) (l : c.Labels w) (s : d.Labels w)
    (hfg : InCollar w face (c.actor w hw goal l)) (hfw : InCollar w face.opposite (d.actor w hw goal s)) :
    macroShift w p (c.actor w hw goal l) ≠ macroShift w r (d.actor w hw goal s) := by
  obtain ⟨role,hdir,hbound⟩ := gate_actor_collar_bound w hw g c hc goal l face hfg
  have hkeyg : PhysicalTiles.key (CellPlan.cell (v,p)) = some (.inl g) := by rw [hcg]; rfl
  have hkeyw : PhysicalTiles.key (CellPlan.cell (v,r)) = some (.inr a) := by rw [hcw]; rfl
  have hflow := PhysicalTiles.gate_neighbor_flow v hP hT hkeyg hkeyw role hdir hn
  apply macro_port_owned_ne w face p r _ _ (g.incoming.get role) hn hbound
  cases hb : g.incoming.get role
  · simp only [hb,Bool.false_eq_true,↓reduceIte] at hflow
    exact wire_input_actor_bound w hw a d hd goal s face.opposite hfw (by rw [hflow])
  · simp only [hb,↓reduceIte] at hflow
    exact wire_output_actor_bound w hw a d hd goal s face.opposite hfw hflow.symm

theorem neighboring_gates_impossible (v : CellPlan.Source) (p r : GridRouting.Point) (face : Direction)
    (hn : PushFS.Reduction.neighbor face p = some r) (a b : VertexData) (g h : GateTileState)
    (hca : CellPlan.cell (v,p) = some (.inl (a,g))) (hcb : CellPlan.cell (v,r) = some (.inl (b,h))) : False := by
  have hap := (Raster.vertexAt_sound (CellPlan.gate_sound hca).1).2
  have hbp := (Raster.vertexAt_sound (CellPlan.gate_sound hcb).1).2
  have ht := neighbor_travels hn
  have hx : p.1 ≤ r.1+1 ∧ r.1 ≤ p.1+1 := by cases face <;> dsimp [Travels] at ht <;> omega
  have hy : p.2 ≤ r.2+1 ∧ r.2 ≤ p.2+1 := by cases face <;> dsimp [Travels] at ht <;> omega
  have he := refinePoint_near_eq (a := a.point) (b := b.point)
    (by simpa only [hap,hbp] using hx) (by simpa only [hap,hbp] using hy)
  exact FiniteRouting.neighbor_ne hn (hap.symm.trans (he.trans hbp))

private theorem neighbors_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (c d : PrimitiveCode) (hc : c ∈ localCodes w (CellPlan.cell (v,p)))
    (hd : d ∈ localCodes w (CellPlan.cell (v,r))) (goal : Bool) (l : c.Labels w) (s : d.Labels w)
    (hfa : InCollar w face (c.actor w hw goal l)) (hfb : InCollar w face.opposite (d.actor w hw goal s)) :
    macroShift w p (c.actor w hw goal l) ≠ macroShift w r (d.actor w hw goal s) := by
  cases hca : CellPlan.cell (v,p) with
  | none => simp [hca,localCodes] at hc
  | some ca =>
    cases hcb : CellPlan.cell (v,r) with
    | none => simp [hcb,localCodes] at hd
    | some cb =>
      rw [hca] at hc
      rw [hcb] at hd
      rcases ca with ⟨a,g⟩ | ⟨e,k⟩ <;> rcases cb with ⟨b,h⟩ | ⟨f,z⟩
      · exact (neighboring_gates_impossible v p r face hn a b g h hca hcb).elim
      · exact gate_wire_neighbor_actor_ne w hw v hP hT p r face hn a g f z hca hcb c d hc hd goal l s hfa hfb
      · apply Ne.symm
        exact gate_wire_neighbor_actor_ne w hw v hP hT r p face.opposite (neighbor_reverse hn) b h e k hcb hca d c hd hc goal s l hfb
          (by simpa only [Direction.opposite_opposite] using hfa)
      · exact wire_neighbor_actor_ne w hw v hP hT p r face hn e f k z hca hcb c d hc hd goal l s hfa hfb

theorem foreign_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (q t : GridRouting.Point × PrimitiveCode) (hq : q ∈ codes w v) (ht : t ∈ codes w v)
    (hpos : q.1 ≠ t.1) (goal : Bool) (l : q.2.Labels w) (s : t.2.Labels w) :
    macroShift w q.1 (q.2.actor w hw goal l) ≠ macroShift w t.1 (t.2.actor w hw goal s) := by
  have hql := code_local w v q hq
  have htl := code_local w v t ht
  intro he
  obtain ⟨face,hn,hfa,hfb⟩ := macro_contact w q.1 t.1 _ _
    (local_actor_bounds w hw q.2 (localCodes_fits w hw _ hql) goal l)
    (local_actor_bounds w hw t.2 (localCodes_fits w hw _ htl) goal s)
    (local_actor_collar_lane w hw _ q.2 hql goal l) hpos he
  exact neighbors_actor_ne w hw v hP hT q.1 t.1 face hn q.2 t.2 hql htl goal l s hfa hfb he

end PushPuzzle.PushS.FiniteSourceInventory
