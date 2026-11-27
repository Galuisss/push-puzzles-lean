/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceSeparation
public import PushS.FiniteRoutingPortBounds

/-! Actual source adjacency matches the canonical incoming flags of the finite-force ports. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires Plan
open Cslib.Complexity.NCL

theorem local_port_used (v : CellPlan.Source) (p : GridRouting.Point) (face : Direction) (incoming : Bool)
    (hp : LocalPort (CellPlan.cell (v,p)) face incoming) : CellPlan.Used (CellPlan.cell (v,p)) face := by
  cases hc : CellPlan.cell (v,p) with
  | none => simp [hc,LocalPort] at hp
  | some c =>
    rw [hc] at hp
    rcases c with ⟨vertex,g⟩ | ⟨e,q⟩
    · have hk : PhysicalTiles.key (CellPlan.cell (v,p)) = some (.inl g) := by rw [hc]; rfl
      obtain ⟨role,hd,_⟩ := hp
      have hu : PhysicalTiles.Used (.inl g) face := ⟨role,hd⟩
      simpa only [hc] using (PhysicalTiles.used_key hk face).mp hu
    · rcases hp with ⟨_,hd⟩ | ⟨_,hd⟩
      · exact Or.inl hd
      · exact Or.inr hd

theorem local_port_of_used (v : CellPlan.Source) (p : GridRouting.Point) (face : Direction)
    (hu : CellPlan.Used (CellPlan.cell (v,p)) face) : ∃ incoming, LocalPort (CellPlan.cell (v,p)) face incoming := by
  cases hc : CellPlan.cell (v,p) with
  | none => simp [hc,CellPlan.Used] at hu
  | some c =>
    rcases c with ⟨vertex,g⟩ | ⟨e,q⟩
    · have hk : PhysicalTiles.key (CellPlan.cell (v,p)) = some (.inl g) := by rw [hc]; rfl
      obtain ⟨role,hd⟩ := (PhysicalTiles.used_key hk face).mpr hu
      exact ⟨g.incoming.get role,role,hd,rfl⟩
    · rw [hc] at hu
      rcases hu with h | h
      · exact ⟨true,Or.inl ⟨rfl,h⟩⟩
      · exact ⟨false,Or.inr ⟨rfl,h⟩⟩

theorem wire_port_unique (e : ℕ) (q : Catalog.Bitmap.Args) (face : Direction) (a b : Bool)
    (ha : LocalPort (some (.inr (e,q))) face a) (hb : LocalPort (some (.inr (e,q))) face b) : a = b := by
  rcases ha with ⟨rfl,ha⟩ | ⟨rfl,ha⟩ <;> rcases hb with ⟨rfl,hb⟩ | ⟨rfl,hb⟩
  · rfl
  · exact (wire_input_ne_output q.1 (ha.symm.trans hb)).elim
  · exact (wire_input_ne_output q.1 (hb.symm.trans ha)).elim
  · rfl

private theorem consecutive_port (a b : Catalog.Kind) (face : Direction) (incoming : Bool)
    (hflow : CellPlan.Consecutive a b face)
    (hp : (incoming = true ∧ face = (Catalog.sourceDirection a).opposite) ∨
      (incoming = false ∧ face = Catalog.targetDirection a)) :
    ((!incoming) = true ∧ face.opposite = (Catalog.sourceDirection b).opposite) ∨
      ((!incoming) = false ∧ face.opposite = Catalog.targetDirection b) := by
  rcases hp with ⟨rfl,hp⟩ | ⟨rfl,hp⟩ <;> rcases hflow with hf | hf
  · exact (wire_input_ne_output a (hp.symm.trans hf.1.symm)).elim
  · exact Or.inr ⟨rfl,hf.2.symm⟩
  · exact Or.inl ⟨rfl,by rw [hf.2]⟩
  · apply False.elim
    apply wire_input_ne_output a
    rw [hf.1,Direction.opposite_opposite]
    exact hp

private theorem gate_wire_port (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (vertex : VertexData) (g : GateTileState) (e : ℕ) (q : Catalog.Bitmap.Args)
    (hcg : CellPlan.cell (v,p) = some (.inl (vertex,g))) (hcw : CellPlan.cell (v,r) = some (.inr (e,q)))
    (incoming : Bool) (hp : LocalPort (CellPlan.cell (v,p)) face incoming) :
    LocalPort (CellPlan.cell (v,r)) face.opposite (!incoming) := by
  rw [hcg] at hp
  obtain ⟨role,hd,hi⟩ := hp
  have hg : PhysicalTiles.key (CellPlan.cell (v,p)) = some (.inl g) := by rw [hcg]; rfl
  have hw : PhysicalTiles.key (CellPlan.cell (v,r)) = some (.inr q) := by rw [hcw]; rfl
  have hf := PhysicalTiles.gate_neighbor_flow v hP hT hg hw role hd hn
  rw [hi] at hf
  rw [hcw]
  cases incoming
  · simp only [Bool.false_eq_true,↓reduceIte] at hf
    exact Or.inl ⟨rfl,by rw [hf]⟩
  · simp only [↓reduceIte] at hf
    exact Or.inr ⟨rfl,hf.symm⟩

theorem local_port_reciprocal (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (incoming : Bool) (hp : LocalPort (CellPlan.cell (v,p)) face incoming) :
    LocalPort (CellPlan.cell (v,r)) face.opposite (!incoming) := by
  have hused := local_port_used v p face incoming hp
  have hother := (CellPlan.used_reciprocal v hP hT hn).mp hused
  cases hca : CellPlan.cell (v,p) with
  | none => simp [hca,LocalPort] at hp
  | some a =>
    cases hcb : CellPlan.cell (v,r) with
    | none => simp [hcb,CellPlan.Used] at hother
    | some b =>
      rcases a with ⟨vertex,g⟩ | ⟨e,q⟩ <;> rcases b with ⟨other,h⟩ | ⟨f,z⟩
      · exact (neighboring_gates_impossible v p r face hn vertex other g h hca hcb).elim
      · simpa only [hcb] using gate_wire_port v hP hT p r face hn vertex g f z hca hcb incoming hp
      · obtain ⟨out,hport⟩ := local_port_of_used v r face.opposite hother
        have hwire := gate_wire_port v hP hT r p face.opposite (neighbor_reverse hn) other h e q hcb hca out hport
        have hwire' : LocalPort (some (.inr (e,q))) face (!out) := by
          simpa only [hca,Direction.opposite_opposite] using hwire
        have hp' : LocalPort (some (.inr (e,q))) face incoming := by simpa only [hca] using hp
        have he := wire_port_unique e q face incoming (!out) hp' hwire'
        have he' : out = !incoming := by simpa only [Bool.not_not] using (congrArg Bool.not he).symm
        simpa only [hcb,he'] using hport
      · rw [hca] at hp
        exact consecutive_port q.1 z.1 face incoming (CellPlan.wire_adjacent v hP hT hn hca hcb hused).2 hp

theorem cell_entry_mem (v : CellPlan.Source) (p : GridRouting.Point)
    (hx : p.1 < Raster.width v.1) (hy : p.2 < Raster.height v.1) :
    (p,CellPlan.cell (v,p)) ∈ CellPlan.cells v := by
  exact List.mem_flatMap.mpr ⟨p.2,List.mem_range.mpr hy,List.mem_map.mpr ⟨p.1,List.mem_range.mpr hx,rfl⟩⟩

theorem code_mem_of_local (w : ℕ) (v : CellPlan.Source) (p : GridRouting.Point) (c : PrimitiveCode)
    (hc : c ∈ localCodes w (CellPlan.cell (v,p))) : (p,c) ∈ codes w v := by
  have hne : CellPlan.cell (v,p) ≠ none := by intro he; simp [he,localCodes] at hc
  have hb := CellPlan.nonempty_bounds hne
  unfold codes
  exact List.mem_flatMap.mpr ⟨(p,CellPlan.cell (v,p)),cell_entry_mem v p hb.1 hb.2,List.mem_map.mpr ⟨c,hc,rfl⟩⟩

end PushPuzzle.PushS.FiniteSourceInventory
