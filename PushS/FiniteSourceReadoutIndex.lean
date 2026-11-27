/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCorePorts
public import PushFS.Reduction.PhysicalSourceIncidences

/-! Every original source incidence selects its literal compiled core outer-box identity. -/

public section

namespace PushPuzzle.PushFS.Reduction.CellPlan.Source

/-- Initial orientation bits in the standard source compiler input. -/
@[expose] def initialBits (v : CellPlan.Source) : List Bool := v.2.1

/-- Target orientation bits in the standard source compiler input. -/
@[expose] def targetBits (v : CellPlan.Source) : List Bool := v.2.2

end PushPuzzle.PushFS.Reduction.CellPlan.Source

namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry
open Cslib.Complexity.NCL Plan PhysicalInventory

attribute [local irreducible] codes width height Raster.width Raster.height

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

theorem record_entry (g : VertexData) (hg : g ∈ vertexRecords v.1) :
    (refinePoint g.point,some (.inl (g,gateTileState (g,v.2)))) ∈ CellPlan.cells v := by
  have hb := Raster.vertex_bounds v.1 hg
  have h := cell_entry_mem v (refinePoint g.point) (by omega) (by omega)
  rw [CellPlan.cell_gate v _ ((Raster.vertexAt_eq_some_iff _ _ _).mpr ⟨hg,rfl⟩)] at h
  exact h

/-- The compiler core owned by the given original source vertex record. -/
@[expose]
def recordSite (g : VertexData) (hg : g ∈ vertexRecords v.1) : CoreSite w hw v :=
  CoreSite.of_gate (refinePoint g.point) (g,gateTileState (g,v.2)) (record_entry v g hg)

theorem recordSite_location (g : VertexData) (hg : g ∈ vertexRecords v.1) :
    ((codes w v).get (recordSite w hw v g hg).index).1 = refinePoint g.point :=
  CoreSite.of_gate_location _ _ _

theorem recordSite_index_injective {g h : VertexData} (hg : g ∈ vertexRecords v.1) (hh : h ∈ vertexRecords v.1)
    (he : (recordSite w hw v g hg).index = (recordSite w hw v h hh).index) : g = h := by
  have hp := congrArg (fun i => ((codes w v).get i).1) he
  rw [recordSite_location,recordSite_location] at hp
  exact vertexRecords_point_injective hg hh (refinePoint_injective hp)

theorem CoreSite.portLabel_injective (s : CoreSite w hw v) : Function.Injective s.portLabel := by
  intro r t he
  by_cases hk : s.gate.core.isAND = true
  · have hl : andPortLabel w r = andPortLabel w t := s.andLabel_injective hk (by
      simpa only [CoreSite.portLabel,dite_eq_left hk] using he)
    fin_cases r <;> fin_cases t <;> simp_all [andPortLabel]
  · have hl : orPortLabel w r = orPortLabel w t := s.orLabel_injective (Bool.eq_false_iff.mpr hk) (by
      simpa only [CoreSite.portLabel,dite_eq_right hk] using he)
    fin_cases r <;> fin_cases t <;> simp_all [orPortLabel]

/-- An original vertex record paired with one of its three ordered ports. -/
abbrev RecordPort := PhysicalInventory.GatePort v

/-- Map each original record port to its actual compiled outer-box identity. -/
@[expose]
def recordPorts : RecordPort v ↪ (inventory w hw v).PhysicalLabel where
  toFun p := (recordSite w hw v p.1.val p.1.property).portLabel p.2
  inj' := by
    rintro ⟨⟨g,hg⟩,r⟩ ⟨⟨h,hh⟩,t⟩ he
    have hi := congrArg (fun l : (inventory w hw v).PhysicalLabel => l.1) he
    rw [CoreSite.portLabel_owner,CoreSite.portLabel_owner] at hi
    have hgh := recordSite_index_injective w hw v hg hh hi
    subst h
    have hrt := CoreSite.portLabel_injective w hw v (recordSite w hw v g hg) he
    change r = t at hrt
    subst t
    rfl

/-- The exact finite NCL incidence chooses its actual source-record outer port label. -/
@[expose]
noncomputable def sourcePortLabels (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hG : (Word.compile v.1).graph.WellFormed) :
    PortIncidence (Word.compile v.1).graph ↪ (inventory w hw v).PhysicalLabel where
  toFun i := recordPorts w hw v (⟨sourceRecord v.1 hP hT i.1,sourceRecord_mem v.1 hP hT i.1⟩,
    sourceRole v.1 hvalid hP hT i)
  inj' := by
    intro i j he
    have hh := (recordPorts w hw v).injective he
    exact source_role_injective v.1 hvalid hP hT hG
      (congrArg (fun p : RecordPort v => (p.1.val,p.2)) hh)

end PushPuzzle.PushS.FiniteSourceInventory
