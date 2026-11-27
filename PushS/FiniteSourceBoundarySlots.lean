/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceArmEndpoints
public import PushS.FiniteSourcePortPhases
public import PushS.FiniteSourcePorts

/-! Literal normal endpoint cells across the actual source-tile seams. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory Line.width Line.height LineSite.atoms

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

/-- Every canonical phase of a producing source port is the same physical slot on its consuming neighbor. -/
theorem macro_boundary_phase (d : Direction) (p r : GridRouting.Point) (phase : Bool)
    (hn : PushFS.Reduction.neighbor d p = some r) :
    macroShift w p (boundarySlot w d false phase) =
      macroShift w r (boundarySlot w d.opposite true (!phase)) :=
  boundary_seam w d (tileStride w*p.1,tileStride w*p.2) (tileStride w*r.1,tileStride w*r.2) phase
    (macro_neighbor_travels w d p r hn)

namespace PathSite

variable {P : PathSpec} (s : PathSite w hw v P)

/-- A kept final endpoint is owned by the actual last emitted line. -/
theorem final_owned (i : Fin P.segments.length) (hi : i.val+1 = P.segments.length)
    (hk : P.keepEndpoint = true) : (s.line i).code.last = true := by
  simp only [line,PathSpec.line,lineCodeAt,ownsLast,hi,ite_true,hk]

/-- The real physical identity at a path's kept final endpoint. -/
def finalIdentity (i : Fin P.segments.length) (hi : i.val+1 = P.segments.length)
    (hk : P.keepEndpoint = true) : (inventory w hw v).PhysicalLabel :=
  (s.line i).finalLabel (s.final_owned i hi hk)

theorem finalIdentity_owner (i : Fin P.segments.length) (hi : i.val+1 = P.segments.length)
    (hk : P.keepEndpoint = true) : (s.finalIdentity i hi hk).1 = (s.line i).index :=
  primitiveLabel_owner w hw v _ _ _ _

/-- A kept path needs only its actual external first identity. -/
noncomputable def Endpoints.of_kept (hk : P.keepEndpoint = true)
    (first : (inventory w hw v).PhysicalLabel)
    (hs : ∀ h,(inventory w hw v).source first = (s.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨0,h⟩).atoms P.initial (Line.cutFirstLabel w (s.line ⟨0,h⟩).atoms)))
    (ht : ∀ h,(inventory w hw v).target first = (s.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨0,h⟩).atoms P.target (Line.cutFirstLabel w (s.line ⟨0,h⟩).atoms))) : s.Endpoints where
  first := first
  final h := by have hh := hk.symm.trans h; cases hh
  source_first := hs
  target_first := ht
  source_final h := by have hh := hk.symm.trans h; cases hh
  target_final h := by have hh := hk.symm.trans h; cases hh

end PathSite

namespace WireBoundary

variable {a : Catalog.Bitmap.Args} (s : PathSite w hw v (wireSpec w a))

theorem length_pos : 0 < (wireSpec w a).segments.length := by
  change 0 < (wireRoute w a.1).length
  rw [wireRoute_length]
  split_ifs <;> omega

def lastIndex : Fin (wireSpec w a).segments.length := ⟨(wireSpec w a).segments.length-1,by
  have := length_pos (w := w) (a := a)
  omega⟩

theorem lastIndex_final : (lastIndex (w := w) (a := a)).val+1 = (wireSpec w a).segments.length := by
  have := length_pos (w := w) (a := a)
  change (wireSpec w a).segments.length-1+1 = (wireSpec w a).segments.length
  omega

theorem keep_endpoint : (wireSpec w a).keepEndpoint = true := rfl

def outputIdentity : (inventory w hw v).PhysicalLabel :=
  s.finalIdentity lastIndex lastIndex_final keep_endpoint

private theorem first_world (phase : Bool) : ((wireSpec w a).line 0).firstWorld w hw phase =
    boundarySlot w (Catalog.sourceDirection a.1).opposite true (!phase) := by
  rw [LineCode.firstWorld_eq w hw _ ((wireSpec w a).line_good w (wireSpec_geometry w a) 0 length_pos),
    wire_first_direction,wire_first_start]
  simpa only [Direction.opposite_opposite] using wire_input_slot w (Catalog.sourceDirection a.1).opposite phase

private theorem last_world (phase : Bool) :
    ((wireSpec w a).line (lastIndex (w := w) (a := a)).val).lastWorld w hw phase = boundarySlot w (Catalog.targetDirection a.1) false phase := by
  rw [LineCode.lastWorld_eq w hw _ ((wireSpec w a).line_good w (wireSpec_geometry w a) _ lastIndex.isLt),
    wire_last_direction w a _ lastIndex_final,wire_last_finish w a _ lastIndex_final]
  rfl

/-- The actual first wire slot uses the complementary local inward phase at the source boundary. -/
theorem first_coordinates (phase : Bool) (h : 0 < (wireSpec w a).segments.length) :
    coordinates ((s.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨0,h⟩).atoms phase (Line.cutFirstLabel w (s.line ⟨0,h⟩).atoms))) =
      macroShift w s.location (boundarySlot w (Catalog.sourceDirection a.1).opposite true (!phase)) := by
  rw [(s.line ⟨0,h⟩).actual_first_coordinates,s.line_location]
  exact congrArg (macroShift w s.location) (first_world (hw := hw) phase)

/-- The actual kept final wire identity lies on its producing source port. -/
theorem output_source : coordinates ((inventory w hw v).source (outputIdentity s)) =
    macroShift w s.location (boundarySlot w (Catalog.targetDirection a.1) false a.2.1) := by
  unfold outputIdentity PathSite.finalIdentity
  rw [LineSite.source_finalLabel,
    (s.line lastIndex).actual_last_coordinates,s.line_location]
  exact congrArg (macroShift w s.location) (last_world (hw := hw) a.2.1)

theorem output_target : coordinates ((inventory w hw v).target (outputIdentity s)) =
    macroShift w s.location (boundarySlot w (Catalog.targetDirection a.1) false a.2.2) := by
  unfold outputIdentity PathSite.finalIdentity
  rw [LineSite.target_finalLabel,
    (s.line lastIndex).actual_last_coordinates,s.line_location]
  exact congrArg (macroShift w s.location) (last_world (hw := hw) a.2.2)

theorem output_owner_location : ((codes w v).get (outputIdentity s).1).1 = s.location := by
  rw [outputIdentity,PathSite.finalIdentity_owner]
  exact s.line_location _

end WireBoundary

/-- Literal coordinate equality determines a cell in the complete output board. -/
theorem boundaryCell_ext {W H : ℕ} {p q : Cell W H} (h : coordinates p = coordinates q) : p = q :=
  Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))

/-- A real consecutive wire tile supplies the entire input endpoint identity in both actual normal configurations. -/
noncomputable def wire_wire_endpoints {a b : Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (wireSpec w b))
    (hn : PushFS.Reduction.neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : Catalog.sourceDirection b.1 = Catalog.targetDirection a.1)
    (hs : a.2.1 = b.2.1) (ht : a.2.2 = b.2.2) : t.Endpoints := by
  apply PathSite.Endpoints.of_kept t rfl (WireBoundary.outputIdentity s)
  · intro h
    apply boundaryCell_ext
    rw [WireBoundary.output_source,WireBoundary.first_coordinates,hd]
    exact (macro_boundary_phase _ _ _ _ hn).trans
      (congrArg (fun q => macroShift w t.location
        (boundarySlot w (Catalog.targetDirection a.1).opposite true (!q))) hs)
  · intro h
    apply boundaryCell_ext
    rw [WireBoundary.output_target,WireBoundary.first_coordinates,hd]
    exact (macro_boundary_phase _ _ _ _ hn).trans
      (congrArg (fun q => macroShift w t.location
        (boundarySlot w (Catalog.targetDirection a.1).opposite true (!q))) ht)

/-- A genuine source-grid neighbor occupies a different source macrocell. -/
theorem neighbor_distinct {d : Direction} {p r : GridRouting.Point}
    (hn : PushFS.Reduction.neighbor d p = some r) : p ≠ r := by
  intro he
  have ht := neighbor_travels hn
  rw [he] at ht
  cases d <;> dsimp [Travels] at ht <;> omega

/-- The actual primitive owner of every event retains its source-tile location. -/
theorem PathEvent.owner_location {P : PathSpec} (p : PathSite w hw v P) (a : PathEvent P) :
    ((codes w v).get (a.owner p)).1 = p.location :=
  congrArg Prod.fst (p.get_index a.code a.member)

/-- Actual reciprocal wire ports give the source direction of the following emitted path. -/
theorem wire_wire_direction (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    {a b : Catalog.Bitmap.Args} (e f : ℕ)
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (wireSpec w b))
    (hn : PushFS.Reduction.neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hca : CellPlan.cell (v,s.location) = some (.inr (e,a)))
    (hcb : CellPlan.cell (v,t.location) = some (.inr (f,b))) :
    Catalog.sourceDirection b.1 = Catalog.targetDirection a.1 := by
  have hp : LocalPort (CellPlan.cell (v,s.location)) (Catalog.targetDirection a.1) false := by
    rw [hca]
    exact Or.inr ⟨rfl,rfl⟩
  have hh := local_port_reciprocal v hP hT _ _ _ hn false hp
  rw [hcb] at hh
  rcases hh with ⟨_,hd⟩ | ⟨h,_⟩
  · have hd' := congrArg Direction.opposite hd
    simpa only [Direction.opposite_opposite] using hd'.symm
  · cases h

/-- Real source metadata automatically identifies the complete consumer wire endpoint selection. -/
noncomputable def actual_wire_wire_endpoints (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    {a b : Catalog.Bitmap.Args} (e f : ℕ)
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (wireSpec w b))
    (hn : PushFS.Reduction.neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hca : CellPlan.cell (v,s.location) = some (.inr (e,a)))
    (hcb : CellPlan.cell (v,t.location) = some (.inr (f,b))) : t.Endpoints := by
  have hu : CellPlan.Used (CellPlan.cell (v,s.location)) (Catalog.targetDirection a.1) := by
    rw [hca]
    exact Or.inr rfl
  have hs : a.2.1 = b.2.1 := by
    simpa only [PhysicalTiles.wirePhase,Bool.false_eq_true,ite_false] using
      wire_neighbor_phase v hP hT _ _ _ hn e f a b hca hcb hu false
  have ht : a.2.2 = b.2.2 := by
    simpa only [PhysicalTiles.wirePhase,ite_true] using
      wire_neighbor_phase v hP hT _ _ _ hn e f a b hca hcb hu true
  exact wire_wire_endpoints s t hn (wire_wire_direction hP hT e f s t hn hca hcb) hs ht

end PushPuzzle.PushS.FiniteSourceInventory
