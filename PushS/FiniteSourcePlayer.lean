/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceInventory
public import PushS.FiniteRoutingPrimitiveGeometry

/-! The actual source compiler reserves its exterior player cell beyond every primitive rectangle. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

private theorem Line.offset_pos (w : ℕ) (atoms : List Line.Atom) (d : Direction) (p q : ℕ × ℕ)
    (ht : Travels d p q (Line.span w atoms)) :
    0 < Line.offsetX w atoms d p ∧ 0 < Line.offsetY w atoms d p := by
  cases d <;> dsimp [Travels,Line.offsetX,Line.offsetY,Line.anchor] at * <;>
    unfold padding FiniteTools.radius at * <;> omega

private theorem lineCode_offset_pos (w : ℕ) (c : LineCode) (hg : LineGood w c.segment) :
    0 < (PrimitiveCode.line c).offsetX w ∧ 0 < (PrimitiveCode.line c).offsetY w := by
  apply Line.offset_pos w _ _ _ c.segment.finish
  rw [Line.program_span_of_bound _ _ _ hg.2.1]
  exact segment_travels c.segment hg.1

theorem gateCode_offset_pos (w : ℕ) (g : GateTileState) {c : PrimitiveCode} (hc : c ∈ gateCodes w g) :
    0 < c.offsetX w ∧ 0 < c.offsetY w := by
  cases c with
  | core g => simp only [PrimitiveCode.offsetX,PrimitiveCode.offsetY]; unfold padding; omega
  | line c => exact lineCode_offset_pos w c (gateCodes_line_good w g c hc).1
  | turn c =>
    simp only [PrimitiveCode.offsetX,PrimitiveCode.offsetY,Turn.offsetX,Turn.offsetY]
    unfold padding FiniteTools.radius
    omega

theorem wireCode_offset_pos (w : ℕ) (q : Catalog.Bitmap.Args) {c : PrimitiveCode} (hc : c ∈ wireCodes w q) :
    0 < c.offsetX w ∧ 0 < c.offsetY w := by
  cases c with
  | core g => simp only [PrimitiveCode.offsetX,PrimitiveCode.offsetY]; unfold padding; omega
  | line c => exact lineCode_offset_pos w c (wireCodes_line_good w q c hc).1
  | turn c =>
    simp only [PrimitiveCode.offsetX,PrimitiveCode.offsetY,Turn.offsetX,Turn.offsetY]
    unfold padding FiniteTools.radius
    omega

end PushPuzzle.PushS.FiniteRouting

namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height

private theorem localCode_offset_pos (w : ℕ) (c : CellPlan.Code) {p : PrimitiveCode}
    (hp : p ∈ localCodes w c) : 0 < p.offsetX w ∧ 0 < p.offsetY w := by
  cases c with
  | none => simp [localCodes] at hp
  | some c =>
    cases c with
    | inl g => exact gateCode_offset_pos w g.2 hp
    | inr q => exact wireCode_offset_pos w q.2 hp

private theorem code_offset_pos (w : ℕ) (v : CellPlan.Source)
    {q : GridRouting.Point × PrimitiveCode}
    (hq : q ∈ codes w v) : 0 < q.2.offsetX w ∧ 0 < q.2.offsetY w := by
  unfold codes at hq
  obtain ⟨entry,_,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  exact localCode_offset_pos w entry.2 hp

theorem inventory_dx_pos (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (i : Fin (codes w v).length) :
    0 < (inventory w hw v).dx i := by
  have hp := (code_offset_pos w v (List.get_mem (codes w v) i)).1
  change 0 < tileStride w*((codes w v).get i).1.1+((codes w v).get i).2.offsetX w
  omega

/-- The actual exterior player cell is absent from the complete emitted wall union. -/
theorem player_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    (inventory w hw v).player ∉ (inventory w hw v).walls :=
  (inventory w hw v).player_floor_of_dx_pos rfl (inventory_dx_pos w hw v)

/-- No owned box occupies the actual exterior player cell. -/
theorem player_empty (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (l : (inventory w hw v).PhysicalLabel) :
    (inventory w hw v).player ≠ (inventory w hw v).source l :=
  (inventory w hw v).player_empty_of_dx_pos rfl (inventory_dx_pos w hw v) l

end PushPuzzle.PushS.FiniteSourceInventory
