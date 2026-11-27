/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalPorts

/-! Gate overlap exclusions and the exterior player for the actual full source plan. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Plan PhysicalBitmap

theorem key_nonempty {c : CellPlan.Code} {k : Key} (hk : key c=some k) : c≠none := by
  intro he
  cases he
  cases hk

theorem same_position_key {q : CellPlan.Source} {p : GridRouting.Point} {k l : Key}
    (hk : key (CellPlan.cell (q,p))=some k) (hl : key (CellPlan.cell (q,p))=some l) : k=l :=
  Option.some.inj (hk.symm.trans hl)

/-- The exact global player (1,1) is outside every real source tile rectangle. -/
theorem player_outside {q : CellPlan.Source} {p : GridRouting.Point} {k : Key}
    (hk : key (CellPlan.cell (q,p))=some k) (s : Cell (piece k).width (piece k).height) :
    (1,1)≠coordinates p k s := by
  have hp := CellPlan.nonempty_lower (key_nonempty hk)
  have hb := coordinate_bounds p k s
  dsimp only [strideX,strideY] at hb
  intro he
  have hx := congrArg Prod.fst he
  omega

theorem gate_gate_overlap {v : CellPlan.Source} {p r : GridRouting.Point} {g h : GateTileState}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (hh : key (CellPlan.cell (v,r))=some (.inl h))
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inl h)).width (piece (.inl h)).height)
    (he : coordinates p (.inl g) q=coordinates r (.inl h) s) : p=r := by
  obtain ⟨a,ha⟩ := gate_code hg
  obtain ⟨b,hb⟩ := gate_code hh
  obtain ⟨_,hap⟩ := Raster.vertexAt_sound (CellPlan.gate_sound ha).1
  obtain ⟨_,hbr⟩ := Raster.vertexAt_sound (CellPlan.gate_sound hb).1
  have hn := overlap_neighbors p r (.inl g) (.inl h) q s he
  rw [←hap,←hbr] at hn
  exact hap.symm.trans ((refinePoint_near_eq ⟨hn.1,hn.2.1⟩ ⟨hn.2.2.1,hn.2.2.2⟩).trans hbr)

/-- A real ordinary tile meeting a gate rectangle shares its row or column. -/
theorem gate_wire_overlap_axis {v : CellPlan.Source} {p r : GridRouting.Point} {g : GateTileState}
    {a : Gadgets.Wires.Catalog.Bitmap.Args}
    (hg : key (CellPlan.cell (v,p))=some (.inl g)) (ha : key (CellPlan.cell (v,r))=some (.inr a))
    (q : Cell (piece (.inl g)).width (piece (.inl g)).height)
    (s : Cell (piece (.inr a)).width (piece (.inr a)).height)
    (he : coordinates p (.inl g) q=coordinates r (.inr a) s) : r.1=p.1 ∨r.2=p.2 := by
  obtain ⟨b,hb⟩ := gate_code hg
  obtain ⟨e,hc⟩ := wire_code ha
  obtain ⟨_,hbp⟩ := Raster.vertexAt_sound (CellPlan.gate_sound hb).1
  have ht := Raster.owner_sound (CellPlan.wire_sound hc).2.1
  have hn := overlap_neighbors p r (.inl g) (.inr a) q s he
  rw [←hbp] at hn ⊢
  exact Raster.trace_near_anchor ht ⟨hn.2.1,hn.1⟩ ⟨hn.2.2.2,hn.2.2.1⟩

theorem same_position_cell {p : GridRouting.Point} {k : Key}
    {q s : Cell (piece k).width (piece k).height} (he : coordinates p k q=coordinates p k s) : q=s := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext <;> apply Fin.ext <;> dsimp only [coordinates] at hx hy <;> omega

end PushPuzzle.PushFS.Reduction.PhysicalTiles
