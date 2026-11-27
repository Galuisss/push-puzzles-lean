/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Interface
public import PushFS.Gadgets.Wires.Chain.CoveredPlacement

/-! Exact corner replay under overlapping actual collar boxes for any finite wire glyph. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Template


variable {w h count W H : ℕ} {T : Template w h count}

/-- Both literal corner walks survive all actual external boxes represented in the local rail mask. -/
theorem Checked.corners_covered (hc : T.Checked) (phase : Bool) (i : Fin 4)
    (fixed : Finset (Cell w h)) (hf : fixed ⊆ T.reservedCells) (hfw : Disjoint fixed T.walls)
    (e : GridEmbedding w h W H) {B : Board W H} {external : Finset (Cell W H)}
    (hw : e.WallsAgree (T.board ∅) B)
    (hinside : ∀ p, e.cells p∈external → p∈fixed)
    (hfixed : ∀ p∈fixed, e.cells p∈external) (he : Disjoint external B.walls) :
    Reachable B (some 1) (e.extend external (T.state phase)) (e.extend external ⟨T.corner i,T.boxes phase⟩) ∧
    Reachable B (some 1) (e.extend external ⟨T.corner i,T.boxes phase⟩) (e.extend external (T.state phase)) := by
  have ha := Finset.union_subset (hc.boxes_reserved phase) hf
  have haw := Finset.disjoint_union_left.mpr ⟨hc.boxes_floor phase,hfw⟩
  have hforward := hc.corner_reachable i ∅ (T.boxes phase∪fixed) ha haw
  have hbackward := hc.corner_to_hub i ∅ (T.boxes phase∪fixed) ha haw
  constructor
  · apply e.reachable_withFixed hw hinside hfixed he
    simpa only [Gates.withFixed,Template.state] using hforward
  · apply e.reachable_withFixed hw hinside hfixed he
    simpa only [Gates.withFixed,Template.state] using hbackward

end PushPuzzle.PushFS.Gadgets.Wires.Template
