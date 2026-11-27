/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingBoundaryOwners

/-! Complete actual gate and wire chart seams: interior owners or canonical high boundary ports. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem WorldOwner.mono (w : ℕ) (hw : 2 ≤ w) (small large : List PrimitiveCode)
    (hs : ∀ c ∈ small, c ∈ large) {point : ℕ × ℕ} {level : ℕ}
    (ho : WorldOwner w hw small point level) : WorldOwner w hw large point level := by
  obtain ⟨c,hc,p,he,hp⟩ := ho
  exact ⟨c,hs c hc,p,he,hp⟩

private theorem Line.orientedRailName_opposite (w : ℕ) (d : Direction) :
    Line.orientedRailName w d.opposite = Line.orientedRailName w d := by cases d <;> rfl

def PortExit (w : ℕ) (code : CellPlan.Code) (point : ℕ × ℕ) (level : ℕ) : Prop :=
  ∃ face incoming, LocalPort code face incoming ∧ point = boundarySlot w face incoming true ∧
    level = (Line.orientedRailName w face).level

private theorem gate_chart_exit_owner_or_port (w : ℕ) (hw : 2 ≤ w) (g : CellPlan.Gate)
    (c : PrimitiveCode) (hc : c ∈ gateCodes w g.2) (chart : c.Charts)
    (q : Cell (c.chart w hw chart).width (c.chart w hw chart).height)
    (hq : (c.chart w hw chart).classifier.name q ≠ .outside)
    (he : c.Exit w hw ((c.chart w hw chart).embedding.cells q)) :
    WorldOwner w hw (gateCodes w g.2) (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level ∨
    PortExit w (some (.inl g)) (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inl (core_chart_exit_owner w hw g.2 chart q he)
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    let P := armSpec w g.2 role
    rcases P.chart_exit_owner_or_boundary w hw (armSpec_geometry w g.2 role) c hc chart q hq he with ho | hb
    · exact Or.inl (WorldOwner.mono w hw P.codes (gateCodes w g.2) (arm_code_mem_gateCodes w g.2 role) ho)
    · rcases hb with ⟨hpoint,hlevel⟩ | ⟨hpoint,hlevel⟩
      · have ho := first_line_core_owner w hw g.2 role
        change c.world w hw ((c.chart w hw chart).embedding.cells q) =
          ((armSpec w g.2 role).line 0).firstWorld w hw false at hpoint
        change ((c.chart w hw chart).classifier.name q).level =
          (Line.orientedRailName w (segmentDirection ((armSpec w g.2 role).line 0).segment)).level at hlevel
        rw [armSpec_first_direction] at hlevel
        rw [←hpoint,←hlevel] at ho
        exact Or.inl ho
      · refine Or.inr ⟨PortAnnulus.outerDirection (g.2.pattern,g.2.rotation,role),g.2.incoming.get role,
          ⟨role,rfl,rfl⟩,?_,?_⟩
        · exact hpoint.trans (armSpec_last_slot w hw g.2 role true)
        · change ((c.chart w hw chart).classifier.name q).level =
            (Line.orientedRailName w (segmentDirection ((armSpec w g.2 role).line ((armRoute w g.2 role).length-1)).segment)).level at hlevel
          simpa only [armSpec_last_direction] using hlevel

private theorem wire_chart_exit_owner_or_port (w : ℕ) (hw : 2 ≤ w) (wire : CellPlan.Wire)
    (c : PrimitiveCode) (hc : c ∈ wireCodes w wire.2) (chart : c.Charts)
    (q : Cell (c.chart w hw chart).width (c.chart w hw chart).height)
    (hq : (c.chart w hw chart).classifier.name q ≠ .outside)
    (he : c.Exit w hw ((c.chart w hw chart).embedding.cells q)) :
    WorldOwner w hw (wireCodes w wire.2) (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level ∨
    PortExit w (some (.inr wire)) (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level := by
  let P := wireSpec w wire.2
  rcases P.chart_exit_owner_or_boundary w hw (wireSpec_geometry w wire.2) c hc chart q hq he with ho | hb
  · exact Or.inl ho
  · rcases hb with ⟨hpoint,hlevel⟩ | ⟨hpoint,hlevel⟩
    · have hi : 0 < (wireRoute w wire.2.1).length := by rw [wireRoute_length]; split_ifs <;> decide
      have hgood := P.line_good w (wireSpec_geometry w wire.2) 0 hi
      refine Or.inr ⟨(Catalog.sourceDirection wire.2.1).opposite,true,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
      · apply hpoint.trans
        rw [LineCode.firstWorld_eq w hw _ hgood,wire_first_direction,wire_first_start]
        simpa only [Direction.opposite_opposite,Bool.not_false] using
          wire_input_slot w (Catalog.sourceDirection wire.2.1).opposite false
      · change ((c.chart w hw chart).classifier.name q).level =
          (Line.orientedRailName w (segmentDirection ((wireSpec w wire.2).line 0).segment)).level at hlevel
        simpa only [wire_first_direction,Line.orientedRailName_opposite] using hlevel
    · let i := (wireRoute w wire.2.1).length-1
      have hpos : 0 < (wireRoute w wire.2.1).length := by rw [wireRoute_length]; split_ifs <;> decide
      have hi : i < (wireRoute w wire.2.1).length := by dsimp [i]; omega
      have hil : i+1 = (wireRoute w wire.2.1).length := by dsimp [i]; omega
      have hgood := P.line_good w (wireSpec_geometry w wire.2) i hi
      refine Or.inr ⟨Catalog.targetDirection wire.2.1,false,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
      · apply hpoint.trans
        change (P.line i).lastWorld w hw true = _
        rw [LineCode.lastWorld_eq w hw _ hgood,wire_last_direction w wire.2 i hil,wire_last_finish w wire.2 i hil]
        rfl
      · change ((c.chart w hw chart).classifier.name q).level =
          (Line.orientedRailName w (segmentDirection ((wireSpec w wire.2).line i).segment)).level at hlevel
        simpa only [wire_last_direction w wire.2 i hil] using hlevel

theorem local_chart_exit_owner_or_port (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code)
    (c : PrimitiveCode) (hc : c ∈ FiniteSourceInventory.localCodes w code) (chart : c.Charts)
    (q : Cell (c.chart w hw chart).width (c.chart w hw chart).height)
    (hq : (c.chart w hw chart).classifier.name q ≠ .outside)
    (he : c.Exit w hw ((c.chart w hw chart).embedding.cells q)) :
    WorldOwner w hw (FiniteSourceInventory.localCodes w code) (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level ∨
    PortExit w code (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_chart_exit_owner_or_port w hw g c hc chart q hq he
    | inr wire => exact wire_chart_exit_owner_or_port w hw wire c hc chart q hq he

end PushPuzzle.PushS.FiniteRouting
