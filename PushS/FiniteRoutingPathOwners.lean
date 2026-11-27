/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSeamOwners
public import PushS.FiniteRoutingPathInventory

/-! Every nonboundary emitted path endpoint has a literal neighboring interior chart owner. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace LineCode

private theorem firstSlot_false (w : ℕ) (hw : 2 ≤ w) (c : LineCode) : c.firstSlot w hw false =
    (Line.rotation w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))
      (segmentDirection c.segment)).cells
        (Line.startCell w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) := by
  apply congrArg (Line.rotation w _ (segmentDirection c.segment)).cells
  apply Prod.ext <;> apply Fin.ext
  · change FiniteTools.radius w+Line.position w _ false (Line.firstLabel w _) = FiniteTools.radius w
    rw [Line.program_position_first]
    rfl
  · rfl

private theorem chart_active_level (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (p : Cell ((PrimitiveCode.line c).chart w hw ()).width ((PrimitiveCode.line c).chart w hw ()).height)
    (hp : ((PrimitiveCode.line c).chart w hw ()).classifier.name p ≠ .outside) :
    (((PrimitiveCode.line c).chart w hw ()).classifier.name p).level =
      (Line.orientedRailName w (segmentDirection c.segment)).level := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  obtain ⟨q,rfl⟩ := (Line.railAxis w atoms (segmentDirection c.segment)).geometry.cells.surjective p
  have hrow : q.2 = Line.railRow w := by
    by_contra hn
    apply hp
    change (Line.railAxis w atoms (segmentDirection c.segment)).name
      ((Line.railClassifier w hw atoms (Line.program_nonempty _ _ _) c.above).name
        ((Line.railAxis w atoms (segmentDirection c.segment)).geometry.cells.symm
          ((Line.railAxis w atoms (segmentDirection c.segment)).geometry.cells q))) = .outside
    rw [Equiv.symm_apply_apply]
    apply ((Line.railAxis w atoms (segmentDirection c.segment)).outside _).mpr
    exact ite_eq_right hn
  have htag := Line.orientedRailChart_row_tag w hw atoms (Line.program_nonempty _ _ _) c.above
    (segmentDirection c.segment) q hrow
  have hl := congrArg AxisTrack.level htag
  change ((Line.orientedRailChart w hw atoms (Line.program_nonempty _ _ _) c.above
    (segmentDirection c.segment)).classifier.name
      ((Line.railAxis w atoms (segmentDirection c.segment)).geometry.cells q)).level = _
  simpa only [AxisTrack.level_shift] using hl

private theorem exit_world (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : (PrimitiveCode.line c).Exit w hw p) :
    (PrimitiveCode.line c).world w hw p = c.firstWorld w hw false ∨
      (PrimitiveCode.line c).world w hw p = c.lastWorld w hw true := by
  rcases hp with hp | hp
  · left
    change (PrimitiveCode.line c).world w hw p = (PrimitiveCode.line c).world w hw (c.firstSlot w hw false)
    rw [firstSlot_false]
    exact congrArg ((PrimitiveCode.line c).world w hw) hp
  · exact Or.inr (congrArg ((PrimitiveCode.line c).world w hw) hp)

end LineCode

namespace TurnCode

private theorem outer_chart_level (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing)
    (incoming : Bool) (q : Cell 7 7)
    (he : ((PrimitiveCode.turn c).chart w hw ()).embedding.cells q = c.outerSlot w incoming) :
    (((PrimitiveCode.turn c).chart w hw ()).classifier.name q).level =
      (Line.orientedRailName w (if incoming then c.incoming else c.outgoing)).level := by
  let base := if incoming then ((0,3) : Cell 7 7) else (3,6)
  have he' : ((PrimitiveCode.turn c).chart w hw ()).embedding.cells
      ((Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells base) = c.outerSlot w incoming :=
    (Turn.orientation_stencil w c.incoming c.outgoing base).symm
  have hq := ((PrimitiveCode.turn c).chart w hw ()).embedding.cells.injective (he.trans he'.symm)
  subst q
  change ((Turn.orientationAxis 7 c.incoming c.outgoing).name
    ((GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name
      ((Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells.symm
        ((Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells base)))).level = _
  rw [Equiv.symm_apply_apply]
  have hbase : (GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name base =
      if incoming then .horizontal 3 else .vertical 3 := by cases incoming <;> decide
  rw [hbase]
  cases incoming <;> cases hd : c.incoming <;> cases ho : c.outgoing <;>
    simp [hd,ho,Perpendicular,rightTurn,Direction.opposite] at hc <;>
    simp [Line.orientedRailName,AxisTrack.level,Turn.orientationAxis,Turn.quarterAxis,rightTurn,
      AxisIsometry.trans,AxisIsometry.refl,AxisIsometry.reflectY,AxisIsometry.reflectX,
      AxisIsometry.clockwise,AxisIsometry.transpose]

end TurnCode

namespace PathSpec

theorem line_mem_codes (P : PathSpec) (i : ℕ) (hi : i < P.segments.length) : .line (P.line i) ∈ P.codes := by
  exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,(P.mem_block i _).mpr (Or.inl rfl)⟩

theorem turn_mem_codes (P : PathSpec) (i : ℕ) (hi : P.hasTurn i) : .turn (P.turn i) ∈ P.codes := by
  exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr (by have h := hi.1; omega),
    (P.mem_block i _).mpr (Or.inr ⟨hi,rfl⟩)⟩

private theorem first_exit_owner (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) (hpos : 0 < i) :
    WorldOwner w hw P.codes ((P.line i).firstWorld w hw false)
      (Line.orientedRailName w (segmentDirection (P.line i).segment)).level := by
  have hp : i-1+1 = i := by omega
  have hi' : i-1+1 < P.segments.length := by omega
  by_cases ht : P.hasTurn (i-1)
  · have H := P.junction_contract w G (i-1) ht
    have h := JunctionContract.outgoing_line_exit_owner w hw _ _ _ H P.codes (P.turn_mem_codes (i-1) ht)
    simpa only [hp] using h
  · have H := P.collinear_contract w G (i-1) hi' ht
    have h := CollinearContract.first_exit_owner w hw _ _ H P.codes (P.line_mem_codes (i-1) (by omega))
    simpa only [hp] using h

private theorem last_exit_owner (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i+1 < P.segments.length) :
    WorldOwner w hw P.codes ((P.line i).lastWorld w hw true)
      (Line.orientedRailName w (segmentDirection (P.line i).segment)).level := by
  by_cases ht : P.hasTurn i
  · exact JunctionContract.incoming_line_exit_owner w hw _ _ _ (P.junction_contract w G i ht)
      P.codes (P.turn_mem_codes i ht)
  · exact CollinearContract.last_exit_owner w hw _ _ (P.collinear_contract w G i hi ht)
      P.codes (P.line_mem_codes (i+1) hi)

private theorem incoming_turn_exit_owner (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) :
    WorldOwner w hw P.codes ((P.turn i).outerWorld w hw true)
      (Line.orientedRailName w (P.turn i).incoming).level :=
  JunctionContract.incoming_turn_exit_owner w hw _ _ _ (P.junction_contract w G i hi)
    P.codes (P.line_mem_codes i (by have h := hi.1; omega))

private theorem outgoing_turn_exit_owner (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) :
    WorldOwner w hw P.codes ((P.turn i).outerWorld w hw false)
      (Line.orientedRailName w (P.turn i).outgoing).level :=
  JunctionContract.outgoing_turn_exit_owner w hw _ _ _ (P.junction_contract w G i hi)
    P.codes (P.line_mem_codes (i+1) hi.1)

def BoundaryExit (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (point : ℕ × ℕ) (level : ℕ) : Prop :=
  (point = (P.line 0).firstWorld w hw false ∧
    level = (Line.orientedRailName w (segmentDirection (P.line 0).segment)).level) ∨
  (point = (P.line (P.segments.length-1)).lastWorld w hw true ∧
    level = (Line.orientedRailName w (segmentDirection (P.line (P.segments.length-1)).segment)).level)

/-- Every actual path chart exit is owned internally or is one of the two literal exterior endpoint cells. -/
theorem chart_exit_owner_or_boundary (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (chart : c.Charts)
    (q : Cell (c.chart w hw chart).width (c.chart w hw chart).height)
    (hq : (c.chart w hw chart).classifier.name q ≠ .outside)
    (he : c.Exit w hw ((c.chart w hw chart).embedding.cells q)) :
    WorldOwner w hw P.codes (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level ∨
    P.BoundaryExit w hw (c.world w hw ((c.chart w hw chart).embedding.cells q))
      ((c.chart w hw chart).classifier.name q).level := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · cases chart
    have hlevel := LineCode.chart_active_level w hw (P.line i) q hq
    rcases LineCode.exit_world w hw (P.line i) _ he with hfirst | hlast
    · by_cases hz : i = 0
      · subst i
        exact Or.inr (Or.inl ⟨hfirst,hlevel⟩)
      · have ho := P.first_exit_owner w hw G i hi' (by omega)
        rw [←hfirst,←hlevel] at ho
        exact Or.inl ho
    · by_cases hn : i+1 < P.segments.length
      · have ho := P.last_exit_owner w hw G i hn
        rw [←hlast,←hlevel] at ho
        exact Or.inl ho
      · have hz : i = P.segments.length-1 := by omega
        subst i
        exact Or.inr (Or.inr ⟨hlast,hlevel⟩)
  · cases chart
    rcases he with he | he
    · have hlevel := TurnCode.outer_chart_level w hw (P.turn i) (P.turn_perpendicular w G i ht) true q he
      have hworld := congrArg ((PrimitiveCode.turn (P.turn i)).world w hw) he
      change (PrimitiveCode.turn (P.turn i)).world w hw
        (((PrimitiveCode.turn (P.turn i)).chart w hw ()).embedding.cells q) = (P.turn i).outerWorld w hw true at hworld
      simp only [↓reduceIte] at hlevel
      have ho := P.incoming_turn_exit_owner w hw G i ht
      rw [←hworld,←hlevel] at ho
      exact Or.inl ho
    · have hlevel := TurnCode.outer_chart_level w hw (P.turn i) (P.turn_perpendicular w G i ht) false q he
      have hworld := congrArg ((PrimitiveCode.turn (P.turn i)).world w hw) he
      change (PrimitiveCode.turn (P.turn i)).world w hw
        (((PrimitiveCode.turn (P.turn i)).chart w hw ()).embedding.cells q) = (P.turn i).outerWorld w hw false at hworld
      simp only [Bool.false_eq_true,↓reduceIte] at hlevel
      have ho := P.outgoing_turn_exit_owner w hw G i ht
      rw [←hworld,←hlevel] at ho
      exact Or.inl ho

end PathSpec

end PushPuzzle.PushS.FiniteRouting
