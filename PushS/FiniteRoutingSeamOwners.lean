/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FinitePrimitiveCharts
public import PushS.FiniteRoutingSharedSlots

/-! Concrete interior stencil owners at real straight and turn seam slots. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace LineCode

def railPoint (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let q : Cell (Line.span w atoms+2) (Line.height w) :=
    (⟨n,by have h : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1; omega⟩,
      Line.railRow w)
  (Line.rotation w atoms (segmentDirection c.segment)).cells ((Line.railEmbedding w atoms).cells q)

theorem railPoint_world (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment) :
    (PrimitiveCode.line c).world w hw (c.railPoint w hw hc n hn) =
      Line.along w (segmentDirection c.segment) c.segment.start n := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  let q : Cell (Line.span w atoms+2) (Line.height w) :=
    (⟨n,by omega⟩,Line.railRow w)
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [hlen]
    exact segment_travels _ hc.1
  have h := Line.placement_row w atoms (segmentDirection c.segment) c.segment.start c.segment.finish ht hc.2.2.1 hc.2.2.2
    ((Line.railEmbedding w atoms).cells q) (by change FiniteTools.radius w ≤ FiniteTools.radius w+n; omega)
    (by change FiniteTools.radius w+n ≤ FiniteTools.radius w+Line.span w atoms; omega)
    (by change 0+FiniteTools.radius w = FiniteTools.radius w; omega)
  change coordinates ((Line.placement w atoms (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2).cells ((Line.railEmbedding w atoms).cells q)) =
      Line.along w (segmentDirection c.segment) c.segment.start n
  change coordinates ((Line.placement w atoms (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2).cells ((Line.railEmbedding w atoms).cells q)) =
      Line.along w (segmentDirection c.segment) c.segment.start (FiniteTools.radius w+n-FiniteTools.radius w) at h
  simpa only [Nat.add_sub_cancel_left] using h

/-- Every scalar strictly inside the two exposed endpoint columns has its actual oriented rail owner. -/
theorem railPoint_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn0 : 0 < n) (hn : n ≤ segmentLength c.segment) :
    (PrimitiveCode.line c).Owner w hw (c.railPoint w hw hc n hn)
      (Line.orientedRailName w (segmentDirection c.segment)).level := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  let q : Cell (Line.span w atoms+2) (Line.height w) :=
    (⟨n,by omega⟩,Line.railRow w)
  refine ⟨(),(Line.railAxis w atoms (segmentDirection c.segment)).geometry.cells q,?_,?_,?_⟩
  · apply (Line.railAxis w atoms (segmentDirection c.segment)).geometry.interior
    refine ⟨hn0,by change n+1 < Line.span w atoms+2; omega,?_,?_⟩
    · change 0 < FiniteTools.radius w
      unfold FiniteTools.radius
      omega
    · change FiniteTools.radius w+1 < Line.height w
      unfold Line.height FiniteTools.side FiniteTools.radius
      omega
  · exact (Line.rotation_rail w atoms (segmentDirection c.segment) q).symm
  · have htag := Line.orientedRailChart_row_tag w hw atoms (Line.program_nonempty _ _ _) c.above
      (segmentDirection c.segment) q rfl
    have hl := congrArg AxisTrack.level htag
    simp only [AxisTrack.level_shift] at hl
    exact hl.symm.le

end LineCode

namespace TurnCode

/-- Both normal phase slots lie strictly inside the literal seven-cell turn stencil. -/
private theorem slot_owner (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing)
    (phase : Bool) (i : Fin 2) :
    (PrimitiveCode.turn c).Owner w hw (c.slot w phase i)
      (Line.orientedRailName w (if i = 0 then c.incoming else c.outgoing)).level := by
  refine ⟨(),(Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells (Turn.stencilSlot phase i),?_,?_,?_⟩
  · apply (Turn.orientationAxis 7 c.incoming c.outgoing).geometry.interior
    have hp := Bool.toNat_le phase
    fin_cases i <;> dsimp [Turn.stencilSlot,Interior] <;> omega
  · change (Turn.stencilEmbedding w).cells
      ((Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells (Turn.stencilSlot phase i)) = _
    rw [←Turn.orientation_stencil,Turn.stencilSlot_cell]
    rfl
  · change (Line.orientedRailName w (if i = 0 then c.incoming else c.outgoing)).level ≤
      ((Turn.orientationAxis 7 c.incoming c.outgoing).name
        ((GuardStencils.cornerClassifier (3 : Fin 7) (3 : Fin 7)).name
          ((Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells.symm
            ((Turn.orientationAxis 7 c.incoming c.outgoing).geometry.cells (Turn.stencilSlot phase i))))).level
    rw [Equiv.symm_apply_apply,Turn.stencilSlot_tag]
    cases hd : c.incoming <;> cases he : c.outgoing <;> fin_cases i <;>
      simp [hd,he,Perpendicular,rightTurn,Direction.opposite] at hc <;>
      simp [Line.orientedRailName,AxisTrack.level,Turn.orientationAxis,Turn.quarterAxis,rightTurn,
        AxisIsometry.trans,AxisIsometry.refl,AxisIsometry.reflectY,AxisIsometry.reflectX,
        AxisIsometry.clockwise,AxisIsometry.transpose]

def outerSlot (w : ℕ) (c : TurnCode) (incoming : Bool) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (Turn.orientation w c.incoming c.outgoing).cells
    ((Turn.stencilEmbedding w).cells (if incoming then ((0,3) : Cell 7 7) else (3,6)))

def outerWorld (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (incoming : Bool) : ℕ × ℕ :=
  (PrimitiveCode.turn c).world w hw (c.outerSlot w incoming)

set_option maxRecDepth 65536 in
private theorem outerWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing)
    (incoming : Bool) : c.outerWorld w hw incoming =
      Line.along w (if incoming then c.incoming.opposite else c.outgoing) c.corner 3 := by
  have hr := Turn.orientation_coordinates w c.incoming c.outgoing
    ((Turn.stencilEmbedding w).cells (if incoming then ((0,3) : Cell 7 7) else (3,6)))
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only [coordinates] at hx hy
  change (Turn.offsetX w c.corner+((Turn.orientation w c.incoming c.outgoing).cells
      ((Turn.stencilEmbedding w).cells (if incoming then ((0,3) : Cell 7 7) else (3,6)))).1.val,
    Turn.offsetY w c.corner+((Turn.orientation w c.incoming c.outgoing).cells
      ((Turn.stencilEmbedding w).cells (if incoming then ((0,3) : Cell 7 7) else (3,6)))).2.val) = _
  rw [hx,hy]
  cases incoming <;> cases hd : c.incoming <;> cases he : c.outgoing <;>
    simp [hd,he,Perpendicular,rightTurn,Direction.opposite] at hc <;>
    dsimp [Turn.quarterCoordinates,Turn.stencilEmbedding,GridEmbedding.translate,coordinates,
      rightTurn,Turn.offsetX,Turn.offsetY,Line.along,Direction.opposite] <;>
    apply Prod.ext <;> simp only [FiniteTools.side,FiniteTools.radius,padding] <;> omega

end TurnCode

def WorldOwner (w : ℕ) (hw : 2 ≤ w) (codes : List PrimitiveCode) (a : ℕ × ℕ) (level : ℕ) : Prop :=
  ∃ c ∈ codes, ∃ p, c.world w hw p = a ∧ c.Owner w hw p level

theorem JunctionContract.incoming_line_exit_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) (codes : List PrimitiveCode) (ht : .turn t ∈ codes) :
    WorldOwner w hw codes (c.lastWorld w hw true) (Line.orientedRailName w (segmentDirection c.segment)).level := by
  refine ⟨.turn t,ht,t.slot w true 0,?_,?_⟩
  · exact (H.incoming_shared_phase w hw c t d true).symm
  · rw [H.incoming_direction]
    exact t.slot_owner w hw H.perpendicular true 0

theorem JunctionContract.outgoing_line_exit_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) (codes : List PrimitiveCode) (ht : .turn t ∈ codes) :
    WorldOwner w hw codes (d.firstWorld w hw false) (Line.orientedRailName w (segmentDirection d.segment)).level := by
  refine ⟨.turn t,ht,t.slot w false 1,?_,?_⟩
  · exact (H.outgoing_shared_phase w hw c t d false).symm
  · rw [H.outgoing_direction]
    exact t.slot_owner w hw H.perpendicular false 1

theorem JunctionContract.incoming_turn_exit_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) (codes : List PrimitiveCode) (hc : .line c ∈ codes) :
    WorldOwner w hw codes (t.outerWorld w hw true) (Line.orientedRailName w t.incoming).level := by
  have hn0 : 0 < segmentLength c.segment-1 := by have h := H.incoming_good.2.1; omega
  have hn : segmentLength c.segment-1 ≤ segmentLength c.segment := by omega
  refine ⟨.line c,hc,c.railPoint w hw H.incoming_good _ hn,?_,?_⟩
  · rw [LineCode.railPoint_world,TurnCode.outerWorld_eq w hw t H.perpendicular true,H.incoming_direction]
    have ht := segment_travels c.segment H.incoming_good.1
    rw [H.incoming_direction,H.incoming_finish] at ht
    have hl := H.incoming_good.2.1
    cases hd : t.incoming <;> simp only [hd] at ht ⊢ <;>
      dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
      apply Prod.ext <;> unfold padding <;> omega
  · rw [←H.incoming_direction]
    exact c.railPoint_owner w hw H.incoming_good _ hn0 hn

theorem JunctionContract.outgoing_turn_exit_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) (codes : List PrimitiveCode) (hd : .line d ∈ codes) :
    WorldOwner w hw codes (t.outerWorld w hw false) (Line.orientedRailName w t.outgoing).level := by
  have hn : 2 ≤ segmentLength d.segment := by have h := H.outgoing_good.2.1; omega
  refine ⟨.line d,hd,d.railPoint w hw H.outgoing_good 2 hn,?_,?_⟩
  · rw [LineCode.railPoint_world,TurnCode.outerWorld_eq w hw t H.perpendicular false,H.outgoing_direction,H.outgoing_start]
    have ht := segment_travels d.segment H.outgoing_good.1
    rw [H.outgoing_direction,H.outgoing_start] at ht
    have hl := H.outgoing_good.2.1
    exact outgoing_along_ray w _ t.outgoing d.segment.finish t.corner ht (by omega) 2 (by omega)
  · rw [←H.outgoing_direction]
    exact d.railPoint_owner w hw H.outgoing_good 2 (by decide) hn

theorem CollinearContract.first_exit_owner (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (H : CollinearContract w c d) (codes : List PrimitiveCode) (hc : .line c ∈ codes) :
    WorldOwner w hw codes (d.firstWorld w hw false) (Line.orientedRailName w (segmentDirection d.segment)).level := by
  have hn0 : 0 < segmentLength c.segment := by have h := H.first_good.2.1; omega
  refine ⟨.line c,hc,c.railPoint w hw H.first_good _ (le_refl _),?_,?_⟩
  · rw [LineCode.railPoint_world,LineCode.firstWorld_eq w hw d H.next_good,←H.directions,←H.joined]
    simpa only [Bool.toNat_false,Nat.add_zero] using along_finish w _ c.segment.start c.segment.finish
      (segmentLength c.segment) false (segment_travels c.segment H.first_good.1)
  · rw [←H.directions]
    exact c.railPoint_owner w hw H.first_good _ hn0 (le_refl _)

theorem CollinearContract.last_exit_owner (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (H : CollinearContract w c d) (codes : List PrimitiveCode) (hd : .line d ∈ codes) :
    WorldOwner w hw codes (c.lastWorld w hw true) (Line.orientedRailName w (segmentDirection c.segment)).level := by
  have hn : 1 ≤ segmentLength d.segment := by have h := H.next_good.2.1; omega
  refine ⟨.line d,hd,d.railPoint w hw H.next_good 1 hn,?_,?_⟩
  · rw [LineCode.railPoint_world,LineCode.lastWorld_eq w hw c H.first_good,H.directions,H.joined]
    rfl
  · rw [H.directions]
    exact d.railPoint_owner w hw H.next_good 1 (by decide) hn

end PushPuzzle.PushS.FiniteRouting
