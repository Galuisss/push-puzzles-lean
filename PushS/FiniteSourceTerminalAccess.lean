/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePortShoulderAccess
public import PushS.FiniteRoutingOuterLanes

/-! Every actual terminal program dock has a complete player-zero access walk, including consuming one-step seams. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

private def boundaryLane (incoming north : Bool) : Cell (Line.width w s.atoms) (Line.height w) :=
  Line.outerCell w s.atoms north ⟨FiniteTools.radius w+Line.span w s.atoms+incoming.toNat,by
    have h := Bool.toNat_le incoming
    unfold Line.width FiniteTools.radius
    omega⟩

private theorem boundaryLane_coordinates (face : Direction) (incoming north : Bool)
    (hd : segmentDirection s.code.segment = face)
    (he : s.code.segment.finish = FiniteRouting.advance face.opposite (boundaryPoint w face) incoming.toNat) :
    coordinates (s.actualEmbedding.cells (s.boundaryLane incoming north)) =
      macroShift w ((codes w v).get s.index).1 (shoulder w face north) := by
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have hin := Bool.toNat_le incoming
  have hslot : (Line.rotation w s.atoms (segmentDirection s.code.segment)).cells (s.boundaryLane incoming north) =
      s.code.laneSlot w hw s.good north (segmentLength s.code.segment+incoming.toNat) (by omega) := by
    congr 1
    apply Prod.ext
    · apply Fin.ext
      change FiniteTools.radius w+Line.span w s.atoms+incoming.toNat = FiniteTools.radius w+(segmentLength s.code.segment+incoming.toNat)
      rw [hspan]
      omega
    · rfl
  rw [s.actual_cell_coordinates,hslot]
  change macroShift w ((codes w v).get s.index).1 (s.code.laneWorld w hw s.good north _ _) = _
  rw [LineCode.laneWorld_eq,Line.outerAlong_finish_add w _ s.code.segment.start s.code.segment.finish _
    (segment_travels _ s.good.1) north incoming.toNat,hd,he,Line.outerAlong_boundary]
  rfl

private theorem boundaryLane_false (north : Bool) : s.boundaryLane false north = s.endLane north := by
  apply Prod.ext <;> apply Fin.ext <;> simp [boundaryLane,endLane,Line.outerCell]

private theorem boundaryLane_true_adjacent (north : Bool) :
    Adjacent (s.actualEmbedding.direction .east) (s.actualEmbedding.cells (s.endLane north))
      (s.actualEmbedding.cells (s.boundaryLane true north)) := by
  apply s.actualEmbedding.adjacent .east
  exact ⟨rfl,rfl⟩

private theorem normal_terminal_end_access (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (face : Direction) (incoming north : Bool)
    (hd : segmentDirection s.code.segment = face)
    (he : s.code.segment.finish = FiniteRouting.advance face.opposite (boundaryPoint w face) incoming.toNat) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (s.endLane north))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (s.endLane north)))
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have hb := code_position_bounds w v _ _ s.code_mem
  have hq := s.boundaryLane_coordinates face incoming north hd he
  have hacc := port_shoulder_access w hw v hP hT phase _ hb face north _ hq
  cases incoming
  · simpa only [s.boundaryLane_false] using hacc
  · have ha := admissible w hw v hP hT
    have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
    have hpos : 1 ≤ Line.span w s.atoms := by have h := s.good.2.1; omega
    let x : Fin (Line.width w s.atoms) := ⟨FiniteTools.radius w+Line.span w s.atoms,by unfold Line.width; omega⟩
    have hfree := s.normal_outer_free phase north x (by dsimp [x]; omega) (le_refl _)
    have hfree' := port_shoulder_free w hw v phase _ face north _ hq
    have hadj := s.boundaryLane_true_adjacent north
    have hs := normal_profile_step w hw v ha phase _ _ _ hadj hfree hfree'
    have hs' := normal_profile_step w hw v ha phase _ _ _ hadj.reverse hfree' hfree
    exact ⟨hacc.1.trans hs',hs.trans hacc.2⟩

theorem normal_terminal_dock_access (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (face : Direction) (incoming : Bool)
    (hd : segmentDirection s.code.segment = face)
    (he : s.code.segment.finish = FiniteRouting.advance face.opposite (boundaryPoint w face) incoming.toNat) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerHub w s.atoms))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerHub w s.atoms)))
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have ha := admissible w hw v hP hT
  have hend := s.normal_terminal_end_access hP hT phase face incoming true hd he
  have hspan : Line.span w s.atoms = segmentLength s.code.segment := Line.program_span_of_bound w _ _ s.good.2.1
  have hpos : 1 ≤ Line.span w s.atoms := by have h := s.good.2.1; omega
  let x : Fin (Line.width w s.atoms) := ⟨FiniteTools.radius w+Line.span w s.atoms,by unfold Line.width; omega⟩
  have hwalk := s.normal_outer_walk ha phase true (Line.outerHubX w s.atoms) x
    (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega) (by dsimp [x]; omega) (le_refl _)
  have hback := s.normal_outer_walk ha phase true x (Line.outerHubX w s.atoms)
    (by dsimp [x]; omega) (le_refl _) (by dsimp [Line.outerHubX]; omega) (by dsimp [Line.outerHubX]; omega)
  exact ⟨hend.1.trans hback,hwalk.trans hend.2⟩

end PushPuzzle.PushS.FiniteSourceInventory.LineSite
