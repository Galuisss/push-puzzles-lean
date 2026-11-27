/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalSolution
public import PushS.PortInputStep

/-! Complete actual canonical macro simulation of every ordered original axis path. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Ordered original axis paths run between the actual complete canonical frame states on one board. -/
theorem encodedSegments_ordered_axis_path_from_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {initial target : List Bool} (hr : Relation.ReflTransGen l.OrderedAxisStep initial target)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none (l.cornerState p (l.canonical initial)).toState (l.cornerState p (l.canonical target)).toState := by
  induction hr with
  | refl => exact .refl
  | @tail before after hpre hstep ih =>
    obtain ⟨hs, port, hp, rfl, ht⟩ := hstep
    exact ih.trans (l.encodedSegments_canonical_axis_from_frame p hl hM ha before hs.toInputLegal hp
      (!(before.getD port false)) (by simp only [Bool.not_not]) ht B hB)

/-- Any ordered original interface-axis path solves its genuine emitted wall-free storage instance. -/
theorem canonicalInstance_solvable_of_orderedReachable (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {initial target : List Bool} (hr : Relation.ReflTransGen l.OrderedAxisStep initial target) :
    (l.canonicalInstance p hl hM ha initial target).Solvable := by
  apply l.canonicalInstance_solvable_of_frame_reachable p hl hM ha
  exact l.encodedSegments_ordered_axis_path_from_frame p hl hM ha hr _ (l.canonicalInstance p hl hM ha initial target).walls_empty

end PushPuzzle.PushS.PortLayout
