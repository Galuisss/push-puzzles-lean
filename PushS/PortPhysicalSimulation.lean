/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortPhysicalSoundness
public import PushS.PortPhysicalCompleteness
public import PushS.PortOrderReachability

/-! Exact physical simulation between the original ordered canonical endpoints. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- A genuine canonical wall-free storage instance solves exactly its original legal axis problem. -/
theorem canonicalInstance_solvable_iff_axisReachable (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : List Bool) (hs : l.OrderedInputs initial) (ht : l.OrderedInputs target) :
    (l.canonicalInstance p hl hM ha initial target).Solvable ↔
      Relation.ReflTransGen l.AxisStep initial target :=
  ⟨l.canonicalInstance_solvable_implies_axisReachable p hl hM ha initial target hs.toInputLegal ht.toInputLegal,
    fun hr => l.canonicalInstance_solvable_of_orderedReachable p hl hM ha
      ((l.axisReachable_iff_orderedReachable hl.lower initial target hs ht).mp hr)⟩

end PushPuzzle.PushS.PortLayout
