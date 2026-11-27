/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Unlimited
public import PushPushFS.Space.Edge

/-! Polynomial-time checking of unrestricted maximum slides with fixed walls. -/

@[expose] public section
namespace PushPuzzle.PushPushFS.Unlimited.Machine

open PushFS (Direction State Instance)
open PushFS.Machine
open Turing.MultiTapeTM ComputableInPolyTime

/-- The board area bounds every complete box run. -/
def edge (q : Instance × List Bool × List Bool) : Bool :=
  PushPushFS.Machine.edge q.1.area q

@[fun_prop] private theorem labelledEdge_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × List Bool =>
        PushPushFS.Machine.labelledEdge q.1.area q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction) (encPair encBits encBits)))
      encBool := by
  unfold PushPushFS.Machine.labelledEdge
  fun_prop

@[fun_prop] theorem edge_polyTime :
    ComputableInPolyTime edge (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
  unfold edge PushPushFS.Machine.edge
  have hc := State.codeValid_computable
  have hlabel := labelledEdge_polyTime
  have hd : ComputableInPolyTime
      (fun q : Instance × List Bool × List Bool =>
        directions.any fun d => PushPushFS.Machine.labelledEdge q.1.area q.1 d q.2.1 q.2.2)
      (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
    apply anyConst
    intro d _
    exact hlabel.comp (g := fun q : Instance × List Bool × List Bool =>
      (q.1, d, q.2.1, q.2.2)) (by fun_prop)
  fun_prop

theorem edge_correct (I : Instance) (u v : List Bool) :
    edge (I, u, v) = true ↔ ∃ s t : State I.width I.height,
      s.bits = u ∧ t.bits = v ∧ Step I.board s t := by
  rw [edge, PushPushFS.Machine.edge_correct]
  simp only [PushFS.Instance.area, ← step_finite_iff]

end PushPuzzle.PushPushFS.Unlimited.Machine
