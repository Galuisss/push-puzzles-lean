/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortConstraintLegal
public import PushS.PortInputStep
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Step
import all PushS.PortConstraintGraph
import Mathlib.Data.List.GetD

/-!
# Exact native moves and reachability of the actual port layout

The existing standard finite native configuration map turns the literal single-axis list update
into the same single-edge reversal. Serializing finite orientations by `List.ofFn` returns the
same full-length axis arrays, preserving moves and their reflexive-transitive closures.

## Main results

* `PortLayout.graphData_step_iff`: standard native moves are exactly the actual `AxisStep`.
* `PortLayout.graphData_reachable_iff`: standard native reachability is exactly actual axis paths.
-/

public section

namespace PushPuzzle.PushS.PortLayout

open Cslib.Complexity

private theorem modify_not_set (axes : List Bool) (i : ℕ) :
    axes.modify i Bool.not = axes.set i (!(axes.getD i false)) := by
  simpa only [List.getD_eq_getElem?_getD, Bool.default_bool] using
    List.modify_eq_set Bool.not i axes

private theorem config_set_not (g : NCL.AndOrGraph) (axes : List Bool)
    (hlen : axes.length = g.edgeCount) (e : Fin g.edgeCount) :
    g.config (axes.set e.val (!(axes.getD e.val false))) = NCL.reverse (g.config axes) e := by
  rw [← modify_not_set]
  exact g.config_modify_not axes hlen e

/-- The same complete actual axis arrays have one legal native edge reversal exactly when
they have the existing one-axis interface move. -/
theorem graphData_step_iff (l : PortLayout) (hb : l.graphData.Bounded) (axes next : List Bool)
    (ha : axes.length = l.portCount) (hn : next.length = l.portCount) :
    l.graphData.graph.Step (l.graphData.config axes) (l.graphData.config next) ↔
      l.AxisStep axes next := by
  have ha' : axes.length = l.graphData.edgeCount := ha
  have hn' : next.length = l.graphData.edgeCount := hn
  constructor
  · rintro ⟨hs, ht, e, he⟩
    have hr := config_set_not l.graphData axes ha' e
    have hx : next = axes.set e.val (!(axes.getD e.val false)) := by
      calc
        next = List.ofFn (l.graphData.config next) := (l.graphData.ofFn_config next hn').symm
        _ = List.ofFn (l.graphData.config (axes.set e.val (!(axes.getD e.val false)))) :=
          congrArg List.ofFn (he.trans hr.symm)
        _ = axes.set e.val (!(axes.getD e.val false)) :=
          l.graphData.ofFn_config _ (by simpa only [List.length_set] using ha')
    exact ⟨(l.graphData_legal_iff hb axes ha).mp hs, e.val, e.isLt, hx,
      (l.graphData_legal_iff hb next hn).mp ht⟩
  · rintro ⟨hs, i, hi, rfl, ht⟩
    let e : Fin l.graphData.edgeCount := ⟨i, hi⟩
    exact ⟨(l.graphData_legal_iff hb axes ha).mpr hs,
      (l.graphData_legal_iff hb _ hn).mpr ht, e, config_set_not l.graphData axes ha' e⟩

/-- The standard native finite graph and the same actual complete interface arrays have exactly
the same reflexive-transitive reachability relation. -/
theorem graphData_reachable_iff (l : PortLayout) (hb : l.graphData.Bounded)
    (axes next : List Bool) (ha : axes.length = l.portCount) (hn : next.length = l.portCount) :
    l.graphData.graph.Reachable (l.graphData.config axes) (l.graphData.config next) ↔
      Relation.ReflTransGen l.AxisStep axes next := by
  constructor
  · intro hr
    have hstep (s t : Fin l.graphData.edgeCount → Bool) (h : l.graphData.graph.Step s t) :
        l.AxisStep (List.ofFn s) (List.ofFn t) := by
      apply (l.graphData_step_iff hb _ _ List.length_ofFn List.length_ofFn).mp
      erw [l.graphData.config_ofFn s, l.graphData.config_ofFn t]
      exact h
    have hpath := Relation.ReflTransGen.lift List.ofFn hstep _ _ hr
    change Relation.ReflTransGen l.AxisStep (List.ofFn (l.graphData.config axes))
      (List.ofFn (l.graphData.config next)) at hpath
    erw [l.graphData.ofFn_config axes ha, l.graphData.ofFn_config next hn] at hpath
    exact hpath
  · intro hr
    apply Relation.ReflTransGen.lift l.graphData.config (fun a b hab => ?_) _ _ hr
    obtain ⟨hs, i, hi, he, ht⟩ := hab
    exact (l.graphData_step_iff hb a b hs.axes_length ht.axes_length).mpr ⟨hs, i, hi, he, ht⟩

end PushPuzzle.PushS.PortLayout
