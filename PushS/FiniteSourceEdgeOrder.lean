/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceProfile
public import PushS.FiniteSourceEdgeMetadata
public import PushFS.Reduction.PhysicalEdgeOrder
public import PushFS.Reduction.ProfileSweep

/-! The actual source-edge coordinate order for complete physical finite-force inventory updates. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical
open PhysicalInventory (EdgeOrder)
open scoped Classical

attribute [local irreducible] codes Raster.width Raster.height

/-- The real physical edge phase before or after this one source-cell update. -/
def edgeWirePhase {word : Word} (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool) (p : GridRouting.Point) : Bool := if phase p then c e else !(c e)

/-- At the actual current source tile, the predecessor is low and the successor is high. -/
structure TileFrontier (word : Word) (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool) (p : GridRouting.Point) : Prop where
  point : HasPoint (Route.edgeSegments (refinedProgram word,e.val)) p
  fresh : phase p = false
  previous : ∀ q,UnitStep (Route.edgeSegments (refinedProgram word,e.val)) q p → edgeWirePhase c e phase q = false
  next : ∀ q,UnitStep (Route.edgeSegments (refinedProgram word,e.val)) p q → edgeWirePhase c e phase q = true

private theorem node_injective {v : CellPlan.Source} {e : ℕ} (order : EdgeOrder v e) :
    Function.Injective order.sequence.node :=
  order.sequence.injective order.flow.step_left_unique order.flow.no_step_source

private theorem node_covers {v : CellPlan.Source} {e : ℕ} (order : EdgeOrder v e)
    (p : GridRouting.Point) (hp : HasPoint (Route.edgeSegments (refinedProgram v.1,e)) p) :
    ∃ j,order.sequence.node j = p :=
  order.sequence.covers order.flow.step_right_unique order.flow.no_step_target (order.connected.point_unitReach hp)

private theorem node_previous {v : CellPlan.Source} {e : ℕ} (order : EdgeOrder v e)
    (i : Fin (order.sequence.length+1)) (p : GridRouting.Point)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e)) p (order.sequence.node i)) :
    ∃ j,order.sequence.node j = p ∧ j.val+1 = i.val := by
  obtain ⟨j,hj⟩ := node_covers order p h.left_mem
  refine ⟨j,hj,?_⟩
  exact (order.sequence.step_index (node_injective order) order.flow.step_right_unique
    order.flow.no_step_target j i (hj.symm ▸ h)).symm

private theorem node_next {v : CellPlan.Source} {e : ℕ} (order : EdgeOrder v e)
    (i : Fin (order.sequence.length+1)) (p : GridRouting.Point)
    (h : UnitStep (Route.edgeSegments (refinedProgram v.1,e)) (order.sequence.node i) p) :
    ∃ j,order.sequence.node j = p ∧ j.val = i.val+1 := by
  obtain ⟨j,hj⟩ := node_covers order p h.right_mem
  refine ⟨j,hj,?_⟩
  exact order.sequence.step_index (node_injective order) order.flow.step_right_unique
    order.flow.no_step_target i j (hj.symm ▸ h)

/-- A false original edge bit advances its exact physical source path in the forward coordinate order. -/
private theorem edge_forward_frontier (word : Word) (c : Fin word.compile.edgeCount → Bool)
    (e : Fin word.compile.edgeCount) (order : EdgeOrder (oneEdgeSource word c e) e.val) (hc : c e = false)
    (i : Fin (order.sequence.length+1)) :
    TileFrontier word c e (ProfileSweep.stage order.sequence.node (fun _ => false) i.val) (order.sequence.node i) where
  point := order.node_mem i
  fresh := ProfileSweep.node_false _ (node_injective order) _ (fun _ => rfl) _ i (le_refl _)
  previous q hq := by
    obtain ⟨j,hj,hji⟩ := node_previous order i q hq
    unfold edgeWirePhase
    rw [← hj,ProfileSweep.node_true _ (fun _ => false) i.val j (by omega)]
    exact hc
  next q hq := by
    obtain ⟨j,hj,hij⟩ := node_next order i q hq
    unfold edgeWirePhase
    rw [← hj,ProfileSweep.node_false _ (node_injective order) (fun _ => false) (fun _ => rfl) i.val j (by omega)]
    simp [hc]

/-- A true original edge bit advances the same actual source path in reverse coordinate order. -/
private theorem edge_backward_frontier (word : Word) (c : Fin word.compile.edgeCount → Bool)
    (e : Fin word.compile.edgeCount) (order : EdgeOrder (oneEdgeSource word c e) e.val) (hc : c e = true)
    (i : Fin (order.sequence.length+1)) :
    TileFrontier word c e (ProfileSweep.stage (fun j => order.sequence.node j.rev) (fun _ => false) i.val)
      (order.sequence.node i.rev) where
  point := order.node_mem i.rev
  fresh := ProfileSweep.node_false _ ((node_injective order).comp Fin.rev_injective) _ (fun _ => rfl) _ i (le_refl _)
  previous q hq := by
    obtain ⟨j,hj,hji⟩ := node_previous order i.rev q hq
    have hj' : order.sequence.node j.rev.rev = q := by simpa only [Fin.rev_rev] using hj
    have hb : i.val ≤ j.rev.val := by
      have hh := Fin.rev_lt_rev.mpr (show j < i.rev from by omega)
      simpa only [Fin.rev_rev,Fin.le_def] using le_of_lt hh
    unfold edgeWirePhase
    rw [← hj',ProfileSweep.node_false (fun j => order.sequence.node j.rev) ((node_injective order).comp Fin.rev_injective)
      (fun _ => false) (fun _ => rfl) i.val j.rev hb]
    simp [hc]
  next q hq := by
    obtain ⟨j,hj,hij⟩ := node_next order i.rev q hq
    have hj' : order.sequence.node j.rev.rev = q := by simpa only [Fin.rev_rev] using hj
    have hb : j.rev.val < i.val := by
      have hh := Fin.rev_lt_rev.mpr (show i.rev < j from by omega)
      simpa only [Fin.rev_rev,Fin.lt_def] using hh
    unfold edgeWirePhase
    rw [← hj',ProfileSweep.node_true (fun j => order.sequence.node j.rev) (fun _ => false) i.val j.rev hb]
    exact hc

private theorem edge_replay_sequence (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    {n : ℕ} (node : Fin n → GridRouting.Point)
    (hcover : ∀ p,HasPoint (Route.edgeSegments (refinedProgram word,e.val)) p → ∃ j,node j = p)
    (hfrontier : ∀ j,TileFrontier word c e (ProfileSweep.stage node (fun _ => false) j.val) (node j))
    (hupdate : ∀ phase p,TileFrontier word c e phase p →
      Reachable (canonicalBoard w hw word target) (some 1)
        (profileState w hw (oneEdgeSource word c e) phase)
        (profileState w hw (oneEdgeSource word c e) (Function.update phase p true))) :
    Reachable (canonicalBoard w hw word target) (some 1)
      (canonicalState w hw word target (configBits c))
      (canonicalState w hw word target (configBits (reverse c e))) := by
  have hr := ProfileSweep.replay node (fun _ => false) (profileState w hw (oneEdgeSource word c e))
    (canonicalBoard w hw word target) (by
      intro j
      have hj := hupdate _ _ (hfrontier j)
      rw [ProfileSweep.step] at hj
      exact hj)
  have ht := edge_profile_finished w hw word hG hP hT c e
    (ProfileSweep.stage node (fun _ => false) n) (by
      intro p hp
      obtain ⟨j,hj⟩ := hcover p hp
      rw [← hj]
      exact ProfileSweep.node_true node (fun _ => false) n j j.isLt)
  rw [edge_profile_initial_canonical,ht,edge_profile_target_canonical] at hr
  exact hr

/-- Replay the explicit genuine source-path sequence of complete actual tile inventory updates. -/
theorem edge_replay (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] []) (target : List Bool)
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (hupdate : ∀ phase p,TileFrontier word c e phase p →
      Reachable (canonicalBoard w hw word target) (some 1)
        (profileState w hw (oneEdgeSource word c e) phase)
        (profileState w hw (oneEdgeSource word c e) (Function.update phase p true))) :
    Reachable (canonicalBoard w hw word target) (some 1)
      (canonicalState w hw word target (configBits c))
      (canonicalState w hw word target (configBits (reverse c e))) := by
  obtain ⟨order⟩ := PhysicalInventory.edgeOrder_exists (oneEdgeSource word c e) hP hT e
  cases hc : c e with
  | false =>
    exact edge_replay_sequence w hw word hG hP hT target c e order.sequence.node (node_covers order)
      (edge_forward_frontier word c e order hc) hupdate
  | true =>
    apply edge_replay_sequence w hw word hG hP hT target c e (fun j => order.sequence.node j.rev) ?_
      (edge_backward_frontier word c e order hc) hupdate
    intro p hp
    obtain ⟨j,hj⟩ := node_covers order p hp
    exact ⟨j.rev,by simpa only [Fin.rev_rev] using hj⟩

end PushPuzzle.PushS.FiniteSourceInventory
