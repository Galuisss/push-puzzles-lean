/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineAction

/-! Ordinary stock executes on the actual trimmed action footprint. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Action.Stock

open PushFS Line.Stock
variable {last : Bool}
attribute [local irreducible] width height

private theorem frame (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) :
    (line w pre post n above).Frame (macroBoard (last:=last) w (pre++ .line n::post) above)
      (fixed w hw pre post n) := by
  have F := Line.Stock.frame w hw pre post n hn above ha
  refine ⟨?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro p hp
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
    exact (FiniteWireFrame.floor_iff _ _ _).mpr (Action.cutCell_active w hw (ownedCount w pre+1) _ above l)
  · intro x hx
    apply lift_free w _ above _ _ (F.track_free x hx)
    apply Or.inr; apply Or.inl
    dsimp [line,FiniteLineMacros.Line.track] at hx
    simp only [span_append,span_cons,Atom.span]
    omega
  · intro x hx
    apply lift_free w _ above _ _ (F.lane_free x hx)
    apply Or.inr; apply Or.inl
    dsimp [line,FiniteLineMacros.Line.laneSegment] at hx
    simp only [span_append,span_cons,Atom.span]
    omega

private theorem high_to_low (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩ := by
  have hr := (frame (last:=last) w hw pre post n hn above ha).forward
  have hzero := inventory w hw pre post n hn above 0 (by omega)
  have hfull := inventory w hw pre post n hn above (n-1) (by omega)
  simp only [Nat.add_zero] at hzero
  have he : ownedCount w pre+1+(n-1) = ownedCount w pre+n := by omega
  rw [he] at hfull
  change Reachable _ _ ⟨_, (line w pre post n above).boxes _ 0⟩
    ⟨_, (line w pre post n above).boxes _ (n-1)⟩ at hr
  rw [← hzero, ← hfull] at hr
  exact hr

private theorem low_to_high (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩ := by
  have hr := (frame (last:=last) w hw pre post n hn above ha).backward
  have hzero := inventory w hw pre post n hn above 0 (by omega)
  have hfull := inventory w hw pre post n hn above (n-1) (by omega)
  simp only [Nat.add_zero] at hzero
  have he : ownedCount w pre+1+(n-1) = ownedCount w pre+n := by omega
  rw [he] at hfull
  change Reachable _ _ ⟨_, (line w pre post n above).boxes _ (n-1)⟩
    ⟨_, (line w pre post n above).boxes _ 0⟩ at hr
  rw [← hzero, ← hfull] at hr
  exact hr


private theorem hub_free (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) (cut : ℕ) (y : Fin (height w))
    (hy : min (lane w above pre).val (laneY w (!(exitSide above pre))).val ≤ y.val)
    (hy' : y.val ≤ max (lane w above pre).val (laneY w (!(exitSide above pre))).val) :
    Free (macroBoard (last:=last) w (pre++ .line n::post) above) (cutBoxes w hw cut (pre++ .line n::post))
      ((line w pre post n above).hub,y) := by
  apply lift_free w _ above _ _ (Line.Stock.hub_free w hw pre post n hn above ha cut y hy hy')
  apply Or.inr; apply Or.inl
  dsimp [line]
  simp only [span_append,span_cons,Atom.span]
  omega

private theorem hub_to_outer (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) (cut : ℕ) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨outerCell w _ (!(exitSide above pre)) (line w pre post n above).hub, cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw cut _ above)
  exact hub_free w hw pre post n hn above ha cut

private theorem outer_to_hub (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) (cut : ℕ) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨outerCell w _ (!(exitSide above pre)) (line w pre post n above).hub, cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw cut _ above)
  intro y hy hy'
  exact hub_free w hw pre post n hn above ha cut y (by simpa only [min_comm, line] using hy)
    (by simpa only [max_comm, line] using hy')

private theorem hub_reachable (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) (cut : ℕ) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  have hs : 1 ≤ span w (pre++ .line n::post) := by simp only [span_append,span_cons,Atom.span]; omega
  apply (outer_macro_connected_of_flip w hw cut _ hflip above true (!(exitSide above pre))
    (outerHubX w _) (line w pre post n above).hub (by dsimp [outerHubX]; omega)
    (by dsimp [outerHubX]; omega) (by dsimp [line]; omega)
    (by dsimp [line]; simp only [span_append, span_cons, Atom.span]; omega)).trans
  exact outer_to_hub w hw pre post n hn above ha cut

private theorem hub_return (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) (cut : ℕ) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨outerHub w _, cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  have hs : 1 ≤ span w (pre++ .line n::post) := by simp only [span_append,span_cons,Atom.span]; omega
  apply (hub_to_outer w hw pre post n hn above ha cut).trans
  exact outer_macro_connected_of_flip w hw cut _ hflip above (!(exitSide above pre)) true
    (line w pre post n above).hub (outerHubX w _) (by dsimp [line]; omega)
    (by dsimp [line]; simp only [span_append, span_cons, Atom.span]; omega)
    (by dsimp [outerHubX]; omega) (by dsimp [outerHubX]; omega)

theorem sweep_low_high (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩ :=
  (hub_reachable w hw pre post n hn above ha hflip _).trans
    ((low_to_high w hw pre post n hn above ha).trans (hub_return w hw pre post n hn above ha hflip _))

theorem sweep_high_low (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) :
    Reachable (macroBoard (last:=last) w (pre++ .line n::post) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩ :=
  (hub_reachable w hw pre post n hn above ha hflip _).trans
    ((high_to_low w hw pre post n hn above ha).trans (hub_return w hw pre post n hn above ha hflip _))

end PushPuzzle.PushS.FiniteRouting.Line.Action.Stock
