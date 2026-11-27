/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.SourceRails

/-! Real physical source order across a shared source SCC supplies each directional seam gap. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness

def TravelHigh (d : Direction) (threshold p : ℕ×ℕ) : Prop :=
  match d with
  | .east=>threshold.1≤p.1
  | .west=>p.1≤threshold.1
  | .south=>threshold.2≤p.2
  | .north=>p.2≤threshold.2

def DirectionalStep (d : Direction) (p q : ℕ×ℕ) : Prop :=
  match d with
  | .east=>p.1+2=q.1
  | .west=>q.1+2=p.1
  | .south=>p.2+2=q.2
  | .north=>q.2+2=p.2

instance (d : Direction) (p q : ℕ×ℕ) : Decidable (DirectionalStep d p q) := by
  unfold DirectionalStep
  split <;> infer_instance

def DirectionalOrder (d : Direction) (p q : ℕ×ℕ) : Prop :=
  match d with
  | .east=>p.1<q.1
  | .west=>q.1<p.1
  | .south=>p.2<q.2
  | .north=>q.2<p.2

def DirectionalGap (d : Direction) (p q : ℕ×ℕ) : Prop :=
  match d with
  | .east=>p.1+2≤q.1
  | .west=>q.1+2≤p.1
  | .south=>p.2+2≤q.2
  | .north=>q.2+2≤p.2

instance (d : Direction) (p q : ℕ×ℕ) : Decidable (DirectionalOrder d p q) := by
  unfold DirectionalOrder
  split <;> infer_instance

instance (d : Direction) (p q : ℕ×ℕ) : Decidable (DirectionalGap d p q) := by
  unfold DirectionalGap
  split <;> infer_instance

theorem travelHigh_join (d : Direction) (a b p q : ℕ×ℕ) (hab : DirectionalStep d a b)
    (hpq : DirectionalGap d p q) (hp : TravelHigh d a p) : TravelHigh d b q := by
  cases d <;> dsimp only [DirectionalStep,DirectionalGap,TravelHigh] at * <;> omega

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

private theorem axial_gap (axis forward : Bool) {S T : LabelledState L I.width I.height}
    (hs : Successful M S T) (cert : Certificate I) (i j : L)
    (hc : component I.board (M.source i)=component I.board (M.source j))
    (horder : if forward then coord axis (M.source i)<coord axis (M.source j)
      else coord axis (M.source j)<coord axis (M.source i)) :
    if forward then coord axis (S.position i)+2≤coord axis (S.position j)
      else coord axis (S.position j)+2≤coord axis (S.position i) := by
  let r : SourceRail M axis (cross axis (M.source i)) := {
    anchor:=i
    witness:=M.source j
    connected:=hc.symm
    different:=by cases forward <;> simp only [Bool.false_eq_true,ite_false,ite_true] at horder <;> omega
    anchor_cross:=rfl }
  cases forward
  · exact r.gap hs cert j i hc.symm rfl horder
  · exact r.gap hs cert i j rfl hc.symm horder

/-- Every actual successful state keeps the full two-cell gap across a literal physical seam. -/
theorem directional_gap (d : Direction) {S T : LabelledState L I.width I.height}
    (hs : Successful M S T) (cert : Certificate I) (i j : L)
    (hc : component I.board (M.source i)=component I.board (M.source j))
    (horder : DirectionalOrder d ((M.source i).1.val,(M.source i).2.val) ((M.source j).1.val,(M.source j).2.val)) :
    DirectionalGap d ((S.position i).1.val,(S.position i).2.val) ((S.position j).1.val,(S.position j).2.val) := by
  cases d
  · exact axial_gap false false hs cert i j hc horder
  · exact axial_gap true true hs cert i j hc horder
  · exact axial_gap false true hs cert i j hc horder
  · exact axial_gap true false hs cert i j hc horder

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
