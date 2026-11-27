/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalMarkedInventory
public import PushFS.Reduction.FullGateRawCanonical
public import PushFS.Gadgets.Wires.Catalog.PhaseMarks

/-! The actual full source and goal inventories depend only on their selected source orientation. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


namespace PhysicalTiles

open Plan Gadgets.Wires
set_option maxRecDepth 65536

private theorem rephase_marked_source (c : Payload) (a b d : List Bool) (offset p : ℕ×ℕ) :
    MarkedAt false (rephase c a b) offset p ↔MarkedAt false (rephase c a d) offset p := by
  rcases c with ⟨v,g⟩|⟨e,k,s,t⟩
  · have hw := GateTileRouting.full_initial_retarget g (gateSignals (v.ports,a))
      (gateSignals (v.ports,b)) (gateSignals (v.ports,d))
    change (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle (GateTileRouting.withFlags g
      (gateSignals (v.ports,a)) (gateSignals (v.ports,b)))).initial.boxes ∧(offset.1+q.1.val,offset.2+q.2.val)=p)↔
      (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle (GateTileRouting.withFlags g
      (gateSignals (v.ports,a)) (gateSignals (v.ports,d)))).initial.boxes ∧(offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset GateTileRouting.C=>q∈xs) hw)) Iff.rfl
  · have hw := Catalog.initial_retarget k (!(a.getD e false)) (!(b.getD e false)) (!(d.getD e false))
    change (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(a.getD e false)) (!(b.getD e false))).initial.boxes ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)↔
        (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(a.getD e false)) (!(d.getD e false))).initial.boxes ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset Catalog.Cell=>q∈xs) hw)) Iff.rfl

private theorem rephase_marked_goals (c : Payload) (a d b : List Bool) (offset p : ℕ×ℕ) :
    MarkedAt true (rephase c a b) offset p ↔MarkedAt true (rephase c d b) offset p := by
  rcases c with ⟨v,g⟩|⟨e,k,s,t⟩
  · have hw := GateTileRouting.full_goals_reinitial g (gateSignals (v.ports,a))
      (gateSignals (v.ports,d)) (gateSignals (v.ports,b))
    change (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle (GateTileRouting.withFlags g
      (gateSignals (v.ports,a)) (gateSignals (v.ports,b)))).board.goals ∧(offset.1+q.1.val,offset.2+q.2.val)=p)↔
      (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle (GateTileRouting.withFlags g
      (gateSignals (v.ports,d)) (gateSignals (v.ports,b)))).board.goals ∧(offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset GateTileRouting.C=>q∈xs) hw)) Iff.rfl
  · have hw := Catalog.goals_reinitial k (!(a.getD e false)) (!(d.getD e false)) (!(b.getD e false))
    change (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(a.getD e false)) (!(b.getD e false))).board.goals ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)↔
        (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(d.getD e false)) (!(b.getD e false))).board.goals ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset Catalog.Cell=>q∈xs) hw)) Iff.rfl

private theorem rephase_marked_canonical (c : Payload) (a b : List Bool) (offset p : ℕ×ℕ) :
    MarkedAt true (rephase c a b) offset p ↔MarkedAt false (rephase c b b) offset p := by
  rcases c with ⟨v,g⟩|⟨e,k,s,t⟩
  · have hw := GateTileRouting.full_goals_canonical g (gateSignals (v.ports,a)) (gateSignals (v.ports,b))
    change (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle (GateTileRouting.withFlags g
      (gateSignals (v.ports,a)) (gateSignals (v.ports,b)))).board.goals ∧(offset.1+q.1.val,offset.2+q.2.val)=p)↔
      (∃q : GateTileRouting.C,q∈(GateTileRouting.fullPuzzle (GateTileRouting.withFlags g
      (gateSignals (v.ports,b)) (gateSignals (v.ports,b)))).initial.boxes ∧(offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset GateTileRouting.C=>q∈xs) hw)) Iff.rfl
  · have hw := Catalog.goals_canonical k (!(a.getD e false)) (!(b.getD e false))
    change (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(a.getD e false)) (!(b.getD e false))).board.goals ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)↔
        (∃q : Catalog.Cell,q∈(Catalog.puzzle k (!(b.getD e false)) (!(b.getD e false))).initial.boxes ∧
      (offset.1+q.1.val,offset.2+q.2.val)=p)
    exact exists_congr fun q=>and_congr (Eq.to_iff (congrArg (fun xs : Finset Catalog.Cell=>q∈xs) hw)) Iff.rfl

private theorem rephase_marked_same (c : Payload) (goal : Bool) (a b d e : List Bool)
    (he : (if goal then b else a)=(if goal then e else d)) (offset p : ℕ×ℕ) :
    MarkedAt goal (rephase c a b) offset p ↔MarkedAt goal (rephase c d e) offset p := by
  cases goal
  · change a=d at he
    subst d
    exact rephase_marked_source c a b e offset p
  · change b=e at he
    subst e
    exact rephase_marked_goals c a d b offset p

end PhysicalTiles

namespace PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

private theorem marks_subset (goal : Bool) (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (a b : List Bool) (he : PhysicalTiles.bits v goal=(if goal then b else a))
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hp : p∈marks goal v hP hT) : p∈marks goal (v.1,(a,b)) hP hT := by
  obtain ⟨i,hi⟩ := (marked_membership goal v hP hT p).mp hp
  have hold : PhysicalTiles.MarkedAt goal (PhysicalTiles.rephase (payload v i) v.2.1 v.2.2)
      (PhysicalTiles.offset (position (v := v) i) (tile (v := v) i)) (p.1.val,p.2.val) := by
    rw [rephase_payload_self v i]
    exact hi
  have hnew := (PhysicalTiles.rephase_marked_same (payload v i) goal v.2.1 v.2.2 a b he
    (PhysicalTiles.offset (position (v := v) i) (tile (v := v) i)) (p.1.val,p.2.val)).mp hold
  apply (marked_membership goal (v.1,(a,b)) hP hT p).mpr
  refine ⟨rephaseIndex v a b i,?_⟩
  rw [rephaseIndex_offset v a b i]
  exact hnew

/-- Source boxes and goals each depend only on their own selected orientation list. -/
theorem marks_eq (goal : Bool) (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (a b : List Bool) (he : PhysicalTiles.bits v goal=(if goal then b else a)) :
    marks goal v hP hT=marks goal (v.1,(a,b)) hP hT := by
  apply Finset.ext
  intro p
  have he' : PhysicalTiles.bits (v.1,(a,b)) goal=(if goal then v.2.2 else v.2.1) := by
    simpa only [PhysicalTiles.bits] using he.symm
  exact ⟨marks_subset goal v hP hT a b he p,
    marks_subset goal (v.1,(a,b)) hP hT v.2.1 v.2.2 he' p⟩

private theorem diagonal_marks (w : Word) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (a : List Bool) :
    marks true (w,(a,a)) hP hT=marks false (w,(a,a)) hP hT := by
  apply Finset.ext
  intro p
  rw [marked_membership,marked_membership]
  apply exists_congr
  intro i
  have hh := PhysicalTiles.rephase_marked_canonical (payload (w,(a,a)) i) a a
    (PhysicalTiles.offset (position (v := (w,(a,a))) i) (tile (v := (w,(a,a))) i)) (p.1.val,p.2.val)
  simpa only [rephase_payload_self (w,(a,a)) i] using hh

/-- The target source orientation has exactly the original complete physical goal set. -/
theorem canonical_final_boxes (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    (canonical v hP hT v.2.2).boxes=(atlas v hP hT).board.goals := by
  calc
    (canonical v hP hT v.2.2).boxes=marks false (v.1,(v.2.2,v.2.2)) hP hT := rfl
    _=marks true (v.1,(v.2.2,v.2.2)) hP hT := (diagonal_marks v.1 hP hT v.2.2).symm
    _=marks true v hP hT := (marks_eq true v hP hT v.2.2 v.2.2 rfl).symm
    _=(atlas v hP hT).board.goals := rfl

end PhysicalInventory
end PushPuzzle.PushFS.Reduction
