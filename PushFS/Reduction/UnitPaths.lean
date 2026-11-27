/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CompleteFlow

/-! Finite directed unit paths of every actual emitted source edge. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction

open Cslib.Complexity.NCL

def UnitStep (ss : List Segment) (p q : GridRouting.Point) : Prop :=
  ∃d,HasArc ss d p ∧neighbor d p=some q

abbrev UnitReach (ss : List Segment) := Relation.ReflTransGen (UnitStep ss)

theorem UnitReach.mono {ss tt : List Segment} {p q : GridRouting.Point}
    (hr : UnitReach ss p q) (hm : ∀s∈ss,s∈tt) : UnitReach tt p q := by
  induction hr with
  | refl=>exact .refl
  | tail _ hs ih=>
    obtain ⟨d,⟨s,hs,ha⟩,hn⟩:=hs
    exact ih.tail ⟨d,⟨s,hm s hs,ha⟩,hn⟩

private theorem horizontal_unitReach (ss : List Segment) (x x' y : ℕ)
    (hm : Segment.mk (x,y) (x',y)∈ss) : UnitReach ss (x,y) (x',y) := by
  by_cases hx : x≤x'
  · have hr : ∀t,t≤x'-x→UnitReach ss (x,y) (x+t,y) := by
      intro t
      induction t with
      | zero=>intro _; exact .refl
      | succ t ih=>
        intro ht
        refine (ih (by omega)).tail ⟨.east,⟨⟨(x,y),(x',y)⟩,hm,?_,⟩,rfl⟩
        change y=y ∧y=y ∧x≤x+t ∧x+t<x'
        exact ⟨rfl,rfl,by omega,by omega⟩
    have he : x+(x'-x)=x':=by omega
    simpa only [he] using hr (x'-x) (le_refl _)
  · have hr : ∀t,t≤x-x'→UnitReach ss (x,y) (x-t,y) := by
      intro t
      induction t with
      | zero=>intro _; exact .refl
      | succ t ih=>
        intro ht
        refine (ih (by omega)).tail ⟨.west,⟨⟨(x,y),(x',y)⟩,hm,?_,⟩,?_⟩
        · change y=y ∧y=y ∧x'<x-t ∧x-t≤x
          exact ⟨rfl,rfl,by omega,by omega⟩
        · change (if x-t=0 then none else some (x-t-1,y))=some (x-(t+1),y)
          rw [ite_eq_right (show x-t≠0 by omega)]
          exact congrArg some (Prod.ext (by omega) rfl)
    have he : x-(x-x')=x':=by omega
    simpa only [he] using hr (x-x') (le_refl _)

private theorem vertical_unitReach (ss : List Segment) (x y y' : ℕ) (hy : y≤y')
    (hm : Segment.mk (x,y) (x,y')∈ss) : UnitReach ss (x,y) (x,y') := by
  have hr : ∀t,t≤y'-y→UnitReach ss (x,y) (x,y+t) := by
    intro t
    induction t with
    | zero=>intro _; exact .refl
    | succ t ih=>
      intro ht
      refine (ih (by omega)).tail ⟨.south,⟨⟨(x,y),(x,y')⟩,hm,?_,⟩,rfl⟩
      change x=x ∧x=x ∧y≤y+t ∧y+t<y'
      exact ⟨rfl,rfl,by omega,by omega⟩
  have he : y+(y'-y)=y':=by omega
  simpa only [he] using hr (y'-y) (le_refl _)

theorem path_unitReach {p q : GridRouting.Point} (r : GridRouting.Path p q) : UnitReach (segments r) p q := by
  induction r with
  | horizontal x x' y=>exact horizontal_unitReach _ x x' y (List.mem_singleton_self _)
  | vertical x y y' hy=>exact vertical_unitReach _ x y y' hy (List.mem_singleton_self _)
  | comp r s ih ih'=>
    exact (UnitReach.mono ih (fun _ hm=>List.mem_append_left _ hm)).trans
      (UnitReach.mono ih' (fun _ hm=>List.mem_append_right _ hm))

theorem Connects.unitReach {ss : List Segment} {p q : GridRouting.Point} (hc : Connects ss p q) : UnitReach ss p q := by
  obtain ⟨r,rfl⟩:=hc
  exact path_unitReach r

def refinedPath {p q : GridRouting.Point} : GridRouting.Path p q→GridRouting.Path (refinePoint p) (refinePoint q)
  | .horizontal x x' y=>.horizontal (16*x+32) (16*x'+32) (16*y+32)
  | .vertical x y y' hy=>.vertical (16*x+32) (16*y+32) (16*y'+32) (by omega)
  | .comp r s=>(refinedPath r).comp (refinedPath s)

private theorem refinedPath_segments {p q : GridRouting.Point} (r : GridRouting.Path p q) :
    segments (refinedPath r)=(segments r).map Segment.refined := by
  induction r with
  | horizontal=>rfl
  | vertical=>rfl
  | comp _ _ ih ih'=>simp only [refinedPath,segments,List.map_append,ih,ih']

theorem Connects.refined {ss : List Segment} {p q : GridRouting.Point} (hc : Connects ss p q) :
    Connects (ss.map Segment.refined) (refinePoint p) (refinePoint q) := by
  obtain ⟨r,rfl⟩:=hc
  exact ⟨refinedPath r,refinedPath_segments r⟩

namespace Plan

theorem complete_unitPath {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] []) (e : Fin w.compile.edgeCount) :
    ∃p q,OutputEndpoint w ⟨[],0,[]⟩ 0 e.val p ∧InputEndpoint w ⟨[],0,[]⟩ 0 e.val q ∧
      UnitFlow (Route.edgeSegments (refinedProgram w,e.val)) (refinePoint p) (refinePoint q) ∧
      UnitReach (Route.edgeSegments (refinedProgram w,e.val)) (refinePoint p) (refinePoint q) := by
  obtain ⟨p,q,hp,hq,hconn,hflow⟩:=complete_flow hP hT e
  refine ⟨p,q,hp,hq,?_,?_⟩
  · rw [refinedProgram,Route.edgeSegments_refined]
    exact hflow.refined
  · rw [refinedProgram,Route.edgeSegments_refined]
    exact hconn.refined.unitReach

end Plan
end PushPuzzle.PushFS.Reduction
