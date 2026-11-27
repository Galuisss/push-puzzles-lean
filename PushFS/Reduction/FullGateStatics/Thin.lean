/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Boundary

/-! Every long straight chart has just two active boundary endpoints under all real D4 orientations. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Gadgets Gadgets.Wires Gadgets.Wires.Catalog
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem center_name (o : RectOrientation) (w : ℕ) :
    (o.axis w 21).name (.horizontal 10)=if o.swapAxes then .vertical 10 else .horizontal 10 := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> rfl

def rowName (o : RectOrientation) (w : ℕ)
    (p : Cell (o.width w 21) (o.height w 21)) : AxisTrack :=
  (o.axis w 21).name (if (((o.axis w 21).geometry.cells.symm p).2.val=10) then .horizontal 10 else .outside)

theorem row_active (o : RectOrientation) (w : ℕ) (p : Cell (o.width w 21) (o.height w 21))
    (hp : rowName o w p≠.outside) : if o.swapAxes then p.1.val=10 else p.2.val=10 := by
  let e:=o.axis w 21
  let q:=e.geometry.cells.symm p
  have hq : q.2.val=10 := by
    by_contra he
    change e.name (if q.2.val=10 then .horizontal 10 else .outside)≠.outside at hp
    apply hp
    rw [ite_eq_right he]
    exact (e.outside .outside).mpr rfl
  have hs:=e.supported q (.horizontal 10) hq
  change ((o.axis w 21).name (.horizontal 10)).Supports (e.geometry.cells q) at hs
  have he : e.geometry.cells q=p := e.geometry.cells.apply_symm_apply p
  rw [he,center_name] at hs
  cases ho : o.swapAxes <;> simpa only [ho,Bool.false_eq_true,ite_true,ite_false,AxisTrack.Supports] using hs

theorem line_active (d : Direction) (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell ((lineOrientation d flip).width (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
      ((lineOrientation d flip).height (lineBase flip n hn a b).width (lineBase flip n hn a b).height))
    (hp : ((lineOrientation d flip).axis (lineBase flip n hn a b).width (lineBase flip n hn a b).height).name
      ((lineBaseClassifier flip n hn a b).name
        (((lineOrientation d flip).axis (lineBase flip n hn a b).width (lineBase flip n hn a b).height).geometry.cells.symm p))≠.outside) :
    if d=.east ∨d=.west then p.2.val=10 else p.1.val=10 := by
  let o:=lineOrientation d flip
  let w:=n+(if flip then 25 else 5)
  cases d <;> cases flip
  all_goals
    change rowName o w p≠.outside at hp
    have hh:=row_active o w p hp
    simpa [o,lineOrientation] using hh

theorem thin_boundary_nat (s : Shape) (p : ℕ×ℕ) (hx : p.1<s.width) (hy : p.2<s.height)
    (hb : p.1=0 ∨p.1+1=s.width ∨p.2=0 ∨p.2+1=s.height)
    (hc : (s.width=21 ∧21<s.height ∧p.1=10) ∨(21<s.width ∧s.height=21 ∧p.2=10)) : p∈s.boundary := by
  rcases p with ⟨x,y⟩
  dsimp only at hx hy hb hc
  rcases hc with ⟨hw,hh,hr⟩|⟨hw,hh,hr⟩
  · simp only [Shape.boundary,hw,ite_true,List.mem_cons,Prod.mk.injEq]
    omega
  · have hw' : s.width≠21 := by omega
    simp only [Shape.boundary,hw',hh,ite_true,ite_false,List.mem_cons,Prod.mk.injEq]
    omega

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
