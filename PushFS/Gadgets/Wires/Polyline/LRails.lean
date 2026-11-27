/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.Line
public import PushFS.Gadgets.Wires.Polyline.Endpoints
public import PushFS.Gadgets.Wires.Polyline.StrongTransport
public import PushFS.Gadgets.Wires.Soundness.Turn

/-! The real joint floor, including support cells on either side of each staggered two-box seam. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline.L

set_option maxRecDepth 65536

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n)

private theorem horizontal_floor (goals : Finset (C m n)) (p : C m n) (hx : 10≤p.1.val)
    (hy : p.2.val=10) :
    p∉(board m n hm hn goals).walls := by
  intro hp
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
      have hh:=congrArg (fun p : C m n=>p.2.val) he
      rw [in_y] at hh
      have hw:=Chain.walls_rows m hm q hq
      omega
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
      have hhX:=congrArg (fun p : C m n=>p.1.val) he
      have hhY:=congrArg (fun p : C m n=>p.2.val) he
      rw [turn_x] at hhX
      rw [turn_y] at hhY
      have check : ∀ q : Turn.C, 10≤q.1.val → q.2.val=9 → Turn.wallTest q=false := by decide +kernel
      have hw:=(Turn.template.mem_walls q).mp hq
      change Turn.wallTest q=true at hw
      rw [check q (by omega) (by omega)] at hw
      contradiction
  · obtain ⟨q,_,he⟩:=Finset.mem_map.mp hp
    have hh:=congrArg (fun p : C m n=>p.2.val) he
    rw [out_y] at hh
    omega

private theorem vertical_floor (goals : Finset (C m n)) (p : C m n) (hx : p.1.val=10)
    (hy : 10≤p.2.val) :
    p∉(board m n hm hn goals).walls := by
  intro hp
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨q,_,he⟩:=Finset.mem_map.mp hp
      have hh:=congrArg (fun p : C m n=>p.1.val) he
      rw [in_x] at hh
      omega
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
      have hhX:=congrArg (fun p : C m n=>p.1.val) he
      have hhY:=congrArg (fun p : C m n=>p.2.val) he
      rw [turn_x] at hhX
      rw [turn_y] at hhY
      have check : ∀ q : Turn.C, q.1.val=10 → 9≤q.2.val → Turn.wallTest q=false := by decide +kernel
      have hw:=(Turn.template.mem_walls q).mp hq
      change Turn.wallTest q=true at hw
      rw [check q (by omega) (by omega)] at hw
      contradiction
  · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
    have hh:=congrArg (fun p : C m n=>p.1.val) he
    rw [out_x] at hh
    have hw:=Chain.walls_rows n hn q hq
    have := q.2.isLt
    omega

/-- The actual full horizontal rail has one static component, right of the protected corner. -/
theorem horizontal_component (a b : Bool) (p q : C m n)
    (hp : p.2.val=10 ∧ 10<p.1.val ∧ p.1.val+1<m+43)
    (hq : q.2.val=10 ∧ 10<q.1.val ∧ q.1.val+1<m+43) :
    SameComponent (atlas m n hm hn (uniform a) (uniform b)).puzzle.board p q := by
  change SameComponent (atlas m n hm hn (uniform a) (uniform b)).board p q
  rw [board_eq]
  have heP : p=(p.1,⟨10,by omega⟩) := Prod.ext rfl (Fin.ext hp.1)
  have heQ : q=(q.1,⟨10,by omega⟩) := Prod.ext rfl (Fin.ext hq.1)
  rw [heP,heQ]
  exact horizontal_tail_component _ 10 (fun x hx=>horizontal_floor m n hm hn _ (x,_) hx rfl)
    p.1 q.1 hp.2 hq.2

/-- The actual full vertical rail has one static component, below the protected corner. -/
theorem vertical_component (a b : Bool) (p q : C m n)
    (hp : p.1.val=10 ∧ 10<p.2.val ∧ p.2.val+1<n+44)
    (hq : q.1.val=10 ∧ 10<q.2.val ∧ q.2.val+1<n+44) :
    SameComponent (atlas m n hm hn (uniform a) (uniform b)).puzzle.board p q := by
  let e:=GridIsometry.transpose (m+43) (n+44)
  apply (e.sameComponent_iff _ _ _).mp
  change SameComponent (e.board (atlas m n hm hn (uniform a) (uniform b)).board) (e.cells p) (e.cells q)
  rw [board_eq]
  have heP : e.cells p=(p.2,⟨10,by omega⟩) := Prod.ext rfl (Fin.ext hp.1)
  have heQ : e.cells q=(q.2,⟨10,by omega⟩) := Prod.ext rfl (Fin.ext hq.1)
  rw [heP,heQ]
  apply horizontal_tail_component _ 10 _ p.2 q.2 hp.2 hq.2
  intro y hy hw
  have hh : (⟨10,by omega⟩,y)∈(board m n hm hn _).walls := (e.mem_walls _ _).mp hw
  exact vertical_floor m n hm hn _ _ rfl hy hh

end PushPuzzle.PushFS.Gadgets.Wires.Polyline.L
