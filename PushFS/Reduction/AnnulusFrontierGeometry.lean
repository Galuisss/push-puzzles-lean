/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusSeamAnchors
public import PushFS.Reduction.AnnulusLineCollars
public import PushFS.RectPlacement

/-! The actual buffered-core frontier uses one common near orientation and a literal shared endpoint anchor. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def frontierFlip (kind : Bool) (role : Fin 3) : Bool :=
  if role=2 then true else decide (role=0) && !kind

def frontierOrientation (kind : Bool) (role : Fin 3) : RectOrientation :=
  lineOrientation (Gates.portDirection role) (frontierFlip kind role)

def frontierBufferIndex (role : Fin 3) : Fin 4 := role.succ

def frontierLeadPlacement (kind : Bool) (n : ℕ) : Fin 3→GridEmbedding (n+5) 21 (2*n+101) (2*n+137) :=
  Fin.cases (GateLead.west kind n) (Fin.cases (GateLead.north kind n) (fun _=>GateLead.east kind n))

def frontierLeadAnchor (n : ℕ) : Chain.C n := (⟨n+2,by omega⟩,10)

/-- Every actual buffered lead has exactly the orientation used at the first real annular filler. -/
theorem frontier_lead_coordinates (kind : Bool) (n : ℕ) (role : Fin 3) (p : Chain.C n) :
    (frontierOrientation kind role).coordinates (n+5) 21
      (GateLead.dx kind n (frontierBufferIndex role)) (GateLead.dy kind n (frontierBufferIndex role)) p=
      (((frontierLeadPlacement kind n role).cells p).1.val,((frontierLeadPlacement kind n role).cells p).2.val) := by
  fin_cases role <;> cases kind <;> rfl

/-- The literal false-phase end anchor is the true semantic buffered port anchor. -/
theorem frontier_lead_anchor (kind : Bool) (n : ℕ) (role : Fin 3) :
    (frontierLeadPlacement kind n role).cells (frontierLeadAnchor n)=GateLead.portAnchor kind n role := by
  fin_cases role
  · apply Prod.ext <;> apply Fin.ext
    · change ((GateLead.west kind n).cells (frontierLeadAnchor n)).1.val=_
      rw [GateLead.west_x kind n (frontierLeadAnchor n)]
      change (if kind then 8 else 9)+(n+4-(n+2))=(if kind then 10 else 11)
      cases kind <;> simp
    · change ((GateLead.west kind n).cells (frontierLeadAnchor n)).2.val=_
      rw [GateLead.west_y kind n (frontierLeadAnchor n)]
      change n+10+(if kind then 29 else 90)+(if kind then 10 else 20-10)=n+20+(if kind then 29 else 90)
      cases kind <;> simp
  · apply Prod.ext <;> apply Fin.ext
    · change n+(if kind then 43 else 44)+(20-10)=n+10+(if kind then 43 else 44)
      omega
    · change ((GateLead.north kind n).cells (frontierLeadAnchor n)).2.val=21
      rw [GateLead.north_y kind n (frontierLeadAnchor n)]
      change 19+(n+4-(n+2))=21
      omega
  · apply Prod.ext <;> apply Fin.ext
    · change n+(if kind then 88 else 87)+(n+2)=2*n+(if kind then 90 else 89)
      cases kind <;> simp <;> omega
    · change n+100+(20-10)=n+110
      omega

set_option maxHeartbeats 0 in
theorem frontier_first_valid : ∀q : Key, 0<(curve q).length := by decide +kernel

set_option maxHeartbeats 0 in
theorem frontier_first_orientation : ∀q : Key,
    lineOrientation (original q 0).travel (fillerFlip q 0)=frontierOrientation q.1.1 (GateAnnulus.role q.1) := by
  decide +kernel

/-- A real common far/near anchor fixes the complete relative primitive coordinates. -/
theorem frontier_relative {n m : ℕ} {hm : 2301≤m} (flip : Bool) (a b : Bool)
    (o : RectOrientation) (dx dy ex ey : ℕ) (p : Chain.C n)
    (q : Cell (lineBase flip m hm a b).width (lineBase flip m hm a b).height)
    (hp : o.coordinates (n+5) 21 dx dy p=o.coordinates _ _ ex ey q)
    (ha : o.coordinates (n+5) 21 dx dy (frontierLeadAnchor n)=
      o.coordinates _ _ ex ey (lineNearAnchor flip m hm a b)) :
    p.1.val=n+q.1.val ∧p.2.val=q.2.val := by
  have hh:=o.placed_inverse_relative o dx dy ex ey p (frontierLeadAnchor n) q (lineNearAnchor flip m hm a b) hp ha
  rw [o.inverseVector_vector] at hh
  change (((q.1.val : ℤ)-2),(q.2.val : ℤ)-10)=((p.1.val : ℤ)-(n+2 : ℕ),(p.2.val : ℤ)-10) at hh
  have hx:=congrArg Prod.fst hh
  have hy:=congrArg Prod.snd hh
  constructor <;> omega

/-- All actual overlapping primitive walls agree on the complete five-column frontier collar. -/
theorem frontier_walls_of_relative (n m : ℕ) (hn : 2301≤n) (hm : 2301≤m) (flip a b : Bool)
    (p : Chain.C n) (q : Cell (lineBase flip m hm a b).width (lineBase flip m hm a b).height)
    (hx : p.1.val=n+q.1.val) (hy : p.2.val=q.2.val) :
    p∈Chain.walls n hn ↔q∈(lineBase flip m hm a b).board.walls := by
  have hp:=p.1.isLt
  have hq : q.1.val<5 := by omega
  rw [Polyline.chain_right7 n hn p (by omega),line_near_walls flip m hm a b q hq,hy]

/-- Same-phase complete physical intervals on the two sides have the true two-cell gap. -/
theorem frontier_disjoint {n m : ℕ} {hm : 2301≤m} (flip a b phase : Bool)
    (o : RectOrientation) (dx dy ex ey : ℕ) (p : Chain.C n)
    (q : Cell (lineBase flip m hm a b).width (lineBase flip m hm a b).height)
    (hp : p.1.val≤n+phase.toNat) (hq : 2+phase.toNat≤q.1.val)
    (ha : o.coordinates (n+5) 21 dx dy (frontierLeadAnchor n)=
      o.coordinates _ _ ex ey (lineNearAnchor flip m hm a b)) :
    o.coordinates (n+5) 21 dx dy p≠o.coordinates _ _ ex ey q := by
  intro he
  have hr:=frontier_relative flip a b o dx dy ex ey p q he ha
  omega

end PushPuzzle.PushFS.Reduction.GateTileRouting
