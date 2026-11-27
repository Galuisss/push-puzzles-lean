/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingFootprint

/-! The actual unrotated core and its outward arm stocks have separate actors and clear rail rays. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry

attribute [local irreducible] FiniteGeometry.side

def coreWorld (w : ℕ) (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) : ℕ × ℕ :=
  (padding w+coreOffset w+p.1.val,padding w+coreOffset w+p.2.val)

theorem andPoint_actor_bounds (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : AndLabel w) :
    origin w-8*w-16-a.toNat ≤ (andPoint w a b c l).1 ∧
      (andPoint w a b c l).1 ≤ origin w+3*w+13-c.toNat ∧
      origin w-8*w-31-b.toNat ≤ (andPoint w a b c l).2 ∧
      (andPoint w a b c l).2 ≤ origin w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> dsimp [andPoint,origin] <;> omega

theorem orPoint_actor_bounds (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : OrLabel w) :
    origin w-2*w-7-a.toNat ≤ (orPoint w a b c l).1 ∧
      (orPoint w a b c l).1 ≤ origin w+3*w+14-c.toNat ∧
      origin w-2*w-13-b.toNat ≤ (orPoint w a b c l).2 ∧
      (orPoint w a b c l).2 ≤ origin w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> dsimp [orPoint,origin] <;> omega

theorem andRay_boxes_separated (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (role : Fin 3) (t : ℕ)
    (ht : (portInflow a b c role).toNat+2 ≤ t) (l : AndLabel w) :
    ¬Nearby 1 (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) t)
      (coreWorld w (andCell w a b c l)) := by
  have hbds := andPoint_actor_bounds w hw a b c l
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hnc : (!c).toNat+c.toNat = 1 := by cases c <;> rfl
  intro hn
  fin_cases role <;>
    simp [Nearby,Line.along,PortAnnulus.innerDirection,corePort,coreWorld,andCell,portInflow,
      origin,coreOffset,padding,spacing] at * <;> omega

theorem orRay_boxes_separated (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (role : Fin 3) (t : ℕ)
    (ht : (portInflow a b c role).toNat+2 ≤ t) (l : OrLabel w) :
    ¬Nearby 1 (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) t)
      (coreWorld w (orCell w a b c l)) := by
  have hbds := orPoint_actor_bounds w hw a b c l
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hnc : (!c).toNat+c.toNat = 1 := by cases c <;> rfl
  intro hn
  fin_cases role <;>
    simp [Nearby,Line.along,PortAnnulus.innerDirection,corePort,coreWorld,orCell,portInflow,
      origin,coreOffset,padding,spacing] at * <;> omega

set_option maxRecDepth 65536 in
set_option maxHeartbeats 1000000 in
/-- The whole outward AND rail ray is actual core floor. -/
theorem andRay_not_wall (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) (t : ℕ)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ andWalls w) :
    coreWorld w p ≠ Line.along w (PortAnnulus.innerDirection role) (corePort w true role) t := by
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  have hb := ((andRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> fin_cases role <;>
    simp [andRectangle,coreWorld,Line.along,PortAnnulus.innerDirection,corePort,
      origin,coreOffset,padding,spacing] at hb hx hy <;> omega

set_option maxRecDepth 65536 in
/-- The whole outward OR rail ray is actual core floor. -/
theorem orRay_not_wall (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) (t : ℕ)
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ orWalls w) :
    coreWorld w p ≠ Line.along w (PortAnnulus.innerDirection role) (corePort w false role) t := by
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  have hb := ((orRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> fin_cases role <;>
    simp [orRectangle,coreWorld,Line.along,PortAnnulus.innerDirection,corePort,
      origin,coreOffset,padding,spacing] at hb hx hy <;> omega

set_option maxRecDepth 65536 in
/-- Every adapter segment after its initial outward ray stays far from the complete core rectangle. -/
private theorem adapter_tail_avoids_core (w : ℕ) (kind : Bool) (role : Fin 3) {p r : ℕ × ℕ}
    (hp : ∃ s ∈ (adapter w kind role).tail, s.Contains p)
    (hrx : coreOffset w ≤ r.1 ∧ r.1 < coreOffset w+FiniteGeometry.side w)
    (hry : coreOffset w ≤ r.2 ∧ r.2 < coreOffset w+FiniteGeometry.side w) :
    ¬Nearby (origin w) p r := by
  obtain ⟨s,hs,hp⟩ := hp
  have hb := Segment.coordinate_bounds hp
  clear hp
  cases kind <;> fin_cases role <;>
    simp [adapter,adapterVertices,corePort,spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl <;>
    dsimp only at hb <;>
    unfold Nearby coreOffset FiniteGeometry.side origin at * <;> omega

private theorem route_tail_avoids_core (w : ℕ) (kind : Bool) (q : Key) {p r : ℕ × ℕ}
    (hp : ∃ s ∈ (route w kind q).tail, s.Contains p)
    (hrx : coreOffset w ≤ r.1 ∧ r.1 < coreOffset w+FiniteGeometry.side w)
    (hry : coreOffset w ≤ r.2 ∧ r.2 < coreOffset w+FiniteGeometry.side w) :
    ¬Nearby (origin w) p r := by
  have hne : adapter w kind q.2.2 ≠ [] := by
    intro h
    have hh := adapter_length w kind q.2.2
    rw [h] at hh
    contradiction
  obtain ⟨a,atoms,he⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨s,hs,hp⟩ := hp
  change s ∈ (adapter w kind q.2.2 ++ curve w q).tail at hs
  rw [he] at hs
  simp only [List.cons_append,List.tail_cons] at hs
  rcases List.mem_append.mp hs with hs | hs
  · apply adapter_tail_avoids_core w kind q.2.2 _ hrx hry
    exact ⟨s,by simpa only [he,List.tail_cons] using hs,hp⟩
  · exact avoids_core w q ⟨s,hs,hp⟩ hrx hry

/-- The narrow footprint of every noninitial arm primitive is disjoint from every actual core cell. -/
theorem route_tail_near_core_disjoint (w : ℕ) (kind : Bool) (q : Key) (margin : ℕ)
    (hm : margin ≤ origin w) {u a : ℕ × ℕ}
    (hu : ∃ s ∈ (route w kind q).tail, s.Contains u)
    (ha : Nearby margin a (padding w+u.1,padding w+u.2))
    (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) : a ≠ coreWorld w p := by
  have hsep := route_tail_avoids_core w kind q hu
    (r := (coreOffset w+p.1.val,coreOffset w+p.2.val))
    (by have hp := p.1.isLt; omega) (by have hp := p.2.isLt; omega)
  intro he
  rw [he] at ha
  unfold coreWorld Nearby at *
  omega

end PushPuzzle.PushS.FiniteRouting
