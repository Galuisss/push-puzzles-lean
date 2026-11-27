/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateOuterAccess

/-! Canonical actual player access to every free interface of a placed thick gate. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateCanonicalAccess

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateMacros FiniteGateForwardContract
open FiniteGateFaceGeometry FiniteGateFaceBridge FiniteGateOuterAccess FiniteGateAStraight

variable {W H : ℕ}

attribute [local irreducible] FiniteGeometry.side

/-- The west AND interface joins the same canonical B face through its literal A-line crossing. -/
structure AndAccess (w : ℕ) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (stock : Finset (Cell W H)) : Prop where
  near : Access w true e B stock
  a : FiniteWireFrame.Frame (Corridor.a.active w true) e B stock
  aBridge : FiniteWireFrame.Frame (Corridor.aBridge.active w true) e B stock
  a_cross : Reachable B (some 1) ⟨e.cells (node w true .aDock),stock⟩
    ⟨e.cells (node w true .aBridge),stock⟩
  a_cross_reverse : Reachable B (some 1) ⟨e.cells (node w true .aBridge),stock⟩
    ⟨e.cells (node w true .aDock),stock⟩

private theorem frame_free {N M : ℕ} {active : Finset (Cell N M)}
    {e : GridEmbedding N M W H} {B : Board W H} {stock : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame active e B stock) (p : Cell N M) (hp : p ∈ active) :
    Free B stock (e.cells p) := ⟨F.floor p hp,F.fixed_avoids p hp⟩

private theorem adjacent_walk {N M : ℕ} {e : GridEmbedding N M W H}
    {B : Board W H} {stock : Finset (Cell W H)} {p q : Cell N M} {d : Direction}
    (hd : Disjoint stock B.walls) (hp : Free B stock (e.cells p)) (hq : Free B stock (e.cells q))
    (ha : Adjacent d p q) :
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells q,stock⟩ :=
  Relation.ReflTransGen.single ⟨e.direction d,Move.walk ⟨hp.1,hd,hp.2⟩
    (e.adjacent d p q ha) hq.1 hq.2 rfl⟩

private theorem left_access {w : ℕ} {kind : Bool} {e : GridEmbedding (side w) (side w) W H}
    {B : Board W H} {stock : Finset (Cell W H)}
    (A : Access w kind e B stock) (p : Cell (side w) (side w)) (hp : p ∈ leftStrip w kind) :
    Reachable B (some 1) ⟨e.cells (dock w kind true),stock⟩ ⟨e.cells p,stock⟩ ∧
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells (dock w kind true),stock⟩ :=
  ⟨left_walk_ambient w kind e A.left _ p (dock_left_mem w kind) hp,
   left_walk_ambient w kind e A.left p _ hp (dock_left_mem w kind)⟩

private theorem right_access {w : ℕ} {kind : Bool} {e : GridEmbedding (side w) (side w) W H}
    {B : Board W H} {stock : Finset (Cell W H)}
    (A : Access w kind e B stock) (p : Cell (side w) (side w)) (hp : p ∈ rightStrip w kind) :
    Reachable B (some 1) ⟨e.cells (dock w kind true),stock⟩ ⟨e.cells p,stock⟩ ∧
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells (dock w kind true),stock⟩ :=
  ⟨A.cross.trans (right_walk_ambient w kind e A.right _ p (dock_right_mem w kind) hp),
   (right_walk_ambient w kind e A.right p _ hp (dock_right_mem w kind)).trans A.cross_reverse⟩

private theorem lip_access (w : ℕ) (hw : 2 ≤ w) (kind : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (A : Access w kind e B stock) (hp : Free B stock (e.cells (point w (column kind) 1
      (by cases kind <;> dsimp [column] <;> omega)))) :
    Reachable B (some 1) ⟨e.cells (dock w kind true),stock⟩
      ⟨e.cells (point w (column kind) 1 (by cases kind <;> dsimp [column] <;> omega)),stock⟩ ∧
    Reachable B (some 1)
      ⟨e.cells (point w (column kind) 1 (by cases kind <;> dsimp [column] <;> omega)),stock⟩
      ⟨e.cells (dock w kind true),stock⟩ := by
  let q := point w (column kind-1) 1 (by cases kind <;> dsimp [column] <;> omega)
  have hq : q ∈ leftStrip w kind :=
    point_left_mem w hw kind (column kind-1) 1
      (by cases kind <;> dsimp [column] <;> omega) (by omega)
  have hqfree := frame_free A.left q hq
  have hadj : Adjacent .east q (point w (column kind) 1
      (by cases kind <;> dsimp [column] <;> omega)) := by
    cases kind <;> dsimp [q,Adjacent,point,column] <;> omega
  have hr := left_access A q hq
  exact ⟨hr.1.trans (adjacent_walk A.left.fixed_floor hqfree hp hadj),
    (adjacent_walk A.left.fixed_floor hp hqfree hadj.reverse).trans hr.2⟩

/-- Every actual free AND macro interface is reached from and returns to the literal B-left dock. -/
theorem AndAccess.access (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (A : AndAccess w e B stock) (p : Cell (side w) (side w)) (hp : p ∈ andPortals w)
    (hfree : Free B stock (e.cells p)) :
    Reachable B (some 1) ⟨e.cells (dock w true true),stock⟩ ⟨e.cells p,stock⟩ ∧
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells (dock w true true),stock⟩ := by
  simp only [andPortals,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hf := ((Corridor.a.walk_ambient w true e A.a).trans A.a_cross).trans
      (Corridor.aBridge.walk_ambient w true e A.aBridge)
    have hb := ((Corridor.aBridge.walk_reverse_ambient w true e A.aBridge).trans
      A.a_cross_reverse).trans (Corridor.a.walk_reverse_ambient w true e A.a)
    simpa only [Corridor.start,Corridor.finish,aInner_and,bLeft_eq] using And.intro hb hf
  · exact left_access A.near _ (point_left_mem w hw true 1 1 (by decide) (by omega))
  · exact left_access A.near _ (point_left_mem w hw true 2 2 (by decide) (by omega))
  · exact left_access A.near _ (point_left_mem w hw true 2 1 (by decide) (by omega))
  · exact lip_access w hw true e A.near hfree
  · exact right_access A.near _ (point_right_mem w hw true (w+4) (by dsimp [column]; omega))
  · exact right_access A.near _ (point_right_mem w hw true (w+6) (by dsimp [column]; omega))

/-- Every actual free OR macro interface is reached from and returns to the literal B-left dock. -/
theorem or_access (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (A : Access w false e B stock) (p : Cell (side w) (side w)) (hp : p ∈ orPortals w)
    (hfree : Free B stock (e.cells p)) :
    Reachable B (some 1) ⟨e.cells (dock w false true),stock⟩ ⟨e.cells p,stock⟩ ∧
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells (dock w false true),stock⟩ := by
  simp only [orPortals,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact left_access A _ (point_left_mem w hw false 1 1 (by decide) (by omega))
  · exact left_access A _ (point_left_mem w hw false 3 2 (by decide) (by omega))
  · exact left_access A _ (point_left_mem w hw false 3 1 (by decide) (by omega))
  · exact lip_access w hw false e A hfree
  · exact right_access A _ (point_right_mem w hw false (w+5) (by dsimp [column]; omega))
  · exact right_access A _ (point_right_mem w hw false (w+7) (by dsimp [column]; omega))

/-- A placed AND single-change macro begins and ends at the same actual canonical outer player cell. -/
theorem and_canonical_step (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H) (extra : Finset (Cell W H))
    (C : Contract true B (fun s => (andBoxes w s.left s.upper s.right).map e.cells ∪ extra)
      ((andPortals w).map e.cells))
    (A : ∀ s : Gates.Signals, AndAccess w e B
      ((andBoxes w s.left s.upper s.right).map e.cells ∪ extra))
    (initial final : Gates.Signals) (hi : Gates.legal true initial) (hf : Gates.legal true final)
    (hs : Gates.singleChange initial final)
    (hne : (andBoxes w initial.left initial.upper initial.right).map e.cells ∪ extra ≠
      (andBoxes w final.left final.upper final.right).map e.cells ∪ extra) :
    Reachable B (some 1)
      (e.extend extra ⟨dock w true true,andBoxes w initial.left initial.upper initial.right⟩)
      (e.extend extra ⟨dock w true true,andBoxes w final.left final.upper final.right⟩) := by
  apply C.canonical_step_at (fun _ => e.cells (dock w true true)) ?_ initial final hi hf hs hne
  intro s p hp hfree
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  exact (A s).access w hw e q hq hfree

/-- A placed OR single-change macro begins and ends at the same actual canonical outer player cell. -/
theorem or_canonical_step (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H) (extra : Finset (Cell W H))
    (C : Contract false B (fun s => (orBoxes w s.left s.upper s.right).map e.cells ∪ extra)
      ((orPortals w).map e.cells))
    (A : ∀ s : Gates.Signals, Access w false e B
      ((orBoxes w s.left s.upper s.right).map e.cells ∪ extra))
    (initial final : Gates.Signals) (hi : Gates.legal false initial) (hf : Gates.legal false final)
    (hs : Gates.singleChange initial final)
    (hne : (orBoxes w initial.left initial.upper initial.right).map e.cells ∪ extra ≠
      (orBoxes w final.left final.upper final.right).map e.cells ∪ extra) :
    Reachable B (some 1)
      (e.extend extra ⟨dock w false true,orBoxes w initial.left initial.upper initial.right⟩)
      (e.extend extra ⟨dock w false true,orBoxes w final.left final.upper final.right⟩) := by
  apply C.canonical_step_at (fun _ => e.cells (dock w false true)) ?_ initial final hi hf hs hne
  intro s p hp hfree
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  exact or_access w hw e (A s) q hq hfree

end PushPuzzle.PushS.FiniteGateCanonicalAccess
