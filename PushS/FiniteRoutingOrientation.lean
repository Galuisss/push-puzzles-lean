/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.RectOrientation
public import PushFS.Gadgets.Wires.Catalog.RotateCertificate
public import PushFS.Gadgets.Wires.Polyline.StrongTransport

/-! Whole-board certificates and prescribed physical target order in all eight rectangular orientations. -/

@[expose] public section
namespace PushPuzzle.PushFS

open Gadgets.Wires.Catalog

private def selected {w h : ℕ} (swap : Bool) (p : Cell w h) : ℕ := if swap then p.2.val else p.1.val

private theorem mapped_column {w h : ℕ} (o : RectOrientation) (p q : Cell w h) (he : p.1 = q.1) :
    selected o.swapAxes ((o.axis w h).geometry.cells p) = selected o.swapAxes ((o.axis w h).geometry.cells q) := by
  have hp := o.point_cells w h p
  have hq := o.point_cells w h q
  have hx := congrArg Fin.val he
  have hpx := congrArg Prod.fst hp
  have hpy := congrArg Prod.snd hp
  have hqx := congrArg Prod.fst hq
  have hqy := congrArg Prod.snd hq
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp only [selected, RectOrientation.point, RectOrientation.width, RectOrientation.height,
      Bool.false_eq_true, ite_true, ite_false] at * <;> omega

private theorem mapped_row {w h : ℕ} (o : RectOrientation) (p q : Cell w h) (he : p.2 = q.2) :
    selected (!o.swapAxes) ((o.axis w h).geometry.cells p) = selected (!o.swapAxes) ((o.axis w h).geometry.cells q) := by
  have hp := o.point_cells w h p
  have hq := o.point_cells w h q
  have hx := congrArg Fin.val he
  have hpx := congrArg Prod.fst hp
  have hpy := congrArg Prod.snd hp
  have hqx := congrArg Prod.fst hq
  have hqy := congrArg Prod.snd hq
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;>
    simp only [selected, RectOrientation.point, RectOrientation.width, RectOrientation.height,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, ite_true, ite_false] at * <;> omega

/-- Occupied component straightness survives every actual rectangular orientation. -/
private theorem RectOrientation.component_linear {w h : ℕ} (o : RectOrientation) (B : Board w h)
    (anchor : Cell w h)
    (hl : ComponentLinear (component B anchor)) :
    ComponentLinear (component ((o.axis w h).geometry.board B) ((o.axis w h).geometry.cells anchor)) := by
  let e := (o.axis w h).geometry
  have column (hc : ∀ p q, component B p = component B anchor → component B q = component B anchor → p.1 = q.1)
      (p q : Cell (o.width w h) (o.height w h))
      (hp : component (e.board B) p = component (e.board B) (e.cells anchor))
      (hq : component (e.board B) q = component (e.board B) (e.cells anchor)) :
      selected o.swapAxes p = selected o.swapAxes q := by
    obtain ⟨p,rfl⟩ := e.cells.surjective p
    obtain ⟨q,rfl⟩ := e.cells.surjective q
    exact mapped_column o p q (hc p q (component_reflect e B hp) (component_reflect e B hq))
  have row (hc : ∀ p q, component B p = component B anchor → component B q = component B anchor → p.2 = q.2)
      (p q : Cell (o.width w h) (o.height w h))
      (hp : component (e.board B) p = component (e.board B) (e.cells anchor))
      (hq : component (e.board B) q = component (e.board B) (e.cells anchor)) :
      selected (!o.swapAxes) p = selected (!o.swapAxes) q := by
    obtain ⟨p,rfl⟩ := e.cells.surjective p
    obtain ⟨q,rfl⟩ := e.cells.surjective q
    exact mapped_row o p q (hc p q (component_reflect e B hp) (component_reflect e B hq))
  rcases hl with hl | hl
  · cases hs : o.swapAxes
    · left
      intro p q hp hq
      apply Fin.ext
      simpa only [hs,selected,Bool.false_eq_true,ite_false] using column hl p q hp hq
    · right
      intro p q hp hq
      apply Fin.ext
      simpa only [hs,selected,ite_true] using column hl p q hp hq
  · cases hs : o.swapAxes
    · right
      intro p q hp hq
      apply Fin.ext
      simpa only [hs,selected,Bool.not_false,ite_true] using row hl p q hp hq
    · left
      intro p q hp hq
      apply Fin.ext
      simpa only [hs,selected,Bool.not_true,Bool.false_eq_true,ite_false] using row hl p q hp hq

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

/-- The complete C1–C3 certificate transports with the actual source and target label maps. -/
theorem Certificate.reorient (cert : Certificate I) (M : SlotMatching I L) (o : RectOrientation) :
    Certificate ((o.axis I.width I.height).geometry.reorientInstance I) :=
  rotateCertificate M cert _ (o.component_linear I.board)

/-- Exact prescribed target order transports through the concrete eight grid symmetries. -/
theorem SlotMatching.Ordered.reorient (ho : M.Ordered) (o : RectOrientation) :
    (M.reorient (o.axis I.width I.height).geometry).Ordered where
  horizontal i j hc hij := by
    let e := (o.axis I.width I.height).geometry
    have hc0 := component_reflect e I.board hc
    have hf := ho.horizontal i j hc0
    have hfr := ho.horizontal j i hc0.symm
    have hv := ho.vertical i j hc0
    have hvr := ho.vertical j i hc0.symm
    have hsi := congrArg Prod.fst (o.point_cells I.width I.height (M.source i))
    have hsj := congrArg Prod.fst (o.point_cells I.width I.height (M.source j))
    have hti := congrArg Prod.fst (o.point_cells I.width I.height (M.target i))
    have htj := congrArg Prod.fst (o.point_cells I.width I.height (M.target j))
    have hsix := (M.source i).1.isLt
    have hsiy := (M.source i).2.isLt
    have hsjx := (M.source j).1.isLt
    have hsjy := (M.source j).2.isLt
    have htix := (M.target i).1.isLt
    have htiy := (M.target i).2.isLt
    have htjx := (M.target j).1.isLt
    have htjy := (M.target j).2.isLt
    change ((o.axis I.width I.height).geometry.cells (M.source i)).1.val <
      ((o.axis I.width I.height).geometry.cells (M.source j)).1.val at hij
    change ((o.axis I.width I.height).geometry.cells (M.target i)).1.val <
      ((o.axis I.width I.height).geometry.cells (M.target j)).1.val
    dsimp only at hsi hsj hti htj
    rw [←hsi,←hsj] at hij
    rw [←hti,←htj]
    rcases o with ⟨s,x,y⟩
    cases s <;> cases x <;> cases y <;>
      simp only [RectOrientation.point,RectOrientation.width,RectOrientation.height,
        Bool.false_eq_true,ite_true,ite_false] at hij ⊢ <;> omega
  vertical i j hc hij := by
    let e := (o.axis I.width I.height).geometry
    have hc0 := component_reflect e I.board hc
    have hf := ho.horizontal i j hc0
    have hfr := ho.horizontal j i hc0.symm
    have hv := ho.vertical i j hc0
    have hvr := ho.vertical j i hc0.symm
    have hsi := congrArg Prod.snd (o.point_cells I.width I.height (M.source i))
    have hsj := congrArg Prod.snd (o.point_cells I.width I.height (M.source j))
    have hti := congrArg Prod.snd (o.point_cells I.width I.height (M.target i))
    have htj := congrArg Prod.snd (o.point_cells I.width I.height (M.target j))
    have hsix := (M.source i).1.isLt
    have hsiy := (M.source i).2.isLt
    have hsjx := (M.source j).1.isLt
    have hsjy := (M.source j).2.isLt
    have htix := (M.target i).1.isLt
    have htiy := (M.target i).2.isLt
    have htjx := (M.target j).1.isLt
    have htjy := (M.target j).2.isLt
    change ((o.axis I.width I.height).geometry.cells (M.source i)).2.val <
      ((o.axis I.width I.height).geometry.cells (M.source j)).2.val at hij
    change ((o.axis I.width I.height).geometry.cells (M.target i)).2.val <
      ((o.axis I.width I.height).geometry.cells (M.target j)).2.val
    dsimp only at hsi hsj hti htj
    rw [←hsi,←hsj] at hij
    rw [←hti,←htj]
    rcases o with ⟨s,x,y⟩
    cases s <;> cases x <;> cases y <;>
      simp only [RectOrientation.point,RectOrientation.width,RectOrientation.height,
        Bool.false_eq_true,ite_true,ite_false] at hij ⊢ <;> omega

end PushPuzzle.PushFS
