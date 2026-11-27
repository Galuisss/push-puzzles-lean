/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.SourceRails
public import PushFS.Gadgets.Wires.Polyline.Reorientation

/-! C1–C3 and exact target order transport through actual D4 generators without any global track-level hypothesis. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


variable {w h W H : ℕ}

theorem component_reflect (e : GridIsometry w h W H) (B : Board w h) {p q : PushFS.Cell w h}
    (hc : component (e.board B) (e.cells p)=component (e.board B) (e.cells q)) : component B p=component B q :=
  component_eq_iff.mpr ((e.sameComponent_iff B p q).mp (component_eq_iff.mp hc))

private theorem linear_transpose (B : Board w h) (anchor : PushFS.Cell w h)
    (hl : ComponentLinear (component B anchor)) :
    ComponentLinear (component ((GridIsometry.transpose w h).board B) ((GridIsometry.transpose w h).cells anchor)) := by
  let e:=GridIsometry.transpose w h
  rcases hl with hc|hr
  · right
    intro p q hp hq
    obtain ⟨p,rfl⟩:=e.cells.surjective p
    obtain ⟨q,rfl⟩:=e.cells.surjective q
    exact hc p q (component_reflect e B hp) (component_reflect e B hq)
  · left
    intro p q hp hq
    obtain ⟨p,rfl⟩:=e.cells.surjective p
    obtain ⟨q,rfl⟩:=e.cells.surjective q
    exact hr p q (component_reflect e B hp) (component_reflect e B hq)

private theorem linear_reflectX (B : Board w h) (anchor : PushFS.Cell w h)
    (hl : ComponentLinear (component B anchor)) :
    ComponentLinear (component ((GridIsometry.reflectX w h).board B) ((GridIsometry.reflectX w h).cells anchor)) := by
  let e:=GridIsometry.reflectX w h
  rcases hl with hc|hr
  · left
    intro p q hp hq
    obtain ⟨p,rfl⟩:=e.cells.surjective p
    obtain ⟨q,rfl⟩:=e.cells.surjective q
    exact congrArg Fin.rev (hc p q (component_reflect e B hp) (component_reflect e B hq))
  · right
    intro p q hp hq
    obtain ⟨p,rfl⟩:=e.cells.surjective p
    obtain ⟨q,rfl⟩:=e.cells.surjective q
    exact hr p q (component_reflect e B hp) (component_reflect e B hq)

variable {I : Instance} {L : Type} [Fintype L]

/-- A physical row/column transport supplies the complete new C1–C3 certificate for all actual labels. -/
theorem rotateCertificate (M : SlotMatching I L) (cert : Certificate I) (e : GridIsometry I.width I.height W H)
    (linear : ∀p, ComponentLinear (component I.board p) → ComponentLinear (component (e.board I.board) (e.cells p))) :
    Certificate (e.reorientInstance I) where
  balanced:=(M.reorient e).componentBalanced
  linear p hp:=by
    change p∈I.initial.boxes.map e.cells.toEmbedding at hp
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    exact linear q (cert.linear q hq)
  separated p hp q hq hc d:=by
    change p∈I.board.goals.map e.cells.toEmbedding at hp
    change q∈I.board.goals.map e.cells.toEmbedding at hq
    obtain ⟨p,hpLocal,rfl⟩:=Finset.mem_map.mp hp
    obtain ⟨q,hqLocal,rfl⟩:=Finset.mem_map.mp hq
    intro ha
    change Adjacent d (e.cells p) (e.cells q) at ha
    exact cert.separated p hpLocal q hqLocal (component_reflect e I.board hc) (e.directions.symm d)
      ((e.adjacent _ _ _).mp (by simpa only [Equiv.apply_symm_apply] using ha))

/-- Transposition preserves the actual complete certificate, including occupied source SCCs and unlabelled goals. -/
theorem transposeCertificate (M : SlotMatching I L) (cert : Certificate I) :
    Certificate ((GridIsometry.transpose I.width I.height).reorientInstance I) :=
  rotateCertificate M cert _ (linear_transpose I.board)

/-- Reflection preserves every real C1–C3 property on the complete board. -/
theorem reflectXCertificate (M : SlotMatching I L) (cert : Certificate I) :
    Certificate ((GridIsometry.reflectX I.width I.height).reorientInstance I) :=
  rotateCertificate M cert _ (linear_reflectX I.board)

/-- Exact static physical target order is preserved when swapping the two actual coordinates. -/
theorem ordered_transpose (M : SlotMatching I L) (ho : M.Ordered) :
    (M.reorient (GridIsometry.transpose I.width I.height)).Ordered where
  horizontal i j hc hij:=by
    have hh:=component_reflect (GridIsometry.transpose I.width I.height) I.board hc
    exact ho.vertical i j hh hij
  vertical i j hc hij:=by
    have hh:=component_reflect (GridIsometry.transpose I.width I.height) I.board hc
    exact ho.horizontal i j hh hij

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
