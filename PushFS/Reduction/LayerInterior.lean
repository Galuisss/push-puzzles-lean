/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerOccurrence

/-! Exact recovery of an actual source layer's named arcs inside its open row interval. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

private theorem LayerOccurrence.row_lower {w : Word} {st : Word.State} {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) : y≤row := by
  induction h with
  | here => exact le_rfl
  | later h ih => exact (Nat.le_add_right _ _).trans ih

/-- A complete named unit arc strictly inside an actual layer belongs to that very layer. -/
theorem LayerOccurrence.arc_inside {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    {st : Word.State} (hlen : st.wires.length=a.length) {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) {e : ℕ} {d : Direction} {p : GridRouting.Point}
    (hp : 0<p.2 ∧ p.2<l.height)
    (ha : HasArc (Route.edgeSegments (programFrom w st y,e)) d (p.1,p.2+row)) :
    HasArc (Route.edgeSegments (l.connections,e)) d p := by
  induction D generalizing st y with
  | nil => cases h
  | @cons sl w a b c layer rest ih =>
    let first : Layer := ⟨sl,st⟩
    have hf : first.HasDrawing := ⟨a,b,layer,hlen⟩
    rw [programFrom_edgeSegments_cons,hasArc_append] at ha
    cases h with
    | here =>
      change 0<p.2 ∧ p.2<first.height at hp
      rcases ha with ha | ha
      · have hh := (hasArc_translate _ 0 row d _).mp ha
        simpa only [Nat.sub_zero,Nat.add_sub_cancel_right] using hh.2.2
      · have hh := programFrom_row_lower w (sl.run st) (row+first.height)
          ((Route.edgeSegments_trace _ _ _).mp ha.point)
        exact False.elim (by change row+first.height≤p.2+row at hh; omega)
    | later h =>
      rcases ha with ha | ha
      · obtain ⟨_,_,ht⟩ := (hasArc_translate _ 0 y d _).mp ha
        have hh := (first.trace_classified hf ((Route.edgeSegments_trace _ _ _).mp ht.point)).row_le hf
        have hr := h.row_lower
        change p.2+row-y≤first.height at hh
        change y+first.height≤row at hr
        exact False.elim (by omega)
      · exact ih (drawn_after_length layer st hlen) h ha

theorem LayerOccurrence.incoming_inside {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    {st : Word.State} (hlen : st.wires.length=a.length) {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) {e : ℕ} {d : Direction} {p : GridRouting.Point}
    (hp : 0<p.2 ∧ p.2<l.height)
    (ha : HasIncoming (Route.edgeSegments (programFrom w st y,e)) d (p.1,p.2+row)) :
    HasIncoming (Route.edgeSegments (l.connections,e)) d p := by
  induction D generalizing st y with
  | nil => cases h
  | @cons sl w a b c layer rest ih =>
    let first : Layer := ⟨sl,st⟩
    have hf : first.HasDrawing := ⟨a,b,layer,hlen⟩
    rw [programFrom_edgeSegments_cons,hasIncoming_append] at ha
    cases h with
    | here =>
      change 0<p.2 ∧ p.2<first.height at hp
      rcases ha with ha | ha
      · have hh := (hasIncoming_translate _ 0 row d _).mp ha
        simpa only [Nat.sub_zero,Nat.add_sub_cancel_right] using hh.2.2
      · have hh := programFrom_row_lower w (sl.run st) (row+first.height)
          ((Route.edgeSegments_trace _ _ _).mp ha.point)
        exact False.elim (by change row+first.height≤p.2+row at hh; omega)
    | later h =>
      rcases ha with ha | ha
      · obtain ⟨_,_,ht⟩ := (hasIncoming_translate _ 0 y d _).mp ha
        have hh := (first.trace_classified hf ((Route.edgeSegments_trace _ _ _).mp ht.point)).row_le hf
        have hr := h.row_lower
        change p.2+row-y≤first.height at hh
        change y+first.height≤row at hr
        exact False.elim (by omega)
      · exact ih (drawn_after_length layer st hlen) h ha

end PushPuzzle.PushFS.Reduction.Plan
