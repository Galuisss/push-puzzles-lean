/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.ProgramFlowData
public import PushFS.Reduction.VertexTable

/-! Actual source-layer occurrences retain the compiler cut, global row and full named unit arcs. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- One actual source instruction at its exact compiler state and placed row. -/
inductive LayerOccurrence : Word → Word.State → ℕ → Layer → ℕ → Prop
  | here (sl : Slice) (w : Word) (st : Word.State) (y : ℕ) :
      LayerOccurrence (sl::w) st y ⟨sl,st⟩ y
  | later {sl : Slice} {w : Word} {st : Word.State} {y row : ℕ} {l : Layer} :
      LayerOccurrence w (sl.run st) (y+(Layer.mk sl st).height) l row →
      LayerOccurrence (sl::w) st y l row

theorem mem_verticesFrom_iff (w : Word) (st : Word.State) (y : ℕ) (v : VertexData) :
    v∈verticesFrom w st y ↔ ∃ l row,LayerOccurrence w st y l row ∧ v=l.vertexData row := by
  induction w generalizing st y with
  | nil =>
    constructor
    · intro h; cases h
    · rintro ⟨l,row,h,_⟩; cases h
  | cons sl w ih =>
    rw [verticesFrom_cons,List.mem_cons]
    constructor
    · rintro (rfl | hv)
      · exact ⟨⟨sl,st⟩,y,.here sl w st y,rfl⟩
      · obtain ⟨l,row,hl,hv⟩ := (ih _ _).mp hv
        exact ⟨l,row,.later hl,hv⟩
    · rintro ⟨l,row,hl,rfl⟩
      cases hl with
      | here => exact Or.inl rfl
      | later hl => exact Or.inr ((ih _ _).mpr ⟨l,row,hl,rfl⟩)

theorem LayerOccurrence.drawing {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    {st : Word.State} (hlen : st.wires.length=a.length) {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) : l.HasDrawing := by
  induction D generalizing st y with
  | nil => cases h
  | cons layer rest ih =>
    cases h with
    | here => exact ⟨_,_,layer,hlen⟩
    | later h => exact ih (drawn_after_length layer st hlen) h

theorem LayerOccurrence.numbered {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b)
    {st : Word.State} (hn : Numbered st) {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) : Numbered l.before := by
  induction D generalizing st y with
  | nil => cases h
  | cons layer rest ih =>
    cases h with
    | here => exact hn
    | later h => exact ih (hn.step (by rw [layer.layer_eq]; rfl)) h

/-- Every actual local directed arc appears at the same edge name in the complete placed program. -/
theorem LayerOccurrence.arc {w : Word} {st : Word.State} {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) {e : ℕ} {d : Direction} {p : GridRouting.Point}
    (ha : HasArc (Route.edgeSegments (l.connections,e)) d p) :
    HasArc (Route.edgeSegments (programFrom w st y,e)) d (p.1,p.2+row) := by
  induction h with
  | here sl w st y =>
    rw [programFrom_edgeSegments_cons,hasArc_append]
    left
    apply (hasArc_translate _ 0 y d _).mpr
    simpa only [Nat.sub_zero,Nat.add_sub_cancel_right] using
      (show 0≤p.1 ∧ y≤p.2+y ∧ HasArc (Route.edgeSegments ((Layer.mk sl st).connections,e)) d p from
        ⟨Nat.zero_le _,by omega,ha⟩)
  | later h ih =>
    rw [programFrom_edgeSegments_cons,hasArc_append]
    exact Or.inr (ih ha)

theorem LayerOccurrence.incoming {w : Word} {st : Word.State} {y row : ℕ} {l : Layer}
    (h : LayerOccurrence w st y l row) {e : ℕ} {d : Direction} {p : GridRouting.Point}
    (ha : HasIncoming (Route.edgeSegments (l.connections,e)) d p) :
    HasIncoming (Route.edgeSegments (programFrom w st y,e)) d (p.1,p.2+row) := by
  induction h with
  | here sl w st y =>
    rw [programFrom_edgeSegments_cons,hasIncoming_append]
    left
    apply (hasIncoming_translate _ 0 y d _).mpr
    simpa only [Nat.sub_zero,Nat.add_sub_cancel_right] using
      (show 0≤p.1 ∧ y≤p.2+y ∧ HasIncoming (Route.edgeSegments ((Layer.mk sl st).connections,e)) d p from
        ⟨Nat.zero_le _,by omega,ha⟩)
  | later h ih =>
    rw [programFrom_edgeSegments_cons,hasIncoming_append]
    exact Or.inr (ih ha)

end PushPuzzle.PushFS.Reduction.Plan
