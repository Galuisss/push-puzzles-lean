/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.TraceData
public import PushS.Source.Diagram.Word.DrawingCorrectness
import all PushS.Source.Diagram.Word.DrawingCorrectness
import all PushS.Source.Strip.Sweep.CanonicalDrawing

import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Pad
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Composition

/-!
# Exact original compiler strands in canonical word traces

Thread the original native labels through the same layered word drawing. The trace query uses
those exact incoming labels and original newly created labels at each actual layer.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_eq`: exact full original canonical trace query.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib Diagram GridLayout GridRouting

private def fromQuery (w : Word) (st : Word.State) (p : GridRouting.Point) (i : ℕ)
    (created : Bool) (slot : ℕ) : LayerInput :=
  let sl := (w.getD i (.swap 0)).data
  let current := Word.run (w.take i) st
  { suffix := current.wires.length - (sl.offset + sl.inputs.length)
    offset := sl.offset
    inputs := sl.inputs.length
    outputs := sl.outputs.length
    created := created
    slot := slot
    x := p.1
    y := p.2 - ((heightsFrom w st).take i).sum }

private def fromAt (width : ℕ) (w : Word) (st : Word.State) (edge : ℕ)
    (p : GridRouting.Point) (i : ℕ) : Bool :=
  let current := Word.run (w.take i) st
  let sl := (w.getD i (.swap 0)).data
  let base := ((heightsFrom w st).take i).sum
  if base ≤ p.2 ∧ p.1 ≤ Strip.Sweep.drawingWidth width ∧ p.2 - base ≤ 4 * width + 6 then
    ((List.range current.wires.length).any fun j =>
      (current.wires.getD j 0 == edge) && (fromQuery w st p i false j).test width) ||
    ((List.range sl.outputs.length).any fun j =>
      (current.next + j == edge) && (fromQuery w st p i true j).test width)
  else false

private def fromTrace (width : ℕ) (w : Word) (st : Word.State) (edge : ℕ)
    (p : GridRouting.Point) : Bool := (List.range w.length).any (fromAt width w st edge p)

private theorem fromQuery_cons (sl : Slice) (w : Word) (st : Word.State)
    (p : GridRouting.Point) (i : ℕ) (created : Bool) (slot : ℕ) :
    fromQuery (sl :: w) st p (i + 1) created slot =
      fromQuery w (sl.run st)
        (p.1, p.2 - (2 * st.wires.length + 2 * (sl.run st).wires.length + 6)) i created slot := by
  simp only [fromQuery, List.getD_cons_succ, List.take_succ_cons, Word.run,
    List.foldl_cons, heightsFrom_cons, List.sum_cons, Nat.sub_sub]

private theorem fromAt_cons (width : ℕ) (sl : Slice) (w : Word) (st : Word.State)
    (edge : ℕ) (p : GridRouting.Point) (i : ℕ) :
    fromAt width (sl :: w) st edge p (i + 1) =
      if 2 * st.wires.length + 2 * (sl.run st).wires.length + 6 ≤ p.2 then
        fromAt width w (sl.run st) edge
          (p.1, p.2 - (2 * st.wires.length + 2 * (sl.run st).wires.length + 6)) i
      else false := by
  simp only [fromAt, List.getD_cons_succ, List.take_succ_cons, heightsFrom_cons,
    List.sum_cons, Word.run, List.foldl_cons, fromQuery_cons, Nat.sub_sub]
  split_ifs <;> first | rfl | omega

private theorem fromTrace_cons (width : ℕ) (sl : Slice) (w : Word) (st : Word.State)
    (edge : ℕ) (p : GridRouting.Point) :
    fromTrace width (sl :: w) st edge p = (fromAt width (sl :: w) st edge p 0 ||
      if 2 * st.wires.length + 2 * (sl.run st).wires.length + 6 ≤ p.2 then
        fromTrace width w (sl.run st) edge
          (p.1, p.2 - (2 * st.wires.length + 2 * (sl.run st).wires.length + 6))
      else false) := by
  simp only [fromTrace, List.length_cons, List.range_succ_eq_map, List.any_cons,
    List.any_map, Function.comp_def, fromAt_cons]
  by_cases hd : 2 * st.wires.length + 2 * (sl.run st).wires.length + 6 ≤ p.2 <;>
    simp [hd]

private theorem trace_from (width : ℕ) (input : TraceInput) :
    input.trace width = fromTrace width input.word ⟨[], 0, []⟩ input.edge (input.x, input.y) :=
  rfl

private def strandLabel {k a b r : ℕ} (st : Word.State) : Strand k a b r → ℕ
  | .inl i => st.wires.getD i.val 0
  | .inr (.inl (.inl i)) => st.wires.getD (k + i.val) 0
  | .inr (.inl (.inr j)) => st.next + j.val
  | .inr (.inr j) => st.wires.getD (k + a + j.val) 0

private theorem strandLabel_input {k a b r : ℕ} (st : Word.State)
    (i : Fin (k + a + r)) : strandLabel st (inputStrand (b := b) i) = st.wires.getD i.val 0 := by
  unfold inputStrand
  split_ifs <;> dsimp only [strandLabel] <;> congr 1 <;> omega

private theorem exists_strand {k a b r : ℕ} (st : Word.State) (edge : ℕ)
    (T : Strand k a b r → Prop) :
    (∃ e, strandLabel st e = edge ∧ T e) ↔
      (∃ i : Fin (k + a + r), st.wires.getD i.val 0 = edge ∧ T (inputStrand i)) ∨
        ∃ j : Fin b, st.next + j.val = edge ∧ T (.inr (.inl (.inr j))) := by
  constructor
  · rintro ⟨e, he, ht⟩
    cases hi : inputIndex e with
    | some i =>
      have h := inputStrand_of_index e i hi
      subst e
      exact Or.inl ⟨i, (strandLabel_input st i) ▸ he, ht⟩
    | none =>
      rcases e with i | ((i | j) | j) <;> simp only [inputIndex, reduceCtorEq] at hi
      exact Or.inr ⟨j, he, ht⟩
  · rintro (⟨i, hi, ht⟩ | ⟨j, hj, ht⟩)
    · exact ⟨inputStrand i, (strandLabel_input st i).trans hi, ht⟩
    · exact ⟨.inr (.inl (.inr j)), hj, ht⟩

private theorem fromAt_zero_data (width k : ℕ) (as bs : List Color)
    (vs : List (Vertex (Fin as.length ⊕ Fin bs.length))) (w : Word) (st : Word.State)
    (edge : ℕ) (p : GridRouting.Point) :
    fromAt width (.gen k as bs vs :: w) st edge p 0 =
      if p.1 ≤ Strip.Sweep.drawingWidth width ∧ p.2 ≤ 4 * width + 6 then
        ((List.range st.wires.length).any fun j =>
          (st.wires.getD j 0 == edge) &&
            (fromQuery (.gen k as bs vs :: w) st p 0 false j).test width) ||
        ((List.range bs.length).any fun j =>
          (st.next + j == edge) &&
            (fromQuery (.gen k as bs vs :: w) st p 0 true j).test width)
      else false := by
  simp only [fromAt, List.take_zero, Word.run, List.foldl_nil, List.getD_cons_zero,
    Slice.data, List.sum_nil, Nat.zero_le, Nat.sub_zero, true_and]

private theorem fromAt_zero {width k r : ℕ} (as bs : List Color)
    (vs : List (Vertex (Fin as.length ⊕ Fin bs.length))) (w : Word) (st : Word.State)
    (hs : st.wires.length = k + as.length + r)
    (ha : k + as.length + r ≤ width) (hb : k + bs.length + r ≤ width)
    (h3 : as.length + bs.length = 3) (edge : ℕ) (p : GridRouting.Point) :
    fromAt width (.gen k as bs vs :: w) st edge p 0 = true ↔
      ∃ e : Strand k as.length bs.length r,
        strandLabel st e = edge ∧ (layer k as.length bs.length r h3).Trace e p := by
  rw [exists_strand]
  have hr : st.wires.length - (k + as.length) = r := by omega
  rw [fromAt_zero_data]
  by_cases hp : p.1 ≤ Strip.Sweep.drawingWidth width ∧ p.2 ≤ 4 * width + 6
  · let x : Fin (Strip.Sweep.drawingWidth width + 1) := ⟨p.1, by omega⟩
    let y : Fin (4 * width + 7) := ⟨p.2, by omega⟩
    have hi (i : Fin (k + as.length + r)) :
        (fromQuery (.gen k as bs vs :: w) st p 0 false i.val).test width =
          decide ((layer k as.length bs.length r h3).Trace (inputStrand i) p) := by
      change PushPuzzle.NCL.Word.DrawingData.LayerInput.test width
        ⟨st.wires.length - (k + as.length), k, as.length, bs.length, false, i.val, p.1, p.2⟩ = _
      rw [hr]
      exact PushPuzzle.NCL.Word.DrawingData.LayerInput.test_inputStrand ha hb h3 i x y
    have hj (j : Fin bs.length) :
        (fromQuery (.gen k as bs vs :: w) st p 0 true j.val).test width =
          decide ((layer k as.length bs.length r h3).Trace (.inr (.inl (.inr j))) p) := by
      change PushPuzzle.NCL.Word.DrawingData.LayerInput.test width
        ⟨st.wires.length - (k + as.length), k, as.length, bs.length, true, j.val, p.1, p.2⟩ = _
      rw [hr]
      exact PushPuzzle.NCL.Word.DrawingData.LayerInput.test_created ha hb h3 j x y
    simp only [hp, true_and, ite_true, Bool.or_eq_true, List.any_eq_true, List.mem_range,
      Bool.and_eq_true, beq_iff_eq, hs]
    constructor
    · rintro (⟨i, hi', he, ht⟩ | ⟨j, hj', he, ht⟩)
      · exact Or.inl ⟨⟨i, hi'⟩, he, of_decide_eq_true (hi ⟨i, hi'⟩ ▸ ht)⟩
      · exact Or.inr ⟨⟨j, hj'⟩, he, of_decide_eq_true (hj ⟨j, hj'⟩ ▸ ht)⟩
    · rintro (⟨i, he, ht⟩ | ⟨j, he, ht⟩)
      · exact Or.inl ⟨i.val, i.isLt, he, (hi i).symm ▸ decide_eq_true ht⟩
      · exact Or.inr ⟨j.val, j.isLt, he, (hj j).symm ▸ decide_eq_true ht⟩
  · have hn (e : Strand k as.length bs.length r)
        (he : (layer k as.length bs.length r h3).Trace e p) : False := by
      have hx := layer_trace_column_le h3 ha hb he
      have hy := (layer k as.length bs.length r h3).row_le e p he
      simp only [Layer.height] at hy
      omega
    simp only [hp, ite_false, Bool.false_eq_true, false_iff]
    rintro (⟨_, _, he⟩ | ⟨_, _, he⟩) <;> exact hn _ he

private theorem name_fromStrand (left as bs right : List Color)
    (v : Vertex (Fin as.length ⊕ Fin bs.length)) (st : Word.State)
    (e : Strand left.length as.length bs.length right.length) :
    (GridDrawing.Pad.diagram left as bs right v).name
      (fun i => st.wires.getD i.val 0) st.next
      (GridDrawing.Pad.fromStrand left as bs right v e) = strandLabel st e := by
  rcases e with i | ((i | j) | j)
  · rfl
  · rfl
  · change st.next + (0 + j.val) = st.next + j.val
    rw [Nat.zero_add]
  · rfl

private theorem first_layer_trace {width : ℕ} {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) (w : Word) (st : Word.State)
    (hs : st.wires.length = a.length) (ha : a.length ≤ width) (hb : b.length ≤ width)
    (edge : ℕ) (p : GridRouting.Point) :
    fromAt width (sl :: w) st edge p 0 = true ↔
      ∃ e : (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.Edge,
        (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.name (fun i => st.wires.getD i.val 0) st.next e = edge ∧
          (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L)).trace e p := by
  rcases L with ⟨left, inputs, outputs, right, v, hsl, hsource, htarget, hp, layout⟩
  have hsource' := hsource.trans (List.append_assoc left inputs right)
  have htarget' := htarget.trans (List.append_assoc left outputs right)
  subst sl
  cases hsource'
  cases htarget'
  have hthree := layout.arity
  have hsrc : st.wires.length = left.length + inputs.length + right.length := by
    simpa only [List.length_append, Nat.add_assoc] using hs
  have has : left.length + inputs.length + right.length ≤ width := by
    simpa only [List.length_append, Nat.add_assoc] using ha
  have hbs : left.length + outputs.length + right.length ≤ width := by
    simpa only [List.length_append, Nat.add_assoc] using hb
  rw [fromAt_zero inputs outputs [v] w st hsrc has hbs hthree]
  constructor
  · rintro ⟨e, he, ht⟩
    refine ⟨GridDrawing.Pad.fromStrand left inputs outputs right v e, ?_, ?_⟩
    · exact (name_fromStrand left inputs outputs right v st e).trans he
    · change ((GridDrawing.Cell.drawing v hp (layer _ _ _ _ layout.arity)).castBoundary
        (GridDrawing.Pad.boundary_length left inputs right)
        (GridDrawing.Pad.boundary_length left outputs right)).trace
          ((GridDrawing.Pad.edgeEquiv left inputs outputs right v)
            (GridDrawing.Pad.fromStrand left inputs outputs right v e)) p
      have hf : (GridDrawing.Pad.edgeEquiv left inputs outputs right v)
          (GridDrawing.Pad.fromStrand left inputs outputs right v e) = e :=
        (GridDrawing.Pad.edgeEquiv left inputs outputs right v).apply_symm_apply e
      rw [hf, castBoundary_trace]
      exact ht
  · rintro ⟨e, he, ht⟩
    let s := GridDrawing.Pad.edgeEquiv left inputs outputs right v e
    refine ⟨s, ?_, ?_⟩
    · have hh := name_fromStrand left inputs outputs right v st s
      have hf : GridDrawing.Pad.fromStrand left inputs outputs right v s = e :=
        (GridDrawing.Pad.edgeEquiv left inputs outputs right v).symm_apply_apply e
      rw [hf] at hh
      exact hh.symm.trans he
    · change ((GridDrawing.Cell.drawing v hp (layer _ _ _ _ layout.arity)).castBoundary
        (GridDrawing.Pad.boundary_length left inputs right)
        (GridDrawing.Pad.boundary_length left outputs right)).trace s p at ht
      rw [castBoundary_trace] at ht
      exact ht

private theorem layer_run_native {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) (st : Word.State) (hs : st.wires.length = a.length) :
    (sl.run st).next = st.next + (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.innerCount ∧
      ∀ j : Fin b.length, (sl.run st).wires.getD j.val 0 =
        (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.name (fun i => st.wires.getD i.val 0) st.next
          ((PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.bottom j) := by
  have hw : List.ofFn (fun i : Fin a.length => st.wires.getD i.val 0) = st.wires := by
    apply List.ext_getElem
    · simp [hs]
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj, Option.getD_some]
  have h := Diagram.run_toWord (I := Prim.interp) (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram 0 [] [] rfl
    (fun i => st.wires.getD i.val 0) st.next st.verts
  simp only [List.nil_append, List.append_nil, hw, (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).toWord_diagram,
    Word.run, List.foldl_cons, List.foldl_nil] at h
  constructor
  · exact congrArg Word.State.next h
  · intro j
    have hw := congrArg Word.State.wires h
    rw [hw]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, j.isLt,
      ↓reduceDIte, Option.getD_some]

private theorem fromTrace_eq {width : ℕ} {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (hclosed : b = []) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) a width)
    (st : Word.State) (hs : st.wires.length = a.length) (edge : ℕ) (p : GridRouting.Point) :
    fromTrace width w st edge p = true ↔
      ∃ e : (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.Edge,
        (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.name (fun i => st.wires.getD i.val 0) st.next e = edge ∧
          (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).trace e p := by
  induction D generalizing st p with
  | nil a =>
    subst a
    simp only [fromTrace, List.length_nil, List.range_zero, List.any_nil,
      Bool.false_eq_true, false_iff]
    rintro ⟨e, _, _⟩
    rcases e with i | e
    · exact i.elim0
    · exact e.elim
  | @cons sl w a b c L D ih =>
    have htyping : Word.WellTyped [sl] a b := by
      rw [← L.toWord_diagram]
      exact Diagram.wellTyped_toWord _ _
    have hb : b.length ≤ width := hwidth [sl] (List.prefix_append _ w) b htyping
    have hrest : (PushPuzzle.NCL.Word.WidthBound w) b width := hwidth.of_append_right htyping
    have hnext := layer_wires_length L st hs
    have hlabels := layer_run_native L st hs
    have hheight : (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L)).height =
        2 * st.wires.length + 2 * (sl.run st).wires.length + 6 := by
      rw [(PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric_height (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L)), layer_height, hs, hnext]
    have hright (e : (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.Edge) :
        ((PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.comp (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram).name
            (fun i => st.wires.getD i.val 0) st.next
            (compRight (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram e) =
          (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.name (fun i => (sl.run st).wires.getD i.val 0)
            (sl.run st).next e := by
      rw [name_compRight, hlabels.1]
      congr 1
      exact funext (fun j => (hlabels.2 j).symm)
    rw [fromTrace_cons, Bool.or_eq_true]
    change _ ↔ ∃ e : ((PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.comp (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram).Edge,
      _ ∧ GridDrawing.Comp.Trace (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L)) (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)) e p
    constructor
    · rintro (hl | hr)
      · obtain ⟨e, he, ht⟩ := (first_layer_trace L w st hs hwidth.start hb edge p).mp hl
        exact ⟨compLeft _ _ e, (name_compLeft _ _ _ _ _).trans he, Or.inl ⟨e, rfl, ht⟩⟩
      · split_ifs at hr with hd
        obtain ⟨e, he, ht⟩ := (ih hclosed hrest (sl.run st) hnext
          (p.1, p.2 - (2 * st.wires.length + 2 * (sl.run st).wires.length + 6))).mp hr
        refine ⟨compRight _ _ e, (hright e).trans he, Or.inr ?_⟩
        rw [← hheight] at hd ht
        exact ⟨hd, e, rfl, ht⟩
    · rintro ⟨e, he, ht⟩
      rcases ht with ⟨f, hf, ht⟩ | ⟨hd, f, hf, ht⟩
      · left
        apply (first_layer_trace L w st hs hwidth.start hb edge p).mpr
        exact ⟨f, (name_compLeft _ _ _ _ _).symm.trans ((congrArg
          (((PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.comp (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram).name
            (fun i => st.wires.getD i.val 0) st.next) hf).trans he), ht⟩
      · right
        have hd' : 2 * st.wires.length + 2 * (sl.run st).wires.length + 6 ≤ p.2 :=
          hheight ▸ hd
        rw [ite_eq_left hd']
        apply (ih hclosed hrest (sl.run st) hnext _).mpr
        refine ⟨f, (hright f).symm.trans ((congrArg
          (((PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.comp (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram).name
            (fun i => st.wires.getD i.val 0) st.next) hf).trans he), ?_⟩
        simpa only [hheight] using ht

/-- The standard native edge query evaluates the same original complete canonical word trace. -/
theorem TraceInput.trace_eq {width : ℕ} {w : Word} (D : w.OrthogonalDrawing [] [])
    (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width) (edge x y : ℕ) :
    (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w edge x y).trace width = true ↔
      ∃ e : (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.Edge, (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.num e = edge ∧
        (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).trace e (x, y) := by
  rw [trace_from]
  have h := fromTrace_eq D rfl hwidth ⟨[], 0, []⟩ rfl edge (x, y)
  have htop : (fun i : Fin 0 => ([] : List ℕ).getD i.val 0) = Fin.val := by
    funext i
    exact i.elim0
  simpa only [Diagram.num, List.length_nil, htop] using h

end PushPuzzle.NCL.Word.DrawingData
