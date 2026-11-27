/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerGeometry
public import PushFS.Reduction.GateBinding

/-!
# The geometric cyclic order of each numbered source vertex

The upper ports occur from left to right; the lower ports occur from right to
left. Their weights, edge numbers and reference directions are the actual
source data. This cyclic order binds the fixed physical gate to its three
external routes.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- The actual numbered input port at a source layer. -/
def Layer.inputPort (l : Layer) (i : ℕ) : WeightedPort ℕ :=
  ⟨⟨l.before.wires.getD (l.instruction.data.offset + i) 0, true⟩,
    (l.instruction.data.inputs.getD i .red).weight⟩

/-- The actual newly numbered output port at a source layer. -/
def Layer.outputPort (l : Layer) (i : ℕ) : WeightedPort ℕ :=
  ⟨⟨l.before.next + i, false⟩, (l.instruction.data.outputs.getD i .red).weight⟩

/-- Clockwise incidence order in the three-port cell drawing. -/
def Layer.circularPorts (l : Layer) : List (WeightedPort ℕ) :=
  (List.range l.instruction.data.inputs.length).map l.inputPort ++
    ((List.range l.instruction.data.outputs.length).map l.outputPort).reverse

/-- The real source constraint with its ports in geometric cyclic order. -/
def Layer.geometricVertex (l : Layer) : Vertex ℕ := ⟨l.circularPorts, 2⟩

private theorem finRange_map {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    rfl

/-- Every planned three-port layer emits exactly one vertex with these weighted incidences. -/
theorem Layer.HasDrawing.geometric_incidence {l : Layer} (h : l.HasDrawing) :
    ∃ v : Vertex ℕ, emitted l = [v] ∧ v.ports.Perm l.geometricVertex.ports := by
  obtain ⟨source, target, D, hlen⟩ := h
  rcases D with ⟨left, a, b, right, v, hsl, hs, ht, hp, layout⟩
  let f : Fin a.length ⊕ Fin b.length → ℕ := Sum.elim
    (fun i => l.before.wires.getD (left.length + i.val) 0)
    (fun j => l.before.next + j.val)
  refine ⟨v.map f, ?_, ?_⟩
  · simp [emitted, hsl, Slice.run, f]
  · have hm := hp.map (WeightedPort.map f)
    change v.ports.map _ |>.Perm _ at hm
    apply hm.trans
    simp only [Diagram.genVertex, List.map_append, List.map_map]
    change ((List.finRange a.length).map (fun i =>
      (⟨⟨l.before.wires.getD (left.length + i.val) 0, true⟩, (a.get i).weight⟩ : WeightedPort ℕ)) ++
      (List.finRange b.length).map (fun i =>
      (⟨⟨l.before.next + i.val, false⟩, (b.get i).weight⟩ : WeightedPort ℕ))).Perm _
    have hi (i : Fin a.length) : a.get i = a.getD i.val .red := by simp [List.getD_eq_getElem?_getD]
    have ho (i : Fin b.length) : b.get i = b.getD i.val .red := by simp [List.getD_eq_getElem?_getD]
    simp only [hi, ho]
    rw [finRange_map a.length (fun i => (⟨⟨l.before.wires.getD (left.length + i) 0, true⟩, (a.getD i .red).weight⟩ : WeightedPort ℕ)),
      finRange_map b.length (fun i => (⟨⟨l.before.next + i, false⟩, (b.getD i .red).weight⟩ : WeightedPort ℕ))]
    have hI : l.inputPort = (fun i => (⟨⟨l.before.wires.getD (left.length + i) 0, true⟩,
        (a.getD i .red).weight⟩ : WeightedPort ℕ)) := by
      funext i
      simp [Layer.inputPort, hsl, Slice.data]
    have hO : l.outputPort = (fun i => (⟨⟨l.before.next + i, false⟩,
        (b.getD i .red).weight⟩ : WeightedPort ℕ)) := by
      funext i
      simp [Layer.outputPort, hsl, Slice.data]
    simp only [Layer.geometricVertex, Layer.circularPorts, hsl, Slice.data, hI, hO]
    apply List.Perm.append_left
    exact List.reverse_perm _ |>.symm

/-- Geometric ordering preserves both the source AND/OR kind and its complete constraint. -/
theorem Layer.geometric_correct {w : Word} (hw : (Word.compile w).Valid)
    {l : Layer} (hl : l ∈ annotate w) (h : l.HasDrawing) :
    l.geometricVertex.IsAndOr ∧ ∀ s, l.geometricVertex.Sat s ↔
      ∀ v ∈ emitted l, v.Sat s := by
  obtain ⟨v, hv, hp⟩ := h.geometric_incidence
  have hvAO := emitted_isAndOr hw hl (show v ∈ emitted l by rw [hv]; simp)
  have hm : v.minInflow = 2 := (orderPorts_correct hvAO).1
  have hg : l.geometricVertex.IsAndOr := by
    rcases hvAO with ⟨a, b, c, _, habc⟩ | ⟨a, b, c, _, habc⟩
    · exact Or.inl ⟨a, b, c, rfl, hp.symm.trans habc⟩
    · exact Or.inr ⟨a, b, c, rfl, hp.symm.trans habc⟩
  refine ⟨hg, fun s => ?_⟩
  rw [hv]
  simpa only [List.mem_singleton, forall_eq] using
    (Vertex.sat_iff_of_perm hp hm s).symm

@[fun_prop] theorem Layer.inputPort_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.inputPort q.2)
      (encPair encLayer encUnary) (encWeightedPort encNat) := by
  let : Fintype Color := ⟨{.red, .blue}, by intro c; cases c <;> simp⟩
  have hc : ComputableInPolyTime Color.weight encColor encNat := of_finite _
  have he : ComputableInPolyTime (fun q : Layer × ℕ =>
      q.1.before.wires.getD (q.1.instruction.data.offset + q.2) 0)
      (encPair encLayer encUnary) encUnary := by fun_prop
  have heb := ComputableInPolyTime.unary_to_binary.comp he
  unfold Layer.inputPort
  fun_prop

@[fun_prop] theorem Layer.outputPort_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.outputPort q.2)
      (encPair encLayer encUnary) (encWeightedPort encNat) := by
  let : Fintype Color := ⟨{.red, .blue}, by intro c; cases c <;> simp⟩
  have hc : ComputableInPolyTime Color.weight encColor encNat := of_finite _
  have he : ComputableInPolyTime (fun q : Layer × ℕ => q.1.before.next + q.2)
      (encPair encLayer encUnary) encUnary := by fun_prop
  have heb := ComputableInPolyTime.unary_to_binary.comp he
  unfold Layer.outputPort
  fun_prop

@[fun_prop] theorem Layer.circularPorts_polyTime :
    ComputableInPolyTime Layer.circularPorts encLayer (encList (encWeightedPort encNat)) := by
  unfold Layer.circularPorts
  fun_prop

@[fun_prop] theorem Layer.geometricVertex_polyTime :
    ComputableInPolyTime Layer.geometricVertex encLayer (encVertex encNat) := by
  unfold Layer.geometricVertex
  fun_prop

end PushPuzzle.PushFS.Reduction.Plan
