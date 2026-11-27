/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CutConnections

/-! Exact upper and lower cut incidences of the source layer's middle strands. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

/-- The top row of a computed band meets each path at its actual source column only. -/
theorem Band.curve_top (b : Band) (i : Fin b.source.length) (p : GridRouting.Point)
    (hy : p.2 = 0) (hp : ∃ s ∈ Band.curve (b, i.val), s.Contains p) :
    p.1 = b.source.getD i.val 0 := by
  have hi := i.isLt
  obtain ⟨s, hs, hp⟩ := hp
  simp only [Band.curve, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Segment.Contains] at hp <;> omega

/-- The bottom row of a computed band meets each path at its actual target column only. -/
theorem Band.curve_bottom (b : Band) (i : Fin b.source.length) (p : GridRouting.Point)
    (hy : p.2 = 2 * (b.source.length + 1))
    (hp : ∃ s ∈ Band.curve (b, i.val), s.Contains p) :
    p.1 = b.target.getD i.val 0 := by
  have hi := i.isLt
  obtain ⟨s, hs, hp⟩ := hp
  simp only [Band.curve, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Segment.Contains] at hp <;> omega

/-- Translate all segments and reflect their entire trace at an arbitrary point. -/
theorem Segment.mem_translate_iff (ss : List Segment) (dx dy : ℕ) (p : GridRouting.Point) :
    (∃ s ∈ ss.map (fun t => t.translate dx dy), s.Contains p) ↔
      dx ≤ p.1 ∧ dy ≤ p.2 ∧ ∃ s ∈ ss, s.Contains (p.1 - dx, p.2 - dy) := by
  simp only [List.mem_map, exists_exists_and_eq_and, Segment.contains_translate]
  constructor
  · rintro ⟨s, hs, hx, hy, hp⟩
    exact ⟨hx, hy, s, hs, hp⟩
  · rintro ⟨hx, hy, s, hs, hp⟩
    exact ⟨s, hs, hx, hy, hp⟩

namespace Plan

/-- The exact middle strand attached to a real upper cut position. -/
def Layer.topStrand (l : Layer) (i : Fin l.before.wires.length) : l.Strand :=
  if hp : i.val < l.instruction.data.offset then .inl ⟨i.val, hp⟩
  else if hg : i.val < l.instruction.data.offset + l.instruction.data.inputs.length then
    .inr (.inl (.inl ⟨i.val - l.instruction.data.offset, by omega⟩))
  else .inr (.inr ⟨i.val - (l.instruction.data.offset + l.instruction.data.inputs.length), by
    have := i.isLt
    omega⟩)

/-- The exact middle strand attached to a real lower cut position. -/
def Layer.bottomStrand {l : Layer} (h : l.HasDrawing) (i : Fin l.after.wires.length) : l.Strand :=
  if hp : i.val < l.instruction.data.offset then .inl ⟨i.val, hp⟩
  else if hg : i.val < l.instruction.data.offset + l.instruction.data.outputs.length then
    .inr (.inl (.inr ⟨i.val - l.instruction.data.offset, by omega⟩))
  else .inr (.inr ⟨i.val - (l.instruction.data.offset + l.instruction.data.outputs.length), by
    have := i.isLt
    obtain ⟨_, _, hk, hn⟩ := h.constraints
    omega⟩)

/-- The selected upper strand starts at the actual expanded upper port. -/
theorem Layer.topStrand_start (l : Layer) (i : Fin l.before.wires.length) :
    GridLayout.middleStart (l.topStrand i) =
      (expanded l.instruction.data.offset l.instruction.data.inputs.length i.val, 0) := by
  unfold Layer.topStrand expanded
  split_ifs <;> simp [GridLayout.middleStart, Nat.add_comm]

/-- The selected lower strand ends at the actual expanded lower port. -/
theorem Layer.bottomStrand_end {l : Layer} (h : l.HasDrawing) (i : Fin l.after.wires.length) :
    GridLayout.middleEnd (l.bottomStrand h i) =
      (expanded l.instruction.data.offset l.instruction.data.outputs.length i.val, 2) := by
  unfold Layer.bottomStrand expanded
  split_ifs <;> simp [GridLayout.middleEnd, Nat.add_comm]

/-- The selected upper strand retains exactly that live source edge name. -/
theorem Layer.topStrand_edge (l : Layer) (i : Fin l.before.wires.length) :
    (l.strandRoute (l.topStrand i)).edge = l.before.wires.getD i.val 0 := by
  unfold Layer.topStrand
  split_ifs with hp hg
  · simp [Layer.strandRoute, Layer.prefixRoutes, List.getD_eq_getElem?_getD, hp]
  · have hi : i.val - l.instruction.data.offset < l.instruction.data.inputs.length := by omega
    have he : l.instruction.data.offset + (i.val - l.instruction.data.offset) = i.val := by omega
    simp [Layer.strandRoute, Layer.inputRoutes, Layer.inputPort, List.getD_eq_getElem?_getD, hi, he]
  · have hi : i.val - (l.instruction.data.offset + l.instruction.data.inputs.length) <
        l.before.wires.length - (l.instruction.data.offset + l.instruction.data.inputs.length) := by
      have := i.isLt
      omega
    have he : l.instruction.data.offset + l.instruction.data.inputs.length +
        (i.val - (l.instruction.data.offset + l.instruction.data.inputs.length)) = i.val := by omega
    simp [Layer.strandRoute, Layer.suffixRoutes, List.getD_eq_getElem?_getD, hi, he]

/-- The selected lower strand retains exactly that actual next-cut edge name. -/
theorem Layer.bottomStrand_edge {l : Layer} (h : l.HasDrawing) (i : Fin l.after.wires.length) :
    (l.strandRoute (l.bottomStrand h i)).edge = l.after.wires.getD i.val 0 := by
  unfold Layer.bottomStrand
  split_ifs with hp hg
  · rw [l.after_prefix h i.val hp]
    simp [Layer.strandRoute, Layer.prefixRoutes, List.getD_eq_getElem?_getD, hp]
  · have hi : i.val - l.instruction.data.offset < l.instruction.data.outputs.length := by omega
    have he : l.instruction.data.offset + (i.val - l.instruction.data.offset) = i.val := by omega
    simpa [Layer.strandRoute, Layer.outputRoutes, Layer.outputPort, List.getD_eq_getElem?_getD, hi, he] using
      (l.after_output h ⟨i.val - l.instruction.data.offset, hi⟩).symm
  · have hi : i.val - (l.instruction.data.offset + l.instruction.data.outputs.length) <
        l.before.wires.length - (l.instruction.data.offset + l.instruction.data.inputs.length) := by
      have := i.isLt
      obtain ⟨_, _, hk, hn⟩ := h.constraints
      omega
    have he : l.instruction.data.offset + l.instruction.data.outputs.length +
        (i.val - (l.instruction.data.offset + l.instruction.data.outputs.length)) = i.val := by omega
    simpa [Layer.strandRoute, Layer.suffixRoutes, List.getD_eq_getElem?_getD, hi, he] using
      (l.after_suffix h (i.val - (l.instruction.data.offset + l.instruction.data.outputs.length))).symm

/-- The real incoming program consists of its upper route, actual middle strand and optional lower route. -/
theorem Layer.incoming_decompose (l : Layer) (i : Fin l.before.wires.length) :
    (l.incomingRoute i.val).path = Band.curve (l.upperBand, i.val) ++
      (l.strandRoute (l.topStrand i)).path ++ (l.exitIndex i.val).elim [] l.bottomPath := by
  unfold Layer.incomingRoute Layer.topStrand Layer.exitIndex
  dsimp only
  split_ifs <;> simp_all only [Layer.strandRoute, Option.elim_some, Option.elim_none, List.append_nil]

end Plan
end PushPuzzle.PushFS.Reduction
