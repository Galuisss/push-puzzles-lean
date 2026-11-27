/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortGeometry
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.GetD

/-!
# Fresh edge numbers along the actual source compilation

Every live wire has a distinct number smaller than the next allocated number.
A gate consumes previous numbers and creates fresh numbers. In particular its
three incidences name distinct edges, including before the final graph check.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- The live cut has no duplicated edge and contains only already allocated numbers. -/
structure Numbered (st : Word.State) : Prop where
  /-- Each active edge crosses the cut once. -/
  nodup : st.wires.Nodup
  /-- Active edges precede the next unused number. -/
  bounded : ∀ e ∈ st.wires, e < st.next

private theorem numbered_gen (st : Word.State) (h : Numbered st)
    (k : ℕ) (a b : List Color) (vs : List (Vertex (Fin a.length ⊕ Fin b.length))) :
    Numbered ((Slice.gen k a b vs).run st) := by
  let ns := List.ofFn (fun j : Fin b.length => st.next + j.val)
  have hn : ns.Nodup := List.nodup_ofFn.mpr (by
    intro i j he
    apply Fin.ext
    dsimp only at he
    omega)
  have hnLower : ∀ e ∈ ns, st.next ≤ e := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    omega
  have hnUpper : ∀ e ∈ ns, e < st.next + b.length := by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    have := i.isLt
    omega
  have hp : (st.wires.take k).Nodup := h.nodup.sublist (List.take_sublist ..)
  have hs : (st.wires.drop (k + a.length)).Nodup := h.nodup.sublist (List.drop_sublist ..)
  have hpn : (st.wires.take k).Disjoint ns := by
    apply List.disjoint_left.mpr
    intro e he hn
    have := h.bounded e (List.mem_of_mem_take he)
    have := hnLower e hn
    omega
  have hps : (st.wires.take k).Disjoint (st.wires.drop (k + a.length)) :=
    List.disjoint_take_drop h.nodup (by omega)
  have hns : ns.Disjoint (st.wires.drop (k + a.length)) := by
    apply List.disjoint_left.mpr
    intro e he hs
    have := h.bounded e (List.mem_of_mem_drop hs)
    have := hnLower e he
    omega
  refine ⟨?_, ?_⟩
  · change ((st.wires.take k ++ ns) ++ st.wires.drop (k + a.length)).Nodup
    exact (hp.append hn hpn).append hs (by
      apply List.disjoint_left.mpr
      intro e he hs
      rcases List.mem_append.mp he with he | he
      · exact List.disjoint_left.mp hps he hs
      · exact List.disjoint_left.mp hns he hs)
  · intro e he
    change e ∈ (st.wires.take k ++ ns) ++ st.wires.drop (k + a.length) at he
    change e < st.next + b.length
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact (h.bounded e (List.mem_of_mem_take he)).trans_le (Nat.le_add_right ..)
      · exact hnUpper e he
    · exact (h.bounded e (List.mem_of_mem_drop he)).trans_le (Nat.le_add_right ..)

/-- Any plane generator preserves the fresh-number invariant. -/
theorem Numbered.step {st : Word.State} (h : Numbered st) {sl : Slice}
    (hsl : sl.data.isSwap = false) : Numbered (sl.run st) := by
  cases sl with
  | gen k a b vs => exact numbered_gen st h k a b vs
  | swap k => cases hsl

/-- Looking up a real active edge always returns an allocated number. -/
theorem Numbered.getD_lt {st : Word.State} (h : Numbered st) {i : ℕ}
    (hi : i < st.wires.length) : st.wires.getD i 0 < st.next := by
  rw [List.getD_eq_getElem _ _ hi]
  exact h.bounded _ (List.getElem_mem hi)

/-- Valid cut indices are determined by the edge number stored there. -/
theorem Numbered.getD_injective {st : Word.State} (h : Numbered st) {i j : ℕ}
    (hi : i < st.wires.length) (hj : j < st.wires.length)
    (he : st.wires.getD i 0 = st.wires.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at he
  have hij := h.nodup.injective_get (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) he
  exact congrArg Fin.val hij

/-- An active edge can occur in a prefix only at its unique cut index. -/
theorem Numbered.index_lt_of_mem_take {st : Word.State} (h : Numbered st) {i k : ℕ}
    (hi : i < st.wires.length) (hm : st.wires.getD i 0 ∈ st.wires.take k) : i < k := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  have hj' : j < st.wires.length := by simp only [List.length_take] at hj; omega
  have he' : st.wires.getD j 0 = st.wires.getD i 0 := by
    simpa only [List.getD_eq_getElem _ _ hj', List.getElem_take] using he
  have hij := h.getD_injective hj' hi he'
  simp only [List.length_take] at hj
  omega

/-- An active edge can occur in a suffix only after that suffix's cut. -/
theorem Numbered.le_index_of_mem_drop {st : Word.State} (h : Numbered st) {i k : ℕ}
    (hi : i < st.wires.length) (hm : st.wires.getD i 0 ∈ st.wires.drop k) : k ≤ i := by
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hm
  have hj' : k + j < st.wires.length := by simp only [List.length_drop] at hj; omega
  have he' : st.wires.getD (k + j) 0 = st.wires.getD i 0 := by
    simpa only [List.getD_eq_getElem _ _ hj', List.getElem_drop] using he
  have hij := h.getD_injective hj' hi he'
  omega

/-- Different consumed input ports have different source edge numbers. -/
theorem Layer.input_edges_injective {l : Layer} (hn : Numbered l.before)
    (h : l.HasDrawing) : Function.Injective (fun i : Fin l.instruction.data.inputs.length =>
      (l.inputPort i.val).port.edge) := by
  intro i j hij
  have hk := h.constraints.2.2.1
  have hi : l.instruction.data.offset + i.val < l.before.wires.length := by have := i.isLt; omega
  have hj : l.instruction.data.offset + j.val < l.before.wires.length := by have := j.isLt; omega
  change l.before.wires.getD (l.instruction.data.offset + i.val) 0 =
    l.before.wires.getD (l.instruction.data.offset + j.val) 0 at hij
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hij
  have he := hn.nodup.injective_get (a₁ := ⟨_, hi⟩) (a₂ := ⟨_, hj⟩) hij
  have he' := congrArg Fin.val he
  change l.instruction.data.offset + i.val = l.instruction.data.offset + j.val at he'
  apply Fin.ext
  omega

/-- Every output port names a freshly allocated edge. -/
theorem Layer.output_edges_injective (l : Layer) :
    Function.Injective (fun i : Fin l.instruction.data.outputs.length =>
      (l.outputPort i.val).port.edge) := by
  intro i j hij
  apply Fin.ext
  change l.before.next + i.val = l.before.next + j.val at hij
  omega

/-- A source edge entering the gate is distinct from every edge created there. -/
theorem Layer.input_ne_output {l : Layer} (hn : Numbered l.before)
    (h : l.HasDrawing) (i : Fin l.instruction.data.inputs.length)
    (j : Fin l.instruction.data.outputs.length) :
    (l.inputPort i.val).port.edge ≠ (l.outputPort j.val).port.edge := by
  have hk := h.constraints.2.2.1
  have hi : l.instruction.data.offset + i.val < l.before.wires.length := by have := i.isLt; omega
  have he := hn.getD_lt hi
  change l.before.wires.getD (l.instruction.data.offset + i.val) 0 ≠ l.before.next + j.val
  omega

end PushPuzzle.PushFS.Reduction.Plan
