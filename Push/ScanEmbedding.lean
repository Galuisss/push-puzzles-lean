/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Scan
import all Push.Scan

/-! Exact line-scan transport, empty-position skipping, and untouched auxiliary holes. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

/-- Every line is enumerated strictly away from its selected boundary. -/
theorem lineCells_pairwise {w h : ℕ} (side : Direction) (lane : ℕ) :
    (lineCells (w := w) (h := h) side lane).Pairwise
      (fun a b => side.position b < side.position a) := by
  cases side with
  | north =>
    simp only [lineCells]
    split
    · rw [List.pairwise_ofFn]
      intro i j hij
      change -(j.val : ℤ) < -(i.val : ℤ)
      omega
    · exact .nil
  | east =>
    simp only [lineCells]
    split
    · rw [List.pairwise_reverse, List.pairwise_ofFn]
      intro i j hij
      change (i.val : ℤ) < (j.val : ℤ)
      omega
    · exact .nil
  | south =>
    simp only [lineCells]
    split
    · rw [List.pairwise_reverse, List.pairwise_ofFn]
      intro i j hij
      change (i.val : ℤ) < (j.val : ℤ)
      omega
    · exact .nil
  | west =>
    simp only [lineCells]
    split
    · rw [List.pairwise_ofFn]
      intro i j hij
      change -(j.val : ℤ) < -(i.val : ℤ)
      omega
    · exact .nil

/-- Relabelling every cell transports both the consumed prefix and its exact remainder. -/
theorem consume_map {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ↪ β)
    (cells : List α) (quota : ℕ) (E : Finset α) :
    consume (cells.map e) quota (E.map e) =
      (consume cells quota E).map (Finset.map e) := by
  induction cells generalizing quota E with
  | nil => cases quota <;> rfl
  | cons a cells ih =>
    cases quota with
    | zero => rfl
    | succ q =>
      have hm : e a ∈ E.map e ↔ a ∈ E := by simp only [Finset.mem_map, e.injective.eq_iff, exists_eq_right]
      by_cases ha : a ∈ E
      · simp only [List.map_cons, consume, ite_eq_left ha, ite_eq_left (hm.mpr ha)]
        rw [← Finset.map_erase]
        exact ih q (E.erase a)
      · simp only [List.map_cons, consume, ite_eq_right ha,
          ite_eq_right (fun hh => ha (hm.mp hh))]
        exact ih (q + 1) E


/-- Auxiliary holes outside the traversed line remain untouched by the entire read. -/
theorem consume_union {α : Type*} [DecidableEq α] (cells : List α) (quota : ℕ)
    (E A : Finset α) (hA : ∀ a ∈ cells, a ∉ A) :
    consume cells quota (E ∪ A) = (consume cells quota E).map (· ∪ A) := by
  induction cells generalizing quota E with
  | nil => cases quota <;> rfl
  | cons a cells ih =>
    cases quota with
    | zero => rfl
    | succ q =>
      have haA := hA a (List.mem_cons_self ..)
      have htA : ∀ b ∈ cells, b ∉ A := fun b hb => hA b (List.mem_cons_of_mem a hb)
      by_cases ha : a ∈ E
      · have haU : a ∈ E ∪ A := Finset.mem_union_left _ ha
        simp only [consume, ite_eq_left haU, ite_eq_left ha]
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem haA]
        exact ih q (E.erase a) htA
      · have haU : a ∉ E ∪ A := by simpa only [Finset.mem_union, not_or] using And.intro ha haA
        simp only [consume, ite_eq_right haU, ite_eq_right ha]
        exact ih (q + 1) E htA

/-- Positions which contain no current hole can be removed from the traversed cell list. -/
theorem consume_filter {α : Type*} [DecidableEq α] (keep : α → Bool)
    (cells : List α) (quota : ℕ) (E : Finset α)
    (hs : ∀ a ∈ cells, a ∈ E → keep a = true) :
    consume (cells.filter keep) quota E = consume cells quota E := by
  induction cells generalizing quota E with
  | nil => rfl
  | cons a cells ih =>
    cases quota with
    | zero => simp only [consume]
    | succ q =>
      have ht : ∀ b ∈ cells, b ∈ E → keep b = true :=
        fun b hb => hs b (List.mem_cons_of_mem a hb)
      cases hk : keep a with
      | false =>
        have ha : a ∉ E := by
          intro ha
          have := hs a (List.mem_cons_self ..) ha
          rw [hk] at this
          cases this
        simp only [List.filter_cons, hk, Bool.false_eq_true, ite_false, consume, ite_eq_right ha]
        exact ih (q + 1) E ht
      | true =>
        simp only [List.filter_cons, hk, ite_true, consume]
        by_cases ha : a ∈ E
        · simp only [ite_eq_left ha]
          exact ih q (E.erase a) (fun b hb he => ht b hb (Finset.mem_of_mem_erase he))
        · simp only [ite_eq_right ha]
          exact ih (q + 1) E ht

/-- The instruction's selected lines avoid every hole in the preserved inventory. -/
@[expose] def Instruction.Avoids {w h : ℕ} (A : Finset (Cell w h)) : Instruction w h → Prop
  | .read side lane _ => ∀ q ∈ A, side.lane q ≠ lane
  | .clear side lanes => ∀ q ∈ A, side.lane q ∉ lanes

/-- A static instruction keeps any off-line inventory exactly fixed. -/
theorem Instruction.eval_union {w h : ℕ} (i : Instruction w h) (E A : Finset (Cell w h))
    (hA : i.Avoids A) : i.eval (E ∪ A) = (i.eval E).map (· ∪ A) := by
  cases i with
  | read side lane quota =>
    exact consume_union _ _ _ _ (by
      intro q hq ha
      exact hA q ha ((mem_lineCells side lane q).mp hq))
  | clear side lanes =>
    change some ((E ∪ A).filter _) = some ((E.filter _) ∪ A)
    rw [Finset.filter_union, Finset.filter_eq_self.mpr hA]

/-- A successful instruction preserves each cell outside its selected lines. -/
private theorem Instruction.mem_eval_outside {w h : ℕ} {i : Instruction w h} {E F : Finset
    (Cell w h)}
    (hh : i.eval E = some F) {p : Cell w h} (hp : i.Avoids {p}) : p ∈ F ↔ p ∈ E := by
  cases i with
  | read side lane quota => exact Instruction.read_outside hh (hp p (Finset.mem_singleton_self _))
  | clear side lanes =>
    have he : E.filter (fun q => side.lane q ∉ lanes) = F := Option.some.inj hh
    rw [← he]
    rw [Finset.mem_filter]
    exact ⟨And.left, fun h => ⟨h, hp p (Finset.mem_singleton_self _)⟩⟩

/-- A successful static program preserves every cell avoided by all its instructions. -/
theorem eval_mem_outside {w h : ℕ} {program : List (Instruction w h)} {E F : Finset (Cell w h)}
    (hh : eval program E = some F) {p : Cell w h}
    (hp : ∀ i ∈ program, i.Avoids {p}) : p ∈ F ↔ p ∈ E := by
  induction program generalizing E with
  | nil =>
    have he : E = F := Option.some.inj hh
    rw [he]
  | cons i rest ih =>
    simp only [eval, Option.bind_eq_some_iff] at hh
    obtain ⟨G, hi, ht⟩ := hh
    exact (ih ht (fun j hj => hp j (List.mem_cons_of_mem i hj))).trans
      (Instruction.mem_eval_outside hi (hp i (List.mem_cons_self ..)))

/-- Successful static reads and clears only delete holes. -/
theorem eval_subset {w h : ℕ} {program : List (Instruction w h)} {E F : Finset (Cell w h)}
    (hh : eval program E = some F) : F ⊆ E := by
  induction program generalizing E with
  | nil =>
    have he : E = F := Option.some.inj hh
    exact he ▸ Finset.Subset.refl _
  | cons i rest ih =>
    simp only [eval, Option.bind_eq_some_iff] at hh
    obtain ⟨G, hi, ht⟩ := hh
    exact (ih ht).trans (Instruction.eval_subset hi)

end PushPuzzle.Push.Scan
