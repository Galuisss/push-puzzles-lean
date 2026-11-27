/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionTools

/-! Complete actual routing programs, holding their first low and last high interfaces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Action

open PushFS
variable {last : Bool}

private theorem cut_trans {w : ℕ} {hw : 2 ≤ w} {atoms : List Atom} {above : Bool} {a b b' c : ℕ}
    (h : Reachable (macroBoard (last:=last) w atoms above) (some 1) ⟨outerHub w atoms, cutBoxes w hw a atoms⟩
      ⟨outerHub w atoms, cutBoxes w hw b atoms⟩)
    (h' : Reachable (macroBoard (last:=last) w atoms above) (some 1) ⟨outerHub w atoms, cutBoxes w hw b' atoms⟩
      ⟨outerHub w atoms, cutBoxes w hw c atoms⟩) (he : b = b') :
    Reachable (macroBoard (last:=last) w atoms above) (some 1) ⟨outerHub w atoms, cutBoxes w hw a atoms⟩
      ⟨outerHub w atoms, cutBoxes w hw c atoms⟩ := by
  subst b'
  exact h.trans h'

private theorem cut_congr {w : ℕ} {hw : 2 ≤ w} {atoms : List Atom} {above : Bool} {a b a' b' : ℕ}
    (h : Reachable (macroBoard (last:=last) w atoms above) (some 1) ⟨outerHub w atoms, cutBoxes w hw a atoms⟩
      ⟨outerHub w atoms, cutBoxes w hw b atoms⟩) (ha : a = a') (hb : b = b') :
    Reachable (macroBoard (last:=last) w atoms above) (some 1) ⟨outerHub w atoms, cutBoxes w hw a' atoms⟩
      ⟨outerHub w atoms, cutBoxes w hw b' atoms⟩ := by
  subst a' b'
  exact h

set_option maxHeartbeats 3000000 in
private theorem initial_high_low (w : ℕ) (hw : 2 ≤ w) (t : ℕ) (ht : buffer w ≤ t)
    (switch odd above : Bool) :
    Reachable (macroBoard (last:=last) w (initialAtoms w switch odd++[.line t]) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw 1 (initialAtoms w switch odd++[.line t])⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (initialAtoms w switch odd++[.line t])) (initialAtoms w switch odd++[.line t])⟩ := by
  have hb : 0 < buffer w := by unfold buffer; omega
  cases switch <;> cases odd
  · simp only [initialAtoms, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line t], rfl⟩
    have h0 := Stock.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_high_low (last:=last) w hw [] [.flip,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.flip,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above
    have h4 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 ⊢
    have result := h0
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h4 (by omega)
    exact cut_congr result (by omega) (by omega)
  · simp only [initialAtoms, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line (buffer w),.parity,.line t], rfl⟩
    have h0 := Stock.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h4 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) (by omega) above ha hflip
    have h5 := Parity.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above hflip
    have h6 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 ⊢
    have result := h0
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h4 (by omega)
    have result := cut_trans result h5 (by omega)
    have result := cut_trans result h6 (by omega)
    exact cut_congr result (by omega) (by omega)
  · simp only [initialAtoms, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line (buffer w),.flip,.line t], rfl⟩
    have h0 := Stock.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.flip,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h4 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line t] (buffer w) (by omega) above ha hflip
    have h5 := Flip.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above
    have h6 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 ⊢
    have result := h0
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h4 (by omega)
    have result := cut_trans result h5 (by omega)
    have result := cut_trans result h6 (by omega)
    exact cut_congr result (by omega) (by omega)
  · simp only [initialAtoms, ite_true, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t], rfl⟩
    have h0 := Stock.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_high_low (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_high_low (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h4 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h5 := Flip.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h6 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) (by omega) above ha hflip
    have h7 := Parity.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above hflip
    have h8 := Stock.sweep_high_low (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    have result := h0
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h4 (by omega)
    have result := cut_trans result h5 (by omega)
    have result := cut_trans result h6 (by omega)
    have result := cut_trans result h7 (by omega)
    have result := cut_trans result h8 (by omega)
    exact cut_congr result (by omega) (by omega)

set_option maxHeartbeats 3000000 in
private theorem initial_low_high (w : ℕ) (hw : 2 ≤ w) (t : ℕ) (ht : buffer w ≤ t)
    (switch odd above : Bool) :
    Reachable (macroBoard (last:=last) w (initialAtoms w switch odd++[.line t]) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (initialAtoms w switch odd++[.line t])) (initialAtoms w switch odd++[.line t])⟩
      ⟨outerHub w _, cutBoxes w hw 1 (initialAtoms w switch odd++[.line t])⟩ := by
  have hb : 0 < buffer w := by unfold buffer; omega
  cases switch <;> cases odd
  · simp only [initialAtoms, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line t], rfl⟩
    have h0 := Stock.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_low_high (last:=last) w hw [] [.flip,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.flip,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above
    have h4 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 ⊢
    have result := h4
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h0 (by omega)
    exact cut_congr result (by omega) (by omega)
  · simp only [initialAtoms, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line (buffer w),.parity,.line t], rfl⟩
    have h0 := Stock.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h4 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) (by omega) above ha hflip
    have h5 := Parity.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above hflip
    have h6 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 ⊢
    have result := h6
    have result := cut_trans result h5 (by omega)
    have result := cut_trans result h4 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h0 (by omega)
    exact cut_congr result (by omega) (by omega)
  · simp only [initialAtoms, Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line (buffer w),.flip,.line t], rfl⟩
    have h0 := Stock.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.flip,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h4 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line t] (buffer w) (by omega) above ha hflip
    have h5 := Flip.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above
    have h6 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 ⊢
    have result := h6
    have result := cut_trans result h5 (by omega)
    have result := cut_trans result h4 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h0 (by omega)
    exact cut_congr result (by omega) (by omega)
  · simp only [initialAtoms, ite_true, List.cons_append, List.nil_append]
    have ha : ∀ a ∈ ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom), a.Valid w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact ht | exact le_rfl | trivial
    have hflip : ∃ left right, ([.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] : List Atom) = left++ .flip::right := ⟨[.line (buffer w)], [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t], rfl⟩
    have h0 := Stock.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h1 := Flip.sweep_low_high (last:=last) w hw [] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h2 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h3 := Flip.sweep_low_high (last:=last) w hw [.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h4 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) (by omega) above ha hflip
    have h5 := Flip.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) (buffer w) (by omega) (by omega) above
    have h6 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) (by omega) above ha hflip
    have h7 := Parity.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [] (buffer w) t (by omega) (by omega) above hflip
    have h8 := Stock.sweep_low_high (last:=last) w hw [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] t (by omega) above ha hflip
    simp only [ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.zero_add, List.cons_append, List.nil_append] at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
    have result := h8
    have result := cut_trans result h7 (by omega)
    have result := cut_trans result h6 (by omega)
    have result := cut_trans result h5 (by omega)
    have result := cut_trans result h4 (by omega)
    have result := cut_trans result h3 (by omega)
    have result := cut_trans result h2 (by omega)
    have result := cut_trans result h1 (by omega)
    have result := cut_trans result h0 (by omega)
    exact cut_congr result (by omega) (by omega)

theorem program_prepared_low_high (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above : Bool) :
    Reachable (macroBoard (last:=last) w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)) (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩ :=
  initial_low_high w hw _ (by omega) switch _ above

theorem program_prepared_high_low (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above : Bool) :
    Reachable (macroBoard (last:=last) w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)) (program w length switch)⟩ :=
  initial_high_low w hw _ (by omega) switch _ above

end PushPuzzle.PushS.FiniteRouting.Line.Action
