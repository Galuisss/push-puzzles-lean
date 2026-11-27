/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineProgram

/-! The owned final interface is pushed first forward and restored last backward. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Terminal

open PushFS
open FiniteTools (radius)

theorem length_eq (w : ℕ) (atoms : List Atom) : (positions w false atoms).length = ownedCount w atoms+1 := by
  simpa only [List.append_nil, positions, List.length_singleton] using positions_split_length w atoms []

theorem last_val (w : ℕ) (atoms : List Atom) : (cutLastLabel w atoms).val = ownedCount w atoms := by
  simp [cutLastLabel, length_eq]

theorem last_position (w : ℕ) (atoms : List Atom) (phase : Bool) :
    position w atoms phase (cutLastLabel w atoms) = span w atoms+phase.toNat := by
  have hh := positions_last w atoms phase
  rw [List.getLast_eq_getElem] at hh
  simpa only [position, cutLastLabel, List.get_eq_getElem, positions_length] using hh

def cut (w : ℕ) (atoms : List Atom) (q : Bool) : ℕ := ownedCount w atoms+if q then 0 else 1

def endCell (w : ℕ) (atoms : List Atom) (d : Fin 4) : Cell (width w atoms) (height w) :=
  (⟨radius w+span w atoms-1+d.val, by
    have := d.isLt
    unfold width radius
    omega⟩, workY w)

attribute [local irreducible] width height

theorem slot (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) :
    cutCell w hw (cut w atoms q) atoms (cutLastLabel w atoms) =
      endCell w atoms ⟨1+q.toNat, by have := Bool.toNat_le q; omega⟩ := by
  have hv := last_val w atoms
  cases q <;> simp only [cutCell, cut, Bool.false_eq_true, ite_false, ite_true]
  · rw [ite_eq_left (by omega)]
    apply Prod.ext <;> apply Fin.ext
    · change radius w+position w atoms false (cutLastLabel w atoms) = _
      rw [last_position]
      dsimp [endCell]; unfold radius; omega
    · rfl
  · rw [ite_eq_right (by omega)]
    apply Prod.ext <;> apply Fin.ext
    · change radius w+position w atoms true (cutLastLabel w atoms) = _
      rw [last_position]
      dsimp [endCell]; unfold radius; omega
    · rfl

theorem other (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (l : Label w atoms)
    (hl : l ≠ cutLastLabel w atoms) : cutCell w hw (cut w atoms q) atoms l = cell w hw atoms false l := by
  have hv := last_val w atoms
  have hlen := l.isLt
  have hcount := length_eq w atoms
  have he : l.val ≠ ownedCount w atoms := by intro he; exact hl (Fin.ext (by omega))
  have hl' : l.val < cut w atoms q := by cases q <;> dsimp [cut] <;> omega
  exact ite_eq_left hl'

theorem no_box (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool) (d : Fin 4)
    (hd : d.val ≠ 1+q.toNat) (p : Cell (width w atoms) (height w))
    (hx : p.1.val = (endCell w atoms d).1.val) : p ∉ cutBoxes w hw (cut w atoms q) atoms := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hxe := congrArg (fun p : Cell (width w atoms) (height w) => p.1.val) he
  have hrad : 0 < radius w := by unfold radius; omega
  by_cases hl : l = cutLastLabel w atoms
  · subst l
    rw [slot] at hxe
    dsimp [endCell] at hx hxe
    omega
  · rw [other w hw atoms q l hl] at hxe
    have hlen := l.isLt
    have hcount := length_eq w atoms
    have hv := last_val w atoms
    have heval : l.val ≠ (cutLastLabel w atoms).val := fun hh => hl (Fin.ext hh)
    have hg := position_gap w hw atoms false l (cutLastLabel w atoms) (by omega)
    rw [last_position] at hg
    simp only [Bool.toNat_false] at hg
    change radius w+position w atoms false l = p.1.val at hxe
    dsimp [endCell] at hx
    omega

theorem end_floor (w : ℕ) (atoms : List Atom) (above : Bool) (d : Fin 4) :
    endCell w atoms d ∉ (macroBoard w atoms above).walls := by
  have hd := d.isLt
  apply (FiniteWireFrame.floor_iff _ _ _).mpr
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, ?_, ?_, row_floor w atoms above _ rfl⟩
  all_goals dsimp [endCell, workY]; unfold radius; omega

/-- Only the actual final physical label changes during endpoint preparation. -/
private theorem push (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (above q : Bool) :
    Move (macroBoard w atoms above) (some 1) (if q then .west else .east)
      ⟨endCell w atoms (if q then 3 else 0), cutBoxes w hw (cut w atoms q) atoms⟩
      ⟨endCell w atoms ⟨1+q.toNat, by have := Bool.toNat_le q; omega⟩,
        cutBoxes w hw (cut w atoms (!q)) atoms⟩ := by
  have hmove := FiniteWireFrame.push_named (cutCell w hw (cut w atoms q) atoms)
    (cutCell w hw (cut w atoms (!q)) atoms) (cutCell_injective w hw _ atoms)
    (cutLastLabel w atoms) (by intro l hl; rw [other w hw atoms q l hl, other w hw atoms (!q) l hl])
    (support := endCell w atoms (if q then 3 else 0)) (d := if q then .west else .east)
    ⟨end_floor w atoms above _, cutBoxes_macro_floor w hw _ atoms above,
      no_box w hw atoms q (if q then 3 else 0) (by cases q <;> simp) _ rfl⟩
    (by rw [slot]; cases q <;> simp [Adjacent, endCell, radius])
    (by rw [slot, slot]; cases q <;> simp [Adjacent, endCell, radius])
    (by rw [slot]; exact end_floor w atoms above _)
    (by rw [slot]; exact no_box w hw atoms q ⟨1+(!q).toNat, by have := Bool.toNat_le (!q); omega⟩ (by cases q <;> simp) _ rfl)
  rw [slot] at hmove
  exact hmove

theorem column_free (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w) (y : Fin (height w))
    (hy : min (workY w).val (laneY w (!(exitSide above pre))).val ≤ y.val)
    (hy' : y.val ≤ max (workY w).val (laneY w (!(exitSide above pre))).val) :
    Free (macroBoard w (pre++[.line n]) above) (cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n]))
      ((endCell w (pre++[.line n]) d).1,y) := by
  have hd' := d.isLt
  have hn' : 2 ≤ n := by unfold buffer at hn; omega
  have hylo : radius w-w-1 ≤ y.val := by
    cases hs : exitSide above pre <;> simp [laneY, workY, hs] at hy hy' ⊢ <;> unfold radius at * <;> omega
  have hyhi : y.val ≤ radius w+w+1 := by
    cases hs : exitSide above pre <;> simp [laneY, workY, hs] at hy hy' ⊢ <;> unfold radius at * <;> omega
  have hex : Exposed w (exitSide above pre) y.val := by
    cases hs : exitSide above pre <;> simp [laneY, workY, Exposed, hs] at hy hy' ⊢ <;> unfold radius at * <;> omega
  refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, no_box w hw _ q d hd _ rfl⟩
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_, hylo, hyhi, ?_⟩
  · dsimp [endCell]; unfold radius; omega
  · dsimp [endCell]; unfold radius; omega
  · by_cases hdx : d.val ≤ 1
    · apply stock_face_floor w hw pre [] above n ha
      · dsimp [endCell]; simp only [span_append, span_cons, span_nil, Atom.span, Nat.add_zero]; unfold radius; omega
      · dsimp [endCell]; simp only [span_append, span_cons, span_nil, Atom.span, Nat.add_zero]; unfold radius; omega
      · exact hex
    · intro hp
      obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp hp
      apply right_face_floor w hw 0 above (pre++[.line n]) ha (List.mem_toFinset.mp hr) _ ?_ ?_ hp
      · dsimp [endCell]; unfold radius; omega
      · simpa only [exitSide_append, exitSide, Atom.nextSide] using hex

private theorem end_to_outer (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w) :
    Reachable (macroBoard w (pre++[.line n]) above) (some 1)
      ⟨endCell w (pre++[.line n]) d, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerCell w _ (!(exitSide above pre)) (endCell w (pre++[.line n]) d).1,
        cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw _ _ above)
  exact column_free w hw pre n hn above q d hd ha

private theorem outer_to_end (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w) :
    Reachable (macroBoard w (pre++[.line n]) above) (some 1)
      ⟨outerCell w _ (!(exitSide above pre)) (endCell w (pre++[.line n]) d).1,
        cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨endCell w (pre++[.line n]) d, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw _ _ above)
  intro y hy hy'
  exact column_free w hw pre n hn above q d hd ha y (by simpa only [min_comm] using hy)
    (by simpa only [max_comm] using hy')

private theorem hub_to_end (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w)
    (hflip : ∃ left right, pre++[.line n] = left++ .flip::right) :
    Reachable (macroBoard w (pre++[.line n]) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨endCell w (pre++[.line n]) d, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  have hb := (Finset.mem_filter.mp ((FiniteWireFrame.floor_iff _ _ _).mp (end_floor w (pre++[.line n]) above d))).2
  apply (outer_macro_connected_of_flip w hw _ _ hflip above true (!(exitSide above pre))
    (outerHubX w _) (endCell w (pre++[.line n]) d).1 (by dsimp [outerHubX]; omega)
    (by dsimp [outerHubX]; omega) hb.1 hb.2.1).trans
  exact outer_to_end w hw pre n hn above q d hd ha

private theorem hub_return (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (d : Fin 4) (hd : d.val ≠ 1+q.toNat)
    (ha : ∀ a ∈ pre++[.line n], a.Valid w)
    (hflip : ∃ left right, pre++[.line n] = left++ .flip::right) :
    Reachable (macroBoard w (pre++[.line n]) above) (some 1)
      ⟨endCell w (pre++[.line n]) d, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerHub w _, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩ := by
  have hb := (Finset.mem_filter.mp ((FiniteWireFrame.floor_iff _ _ _).mp (end_floor w (pre++[.line n]) above d))).2
  apply (end_to_outer w hw pre n hn above q d hd ha).trans
  exact outer_macro_connected_of_flip w hw _ _ hflip above (!(exitSide above pre)) true
    (endCell w (pre++[.line n]) d).1 (outerHubX w _) hb.1 hb.2.1
    (by dsimp [outerHubX]; omega) (by dsimp [outerHubX]; omega)

/-- The final box has a real support walk, one push, and a return to the global line hub. -/
private theorem prepare (w : ℕ) (hw : 2 ≤ w) (pre : List Atom) (n : ℕ)
    (hn : buffer w ≤ n) (above q : Bool) (ha : ∀ a ∈ pre++[.line n], a.Valid w)
    (hflip : ∃ left right, pre++[.line n] = left++ .flip::right) :
    Reachable (macroBoard w (pre++[.line n]) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (cut w (pre++[.line n]) q) (pre++[.line n])⟩
      ⟨outerHub w _, cutBoxes w hw (cut w (pre++[.line n]) (!q)) (pre++[.line n])⟩ := by
  have he := hub_to_end w hw pre n hn above q (if q then 3 else 0) (by cases q <;> simp) ha hflip
  have hx := hub_return w hw pre n hn above (!q) ⟨1+q.toNat, by have := Bool.toNat_le q; omega⟩
    (by cases q <;> simp) ha hflip
  exact (he.tail ⟨if q then .west else .east, push w hw _ above q⟩).trans hx

private theorem program_prepare (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above q : Bool) :
    Reachable (macroBoard w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (cut w (program w length switch) q) (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw (cut w (program w length switch) (!q)) (program w length switch)⟩ := by
  obtain ⟨post, hp⟩ := program_contains_flip w length switch
  exact prepare w hw (initialAtoms w switch (decide (length % 2 = 1))) _ (by omega) above q
    (program_valid w length switch) ⟨[.line (buffer w)], post, hp⟩

end PushPuzzle.PushS.FiniteRouting.Line.Terminal

namespace PushPuzzle.PushS.FiniteRouting.Line
open PushFS

/-- Execute every physical atom, preparing the owned last interface when requested. -/
theorem program_low_high (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool) :
    Reachable (macroBoard w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)+if last then 1 else 0) (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩ := by
  cases last
  · exact program_prepared_low_high w hw length switch above
  · exact (Terminal.program_prepare w hw length switch above false).trans
      (program_prepared_low_high w hw length switch above)

theorem program_high_low (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool) :
    Reachable (macroBoard w (program w length switch) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw 1 (program w length switch)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w (program w length switch)+if last then 1 else 0) (program w length switch)⟩ := by
  cases last
  · exact program_prepared_high_low w hw length switch above
  · exact (program_prepared_high_low w hw length switch above).trans
      (Terminal.program_prepare w hw length switch above true)

end PushPuzzle.PushS.FiniteRouting.Line
