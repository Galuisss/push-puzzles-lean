/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineTerminal
public import PushS.FiniteRoutingLineMatching

/-! Shared real interface boxes and exact owned-stock contracts for complete routing macros. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

/-- The predecessor retains the low first box; an unowned final box is already high. -/
def interfaceBoxes (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last : Bool) :
    Finset (Cell (width w atoms) (height w)) :=
  {cell w hw atoms false (cutFirstLabel w atoms)} ∪
    if last then ∅ else {cell w hw atoms true (cutLastLabel w atoms)}

attribute [local irreducible] width height

private theorem split_inventory (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last phase : Bool)
    (f : Label w atoms → Cell (width w atoms) (height w))
    (hfirst : f (cutFirstLabel w atoms) = cell w hw atoms false (cutFirstLabel w atoms))
    (hlast : last = false → f (cutLastLabel w atoms) = cell w hw atoms true (cutLastLabel w atoms))
    (howned : ∀ l : OwnedLabel w atoms false last, f l.val = ownedCell w hw atoms false last phase l) :
    Finset.univ.image f = ownedBoxes w hw atoms false last phase ∪ interfaceBoxes w hw atoms last := by
  have hlen := Terminal.length_eq w atoms
  have hval := Terminal.last_val w atoms
  ext p
  constructor
  · intro hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases h0 : l.val = 0
    · have he : l = cutFirstLabel w atoms := Fin.ext h0
      rw [he, hfirst]
      apply Finset.mem_union_right
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
    by_cases he : last = false ∧ l = cutLastLabel w atoms
    · rw [he.2, hlast he.1]
      apply Finset.mem_union_right
      apply Finset.mem_union_right
      simp [he.1]
    · have hp : (false = true ∨ 0 < l.val) ∧ (last = true ∨ l.val+1 < (positions w false atoms).length) := by
        refine ⟨Or.inr (by omega), ?_⟩
        cases last
        · apply Or.inr
          have hl := l.isLt
          have hne : l.val ≠ (cutLastLabel w atoms).val := by intro hh; exact he ⟨rfl, Fin.ext hh⟩
          omega
        · exact Or.inl rfl
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨⟨l,hp⟩, Finset.mem_univ _, (howned _).symm⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l.val, Finset.mem_univ _, howned l⟩
    · rcases Finset.mem_union.mp hp with hp | hp
      · have he := Finset.mem_singleton.mp hp
        exact Finset.mem_image.mpr ⟨cutFirstLabel w atoms, Finset.mem_univ _, hfirst.trans he.symm⟩
      · cases last
        · have he := Finset.mem_singleton.mp hp
          exact Finset.mem_image.mpr ⟨cutLastLabel w atoms, Finset.mem_univ _, (hlast rfl).trans he.symm⟩
        · simp at hp

theorem cut_source_inventory (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last : Bool)
    (hpos : 0 < ownedCount w atoms) :
    cutBoxes w hw (ownedCount w atoms+if last then 1 else 0) atoms =
      ownedBoxes w hw atoms false last false ∪ interfaceBoxes w hw atoms last := by
  apply split_inventory
  · exact cutCell_first w hw _ atoms (by cases last <;> dsimp <;> omega)
  · intro hl
    subst last
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
    apply cutCell_last
    rw [Terminal.length_eq]
    omega
  · intro l
    have hl := l.val.isLt
    have hp := l.property.2
    have hlen := Terminal.length_eq w atoms
    have hlt : l.val.val < ownedCount w atoms+if last then 1 else 0 := by
      cases last <;> simp only [Bool.false_eq_true, false_or] at hp <;> dsimp <;> omega
    exact ite_eq_left hlt

theorem cut_target_inventory (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last : Bool)
    (hpos : 0 < ownedCount w atoms) :
    cutBoxes w hw 1 atoms = ownedBoxes w hw atoms false last true ∪ interfaceBoxes w hw atoms last := by
  apply split_inventory
  · exact cutCell_first w hw 1 atoms (by omega)
  · intro _
    apply cutCell_last
    rw [Terminal.length_eq]
    omega
  · intro l
    have hl : 0 < l.val.val := by simpa only [Bool.false_eq_true, false_or] using l.property.1
    exact ite_eq_right (by omega)

theorem program_ownedCount_pos (w length : ℕ) (switch : Bool) : 0 < ownedCount w (program w length switch) := by
  have hb : 0 < buffer w := by unfold buffer; omega
  cases switch <;> cases h : decide (length % 2 = 1) <;>
    simp [program, initialAtoms, h, ownedCount, ownedPositions, Atom.positions]

/-- The local inventory explicitly includes both shared interface owners during the propagation wave. -/
private theorem program_owned_low_high (w : ℕ) (hw : 2 ≤ w) (length : ℕ)
    (switch above last : Bool) :
    Reachable (macroBoard w (program w length switch) above) (some 1)
      ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last false ∪
        interfaceBoxes w hw (program w length switch) last⟩
      ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last true ∪
        interfaceBoxes w hw (program w length switch) last⟩ := by
  have hh := program_low_high w hw length switch above last
  rw [cut_source_inventory w hw _ last (program_ownedCount_pos w length switch),
    cut_target_inventory w hw _ last (program_ownedCount_pos w length switch)] at hh
  exact hh

private theorem program_owned_high_low (w : ℕ) (hw : 2 ≤ w) (length : ℕ)
    (switch above last : Bool) :
    Reachable (macroBoard w (program w length switch) above) (some 1)
      ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last true ∪
        interfaceBoxes w hw (program w length switch) last⟩
      ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last false ∪
        interfaceBoxes w hw (program w length switch) last⟩ := by
  have hh := program_high_low w hw length switch above last
  rw [cut_source_inventory w hw _ last (program_ownedCount_pos w length switch),
    cut_target_inventory w hw _ last (program_ownedCount_pos w length switch)] at hh
  exact hh

theorem program_owned_low_high_placed (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool)
    {W H : ℕ} (e : GridEmbedding (width w (program w length switch)) (height w) W H)
    {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (active w (program w length switch) above) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last false ∪
        interfaceBoxes w hw (program w length switch) last⟩)
      (e.extend fixed ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last true ∪
        interfaceBoxes w hw (program w length switch) last⟩) :=
  frame.replay (program_owned_low_high w hw length switch above last)

theorem program_owned_high_low_placed (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool)
    {W H : ℕ} (e : GridEmbedding (width w (program w length switch)) (height w) W H)
    {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (active w (program w length switch) above) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last true ∪
        interfaceBoxes w hw (program w length switch) last⟩)
      (e.extend fixed ⟨outerHub w _, ownedBoxes w hw (program w length switch) false last false ∪
        interfaceBoxes w hw (program w length switch) last⟩) :=
  frame.replay (program_owned_high_low w hw length switch above last)

end PushPuzzle.PushS.FiniteRouting.Line
