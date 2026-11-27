/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingToolGeometry
import Mathlib.Tactic.FinCases

/-! Exact five-label flip inventory, including the real neighboring stock boxes. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Tool.Flip

open PushFS FiniteTools

def headLabel (w : ℕ) (post : List Atom) (i : Fin 2) : Label w (.flip::post) :=
  ⟨i.val, by simp [positions, Atom.positions]; have := i.isLt; omega⟩

theorem head_position (w : ℕ) (post : List Atom) (q : Bool) (i : Fin 2) :
    position w (.flip::post) q (headLabel w post i) = if i.val = 0 then q.toNat else w+3*q.toNat := by
  fin_cases i <;> simp [position, positions, Atom.positions, headLabel]

def index : FlipLabel → ℕ
  | .predecessor => 0
  | .left => 1
  | .middle => 2
  | .right => 3
  | .successor => 4

def label (w : ℕ) (before after : List Atom) (n m : ℕ) (hn : 0 < n) (hm : 1 < m) :
    FlipLabel → Label w (before++ .line n:: .flip:: .line m::after)
  | .predecessor => tailLabel w before _ (lineLabel w n _ ⟨n-1, by omega⟩)
  | .left => tailLabel w before _ (tailLabel w [.line n] _ (headLabel w _ 0))
  | .middle => tailLabel w before _ (tailLabel w [.line n] _ (headLabel w _ 1))
  | .right => tailLabel w before _ (tailLabel w [.line n,.flip] _ (lineLabel w m after ⟨0, by omega⟩))
  | .successor => tailLabel w before _ (tailLabel w [.line n,.flip] _ (lineLabel w m after ⟨1, hm⟩))

theorem label_val (w : ℕ) (before after : List Atom) (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (l : FlipLabel) :
    (label w before after n m hn hm l).val = ownedCount w before+n-1+index l := by
  cases l <;> dsimp [label, tailLabel, lineLabel, headLabel, index] <;>
    simp only [ownedCount, ownedPositions, Atom.positions,
      List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil] <;> omega

theorem label_complete (w : ℕ) (before after : List Atom) (n m : ℕ) (hn : 0 < n) (hm : 1 < m)
    (l : Label w (before++ .line n:: .flip:: .line m::after))
    (hl : ownedCount w before+n-1 ≤ l.val) (hl' : l.val ≤ ownedCount w before+n+3) :
    ∃ i, label w before after n m hn hm i = l := by
  by_cases h0 : l.val = ownedCount w before+n-1
  · exact ⟨.predecessor, Fin.ext (by rw [label_val]; exact h0.symm)⟩
  by_cases h1 : l.val = ownedCount w before+n
  · exact ⟨.left, Fin.ext (by rw [label_val]; dsimp [index]; omega)⟩
  by_cases h2 : l.val = ownedCount w before+n+1
  · exact ⟨.middle, Fin.ext (by rw [label_val]; dsimp [index]; omega)⟩
  by_cases h3 : l.val = ownedCount w before+n+2
  · exact ⟨.right, Fin.ext (by rw [label_val]; dsimp [index]; omega)⟩
  exact ⟨.successor, Fin.ext (by rw [label_val]; dsimp [index]; omega)⟩

def cut (w : ℕ) (before : List Atom) (n : ℕ) (q : Bool) : ℕ :=
  ownedCount w before+n + if q then 0 else 3

def phase (q : Bool) : FlipLabel → Bool
  | .predecessor => false
  | .successor => true
  | _ => q

def normalPosition (w offset : ℕ) (q : Bool) : FlipLabel → ℕ
  | .predecessor => offset-2+q.toNat
  | .left => offset+q.toNat
  | .middle => offset+w+3*q.toNat
  | .right => offset+2*w+2+q.toNat
  | .successor => offset+2*w+4+q.toNat

private theorem normal_position (w : ℕ) (before after : List Atom) (n m : ℕ) (hn : 0 < n)
    (hm : 1 < m)
    (q : Bool) (l : FlipLabel) :
    position w (before++ .line n:: .flip:: .line m::after) q (label w before after n m hn hm l) =
      normalPosition w (span w before+2*n) q l := by
  cases l <;> dsimp [label]
  all_goals rw [tail_position]
  · rw [line_position]; dsimp [normalPosition]; omega
  · have hh := tail_position w [.line n] (.flip::.line m::after) q (headLabel w _ 0)
    simp only [List.singleton_append] at hh
    rw [hh, head_position]; simp [normalPosition, Atom.span, Nat.add_assoc]
  · have hh := tail_position w [.line n] (.flip::.line m::after) q (headLabel w _ 1)
    simp only [List.singleton_append] at hh
    rw [hh, head_position]; simp [normalPosition, Atom.span, Nat.add_assoc]
  · have hh := tail_position w [.line n,.flip] (.line m::after) q (lineLabel w m after ⟨0, by omega⟩)
    simp only [List.cons_append, List.nil_append] at hh
    rw [hh, line_position]; simp [normalPosition, Atom.span, Nat.add_assoc]
  · have hh := tail_position w [.line n,.flip] (.line m::after) q (lineLabel w m after ⟨1, hm⟩)
    simp only [List.cons_append, List.nil_append] at hh
    rw [hh, line_position]; simp [normalPosition, Atom.span, Nat.add_assoc]; omega

private theorem cut_slot (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ) (hn : 0 < n)
    (hm : 1 < m)
    (q : Bool) (l : FlipLabel) :
    cutCell w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after)
      (label w before after n m hn hm l) =
      cell w hw (before++ .line n:: .flip:: .line m::after) (phase q l) (label w before after n m hn hm l) := by
  have hv := label_val w before after n m hn hm l
  cases q <;> cases l <;> simp only [cutCell, cut, phase, Bool.false_eq_true, ite_false, ite_true] <;>
    first | (rw [ite_eq_left (by dsimp [index] at hv; omega)]) | (rw [ite_eq_right (by dsimp [index] at hv; omega)])

abbrev place := flipPlace

attribute [local irreducible] width height

theorem slot (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ) (hn : 0 < n) (hm : 1 < m)
    (above q : Bool) (l : FlipLabel) :
    cutCell w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after)
      (label w before after n m hn hm l) =
      (place w before after n m above).cells (flipCell w q l) := by
  rw [cut_slot]
  apply Prod.ext <;> apply Fin.ext
  · change radius w+position w _ (phase q l) _ = _
    rw [normal_position]
    have hq := Bool.toNat_le q
    cases l <;> dsimp [normalPosition, phase, place, flipPlace, embedding, flipCell, flipPoint] <;>
      unfold radius <;> omega
  · cases hb : exitSide above before <;>
      cases l <;> simp [cell, place, flipPlace, embedding, hb, flipCell, flipPoint, radius] <;> omega

def fixed (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ) (hn : 0 < n) (hm : 1 < m) :
    Finset (Cell (width w (before++ .line n:: .flip:: .line m::after)) (height w)) :=
  (Finset.univ.filter fun l => ¬∃ i, label w before after n m hn hm i = l).image
    (cutCell w hw (cut w before n false) (before++ .line n:: .flip:: .line m::after))

private theorem rest (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ) (hn : 0 < n)
    (hm : 1 < m)
    (q : Bool) (l : Label w (before++ .line n:: .flip:: .line m::after))
    (hl : ¬∃ i, label w before after n m hn hm i = l) :
    cutCell w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after) l =
      cutCell w hw (cut w before n false) (before++ .line n:: .flip:: .line m::after) l := by
  have hout : l.val < ownedCount w before+n-1 ∨ ownedCount w before+n+3 < l.val := by
    by_contra hh
    exact hl (label_complete w before after n m hn hm l (by omega) (by omega))
  cases q
  · rfl
  · rcases hout with hout | hout
    · simp only [cutCell, cut, ite_true, Bool.false_eq_true, ite_false,
        ite_eq_left (by omega : l.val < ownedCount w before+n+0),
        ite_eq_left (by omega : l.val < ownedCount w before+n+3)]
    · simp only [cutCell, cut, ite_true, Bool.false_eq_true, ite_false,
        ite_eq_right (by omega : ¬l.val < ownedCount w before+n+0),
        ite_eq_right (by omega : ¬l.val < ownedCount w before+n+3)]

theorem inventory (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ) (hn : 0 < n) (hm : 1 < m)
    (above q : Bool) :
    cutBoxes w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after) =
      (flipBoxes w q).map (place w before after n m above).cells ∪
        fixed w hw before after n m hn hm := by
  ext p
  constructor
  · intro hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases hl : ∃ i, label w before after n m hn hm i = l
    · obtain ⟨i, rfl⟩ := hl
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨_,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, (slot w hw before after n m hn hm above q i).symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, (rest w hw before after n m hn hm q l hl).symm⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, slot w hw before after n m hn hm above q i⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _,
        rest w hw before after n m hn hm q l (Finset.mem_filter.mp hl).2⟩

end PushPuzzle.PushS.FiniteRouting.Line.Tool.Flip
