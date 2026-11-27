/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingDeepRows

/-! The mandatory first flip's two literal mouth columns miss every normal stock slot. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

namespace Line

/-- A normal scalar slot advancing by one cell gives the literal eastward unit step. -/
theorem normal_adjacent_of_position (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom)
    (l : Label w atoms) (n : ℕ) (hpos : ∀ q, position w atoms q l = n+q.toNat) :
    Adjacent .east (cell w hw atoms false l) (cell w hw atoms true l) := by
  change FiniteTools.radius w+position w atoms true l = FiniteTools.radius w+position w atoms false l+1 ∧ _
  rw [hpos false,hpos true]
  exact ⟨by simp [Nat.add_assoc],rfl⟩

/-- Every working-row point in a one-step normal pair is one of its two literal slots. -/
theorem eq_normal_pair_cell (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom)
    (l : Label w atoms) (n : ℕ) (hpos : ∀ q, position w atoms q l = n+q.toNat)
    (p : Cell (width w atoms) (height w))
    (hx : FiniteTools.radius w+n ≤ p.1.val) (hx' : p.1.val ≤ FiniteTools.radius w+n+1)
    (hy : p.2.val = FiniteTools.radius w) : ∃ q, p = cell w hw atoms q l := by
  by_cases he : p.1.val = FiniteTools.radius w+n
  · refine ⟨false,Prod.ext (Fin.ext ?_) (Fin.ext hy)⟩
    change p.1.val = FiniteTools.radius w+position w atoms false l
    rw [hpos false]
    simpa using he
  · refine ⟨true,Prod.ext (Fin.ext ?_) (Fin.ext hy)⟩
    change p.1.val = FiniteTools.radius w+position w atoms true l
    rw [hpos true]
    simp only [Bool.toNat_true]
    omega

private theorem flip_mouth_not_mem (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (q : Bool) (j : Fin 2) :
    span w pre+w+1+j.val ∉ positions w q (pre++ .flip::post) := by
  intro hh
  have hj := j.isLt
  have hb := Bool.toNat_le q
  rw [positions_split] at hh
  rcases List.mem_append.mp hh with hh | hh
  · have hg := ownedPositions_bounds w hw q pre hh
    omega
  · obtain ⟨x,hx,he⟩ := List.mem_map.mp hh
    simp only [positions,Atom.positions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with (h | h) | h
    · omega
    · cases q <;> simp at h <;> omega
    · obtain ⟨z,hz,hez⟩ := List.mem_map.mp h
      have hbound := positions_bounds w hw q post hz
      dsimp [Atom.span] at hez
      omega

private theorem first_mouth_not_mem (w length : ℕ) (hw : 2 ≤ w) (switch q : Bool) (j : Fin 2) :
    2*buffer w+w+1+j.val ∉ positions w q (program w length switch) := by
  obtain ⟨post,hp⟩ := program_contains_flip w length switch
  rw [hp]
  simpa only [span_cons,span_nil,Atom.span,Nat.add_zero] using
    flip_mouth_not_mem w hw [.line (buffer w)] post q j

end Line

namespace LineCode

theorem first_mouth_actor_ne (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (j : Fin 2) (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    Line.along w (segmentDirection c.segment) c.segment.start (2*Line.buffer w+w+1+j.val) ≠
      (PrimitiveCode.line c).actor w hw goal l := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  let q := if goal then c.target else c.initial
  have hmem := Line.position_mem w atoms q l.val
  have hb := Line.positions_bounds w hw q atoms hmem
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  change Line.span w atoms = segmentLength c.segment at hlen
  rw [hlen] at hb
  have hq := Bool.toNat_le q
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  have hj := j.isLt
  rw [line_actor w hw c hc goal l]
  change Line.along w (segmentDirection c.segment) c.segment.start (2*Line.buffer w+w+1+j.val) ≠
    Line.along w (segmentDirection c.segment) c.segment.start (Line.position w atoms q l.val)
  intro he
  have hn : 2*Line.buffer w+w+1+j.val = Line.position w atoms q l.val := by
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    cases hd : segmentDirection c.segment <;> simp only [hd] at ht hx hy <;>
      dsimp [Travels,Line.along] at ht hx hy <;> unfold Line.buffer padding at * <;> omega
  apply Line.first_mouth_not_mem w (segmentLength c.segment) hw (c.above != c.desiredSide) q j
  exact hn ▸ hmem

theorem actionWorld_on_row (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hx : FiniteTools.radius w ≤ p.1.val)
    (hx' : p.1.val ≤ FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))+1)
    (hy : p.2.val = FiniteTools.radius w) :
    c.actionWorld w hw p = Line.along w (segmentDirection c.segment) c.segment.start (p.1.val-FiniteTools.radius w) := by
  have ht := segment_travels c.segment hc.1
  rw [c.actionWorld_native w hw hc p]
  have ⟨hpx,hpy⟩ := c.action_cell_bounds w hc p
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,Line.along] at ht ⊢ <;>
    apply Prod.ext <;> simp only [FiniteTools.radius,hlen,padding] at * <;> omega

end LineCode
end PushPuzzle.PushS.FiniteRouting
