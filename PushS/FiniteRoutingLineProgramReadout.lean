/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineSignal

/-! Successful physical trajectories transmit a threshold through every emitted program atom. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Readout.LineGlyph

open PushFS PushFS.Gadgets.Wires.Soundness
open FiniteTools (radius)

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]
    {M : SlotMatching I GlobalLabel} {A : ComponentTracks I} {w : ℕ} {above : Bool}
    {S final : LabelledState GlobalLabel I.width I.height}

private theorem high_of_index {atoms : List Atom} (g : LineGlyph M A w atoms above)
    (i j : Label w atoms)
    (he : i.val = j.val) (hi : g.High S i) : g.High S j := by
  exact (Fin.ext he : i = j) ▸ hi

set_option maxHeartbeats 3000000 in
private theorem initial_signal (t : ℕ) (switch odd : Bool)
    (g : LineGlyph M A w (initialAtoms w switch odd++[.line t]) above)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.High S (cutFirstLabel w _)) : g.High S (cutLastLabel w _) := by
  cases switch <;> cases odd
  · change LineGlyph M A w [.line (buffer w),.flip,.line (buffer w),.flip,.line t] above at g
    change g.High S (cutFirstLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line t]) at hin
    change g.High S (cutLastLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line t])
    have hi0 : g.High S (headAt w [] [.flip,.line (buffer w),.flip,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, cutFirstLabel, Fin.val_mk, ownedCount, ownedPositions, List.length_nil] ) hin
    have f0 := stock_signal [] [.flip,.line (buffer w),.flip,.line t] (buffer w) g h cert hi0
    have hi1 : g.High S (headAt w [.line (buffer w)] [.line (buffer w),.flip,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_nil, Nat.zero_add, Nat.add_zero] ) f0
    have f1 := flip_signal [.line (buffer w)] [.line (buffer w),.flip,.line t] g h cert ho hi1
    have hi2 : g.High S (headAt w [.line (buffer w),.flip] [.flip,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero] ) f1
    have f2 := stock_signal [.line (buffer w),.flip] [.flip,.line t] (buffer w) g h cert hi2
    have hi3 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w)] [.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f2
    have f3 := flip_signal [.line (buffer w),.flip,.line (buffer w)] [.line t] g h cert ho hi3
    have hi4 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip] [] (.line t)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f3
    have f4 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip] [] t g h cert hi4
    exact g.high_of_index _ _ (by simp only [endAt_val, Terminal.last_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f4
  · change LineGlyph M A w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] above at g
    change g.High S (cutFirstLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t]) at hin
    change g.High S (cutLastLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t])
    have hi0 : g.High S (headAt w [] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, cutFirstLabel, Fin.val_mk, ownedCount, ownedPositions, List.length_nil] ) hin
    have f0 := stock_signal [] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) g h cert hi0
    have hi1 : g.High S (headAt w [.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.parity,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_nil, Nat.zero_add, Nat.add_zero] ) f0
    have f1 := flip_signal [.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.parity,.line t] g h cert ho hi1
    have hi2 : g.High S (headAt w [.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero] ) f1
    have f2 := stock_signal [.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) g h cert hi2
    have hi3 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.parity,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f2
    have f3 := flip_signal [.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.parity,.line t] g h cert ho hi3
    have hi4 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f3
    have f4 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) g h cert hi4
    have hi5 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line t] (.parity)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f4
    have f5 := parity_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line t] g h cert ho hi5
    have hi6 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] (.line t)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f5
    have f6 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] t g h cert hi6
    exact g.high_of_index _ _ (by simp only [endAt_val, Terminal.last_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f6
  · change LineGlyph M A w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] above at g
    change g.High S (cutFirstLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t]) at hin
    change g.High S (cutLastLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t])
    have hi0 : g.High S (headAt w [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, cutFirstLabel, Fin.val_mk, ownedCount, ownedPositions, List.length_nil] ) hin
    have f0 := stock_signal [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line t] (buffer w) g h cert hi0
    have hi1 : g.High S (headAt w [.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.flip,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_nil, Nat.zero_add, Nat.add_zero] ) f0
    have f1 := flip_signal [.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.flip,.line t] g h cert ho hi1
    have hi2 : g.High S (headAt w [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero] ) f1
    have f2 := stock_signal [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line t] (buffer w) g h cert hi2
    have hi3 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.flip,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f2
    have f3 := flip_signal [.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.flip,.line t] g h cert ho hi3
    have hi4 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f3
    have f4 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line t] (buffer w) g h cert hi4
    have hi5 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f4
    have f5 := flip_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line t] g h cert ho hi5
    have hi6 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [] (.line t)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f5
    have f6 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [] t g h cert hi6
    exact g.high_of_index _ _ (by simp only [endAt_val, Terminal.last_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f6
  · change LineGlyph M A w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] above at g
    change g.High S (cutFirstLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t]) at hin
    change g.High S (cutLastLabel w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t])
    have hi0 : g.High S (headAt w [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, cutFirstLabel, Fin.val_mk, ownedCount, ownedPositions, List.length_nil] ) hin
    have f0 := stock_signal [] [.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) g h cert hi0
    have hi1 : g.High S (headAt w [.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_nil, Nat.zero_add, Nat.add_zero] ) f0
    have f1 := flip_signal [.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] g h cert ho hi1
    have hi2 : g.High S (headAt w [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero] ) f1
    have f2 := stock_signal [.line (buffer w),.flip] [.flip,.line (buffer w),.flip,.line (buffer w),.parity,.line t] (buffer w) g h cert hi2
    have hi3 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.parity,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f2
    have f3 := flip_signal [.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.flip,.line (buffer w),.parity,.line t] g h cert ho hi3
    have hi4 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f3
    have f4 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip] [.flip,.line (buffer w),.parity,.line t] (buffer w) g h cert hi4
    have hi5 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.parity,.line t] (.flip)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f4
    have f5 := flip_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line (buffer w),.parity,.line t] g h cert ho hi5
    have hi6 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (.line (buffer w))) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f5
    have f6 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip] [.parity,.line t] (buffer w) g h cert hi6
    have hi7 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line t] (.parity)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f6
    have f7 := parity_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w)] [.line t] g h cert ho hi7
    have hi8 : g.High S (headAt w [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] (.line t)) :=
      g.high_of_index _ _ (by simp only [headAt_val, endAt_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f7
    have f8 := stock_signal [.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.flip,.line (buffer w),.parity] [] t g h cert hi8
    exact g.high_of_index _ _ (by simp only [endAt_val, Terminal.last_val, ownedCount, ownedPositions, Atom.positions, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]; omega) f8

/-- The actual first working box forcing high implies the actual far endpoint has crossed its high threshold. -/
theorem program_signal (length : ℕ) (switch : Bool)
    (g : LineGlyph M A w (program w length switch) above)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dx+radius w+1 ≤ (S.position (g.labels (cutFirstLabel w _))).1.val) :
    g.dx+radius w+span w (program w length switch)+1 ≤
      (S.position (g.labels (cutLastLabel w _))).1.val := by
  have hi : g.High S (cutFirstLabel w _) := by
    dsimp [High]
    rwa [position_first]
  have hh := initial_signal _ switch _ g h cert ho hi
  dsimp [High] at hh
  rwa [Terminal.last_position] at hh

end PushPuzzle.PushS.FiniteRouting.Line.Readout.LineGlyph
