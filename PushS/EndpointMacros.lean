/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.LinePush
public import PushS.PortEndpointCounts
import all PushS.PortEndpointCounts
import all PushS.PortEndpointCrossing
import all PushS.PortSegments

/-! Real horizontal WIRE pushes on the two emitted endpoint traces. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem horizontal_contains (x u y : ℕ) (q : ℕ × ℕ) :
    (segment x y u y).Contains q ↔ q.2 = y ∧ min x u ≤ q.1 ∧ q.1 ≤ max x u := by
  simpa only [mem_pointHoles, List.mem_singleton, exists_eq_left] using horizontal_mem x u y q

private theorem vertical_contains (x y v : ℕ) (q : ℕ × ℕ) :
    (segment x y x v).Contains q ↔ q.1 = x ∧ min y v ≤ q.2 ∧ q.2 ≤ max y v := by
  simpa only [mem_pointHoles, List.mem_singleton, exists_eq_left] using vertical_mem x y v q

private theorem pair_mem (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (hs : f.side = e.side) (hj : f.level = e.level) (hi : f.internal = e.internal)
    (he : e.inward = true) (hf : f.inward = false) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        ((endpointSegments (coordinates p) state e).take 1 ++
          (endpointSegments (coordinates p) state f).take 1) ∨
      q.2.val = onSide (coordinates p) e.side (readDepth p e.level) ∧
        (p.x e.port + 1 ≤ q.1.val ∧
          q.1.val ≤ p.x e.port + 1 + (state.internal.getD e.internal false).toNat ∨
        p.x f.port - (1 + (!(state.internal.getD e.internal false)).toNat) ≤ q.1.val ∧
          q.1.val ≤ p.x f.port - 1) := by
  have hx := readLength_add_lt_x p f.port 0
  have hb := Bool.toNat_le (state.internal.getD e.internal false)
  have hbn := Bool.toNat_le (!(state.internal.getD e.internal false))
  simp only [endpointSegments, he, hf, hs, hj, hi]
  simp only [ite_true, Bool.false_eq_true, ite_false, List.take_succ_cons, List.take_zero]
  simp only [SegmentRecipe.mem_holes, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_and_right, exists_or, exists_eq_left]
  simp only [show (coordinates p).x e.port = p.x e.port from rfl,
    show (coordinates p).x f.port = p.x f.port from rfl,
    show (coordinates p).depth e.level = readDepth p e.level from rfl]
  simp only [vertical_contains, horizontal_contains, inward, Bool.false_eq_true, ite_true, ite_false]
  omega

private theorem pair_axes (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (i : ℕ) (gain : Bool) :
    (endpointSegments (coordinates p) { state with internal := state.internal.set i gain } e).take 1 ++
        (endpointSegments (coordinates p) { state with internal := state.internal.set i gain } f).take 1 =
      (endpointSegments (coordinates p) state e).take 1 ++
        (endpointSegments (coordinates p) state f).take 1 := by
  simp only [endpointSegments, List.take_succ_cons, List.take_zero]

private theorem axes_column (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointSegments (coordinates p) state e).take 1 ++
        (endpointSegments (coordinates p) state f).take 1)) :
    q.1.val = p.x e.port ∨ q.1.val = p.x f.port := by
  simp only [SegmentRecipe.mem_holes, endpointSegments, List.take_succ_cons, List.take_zero,
    List.mem_append, List.mem_singleton, or_and_right, exists_or, exists_eq_left] at hq
  rcases hq with hq | hq <;>
    simp only [vertical_contains] at hq <;>
    change _ = (coordinates p).x e.port ∨ _ = (coordinates p).x f.port <;> omega

section Wire

variable (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (hs : f.side = e.side) (hj : f.level = e.level) (hi : f.internal = e.internal)
    (he : e.inward = true) (hf : f.inward = false) (hports : e.port < f.port)
    (hport : f.port < p.axes) (hindex : e.internal < state.internal.length) (gain : Bool)
    (hbefore : state.internal.getD e.internal false = !gain)
    (ambient : Finset (Cell (p.W + 1) (p.H + 1)))
    (ha : Disjoint ambient (SegmentRecipe.holes (p.W + 1) (p.H + 1)
      [⟨(p.x e.port + 2, if e.side = .upper then readDepth p e.level
          else p.H - readDepth p e.level),
        (p.x f.port - 2, if e.side = .upper then readDepth p e.level
          else p.H - readDepth p e.level)⟩]))

include hs hj hi he hf hports hport hindex hbefore ha

/-- Flipping a WIRE's actual internal bit performs one complete horizontal push.
The ambient holes avoid the closed box-and-destination interval on its working row. -/
theorem wire_move (s t : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f))
    (htempty : t.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) { state with internal := state.internal.set e.internal gain } e ++
        endpointSegments (coordinates p) { state with internal := state.internal.set e.internal gain } f))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x e.port + 1 else p.x f.port - 1,
        if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level))
    (ht : (t.player.1.val, t.player.2.val) =
      (if gain then p.x e.port + 2 else p.x f.port - 2,
        if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Move B none (if gain then .east else .west) s.toState t.toState := by
  let row := onSide (coordinates p) e.side (readDepth p e.level)
  have hgap := axis_spacing p hports
  have hD := readDepth_readLength_margin p 0 0
  have hx := readLength_add_lt_x p e.port 0
  have hxr := x_add_readLength_lt_W p hport 0
  have hy := readDepth_add_lt_H p e.level
  have hrow : row < p.H + 1 := by
    dsimp [row, onSide, coordinates]; split_ifs <;> omega
  have hupdate : (state.internal.set e.internal gain).getD e.internal false = gain := by
    simp [List.getD, hindex]
  have hfree (q : Cell (p.W + 1) (p.H + 1)) (hq : q.2.val = row)
      (hl : p.x e.port + 2 ≤ q.1.val) (hr : q.1.val ≤ p.x f.port - 2) : q ∉ ambient := by
    intro hqA
    apply Finset.disjoint_left.mp ha hqA
    rw [SegmentRecipe.mem_holes]
    refine ⟨_, List.mem_singleton_self _, Or.inr ⟨rfl, ?_, ?_, ?_⟩⟩
    · exact hq
    · dsimp only; omega
    · dsimp only; omega
  let dest : Cell (p.W + 1) (p.H + 1) :=
    (⟨if gain then p.x f.port - 2 else p.x e.port + 2, by split_ifs <;> omega⟩,
      ⟨row, hrow⟩)
  have hmem := pair_mem p state e f hs hj hi he hf
  simp only [hbefore] at hmem
  have hmem' := pair_mem p {state with internal := state.internal.set e.internal gain}
    e f hs hj hi he hf
  simp only [pair_axes, hupdate] at hmem'
  have hplayer : s.player.2.val = row := by
    have := congrArg Prod.snd hp; exact this
  have htplayer : t.player.2.val = row := by
    have := congrArg Prod.snd ht; exact this
  have hpx : s.player.1.val = if gain then p.x e.port + 1 else p.x f.port - 1 := congrArg Prod.fst hp
  have htx : t.player.1.val = if gain then p.x e.port + 2 else p.x f.port - 2 := congrArg Prod.fst ht
  have htarget : t.empty = insert t.player (s.empty.erase dest) := by
    ext q
    rw [htempty, Finset.mem_union, hmem', Finset.mem_insert, Finset.mem_erase,
      hempty, Finset.mem_union, hmem]
    have haxes := axes_column p state e f (q := q)
    have htp : q = t.player ↔ q.1.val = t.player.1.val ∧ q.2.val = row := by
      simp only [Prod.ext_iff, Fin.ext_iff]; rw [htplayer]
    have hdp : q = dest ↔ q.1.val = dest.1.val ∧ q.2.val = row := by
      simp only [Prod.ext_iff, Fin.ext_iff]; rfl
    simp only [ne_eq, htp, hdp]
    dsimp only [row] at *
    have hqa : q ∈ ambient → q.2.val ≠ onSide (coordinates p) e.side (readDepth p e.level) ∨
        q.1.val < p.x e.port + 2 ∨ p.x f.port - 2 < q.1.val := by
      intro hqA
      by_contra! h
      exact hfree q h.1 h.2.1 h.2.2 hqA
    clear hdp htp
    by_cases hA : q ∈ ambient <;> by_cases hC : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointSegments (coordinates p) state e).take 1 ++
        (endpointSegments (coordinates p) state f).take 1) <;>
      simp only [hA, hC, true_or, false_or, true_implies, true_iff, and_true] at hqa haxes ⊢ <;>
      cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
      Bool.not_true, Bool.toNat_false, Bool.toNat_true, Nat.add_zero, dest] at htx ⊢ <;> omega
  apply HoleState.move_to_first_hole s t (if gain then .east else .west) dest
    (p.x f.port - p.x e.port - 4) (by omega) _ _ _ _ _ htarget B hB
  · cases gain <;> simp [Direction.lane, dest, hplayer]
  · cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Direction.position, dest]
      at hpx ⊢ <;> omega
  · intro q hline hl hr hq
    rw [hempty, Finset.mem_union, hmem] at hq
    have haxes := axes_column p state e f (q := q)
    have hqa := hfree q
    dsimp only [row] at *
    rcases hq with hq | hq | hq
    · cases gain <;> simp [Direction.lane, Direction.position, dest] at hpx hline hl hr
      all_goals exact hqa (by omega) (by omega) (by omega) hq
    · have hcol := haxes hq
      cases gain <;> simp [Direction.lane, Direction.position, dest] at hpx hline hl hr <;> omega
    · cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
      Bool.not_true, Bool.toNat_false, Bool.toNat_true, Direction.lane, Direction.position, dest] at hpx hline hl hr hq <;> omega
  · rw [hempty, Finset.mem_union, hmem]
    dsimp only [row] at *
    cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
      Bool.not_true, Bool.toNat_false, Bool.toNat_true, dest] <;> omega
  · cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Adjacent, Fin.ext_iff] at hpx htx ⊢ <;> omega

/-- The same WIRE macro constructs its actual target configuration and one legal step. -/
theorem wire_step (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x e.port + 1 else p.x f.port - 1,
        if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointSegments (coordinates p) { state with internal := state.internal.set e.internal gain } e ++
          endpointSegments (coordinates p) { state with internal := state.internal.set e.internal gain } f) ∧
      (t.player.1.val, t.player.2.val) =
        (if gain then p.x e.port + 2 else p.x f.port - 2,
          if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) := by
  have hgap := axis_spacing p hports
  have hD := readDepth_readLength_margin p 0 0
  have hx := x_add_readLength_lt_W p hport 0
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨if gain then p.x e.port + 2 else p.x f.port - 2, by split_ifs <;> omega⟩, s.player.2)
  have hcoord : (q.1.val, q.2.val) =
      (if gain then p.x e.port + 2 else p.x f.port - 2,
        if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) := by
    have hy : s.player.2.val =
        if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level :=
      congrArg Prod.snd hp
    exact Prod.ext rfl hy
  let target := { state with internal := state.internal.set e.internal gain }
  have hnew : target.internal.getD e.internal false = gain := by
    simp [target, List.getD, hindex]
  have hq : q ∈ ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) target e ++ endpointSegments (coordinates p) target f) := by
    rw [Finset.mem_union, pair_mem p target e f hs hj hi he hf]
    right; right
    have hrow : q.2.val = onSide (coordinates p) e.side (readDepth p e.level) :=
      congrArg Prod.snd hp
    simp only [hrow, true_and, hnew]
    cases gain <;> simp only [q, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true] <;> omega
  let t : HoleState (p.W + 1) (p.H + 1) := ⟨q, _, hq⟩
  exact ⟨t, ⟨_, wire_move p state e f hs hj hi he hf hports hport hindex gain hbefore
    ambient ha s t hempty rfl hp hcoord B hB⟩, rfl, hcoord⟩

end Wire

end PushPuzzle.PushS.PortLayout
