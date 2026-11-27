/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.EndpointMacros
import all PushS.EndpointMacros
import all PushS.PortSegments

/-! Real shared-axis flips between the emitted upper and lower ordinary endpoints. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem pair_axis_mem (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (he : e.side = .upper) (hf : f.side = .lower) (hp : f.port = e.port)
    (hj : 1 ≤ f.level) (hm : f.level ≤ p.levels) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        ((endpointSegments (coordinates p) state e).drop 1 ++
          (endpointSegments (coordinates p) state f).drop 1) ∨
      q.1.val = p.x e.port ∧
        (readDepth p e.level ≤ q.2.val ∧
          q.2.val ≤ readDepth p e.level + 1 + (state.axes.getD e.port false).toNat ∨
        p.H - readDepth p f.level - 1 - (!(state.axes.getD e.port false)).toNat ≤ q.2.val ∧
          q.2.val ≤ p.H - readDepth p f.level) := by
  have hlo := readDepth_ge p hj hm
  have hhi := readDepth_add_lt_H p f.level
  have hb := Bool.toNat_le (state.axes.getD e.port false)
  have hn := Bool.toNat_le (!(state.axes.getD e.port false))
  simp only [endpointSegments, he, hf, hp, reduceCtorEq, ite_true, ite_false]
  simp only [List.drop_succ_cons, List.drop_zero, SegmentRecipe.mem_holes, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, or_and_right, exists_or, exists_eq_left]
  simp only [vertical_contains, horizontal_contains, onSide, coordinates, Coordinates.x, Coordinates.depth,
    readDepth, Scales.Parameters.x, ite_true, reduceCtorEq, ite_false] at *
  omega

private theorem pair_horizontal (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (i : ℕ) (gain : Bool) :
    (endpointSegments (coordinates p) { state with axes := state.axes.set i gain } e).drop 1 ++
        (endpointSegments (coordinates p) { state with axes := state.axes.set i gain } f).drop 1 =
      (endpointSegments (coordinates p) state e).drop 1 ++
        (endpointSegments (coordinates p) state f).drop 1 := by
  simp only [endpointSegments, List.drop_succ_cons, List.drop_zero]

private theorem horizontal_off_axis (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (hp : f.port = e.port) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointSegments (coordinates p) state e).drop 1 ++
        (endpointSegments (coordinates p) state f).drop 1)) : q.1.val ≠ p.x e.port := by
  have hx := readLength_add_lt_x p e.port 0
  have he := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
    else !(state.internal.getD e.internal false))
  have hf := Bool.toNat_le (if f.inward then state.internal.getD f.internal false
    else !(state.internal.getD f.internal false))
  simp only [endpointSegments, hp, List.drop_succ_cons, List.drop_zero,
    SegmentRecipe.mem_holes, List.mem_append, List.mem_singleton,
    or_and_right, exists_or, exists_eq_left, horizontal_contains] at hq
  change readLength p 0 + 64 < (coordinates p).x e.port at hx
  change _ ≠ (coordinates p).x e.port
  cases hd : e.inward <;> cases hd' : f.inward <;>
    simp only [inward, hd, hd', Bool.false_eq_true, ite_false, ite_true] at hq <;> omega

section Axis

variable (p : Scales.Parameters) (state : SignalState) (e f : Endpoint)
    (he : e.side = .upper) (hf : f.side = .lower) (hports : f.port = e.port)
    (hj : 1 ≤ f.level) (hm : f.level ≤ p.levels) (hport : e.port < p.axes)
    (hindex : e.port < state.axes.length) (gain : Bool)
    (hbefore : state.axes.getD e.port false = !gain)
    (ambient : Finset (Cell (p.W + 1) (p.H + 1)))
    (ha : Disjoint ambient (SegmentRecipe.holes (p.W + 1) (p.H + 1)
      [⟨(p.x e.port, readDepth p e.level + 2),
        (p.x e.port, p.H - readDepth p f.level - 2)⟩]))

include he hf hports hj hm hport hindex hbefore ha

/-- Flipping one actual shared axis bit is one complete vertical push. Its two ordinary
horizontal traces stay fixed; ambient holes avoid the central box-and-destination segment. -/
theorem axis_move (s t : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f))
    (htempty : t.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) { state with axes := state.axes.set e.port gain } e ++
        endpointSegments (coordinates p) { state with axes := state.axes.set e.port gain } f))
    (hp : (s.player.1.val, s.player.2.val) =
      (p.x e.port, if gain then readDepth p e.level + 1 else p.H - readDepth p f.level - 1))
    (ht : (t.player.1.val, t.player.2.val) =
      (p.x e.port, if gain then readDepth p e.level + 2 else p.H - readDepth p f.level - 2))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Move B none (if gain then .south else .north) s.toState t.toState := by
  have hu := readDepth_add_lt_D p e.level
  have hl := readDepth_add_lt_D p f.level
  have hH : p.H = 2 * p.D := rfl
  have hx := x_add_readLength_lt_W p hport 0
  have hupdate : (state.axes.set e.port gain).getD e.port false = gain := by
    simp [List.getD, hindex]
  have hfree (q : Cell (p.W + 1) (p.H + 1)) (hq : q.1.val = p.x e.port)
      (hlo : readDepth p e.level + 2 ≤ q.2.val)
      (hhi : q.2.val ≤ p.H - readDepth p f.level - 2) : q ∉ ambient := by
    intro hqA
    apply Finset.disjoint_left.mp ha hqA
    rw [SegmentRecipe.mem_holes]
    refine ⟨_, List.mem_singleton_self _, Or.inl ⟨rfl, hq, ?_, ?_⟩⟩ <;> dsimp only <;> omega
  let dest : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x e.port, by omega⟩,
      ⟨if gain then p.H - readDepth p f.level - 2 else readDepth p e.level + 2, by
        split_ifs <;> omega⟩)
  have hmem := pair_axis_mem p state e f he hf hports hj hm
  simp only [hbefore] at hmem
  have hmem' := pair_axis_mem p {state with axes := state.axes.set e.port gain}
    e f he hf hports hj hm
  simp only [pair_horizontal, hupdate] at hmem'
  have hplayer : s.player.1.val = p.x e.port := congrArg Prod.fst hp
  have htplayer : t.player.1.val = p.x e.port := congrArg Prod.fst ht
  have hpy : s.player.2.val = if gain then readDepth p e.level + 1
      else p.H - readDepth p f.level - 1 := congrArg Prod.snd hp
  have hty : t.player.2.val = if gain then readDepth p e.level + 2
      else p.H - readDepth p f.level - 2 := congrArg Prod.snd ht
  have htarget : t.empty = insert t.player (s.empty.erase dest) := by
    ext q
    rw [htempty, Finset.mem_union, hmem', Finset.mem_insert, Finset.mem_erase,
      hempty, Finset.mem_union, hmem]
    have hoff := horizontal_off_axis p state e f hports (q := q)
    have htp : q = t.player ↔ q.1.val = p.x e.port ∧ q.2.val = t.player.2.val := by
      simp only [Prod.ext_iff, Fin.ext_iff]; rw [htplayer]
    have hdp : q = dest ↔ q.1.val = p.x e.port ∧ q.2.val = dest.2.val := by
      simp only [Prod.ext_iff, Fin.ext_iff]; rfl
    simp only [ne_eq, htp, hdp]
    have hqa : q ∈ ambient → q.1.val ≠ p.x e.port ∨
        q.2.val < readDepth p e.level + 2 ∨ p.H - readDepth p f.level - 2 < q.2.val := by
      intro hqA
      by_contra! h
      exact hfree q h.1 h.2.1 h.2.2 hqA
    clear hdp htp
    by_cases hA : q ∈ ambient <;>
      by_cases hC : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        ((endpointSegments (coordinates p) state e).drop 1 ++
          (endpointSegments (coordinates p) state f).drop 1) <;>
      simp only [hA, hC, true_or, false_or, true_implies, true_iff, and_true] at hqa hoff ⊢ <;>
      cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
        Bool.not_true, Bool.toNat_false, Bool.toNat_true, Nat.add_zero, dest] at hty ⊢ <;> omega
  apply HoleState.move_to_first_hole s t (if gain then .south else .north) dest
    (p.H - readDepth p f.level - readDepth p e.level - 4) (by omega) _ _ _ _ _ htarget B hB
  · cases gain <;> simp [Direction.lane, dest, hplayer]
  · cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Direction.position, dest]
      at hpy ⊢ <;> omega
  · intro q hline hlo hhi hq
    rw [hempty, Finset.mem_union, hmem] at hq
    rcases hq with hq | hq | hq
    · cases gain <;> simp [Direction.lane, Direction.position, dest] at hpy hline hlo hhi
      all_goals exact hfree q (by omega) (by omega) (by omega) hq
    · have hoff := horizontal_off_axis p state e f hports hq
      cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Direction.lane] at hline <;> omega
    · cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
        Bool.not_true, Bool.toNat_false, Bool.toNat_true,
        Direction.lane, Direction.position, dest] at hpy hline hlo hhi hq <;> omega
  · rw [hempty, Finset.mem_union, hmem]
    cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.not_false,
      Bool.not_true, Bool.toNat_false, Bool.toNat_true, dest, true_and] <;> omega
  · cases gain <;> simp only [Bool.false_eq_true, ite_false, ite_true, Adjacent, Fin.ext_iff] at hpy hty ⊢ <;> omega

/-- The shared-axis macro constructs its actual target configuration and one legal step. -/
theorem axis_step (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f))
    (hp : (s.player.1.val, s.player.2.val) =
      (p.x e.port, if gain then readDepth p e.level + 1 else p.H - readDepth p f.level - 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointSegments (coordinates p) { state with axes := state.axes.set e.port gain } e ++
          endpointSegments (coordinates p) { state with axes := state.axes.set e.port gain } f) ∧
      (t.player.1.val, t.player.2.val) =
        (p.x e.port, if gain then readDepth p e.level + 2 else p.H - readDepth p f.level - 2) := by
  have hu := readDepth_add_lt_H p e.level
  let q : Cell (p.W + 1) (p.H + 1) :=
    (s.player.1, ⟨if gain then readDepth p e.level + 2 else p.H - readDepth p f.level - 2,
      by split_ifs <;> omega⟩)
  have hcoord : (q.1.val, q.2.val) =
      (p.x e.port, if gain then readDepth p e.level + 2 else p.H - readDepth p f.level - 2) := by
    have hx : s.player.1.val = p.x e.port := congrArg Prod.fst hp
    exact Prod.ext hx rfl
  let target := { state with axes := state.axes.set e.port gain }
  have hnew : target.axes.getD e.port false = gain := by
    simp [target, List.getD, hindex]
  have hq : q ∈ ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) target e ++ endpointSegments (coordinates p) target f) := by
    rw [Finset.mem_union, pair_axis_mem p target e f he hf hports hj hm]
    right; right
    have hcol : q.1.val = p.x e.port := congrArg Prod.fst hp
    simp only [hcol, true_and, hnew]
    cases gain <;> simp only [q, Bool.false_eq_true, ite_false, ite_true,
      Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true] <;> omega
  let t : HoleState (p.W + 1) (p.H + 1) := ⟨q, _, hq⟩
  exact ⟨t, ⟨_, axis_move p state e f he hf hports hj hm hport hindex gain hbefore
    ambient ha s t hempty rfl hp hcoord B hB⟩, rfl, hcoord⟩

end Axis

end PushPuzzle.PushS.PortLayout
