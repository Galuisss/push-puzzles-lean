/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.Geometry

/-! Polynomial-time wall, box and player queries and state legality checking. -/

@[expose] public section

namespace PushPuzzle.PushFS.Machine


open Turing.MultiTapeTM ComputableInPolyTime

abbrev Query := Instance × List Bool × RawCell
abbrev encQuery : Query ↪ List Bool := encPair encoding (encPair encBits encRawCell)

/-- Query the box bitmap of a raw state code. -/
def boxAt (q : Query) : Bool := bitAt (q.2.1, index (q.1.width, q.2.2))

@[fun_prop] theorem boxAt_polyTime : ComputableInPolyTime boxAt encQuery encBool := by
  unfold boxAt
  fun_prop

/-- Query the player bitmap, after the first `area` box bits. -/
def playerAt (q : Query) : Bool := bitAt (q.2.1, q.1.area + index (q.1.width, q.2.2))

@[fun_prop] theorem playerAt_polyTime : ComputableInPolyTime playerAt encQuery encBool := by
  unfold playerAt
  fun_prop

/-- The wall bit is always taken from the immutable board. -/
def wallAt (q : Instance × RawCell) : Bool :=
  bitAt (flags Encoding.Tile.wall q.1, index (q.1.width, q.2))

@[fun_prop] theorem wallAt_polyTime :
    ComputableInPolyTime wallAt (encPair encoding encRawCell) encBool := by
  unfold wallAt
  have hw := flags_polyTime Encoding.Tile.wall
  fun_prop

/-- Every genuine coordinate has an in-bounds bitmap address. -/
private theorem index_lt (I : Instance) (p : Cell I.width I.height) :
    index (I.width, rawCell p) < I.area := by
  rw [index_eq]
  simpa [Instance.area, Nat.mul_comm] using (finProdFinEquiv p.swap).isLt

private theorem bitAt_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    bitAt (List.ofFn f, i.val) = f i := by
  simp [bitAt, i.isLt]

theorem boxAt_correct (I : Instance) (s : State I.width I.height) (p : Cell I.width I.height) :
    boxAt (I, s.bits, rawCell p) = decide (p ∈ s.boxes) := by
  unfold boxAt bitAt
  rw [State.bits, List.getElem?_append_left (by simpa [Instance.area] using index_lt I p)]
  change bitAt (s.boxBits, index (I.width, rawCell p)) = _
  rw [index_eq]
  exact (bitAt_ofFn _ (finProdFinEquiv p.swap)).trans (by simp)

theorem playerAt_correct (I : Instance) (s : State I.width I.height) (p : Cell I.width I.height) :
    playerAt (I, s.bits, rawCell p) = decide (p = s.player) := by
  unfold playerAt bitAt
  rw [State.bits, List.getElem?_append_right (by simp [Instance.area])]
  simp only [State.length_boxBits, Instance.area, Nat.add_sub_cancel_left]
  change bitAt (s.playerBits, index (I.width, rawCell p)) = _
  rw [index_eq]
  exact (bitAt_ofFn _ (finProdFinEquiv p.swap)).trans (by simp)

theorem wallAt_correct (I : Instance) (p : Cell I.width I.height) :
    wallAt (I, rawCell p) = decide (p ∈ I.board.walls) := by
  unfold wallAt
  rw [flags_eq_ofFn, index_eq, bitAt_ofFn]
  simp [Encoding.tile]

/-- Test whether a code represents a board-valid state, assuming its syntax is
already a valid state code. The separate state decoder checks that syntax. -/
def valid (q : Instance × List Bool) : Bool :=
  (cells (q.1.width, q.1.height)).all fun p =>
    (!boxAt (q.1, q.2, p) || !wallAt (q.1, p)) &&
    (!playerAt (q.1, q.2, p) || (!wallAt (q.1, p) && !boxAt (q.1, q.2, p)))

@[fun_prop] theorem valid_polyTime :
    ComputableInPolyTime valid (encPair encoding encBits) encBool := by
  unfold valid
  apply allWithInput
  · fun_prop
  · fun_prop

/-- The raw Boolean legality check is exactly the semantic state invariant. -/
theorem valid_correct (I : Instance) (s : State I.width I.height) :
    valid (I, s.bits) = true ↔ s.Valid I.board := by
  simp only [valid, List.all_eq_true, forall_cells_iff]
  simp only [ boxAt_correct, wallAt_correct, playerAt_correct,
    Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro hv
    have hp := hv s.player
    refine ⟨?_, Finset.disjoint_left.mpr ?_, ?_⟩
    · exact hp.2.resolve_left (by simp) |>.1
    · intro p hb hw
      exact (hv p).1.elim (fun hn => hn hb) (fun hn => hn hw)
    · exact hp.2.resolve_left (by simp) |>.2
  · rintro ⟨hp, hb, he⟩ p
    constructor
    · by_cases hbox : p ∈ s.boxes
      · exact Or.inr (fun hw => Finset.disjoint_left.mp hb hbox hw)
      · exact Or.inl hbox
    · by_cases hplayer : p = s.player
      · subst p
        exact Or.inr ⟨hp, he⟩
      · exact Or.inl hplayer

end PushPuzzle.PushFS.Machine
