/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicRoundPolyTime
public import Push.CyclicRoundBudget
public import Push.CyclicSchedulePeeling

/-! Actual polynomial-time source/program families with one fixed cyclic read/clear skeleton. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicReader

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM
open scoped PushPuzzle.Push.AcceptanceProgram

/-- The read requests of a compact block, with an empty default for a clear block. -/
def readRequests : Round → List (ℕ × ℕ)
  | .read _ requests => requests
  | .clear .. => []

/-- The clear lanes of a compact block, with an empty default for a read block. -/
def clearLanes : Round → Finset ℕ
  | .read .. => ∅
  | .clear _ lanes => lanes

/-- The actual first read request list of a fixed-shape source family. -/
def firstRequests (rounds : List Round) : List (ℕ × ℕ) :=
  readRequests (rounds.headD (.read .west []))

/-- The actual first clear-lane set of a fixed-shape source family. -/
def firstLanes (rounds : List Round) : Finset ℕ :=
  clearLanes (rounds.headD (.read .west []))

@[fun_prop] theorem readRequests_polyTime : ComputableInPolyTime readRequests encRound Scan.encRequests := by
  have h := encRound_elim_polyTime (encP := encUnit) (encE := Scan.encRequests)
    (g0 := fun p => p.2.2) (g1 := fun _ => []) (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun block : Round => ((), block))
    encRound (encPair encUnit encRound) from by fun_prop)
  exact hh.of_enc_eq (by intro block; cases block <;> rfl)

@[fun_prop] theorem clearLanes_polyTime : ComputableInPolyTime clearLanes encRound encLaneSet := by
  have he : ComputableInPolyTime (fun _ : Unit × Direction × List (ℕ × ℕ) => (∅ : Finset ℕ))
      (encPair encUnit (encPair (encFinite Direction) Scan.encRequests)) encLaneSet :=
    ComputableInPolyTime.const _
  have h := encRound_elim_polyTime (encP := encUnit) (encE := encLaneSet)
    (g0 := fun _ => ∅) (g1 := fun p => p.2.2) he (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun block : Round => ((), block))
    encRound (encPair encUnit encRound) from by fun_prop)
  exact hh.of_enc_eq (by intro block; cases block <;> rfl)

@[fun_prop] theorem firstRequests_polyTime : ComputableInPolyTime firstRequests encRounds Scan.encRequests := by
  unfold firstRequests encRounds
  fun_prop

@[fun_prop] theorem firstLanes_polyTime : ComputableInPolyTime firstLanes encRounds encLaneSet := by
  unfold firstLanes encRounds
  fun_prop

/-- A fixed leading read shape recovers the actual first requests and literal remainder. -/
theorem read_cons_of_shapes (rounds : List Round) (side : Direction) (shapes : List (Bool × Direction))
    (hs : rounds.map Round.shape = (true, side) :: shapes) :
    rounds = .read side (firstRequests rounds) :: rounds.tail ∧
      rounds.tail.map Round.shape = shapes := by
  cases rounds with
  | nil => cases hs
  | cons block rest =>
    cases block with
    | read dir requests =>
      have hd : dir = side ∧ rest.map Round.shape = shapes := by simpa only [List.map_cons,
        Round.shape, List.cons.injEq, Prod.mk.injEq, true_and] using hs
      obtain ⟨hdir, hrest⟩ := hd
      subst dir
      exact ⟨rfl, hrest⟩
    | clear dir lanes => simp only [List.map_cons, Round.shape, List.cons.injEq, Prod.mk.injEq,
        Bool.false_eq_true, false_and] at hs

/-- A fixed leading clear shape recovers its actual finite lane set and literal remainder. -/
theorem clear_cons_of_shapes (rounds : List Round) (side : Direction) (shapes : List (Bool × Direction))
    (hs : rounds.map Round.shape = (false, side) :: shapes) :
    rounds = .clear side (firstLanes rounds) :: rounds.tail ∧
      rounds.tail.map Round.shape = shapes := by
  cases rounds with
  | nil => cases hs
  | cons block rest =>
    cases block with
    | read dir requests => simp only [List.map_cons, Round.shape, List.cons.injEq, Prod.mk.injEq,
        Bool.true_eq_false, false_and] at hs
    | clear dir lanes =>
      have hd : dir = side ∧ rest.map Round.shape = shapes := by simpa only [List.map_cons,
        Round.shape, List.cons.injEq, Prod.mk.injEq, true_and] using hs
      obtain ⟨hdir, hrest⟩ := hd
      subst dir
      exact ⟨rfl, hrest⟩

/-- A complete computed family satisfying the actual reader budget and the next erase preparation condition. -/
structure Family (α : Type) (enc : α ↪ List Bool) (shapes : List (Bool × Direction)) where
  reader : α → ColumnScan.Input
  rounds : α → List Round
  reader_polyTime : ComputableInPolyTime reader enc ColumnScan.Input.encoding
  rounds_polyTime : ComputableInPolyTime rounds enc encRounds
  shapes_eq : ∀ a, (rounds a).map Round.shape = shapes
  bounded : ∀ a, ∀ i ∈ instructions (rounds a), Cyclic.SourceBounded (reader a) i
  budget : ∀ a, Cyclic.Budget (reader a) (rounds a)
  extra_zero : ∀ a, (reader a).extraWidth = 0
  erase_ready : ∀ a, shapes[1]? = some (false, .north) → (reader a).height ≤ (reader a).quota

end PushPuzzle.Push.CyclicReader
