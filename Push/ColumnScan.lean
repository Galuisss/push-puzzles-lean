/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Basic
public import PushS.HoleState
public import Push.ConvexSupport
public import Mathlib.Data.List.GetD

/-! The committed column reader: source rectangle, three-hole seal, room, and needles. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan

open PushFS PushS

/-- A live source rectangle and a quota for every source column. -/
structure Input where
  width : ℕ
  height : ℕ
  initial : HoleState width height
  quotas : List ℕ
  quotas_width : quotas.length = width
  quotas_le : quotas.sum ≤ initial.empty.card
  /-- Additional empty room columns used by subsequent reader rounds. -/
  extraWidth : ℕ := 0

namespace Input

variable (r : Input)

theorem width_pos : 0 < r.width := Nat.zero_lt_of_lt r.initial.player.1.isLt
theorem height_pos : 0 < r.height := Nat.zero_lt_of_lt r.initial.player.2.isLt

/-- Number of source holes, including the player's cell. -/
def sourceHoles : ℕ := r.initial.empty.card

/-- The total number of requested source holes. -/
def quota : ℕ := r.quotas.sum

/-- The separation leaves more rows than the source holes and the source columns. -/
def length : ℕ := max 7 (r.quota + max r.sourceHoles r.width + 4)

/-- Source columns, the seal, and the complete eastern room. -/
def outputWidth : ℕ := r.width + 2 + r.extraWidth
/-- Source rows plus the separated reader room. -/
def outputHeight : ℕ := r.height + r.length

theorem length_ge_seven : 7 ≤ r.length := Nat.le_max_left _ _

theorem separation : r.quota + max r.sourceHoles r.width + 4 ≤ r.length :=
  Nat.le_max_right _ _

/-- The lowest needle, next to the seal's landing cell. -/
def firstLevel : ℕ := r.height - 1 + r.length - 2

/-- Reading the columns from right to left lowers the next needle by the current quota. -/
def needleLevel (i : Fin r.width) : ℕ :=
  r.firstLevel - (r.quotas.drop (i.val + 1)).sum

/-- The final needle traversal ends at this level in the leftmost source column. -/
def targetLevel : ℕ := r.firstLevel - r.quota

/-- The level after reading all columns at or to the right of this boundary. -/
def readLevel (k : ℕ) : ℕ := r.firstLevel - (r.quotas.drop k).sum

private theorem drop_sum_le (xs : List ℕ) (i : ℕ) : (xs.drop i).sum ≤ xs.sum := by
  have h := congrArg List.sum (List.take_append_drop i xs)
  rw [List.sum_append] at h
  omega

theorem targetLevel_lower : r.height + max r.sourceHoles r.width < r.targetLevel := by
  have := r.separation
  have := r.height_pos
  dsimp [targetLevel, firstLevel]
  omega

theorem targetLevel_le_needleLevel (i : Fin r.width) : r.targetLevel ≤ r.needleLevel i := by
  have := drop_sum_le r.quotas (i.val + 1)
  dsimp [targetLevel, needleLevel, quota]
  omega

private theorem needleLevel_le_firstLevel (i : Fin r.width) : r.needleLevel i ≤ r.firstLevel :=
  Nat.sub_le _ _

theorem firstLevel_lt_height : r.firstLevel < r.outputHeight := by
  have := r.height_pos
  dsimp [firstLevel, outputHeight]
  omega

theorem needleLevel_eq_readLevel (i : Fin r.width) :
    r.needleLevel i = r.readLevel (i.val + 1) := rfl

theorem readLevel_zero : r.readLevel 0 = r.targetLevel := by
  simp only [readLevel, List.drop_zero, targetLevel, quota]

/-- Adjacent needle boundaries differ by exactly that column's prescribed quota. -/
theorem readLevel_succ (i : Fin r.width) :
    r.readLevel (i.val + 1) = r.readLevel i.val + r.quotas.getD i.val 0 := by
  have hi : i.val < r.quotas.length := r.quotas_width.symm ▸ i.isLt
  have hs : (r.quotas.drop i.val).sum =
      r.quotas.getD i.val 0 + (r.quotas.drop (i.val + 1)).sum := by
    rw [List.drop_eq_getElem_cons hi, List.sum_cons, List.getD_eq_getElem _ _ hi]
  have hsum := drop_sum_le r.quotas i.val
  have hbound := r.targetLevel_lower
  dsimp [readLevel, targetLevel, quota] at hbound ⊢
  omega

theorem needleLevel_lt_height (i : Fin r.width) : r.needleLevel i < r.outputHeight :=
  (r.needleLevel_le_firstLevel i).trans_lt r.firstLevel_lt_height

/-- The source occupies exactly the original top-left rectangle. -/
def embed (q : Cell r.width r.height) : Cell r.outputWidth r.outputHeight :=
  (⟨q.1.val, by have := q.1.isLt; dsimp [outputWidth]; omega⟩,
    ⟨q.2.val, by have := q.2.isLt; dsimp [outputHeight]; omega⟩)

theorem embed_injective : Function.Injective r.embed := by
  intro a b hab
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg (fun q => q.1.val) hab
  · exact congrArg (fun q => q.2.val) hab

/-- The unchanged source holes inside the enlarged rectangle. -/
def sourceEmpty : Finset (Cell r.outputWidth r.outputHeight) := r.initial.empty.image r.embed

/-- The sole side door from the source rectangle. -/
def door : Cell r.outputWidth r.outputHeight :=
  (⟨r.width, by dsimp [outputWidth]; omega⟩,
    ⟨r.height - 1, by have := r.height_pos; dsimp [outputHeight]; omega⟩)

/-- The second upper seal hole. -/
def upper : Cell r.outputWidth r.outputHeight :=
  (r.door.1, ⟨r.height, by have := r.length_ge_seven; dsimp [outputHeight]; omega⟩)

/-- The lower seal hole at the room's bottom. -/
def bottom : Cell r.outputWidth r.outputHeight :=
  (r.door.1, ⟨r.outputHeight - 1, by have := r.height_pos; dsimp [outputHeight]; omega⟩)

/-- The first committed landing, reached by consuming both upper seal holes. -/
def landing : Cell r.outputWidth r.outputHeight :=
  (r.door.1, ⟨r.firstLevel, r.firstLevel_lt_height⟩)

/-- The entire eastern room lies below the original source rows. -/
def room : Finset (Cell r.outputWidth r.outputHeight) :=
  Finset.univ.filter fun q => r.width < q.1.val ∧ r.height ≤ q.2.val

/-- One original needle in each source column. -/
def needle (i : Fin r.width) : Cell r.outputWidth r.outputHeight :=
  (⟨i.val, by have := i.isLt; dsimp [outputWidth]; omega⟩,
    ⟨r.needleLevel i, r.needleLevel_lt_height i⟩)

/-- The complete finite set of original column needles. -/
def needles : Finset (Cell r.outputWidth r.outputHeight) := Finset.univ.image r.needle

/-- All other cells of the extension contain ordinary movable boxes. -/
def empty : Finset (Cell r.outputWidth r.outputHeight) :=
  r.sourceEmpty ∪ ({r.door, r.upper, r.bottom} ∪ r.room ∪ r.needles)

/-- The ordinary player destination at the end of the leftmost quota. -/
def target : Cell r.outputWidth r.outputHeight :=
  (⟨0, by dsimp [outputWidth]; omega⟩,
    ⟨r.targetLevel, (r.targetLevel_le_needleLevel ⟨0, r.width_pos⟩).trans_lt
      (r.needleLevel_lt_height _)⟩)

/-- The literal initial player and hole set on the extended board. -/
def initialState : HoleState r.outputWidth r.outputHeight where
  player := r.embed r.initial.player
  empty := r.empty
  player_empty := Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨r.initial.player, r.initial.player_empty, rfl⟩)

/-- The literal no-wall player-target instance emitted by the column reader. -/
def compile : Push.Instance where
  width := r.outputWidth
  height := r.outputHeight
  initial := r.initialState.toState
  target := r.target
  player_empty := by simpa only [HoleState.toState, Finset.mem_compl, not_not] using
    r.initialState.player_empty

theorem needleLevel_rightmost :
    r.needleLevel ⟨r.width - 1, by have := r.width_pos; omega⟩ = r.firstLevel := by
  have hn : r.width - 1 + 1 = r.quotas.length := by rw [r.quotas_width]; have := r.width_pos; omega
  simp only [needleLevel, hn, List.drop_length, List.sum_nil, Nat.sub_zero]

/-- The needle and target region lies strictly beyond both source budgets. -/
theorem needle_far_south (i : Fin r.width) :
    r.height + max r.sourceHoles r.width < (r.needle i).2.val :=
  r.targetLevel_lower.trans_le (r.targetLevel_le_needleLevel i)

/-- The source bitmap is copied exactly; no auxiliary reader hole lies in its rectangle. -/
theorem embed_mem_empty (q : Cell r.width r.height) :
    r.embed q ∈ r.empty ↔ q ∈ r.initial.empty := by
  have hqx := q.1.isLt
  have hqy := q.2.isLt
  have hheight := r.height_pos
  have hlength := r.length_ge_seven
  have hsource : r.embed q ∈ r.sourceEmpty ↔ q ∈ r.initial.empty := by
    simp only [sourceEmpty, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right]
  rw [empty, Finset.mem_union, hsource]
  suffices r.embed q ∉ ({r.door, r.upper, r.bottom} ∪ r.room ∪ r.needles) by tauto
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  rintro (((he | he | he) | he) | he)
  · have := congrArg (fun p => p.1.val) he
    change q.1.val = r.width at this
    omega
  · have := congrArg (fun p => p.1.val) he
    change q.1.val = r.width at this
    omega
  · have := congrArg (fun p => p.1.val) he
    change q.1.val = r.width at this
    omega
  · have := (Finset.mem_filter.mp he).2.1
    change r.width < q.1.val at this
    omega
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
    have hy := congrArg (fun p => p.2.val) hi
    have hf := r.needle_far_south i
    change (r.needle i).2.val = q.2.val at hy
    omega

/-- The only auxiliary hole on a source row is its lower-right side door. -/
theorem empty_on_source_row {q : Cell r.outputWidth r.outputHeight}
    (hq : q ∈ r.empty) (hy : q.2.val < r.height) : q.1.val < r.width ∨ q = r.door := by
  rw [empty, Finset.mem_union] at hq
  rcases hq with hs | ha
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
    exact Or.inl a.1.isLt
  · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (((he | he | he) | he) | he)
    · exact Or.inr he
    · have := congrArg (fun q => q.2.val) he
      change q.2.val = r.height at this
      omega
    · have := congrArg (fun q => q.2.val) he
      change q.2.val = r.height + r.length - 1 at this
      have hlen := r.length_ge_seven
      have hpos := r.height_pos
      omega
    · have := (Finset.mem_filter.mp he).2.2
      omega
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
      have hf := r.needle_far_south i
      have hi' := congrArg (fun q => q.2.val) hi
      omega

/-- The reader's eastern column has no hole at or north of the source corner. -/
theorem east_full_on_source_rows (q : Cell r.outputWidth r.outputHeight)
    (hx : r.width < q.1.val) (hy : q.2.val < r.height) : q ∈ r.compile.initial.boxes := by
  change q ∈ r.emptyᶜ
  apply Finset.mem_compl.mpr
  intro he
  rcases r.empty_on_source_row he hy with h | h
  · omega
  · have := congrArg (fun q => q.1.val) h
    change q.1.val = r.width at this
    omega

/-- The separator and the eastern column are solid strictly north of the source corner. -/
theorem northeast_full_initial (q : Cell r.outputWidth r.outputHeight)
    (hx : r.width ≤ q.1.val) (hy : q.2.val + 1 < r.height) : q ∈ r.compile.initial.boxes := by
  change q ∈ r.emptyᶜ
  apply Finset.mem_compl.mpr
  intro he
  rcases r.empty_on_source_row he (by omega) with h | h
  · omega
  · have := congrArg (fun q => q.2.val) h
    change q.2.val = r.height - 1 at this
    omega

/-- No play can open a second side door on any original source row. -/
theorem east_full {t : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.board none r.compile.initial t)
    (q : Cell r.outputWidth r.outputHeight) (hx : r.width < q.1.val)
    (hy : q.2.val < r.height) : q ∈ t.boxes := by
  apply Push.Support.northeast_full (r.width + 1) (r.height - 1) hr
    (fun a ha hb => r.east_full_on_source_rows a (by omega) (by have := r.height_pos; omega)) q
  · omega
  · omega

/-- The region north of the unique source exit stays solid for arbitrary trajectories. -/
theorem northeast_full {t : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.board none r.compile.initial t)
    (q : Cell r.outputWidth r.outputHeight) (hx : r.width ≤ q.1.val)
    (hy : q.2.val + 1 < r.height) : q ∈ t.boxes := by
  apply Push.Support.northeast_full r.width (r.height - 2) hr
    (fun a ha hb => r.northeast_full_initial a ha (by omega)) q hx
  omega

end Input
end PushPuzzle.Push.ColumnScan
