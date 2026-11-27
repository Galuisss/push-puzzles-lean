/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Single

/-!
# Explicit walks through empty straight corridors

These paths keep the box set fixed and move the player through adjacent empty
cells. Corridor freeness is a static geometric condition.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

def Free (B : Board w h) (boxes : Finset (Cell w h)) (p : Cell w h) : Prop :=
  p ∉ B.walls ∧ p ∉ boxes

/-- A specified finite sequence of adjacent free cells is a real walking path. -/
theorem walk_fin_path {B : Board w h} {boxes : Finset (Cell w h)} {n : ℕ}
    (hboxes : Disjoint boxes B.walls) (positions : Fin (n + 1) → Cell w h)
    (hfree : ∀ i, Free B boxes (positions i))
    (hadj : ∀ i : Fin n, ∃ d, Adjacent d (positions i.castSucc) (positions i.succ)) :
    ∀ i, Reachable B (some 1) ⟨positions 0, boxes⟩ ⟨positions i, boxes⟩ := by
  intro i
  induction i using Fin.induction with
  | zero => exact .refl
  | succ i ih =>
    obtain ⟨d, hd⟩ := hadj i
    have hs : (⟨positions i.castSucc, boxes⟩ : State w h).Valid B :=
      ⟨(hfree i.castSucc).1, hboxes, (hfree i.castSucc).2⟩
    exact ih.tail ⟨d, Move.single_iff.mpr (SingleMoveView.walk hs hd (hfree i.succ).1 (hfree i.succ).2)⟩

private theorem walk_east {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (x : Fin w) (y : Fin h) (k : ℕ)
    (hk : x.val + k < w)
    (hfree : ∀ a : Fin w, x.val ≤ a.val → a.val ≤ x.val + k → Free B boxes (a, y)) :
    Reachable B (some 1) ⟨(x, y), boxes⟩ ⟨(⟨x.val + k, hk⟩, y), boxes⟩ := by
  let positions : Fin (k + 1) → Cell w h :=
    fun i => (⟨x.val + i.val, by have := i.isLt; omega⟩, y)
  have hstart : positions 0 = (x, y) := by apply Prod.ext <;> apply Fin.ext <;> simp [positions]
  have hend : positions (Fin.last k) = (⟨x.val + k, hk⟩, y) := rfl
  rw [← hstart, ← hend]
  apply walk_fin_path hboxes positions
  · intro i
    exact hfree _ (by dsimp [positions]; omega) (by dsimp [positions]; have := i.isLt; omega)
  · intro i
    exact ⟨.east, by simp [Adjacent, positions, Nat.add_assoc]⟩

private theorem walk_west {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (x : Fin w) (y : Fin h) (k : ℕ)
    (hk : k ≤ x.val)
    (hfree : ∀ a : Fin w, x.val - k ≤ a.val → a.val ≤ x.val → Free B boxes (a, y)) :
    Reachable B (some 1) ⟨(x, y), boxes⟩
      ⟨(⟨x.val - k, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩, y), boxes⟩ := by
  let positions : Fin (k + 1) → Cell w h :=
    fun i => (⟨x.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩, y)
  have hstart : positions 0 = (x, y) := by apply Prod.ext <;> apply Fin.ext <;> simp [positions]
  have hend : positions (Fin.last k) =
      (⟨x.val - k, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩, y) := rfl
  rw [← hstart, ← hend]
  apply walk_fin_path hboxes positions
  · intro i
    exact hfree _ (by dsimp [positions]; have := i.isLt; omega) (by dsimp [positions]; omega)
  · intro i
    refine ⟨.west, ?_, rfl⟩
    dsimp [positions]
    have := i.isLt
    omega

private theorem walk_south {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (x : Fin w) (y : Fin h) (k : ℕ)
    (hk : y.val + k < h)
    (hfree : ∀ b : Fin h, y.val ≤ b.val → b.val ≤ y.val + k → Free B boxes (x, b)) :
    Reachable B (some 1) ⟨(x, y), boxes⟩ ⟨(x, ⟨y.val + k, hk⟩), boxes⟩ := by
  let positions : Fin (k + 1) → Cell w h :=
    fun i => (x, ⟨y.val + i.val, by have := i.isLt; omega⟩)
  have hstart : positions 0 = (x, y) := by apply Prod.ext <;> apply Fin.ext <;> simp [positions]
  have hend : positions (Fin.last k) = (x, ⟨y.val + k, hk⟩) := rfl
  rw [← hstart, ← hend]
  apply walk_fin_path hboxes positions
  · intro i
    exact hfree _ (by dsimp [positions]; omega) (by dsimp [positions]; have := i.isLt; omega)
  · intro i
    exact ⟨.south, by simp [Adjacent, positions, Nat.add_assoc]⟩

private theorem walk_north {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (x : Fin w) (y : Fin h) (k : ℕ)
    (hk : k ≤ y.val)
    (hfree : ∀ b : Fin h, y.val - k ≤ b.val → b.val ≤ y.val → Free B boxes (x, b)) :
    Reachable B (some 1) ⟨(x, y), boxes⟩
      ⟨(x, ⟨y.val - k, lt_of_le_of_lt (Nat.sub_le _ _) y.isLt⟩), boxes⟩ := by
  let positions : Fin (k + 1) → Cell w h :=
    fun i => (x, ⟨y.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) y.isLt⟩)
  have hstart : positions 0 = (x, y) := by apply Prod.ext <;> apply Fin.ext <;> simp [positions]
  have hend : positions (Fin.last k) =
      (x, ⟨y.val - k, lt_of_le_of_lt (Nat.sub_le _ _) y.isLt⟩) := rfl
  rw [← hstart, ← hend]
  apply walk_fin_path hboxes positions
  · intro i
    exact hfree _ (by dsimp [positions]; have := i.isLt; omega) (by dsimp [positions]; omega)
  · intro i
    refine ⟨.north, rfl, ?_⟩
    dsimp [positions]
    have := i.isLt
    omega

/-- Walk between arbitrary endpoints of an empty row interval. -/
theorem walk_horizontal {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (a b : Fin w) (y : Fin h)
    (hfree : ∀ x : Fin w, min a.val b.val ≤ x.val → x.val ≤ max a.val b.val →
      Free B boxes (x, y)) :
    Reachable B (some 1) ⟨(a, y), boxes⟩ ⟨(b, y), boxes⟩ := by
  by_cases hab : a.val ≤ b.val
  · have hk : a.val + (b.val - a.val) < w := by have := b.isLt; omega
    have he : (⟨a.val + (b.val - a.val), hk⟩ : Fin w) = b := by apply Fin.ext; dsimp; omega
    rw [← he]
    apply walk_east hboxes a y (b.val - a.val) hk
    intro x hlo hhi
    exact hfree x (by omega) (by omega)
  · have hk : a.val - b.val ≤ a.val := Nat.sub_le _ _
    have he : (⟨a.val - (a.val - b.val), lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩ : Fin w) = b := by
      apply Fin.ext; dsimp; omega
    rw [← he]
    apply walk_west hboxes a y (a.val - b.val) hk
    intro x hlo hhi
    exact hfree x (by omega) (by omega)

theorem walk_vertical {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (x : Fin w) (a b : Fin h)
    (hfree : ∀ y : Fin h, min a.val b.val ≤ y.val → y.val ≤ max a.val b.val →
      Free B boxes (x, y)) :
    Reachable B (some 1) ⟨(x, a), boxes⟩ ⟨(x, b), boxes⟩ := by
  by_cases hab : a.val ≤ b.val
  · have hk : a.val + (b.val - a.val) < h := by have := b.isLt; omega
    have he : (⟨a.val + (b.val - a.val), hk⟩ : Fin h) = b := by apply Fin.ext; dsimp; omega
    rw [← he]
    apply walk_south hboxes x a (b.val - a.val) hk
    intro y hlo hhi
    exact hfree y (by omega) (by omega)
  · have hk : a.val - b.val ≤ a.val := Nat.sub_le _ _
    have he : (⟨a.val - (a.val - b.val), lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩ : Fin h) = b := by
      apply Fin.ext; dsimp; omega
    rw [← he]
    apply walk_north hboxes x a (a.val - b.val) hk
    intro y hlo hhi
    exact hfree y (by omega) (by omega)

/-- Prepare one horizontal push from an empty parallel lane and return to the
same hub afterward. All lane travel is expanded by `walk_horizontal`; the box
set changes exactly by the specified single-box push. This works on either side
of the track, using the explicitly supplied vertical entry and exit edges. -/
theorem push_via_parallel_row {B : Board w h} {boxes : Finset (Cell w h)}
    (hboxes : Disjoint boxes B.walls) (hub a x b : Fin w) (u y : Fin h)
    (entry d : Direction)
    (hentry : Adjacent entry (a, u) (a, y))
    (hexit : Adjacent entry.opposite (x, y) (x, u))
    (hax : Adjacent d (a, y) (x, y)) (hxb : Adjacent d (x, y) (b, y))
    (hsupport : Free B boxes (a, y)) (hsource : (x, y) ∈ boxes)
    (hdest : Free B boxes (b, y))
    (hlaneIn : ∀ z : Fin w, min hub.val a.val ≤ z.val → z.val ≤ max hub.val a.val →
      Free B boxes (z, u))
    (hlaneOut : ∀ z : Fin w, min x.val hub.val ≤ z.val → z.val ≤ max x.val hub.val →
      Free B boxes (z, u)) :
    Reachable B (some 1) ⟨(hub, u), boxes⟩ ⟨(hub, u), insert (b, y) (boxes.erase (x, y))⟩ := by
  have hrowne : u ≠ y := by
    intro he
    exact hentry.ne (by rw [he])
  have hin := walk_horizontal hboxes hub a u hlaneIn
  have hfreeA : Free B boxes (a, u) := hlaneIn a (by omega) (by omega)
  have hdown : SingleMoveView B entry (⟨(a, u), boxes⟩ : State w h) ⟨(a, y), boxes⟩ :=
    SingleMoveView.walk ⟨hfreeA.1, hboxes, hfreeA.2⟩ hentry hsupport.1 hsupport.2
  have hpush : SingleMoveView B d (⟨(a, y), boxes⟩ : State w h)
      ⟨(x, y), insert (b, y) (boxes.erase (x, y))⟩ :=
    SingleMoveView.push ⟨hsupport.1, hboxes, hsupport.2⟩ hax hsource hxb hdest.1 hdest.2
  have hfreeNew : ∀ z : Fin w, min x.val hub.val ≤ z.val → z.val ≤ max x.val hub.val →
      Free B (insert (b, y) (boxes.erase (x, y))) (z, u) := by
    intro z hlo hhi
    have hf := hlaneOut z hlo hhi
    refine ⟨hf.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hrowne (congrArg Prod.snd he)
    · exact hf.2 (Finset.mem_of_mem_erase he)
  have hfreeX := hfreeNew x (by omega) (by omega)
  have hup : SingleMoveView B entry.opposite
      (⟨(x, y), insert (b, y) (boxes.erase (x, y))⟩ : State w h)
      ⟨(x, u), insert (b, y) (boxes.erase (x, y))⟩ :=
    SingleMoveView.walk hpush.valid_target hexit hfreeX.1 hfreeX.2
  have hout := walk_horizontal hpush.valid_target.2.1 x hub u hfreeNew
  exact (((hin.tail ⟨entry, Move.single_iff.mpr hdown⟩).tail ⟨d, Move.single_iff.mpr hpush⟩).tail ⟨entry.opposite, Move.single_iff.mpr hup⟩).trans hout

end PushPuzzle.PushFS
