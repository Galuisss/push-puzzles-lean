/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanNeedles
public import Push.SealProjection

/-! The actual committed reader closes its source door before its first western southern visit. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier SealProjection

variable (r : ColumnScan.Input)

private theorem empty_on_separator {p : Cell r.outputWidth r.outputHeight}
    (hp : p ∈ r.empty) (hx : p.1.val = r.width) : p = r.door ∨ p = r.upper ∨ p = r.bottom := by
  simp only [empty, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hs | (((hp | hp | hp) | hp) | hp)
  · obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hs
    have hqx := q.1.isLt
    have he := congrArg (fun q => q.1.val) hq
    change q.1.val = p.1.val at he
    omega
  · exact Or.inl hp
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr hp)
  · have := (Finset.mem_filter.mp hp).2.1
    omega
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
    have hix := i.isLt
    have he := congrArg (fun q => q.1.val) hi
    change i.val = p.1.val at he
    omega

/-- The actual separator column starts with precisely the seal's three ordinary holes. -/
private theorem separator_initial_holes :
    columnHoles r.width (r.outputHeight - 1 : ℕ) r.compile.initial =
      ({0, (r.length : ℤ) - 1, (r.length : ℤ)} : Finset ℤ) := by
  change columnHoles r.width (r.outputHeight - 1 : ℕ) r.initialState.toState = _
  have hheight := r.height_pos
  have hlength := r.length_ge_seven
  have hd : coordinate (r.outputHeight - 1 : ℕ) r.door = r.length := by
    dsimp [coordinate, door, outputHeight]
    omega
  have hu : coordinate (r.outputHeight - 1 : ℕ) r.upper = (r.length : ℤ) - 1 := by
    dsimp [coordinate, upper, outputHeight]
    omega
  have hb : coordinate (r.outputHeight - 1 : ℕ) r.bottom = 0 := by
    simp only [coordinate, bottom, Int.sub_self]
  ext z
  constructor
  · intro hz
    obtain ⟨p, hp, hpx, hcoord⟩ := mem_columnHoles.mp hz
    rw [r.initialState.holes_toState] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases r.empty_on_separator hp hpx with he | he | he
    · rw [he, hd] at hcoord
      exact Or.inr (Or.inr hcoord.symm)
    · rw [he, hu] at hcoord
      exact Or.inr (Or.inl hcoord.symm)
    · rw [he, hb] at hcoord
      exact Or.inl hcoord.symm
  · intro hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact mem_columnHoles.mpr ⟨r.bottom, by rw [r.initialState.holes_toState]; change _ ∈ r.empty; simp only [empty, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto, rfl, hb⟩
    · exact mem_columnHoles.mpr ⟨r.upper, by rw [r.initialState.holes_toState]; change _ ∈ r.empty; simp only [empty, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto, rfl, hu⟩
    · exact mem_columnHoles.mpr ⟨r.door, by rw [r.initialState.holes_toState]; change _ ∈ r.empty; simp only [empty, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto, rfl, hd⟩

/-- The committed landing is exactly coordinate two in the separator column. -/
private theorem landing_seal_coordinate : coordinate (r.outputHeight - 1 : ℕ) r.landing = 2 := by
  have := r.height_pos
  have := r.length_ge_seven
  dsimp [coordinate, landing, firstLevel, outputHeight]
  omega

/-- The original source door is exactly the seal's upper endpoint. -/
private theorem door_seal_coordinate : coordinate (r.outputHeight - 1 : ℕ) r.door = r.length := by
  have := r.height_pos
  dsimp [coordinate, door, outputHeight]
  omega

/-- A successful pre-needle prefix cannot create a separator hole by a horizontal push. -/
private theorem before_south_move_guard
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hm : Move r.compile.board none d s t)
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    d = .east ∨ d = .west → s.boxes ≠ t.boxes → t.player.1.val ≠ r.width := by
  intro hd hchanged htx
  have hreach : Reachable r.compile.board none r.compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hr
  have hN := reachable_north hr (r.initial_north r.width)
  have hstep : Step r.compile.board none s t := ⟨d, hm⟩
  have hsf := (Relation.ReflTransGen.single hstep).trans htf
  cases hm with
  | walk _ _ _ _ hb => exact hchanged hb.symm
  | @push n hv hn hc run hp hb =>
    let q : Cell r.outputWidth r.outputHeight := run.cell ⟨n + 1, by omega⟩
    have ha := players_adjacent (Move.push hv hn hc run hp hb)
    have hpos := run.position ⟨n + 1, by omega⟩
    have hlane := run.lane ⟨n + 1, by omega⟩
    rcases hd with rfl | rfl
    · simp only [Adjacent, Direction.position, Direction.lane] at ha hpos hlane
      have hsx : s.player.1.val < r.width := by omega
      have hsy := congrArg Fin.val ha.2
      by_cases hy : t.player.2.val < r.height
      · have hqx : r.width < q.1.val := by dsimp [q]; omega
        have hqy : q.2.val < r.height := by dsimp [q]; omega
        exact run.empty (r.east_full hreach q hqx hqy)
      · have hsHole := player_mem_holes hv
        obtain ⟨i, hi⟩ := (r.before_south_exact hr hsf hfx hfy hsx (by omega)).mp hsHole
        have hyi := congrArg (fun q => q.2.val) hi
        have hyi' := r.targetLevel_le_needleLevel i
        have := hN hsx
        change r.needleLevel i = s.player.2.val at hyi
        omega
    · simp only [Adjacent, Direction.position, Direction.lane] at ha hpos hlane
      have hsy := congrArg Fin.val ha.2
      by_cases hy : t.player.2.val < r.height
      · have hsp := r.east_full hreach s.player (by omega) (by omega)
        exact hv.2.2 hsp
      · have hqx : q.1.val < r.width := by dsimp [q]; omega
        have hqy : r.height ≤ q.2.val := by dsimp [q]; omega
        obtain ⟨i, hi⟩ := (r.before_south_exact hr hsf hfx hfy hqx hqy).mp
          ((mem_holes _).mpr run.empty)
        have htN : North r.width r.targetLevel t := fun hx => by omega
        have hneedle := r.before_south_all_needles (hr.tail ⟨hstep, htN⟩) htf hfx hfy i
        rw [hi, mem_holes] at hneedle
        exact hneedle (by rw [hb]; exact Finset.mem_insert_self _ _)

/-- The entire prefix preceding a western southern visit obeys the seal projection guard. -/
private theorem before_south_guarded
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    Relation.ReflTransGen (GuardedStep r.compile.board none r.width) r.initialState.toState s := by
  revert hsf
  induction hr with
  | refl => exact fun _ => .refl
  | @tail u v hpre hm ih =>
    intro hvf
    have huf := (Relation.ReflTransGen.single hm.1).trans hvf
    exact (ih huf).tail ⟨hm.1.choose, hm.1.choose_spec,
      r.before_south_move_guard hpre hm.1.choose_spec hvf hfx hfy⟩

/-- At the actual committed landing, the source door has already become an ordinary box. -/
theorem landing_door_occupied
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : s.player = r.landing) : r.door ∈ s.boxes := by
  have hL : (7 : ℤ) ≤ r.length := by exact_mod_cast r.length_ge_seven
  have hseal := player_landing_seals hL (r.before_south_guarded hr hsf hfx hfy)
    r.compile.initial_valid r.separator_initial_holes
    (show s.player.1.val = r.width by rw [hs]; rfl)
    (show coordinate (r.outputHeight - 1 : ℕ) s.player = 2 by
      rw [hs]; exact r.landing_seal_coordinate)
  by_contra hdoor
  have hh : coordinate (r.outputHeight - 1 : ℕ) r.door ∈
      columnHoles r.width (r.outputHeight - 1 : ℕ) s :=
    (coordinate_mem_columnHoles rfl).mpr ((mem_holes _).mpr hdoor)
  rw [r.door_seal_coordinate] at hh
  exact hseal hh

end PushPuzzle.Push.ColumnScan.Input
