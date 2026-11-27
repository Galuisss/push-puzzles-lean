/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortRailProjection
public import Mathlib.Data.Finset.Max

/-! A column with boxes followed by holes retains this order under actual guarded pushes. -/

public section
namespace PushPuzzle.Push.AcceptanceColumnPrefix

open PushFS PushS

/-- The open finite vertical interval above a work row. -/
@[expose] def band {w h : ℕ} (column lower upper : ℕ) : Finset (Cell w h) :=
  Finset.univ.filter fun q => q.1.val = column ∧ lower < q.2.val ∧ q.2.val < upper

/-- Inside the column interval every cell above an occupied cell is occupied. -/
@[expose] def Closed {w h : ℕ} (column lower upper : ℕ) (s : State w h) : Prop :=
  ∀ q ∈ band column lower upper, ∀ r ∈ band column lower upper,
    q.2.val ≤ r.2.val → r ∈ s.boxes → q ∈ s.boxes

variable {w h column lower upper : ℕ} {B : Board w h} {cap : Option ℕ} {s t : State w h} {d : Direction}

private theorem south_first_outside (closed : Closed column lower upper s)
    (cutPlayer : ¬(s.player.1.val = column ∧ s.player.2.val = lower))
    {n : ℕ} (run : Run B .south s n) (positive : 0 < n)
    (valid : s.Valid B) : run.cell 1 ∉ band column lower upper := by
  intro hf
  obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hf
  have hp := run.position 1
  have hc := run.lane 1
  simp only [Direction.position, Direction.lane, Fin.val_one] at hp hc
  have hplayerX : s.player.1.val = column := hc.symm.trans hx
  have hplayerY : lower < s.player.2.val := by
    by_contra hn
    exact cutPlayer ⟨hplayerX, by omega⟩
  have playerBand : s.player ∈ band column lower upper :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplayerX, hplayerY, by omega⟩
  exact valid.2.2 (closed s.player playerBand _ hf (by omega) (run.first_occupied positive))

private theorem south_earlier_occupied {n : ℕ} (run : Run B .south s n) (q : Cell w h)
    (hx : q.1.val = s.player.1.val) (hlo : s.player.2.val < q.2.val)
    (hhi : q.2.val < (run.cell ⟨n + 1, by omega⟩).2.val) : q ∈ s.boxes := by
  have he := run.position ⟨n + 1, by omega⟩
  simp only [Direction.position] at he
  let i := q.2.val - s.player.2.val
  have hi : 0 < i ∧ i ≤ n := by dsimp only [i]; omega
  let idx : Fin (n + 2) := ⟨i, by omega⟩
  have hc := run.position idx
  have hl := run.lane idx
  simp only [Direction.position, Direction.lane] at hc hl
  have hidx : idx.val = i := rfl
  rw [hidx] at hc
  have hiEq : s.player.2.val + i = q.2.val := by dsimp only [i]; omega
  have hq : run.cell idx = q := Prod.ext (Fin.ext (hl.trans hx.symm)) (Fin.ext (by omega))
  exact hq ▸ run.occupied_at idx hi.1 hi.2

/-- Real pushes preserve the box-prefix order when transverse transfers and northward input from below are excluded. -/
theorem Closed.move (closed : Closed column lower upper s) (move : Move B cap d s t)
    (cutPlayer : ¬(s.player.1.val = column ∧ s.player.2.val = lower))
    (horizontal : ∀ {n} (run : Run B d s n), 0 < n → t.player = run.cell 1 →
      t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)) →
      (d = .east ∨ d = .west) → run.cell 1 ∉ band column lower upper ∧
        run.cell ⟨n + 1, by omega⟩ ∉ band column lower upper)
    (northInput : ∀ {n} (run : Run B .north s n), 0 < n → t.player = run.cell 1 →
      t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)) →
      run.cell ⟨n + 1, by omega⟩ ∈ band column lower upper → run.cell 1 ∈ band column lower upper) :
    Closed column lower upper t := by
  cases move with
  | walk _ _ _ _ boxes => simpa only [Closed, boxes] using closed
  | @push n valid positive _ run player boxes =>
    have northDest (hd : d = .north) : run.cell ⟨n + 1, by omega⟩ ∉ band column lower upper := by
      subst d
      intro hz
      have hf := northInput run positive player boxes hz
      have hp1 := run.position 1
      have hpN := run.position ⟨n + 1, by omega⟩
      simp only [Direction.position, Fin.val_one] at hp1 hpN
      exact run.empty (closed _ hz _ hf (by omega) (run.first_occupied positive))
    intro q hq r hr hqr hrbox
    rw [boxes] at hrbox ⊢
    obtain ⟨_, hqx, hqlo, hqhi⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hrx, hrlo, hrhi⟩ := Finset.mem_filter.mp hr
    rcases Finset.mem_insert.mp hrbox with he | hrbox
    · subst r
      by_cases hqz : q = run.cell ⟨n + 1, by omega⟩
      · exact Finset.mem_insert.mpr (Or.inl hqz)
      · cases d with
        | east => exact ((horizontal run positive player boxes (Or.inl rfl)).2 hr).elim
        | west => exact ((horizontal run positive player boxes (Or.inr rfl)).2 hr).elim
        | north => exact (northDest rfl hr).elim
        | south =>
          have hf := south_first_outside closed cutPlayer run positive valid
          have hp1 := run.position 1
          have hpN := run.position ⟨n + 1, by omega⟩
          have hl1 := run.lane 1
          have hlN := run.lane ⟨n + 1, by omega⟩
          simp only [Direction.position, Direction.lane, Fin.val_one] at hp1 hpN hl1 hlN
          have firstX : (run.cell 1).1.val = column := hl1.trans (hlN.symm.trans hrx)
          have firstLow : (run.cell 1).2.val ≤ lower := by
            by_contra hn
            exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, firstX, by omega, by omega⟩)
          have hqzY : q.2.val < (run.cell ⟨n + 1, by omega⟩).2.val := by
            by_contra hn
            apply hqz
            exact Prod.ext (Fin.ext (hqx.trans hrx.symm)) (Fin.ext (by omega))
          have hqb := south_earlier_occupied run q (hqx.trans (hrx.symm.trans hlN)) (by omega) hqzY
          exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hf (h ▸ hq), hqb⟩)
    · obtain ⟨hrfirst, hrold⟩ := Finset.mem_erase.mp hrbox
      have hqb := closed q hq r hr hqr hrold
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      refine ⟨?_, hqb⟩
      intro hfirst
      cases d with
      | east => exact (horizontal run positive player boxes (Or.inl rfl)).1 (hfirst ▸ hq)
      | west => exact (horizontal run positive player boxes (Or.inr rfl)).1 (hfirst ▸ hq)
      | south => exact south_first_outside closed cutPlayer run positive valid (hfirst ▸ hq)
      | north =>
        have hp1 := run.position 1
        have hl1 := run.lane 1
        simp only [Direction.position, Direction.lane, Fin.val_one] at hp1 hl1
        have hplayerX : s.player.1.val = column := hl1.symm.trans (hfirst ▸ hqx)
        have hplayerBelow : s.player.2.val ≤ r.2.val := by
          have hneY : q.2.val ≠ r.2.val := by
            intro hy
            have he : q = r := Prod.ext (Fin.ext (hqx.trans hrx.symm)) (Fin.ext hy)
            exact hrfirst (he.symm.trans hfirst)
          have hfirstY := congrArg (fun z : Cell w h => z.2.val) hfirst
          omega
        have hplayerBand : s.player ∈ band column lower upper :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplayerX, by
            have hfirstY := congrArg (fun z : Cell w h => z.2.val) hfirst
            omega, by omega⟩
        exact valid.2.2 (closed s.player hplayerBand r hr hplayerBelow hrold)

/-- A box-prefix column has exactly one contiguous terminal hole interval below its last box. -/
theorem Closed.holes_suffix (closed : Closed column lower upper s) :
    ∃ gap : ℕ, gap ≤ upper - lower - 1 ∧
      ∀ q ∈ band column lower upper, q ∈ holes s ↔ upper - gap ≤ q.2.val := by
  classical
  let E := holes s ∩ band column lower upper
  by_cases hE : E = ∅
  · refine ⟨0, by omega, ?_⟩
    intro q hq
    have hy := (Finset.mem_filter.mp hq).2.2.2
    constructor
    · intro hh
      exact (Finset.notMem_empty q (hE ▸ Finset.mem_inter.mpr ⟨hh, hq⟩)).elim
    · intro hh
      omega
  · have hEn : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let rows := E.image (fun q => q.2.val)
    have rowsN : rows.Nonempty := hEn.image _
    let first := rows.min' rowsN
    have hfirst : first ∈ rows := Finset.min'_mem _ _
    obtain ⟨r, hr, hrfirst⟩ := Finset.mem_image.mp hfirst
    obtain ⟨hrhole, hrband⟩ := Finset.mem_inter.mp hr
    obtain ⟨_, _, hrlo, hrhi⟩ := Finset.mem_filter.mp hrband
    have hfirstLo : lower < first := by omega
    have hfirstHi : first < upper := by omega
    refine ⟨upper - first, by omega, ?_⟩
    intro q hq
    have hbound : upper - (upper - first) = first := by omega
    rw [hbound]
    constructor
    · intro hh
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hh, hq⟩, rfl⟩)
    · intro hqrow
      apply (mem_holes q).mpr
      intro hb
      have rb := closed r hrband q hq (by omega) hb
      exact (mem_holes r).mp hrhole rb

end PushPuzzle.Push.AcceptanceColumnPrefix
