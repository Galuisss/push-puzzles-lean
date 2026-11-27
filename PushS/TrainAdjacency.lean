/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Labels

/-! Adjacent physical boxes cannot separate while confined to the same straight track. -/

@[expose] public section
namespace PushPuzzle.PushS.TrainAdjacency

open PushFS Labels

variable {w h n : ℕ} {B : Board w h} {cap : Option ℕ}
  {axis d : Direction} {s : State w h}

private def OnRun (r : Run B d s n) (p : Cell w h) : Prop :=
  ∃ i : Fin n, r.cell ⟨i.val + 1, by omega⟩ = p

private theorem onRun_adjacent (r : Run B d s n) (hv : s.Valid B)
    {p q : Cell w h} (hp : p ∈ s.boxes) (hq : q ∈ s.boxes) (ha : Adjacent d p q) :
    OnRun r p ↔ OnRun r q := by
  constructor
  · rintro ⟨i, hi⟩
    have haq : Adjacent d (r.cell ⟨i.val + 1, by omega⟩) q := hi.symm ▸ ha
    have hqcell : r.cell ⟨i.val + 2, by omega⟩ = q :=
      (r.adjacent ⟨i.val + 1, by omega⟩).functional haq
    by_cases hi' : i.val + 1 < n
    · exact ⟨⟨i.val + 1, hi'⟩, hqcell⟩
    · have he : (⟨i.val + 2, by omega⟩ : Fin (n + 2)) =
          ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ := by
        apply Fin.ext
        change i.val + 2 = n + 1
        omega
      have hm : r.cell ⟨i.val + 2, by omega⟩ ∈ s.boxes := hqcell.symm ▸ hq
      exact False.elim (r.empty (he ▸ hm))
  · rintro ⟨j, hj⟩
    have haq : Adjacent d p (r.cell ⟨j.val + 1, by omega⟩) := hj.symm ▸ ha
    have hpcell : r.cell ⟨j.val, by omega⟩ = p :=
      (r.adjacent ⟨j.val, by omega⟩).reverse.functional haq.reverse
    by_cases hj' : 0 < j.val
    · let i : Fin n := ⟨j.val - 1, by omega⟩
      refine ⟨i, ?_⟩
      have he : (⟨i.val + 1, by omega⟩ : Fin (n + 2)) = ⟨j.val, by omega⟩ := by
        apply Fin.ext
        change j.val - 1 + 1 = j.val
        omega
      exact (congrArg r.cell he).trans hpcell
    · have he : (⟨j.val, by omega⟩ : Fin (n + 2)) = 0 := by
        apply Fin.ext
        change j.val = 0
        omega
      have hplayer : s.player = p := by simpa only [he, r.start] using hpcell
      exact False.elim (hv.2.2 (hplayer.symm ▸ hp))

private theorem shift_off (r : Run B d s n) {p : Cell w h} (hp : ¬OnRun r p) :
    shiftMap r p = p := by
  rcases shiftMap_cases r p with he | ⟨i, hi, _⟩
  · exact he
  · exact False.elim (hp ⟨i, hi.symm⟩)

private theorem shift_on_adjacent (r : Run B d s n) {p : Cell w h} (hp : OnRun r p) :
    Adjacent d p (shiftMap r p) := by
  obtain ⟨i, rfl⟩ := hp
  rw [shiftMap_on]
  exact r.adjacent ⟨i.val + 1, by omega⟩

private theorem adjacent_translate {p q p' q' : Cell w h}
    (ha : Adjacent d p q) (hp : Adjacent d p p') (hq : Adjacent d q q') :
    Adjacent d p' q' := by
  apply (adjacent_iff_coordinates d _ _).mpr
  refine ⟨hq.lane.trans (ha.lane.trans hp.lane.symm), ?_⟩
  have h := ha.position
  have hi := hp.position
  have hj := hq.position
  omega

private theorem shift_adjacent_parallel (r : Run B d s n) (hv : s.Valid B)
    {p q : Cell w h} (hp : p ∈ s.boxes) (hq : q ∈ s.boxes) (ha : Adjacent d p q) :
    Adjacent d (shiftMap r p) (shiftMap r q) := by
  classical
  by_cases hi : OnRun r p
  · exact adjacent_translate ha (shift_on_adjacent r hi)
      (shift_on_adjacent r ((onRun_adjacent r hv hp hq ha).mp hi))
  · have hj : ¬OnRun r q := fun h => hi ((onRun_adjacent r hv hp hq ha).mpr h)
    simpa only [shift_off r hi, shift_off r hj] using ha

private theorem parallel_of_lane_eq {p q : Cell w h} (ha : Adjacent d p q)
    (hl : axis.lane q = axis.lane p) : d = axis ∨ d = axis.opposite := by
  cases axis <;> cases d <;> simp_all [Adjacent, Direction.lane, Direction.opposite]

private theorem shift_fixed_transverse (r : Run B d s n)
    (hd : ¬(d = axis ∨ d = axis.opposite)) {p : Cell w h}
    (hl : axis.lane (shiftMap r p) = axis.lane p) : shiftMap r p = p := by
  rcases shiftMap_cases r p with he | ⟨i, hi, hm⟩
  · exact he
  · have hp : OnRun r p := ⟨i, hi.symm⟩
    exact False.elim (hd (parallel_of_lane_eq (shift_on_adjacent r hp) hl))

/-- A simultaneous push preserves neighboring boxes whose transverse coordinates stay fixed. -/
theorem shift_adjacent (r : Run B d s n) (hv : s.Valid B)
    {p q : Cell w h} (hp : p ∈ s.boxes) (hq : q ∈ s.boxes)
    (ha : Adjacent axis p q)
    (hlp : axis.lane (shiftMap r p) = axis.lane p)
    (hlq : axis.lane (shiftMap r q) = axis.lane q) :
    Adjacent axis (shiftMap r p) (shiftMap r q) := by
  by_cases hd : d = axis ∨ d = axis.opposite
  · rcases hd with rfl | hd
    · exact shift_adjacent_parallel r hv hp hq ha
    · have hrev : Adjacent d q p := hd.symm ▸ ha.reverse
      have h := (shift_adjacent_parallel r hv hq hp hrev).reverse
      simpa only [hd, Direction.opposite_opposite] using h
  · simpa only [shift_fixed_transverse r hd hlp, shift_fixed_transverse r hd hlq] using ha

variable {ι : Type} [Fintype ι] {S T : LabelledState ι w h} {i j : ι}

end PushPuzzle.PushS.TrainAdjacency
