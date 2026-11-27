/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Space.SlideCheck
public import PushFS.Space.Edge

/-! Polynomial-time testing of maximum-slide edges, rejecting malformed state words. -/

@[expose] public section
namespace PushPuzzle.PushPush.Machine

open PushFS (Cell Direction Adjacent State Instance)
open PushFS.Machine
open Turing.MultiTapeTM ComputableInPolyTime

/-- The player occupies an empty square. -/
def playerClear (q : Instance × List Bool) : Bool :=
  (cells (q.1.width, q.1.height)).all fun p =>
    !playerAt (q.1, q.2, p) || !boxAt (q.1, q.2, p)

@[fun_prop] theorem playerClear_polyTime :
    ComputableInPolyTime playerClear (encPair PushFS.encoding encBits) encBool := by
  unfold playerClear
  fun_prop

theorem playerClear_correct (I : Instance) (s : State I.width I.height) :
    playerClear (I, s.bits) = true ↔ s.player ∉ s.boxes := by
  simp only [playerClear, List.all_eq_true, forall_cells_iff, playerAt_correct, boxAt_correct,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro h
    simpa only [not_true_eq_false, false_or] using h s.player
  · intro h p
    by_cases hp : p = s.player
    · exact Or.inr (hp ▸ h)
    · exact Or.inl hp

private theorem first_adjacent {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) :
    Adjacent d s.player (r.cell ⟨1, by omega⟩) := by
  have ha := r.adjacent ⟨0, by omega⟩
  change Adjacent d (r.cell 0) (r.cell ⟨1, by omega⟩) at ha
  rwa [r.start] at ha

/-- Enumerate bounded lengths and distances and inspect each affected box cell. -/
def labelledEdge (I : Instance) (d : Direction) (u v : List Bool) : Bool :=
  playerClear (I, u) &&
  (cells (I.width, I.height)).any fun p => playerAt (I, u, p) &&
    (cells (I.width, I.height)).any fun q => playerAt (I, v, q) &&
      adjacent (d, p, q) &&
      ((!boxAt (I, u, q) && (boxes (I, v) == boxes (I, u))) ||
        (List.range (I.area + 1)).any fun n =>
          (List.range (I.area + 1)).any fun k =>
            decide (0 < n) && decide (0 < k) && checkSlide I d u p n k &&
              checkUpdate I d u v p n k)

@[fun_prop] theorem labelledEdge_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × List Bool =>
        labelledEdge q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction) (encPair encBits encBits)))
      encBool := by
  unfold labelledEdge
  fun_prop

private theorem labelledEdge_correct (I : Instance) (d : Direction)
    (s t : State I.width I.height) :
    labelledEdge I d s.bits t.bits = true ↔ Move d s t := by
  simp only [labelledEdge, Bool.and_eq_true, playerClear_correct, List.any_eq_true,
    exists_cells_iff, playerAt_correct, decide_eq_true_eq, exists_eq_left,
    adjacent_correct, Bool.not_eq_true', decide_eq_false_iff_not,
    boxAt_correct, boxes_correct, Bool.or_eq_true, beq_iff_eq, List.mem_range]
  simp only [and_assoc, exists_eq_left]
  constructor
  · rintro ⟨hv, ha, hw | hp⟩
    · exact .walk hv ha hw.1 ((State.boxBits_eq_iff t s).mp hw.2)
    · obtain ⟨n, _, k, _, hn, hk, hr, hb⟩ := hp
      obtain ⟨r⟩ := (checkSlide_correct I d s n k).mp hr
      have hq : t.player = r.cell ⟨1, by omega⟩ :=
        ha.functional (first_adjacent r hn hk)
      exact .push hv hn hk r hq ((checkUpdate_correct I d s t r).mp hb)
  · intro hm
    cases hm with
    | walk hv ha he hb =>
      exact ⟨hv, ha, Or.inl ⟨he, (State.boxBits_eq_iff t s).mpr hb⟩⟩
    | @push n k hv hn hk r hp hb =>
      have hbound := slide_length_le r
      change n + k + 1 ≤ I.area at hbound
      refine ⟨hv, hp ▸ first_adjacent r hn hk, Or.inr ?_⟩
      exact ⟨n, by omega, k, by omega, hn, hk,
        (checkSlide_correct I d s n k).mpr ⟨r⟩,
        (checkUpdate_correct I d s t r).mpr hb⟩

/-- A maximum-slide edge between well-formed dense state words. -/
def edge (q : Instance × List Bool × List Bool) : Bool :=
  State.codeValid (q.1.area, q.2.1) && State.codeValid (q.1.area, q.2.2) &&
    directions.any fun d => labelledEdge q.1 d q.2.1 q.2.2

@[fun_prop] theorem edge_polyTime :
    ComputableInPolyTime edge (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
  unfold edge
  have hc := State.codeValid_computable
  have hd : ComputableInPolyTime
      (fun q : Instance × List Bool × List Bool =>
        directions.any fun d => labelledEdge q.1 d q.2.1 q.2.2)
      (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
    apply anyConst
    intro d _
    fun_prop
  fun_prop

theorem edge_correct (I : Instance) (u v : List Bool) :
    edge (I, u, v) = true ↔ ∃ s t : State I.width I.height,
      s.bits = u ∧ t.bits = v ∧ Step s t := by
  simp only [edge, Bool.and_eq_true, List.any_eq_true, mem_directions, true_and]
  constructor
  · rintro ⟨⟨hu, hv⟩, d, hd⟩
    obtain ⟨s, rfl⟩ := (State.codeValid_correct (w := I.width) (h := I.height) u).mp hu
    obtain ⟨t, rfl⟩ := (State.codeValid_correct (w := I.width) (h := I.height) v).mp hv
    exact ⟨s, t, rfl, rfl, d, (labelledEdge_correct I d s t).mp hd⟩
  · rintro ⟨s, t, rfl, rfl, d, hd⟩
    exact ⟨⟨(State.codeValid_correct _).mpr ⟨s, rfl⟩,
      (State.codeValid_correct _).mpr ⟨t, rfl⟩⟩,
      d, (labelledEdge_correct I d s t).mpr hd⟩

end PushPuzzle.PushPush.Machine
