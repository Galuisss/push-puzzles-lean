/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Space.Edge
public import PushPush.Finite

/-! Polynomial-time testing of maximum-slide edges, rejecting malformed state words. -/

public section
namespace PushPuzzle.PushPush.Finite.Machine

open PushFS (Direction Adjacent State Instance)
open PushFS.Machine
open Turing.MultiTapeTM ComputableInPolyTime

open PushPush.Machine

variable (limit : ℕ)

private theorem first_adjacent {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k) :
    Adjacent d s.player (r.cell ⟨1, by omega⟩) := by
  have ha := r.adjacent ⟨0, by omega⟩
  change Adjacent d (r.cell 0) (r.cell ⟨1, by omega⟩) at ha
  rwa [r.start] at ha

/-- Enumerate bounded lengths and distances and inspect each affected box cell. -/
private def labelledEdge (I : Instance) (d : Direction) (u v : List Bool) : Bool :=
  playerClear (I, u) &&
  (cells (I.width, I.height)).any fun p => playerAt (I, u, p) &&
    (cells (I.width, I.height)).any fun q => playerAt (I, v, q) &&
      adjacent (d, p, q) &&
      ((!boxAt (I, u, q) && (boxes (I, v) == boxes (I, u))) ||
        (List.range (I.area + 1)).any fun n =>
          (List.range (I.area + 1)).any fun k =>
            decide (0 < n) && decide (n ≤ limit) && decide (0 < k) && checkSlide I d u p n k &&
              checkUpdate I d u v p n k)

@[fun_prop] private theorem labelledEdge_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × List Bool =>
        labelledEdge limit q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction) (encPair encBits encBits)))
      encBool := by
  unfold labelledEdge
  fun_prop

private theorem labelledEdge_correct (I : Instance) (d : Direction)
    (s t : State I.width I.height) :
    labelledEdge limit I d s.bits t.bits = true ↔ Finite.Move limit d s t := by
  simp only [labelledEdge, Bool.and_eq_true, playerClear_correct, List.any_eq_true,
    exists_cells_iff, playerAt_correct, decide_eq_true_eq, exists_eq_left,
    adjacent_correct, Bool.not_eq_true', decide_eq_false_iff_not,
    boxAt_correct, boxes_correct, Bool.or_eq_true, beq_iff_eq, List.mem_range]
  simp only [and_assoc, exists_eq_left]
  constructor
  · rintro ⟨hv, ha, hw | hp⟩
    · exact .walk hv ha hw.1 ((State.boxBits_eq_iff t s).mp hw.2)
    · obtain ⟨n, _, k, _, hn, hc, hk, hr, hb⟩ := hp
      obtain ⟨r⟩ := (checkSlide_correct I d s n k).mp hr
      have hq : t.player = r.cell ⟨1, by omega⟩ :=
        ha.functional (first_adjacent r hn hk)
      exact .push hv hn hc hk r hq ((checkUpdate_correct I d s t r).mp hb)
  · intro hm
    cases hm with
    | walk hv ha he hb =>
      exact ⟨hv, ha, Or.inl ⟨he, (State.boxBits_eq_iff t s).mpr hb⟩⟩
    | @push n k hv hn hc hk r hp hb =>
      have hbound := slide_length_le r
      change n + k + 1 ≤ I.area at hbound
      refine ⟨hv, hp ▸ first_adjacent r hn hk, Or.inr ?_⟩
      exact ⟨n, by omega, k, by omega, hn, hc, hk,
        (checkSlide_correct I d s n k).mpr ⟨r⟩,
        (checkUpdate_correct I d s t r).mpr hb⟩

/-- A maximum-slide edge between well-formed dense state words. -/
def edge (q : Instance × List Bool × List Bool) : Bool :=
  let (I, u, v) := q
  State.codeValid (I.area, u) && State.codeValid (I.area, v) &&
    directions.any fun d => labelledEdge limit I d u v

@[fun_prop] theorem edge_polyTime :
    ComputableInPolyTime (edge limit) (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
  unfold edge
  have hc := State.codeValid_computable
  have hd : ComputableInPolyTime
      (fun q : Instance × List Bool × List Bool =>
        directions.any fun d => labelledEdge limit q.1 d q.2.1 q.2.2)
      (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
    apply anyConst
    intro d _
    fun_prop
  fun_prop

theorem edge_correct (I : Instance) (u v : List Bool) :
    edge limit (I, u, v) = true ↔ ∃ s t : State I.width I.height,
      s.bits = u ∧ t.bits = v ∧ Finite.Step limit s t := by
  simp only [edge, Bool.and_eq_true, List.any_eq_true, mem_directions, true_and]
  constructor
  · rintro ⟨⟨hu, hv⟩, d, hd⟩
    obtain ⟨s, rfl⟩ := (State.codeValid_correct (w := I.width) (h := I.height) u).mp hu
    obtain ⟨t, rfl⟩ := (State.codeValid_correct (w := I.width) (h := I.height) v).mp hv
    exact ⟨s, t, rfl, rfl, d, (labelledEdge_correct limit I d s t).mp hd⟩
  · rintro ⟨s, t, rfl, rfl, d, hd⟩
    exact ⟨⟨(State.codeValid_correct _).mpr ⟨s, rfl⟩,
      (State.codeValid_correct _).mpr ⟨t, rfl⟩⟩,
      d, (labelledEdge_correct limit I d s t).mpr hd⟩

end PushPuzzle.PushPush.Finite.Machine
