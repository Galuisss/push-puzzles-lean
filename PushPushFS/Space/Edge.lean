/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Space.SlideCheck
public import PushFS.Space.Edge

/-! Polynomial-time testing of maximum-slide edges, rejecting malformed state words. -/

@[expose] public section
namespace PushPuzzle.PushPushFS.Machine

open PushFS (Cell Direction Adjacent State Instance)
open PushFS.Machine
open Turing.MultiTapeTM ComputableInPolyTime

private theorem first_adjacent {w h n k : ℕ} {B : PushFS.Board w h} {d : Direction} {s : State w h}
    (r : Slide B d s n k) (hn : 0 < n) (hk : 0 < k) :
    Adjacent d s.player (r.cell ⟨1, by omega⟩) := by
  have ha := r.ray.adjacent ⟨0, by omega⟩
  change Adjacent d (r.cell 0) (r.cell ⟨1, by omega⟩) at ha
  simpa only [Slide.cell, r.ray.start, blocked] using ha

/-- Enumerate bounded lengths and distances and inspect each affected box cell. -/
def labelledEdge (limit : ℕ) (I : Instance) (d : Direction) (u v : List Bool) : Bool :=
  valid (I, u) &&
  (cells (I.width, I.height)).any fun p => playerAt (I, u, p) &&
    (cells (I.width, I.height)).any fun q => playerAt (I, v, q) &&
      adjacent (d, p, q) && !wallAt (I, q) &&
      ((!boxAt (I, u, q) && (boxes (I, v) == boxes (I, u))) ||
        (List.range (I.area + 1)).any fun n =>
          (List.range (I.area + 1)).any fun k =>
            decide (0 < n) && decide (n ≤ limit) && decide (0 < k) && checkSlide I d u p n k &&
              PushPush.Machine.checkUpdate I d u v p n k)

@[fun_prop] private theorem labelledEdge_polyTime (limit : ℕ) :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × List Bool =>
        labelledEdge limit q.1 q.2.1 q.2.2.1 q.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction) (encPair encBits encBits)))
      encBool := by
  unfold labelledEdge
  fun_prop

private theorem labelledEdge_correct (limit : ℕ) (I : Instance) (d : Direction)
    (s t : State I.width I.height) :
    labelledEdge limit I d s.bits t.bits = true ↔ Move I.board limit d s t := by
  simp only [labelledEdge, Bool.and_eq_true, Bool.or_eq_true,
    List.any_eq_true, exists_cells_iff, List.mem_range]
  simp only [valid_correct, playerAt_correct, adjacent_correct,
    boxAt_correct, wallAt_correct, boxes_correct]
  simp only [decide_eq_true_eq, exists_eq_left, Bool.not_eq_true',
    decide_eq_false_iff_not, beq_iff_eq, and_assoc]
  constructor
  · rintro ⟨hv, ha, hf, hw | hp⟩
    · exact .walk hv ha hf hw.1 ((State.boxBits_eq_iff t s).mp hw.2)
    · obtain ⟨n, _, k, _, hn, hlim, hk, hr, hb⟩ := hp
      obtain ⟨r⟩ := (checkSlide_correct I d s n k).mp hr
      have hq : t.player = r.cell ⟨1, by omega⟩ :=
        ha.functional (first_adjacent r hn hk)
      exact .push hv hn hlim hk r hq ((checkUpdate_correct I d s t r).mp hb)
  · intro hm
    cases hm with
    | walk hv ha hf he hb =>
      exact ⟨hv, ha, hf, Or.inl ⟨he, (State.boxBits_eq_iff t s).mpr hb⟩⟩
    | @push n k hv hn hlim hk r hp hb =>
      have hbound := PushPush.Machine.slide_length_le r.ray
      change n + k + 1 ≤ I.area at hbound
      refine ⟨hv, hp ▸ first_adjacent r hn hk, hp ▸ r.floor _, Or.inr ?_⟩
      exact ⟨n, by omega, k, by omega, hn, hlim, hk,
        (checkSlide_correct I d s n k).mpr ⟨r⟩,
        (checkUpdate_correct I d s t r).mpr hb⟩

/-- A maximum-slide edge between well-formed dense state words. -/
def edge (limit : ℕ) (q : Instance × List Bool × List Bool) : Bool :=
  State.codeValid (q.1.area, q.2.1) && State.codeValid (q.1.area, q.2.2) &&
    directions.any fun d => labelledEdge limit q.1 d q.2.1 q.2.2

@[fun_prop] theorem edge_polyTime (limit : ℕ) :
    ComputableInPolyTime (edge limit) (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
  unfold edge
  have hc := State.codeValid_computable
  have hlabel := labelledEdge_polyTime limit
  have hd : ComputableInPolyTime
      (fun q : Instance × List Bool × List Bool =>
        directions.any fun d => labelledEdge limit q.1 d q.2.1 q.2.2)
      (encPair PushFS.encoding (encPair encBits encBits)) encBool := by
    apply anyConst
    intro d _
    fun_prop
  fun_prop

theorem edge_correct (limit : ℕ) (I : Instance) (u v : List Bool) :
    edge limit (I, u, v) = true ↔ ∃ s t : State I.width I.height,
      s.bits = u ∧ t.bits = v ∧ Step I.board limit s t := by
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

end PushPuzzle.PushPushFS.Machine
