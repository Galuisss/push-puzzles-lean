/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.RunCheck
public import PushFS.Space.StateDecoding

/-! A polynomial-time edge test for finite and unlimited pushing. -/

@[expose] public section

namespace PushPuzzle.PushFS.Machine


open Turing.MultiTapeTM ComputableInPolyTime

/-- The box half of a raw state word. -/
def boxes (q : Instance × List Bool) : List Bool := q.2.take q.1.area

@[fun_prop] theorem boxes_polyTime :
    ComputableInPolyTime boxes (encPair encoding encBits) encBits := by
  unfold boxes
  fun_prop

@[simp] theorem boxes_correct (I : Instance) (s : State I.width I.height) :
    boxes (I, s.bits) = s.boxBits := by
  simp [boxes, State.bits, Instance.area]

/-- Check a fixed push limit against a computed unary run length. -/
def checkPermits (cap : Option ℕ) (n : ℕ) : Bool :=
  match cap with
  | none => true
  | some k => decide (n ≤ k)

@[fun_prop] theorem checkPermits_polyTime (cap : Option ℕ) :
    ComputableInPolyTime (checkPermits cap) encUnary encBool := by
  cases cap with
  | none => exact const true
  | some k => unfold checkPermits; fun_prop

theorem checkPermits_correct (cap : Option ℕ) (n : ℕ) :
    checkPermits cap n = true ↔ Permits cap n := by
  cases cap <;> simp [checkPermits, Permits]

/-- A direction-labelled step, including the entire run and exact bitmap update. -/
def labelledEdge (cap : Option ℕ) (I : Instance) (d : Direction) (u v : List Bool) : Bool :=
  valid (I, u) &&
  (cells (I.width, I.height)).any fun p => playerAt (I, u, p) &&
    (cells (I.width, I.height)).any fun q => playerAt (I, v, q) &&
      adjacent (d, p, q) && !wallAt (I, q) &&
      ((!boxAt (I, u, q) && (boxes (I, v) == boxes (I, u))) ||
        (List.range (I.area + 1)).any fun n =>
          decide (0 < n) && checkPermits cap n && checkRun I d u p n &&
            (boxes (I, v) == pushBits (boxes (I, u), index (I.width, q),
              index (I.width, advance d p (n + 1)))))

@[fun_prop] theorem labelledEdge_polyTime (cap : Option ℕ) :
    ComputableInPolyTime
      (fun p : Instance × Direction × List Bool × List Bool =>
        labelledEdge cap p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encoding (encPair (encFinite Direction) (encPair encBits encBits))) encBool := by
  unfold labelledEdge
  fun_prop

private theorem first_adjacent {w h n : ℕ} {B : Board w h} {d : Direction}
    {s : State w h} (r : Run B d s n) : Adjacent d s.player (r.cell 1) := by
  have ha := r.adjacent 0
  change Adjacent d (r.cell 0) (r.cell 1) at ha
  rwa [r.start] at ha

/-- The executable labelled checker agrees with the semantic move relation. -/
private theorem labelledEdge_correct (cap : Option ℕ) (I : Instance) (d : Direction)
    (s t : State I.width I.height) :
    labelledEdge cap I d s.bits t.bits = true ↔ Move I.board cap d s t := by
  simp only [labelledEdge, Bool.and_eq_true, valid_correct, List.any_eq_true,
    exists_cells_iff, playerAt_correct, decide_eq_true_eq, exists_eq_left,
    adjacent_correct, wallAt_correct, Bool.not_eq_true', decide_eq_false_iff_not,
    boxAt_correct, boxes_correct, Bool.or_eq_true, beq_iff_eq,
    List.mem_range, checkPermits_correct]
  simp only [and_assoc, exists_eq_left]
  constructor
  · rintro ⟨hv, ha, hf, hw | hp⟩
    · exact .walk hv ha hf hw.1 ((State.boxBits_eq_iff t s).mp hw.2)
    · obtain ⟨n, _, hn, hc, hr, hb⟩ := hp
      obtain ⟨run⟩ := (checkRun_correct I d s n).mp hr
      have hq : t.player = run.cell 1 := ha.functional (first_adjacent run)
      have he := advance_run run ⟨n + 1, by omega⟩
      rw [← he, index_eq, index_eq, hq, pushBits_boxBits] at hb
      exact .push hv hn hc run hq ((State.boxBits_eq_iff _ _).mp hb)
  · intro hm
    cases hm with
    | walk hv ha hf he hb =>
      exact ⟨hv, ha, hf, Or.inl ⟨he, (State.boxBits_eq_iff t s).mpr hb⟩⟩
    | @push n hv hn hc run hp hb =>
      have hbound : n < I.area + 1 := by
        have hcard := Finset.card_le_univ s.boxes
        have hrun := run.length_le_card
        simp only [Fintype.card_prod, Fintype.card_fin] at hcard
        change n < I.width * I.height + 1
        omega
      refine ⟨hv, hp ▸ first_adjacent run, hp ▸ run.floor 1, Or.inr ?_⟩
      refine ⟨n, hbound, hn, hc, (checkRun_correct I d s n).mpr ⟨run⟩, ?_⟩
      rw [← advance_run run ⟨n + 1, by omega⟩, hp, index_eq, index_eq, pushBits_boxBits]
      exact (State.boxBits_eq_iff _ _).mpr hb

/-- The fixed list of available directions. -/
def directions : List Direction := [.north, .east, .south, .west]

@[simp] theorem mem_directions (d : Direction) : d ∈ directions := by
  cases d <;> simp [directions]

/-- An edge checker rejecting every malformed endpoint code. -/
def edge (cap : Option ℕ) (q : Instance × List Bool × List Bool) : Bool :=
  State.codeValid (q.1.area, q.2.1) && State.codeValid (q.1.area, q.2.2) &&
    directions.any fun d => labelledEdge cap q.1 d q.2.1 q.2.2

@[fun_prop] theorem edge_polyTime (cap : Option ℕ) :
    ComputableInPolyTime (edge cap) (encPair encoding (encPair encBits encBits)) encBool := by
  unfold edge
  have hcode := State.codeValid_computable
  have hdirs : ComputableInPolyTime
      (fun q : Instance × List Bool × List Bool =>
        directions.any fun d => labelledEdge cap q.1 d q.2.1 q.2.2)
      (encPair encoding (encPair encBits encBits)) encBool := by
    apply anyConst
    intro d _
    fun_prop
  fun_prop

/-- Every accepted raw edge represents exactly one real legal puzzle step. -/
theorem edge_correct (cap : Option ℕ) (I : Instance) (u v : List Bool) :
    edge cap (I, u, v) = true ↔ ∃ s t : State I.width I.height,
      s.bits = u ∧ t.bits = v ∧ Step I.board cap s t := by
  simp only [edge, Bool.and_eq_true, List.any_eq_true, mem_directions, true_and]
  constructor
  · rintro ⟨⟨hu, hv⟩, d, hd⟩
    obtain ⟨s, rfl⟩ := (State.codeValid_correct (w := I.width) (h := I.height) u).mp hu
    obtain ⟨t, rfl⟩ := (State.codeValid_correct (w := I.width) (h := I.height) v).mp hv
    exact ⟨s, t, rfl, rfl, d, (labelledEdge_correct cap I d s t).mp hd⟩
  · rintro ⟨s, t, rfl, rfl, d, hd⟩
    exact ⟨⟨(State.codeValid_correct _).mpr ⟨s, rfl⟩,
      (State.codeValid_correct _).mpr ⟨t, rfl⟩⟩,
      d, (labelledEdge_correct cap I d s t).mpr hd⟩

end PushPuzzle.PushFS.Machine
