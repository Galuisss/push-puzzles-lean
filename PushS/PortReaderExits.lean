/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortReaderBudget
public import PushS.PortStreetSupport
public import PushS.StreetExits
import all PushS.PortWalkBudget
import all PushS.Support
import all PushS.StreetExits
import all PushS.PortStreetSupport
import all PushS.PortStreetSeparation
import all PushS.EndpointMacros
import all PushS.PortSegments

/-! Exact departure columns of the actual reader public-walk region. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction Boundary

/-- Departures use an original street column or one of the two cells beside a main axis. -/
@[expose] def readerExitSet (l : PortLayout) (p : Scales.Parameters) :
    Set (Cell (p.W + 1) (p.H + 1)) :=
  {a | a.1 ∈ l.streetColumnSet p ∨ ∃ i < l.portCount, Nat.dist a.1.val (p.x i) ≤ 1}

private theorem column_of_coordinate (l : PortLayout) (p : Scales.Parameters)
    (a : Cell (p.W + 1) (p.H + 1)) {x : ℕ}
    (hx : x ∈ streetColumns l (coordinates p)) (ha : a.1.val = x) : a.1 ∈ l.streetColumnSet p := by
  change a.1.val ∈ streetColumns l (coordinates p)
  rwa [ha]

private theorem frame_column (l : PortLayout) (p : Scales.Parameters)
    (a : Cell (p.W + 1) (p.H + 1)) (hx : a.1.val = 0 ∨ a.1.val = p.W) :
    a.1 ∈ l.streetColumnSet p := by
  change a.1.val ∈ streetColumns l (coordinates p)
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]
  change a.1.val = 0 ∨ a.1.val = p.W ∨ _
  exact hx.elim Or.inl (fun h => Or.inr (Or.inl h))

private theorem selected_base_mem (l : PortLayout) (p : Scales.Parameters) (j : ℕ)
    {e : Endpoint} (he : e ∈ l.endpoints) {s : Segment} {k : ℕ}
    (hk : (s, k) ∈ ((endpointFixedSegments l (coordinates p) e).take 3).zipIdx)
    (hsel : if k = 1 then j < e.level else j ≤ e.level) : s ∈ l.readerWalkSegments p j :=
  List.mem_flatMap.mpr ⟨e, he, List.mem_filterMap.mpr ⟨(s, k), hk, by simp [hsel]⟩⟩

private theorem branch_departure (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (j : ℕ) {e : Endpoint} (he : e ∈ l.endpoints)
    (hlev : j ≤ e.level) {a b : Cell (p.W + 1) (p.H + 1)}
    (hx : b.1.val = a.1.val + 1 ∨ b.1.val + 1 = a.1.val) (hy : b.2 = a.2)
    (ha : (segment (inward (auxiliary (coordinates p) e).1 e.inward 1)
      (onSide (coordinates p) e.side ((coordinates p).depth e.level + 2))
      (outward ((coordinates p).x e.port) e.inward 1)
      (onSide (coordinates p) e.side ((coordinates p).depth e.level + 2))).Contains
        (a.1.val, a.2.val)) (hout : b ∉ l.readerWalkHoles p j) : Nat.dist a.1.val (p.x e.port) ≤ 1 := by
  let c := coordinates p
  let fseg := segment (auxiliary c e).1 (onSide c e.side 1)
    (auxiliary c e).1 (onSide c e.side (c.depth e.level + 2))
  let branch := segment (inward (auxiliary c e).1 e.inward 1) (onSide c e.side (c.depth e.level + 2))
    (outward (c.x e.port) e.inward 1) (onSide c e.side (c.depth e.level + 2))
  have hf : fseg ∈ l.readerWalkSegments p j :=
    selected_base_mem l p j (k := 0) he ((List.mem_zipIdx_iff_getElem?).mpr rfl) (by simpa using hlev)
  have hb : branch ∈ l.readerWalkSegments p j :=
    selected_base_mem l p j (k := 2) he ((List.mem_zipIdx_iff_getElem?).mpr rfl) (by simpa using hlev)
  have hgeom := (horizontal_contains _ _ _ _).mp ha
  have hby : b.2.val = onSide c e.side (c.depth e.level + 2) :=
    (congrArg Fin.val hy).trans hgeom.1
  have hnotF : b.1.val ≠ (auxiliary c e).1 := by
    intro h
    apply hout
    apply Finset.mem_union_right
    apply (SegmentRecipe.mem_holes _ b).mpr
    refine ⟨fseg, hf, ?_⟩
    apply (vertical_contains _ _ _ _).mpr
    exact ⟨h, hby ▸ min_le_right _ _, hby ▸ le_max_right _ _⟩
  have hnotBranch : ¬(min (inward (auxiliary c e).1 e.inward 1) (outward (c.x e.port) e.inward 1) ≤ b.1.val ∧
      b.1.val ≤ max (inward (auxiliary c e).1 e.inward 1) (outward (c.x e.port) e.inward 1)) := by
    intro h
    exact hout (Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ b).mpr
      ⟨branch, hb, (horizontal_contains _ _ _ _).mpr ⟨hby, h.1, h.2⟩⟩))
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hL : 16384 ≤ c.length e.level := readLength_ge p hj hm
  have hmargin : c.length e.level + 64 < c.x e.port := readLength_add_lt_x p e.port e.level
  change Nat.dist a.1.val (c.x e.port) ≤ 1
  dsimp only [c] at hL hmargin hnotF hnotBranch ⊢
  cases hd : e.inward <;>
    simp only [auxiliary, outward, inward, hd, Bool.false_eq_true, ite_false, ite_true,
      Nat.dist_eq_max_sub_min] at hgeom hnotF hnotBranch ⊢ <;> omega

private theorem horizontal_reader_exit (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (j : ℕ) {a b : Cell (p.W + 1) (p.H + 1)}
    (hx : b.1.val = a.1.val + 1 ∨ b.1.val + 1 = a.1.val) (hy : b.2 = a.2)
    (ha : a ∈ l.readerWalkHoles p j) (hb : b ∉ l.readerWalkHoles p j) : a ∈ l.readerExitSet p := by
  change a.1 ∈ l.streetColumnSet p ∨ ∃ i < l.portCount, Nat.dist a.1.val (p.x i) ≤ 1
  rcases Finset.mem_union.mp ha with hframe | hwalk
  · left
    have hbf : b ∉ Boundary.frame := fun h => hb (Finset.mem_union_left _ h)
    have hside := Support.horizontal_frame_side hframe hbf hy
    apply frame_column l p a
    rcases hside with hside | hside
    · left
      simpa only [edge, Finset.mem_filter, Finset.mem_univ, true_and] using hside
    · right
      have h := hside
      simp only [edge, Finset.mem_filter, Finset.mem_univ, true_and] at h
      omega
  · obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ a).mp hwalk
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨⟨seg, k⟩, hzip, hselected⟩ := List.mem_filterMap.mp hs
    dsimp only at hselected
    have heq : seg = s := by split_ifs at hselected <;> exact Option.some.inj hselected
    subst s
    have hlev : j ≤ e.level := by
      split_ifs at hselected <;> omega
    dsimp only [endpointFixedSegments] at hzip
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
      List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil, or_false] at hzip
    rcases hzip with hzip | hzip | hzip
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzip
      exact Or.inl (column_of_coordinate l p a (auxiliary_columns l p he).1 (vertical_contains _ _ _ _ |>.mp hcontains).1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzip
      exact Or.inl (column_of_coordinate l p a (auxiliary_columns l p he).2 (vertical_contains _ _ _ _ |>.mp hcontains).1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hzip
      exact Or.inr ⟨e.port, l.endpoints_port_lt hl he,
        branch_departure l p hl hM j he hlev hx hy hcontains hb⟩

/-- A supported actual step leaving the reader walks starts at one of the exact exit columns. -/
theorem step_readerWalk_exit (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {j : ℕ}
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hm : Step B cap s t)
    (hs : s.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p))
    (ht : t.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p))
    (hin : s.player ∈ l.readerWalkHoles p j) (hout : t.player ∉ l.readerWalkHoles p j) :
    s.player ∈ l.readerExitSet p := by
  obtain ⟨d, hm⟩ := hm
  have ha := players_adjacent hm
  cases d with
  | north =>
    have hc := Support.vertical_column (l.workingRowSet_separated p) ht hs ha.1.symm ha.2
    exact Or.inl (ha.1 ▸ hc)
  | south =>
    exact Or.inl (Support.vertical_column (l.workingRowSet_separated p) hs ht ha.1 ha.2.symm)
  | east => exact horizontal_reader_exit l p hl hM j (Or.inl ha.1) ha.2 hin hout
  | west => exact horizontal_reader_exit l p hl hM j (Or.inr ha.1) ha.2 hin hout

end PushPuzzle.PushS.PortLayout
