/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateTools
public import PushS.FiniteSquareLine
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.DeriveFintype

/-! The four straight sweeps between the actual AND A-branch tools. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateAStraight

set_option maxRecDepth 8192

open PushFS FiniteGeometry FiniteGateCore FiniteGateState FiniteGateTools
open FiniteLineMacros FiniteSquareLine

/-- Ordered full-branch checkpoints, with A itself still in its closed slot. -/
def stage (w : ℕ) (b c : Bool) (j : Fin 8) : AndPhases w where
  west i := decide (if i.val = 0 then 2 ≤ j.val else 1 ≤ j.val)
  upper i := decide (if i.val = 0 then 2 ≤ j.val else if i.val = w+4 then 4 ≤ j.val else 3 ≤ j.val)
  middle := if 4 ≤ j.val then 3 else 0
  lower i := decide (if i.val = 0 then 4 ≤ j.val else if i.val = w+4 then 6 ≤ j.val else 5 ≤ j.val)
  guard i := decide (if i.val = 0 then 6 ≤ j.val else 7 ≤ j.val)
  triggerA := 1
  branchB _ := b
  branchC _ := c

inductive Segment
  | west | upper | lower | guard
  deriving DecidableEq

namespace Segment

def count (w : ℕ) : Segment → ℕ
  | .guard => 3*w+4
  | _ => w+3

def before : Segment → Fin 8
  | .west => 0
  | .upper => 2
  | .lower => 4
  | .guard => 6

def after : Segment → Fin 8
  | .west => 1
  | .upper => 3
  | .lower => 5
  | .guard => 7

def endpoint (k : Segment) (q : Bool) : Fin 8 := if q then k.after else k.before

def base (w : ℕ) : Segment → ℕ
  | .west => origin w-8*w-17
  | .upper => t w+3
  | .lower => origin w-2*w-8
  | .guard => s w+3

def row (w : ℕ) : Segment → ℕ
  | .west => t w
  | .upper | .lower => s w
  | .guard => origin w

def lane (w : ℕ) : Segment → ℕ
  | .west => t w+1
  | .upper => s w-1
  | .lower => s w+1
  | .guard => origin w-1

def entry : Segment → Direction
  | .west | .lower => .north
  | .upper | .guard => .south

def hubCoordinate (w : ℕ) : Segment → ℕ
  | .west => s w-2
  | .upper => t w+2
  | .lower => origin w-2
  | .guard => origin w+1

/-- Horizontal or transposed-vertical geometry of the whole selected straight chain. -/
def sweep (w : ℕ) (k : Segment) : Sweep (side w) where
  line := {
    count := k.count w
    base := k.base w
    base_pos := by cases k <;> dsimp [base, s, t, origin] <;> omega
    fits := by cases k <;> dsimp [base, count, s, t, origin, FiniteGeometry.side] <;> omega
    row := ⟨k.row w, by cases k <;> dsimp [row, s, t, origin, FiniteGeometry.side] <;> omega⟩
    lane := ⟨k.lane w, by cases k <;> dsimp [lane, s, t, origin, FiniteGeometry.side] <;> omega⟩
    entry := k.entry
    crossing := by
      intro x
      cases k <;> dsimp [row, lane, entry, Adjacent, s, t, origin] <;> omega
    hub := ⟨k.hubCoordinate w, by cases k <;> dsimp [hubCoordinate, s, t, origin, FiniteGeometry.side] <;> omega⟩ }
  vertical := match k with | .upper | .lower => true | _ => false

/-- Every tool boundary box is excluded from its neighboring straight sweep. -/
def keep {w : ℕ} : Segment → AndLabel w → Bool
  | .west, .west i => decide (i.val = 0)
  | .upper, .upper i => decide (i.val = 0 ∨ i.val = w+4)
  | .lower, .lower i => decide (i.val = 0 ∨ i.val = w+4)
  | .guard, .guard i => decide (i.val = 0)
  | _, _ => true

private def label (w : ℕ) : (k : Segment) → Fin (k.count w) → AndLabel w
  | .west, i => .west ⟨w+3-i.val, by have := i.isLt; dsimp [count] at *; omega⟩
  | .upper, i => .upper ⟨i.val+1, by have := i.isLt; dsimp [count] at *; omega⟩
  | .lower, i => .lower ⟨i.val+1, by have := i.isLt; dsimp [count] at *; omega⟩
  | .guard, i => .guard ⟨i.val+1, by have := i.isLt; dsimp [count] at *; omega⟩

def fixed (w : ℕ) (b c : Bool) (k : Segment) : Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => k.keep l).image (andMixedCell w (stage w b c k.before))

/-- The two-row or two-column strip used by a straight sweep. -/
def Region (w : ℕ) : Segment → Cell (side w) (side w) → Prop
  | .west, p => origin w-8*w-18 ≤ p.1.val ∧ p.1.val ≤ s w-2 ∧
      (p.2.val = t w ∨ p.2.val = t w+1)
  | .upper, p => (p.1.val = s w ∨ p.1.val+1 = s w) ∧
      t w+2 ≤ p.2.val ∧ p.2.val ≤ origin w-4*w-12
  | .lower, p => (p.1.val = s w ∨ p.1.val = s w+1) ∧
      origin w-2*w-9 ≤ p.2.val ∧ p.2.val ≤ origin w-2
  | .guard, p => s w+2 ≤ p.1.val ∧ p.1.val ≤ origin w+2 ∧
      (p.2.val = origin w ∨ p.2.val+1 = origin w)

attribute [local irreducible] FiniteGeometry.side

private theorem kept_cell (w : ℕ) (b c q : Bool) (k : Segment) (l : AndLabel w)
    (hl : k.keep l = true) :
    andMixedCell w (stage w b c (k.endpoint q)) l =
      andMixedCell w (stage w b c k.before) l := by
  cases q with
  | false => rfl
  | true =>
    cases k <;> cases l <;>
      simp [keep, stage, endpoint, before, after, andMixedCell, andCell, andPoint] at hl ⊢
    · simp [hl]
    · rename_i i
      rcases hl with rfl | hl
      · simp
      · have hi : i ≠ 0 := by
          intro he
          have he' := congrArg Fin.val he
          simp only [Fin.val_zero] at he'
          omega
        simp [hi, hl]
    · rename_i i
      rcases hl with rfl | hl
      · simp
      · have hi : i ≠ 0 := by
          intro he
          have he' := congrArg Fin.val he
          simp only [Fin.val_zero] at he'
          omega
        simp [hi, hl]
    · simp [hl]

private theorem selected_cell (w : ℕ) (b c q : Bool) (k : Segment) (i : Fin (k.count w)) :
    andMixedCell w (stage w b c (k.endpoint q)) (k.label w i) =
      andCell w q false false (k.label w i) := by
  have hi := i.isLt
  cases k <;> cases q <;>
    simp [label, count, stage, endpoint, before, after, andMixedCell] at hi ⊢
  all_goals (congr 1; simp; omega)

private theorem position_slot (w : ℕ) (b c q : Bool) (k : Segment) (i : Fin (k.count w)) :
    (k.sweep w).position (if q then k.count w else 0) i =
      andMixedCell w (stage w b c (k.endpoint q)) (k.label w i) := by
  rw [selected_cell]
  have hi := i.isLt
  cases k <;> cases q
  all_goals dsimp only [count] at hi
  all_goals apply Prod.ext <;> apply Fin.ext <;>
    simp [sweep, Sweep.position, Sweep.map, Line.position, base, row, lane,
      count, label, andCell, andPoint, s, t, origin, hi]
  all_goals omega

private theorem region_floor (w : ℕ) (hw : 2 ≤ w) (k : Segment) (p : Cell (side w) (side w))
    (hp : k.Region w p) : p ∉ andWalls w := by
  intro hm
  obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp hm
  have hm' := ((andRectangle w i).mem_cells _ _ _).mp hm
  cases k <;> fin_cases i <;>
    simp [Region, andRectangle, s, t, origin] at hp hm' <;> omega

private theorem fixed_free (w : ℕ) (hw : 2 ≤ w) (b c : Bool) (k : Segment)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hp : k.Region w p) : Free (andBoard w goals) (k.fixed w b c) p := by
  refine ⟨k.region_floor w hw p hp, ?_⟩
  intro hm
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hm
  have hkeep := (Finset.mem_filter.mp hl).2
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  cases l with
  | west i =>
    have hbit := Bool.toNat_le ((stage w b c k.before).west i)
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell, andCell, andPoint] at hpx hpy
    all_goals try (dsimp [s, t, origin] at hp hpx hpy; omega)
    have hi : i.val = 0 := by simpa only [keep, decide_eq_true_eq] using hkeep
    have hi0 : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using hi)
    subst i
    simp [stage, before] at hpx hpy
    dsimp [s, t, origin] at hp hpx hpy
    omega
  | upper i =>
    have hbit := Bool.toNat_le ((stage w b c k.before).upper i)
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell, andCell, andPoint] at hpx hpy
    all_goals try (dsimp [s, t, origin] at hp hpx hpy; omega)
    have hi : i.val = 0 ∨ i.val = w+4 := by simpa only [keep, decide_eq_true_eq] using hkeep
    rcases hi with hi | hi
    · have hi0 : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using hi)
      subst i
      simp [stage, before] at hpx hpy
      dsimp [s, t, origin] at hp hpx hpy
      omega
    · have hi0 : i ≠ 0 := by
        intro he
        have he' := congrArg Fin.val he
        simp only [Fin.val_zero] at he'
        omega
      simp [stage, before, hi, hi0] at hpx hpy
      dsimp [s, t, origin] at hp hpx hpy
      omega
  | middle =>
    have hmid := (stage w b c k.before).middle.isLt
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell] at hpx hpy
    all_goals dsimp [s, t, origin] at hp hpx hpy; omega
  | lower i =>
    have hbit := Bool.toNat_le ((stage w b c k.before).lower i)
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell, andCell, andPoint] at hpx hpy
    all_goals try (dsimp [s, t, origin] at hp hpx hpy; omega)
    have hi : i.val = 0 ∨ i.val = w+4 := by simpa only [keep, decide_eq_true_eq] using hkeep
    rcases hi with hi | hi
    · have hi0 : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using hi)
      subst i
      simp [stage, before] at hpx hpy
      dsimp [s, t, origin] at hp hpx hpy
      omega
    · have hi0 : i ≠ 0 := by
        intro he
        have he' := congrArg Fin.val he
        simp only [Fin.val_zero] at he'
        omega
      simp [stage, before, hi, hi0] at hpx hpy
      dsimp [s, t, origin] at hp hpx hpy
      omega
  | guard i =>
    have hbit := Bool.toNat_le ((stage w b c k.before).guard i)
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell, andCell, andPoint] at hpx hpy
    all_goals try (dsimp [s, t, origin] at hp hpx hpy; omega)
    have hi : i.val = 0 := by simpa only [keep, decide_eq_true_eq] using hkeep
    have hi0 : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using hi)
    subst i
    simp [stage, before] at hpx hpy
    dsimp [s, t, origin] at hp hpx hpy
    omega
  | triggerA =>
    cases k <;> dsimp [Region, andMixedCell, stage] at hp hpx hpy
    all_goals dsimp [s, t, origin] at hp hpx hpy; omega
  | branchB i =>
    have hbit := Bool.toNat_le ((stage w b c k.before).branchB i)
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell, andCell, andPoint] at hpx hpy
    all_goals dsimp [s, t, origin] at hp hpx hpy; omega
  | branchC i =>
    have hbit := Bool.toNat_le ((stage w b c k.before).branchC i)
    cases k <;> dsimp only [Region] at hp
    all_goals dsimp only [andMixedCell, andCell, andPoint] at hpx hpy
    all_goals dsimp [s, t, origin] at hp hpx hpy; omega

/-- The selected straight chain and its fixed neighbors satisfy the full physical sweep frame. -/
theorem frame (w : ℕ) (hw : 2 ≤ w) (b c : Bool) (k : Segment)
    (goals : Finset (Cell (side w) (side w))) :
    (k.sweep w).Frame (andBoard w goals) (k.fixed w b c) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact andMixedCell_floor w hw (stage w b c k.before) l hm
  · intro x hx
    apply k.fixed_free w hw b c goals
    cases k <;> dsimp [sweep, Sweep.map, Line.track, base, count, row, Region] at hx ⊢
    all_goals dsimp [s, t, origin] at *; omega
  · intro x hx
    apply k.fixed_free w hw b c goals
    cases k <;> dsimp [sweep, Sweep.map, Line.laneSegment, base, count, lane, hubCoordinate, Region] at hx ⊢
    all_goals dsimp [s, t, origin] at *; omega

private theorem label_cover (w : ℕ) (k : Segment) (l : AndLabel w)
    (hk : k.keep l = false) : ∃ i, k.label w i = l := by
  cases k <;> cases l <;> try exact False.elim (Bool.noConfusion hk)
  · rename_i i
    have hi : i.val ≠ 0 := by simpa only [keep, decide_eq_false_iff_not] using hk
    have hib := i.isLt
    refine ⟨⟨w+3-i.val, by dsimp [count]; omega⟩, ?_⟩
    apply congrArg AndLabel.west
    apply Fin.ext
    dsimp [label]
    omega
  · rename_i i
    have hi : ¬(i.val = 0 ∨ i.val = w+4) := by simpa only [keep, decide_eq_false_iff_not] using hk
    have hib := i.isLt
    refine ⟨⟨i.val-1, by dsimp [count]; omega⟩, ?_⟩
    apply congrArg AndLabel.upper
    apply Fin.ext
    dsimp [label]
    omega
  · rename_i i
    have hi : ¬(i.val = 0 ∨ i.val = w+4) := by simpa only [keep, decide_eq_false_iff_not] using hk
    have hib := i.isLt
    refine ⟨⟨i.val-1, by dsimp [count]; omega⟩, ?_⟩
    apply congrArg AndLabel.lower
    apply Fin.ext
    dsimp [label]
    omega
  · rename_i i
    have hi : i.val ≠ 0 := by simpa only [keep, decide_eq_false_iff_not] using hk
    have hib := i.isLt
    refine ⟨⟨i.val-1, by dsimp [count]; omega⟩, ?_⟩
    apply congrArg AndLabel.guard
    apply Fin.ext
    dsimp [label]
    omega

/-- The sweep endpoints enumerate the complete actual mixed gate inventory. -/
theorem boxes_endpoint (w : ℕ) (b c q : Bool) (k : Segment) :
    (k.sweep w).boxes (k.fixed w b c) (if q then k.count w else 0) =
      andMixedBoxes w (stage w b c (k.endpoint q)) := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      have hkeep := (Finset.mem_filter.mp hl).2
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, kept_cell w b c q k l hkeep⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨k.label w i, Finset.mem_univ _,
        (position_slot w b c q k i).symm⟩
  · intro hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    by_cases hk : k.keep l = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩,
        (kept_cell w b c q k l hk).symm⟩
    · obtain ⟨i, hi⟩ := label_cover w k l (Bool.eq_false_iff.mpr hk)
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by
        rw [position_slot, hi]⟩

/-- Update every selected ordinary box, preserving all prepared tool neighbors. -/
theorem forward (w : ℕ) (hw : 2 ≤ w) (b c : Bool) (k : Segment)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.before)⟩
      ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.after)⟩ := by
  have hr := (k.frame w hw b c goals).forward
  have hzero := boxes_endpoint w b c false k
  change (k.sweep w).boxes (k.fixed w b c) 0 = andMixedBoxes w (stage w b c k.before) at hzero
  have hfull := boxes_endpoint w b c true k
  change (k.sweep w).boxes (k.fixed w b c) (k.count w) = andMixedBoxes w (stage w b c k.after) at hfull
  change Reachable (andBoard w goals) (some 1)
    ⟨(k.sweep w).hub, (k.sweep w).boxes (k.fixed w b c) 0⟩
    ⟨(k.sweep w).hub, (k.sweep w).boxes (k.fixed w b c) (k.count w)⟩ at hr
  rw [hzero, hfull] at hr
  exact hr

/-- Reverse every selected ordinary box in the opposite frontier order. -/
theorem backward (w : ℕ) (hw : 2 ≤ w) (b c : Bool) (k : Segment)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.after)⟩
      ⟨(k.sweep w).hub, andMixedBoxes w (stage w b c k.before)⟩ := by
  have hr := (k.frame w hw b c goals).backward
  have hzero := boxes_endpoint w b c false k
  change (k.sweep w).boxes (k.fixed w b c) 0 = andMixedBoxes w (stage w b c k.before) at hzero
  have hfull := boxes_endpoint w b c true k
  change (k.sweep w).boxes (k.fixed w b c) (k.count w) = andMixedBoxes w (stage w b c k.after) at hfull
  change Reachable (andBoard w goals) (some 1)
    ⟨(k.sweep w).hub, (k.sweep w).boxes (k.fixed w b c) (k.count w)⟩
    ⟨(k.sweep w).hub, (k.sweep w).boxes (k.fixed w b c) 0⟩ at hr
  rw [hfull, hzero] at hr
  exact hr

end Segment
end PushPuzzle.PushS.FiniteGateAStraight
