/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutHalfCard
public import Push.ScanMedian
public import PushS.Boundary
public import Mathlib.Data.List.Perm.Basic

/-! Double-ended ordinary-axis reads retain the physical upper or lower probe hole of its decoded bit. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- The literal upper/lower depth-plus-two probe selected by the genuine axis threshold. -/
def ordinaryProbe (p : Scales.Parameters) (upper lower : Endpoint) (parameter : ℕ)
    (hp : upper.port < p.axes) : Cell (p.W + 1) (p.H + 1) :=
  (⟨p.x upper.port, by have := x_add_readLength_lt_W p hp 0; omega⟩,
    ⟨if parameter ≤ 1 then readDepth p upper.level + 2 else p.H - (readDepth p lower.level + 2), by
      have := readDepth_add_lt_H p upper.level
      split <;> omega⟩)

/-- The five actual non-frame axis holes are ordered around the decoded physical probe. -/
private theorem ordinary_axis_five_holes {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement}
    (joint : OrdinaryAxisReadout p upper lower u a) (hp : upper.port < p.axes)
    (hYu : 4 ≤ readDepth p upper.level) (hYl : 4 ≤ readDepth p lower.level)
    (hsu : a.upperShift = 0) (hsl : a.lowerShift = 0)
    (hcut : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = p.x upper.port → q.2.val = p.D → q ∉ holes u) :
    ∃ first second fourth fifth,
      (Scan.lineCells (w := p.W + 1) (h := p.H + 1) .north (p.x upper.port)).filter
        (fun q => decide (q ∈ holes u \ Boundary.frame)) =
        [first, second, ordinaryProbe p upper lower a.parameter hp, fourth, fifth] := by
  let E : Finset (Cell (p.W + 1) (p.H + 1)) := holes u \ Boundary.frame
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  have hx0 := readLength_add_lt_x p upper.port 0
  have hxW := x_add_readLength_lt_W p hp 0
  have hb := joint.parameter_le
  let up : Fin 4 → Cell (p.W + 1) (p.H + 1) := fun i =>
    (⟨p.x upper.port, by omega⟩, ⟨readDepth p upper.level + i.val, by have := i.isLt; omega⟩)
  let low : Fin 4 → Cell (p.W + 1) (p.H + 1) := fun i =>
    (⟨p.x upper.port, by omega⟩, ⟨p.H - (readDepth p lower.level + i.val), by omega⟩)
  have hup (q : Cell (p.W + 1) (p.H + 1)) (i : Fin 4) :
      q = up i ↔ q.1.val = p.x upper.port ∧ q.2.val = readDepth p upper.level + i.val := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨hx, hy⟩; exact Prod.ext (Fin.ext hx) (Fin.ext hy)
  have hlow (q : Cell (p.W + 1) (p.H + 1)) (i : Fin 4) :
      q = low i ↔ q.1.val = p.x upper.port ∧ q.2.val = p.H - (readDepth p lower.level + i.val) := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨hx, hy⟩; exact Prod.ext (Fin.ext hx) (Fin.ext hy)
  have hmem (q : Cell (p.W + 1) (p.H + 1)) :
      q ∈ (Scan.lineCells .north (p.x upper.port)).filter (fun q => decide (q ∈ E)) ↔
      q.1.val = p.x upper.port ∧
        ((readDepth p upper.level ≤ q.2.val ∧ q.2.val ≤ readDepth p upper.level + 3 - a.parameter) ∨
          (readDepth p lower.level ≤ p.H - q.2.val ∧ p.H - q.2.val ≤ readDepth p lower.level + a.parameter)) := by
    simp only [List.mem_filter, Scan.mem_lineCells, Direction.lane, decide_eq_true_eq, E, Finset.mem_sdiff]
    constructor
    · rintro ⟨hx, hq, hframe⟩
      have hy : 0 < q.2.val ∧ q.2.val < p.H := by
        simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hframe
        have := q.2.isLt
        omega
      refine ⟨hx, ?_⟩
      by_cases hn : q.2.val < p.D
      · left
        have hw := (joint.upper_holes q hx ⟨hy.1, hn⟩).mp hq
        rw [hsu] at hw
        omega
      · by_cases hc : q.2.val = p.D
        · exact False.elim (hcut q hx hc hq)
        · right
          have hw := (joint.lower_holes q hx (by omega)).mp hq
          rw [hsl] at hw
          omega
    · rintro ⟨hx, hinterval⟩
      have hy : 0 < q.2.val ∧ q.2.val < p.H := by rcases hinterval with h | h <;> omega
      refine ⟨hx, ?_, ?_⟩
      · rcases hinterval with hu | hl
        · apply (joint.upper_holes q hx (by omega)).mpr
          rw [hsu]
          right
          omega
        · apply (joint.lower_holes q hx (by omega)).mpr
          rw [hsl]
          right
          omega
      · simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
  have hcases : a.parameter = 0 ∨ a.parameter = 1 ∨ a.parameter = 2 ∨ a.parameter = 3 := by omega
  rcases hcases with hcase | hcase | hcase | hcase
  all_goals
    let slots : List (Cell (p.W + 1) (p.H + 1)) :=
      if a.parameter = 0 then [up 0, up 1, up 2, up 3, low 0]
      else if a.parameter = 1 then [up 0, up 1, up 2, low 1, low 0]
      else if a.parameter = 2 then [up 0, up 1, low 2, low 1, low 0]
      else [up 0, low 3, low 2, low 1, low 0]
    have hslots : ∀ q, q ∈ slots ↔ q ∈ (Scan.lineCells .north (p.x upper.port)).filter (fun q => decide (q ∈ E)) := by
      intro q
      rw [hmem]
      simp [slots, hcase, hup, hlow]
      have hy := q.2.isLt
      omega
    have horder : slots.Pairwise (fun q r => q.2.val < r.2.val) := by
      simp [slots, hcase, List.pairwise_cons, up, low]
      omega
    have hn : slots.Nodup := horder.nodup
    have hperm := (List.perm_ext_iff_of_nodup ((Scan.lineCells_nodup .north _).filter _) hn).mpr (fun q => (hslots q).symm)
    have heq : (Scan.lineCells .north (p.x upper.port)).filter (fun q => decide (q ∈ E)) = slots := by
      apply List.Perm.eq_of_pairwise (le := fun q r => q.2.val < r.2.val) _ _ horder hperm
      · intro q r _ _ hqr hrq; omega
      · exact ((Scan.lineCells_pairwise .north _).filter _).imp (by intro q r h; change -(r.2.val : ℤ) < -(q.2.val : ℤ) at h; omega)
    rw [heq]
    simp [slots, hcase, ordinaryProbe]
    rfl

/-- Two real static reads from each end retain precisely the decoded upper/lower probe on this axis. -/
theorem ordinary_two_reads_probe {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement}
    (joint : OrdinaryAxisReadout p upper lower u a) (hp : upper.port < p.axes)
    (hYu : 4 ≤ readDepth p upper.level) (hYl : 4 ≤ readDepth p lower.level)
    (hsu : a.upperShift = 0) (hsl : a.lowerShift = 0)
    (hcut : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = p.x upper.port → q.2.val = p.D → q ∉ holes u) :
    Scan.eval [.read .north (p.x upper.port) 2, .read .south (p.x upper.port) 2]
      (holes u \ Boundary.frame) = some (insert (ordinaryProbe p upper lower a.parameter hp)
        ((holes u \ Boundary.frame).filter fun q => q.1.val ≠ p.x upper.port)) := by
  obtain ⟨first, second, fourth, fifth, hholes⟩ := ordinary_axis_five_holes joint hp hYu hYl hsu hsl hcut
  have hmedian := Scan.five_hole_middle _ (holes u \ Boundary.frame)
    (Scan.lineCells_nodup .north (p.x upper.port)) first second
      (ordinaryProbe p upper lower a.parameter hp) fourth fifth hholes
  have hreverse : (Scan.lineCells (w := p.W + 1) (h := p.H + 1) .north (p.x upper.port)).reverse =
      Scan.lineCells .south (p.x upper.port) := by
    have hx : p.x upper.port < p.W + 1 := by have := x_add_readLength_lt_W p hp 0; omega
    simp only [Scan.lineCells, dite_eq_left hx]
  rw [hreverse] at hmedian
  have hid (F : Finset (Cell (p.W + 1) (p.H + 1))) :
      (Scan.consume (Scan.lineCells .south (p.x upper.port)) 2 F).bind
        (fun G => some G) = Scan.consume (Scan.lineCells .south (p.x upper.port)) 2 F := by
    cases Scan.consume (Scan.lineCells .south (p.x upper.port)) 2 F <;> rfl
  simpa only [Scan.eval, Scan.Instruction.eval, hid, Scan.mem_lineCells, Direction.lane] using hmedian

end PushPuzzle.Push.AcceptanceAxisReadout
