/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessFrame
public import Push.AcceptanceProgramMargins
public import PushS.PortCentralStrip
import all PushS.PortCentralStrip
import all Push.AcceptanceProgram
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgramLayout

/-! The actual first side clear leaves only original marker stock in the remote central band. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- The exact hole set after the reader's whole frame and first side-band clear. -/
def sideClearHoles (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (E \ Boundary.frame).filter fun q =>
    Direction.north.lane q ∉ sideBands p (targetHoles l p target \ Boundary.frame).card

/-- The literal first three rounds of the actual schedule. -/
def sideClearSchedule (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  frameSchedule p.W p.H ++ [.clear .north (sideBands p (targetHoles l p target \ Boundary.frame).card)]

/-- Full acceptance gives the exact dynamic remainder after those first three rounds. -/
theorem program_sideClear_eval (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {E : Finset (Cell (p.W + 1) (p.H + 1))}
    (ha : Scan.Accepts (instructions (program l p target).rounds) E) :
    Scan.eval (instructions (emit (sideClearSchedule l p target) (targetHoles l p target)).rounds) E =
      some (sideClearHoles l p target E) := by
  have hprefix : ∃ rest, schedule l p (targetHoles l p target \ Boundary.frame).card =
      sideClearSchedule l p target ++ rest := by
    unfold schedule preparation sideClearSchedule
    simp only [List.append_assoc, List.singleton_append]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hrest⟩ := hprefix
  unfold program at ha
  rw [hrest] at ha
  obtain ⟨F, hF⟩ := accepts_emitted_prefix _ _ _ _ ha
  rw [sideClearSchedule, emit_rounds_append, instructions, List.flatMap_append, eval_append] at hF ⊢
  simp only [emit, Round.instructions, List.flatMap_cons, List.flatMap_nil,
    List.singleton_append, Scan.eval, Scan.Instruction.eval, Option.bind_some] at hF ⊢
  obtain ⟨G, hG, _⟩ := Option.bind_eq_some_iff.mp hF
  have hD : 0 < p.D := by have := p.outer_distance; omega
  have hW : 1 ≤ p.W := Nat.mul_pos (by omega) hD
  have hH : 1 ≤ p.H := by change 1 ≤ 2 * p.D; omega
  have hrem := (frame_eval_remainder hW hH (l.encodedSegments_frame_subset p (l.canonical target)) hG).1
  rw [hG, Option.bind_some, hrem]
  rfl

private theorem initial_interior_card_eq (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool) :
    (targetHoles l p initial \ Boundary.frame).card = (targetHoles l p target \ Boundary.frame).card := by
  have h := l.encodedSegments_holes_card_eq p hl hM haxes (l.canonical initial) (l.canonical target)
  have hi := Finset.card_sdiff_add_card_eq_card (l.encodedSegments_frame_subset p (l.canonical initial))
  have ht := Finset.card_sdiff_add_card_eq_card (l.encodedSegments_frame_subset p (l.canonical target))
  change (targetHoles l p initial).card = (targetHoles l p target).card at h
  change (targetHoles l p initial \ Boundary.frame).card + Boundary.frame.card = (targetHoles l p initial).card at hi
  change (targetHoles l p target \ Boundary.frame).card + Boundary.frame.card = (targetHoles l p target).card at ht
  omega

/-- Every remote endpoint hole was already a hole in the genuine initial position. -/
private theorem far_hole_source {w h : ℕ} {B : Board w h} {cap : Option ℕ} {s t : State w h}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (ht : Disjoint t.boxes Boundary.frame)
    {q : Cell w h} (hq : Distant.Far s q) (hh : q ∈ PushS.holes t) : q ∈ PushS.holes s := by
  apply (PushS.mem_holes _).mpr
  intro hb
  exact (PushS.mem_holes _).mp hh (Distant.box_at hr .refl hp ht hq hb)

/-- Central holes surviving the actual first side clear are the source's literal fixed markers. -/
theorem sideClearHoles_central_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame)
    (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ sideClearHoles l p target (PushS.holes t))
    (hy : p.D ≤ q.2.val + 4) (hy' : q.2.val ≤ p.D + 4) : q ∈ l.centralMarkers p := by
  obtain ⟨hq, hside⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq, hframe⟩ := Finset.mem_sdiff.mp hq
  have hx0 : q.1.val ≠ 0 := by
    intro he
    exact hframe ((Boundary.mem_frame q).mpr ⟨.west, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)
  have hxW : q.1.val ≠ p.W := by
    intro he
    exact hframe ((Boundary.mem_frame q).mpr ⟨.east, by simp [Boundary.edge, he]⟩)
  have hside' : ¬((1 ≤ q.1.val ∧ q.1.val ≤ (targetHoles l p target \ Boundary.frame).card) ∨
      (p.W - (targetHoles l p target \ Boundary.frame).card ≤ q.1.val ∧ q.1.val < p.W)) := by
    intro hb
    exact hside (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr q.1.isLt, hb⟩)
  have hcount : (PushS.holes s \ Boundary.frame).card = (targetHoles l p target \ Boundary.frame).card := by
    rw [hs, initial_interior_card_eq l p hl hM haxes initial target]
  have hk := l.encodedSegments_interior_card_le p hl haxes (l.canonical target)
  change (targetHoles l p target \ Boundary.frame).card ≤ 2 * p.b p.levels at hk
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  have hxf := q.1.isLt
  have hfar : Distant.Far s q := by
    apply (Distant.far_iff_margins s q).mpr
    rw [hcount]
    omega
  have hsource := far_hole_source hr hp (program_frame_empty l p target ha) hfar hq
  rw [hs] at hsource
  by_contra hc
  have hband := l.encodedSegments_central_strip p (l.canonical initial) hsource hframe hc
  have hY := PortLayout.last_depth_margin p
  omega

end PushPuzzle.Push.AcceptanceSoundness
