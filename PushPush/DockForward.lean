/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockLift
public import PushPush.Walking
public import Push.CornerDockBackupCanonical
import all Push.CornerDockForward
import all Push.CornerDockBackupCanonical

/-! One maximum slide opens the complete southern docking corridor. -/

@[expose] public section
namespace PushPuzzle.PushPush.CornerDock

open PushFS (Cell State Direction Adjacent)

variable (r : Push.CornerDock.Input)

private def corridorSlide (s : PushS.HoleState r.width r.height) :
    Slide .south (r.stage s 0 (by omega)).toState (r.distance - 1) r.distance where
  cell i := (r.entry.1, ⟨r.goalY.val + i.val, by
    have := i.isLt
    have := r.height_eq
    have := r.distance_pos
    change r.goalY.val + i.val < r.height + r.distance
    omega⟩)
  start := by apply Prod.ext <;> apply Fin.ext <;> rfl
  adjacent i := ⟨rfl, by change r.goalY.val + (i.val + 1) = r.goalY.val + i.val + 1; omega⟩
  occupied i := by
    apply Finset.mem_compl.mpr
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · have hx := r.source_x hh
      change 2 ≤ 1 at hx
      omega
    · have hp := (Finset.mem_filter.mp hh).2
      have := i.isLt
      have := r.height_eq
      change (1 = 0 ∧ _) ∨ (1 = 1 ∧ _) at hp
      dsimp only at hp
      omega
  clear i := by
    apply Finset.notMem_compl.mpr
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inr ⟨rfl, Or.inr ?_⟩⟩
    change r.height + 0 ≤ r.goalY.val + (r.distance - 1 + i.val + 1)
    have := r.height_eq
    have := r.distance_pos
    omega
  stopped q hq := by
    have hqbound := q.2.isLt
    have hy := hq.2
    change q.2.val = r.goalY.val + (r.distance - 1 + r.distance) + 1 at hy
    have := r.height_eq
    have := r.distance_pos
    change q.2.val < r.height + r.distance at hqbound
    omega

private theorem corridor_before (s : PushS.HoleState r.width r.height)
    (p : Cell r.outputWidth r.outputHeight) : p ∈ (corridorSlide r s).before ↔
      p.1.val = 1 ∧ r.goalY.val < p.2.val ∧ p.2.val < r.height := by
  simp only [Slide.before, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    have := i.isLt
    have := r.height_eq
    change 1 = 1 ∧ r.goalY.val < r.goalY.val + (i.val + 1) ∧
      r.goalY.val + (i.val + 1) < r.height
    omega
  · rintro ⟨hx, hlo, hhi⟩
    let i : Fin (r.distance - 1) := ⟨p.2.val - r.goalY.val - 1, by
      have := r.height_eq
      omega⟩
    refine ⟨i, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact hx.symm
    · change r.goalY.val + (p.2.val - r.goalY.val - 1 + 1) = p.2.val
      omega

private theorem corridor_after (s : PushS.HoleState r.width r.height)
    (p : Cell r.outputWidth r.outputHeight) : p ∈ (corridorSlide r s).after ↔
      p.1.val = 1 ∧ r.height < p.2.val := by
  simp only [Slide.after, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    have := r.height_eq
    change 1 = 1 ∧ r.height < r.goalY.val + (r.distance + i.val + 1)
    omega
  · rintro ⟨hx, hy⟩
    let i : Fin (r.distance - 1) := ⟨p.2.val - r.height - 1, by
      have := p.2.isLt
      change p.2.val < r.height + r.distance at this
      omega⟩
    refine ⟨i, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact hx.symm
    · change r.goalY.val + (r.distance + (p.2.val - r.height - 1) + 1) = p.2.val
      have := r.height_eq
      omega

private theorem corridor_boxes (s : PushS.HoleState r.width r.height) :
    (corridorSlide r s).boxes = (r.stage s r.distance le_rfl).toState.boxes := by
  ext p
  simp only [Slide.boxes, Finset.mem_union, Finset.mem_sdiff, corridor_before, corridor_after]
  by_cases hs : p ∈ s.empty.image r.embed
  · have hx := r.source_x hs
    change 2 ≤ p.1.val at hx
    simp only [PushS.HoleState.toState, Push.CornerDock.Input.stage, Finset.mem_compl,
      Finset.mem_union, hs, true_or, not_true_eq_false, false_and]
    change (False ∨ p.1.val = 1 ∧ r.height < p.2.val) ↔ False
    constructor
    · rintro (hh | ⟨hp, _⟩)
      · exact hh
      · rw [hp] at hx
        omega
    · exact False.elim
  · simp only [PushS.HoleState.toState, Push.CornerDock.Input.stage, Finset.mem_compl,
      Finset.mem_union, hs, false_or, Push.CornerDock.Input.stageAux, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have := r.height_eq
    have := p.2.isLt
    change p.2.val < r.height + r.distance at this
    omega

private theorem corridor_reachable (s : PushS.HoleState r.width r.height) :
    Reachable (r.stage s 0 (by omega)).toState (r.stage s r.distance le_rfl).toState := by
  have hd := r.distance_pos
  by_cases h : r.distance = 1
  · apply Relation.ReflTransGen.single
    refine ⟨.south, .walk (Finset.notMem_compl.mpr (r.stage s 0 (by omega)).player_empty) ?_ ?_ ?_⟩
    · constructor
      · rfl
      · change r.goalY.val + r.distance = r.goalY.val + 0 + 1
        omega
    · apply Finset.notMem_compl.mpr
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Or.inr ⟨rfl, Or.inr ?_⟩⟩
      change r.height + 0 ≤ r.goalY.val + r.distance
      have := r.height_eq
      omega
    · have hb := corridor_boxes r s
      have hbefore : (corridorSlide r s).before = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have := (corridor_before r s p).mp hp
        have := r.height_eq
        omega
      have hafter : (corridorSlide r s).after = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have := (corridor_after r s p).mp hp
        have := p.2.isLt
        change p.2.val < r.height + r.distance at this
        omega
      simpa only [Slide.boxes, hbefore, hafter, Finset.sdiff_empty, Finset.union_empty] using hb.symm
  · have hr := (corridorSlide r s).advance_reachable (by omega) hd
      (Finset.notMem_compl.mpr (r.stage s 0 (by omega)).player_empty) (Fin.last r.distance) hd
    have he : (corridorSlide r s).returnState (Fin.last r.distance) =
        (r.stage s r.distance le_rfl).toState := by
      apply State.ext
      · apply Prod.ext <;> apply Fin.ext <;> rfl
      · exact corridor_boxes r s
    exact he ▸ hr

/-- Canonical maximum docking retains the source holes and both return corridors. -/
theorem goal_to_ready (s : PushS.HoleState r.width r.height) (hp : s.player = r.sourceGoal) :
    ∃ t : PushS.HoleState r.outputWidth r.outputHeight,
      Reachable (r.extend s).toState t.toState ∧ t.player = r.target ∧
        Push.CornerDock.Backup.Ready r s.toState t := by
  have he : r.entry ∈ (r.extend s).empty := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
  have hentry : Move .west (r.extend s).toState ((r.extend s).walk r.entry he).toState :=
    .walk (Finset.notMem_compl.mpr (r.extend s).player_empty) (by
      change Adjacent .west (r.embed s.player) r.entry
      rw [hp]
      exact ⟨rfl, rfl⟩) (Finset.notMem_compl.mpr he) rfl
  have hstart : Reachable (r.extend s).toState (r.stage s 0 (by omega)).toState := by
    rw [← r.stage_zero s he]
    exact .single ⟨.west, hentry⟩
  let a := r.stage s r.distance le_rfl
  have hready := Push.CornerDock.Backup.stage_ready r s
  let west : Cell r.outputWidth r.outputHeight := (r.target.1, a.player.2)
  have hw : west ∈ a.empty := hready.western west rfl (by
    change r.height ≤ r.goalY.val + r.distance
    have := r.height_eq
    omega)
  have hm : Move .west a.toState (a.walk west hw).toState :=
    .walk (Finset.notMem_compl.mpr a.player_empty) ⟨rfl, rfl⟩ (Finset.notMem_compl.mpr hw) rfl
  have htarget : r.target ∈ a.empty := hready.western _ rfl (by
    change r.height ≤ r.height + r.distance - 1
    have := r.distance_pos
    omega)
  have hwalk : Reachable (a.walk west hw).toState ((a.walk west hw).walk r.target htarget).toState := by
    apply walk_vertical
    intro y hlo _
    apply Finset.notMem_compl.mpr
    apply hready.western _ rfl
    change r.height ≤ y.val
    change min (r.goalY.val + r.distance) (r.height + r.distance - 1) ≤ y.val at hlo
    have := r.height_eq
    omega
  exact ⟨_, ((hstart.trans (corridor_reachable r s)).tail ⟨.west, hm⟩).trans hwalk,
    rfl, ⟨hready.source, hready.western, hready.corridor⟩⟩

end PushPuzzle.PushPush.CornerDock
