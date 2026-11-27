/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Closure
public import PushS.InventoryHoles
public import PushS.RowInventory

/-! A closed rail's actual occupancy projects to the existing line-label dynamics. -/

public section
namespace PushPuzzle.PushS.BoxMask

open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {R : Finset (Cell w h)}
  {s t : State w h}

/-- Retain just the boxes occupying the specified region, with the same actual player. -/
@[expose] def keep (s : State w h) (R : Finset (Cell w h)) : State w h :=
  ⟨s.player, s.boxes ∩ R⟩

/-- A region's exact hole set determines its retained occupied cells. -/
theorem keep_boxes_of_holes {H : Finset (Cell w h)} (hholes : holes s ∩ R = H) :
    (keep s R).boxes = R \ H := by
  rw [← hholes]
  ext q
  simp only [keep, Finset.mem_inter, Finset.mem_sdiff, mem_holes]
  tauto

/-- A full straight run between two region cells stays inside the region after its player cell. -/
@[expose] def RunClosed (R : Finset (Cell w h)) : Prop :=
  ∀ {B : Board w h} {d : Direction} {s : State w h} {n : ℕ} (run : Run B d s n), 0 < n →
    run.cell 1 ∈ R → run.cell ⟨n + 1, by omega⟩ ∈ R →
    ∀ i : Fin (n + 2), 0 < i.val → run.cell i ∈ R

private theorem keep_valid (hv : s.Valid B) : (keep s R).Valid B :=
  ⟨hv.1, hv.2.1.mono_left Finset.inter_subset_left,
    fun h => hv.2.2 (Finset.mem_inter.mp h).1⟩

private def keptRun {d : Direction} {n : ℕ} (run : Run B d s n)
    (hin : ∀ i : Fin n, run.cell ⟨i.val + 1, by omega⟩ ∈ R) : Run B d (keep s R) n where
  cell := run.cell
  start := run.start
  adjacent := run.adjacent
  occupied i := Finset.mem_inter.mpr ⟨run.occupied i, hin i⟩
  empty h := run.empty (Finset.mem_inter.mp h).1
  floor := run.floor

/-- A balanced real step projects to a real step on the retained occupancy.
Transverse pushes whose first box and destination are outside project to a walk. -/
theorem keep_step (hclosed : RunClosed R) (hm : Step B cap s t)
    (hcount : Inventory.count R s = Inventory.count R t) : Step B cap (keep s R) (keep t R) := by
  obtain ⟨d, hmove⟩ := hm
  refine ⟨d, ?_⟩
  cases hmove with
  | walk hv ha hf he hb =>
    exact .walk (keep_valid hv) ha hf (fun h => he (Finset.mem_inter.mp h).1)
      (congrArg (· ∩ R) hb)
  | @push n hv hn hc run hp hb =>
    have hiff := Inventory.transfer_iff_of_count run hn hb hcount
    by_cases hfirst : run.cell 1 ∈ R
    · have hlast := hiff.mp hfirst
      let r := keptRun run (fun i => hclosed run hn hfirst hlast ⟨i.val + 1, by omega⟩ (by exact Nat.succ_pos _))
      refine .push (keep_valid hv) hn hc r hp ?_
      change t.boxes ∩ R = insert (run.cell ⟨n + 1, by omega⟩) ((s.boxes ∩ R).erase (run.cell 1))
      rw [hb, Finset.insert_inter_of_mem hlast, Finset.erase_inter]
    · have hlast : run.cell ⟨n + 1, by omega⟩ ∉ R := fun h => hfirst (hiff.mpr h)
      refine .walk (keep_valid hv) ?_ ?_ ?_ ?_
      · change Adjacent d s.player t.player
        rw [hp, ← run.start]
        exact run.adjacent 0
      · change t.player ∉ B.walls
        rw [hp]
        exact run.floor 1
      · change t.player ∉ s.boxes ∩ R
        rw [hp]
        exact fun h => hfirst (Finset.mem_inter.mp h).2
      · change t.boxes ∩ R = s.boxes ∩ R
        rw [hb, Finset.insert_inter_of_notMem hlast, Finset.erase_inter,
          Finset.erase_eq_of_notMem (fun h => hfirst (Finset.mem_inter.mp h).2)]

/-- If the region lies on one line, the projected line inventory is precisely its actual boxes. -/
theorem lineBoxes_keep {axis : Direction} {lane : ℕ}
    (hon : ∀ q ∈ R, axis.lane q = lane) (s : State w h) :
    RowLabels.lineBoxes axis lane (keep s R) = s.boxes ∩ R := by
  ext q
  simp only [RowLabels.lineBoxes, keep, Finset.mem_filter, Finset.mem_inter]
  exact ⟨fun ⟨hq, _⟩ => hq, fun hq => ⟨hq, hon q hq.2⟩⟩

/-- Coordinates on a single retained line determine its actual occupied cells. -/
theorem box_mem_iff_image {axis : Direction} {lane : ℕ}
    (hon : ∀ q ∈ R, axis.lane q = lane) (s : State w h) {q : Cell w h} (hq : q ∈ R) :
    q ∈ s.boxes ↔ axis.position q ∈ (s.boxes ∩ R).image axis.position := by
  constructor
  · intro hb
    exact Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hb, hq⟩, rfl⟩
  · intro hx
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hx
    have hrq : r = q := axis.cell_ext ((hon r (Finset.mem_inter.mp hr).2).trans (hon q hq).symm) he
    exact hrq ▸ (Finset.mem_inter.mp hr).1

/-- A balanced actual step induces the existing admissible line update on its retained occupancy. -/
theorem keep_admissible {axis : Direction} {lane : ℕ}
    (hclosed : RunClosed R) (hon : ∀ q ∈ R, axis.lane q = lane)
    (hm : Step B cap s t) (hcount : Inventory.count R s = Inventory.count R t) :
    RowLabels.LineAdmissible B cap axis lane (keep s R) (keep t R) := by
  apply RowLabels.step_admissible_of_card (keep_step hclosed hm hcount)
  rw [lineBoxes_keep hon t, lineBoxes_keep hon s]
  simpa only [Inventory.count_eq_card, Finset.filter_mem_eq_inter] using hcount.symm

/-- The entire balanced physical path projects to the same line-label dynamics. -/
theorem keep_admissible_reachable {axis : Direction} {lane : ℕ}
    (hclosed : RunClosed R) (hon : ∀ q ∈ R, axis.lane q = lane)
    (hr : Relation.ReflTransGen (fun a b => Step B cap a b ∧ Inventory.count R a = Inventory.count R b) s t) :
    Relation.ReflTransGen (RowLabels.LineAdmissible B cap axis lane) (keep s R) (keep t R) :=
  hr.lift (fun s => keep s R) (fun _ _ hm => keep_admissible hclosed hon hm.1 hm.2)

end PushPuzzle.PushS.BoxMask
