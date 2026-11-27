/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Inventory
public import PushS.Holes

/-! Equal endpoint hole counts close a region's one-way box inventory. -/

public section
namespace PushPuzzle.PushS.Inventory


open PushFS

variable {w h k : ℕ} {B : Board w h} {cap : Option ℕ}
  {s u t : State w h} {R : Finset (Cell w h)}

/-- The region is partitioned by its boxes and holes. -/
theorem count_add_holes (R : Finset (Cell w h)) (s : State w h) :
    count R s + (holes s ∩ R).card = R.card := by
  rw [count_eq_card, Finset.filter_mem_eq_inter]
  have he : holes s ∩ R = R \ s.boxes := by
    ext q
    simp only [Finset.mem_inter, mem_holes, Finset.mem_sdiff]
    tauto
  rw [he, Finset.inter_comm s.boxes R]
  exact Finset.card_inter_add_card_sdiff R s.boxes

/-- A no-export region with matching endpoint hole counts has that count at every intermediate state. -/
theorem holes_of_balanced (hpre : Relation.ReflTransGen (ForwardStep B cap R) s u)
    (hpost : Relation.ReflTransGen (ForwardStep B cap R) u t)
    (hs : (holes s ∩ R).card = k) (ht : (holes t ∩ R).card = k) : (holes u ∩ R).card = k := by
  have hbefore := reachable_mono hpre
  have hafter := reachable_mono hpost
  have hI := count_add_holes R s
  have hu := count_add_holes R u
  have hT := count_add_holes R t
  omega

/-- The same conclusion holds for a region that cannot receive boxes. -/
theorem holes_of_balanced_compl (hpre : Relation.ReflTransGen (ForwardStep B cap Rᶜ) s u)
    (hpost : Relation.ReflTransGen (ForwardStep B cap Rᶜ) u t)
    (hs : (holes s ∩ R).card = k) (ht : (holes t ∩ R).card = k) : (holes u ∩ R).card = k := by
  have hbefore := reachable_mono hpre
  have hafter := reachable_mono hpost
  have hI := count_add_holes R s
  have hu := count_add_holes R u
  have hT := count_add_holes R t
  have hcI := count_add_compl R s
  have hcu := count_add_compl R u
  have hcT := count_add_compl R t
  have hbI := (reachable_forget hpre).card_boxes
  have hbT := (reachable_forget hpost).card_boxes
  omega

/-- A balanced push transfers either both its first box and destination into the region, or neither. -/
theorem transfer_iff_of_count {d : Direction} {n : ℕ} (run : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (he : count R s = count R t) : run.cell 1 ∈ R ↔ run.cell ⟨n + 1, by omega⟩ ∈ R := by
  have hc := push_accounting (R := R) run hn hb
  by_cases hfirst : run.cell 1 ∈ R <;> by_cases hlast : run.cell ⟨n + 1, by omega⟩ ∈ R <;>
    simp only [hfirst, hlast, ite_true, ite_false] at hc ⊢ <;> omega

end PushPuzzle.PushS.Inventory
