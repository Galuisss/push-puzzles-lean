/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanResidualScan
public import Mathlib.Data.Finset.Max

/-! Bottom-first source deletion orders remainders by their column inventories. -/

public section
namespace PushPuzzle.Push.ReaderResidual

open PushFS

variable {w h : ℕ} {E F G : Finset (Cell w h)}

/-- Each column retains an initial northern portion of its original holes. -/
structure BottomRemainder (E F : Finset (Cell w h)) : Prop where
  subset : F ⊆ E
  northern : ∀ p ∈ F, ∀ q ∈ E, q.1 = p.1 → q.2.val ≤ p.2.val → q ∈ F

theorem BottomRemainder.refl (E : Finset (Cell w h)) : BottomRemainder E E :=
  ⟨Finset.Subset.refl _, fun _ _ _ h _ _ => h⟩

theorem BottomRemainder.trans (hEF : BottomRemainder E F) (hFG : BottomRemainder F G) :
    BottomRemainder E G :=
  ⟨hFG.subset.trans hEF.subset, fun p hp q hq hx hy =>
    hFG.northern p hp q (hEF.northern p (hFG.subset hp) q hq hx hy) hx hy⟩

/-- Deleting the next southern hole preserves the original northern-prefix relation. -/
theorem BottomRemainder.pop (hEF : BottomRemainder E F) (pop : BottomPop F G) :
    BottomRemainder E G := by
  refine ⟨?_, ?_⟩
  · rw [pop.result]
    exact (Finset.erase_subset _ _).trans hEF.subset
  · intro p hp q hq hx hy
    rw [pop.result] at hp ⊢
    obtain ⟨hpm, hp⟩ := Finset.mem_erase.mp hp
    have hqF := hEF.northern p hp q hq hx hy
    apply Finset.mem_erase.mpr ⟨?_, hqF⟩
    intro hqm
    have hpx : p.1 = pop.cell.1 := hx.symm.trans (congrArg Prod.fst hqm)
    have hmax := pop.maximal p hp hpx
    have he : p = pop.cell := by
      apply Prod.ext hpx
      apply Fin.ext
      have hqy := congrArg (fun q => q.2.val) hqm
      omega
    exact hpm he

/-- Static bottom reads retain the same northern-prefix relation as physical source pops. -/
theorem bottom_read_remainder (col quota : ℕ)
    (hread : (Scan.Instruction.read .south col quota).eval E = some F) : BottomRemainder E F := by
  induction quota generalizing E with
  | zero =>
    have he : E = F := by
      simpa only [Scan.Instruction.eval, Scan.consume, Option.some.injEq] using hread
    exact he ▸ BottomRemainder.refl E
  | succ k ih =>
    have hcount := (Scan.Instruction.read_accepts_iff .south col (k + 1) E).mp ⟨F, hread⟩
    have hne : (E.filter fun q => q.1.val = col).Nonempty := by
      apply Finset.card_pos.mp
      change k + 1 ≤ (E.filter fun q => q.1.val = col).card at hcount
      omega
    obtain ⟨p, hp, hmax⟩ := (E.filter fun q => q.1.val = col).exists_max_image (fun q => q.2.val) hne
    obtain ⟨hpE, hpx⟩ := Finset.mem_filter.mp hp
    let pop : BottomPop E (E.erase p) := ⟨p, hpE, fun q hq hx => hmax q
      (Finset.mem_filter.mpr ⟨hq, (congrArg Fin.val hx).trans hpx⟩), rfl⟩
    have hone : Scan.consume (Scan.lineCells .south col) 1 E = some (E.erase p) := by
      have hpop := pop.read
      change Scan.consume (Scan.lineCells .south p.1.val) 1 E = _ at hpop
      simpa only [hpx] using hpop
    have htail : (Scan.Instruction.read .south col k).eval (E.erase p) = some F := by
      change Scan.consume (Scan.lineCells .south col) (k + 1) E = some F at hread
      rw [Nat.add_comm k 1, Scan.consume_add, hone, Option.bind_some] at hread
      exact hread
    exact ((BottomRemainder.refl E).pop pop).trans (ih htail)

/-- Column counts determine inclusion among the actual bottom-first remainders. -/
theorem BottomRemainder.subset_of_column_card (hEF : BottomRemainder E F)
    (hEG : BottomRemainder E G)
    (hcard : ∀ x : Fin w, (F.filter fun q => q.1 = x).card ≤ (G.filter fun q => q.1 = x).card) :
    F ⊆ G := by
  intro p hp
  by_contra hpg
  have hsub : (G.filter fun q => q.1 = p.1) ⊆ (F.filter fun q => q.1 = p.1).erase p := by
    intro q hq
    obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
    have hqp : q ≠ p := fun he => hpg (he ▸ hq)
    have hy : q.2.val < p.2.val := by
      by_contra hy
      exact hpg (hEG.northern q hq p (hEF.subset hp) hx.symm (by omega))
    exact Finset.mem_erase.mpr ⟨hqp, Finset.mem_filter.mpr
      ⟨hEF.northern p hp q (hEG.subset hq) hx hy.le, hx⟩⟩
  have hc := Finset.card_le_card hsub
  have hp' : p ∈ F.filter (fun q => q.1 = p.1) := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hd := Finset.card_erase_add_one hp'
  have hbound := hcard p.1
  omega

end PushPuzzle.Push.ReaderResidual
