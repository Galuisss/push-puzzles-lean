/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlockBudget

/-! Exact sparse whole-run words supply complete parallel round certificates. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell)
open Push.AcceptanceProgram

variable {w h : ℕ}

theorem Exec.of_exact {rounds : List Round} {E F : Finset (Cell w h)}
    (hb : Push.Scan.Bounded (instructions (w := w) (h := h) rounds))
    (H : WholeScan.Exec (instructions (w := w) (h := h) rounds) E F) : Exec rounds E F := by
  induction rounds generalizing E with
  | nil => cases H; exact .nil _
  | cons block rounds ih =>
    cases block with
    | clear side lanes => cases H
    | read side requests =>
      obtain ⟨G, hhead, htail⟩ := (WholeScan.Exec.append_iff _ _ _ _).mp H
      have hreq : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h := by
        intro a ha
        exact hb (.read side a.1 a.2) (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
      have hloos := hhead.loosen_lines (List.forall₂_same.mpr (by intro a _; exact ⟨rfl, le_rfl⟩))
      exact .cons (hloos.normalize hreq)
        (ih (by intro i hi; exact hb i (List.mem_append_right _ hi)) htail)

end PushPuzzle.PushPush.WholeBlocks
