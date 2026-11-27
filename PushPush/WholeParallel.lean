/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeScan
public import Push.ScanLaneProjection

/-! Same-direction whole-run blocks retain their summed per-lane whole-run cut. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction Adjacent)

variable {w h : ℕ}

theorem Exec.subset {program : List (Push.Scan.Instruction w h)} {E F : Finset (Cell w h)}
    (H : Exec program E F) : F ⊆ E := Push.Scan.eval_subset H.eval

private theorem Exec.lines_no_split (side : Direction) (requests : List (ℕ × ℕ))
    {E F : Finset (Cell w h)} (H : Exec (Push.Scan.lines side requests) E F) :
    ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent side.opposite p q := by
  induction requests generalizing E with
  | nil => cases H; simp
  | cons request requests ih =>
    rcases request with ⟨lane, quota⟩
    cases H with
    | @cons _ _ _ _ _ M _ head tail =>
      intro p hp q hq ha
      by_cases hpm : p ∈ M
      · exact ih tail p (Finset.mem_sdiff.mpr ⟨hpm, (Finset.mem_sdiff.mp hp).2⟩) q hq ha
      · exact head.no_split p (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp).1, hpm⟩)
          q (tail.subset hq) ha

/-- Repeated requests on one lane form one exact whole-run read with their summed quota. -/
theorem Exec.parallel_read (side : Direction) (requests : List (ℕ × ℕ))
    {E F : Finset (Cell w h)} (H : Exec (Push.Scan.lines side requests) E F) (lane : ℕ) :
    Read side lane (Push.Scan.quotaAt requests lane)
      (E.filter fun q => side.lane q = lane) (F.filter fun q => side.lane q = lane) where
  eval := Push.Scan.lines_lane_projection side requests lane H.eval
  no_split := by
    intro p hp q hq ha
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp, hpl⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq, _⟩ := Finset.mem_filter.mp hq
    have hpnot' : p ∉ F := fun hf => hpnot (Finset.mem_filter.mpr ⟨hf, hpl⟩)
    exact H.lines_no_split side requests p (Finset.mem_sdiff.mpr ⟨hp, hpnot'⟩) q hq ha

end PushPuzzle.PushPush.WholeScan
