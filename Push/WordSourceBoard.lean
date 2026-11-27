/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSourcePolyTime
public import PushS.PortPhysicalCompleteness

/-! Fixed-level actual canonical source boards and their original NCL macro paths. -/

public section
namespace PushPuzzle.Push.WordSource

open PushFS PushS Cslib.Complexity Turing.MultiTapeTM

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- One physical axis per repaired port, with the fixed repaired working-level allocation. -/
@[expose] def scales (x : NCL.HWord.Instance q) : Scales.Parameters where
  axes := (layout H hq x).portCount + 1
  levels := levelBudget q + 1
  axes_pos := Nat.le_add_left 1 _
  levels_pos := Nat.le_add_left 1 _

/-- The actual repaired port layout fits its allocated physical axes. -/
theorem portCount_le_scales_axes (x : NCL.HWord.Instance q) :
    (layout H hq x).portCount ≤ (scales H hq x).axes := Nat.le_succ _

/-- The complete actual repaired layout fits the same fixed level allocation on every word. -/
theorem highest_le_scales_levels (x : NCL.HWord.Instance q) :
    (layout H hq x).pages.highest ≤ (scales H hq x).levels :=
  (layout_highest_le H hq x).trans (Nat.le_succ _)

/-- The complete actual marked source recipe with the repaired canonical endpoint words. -/
@[expose] def recipe (x : NCL.HWord.Instance q) : SegmentRecipe :=
  (layout H hq x).canonicalRecipe (scales H hq x) (initialAxes H hq x) (targetAxes H hq x)

/-- The actual canonical source board emitted from the reader-partner layout and repaired endpoint words. -/
@[expose] def puzzle (x : NCL.HWord.Instance q) : PushS.Instance :=
  (layout H hq x).canonicalInstance (scales H hq x) (layout_valid H hq x)
    (highest_le_scales_levels H hq x) (portCount_le_scales_axes H hq x)
    (initialAxes H hq x) (targetAxes H hq x)

/-- The actual unary physical-axis allocation emits in standard polynomial time. -/
theorem computableInPolyTime_scales_axes :
    ComputableInPolyTime (fun x => (scales H hq x).axes) (NCL.HWord.encInstance q) encUnary := by
  have hp := encPortLayout_portCount_polyTime (computableInPolyTime_layout H hq)
  change ComputableInPolyTime (fun x => (layout H hq x).portCount + 1) _ _
  fun_prop

/-- The full actual marked recipe emits in standard polynomial time at this fixed level allocation. -/
theorem computableInPolyTime_recipe :
    ComputableInPolyTime (recipe H hq) (NCL.HWord.encInstance q) encSegmentRecipe :=
  PortLayout.computableInPolyTime_canonicalRecipe (computableInPolyTime_layout H hq)
    (computableInPolyTime_scales_axes H hq) (fun _ => rfl)
    (computableInPolyTime_initialAxes H hq) (computableInPolyTime_targetAxes H hq)

/-- The actual dense canonical source board uses the standard polynomial-time instance encoding. -/
theorem computableInPolyTime_puzzle :
    ComputableInPolyTime (puzzle H hq) (NCL.HWord.encInstance q) PushS.encoding :=
  PortLayout.computableInPolyTime_canonicalInstance_of_layout
    (layout := layout H hq) (p := scales H hq) (M := levelBudget q + 1)
    (initial := initialAxes H hq) (target := targetAxes H hq)
    (computableInPolyTime_layout H hq) (computableInPolyTime_scales_axes H hq) (fun _ => rfl)
    (layout_valid H hq) (highest_le_scales_levels H hq) (portCount_le_scales_axes H hq)
    (computableInPolyTime_initialAxes H hq) (computableInPolyTime_targetAxes H hq)

/-- The canonical source instance contains exactly the dense bitmap of its actual emitted recipe. -/
theorem puzzle_data (x : NCL.HWord.Instance q) :
    PushFS.Encoding.data (puzzle H hq x).toInstance = (recipe H hq x).emit :=
  (layout H hq x).canonicalInstance_data_eq (scales H hq x) (layout_valid H hq x)
    (highest_le_scales_levels H hq x) (portCount_le_scales_axes H hq x) _ _

/-- The actual emitted initial source holes are the repaired canonical initial bitmap. -/
theorem puzzle_initial_holes (x : NCL.HWord.Instance q) :
    PushS.holes (puzzle H hq x).initial =
      SegmentRecipe.holes ((scales H hq x).W + 1) ((scales H hq x).H + 1)
        ((layout H hq x).encodedSegments (scales H hq x) ((layout H hq x).canonical (initialAxes H hq x))) :=
  (layout H hq x).physicalInstance_initial_holes (scales H hq x) (layout_valid H hq x)
    (highest_le_scales_levels H hq x) (portCount_le_scales_axes H hq x) _ _

/-- The actual source starts at the complete repaired canonical frame state. -/
private theorem puzzle_initial_eq_corner (x : NCL.HWord.Instance q) :
    (puzzle H hq x).initial =
      ((layout H hq x).cornerState (scales H hq x) ((layout H hq x).canonical (initialAxes H hq x))).toState :=
  (layout H hq x).physicalInstance_initial_eq_corner (scales H hq x) (layout_valid H hq x)
    (highest_le_scales_levels H hq x) (portCount_le_scales_axes H hq x) _ _

/-- Every accepted H-word runs the original actual NCL macros between its repaired canonical frame states. -/
theorem word_frame_reachable {x : NCL.HWord.Instance q} (hx : x ∈ NCL.HWord.language H)
    (B : Board ((scales H hq x).W + 1) ((scales H hq x).H + 1)) (hB : B.walls = ∅) :
    Reachable B none
      ((layout H hq x).cornerState (scales H hq x) ((layout H hq x).canonical (initialAxes H hq x))).toState
      ((layout H hq x).cornerState (scales H hq x) ((layout H hq x).canonical (targetAxes H hq x))).toState := by
  have hg := PushS.WordSource.guard_of_mem H hq hx
  exact (layout H hq x).encodedSegments_ordered_axis_path_from_frame (scales H hq x)
    (layout_valid H hq x) (highest_le_scales_levels H hq x) (portCount_le_scales_axes H hq x)
    ((axes_ordered_reachable_iff H hq hg).mpr hx) B hB

/-- The actual emitted source runs from its literal initial state to its complete canonical target at the frame corner. -/
theorem puzzle_forward {x : NCL.HWord.Instance q} (hx : x ∈ NCL.HWord.language H) :
    Reachable (puzzle H hq x).board none (puzzle H hq x).initial
      ((layout H hq x).cornerState (scales H hq x) ((layout H hq x).canonical (targetAxes H hq x))).toState := by
  rw [puzzle_initial_eq_corner]
  exact word_frame_reachable H hq hx _ (puzzle H hq x).walls_empty

end PushPuzzle.Push.WordSource
