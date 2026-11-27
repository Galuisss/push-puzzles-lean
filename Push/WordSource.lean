/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.WordTopology
public import PushS.WordRecipe
public import PushS.StripSourceReachability
public import Push.PartnerConfigurationNative
public import Push.PartnerResourcesDepth
import all PushS.StripSourceConfiguration

/-! Actual reader-partner layouts and direction words emitted from the native hard word family. -/

public section
namespace PushPuzzle.Push.WordSource

open PushS Cslib.Complexity

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

/-- The native strip compiler's fixed upper active-arc budget. -/
@[expose] def upperBudget (q : ℕ) : ℕ :=
  (2 * PushPuzzle.NCL.HWord.Strip.Sweep.drawingSpan q + 1) * (4 * PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q + 7)

/-- A fixed working-level bound for the complete actual reader-partner repair. -/
@[expose] def levelBudget (q : ℕ) : ℕ :=
  2 * max (upperBudget q) (PushS.WordSource.levelBudget q) + 2

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The actual original native drawing arrays. -/
abbrev native (x : NCL.HWord.Instance q) := PushS.WordSource.native H hq x

/-- The native endpoint legality and equal-word-length guard. -/
abbrev guard (x : NCL.HWord.Instance q) := PushS.WordSource.guard H hq x

/-- The actual unmodified contour layout emitted by the native drawing. -/
@[expose] def rawLayout (x : NCL.HWord.Instance q) : PortLayout :=
  StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)

/-- The original normalized contour direction word at the initial endpoint. -/
@[expose] def rawInitial (x : NCL.HWord.Instance q) : List Bool :=
  StripSource.normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)

/-- The original normalized contour direction word at the target endpoint. -/
@[expose] def rawTarget (x : NCL.HWord.Instance q) : List Bool :=
  StripSource.normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)

/-- The actual layout after all ears and common-cut buffers have been emitted. -/
@[expose] def layout (x : NCL.HWord.Instance q) : PortLayout :=
  (Partner.Cuts.repair (rawLayout H hq x)).layout

/-- The same actual repair applied to the initial contour word. -/
@[expose] def initialAxes (x : NCL.HWord.Instance q) : List Bool :=
  Partner.Cuts.repairAxes (rawLayout H hq x) (rawInitial H hq x)

/-- The same actual repair applied to the target contour word. -/
@[expose] def targetAxes (x : NCL.HWord.Instance q) : List Bool :=
  Partner.Cuts.repairAxes (rawLayout H hq x) (rawTarget H hq x)

/-- Every native source layout has its genuine two-page partition and noncrossing geometry. -/
private theorem raw_valid (x : NCL.HWord.Instance q) : (rawLayout H hq x).pages.Valid :=
  PushS.WordSource.layout_pages_valid H hq x

/-- The actual complete repaired layout retains the valid physical page geometry. -/
theorem layout_valid (x : NCL.HWord.Instance q) : (layout H hq x).pages.Valid :=
  Partner.Cuts.repair_valid (raw_valid H hq x)

/-- Every actual repaired middle axis has the partners required by the endpoint reader. -/
theorem layout_readerPartners (x : NCL.HWord.Instance q) : Partner.ReaderPartners (layout H hq x) :=
  Partner.Cuts.repair_readerPartners (raw_valid H hq x)

/-- Every original initial contour port has exactly one normalized direction bit. -/
private theorem rawInitial_length (x : NCL.HWord.Instance q) :
    (rawInitial H hq x).length = (rawLayout H hq x).portCount :=
  Comb.length_normalizedAxes _ _

/-- Every original target contour port has exactly one normalized direction bit. -/
private theorem rawTarget_length (x : NCL.HWord.Instance q) :
    (rawTarget H hq x).length = (rawLayout H hq x).portCount :=
  Comb.length_normalizedAxes _ _

/-- The actual repaired initial word has exactly one direction bit per repaired port. -/
theorem initialAxes_length (x : NCL.HWord.Instance q) :
    (initialAxes H hq x).length = (layout H hq x).portCount :=
  Partner.Cuts.repairAxes_length _ _ (rawInitial_length H hq x)

/-- The actual repaired target word has exactly one direction bit per repaired port. -/
theorem targetAxes_length (x : NCL.HWord.Instance q) :
    (targetAxes H hq x).length = (layout H hq x).portCount :=
  Partner.Cuts.repairAxes_length _ _ (rawTarget_length H hq x)

/-- Admitted initial endpoints retain the actual AND light-input order after repair. -/
theorem initial_ordered {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    (layout H hq x).OrderedInputs (initialAxes H hq x) :=
  Partner.Cuts.repairAxes_ordered (raw_valid H hq x) (PushS.WordSource.initial_ordered H hq hx)

/-- Admitted target endpoints retain the actual AND light-input order after repair. -/
theorem target_ordered {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    (layout H hq x).OrderedInputs (targetAxes H hq x) :=
  Partner.Cuts.repairAxes_ordered (raw_valid H hq x) (PushS.WordSource.target_ordered H hq hx)

/-- The native source drawing has the same fixed upper active-arc bound on every word. -/
private theorem raw_upperActive_le (x : NCL.HWord.Instance q) :
    (rawLayout H hq x).pages.upperPage.maxActive ≤ upperBudget q := by
  obtain ⟨drawing, he, _, hwin, hpanel, _, _⟩ := PushS.WordSource.native_validDrawing H hq x
  obtain ⟨height, hfit⟩ := StripSource.drawingFits drawing (PushS.WordSource.native_valid H hq x) hwin
  have hu := Comb.compile_upper_maxActive_le (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)
    (native H hq x).ncl.graph (PushS.WordSource.native_valid H hq x) drawing height
    (PushPuzzle.NCL.HWord.Strip.Sweep.drawingSpan q) hfit hwin hpanel
  simpa only [rawLayout, StripSource.layout, StripSource.toComb, he, upperBudget] using hu

/-- The original source's highest working level has its fixed word-family bound. -/
private theorem raw_highest_le (x : NCL.HWord.Instance q) :
    (rawLayout H hq x).pages.highest ≤ PushS.WordSource.levelBudget q :=
  StripSource.validDrawing_highest_le (PushS.WordSource.native_valid H hq x)
    (PushS.WordSource.native_validDrawing H hq x)

/-- The actual complete partner repair stays within a fixed number of working levels. -/
theorem layout_highest_le (x : NCL.HWord.Instance q) :
    (layout H hq x).pages.highest ≤ levelBudget q := by
  have hh := Partner.Resources.repair_highest_le_source (raw_valid H hq x) (raw_upperActive_le H hq x)
  exact hh.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (max_le_max le_rfl (raw_highest_le H hq x))) 2)

/-- Complete actual partner repair grows the number of contour ports only linearly. -/
theorem layout_portCount_le (x : NCL.HWord.Instance q) :
    (layout H hq x).portCount ≤
      3 * (rawLayout H hq x).portCount + 6 * (rawLayout H hq x).portCount * (upperBudget q + 1) :=
  Partner.Resources.repair_portCount_le (raw_valid H hq x) (raw_upperActive_le H hq x)

/-- For admitted native endpoints, the repaired physical axis paths are exactly H-word reachability. -/
theorem axes_reachable_iff {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    Relation.ReflTransGen (layout H hq x).AxisStep (initialAxes H hq x) (targetAxes H hq x) ↔
      x ∈ NCL.HWord.language H := by
  have hg := (PushS.WordSource.guard_eq_true_iff H hq x).mp hx
  obtain ⟨drawing, _⟩ := PushS.WordSource.native_validDrawing H hq x
  obtain ⟨hv, he⟩ := PushS.WordSource.native_drawing_counts H hq x
  have hn := StripSource.normalizedAxes_reachable_iff (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)
    (native H hq x) (PushS.WordSource.native_valid H hq x) hv he drawing hg.2.1 hg.2.2
  exact (Partner.Cuts.repairAxes_reachable_iff (raw_valid H hq x) _ _
    (rawInitial_length H hq x) (rawTarget_length H hq x)).trans
      (hn.symm.trans (PushS.WordSource.native_reachable_iff H hq hx))

/-- The same native word path admits the ordered axis macros used by the actual physical board. -/
theorem axes_ordered_reachable_iff {x : NCL.HWord.Instance q} (hx : guard H hq x = true) :
    Relation.ReflTransGen (layout H hq x).OrderedAxisStep (initialAxes H hq x) (targetAxes H hq x) ↔
      x ∈ NCL.HWord.language H :=
  ((layout H hq x).axisReachable_iff_orderedReachable (layout_valid H hq x).lower _ _
    (initial_ordered H hq hx) (target_ordered H hq hx)).symm.trans (axes_reachable_iff H hq hx)

end PushPuzzle.Push.WordSource
