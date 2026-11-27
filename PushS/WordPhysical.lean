/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.WordRecipe
public import PushS.PortPhysicalSimulation
public import PushS.StripSourceReachability

/-! The original word problem and its actual full wall-free canonical instance. -/

public section
namespace PushPuzzle.PushS.WordSource

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The literal fixed-level wall-free board emitted from the actual original native strip instance. -/
@[expose] def puzzle (x : NCL.HWord.Instance q)
    (hpages : (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).pages.Valid) : Instance :=
  (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).canonicalInstance
    (scales H hq (levelBudget q) x) hpages (highest_le_scales_levels H hq x)
    (portCount_le_scales_axes H hq (levelBudget q) x)
    (StripSource.normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (StripSource.normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))

/-- The actual admitted word board solves exactly the original fixed-alphabet word instance. -/
theorem puzzle_solvable_iff {x : NCL.HWord.Instance q} (hx : guard H hq x = true)
    (hpages : (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).pages.Valid) :
    (puzzle H hq x hpages).Solvable ↔ x ∈ NCL.HWord.language H := by
  obtain ⟨P, _⟩ := native_validDrawing H hq x
  obtain ⟨hv, he'⟩ := native_drawing_counts H hq x
  have hg := (guard_eq_true_iff H hq x).mp hx
  have hn := StripSource.normalizedAxes_reachable_iff (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)
    (native H hq x) (native_valid H hq x) hv he' P hg.2.1 hg.2.2
  have hp := PortLayout.canonicalInstance_solvable_iff_axisReachable
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (scales H hq (levelBudget q) x) hpages (highest_le_scales_levels H hq x)
    (portCount_le_scales_axes H hq (levelBudget q) x)
    (StripSource.normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (StripSource.normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (initial_ordered H hq (x := x) hx) (target_ordered H hq (x := x) hx)
  exact hp.trans (hn.symm.trans (native_reachable_iff H hq (x := x) hx))

/-- The original complete puzzle uses the standard polynomial-time dense instance encoding. -/
theorem computableInPolyTime_puzzle
    (hpages : ∀ x, (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).pages.Valid) :
    ComputableInPolyTime (fun x => puzzle H hq x (hpages x)) (NCL.HWord.encInstance q) encoding := by
  have hn := PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq
  have hl := (StripSource.computableInPolyTime_layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp hn
  have hi := (StripSource.computableInPolyTime_normalizedInitialAxes
    (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp hn
  have ht := (StripSource.computableInPolyTime_normalizedTargetAxes
    (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp hn
  exact PortLayout.computableInPolyTime_canonicalInstance_of_layout
    (layout := fun x => StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (p := scales H hq (levelBudget q)) (M := levelBudget q + 1)
    (initial := fun x => StripSource.normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x))
    (target := fun x => StripSource.normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)) hl
    (computableInPolyTime_scales_axes H hq (levelBudget q)) (fun _ => rfl)
    hpages (highest_le_scales_levels H hq) (portCount_le_scales_axes H hq (levelBudget q)) hi ht

end PushPuzzle.PushS.WordSource
