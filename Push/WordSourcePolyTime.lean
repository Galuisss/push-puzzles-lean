/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSource
public import Push.PartnerPolyTimeAxes

/-! Standard polynomial-time emission of the actual repaired hard-word source data. -/

public section
namespace PushPuzzle.Push.WordSource

open PushS Cslib.Complexity Turing.MultiTapeTM

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The original native layout emits in the standard unary port-layout encoding. -/
private theorem computableInPolyTime_rawLayout :
    ComputableInPolyTime (rawLayout H hq) (NCL.HWord.encInstance q) encPortLayout :=
  (StripSource.computableInPolyTime_layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp
    (PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq)

/-- The actual complete reader-partner layout emits in standard polynomial time. -/
theorem computableInPolyTime_layout :
    ComputableInPolyTime (layout H hq) (NCL.HWord.encInstance q) encPortLayout :=
  Partner.encBufferState_layout_polyTime (Partner.Cuts.repair_polyTime.comp (computableInPolyTime_rawLayout H hq))

/-- The original normalized initial contour word emits in standard polynomial time. -/
private theorem computableInPolyTime_rawInitial :
    ComputableInPolyTime (rawInitial H hq) (NCL.HWord.encInstance q) (encList encBool) :=
  (StripSource.computableInPolyTime_normalizedInitialAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp
    (PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq)

/-- The original normalized target contour word emits in standard polynomial time. -/
private theorem computableInPolyTime_rawTarget :
    ComputableInPolyTime (rawTarget H hq) (NCL.HWord.encInstance q) (encList encBool) :=
  (StripSource.computableInPolyTime_normalizedTargetAxes (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)).comp
    (PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_compile H hq)

/-- The actual repaired initial physical direction word emits in standard polynomial time. -/
theorem computableInPolyTime_initialAxes :
    ComputableInPolyTime (initialAxes H hq) (NCL.HWord.encInstance q) (encList encBool) :=
  Partner.Cuts.repairAxes_polyTime.comp ((computableInPolyTime_rawLayout H hq).pair (computableInPolyTime_rawInitial H hq))

/-- The actual repaired target physical direction word emits in standard polynomial time. -/
theorem computableInPolyTime_targetAxes :
    ComputableInPolyTime (targetAxes H hq) (NCL.HWord.encInstance q) (encList encBool) :=
  Partner.Cuts.repairAxes_polyTime.comp ((computableInPolyTime_rawLayout H hq).pair (computableInPolyTime_rawTarget H hq))

/-- The same actual endpoint legality guard has its standard polynomial-time implementation. -/
theorem computableInPolyTime_guard :
    ComputableInPolyTime (guard H hq) (NCL.HWord.encInstance q) encBool :=
  PushS.WordSource.computableInPolyTime_guard H hq

end PushPuzzle.Push.WordSource
