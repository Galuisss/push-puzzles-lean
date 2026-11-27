/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalRaster
public import PushFS.Reduction.Fallback
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Reachability
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.PlanePolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.TypingPolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.CompilePolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.StepPolyTime

/-! The total actual physical source-to-PushFS compiler and its standard-encoding polynomial-time machine. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalCompiler


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL

def source (x : PlaneWordAndOrNCL.Instance) : CellPlan.Source := (x.word,(x.initial,x.target))

theorem source_polyTime : ComputableInPolyTime source encPlaneWordAndOrNCL CellPlan.encSource := by
  unfold source
  fun_prop

def guard (x : PlaneWordAndOrNCL.Instance) : Bool := x.word.checkPlane && decide (x.word.WellTyped [] [])

theorem guard_spec (x : PlaneWordAndOrNCL.Instance) :
    guard x=true ↔x.word.checkPlane=true ∧x.word.WellTyped [] [] := by simp only [guard,Bool.and_eq_true,decide_eq_true_eq]

private theorem guard_polyTime : ComputableInPolyTime guard encPlaneWordAndOrNCL encBool := by
  have hw : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>x.word) encPlaneWordAndOrNCL encWord := by fun_prop
  exact (Word.computableInPolyTime_checkPlane.bool_and' Word.computableInPolyTime_wellTyped).comp hw

/-- Complete physical storage board for each checked source; the certified rejecting board handles other words. -/
noncomputable def compile (x : PlaneWordAndOrNCL.Instance) : Instance :=
  if h : guard x=true then PhysicalInventory.puzzle (source x) ((guard_spec x).mp h).1 ((guard_spec x).mp h).2
  else reject

def output (x : PlaneWordAndOrNCL.Instance) : Encoding.Data :=
  if guard x then PhysicalBitmap.data (source x) else Encoding.data reject

theorem output_polyTime : ComputableInPolyTime output encPlaneWordAndOrNCL Encoding.encData :=
  guard_polyTime.ite' (PhysicalBitmap.data_polyTime.comp source_polyTime) (const (Encoding.data reject))

private theorem compile_data (x : PlaneWordAndOrNCL.Instance) : Encoding.data
    (compile x)=output x := by
  by_cases h : guard x=true
  · rw [compile,dite_eq_left h,output,ite_eq_left h]
    exact PhysicalInventory.data_eq (source x) ((guard_spec x).mp h).1 ((guard_spec x).mp h).2
  · rw [compile,dite_eq_right h,output,ite_eq_right h]

/-- The actual total unlabelled storage-instance compiler has a genuine standard-encoding PT machine. -/
private theorem compile_polyTime : ComputableInPolyTime compile encPlaneWordAndOrNCL encoding :=
  output_polyTime.of_enc_eq (fun x=>congrArg Encoding.encData (compile_data x))

private theorem compile_eq (x : PlaneWordAndOrNCL.Instance) (hP : x.word.checkPlane=true)
    (hT : x.word.WellTyped [] []) :
    compile x=PhysicalInventory.puzzle (source x) hP hT := by
  exact dite_eq_left ((guard_spec x).mpr ⟨hP,hT⟩)

/-- The complete source-side checks used by the decision-problem reduction. -/
structure SourceChecks (x : PlaneWordAndOrNCL.Instance) : Prop where
  plane : x.word.checkPlane=true
  typed : x.word.WellTyped [] []
  valid : (Word.compile x.word).Valid
  initial_width : x.initial.length=(Word.compile x.word).edgeCount
  target_width : x.target.length=(Word.compile x.word).edgeCount
  initial_legal : (Word.compile x.word).checkLegal x.initial=true
  target_legal : (Word.compile x.word).checkLegal x.target=true

def checkedGuard (x : PlaneWordAndOrNCL.Instance) : Bool :=
  guard x && ((Word.compile x.word).checkValid &&
    ((decide (x.initial.length=(Word.compile x.word).edgeCount) &&
      decide (x.target.length=(Word.compile x.word).edgeCount)) &&
      ((Word.compile x.word).checkLegal x.initial && (Word.compile x.word).checkLegal x.target)))

theorem checkedGuard_spec (x : PlaneWordAndOrNCL.Instance) :
    checkedGuard x=true ↔SourceChecks x := by
  simp only [checkedGuard,Bool.and_eq_true,guard_spec,AndOrGraph.checkValid_eq_true_iff,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hP,hT⟩,hV,⟨ha,hb⟩,hLa,hLb⟩
    exact ⟨hP,hT,hV,ha,hb,hLa,hLb⟩
  · intro h
    exact ⟨⟨h.plane,h.typed⟩,h.valid,⟨h.initial_width,h.target_width⟩,h.initial_legal,h.target_legal⟩

theorem checkedGuard_polyTime : ComputableInPolyTime checkedGuard encPlaneWordAndOrNCL encBool := by
  have hw : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>x.word)
      encPlaneWordAndOrNCL encWord := by fun_prop
  have hg:=Word.computableInPolyTime_compile.comp hw
  have hvalid:=AndOrGraph.computableInPolyTime_checkValid.comp hg
  have ha : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>x.initial)
      encPlaneWordAndOrNCL (encList encBool) := by fun_prop
  have hb : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>x.target)
      encPlaneWordAndOrNCL (encList encBool) := by fun_prop
  have ha':=(bits_encList_polyTime encBool).2.comp ha
  have hb':=(bits_encList_polyTime encBool).2.comp hb
  have hn : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>(Word.compile x.word).edgeCount)
      encPlaneWordAndOrNCL encNat := by fun_prop
  have hna : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>x.initial.length)
      encPlaneWordAndOrNCL encUnary := by fun_prop
  have hnb : ComputableInPolyTime (fun x : PlaneWordAndOrNCL.Instance=>x.target.length)
      encPlaneWordAndOrNCL encUnary := by fun_prop
  have hsizeA:=(ComputableInPolyTime.unary_to_binary.comp hna).decide_eq' hn
  have hsizeB:=(ComputableInPolyTime.unary_to_binary.comp hnb).decide_eq' hn
  have hlegalA:=AndOrGraph.computableInPolyTime_checkLegal hg ha'
  have hlegalB:=AndOrGraph.computableInPolyTime_checkLegal hg hb'
  exact guard_polyTime.bool_and' (hvalid.bool_and' ((hsizeA.bool_and' hsizeB).bool_and'
    (hlegalA.bool_and' hlegalB)))

/-- Source membership supplies every decidable validity and endpoint check. -/
theorem checks_of_mem {x : PlaneWordAndOrNCL.Instance} (hx : x∈PlaneWordAndOrNCL) : SourceChecks x := by
  obtain ⟨hP,hT,hV,ha,hb,hLa,hr⟩:=hx
  exact ⟨hP,hT,hV,ha,hb,(AndOrGraph.checkLegal_eq_true_iff _ hV.1 _).mpr hLa,
    (AndOrGraph.checkLegal_eq_true_iff _ hV.1 _).mpr (hr.legal hLa)⟩

/-- Reject malformed source data before emitting a complete actual physical board. -/
noncomputable def checkedCompile (x : PlaneWordAndOrNCL.Instance) : Instance :=
  if checkedGuard x then compile x else reject

theorem checkedCompile_polyTime : ComputableInPolyTime checkedCompile encPlaneWordAndOrNCL encoding :=
  checkedGuard_polyTime.ite' compile_polyTime (const reject)

theorem checkedCompile_eq (x : PlaneWordAndOrNCL.Instance) (hx : SourceChecks x) :
    checkedCompile x=PhysicalInventory.puzzle (source x) hx.plane hx.typed := by
  rw [checkedCompile,ite_eq_left ((checkedGuard_spec x).mpr hx)]
  exact compile_eq x hx.plane hx.typed

theorem checkedCompile_reject (x : PlaneWordAndOrNCL.Instance) (hx : ¬SourceChecks x) :
    checkedCompile x=reject :=
  ite_eq_right (fun h=>hx ((checkedGuard_spec x).mp h))

end PushPuzzle.PushFS.Reduction.PhysicalCompiler
