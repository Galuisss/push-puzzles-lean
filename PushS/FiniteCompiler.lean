/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLegal
public import PushFS.Reduction.PhysicalCompiler

/-! A total actual finite-force source compiler in the standard dense machine encoding. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteCompiler

open PushFS PushFS.Reduction
open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime

/-- Every checked source is rendered as the complete thick-wall board; rejected sources use the fixed corridor. -/
def walled (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance) : PushFS.Instance :=
  if h : PhysicalCompiler.checkedGuard x = true then
    FiniteSourceInventory.checkedPuzzle w hw (PhysicalCompiler.source x)
      ((PhysicalCompiler.checkedGuard_spec x).mp h).plane ((PhysicalCompiler.checkedGuard_spec x).mp h).typed
  else reject

def walledOutput (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance) : Encoding.Data :=
  if PhysicalCompiler.checkedGuard x then (FiniteSourceInventory.table w hw).data (PhysicalCompiler.source x)
  else Encoding.data reject

private theorem walled_data (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance) :
    Encoding.data (walled w hw x) = walledOutput w hw x := by
  by_cases h : PhysicalCompiler.checkedGuard x = true
  · rw [walled,dite_eq_left h,walledOutput,ite_eq_left h]
    exact FiniteSourceInventory.checkedPuzzle_data w hw _ _ _
  · rw [walled,dite_eq_right h,walledOutput,ite_eq_right h]

private theorem walledOutput_polyTime (w : ℕ) (hw : 2 ≤ w) :
    ComputableInPolyTime (walledOutput w hw) encPlaneWordAndOrNCL Encoding.encData :=
  PhysicalCompiler.checkedGuard_polyTime.ite'
    ((FiniteSourceInventory.data_polyTime w hw).comp PhysicalCompiler.source_polyTime) (const (Encoding.data reject))

private theorem walled_polyTime (w : ℕ) (hw : 2 ≤ w) :
    ComputableInPolyTime (walled w hw) encPlaneWordAndOrNCL PushFS.encoding :=
  (walledOutput_polyTime w hw).of_enc_eq (fun x => congrArg Encoding.encData (walled_data w hw x))

/-- Every virtual wall is emitted as an ordinary box already on its storage target. -/
noncomputable def compile (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance) : PushS.Instance :=
  FiniteWalls.fillWalls (walled w hw x)

theorem compile_polyTime (w : ℕ) (hw : 2 ≤ w) :
    ComputableInPolyTime (compile w hw) encPlaneWordAndOrNCL PushS.encoding :=
  FiniteWalls.fillWalls_polyTime.comp (walled_polyTime w hw)

/-- The actual complete compiler wall union is frozen at its prescribed finite force. -/
theorem walled_thick (k : ℕ) (hk : 1 ≤ k) (x : PlaneWordAndOrNCL.Instance) :
    FiniteFreeze.Thick k (walled (k+1) (by omega) x).board.walls := by
  by_cases h : PhysicalCompiler.checkedGuard x = true
  · rw [walled,dite_eq_left h]
    exact FiniteSourceInventory.walls_thick k hk _
  · rw [walled,dite_eq_right h]
    intro d p hp
    exact False.elim (Finset.notMem_empty p hp)

theorem compile_solvable_iff (k : ℕ) (hk : 1 ≤ k) (x : PlaneWordAndOrNCL.Instance) :
    (compile (k+1) (by omega) x).SolvableFinite k ↔ (walled (k+1) (by omega) x).Solvable (some k) :=
  FiniteWalls.fillWalls_solvable_iff _ (walled_thick k hk x)

theorem walled_eq (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance)
    (hx : PhysicalCompiler.SourceChecks x) :
    walled w hw x = FiniteSourceInventory.checkedPuzzle w hw (PhysicalCompiler.source x) hx.plane hx.typed :=
  dite_eq_left ((PhysicalCompiler.checkedGuard_spec x).mpr hx)

end PushPuzzle.PushS.FiniteCompiler
