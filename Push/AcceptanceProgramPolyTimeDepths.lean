/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeLayout
import all Push.AcceptanceProgramLayout
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! Actual fixed-level depth tables give uniform unary machines for dynamic page-column requests. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushS PushS.PortLayout Turing.MultiTapeTM

/-- Every allocated literal work depth, including level zero, in bounded table order. -/
@[expose] def fullDepthTable (p : Scales.Parameters) : List ℕ :=
  (List.range (p.levels + 1)).map p.Y

/-- Bounded table lookup agrees with the actual scale at every allocated level. -/
theorem fullDepthTable_getD (p : Scales.Parameters) {j : ℕ} (hj : j ≤ p.levels) :
    (fullDepthTable p).getD j 0 = p.Y j := by
  rw [List.getD_eq_getElem _ _ (by simp only [fullDepthTable, List.length_map, List.length_range]; omega)]
  simp only [fullDepthTable, List.getElem_map, List.getElem_range]

variable {α : Type} {enc : α ↪ List Bool} {p : α → Scales.Parameters} {M : ℕ}
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)

include haxes hlevels

/-- The actual complete work-depth table emits in standard polynomial time at a fixed level allocation. -/
theorem fullDepthTable_polyTime :
    ComputableInPolyTime (fun a => fullDepthTable (p a)) enc (encList encUnary) := by
  have htab := ComputableInPolyTime.mapConst (List.range (M + 1))
    (fun j _ => computableInPolyTime_Y haxes hlevels j)
  exact htab.of_enc_eq (fun a => by simp only [fullDepthTable, hlevels])

/-- Dynamic lookups in the actual fixed-level table use standard unary machines. -/
private theorem fullDepthLookup_polyTime : ComputableInPolyTime
    (fun q : α × ℕ => (fullDepthTable (p q.1)).getD q.2 0) (encPair enc encUnary) encUnary := by
  have ht := (fullDepthTable_polyTime haxes hlevels).comp (ComputableInPolyTime.fst enc encUnary)
  fun_prop

/-- The literal trim depth is polynomial-time even when its page-column level is supplied dynamically. -/
theorem trimDepth_polyTime : ComputableInPolyTime
    (fun q : α × ℕ => trimDepth (p q.1) q.2) (encPair enc encUnary) encUnary := by
  have hD : ComputableInPolyTime (fun q : α × ℕ => (p q.1).D) (encPair enc encUnary) encUnary :=
    (computableInPolyTime_D haxes hlevels).comp (ComputableInPolyTime.fst enc encUnary)
  have htab : ComputableInPolyTime (fun q : α × ℕ => fullDepthTable (p q.1))
      (encPair enc encUnary) (encList encUnary) :=
    (fullDepthTable_polyTime haxes hlevels).comp (ComputableInPolyTime.fst enc encUnary)
  have hsucc : ComputableInPolyTime Nat.succ encUnary encUnary := by
    change ComputableInPolyTime (fun n : ℕ => n + 1) _ _
    fun_prop
  have hy := fullDepthLookup_polyTime haxes hlevels
  have hargs : ComputableInPolyTime (fun q : α × ℕ => (q.1, q.2 + 1))
      (encPair enc encUnary) (encPair enc encUnary) := by fun_prop
  have hn : ComputableInPolyTime (fun q : α × ℕ => (fullDepthTable (p q.1)).getD (q.2 + 1) 0)
      (encPair enc encUnary) encUnary := hy.comp hargs
  have hraw : ComputableInPolyTime (fun q : α × ℕ =>
      if q.2 < M then ((fullDepthTable (p q.1)).getD q.2 0 + (fullDepthTable (p q.1)).getD (q.2 + 1) 0) / 2
      else (p q.1).D - 2) (encPair enc encUnary) encUnary := by fun_prop
  exact hraw.of_enc_eq (fun q => by
    apply congrArg encUnary
    unfold trimDepth
    rw [hlevels]
    split_ifs with hj
    · rw [fullDepthTable_getD _ (by rw [hlevels]; omega), fullDepthTable_getD _ (by rw [hlevels]; omega)]
    · rfl)

end PushPuzzle.Push.AcceptanceProgram
