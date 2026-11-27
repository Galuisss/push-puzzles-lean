/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeDepths
import all Push.AcceptanceProgramLayout

/-! Standard request-list and actual column-trim emission from the real fixed-level geometry. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout Turing.MultiTapeTM

/-- Canonically sorted actual lane sets emit their complete computed prefix-request list. -/
private theorem prefixRequests_polyTime {α : Type} {enc : α ↪ List Bool}
    {lanes : α → Finset ℕ} {span : α → ℕ → ℕ}
    (hl : ComputableInPolyTime lanes enc encLaneSet)
    (hs : ComputableInPolyTime (fun p : α × ℕ => span p.1 p.2) (encPair enc encUnary) encUnary) :
    ComputableInPolyTime (fun a => prefixRequests (lanes a) (span a)) enc Scan.encRequests := by
  have hpair : ComputableInPolyTime (fun p : α × ℕ => (p.2, span p.1 p.2))
      (encPair enc encUnary) (encPair encUnary encUnary) := by fun_prop
  exact ComputableInPolyTime.mapWithInput (laneSet_sort_polyTime.comp hl) hpair

/-- A computed common span emits all requests of one actual finite lane family. -/
@[fun_prop] theorem prefixRequests_const_polyTime {α : Type} {enc : α ↪ List Bool}
    {lanes : α → Finset ℕ} {span : α → ℕ}
    (hl : ComputableInPolyTime lanes enc encLaneSet) (hs : ComputableInPolyTime span enc encUnary) :
    ComputableInPolyTime (fun a => prefixRequests (lanes a) (fun _ => span a)) enc Scan.encRequests :=
  prefixRequests_polyTime (span := fun a _ => span a) hl (hs.comp (ComputableInPolyTime.fst _ _))

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)

include haxes hlevels

/-- An actual whole-row template emits in the compact standard encoding. -/
theorem readRows_polyTime (side : Direction) {rows : α → Finset ℕ}
    (hr : ComputableInPolyTime rows enc encLaneSet) :
    ComputableInPolyTime (fun a => readRows (p a) side (rows a)) enc encTemplate := by
  have hW : ComputableInPolyTime (fun q : α × ℕ => (p q.1).W + 1) (encPair enc encUnary) encUnary := by
    have hw := (computableInPolyTime_W haxes hlevels).comp (ComputableInPolyTime.fst enc encUnary)
    fun_prop
  have hreq := prefixRequests_polyTime (span := fun a _ => (p a).W + 1) hr hW
  unfold readRows
  fun_prop

/-- An actual whole-column template emits in the compact standard encoding. -/
theorem readColumns_polyTime (side : Direction) {columns : α → Finset ℕ}
    (hc : ComputableInPolyTime columns enc encLaneSet) :
    ComputableInPolyTime (fun a => readColumns (p a) side (columns a)) enc encTemplate := by
  have hH : ComputableInPolyTime (fun q : α × ℕ => (p q.1).H + 1) (encPair enc encUnary) encUnary := by
    have hh := (computableInPolyTime_H haxes hlevels).comp (ComputableInPolyTime.fst enc encUnary)
    fun_prop
  have hreq := prefixRequests_polyTime (span := fun a _ => (p a).H + 1) hc hH
  unfold readColumns
  fun_prop

include hl

/-- The actual public-column trim computes every request from its own page and marker depth. -/
theorem trimRound_polyTime (side : Side) :
    ComputableInPolyTime (fun a => trimRound (layout a) (p a) side) enc encTemplate := by
  have hcols := acceptance_pageColumns_polyTime hl haxes hlevels side
  have hfiltered : ComputableInPolyTime (fun a => (pageColumns (layout a) (p a) side).filter fun c => !c.privateColumn)
      enc (encList encPageColumn) := by fun_prop
  have hargs : ComputableInPolyTime (fun q : α × PageColumn => (q.1, q.2.level))
      (encPair enc encPageColumn) (encPair enc encUnary) := by fun_prop
  have hdepth : ComputableInPolyTime (fun q : α × PageColumn => trimDepth (p q.1) q.2.level)
      (encPair enc encPageColumn) encUnary := (trimDepth_polyTime haxes hlevels).comp hargs
  have hcallback : ComputableInPolyTime (fun q : α × PageColumn => (q.2.column, trimDepth (p q.1) q.2.level))
      (encPair enc encPageColumn) (encPair encUnary encUnary) := by fun_prop
  have hrequests := ComputableInPolyTime.mapWithInput (f := fun a c => (c.column, trimDepth (p a) c.level)) hfiltered hcallback
  unfold trimRound
  fun_prop

end PushPuzzle.Push.AcceptanceProgram
