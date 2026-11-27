/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideExcluded
public import PushS.PortPageClosure
import all PushS.PortBackground

/-! The actual accepted path avoids and freezes the complete physical page closure. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- Every actual accepted step avoids all central holes, wide separators, and full page-background boxes. -/
theorem canonical_page_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hm : Step (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Freeze.AvoidingStep (l.canonicalInstance p hl hM haxes initial target).board none
      (l.pageBlockers p hl) u v := by
  have hgeo := canonical_page_geometry_step_avoiding l p hl hM haxes initial target hsu hm hvt ha
  have hWu := canonical_wide_excluded_at l p hl hM haxes initial target hgate hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ha
  have hWv := canonical_wide_excluded_at l p hl hM haxes initial target hgate (hsu.tail hm) hvt ha
  refine ⟨hm, ?_⟩
  intro d n run hn hp hb i hblock
  rcases Finset.mem_union.mp hblock with hholes | hbackground
  · rcases Finset.mem_union.mp hholes with hc | hw
    · exact hgeo.2 d n run hn hp hb i (Finset.mem_union_left _ hc)
    · exact Blocked.run_avoids run hWu hWv hb i hw
  · exact hgeo.2 d n run hn hp hb i (Finset.mem_union_right _ hbackground)

/-- Every true accepted prefix avoids the full blockers used by the original page closure certificate. -/
theorem canonical_page_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.canonicalInstance p hl hM haxes initial target).board none (l.pageBlockers p hl))
      (l.canonicalInstance p hl hM haxes initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact canonical_page_step_avoiding l p hl hM haxes initial target hgate hsa hm (hbu.trans hut) ha

/-- The established static closure now freezes the actual page background, central columns and wide bars. -/
private theorem canonical_page_closure_avoiding {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.canonicalInstance p hl hM haxes initial target).board none (l.pageFrozenBlockers p hl))
      (l.canonicalInstance p hl hM haxes initial target).initial u :=
  (l.pageBackground_closure p hl hM haxes (l.canonical initial) (l.canonical target)).reachable
    (canonical_page_avoiding_prefix l p hl hM haxes initial target hgate hsu hut ha)

/-- Every labelled box in the complete actual page closure retains its original position. -/
theorem canonical_page_closure_frozen {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (l.canonicalInstance p hl hM haxes initial target).initial)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ∃ U : LabelledState ι (p.W + 1) (p.H + 1), U.state = u ∧
      Labels.GuardedReachable (l.canonicalInstance p hl hM haxes initial target).board none
        (l.pageFrozenBlockers p hl) S U ∧
      ∀ i, S.position i ∈ l.pageFrozenBlockers p hl → U.position i = S.position i := by
  have hguard := canonical_page_closure_avoiding l p hl hM haxes initial target hgate hsu hut ha
  rw [← hS] at hguard
  obtain ⟨U, hU, hlabels⟩ := Labels.lift_guarded hguard
  exact ⟨U, hU, hlabels, hlabels.position⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
