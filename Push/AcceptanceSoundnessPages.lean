/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPageSecond
import all Push.AcceptanceSoundnessCentral
import all PushS.PortBackground

/-! The common endpoint certificate gives the real separate-page street support throughout its whole trajectory. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The two genuine terminal sparse page supports intersect in the original physical page support. -/
theorem canonical_terminal_pages_supported (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (l.twoPageStreets p hl).support (Blocked.fill t (l.centralMarkers p)) := by
  apply canonical_filled_page_of_intersection l p hl hM haxes initial target hr ha
  intro q hq
  exact ⟨canonical_terminal_page_first_supported l p hl hM haxes initial target hr ha q hq,
    canonical_terminal_page_second_supported l p hl hM haxes initial target hr ha q hq⟩

/-- Every actual prefix of an accepted source path has the same separate-page support after filling its central markers. -/
theorem canonical_pages_supported_at (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (l.twoPageStreets p hl).support (Blocked.fill u (l.centralMarkers p)) := by
  have hC : Support.RelativeClosed (l.twoPageStreets p hl).support (l.geometricBlockers p) :=
    (l.twoPageStreets p hl).relativeClosed.mono_blockers
    (fun _ h => Finset.mem_union_left _ (l.twoPageStreets_blockers_subset p hl h))
  have hguard : Relation.ReflTransGen (Freeze.AvoidingStep
      (l.canonicalInstance p hl hM haxes initial target).board none (l.geometricBlockers p)) u t := by
    apply enrich_path hut
    intro a b hua hm hbt
    exact canonical_step_avoiding l p hl hM haxes initial target (hsu.trans hua) hm hbt ha
  have hterminal := canonical_terminal_pages_supported l p hl hM haxes initial target (hsu.trans hut) ha
  have hreverse {a b : State (p.W + 1) (p.H + 1)}
      (hpath : Relation.ReflTransGen (Freeze.AvoidingStep
        (l.canonicalInstance p hl hM haxes initial target).board none (l.geometricBlockers p)) a b) :
      Support.Supported (l.twoPageStreets p hl).support (Blocked.fill b (l.centralMarkers p)) →
        Support.Supported (l.twoPageStreets p hl).support (Blocked.fill a (l.centralMarkers p)) := by
    induction hpath with
    | refl => exact id
    | tail _ hm ih =>
      exact fun ht => ih (hC.step_source_filled_of_avoiding (fun _ h => Finset.mem_union_left _ h) hm ht)
  exact hreverse hguard hterminal

/-- Every actual prefix player lies in the original separate-page street system. -/
theorem canonical_player_on_pages (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    u.player ∈ (l.twoPageStreets p hl).support := by
  apply canonical_pages_supported_at l p hl hM haxes initial target hsu hut ha u.player
  intro hb
  rcases Finset.mem_union.mp hb with hb | hb
  · exact (hsu.valid (l.canonicalInstance p hl hM haxes initial target).initial_valid).2.2 hb
  · exact (canonical_central_markers_excluded_at l p hl hM haxes initial target hsu hut ha).player hb

/-- Every cell of a genuine accepted push ray is supported on its actual physical pages. -/
theorem canonical_push_run_on_pages (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {s u t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hss : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial s)
    (run : Run (l.canonicalInstance p hl hM haxes initial target).board d s n) (hn : 0 < n)
    (hp : u.player = run.cell 1)
    (hb : u.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (i : Fin (n + 2)) : run.cell i ∈ (l.twoPageStreets p hl).support := by
  have hm : Move (l.canonicalInstance p hl hM haxes initial target).board none d s u :=
    .push (hss.valid (l.canonicalInstance p hl hM haxes initial target).initial_valid) hn trivial run hp hb
  have havoid := canonical_step_avoiding l p hl hM haxes initial target hss ⟨d, hm⟩ hut ha
  have hC : Support.RelativeClosed (l.twoPageStreets p hl).support (l.geometricBlockers p) :=
    (l.twoPageStreets p hl).relativeClosed.mono_blockers
    (fun _ h => Finset.mem_union_left _ (l.twoPageStreets_blockers_subset p hl h))
  exact hC.push_run_filled_of_avoiding (fun _ h => Finset.mem_union_left _ h)
    (hss.valid (l.canonicalInstance p hl hM haxes initial target).initial_valid) run hn hp hb
    (havoid.2 d n run hn hp hb) (canonical_pages_supported_at l p hl hM haxes initial target (hss.tail ⟨d, hm⟩) hut ha) i

end PushPuzzle.Push.AcceptanceSoundness
