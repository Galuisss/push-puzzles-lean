/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortPageSupport
public import PushS.PortWideBars
import all PushS.PortPageSupport
import all PushS.PortBackground

/-!
# Frozen physical background of the actual two-page support

Every successful push stays within its actual page streets. Cells outside this support,
apart from the permanent central holes, remain full and retain their physical box identities.
Together with central and wide permanent holes they provide the computed page blockers.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Actual background cells outside both page streets and the permanent central holes. -/
@[expose] noncomputable def pageBackgroundBoxes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact (Finset.univ.filter fun q => q ∉ (l.twoPageStreets p hl).support) \ l.centralMarkers p

/-- A page background cell lies outside the cut support and the central markers. -/
theorem mem_pageBackgroundBoxes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.pageBackgroundBoxes p hl ↔
      q ∉ (l.twoPageStreets p hl).support ∧ q ∉ l.centralMarkers p := by
  classical
  simp only [pageBackgroundBoxes, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Permanent central and wide holes together with the full page background. -/
@[expose] noncomputable def pageBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (l.centralMarkers p ∪ l.wideSeparatorHoles p) ∪ l.pageBackgroundBoxes p hl

private theorem pages_subset_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : (l.twoPageStreets p hl).support ⊆
      Support.streets (l.streetColumnSet p) (l.workingRowSet p) := by
  intro q hq
  rcases hq with hy | hv
  · exact Or.inr hy
  · apply Or.inl
    rw [← l.pageColumnSet_union p hl]
    exact (l.twoPageStreets p hl).system.vertical_columns q hv

/-- The original global background is part of the more precise page background. -/
theorem backgroundBoxes_subset_pageBackgroundBoxes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : l.backgroundBoxes p ⊆ l.pageBackgroundBoxes p hl := by
  intro q hq
  obtain ⟨hs, hc⟩ := (l.mem_backgroundBoxes p q).mp hq
  exact (l.mem_pageBackgroundBoxes p hl q).mpr ⟨fun hp => hs (pages_subset_streets l p hl hp), hc⟩

/-- The page blockers contain every blocker used by the actual wide-bar closure. -/
theorem wideBlockers_subset_pageBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : l.wideBlockers p ⊆ l.pageBlockers p hl := by
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hw
  · rcases Finset.mem_union.mp hq with hc | hb
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hc)
    · exact Finset.mem_union_right _ (l.backgroundBoxes_subset_pageBackgroundBoxes p hl hb)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

/-- Every actual initial page-background cell contains a box. -/
theorem pageBackgroundBoxes_initial_full :
    l.pageBackgroundBoxes p hl ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  classical
  have hs := l.encoded_without_central_page_supported p hl hM initial _
    (l.physicalInstance_initial_holes p hl hM ha initial target)
  intro q hq
  obtain ⟨hp, hc⟩ := (l.mem_pageBackgroundBoxes p hl q).mp hq
  by_contra hb
  exact hp (hs q (fun h => (Finset.mem_union.mp h).elim hb hc))

/-- Every page-background cell remains full at every prefix of an actual solution. -/
theorem physicalInstance_page_background_full {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.pageBackgroundBoxes p hl ⊆ u.boxes := by
  classical
  intro q hq
  obtain ⟨hp, hc⟩ := (l.mem_pageBackgroundBoxes p hl q).mp hq
  by_contra hb
  exact hp (l.physicalInstance_filled_page_supported_at p hl hM ha initial target hsu hut ht q
    (fun h => (Finset.mem_union.mp h).elim hb hc))

/-- Every actual solution player stays on the specified page of its selected column. -/
theorem physicalInstance_player_on_pages {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    u.player ∈ (l.twoPageStreets p hl).support := by
  have hv := hsu.valid (l.physicalInstance p hl hM ha initial target).initial_valid
  have hG := l.physicalInstance_central_excluded p hl hM ha initial target hsu hut ht
  exact l.physicalInstance_filled_page_supported_at p hl hM ha initial target hsu hut ht u.player
    (fun h => (Finset.mem_union.mp h).elim hv.2.2 hG.player)

/-- Every complete push ray in an actual solution stays on its cut page streets. -/
theorem physicalInstance_push_run_on_pages {s u t : State (p.W + 1) (p.H + 1)}
    {d : Direction} {n : ℕ}
    (hss : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s)
    (r : Run (l.physicalInstance p hl hM ha initial target).board d s n) (hn : 0 < n)
    (hp : u.player = r.cell 1)
    (hb : u.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (i : Fin (n + 2)) : r.cell i ∈ (l.twoPageStreets p hl).support := by
  have hs := hss.valid (l.physicalInstance p hl hM ha initial target).initial_valid
  have hm : Step (l.physicalInstance p hl hM ha initial target).board none s u :=
    ⟨d, .push hs hn trivial r hp hb⟩
  have hGs := l.physicalInstance_central_excluded p hl hM ha initial target hss
    ((Relation.ReflTransGen.single hm).trans hut) ht
  have hGu := l.physicalInstance_central_excluded p hl hM ha initial target (hss.tail hm) hut ht
  have hu := (Support.supported_fill_iff _ _ u).mp
    (l.physicalInstance_filled_page_supported_at p hl hM ha initial target (hss.tail hm) hut ht)
  have hC := (l.twoPageStreets p hl).relativeClosed.union_blockers
    (l.twoPageStreets_blockers_subset p hl)
  exact (hC.push_run hs r hn hp hb hGs hGu hu i).resolve_right
    (Blocked.run_avoids r hGs hGu hb i)

private theorem step_page_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hm : Step (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Freeze.AvoidingStep (l.physicalInstance p hl hM ha initial target).board none
      (l.pageBlockers p hl) u v := by
  refine ⟨hm, ?_⟩
  intro d n r hn hp hb i hblock
  rcases Finset.mem_union.mp hblock with hholes | hbackground
  · rcases Finset.mem_union.mp hholes with hc | hw
    · exact Blocked.run_avoids r
        (l.physicalInstance_central_excluded p hl hM ha initial target hsu
          ((Relation.ReflTransGen.single hm).trans hvt) ht)
        (l.physicalInstance_central_excluded p hl hM ha initial target (hsu.tail hm) hvt ht) hb i hc
    · exact Blocked.run_avoids r
        (l.physicalInstance_wide_excluded_at p hl hM ha initial target hsu
          ((Relation.ReflTransGen.single hm).trans hvt) ht)
        (l.physicalInstance_wide_excluded_at p hl hM ha initial target (hsu.tail hm) hvt ht) hb i hw
  · exact ((l.mem_pageBackgroundBoxes p hl (r.cell i)).mp hbackground).1
      (l.physicalInstance_push_run_on_pages p hl hM ha initial target hsu r hn hp hb hvt ht i)

/-- Every successful prefix carries complete push-ray avoidance of the actual page blockers. -/
theorem physicalInstance_page_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.pageBlockers p hl))
      (l.physicalInstance p hl hM ha initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact step_page_avoiding l p hl hM ha initial target hsa hm (hbu.trans hut) ht

/-- A complete actual solution avoids all computed page blockers along every push ray. -/
theorem physicalInstance_page_avoiding {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.pageBlockers p hl))
      (l.physicalInstance p hl hM ha initial target).initial t :=
  l.physicalInstance_page_avoiding_prefix p hl hM ha initial target hr .refl ht

/-- The physical lifting of every successful prefix fixes every original page-background box. -/
theorem physicalInstance_page_background_frozen_at {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (l.physicalInstance p hl hM ha initial target).initial)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ U : LabelledState ι (p.W + 1) (p.H + 1), U.state = u ∧
      Labels.GuardedReachable (l.physicalInstance p hl hM ha initial target).board none
        (l.pageBlockers p hl) S U ∧
      ∀ i, S.position i ∈ l.pageBackgroundBoxes p hl → U.position i = S.position i := by
  have hg := l.physicalInstance_page_avoiding_prefix p hl hM ha initial target hsu hut ht
  rw [← hS] at hg
  obtain ⟨U, hu, hlabels⟩ := Labels.lift_guarded hg
  exact ⟨U, hu, hlabels, fun i hi => hlabels.position i (Finset.mem_union_right _ hi)⟩

end Solution
end PushPuzzle.PushS.PortLayout
