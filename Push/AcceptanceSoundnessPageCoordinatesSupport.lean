/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPageCoordinates
import all PushS.RelativeSupport

/-! Relative reverse support uses actual ray avoidance for both empty markers and full blockers. -/

public section
namespace PushPuzzle.PushS.Support

open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {G K : Finset (Cell w h)}
  {C D : Set (Cell w h)} {s t : State w h}

/-- Enlarging the avoided blockers preserves the same relative support. -/
theorem RelativeClosed.mono_blockers (hC : RelativeClosed C G) (hGK : G ⊆ K) :
    RelativeClosed C K := by
  intro d p q ha hp hq hpK hqK r hr
  apply hC ha hp hq (fun hg => hpK (hGK hg)) (fun hg => hqK (hGK hg))
  exact Relation.ReflTransGen.mono
    (fun _ _ h => ⟨h.1, fun hg => h.2.1 (hGK hg), fun hg => h.2.2 (hGK hg)⟩) _ _ hr

/-- Two supports closed along the same clear rays retain that closure in their intersection. -/
private theorem RelativeClosed.inter (hC : RelativeClosed C G) (hD : RelativeClosed D G) :
    RelativeClosed (C ∩ D) G := by
  intro d p q ha hp hq hpG hqG r hr
  exact ⟨hC ha hp.1 hq.1 hpG hqG r hr, hD ha hp.2 hq.2 hpG hqG r hr⟩

/-- A real push whose complete ray avoids the blockers lies in its terminal relative support. -/
theorem RelativeClosed.push_run_of_avoiding (hC : RelativeClosed C G)
    {d : Direction} {n : ℕ} (hs : s.Valid B) (run : Run B d s n) (hn : 0 < n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hG : ∀ i, run.cell i ∉ G) (ht : Supported C t) (i : Fin (n + 2)) : run.cell i ∈ C := by
  have hm : Move B none d s t := .push hs hn trivial run hp hb
  apply hC (players_adjacent hm) (ht _ ((mem_holes _).mp (source_player_mem_holes hm)))
    (ht _ hm.valid_target.2.2)
  · simpa only [run.start] using hG 0
  · simpa only [hp] using hG 1
  · exact straightReach_run run hG i

/-- Filling a subset of the avoided markers retains the same supported true push ray. -/
theorem RelativeClosed.push_run_filled_of_avoiding (hC : RelativeClosed C K) (hGK : G ⊆ K)
    {d : Direction} {n : ℕ} (hs : s.Valid B) (run : Run B d s n) (hn : 0 < n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hK : ∀ i, run.cell i ∉ K) (ht : Supported C (Blocked.fill t G))
    (i : Fin (n + 2)) : run.cell i ∈ C := by
  have hm : Move B none d s t := .push hs hn trivial run hp hb
  have hsource : s.player ∉ (Blocked.fill t G).boxes := by
    intro hb'
    rcases Finset.mem_union.mp hb' with hb' | hb'
    · exact (mem_holes _).mp (source_player_mem_holes hm) hb'
    · exact hK 0 (run.start.symm ▸ hGK hb')
  have htarget : t.player ∉ (Blocked.fill t G).boxes := by
    intro hb'
    rcases Finset.mem_union.mp hb' with hb' | hb'
    · exact hm.valid_target.2.2 hb'
    · exact hK 1 (hp ▸ hGK hb')
  apply hC (players_adjacent hm) (ht _ hsource) (ht _ htarget)
  · simpa only [run.start] using hK 0
  · simpa only [hp] using hK 1
  · exact straightReach_run run hK i

/-- Filled terminal support pulls back through a true push avoiding all geometric blockers. -/
private theorem RelativeClosed.move_source_filled_of_avoiding (hC : RelativeClosed C K)
    (hGK : G ⊆ K)
    {d : Direction} (hm : Move B cap d s t)
    (hK : ∀ n (run : Run B d s n) (_hn : 0 < n)
      (_hp : t.player = run.cell 1)
      (_hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1))),
      ∀ i, run.cell i ∉ K) (ht : Supported C (Blocked.fill t G)) : Supported C (Blocked.fill s G) := by
  cases hm with
  | walk _ _ _ _ hb => simpa only [Supported, Blocked.fill, hb] using ht
  | @push n hs hn _ run hp hb =>
    intro q hq
    have hqbox : q ∉ s.boxes := fun hb => hq (Finset.mem_union_left _ hb)
    have hqG : q ∉ G := fun hg => hq (Finset.mem_union_right _ hg)
    by_cases he : q = run.cell ⟨n + 1, by omega⟩
    · subst q
      exact hC.push_run_filled_of_avoiding hGK hs run hn hp hb (hK n run hn hp hb) ht _
    · apply ht q
      intro hq'
      rcases Finset.mem_union.mp hq' with hq' | hq'
      · rw [hb] at hq'
        rcases Finset.mem_insert.mp hq' with he' | hb'
        · exact he he'
        · exact hqbox (Finset.mem_erase.mp hb').2
      · exact hqG hq'

/-- The actual geometric-avoidance step also pulls back support after filling its empty markers. -/
theorem RelativeClosed.step_source_filled_of_avoiding (hC : RelativeClosed C K) (hGK : G ⊆ K)
    (hm : Freeze.AvoidingStep B cap K s t) (ht : Supported C (Blocked.fill t G)) :
    Supported C (Blocked.fill s G) := by
  obtain ⟨d, hd⟩ := hm.1
  exact hC.move_source_filled_of_avoiding hGK hd (hm.2 d) ht

end PushPuzzle.PushS.Support

namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Both actual page supports are closed relative to the common established geometric blockers. -/
private theorem page_intersection_relativeClosed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) :
    Support.RelativeClosed ((twoPageFirst l p hl).support ∩ (twoPageSecond l p hl).support)
      (l.geometricBlockers p) := by
  apply Support.RelativeClosed.inter
  · exact (twoPageFirst_relativeClosed l p hl).mono_blockers
      (fun _ h => Finset.mem_union_left _ (twoPageFirst_blockers_subset l p hl h))
  · exact (twoPageSecond_relativeClosed l p hl).mono_blockers (twoPageSecond_blockers_subset l p hl)

/-- Filled terminal support preserves each isolated point on the original, unfilled true trajectory. -/
private theorem relative_isolated_box_reachable_filled {w h : ℕ} {C : Set (Cell w h)}
    {G K : Finset (Cell w h)} (hC : Support.RelativeClosed C K) (hGK : G ⊆ K)
    {q : Cell w h} (hi : Isolated C q) {B : Board w h} {cap : Option ℕ} {s t : State w h}
    (hr : Relation.ReflTransGen (Freeze.AvoidingStep B cap K) s t)
    (ht : Support.Supported C (Blocked.fill t G)) : q ∈ t.boxes ↔ q ∈ s.boxes := by
  revert ht
  induction hr with
  | refl => exact fun _ => Iff.rfl
  | @tail u v _ hm ih =>
    intro ht
    have he : q ∈ v.boxes ↔ q ∈ u.boxes := by
      obtain ⟨d, hd⟩ := hm.1
      cases hd with
      | walk _ _ _ _ hb => rw [hb]
      | @push n hs hn _ run hp hb =>
        have hRun := hC.push_run_filled_of_avoiding hGK hs run hn hp hb (hm.2 d n run hn hp hb) ht
        have hfirst : q ≠ run.cell 1 := by
          intro he
          subst q
          exact hi _ _ (run.adjacent 0).reverse (hRun 0)
        have hlast : q ≠ run.cell ⟨n + 1, by omega⟩ := by
          intro he
          subst q
          exact hi _ _ (run.adjacent ⟨n, by omega⟩).reverse (hRun ⟨n, by omega⟩)
        rw [hb]
        simp only [Finset.mem_insert, Finset.mem_erase]
        tauto
    exact he.trans (ih (hC.step_source_filled_of_avoiding hGK hm ht))

/-- Actual accepted play and the two terminal page supports give the original physical page support. -/
theorem canonical_filled_page_of_intersection (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : List Bool) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM ha initial target).board none
      (l.canonicalInstance p hl hM ha initial target).initial t)
    (haccept : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (ht : Support.Supported ((twoPageFirst l p hl).support ∩ (twoPageSecond l p hl).support)
      (Blocked.fill t (l.centralMarkers p))) :
    Support.Supported (l.twoPageStreets p hl).support (Blocked.fill t (l.centralMarkers p)) := by
  intro q hq
  by_contra ho
  have hpoint := ht q hq
  have hi := page_extra_intersection_isolated l p hl hpoint ho
  have hqG : q ∉ l.centralMarkers p := fun hg => hq (Finset.mem_union_right _ hg)
  have hqbox : q ∈ (l.canonicalInstance p hl hM ha initial target).initial.boxes := by
    by_contra hb
    apply ho
    apply canonical_filled_page_supported l p hl hM ha initial target q
    intro h
    exact (Finset.mem_union.mp h).elim hb hqG
  have he := relative_isolated_box_reachable_filled (page_intersection_relativeClosed l p hl)
    (fun _ h => Finset.mem_union_left _ h) hi
    (canonical_avoiding_prefix l p hl hM ha initial target hr .refl haccept) ht
  exact hq (Finset.mem_union_left _ (he.mpr hqbox))

end PushPuzzle.Push.AcceptanceSoundness
