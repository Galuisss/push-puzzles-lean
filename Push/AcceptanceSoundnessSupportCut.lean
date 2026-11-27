/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupport
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramCut
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortInstance

/-! Original central-cut holes cannot be consumed once actual global support and new flank markers are known. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

private theorem auxiliary_flank_fixed (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ auxiliaries l p) {y : ℕ} (hy : y = p.D - 2 ∨ y = p.D + 2) : point x y ∈ l.fixedSegments p := by
  obtain ⟨hstreet, hnot⟩ := Finset.mem_sdiff.mp hx
  have haxis : x ∉ axisColumns l (coordinates p) := by
    intro ha
    exact hnot (Finset.mem_union_left _ (List.mem_toFinset.mpr ha))
  have hx0 : x ≠ 0 := by intro he; exact hnot (Finset.mem_union_right _ (by simp [he]))
  have hxW : x ≠ p.W := by intro he; exact hnot (Finset.mem_union_right _ (by simp [he]))
  have haux : x ∈ (streetColumns l (coordinates p)).filter
      (fun x => decide (x ≠ 0 ∧ x ≠ (coordinates p).W) && !((axisColumns l (coordinates p)).contains x)) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_toFinset.mp hstreet, ?_⟩
    simp only [show (coordinates p).W = p.W from rfl, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hx0, hxW⟩, by simpa using haxis⟩
  unfold fixedSegments markedInterior
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨x, haux, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  exact hy.elim (fun he => Or.inl (congrArg (point x) he)) (fun he => Or.inr (congrArg (point x) he))

private theorem auxiliary_flank_marker (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ auxiliaries l p)
    (hy : q.2.val = p.D - 2 ∨ q.2.val = p.D + 2) : q ∈ newCentralMarkers l p := by
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  have hnot := (Finset.mem_sdiff.mp hx).2
  have hx0 : q.1.val ≠ 0 := by intro he; exact hnot (Finset.mem_union_right _ (by simp [he]))
  have hxW : q.1.val ≠ p.W := by intro he; exact hnot (Finset.mem_union_right _ (by simp [he]))
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨point q.1.val q.2.val,
      auxiliary_flank_fixed l p hx hy, by simp [point, PortLayout.segment, Segment.Contains]⟩
  · intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega
  · omega
  · omega

section Canonical

variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

/-- A real push on an accepted source trajectory cannot fill an original central-cut hole. -/
private theorem canonical_push_avoids_central_cut {s u t : State (p.W + 1) (p.H + 1)}
    {d : Direction} {n : ℕ}
    (hss : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial s)
    (run : Run (l.canonicalInstance p hl hM haxes initial target).board d s n) (hn : 0 < n)
    (hp : u.player = run.cell 1)
    (hb : u.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.centralMarkers p) (hy : g.2.val = p.D) :
    run.cell ⟨n + 1, by omega⟩ ≠ g := by
  intro hend
  have hm : Move (l.canonicalInstance p hl hM haxes initial target).board none d s u :=
    .push (hss.valid (l.canonicalInstance p hl hM haxes initial target).initial_valid) hn trivial run hp hb
  have hst := (Relation.ReflTransGen.single ⟨d, hm⟩).trans hut
  have hsplayer := canonical_player_on_original l p hl hM haxes initial target hss hst ha
  have huplayer := canonical_player_on_original l p hl hM haxes initial target (hss.tail ⟨d, hm⟩) hut ha
  have hnewS := newCentralMarkers_excluded_at l p hl hM haxes initial target hss hst
    (canonical_initial_frame l p hl hM haxes initial target) (canonical_initial_holes l p hl hM haxes initial target) ha
  have hnewU := newCentralMarkers_excluded_at l p hl hM haxes initial target (hss.tail ⟨d, hm⟩) hut
    (canonical_initial_frame l p hl hM haxes initial target) (canonical_initial_holes l p hl hM haxes initial target) ha
  have hlast := run.position ⟨n + 1, by omega⟩
  have hlane := run.lane ⟨n + 1, by omega⟩
  rw [hend] at hlast hlane
  have haux := l.acceptanceOriginalAux_mem p hl hM haxes
    (l.acceptanceCutAux p (l.canonical initial) (l.centralMarkers_subset_encoded p _ hg)
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).2 hy)
  have hY (y : Fin (p.H + 1)) (hyD : y.val = p.D) : y ∉ l.workingRowSet p := by
    intro hrow
    have hgap := work_rows_central_gap l p (q := (g.1, y)) ((working_rows_iff l p y).mpr hrow)
    change y.val + 4 < p.D ∨ p.D + 4 < y.val at hgap
    have hD := last_depth_margin p
    omega
  cases d with
  | north =>
    let i : Fin (n + 2) := ⟨n - 1, by omega⟩
    have hi := run.position i
    have hix := run.lane i
    have hx : (run.cell i).1.val = g.1.val := by
      change (run.cell i).1.val = s.player.1.val at hix
      change g.1.val = s.player.1.val at hlane
      exact hix.trans hlane.symm
    have hiy : (run.cell i).2.val = p.D + 2 := by
      change -(g.2.val : ℤ) = -(s.player.2.val : ℤ) + (n + 1 : ℕ) at hlast
      change -((run.cell i).2.val : ℤ) = -(s.player.2.val : ℤ) + (n - 1 : ℕ) at hi
      omega
    exact Blocked.run_avoids run hnewS hnewU hb i
      (auxiliary_flank_marker l p (hx.symm ▸ haux) (Or.inr hiy))
  | south =>
    let i : Fin (n + 2) := ⟨n - 1, by omega⟩
    have hi := run.position i
    have hix := run.lane i
    have hx : (run.cell i).1.val = g.1.val := by
      change (run.cell i).1.val = s.player.1.val at hix
      change g.1.val = s.player.1.val at hlane
      exact hix.trans hlane.symm
    have hiy : (run.cell i).2.val = p.D - 2 := by
      change (g.2.val : ℤ) = (s.player.2.val : ℤ) + (n + 1 : ℕ) at hlast
      change ((run.cell i).2.val : ℤ) = (s.player.2.val : ℤ) + (n - 1 : ℕ) at hi
      omega
    exact Blocked.run_avoids run hnewS hnewU hb i
      (auxiliary_flank_marker l p (hx.symm ▸ haux) (Or.inl hiy))
  | east =>
    have has := players_adjacent hm
    have hsY : s.player.2 ∉ l.workingRowSet p := hY _ (by change g.2.val = s.player.2.val at hlane; omega)
    have huY : u.player.2 ∉ l.workingRowSet p := by rw [has.2]; exact hsY
    exact l.streetColumnSet_separated p (hsplayer.resolve_right hsY) (huplayer.resolve_right huY) has.1.symm
  | west =>
    have has := players_adjacent hm
    have hsY : s.player.2 ∉ l.workingRowSet p := hY _ (by change g.2.val = s.player.2.val at hlane; omega)
    have huY : u.player.2 ∉ l.workingRowSet p := by rw [has.2]; exact hsY
    exact l.streetColumnSet_separated p (huplayer.resolve_right huY) (hsplayer.resolve_right hsY) has.1

/-- Every original D0 cut hole stays empty along the genuine accepted trajectory. -/
theorem canonical_central_cut_empty_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.centralMarkers p) (hy : g.2.val = p.D) :
    g ∈ PushS.holes u := by
  induction hsu with
  | refl =>
    exact (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => g ∈ E)
      (canonical_initial_holes l p hl hM haxes initial target)).mpr
      (l.centralMarkers_subset_encoded p (l.canonical initial) hg)
  | @tail s u hss hstep ih =>
    have hold := ih ((Relation.ReflTransGen.single hstep).trans hut)
    cases hstep.choose_spec with
    | walk _ _ _ _ hb => simpa only [PushS.holes, hb] using hold
    | @push n hs hn _ run hp hb =>
      have hne := canonical_push_avoids_central_cut l p hl hM haxes initial target hss run hn hp hb hut ha hg hy
      exact (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => g ∈ E)
        (PushS.holes_push run hn hb)).mpr
        (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hne, hold⟩))

/-- Actual acceptance protects every original and newly added central marker at the terminal state. -/
private theorem canonical_central_markers_terminal {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.centralMarkers p ⊆ PushS.holes t := by
  intro g hg
  by_cases hy : g.2.val = p.D
  · exact canonical_central_cut_empty_at l p hl hM haxes initial target hr .refl ha hg hy
  · exact newCentralMarkers_terminal l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target) (canonical_initial_holes l p hl hM haxes initial target)
      ha (Finset.mem_filter.mpr ⟨hg, hy⟩)

/-- The whole actual central marker set is permanently empty and unvisited on accepted source play. -/
theorem canonical_central_markers_excluded_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Blocked.Excluded (l.centralMarkers p) u := by
  apply Distant.excluded_at hsu hut (canonical_initial_frame l p hl hM haxes initial target)
    (program_frame_empty l p target ha)
  · exact l.centralMarkers_far p hl haxes (l.canonical initial) _ (canonical_initial_holes l p hl hM haxes initial target)
  · exact canonical_central_markers_terminal l p hl hM haxes initial target (hsu.trans hut) ha

/-- All actual central marker holes may be filled with boxes throughout any accepted source segment. -/
theorem canonical_central_fill_between {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (huv : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (Blocked.fill u (l.centralMarkers p)) (Blocked.fill v (l.centralMarkers p)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) huv
    (fun _ hux hxv => canonical_central_markers_excluded_at l p hl hM haxes initial target
      (hsu.trans hux) (hxv.trans hvt) ha)
  rw [(l.canonicalInstance p hl hM haxes initial target).walls_empty]
  exact Finset.disjoint_empty_right _

/-- Filling all established central markers retains the actual global street support. -/
theorem canonical_central_filled_supported_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (supportCoordinates l p).original (Blocked.fill u (l.centralMarkers p)) := by
  intro q hq
  apply canonical_original_supported_at l p hl hM haxes initial target hsu hut ha q
  intro hb
  exact hq ((Finset.mem_union.mp hb).elim (Finset.mem_union_left _)
    (fun hm => Finset.mem_union_right _ (newCentralMarkers_subset l p hm)))

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
