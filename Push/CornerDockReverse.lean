/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockLift
public import Push.FirstExit
public import Push.ConvexSupport
import all Push.ConvexSupport

/-! The first westward dock exit recovers a complete original left-goal trajectory. -/

@[expose] public section
namespace PushPuzzle.Push.CornerDock.Input

open PushFS PushS

variable (r : Input)

private def InsideCell (q : Cell r.outputWidth r.outputHeight) : Prop :=
  2 ≤ q.1.val ∧ q.2.val < r.height

private def Inside (s : PushFS.State r.outputWidth r.outputHeight) : Prop := r.InsideCell s.player

private def InsideStep (s t : PushFS.State r.outputWidth r.outputHeight) : Prop :=
  @Step r.outputWidth r.outputHeight r.compile.board none s t ∧ r.Inside t

private theorem initial_inside : r.Inside (r.extend r.initial).toState := by
  change 2 ≤ r.initial.player.1.val + 2 ∧ r.initial.player.2.val < r.height
  exact ⟨by omega, r.initial.player.2.isLt⟩

private theorem prefix_real {s : PushFS.State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s) :
    @Reachable r.outputWidth r.outputHeight r.compile.board none (r.extend r.initial).toState s :=
  Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hr

private theorem prefix_inside {s : PushFS.State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s) : r.Inside s := by
  cases hr with
  | refl => exact r.initial_inside
  | tail _ hm => exact hm.2

private theorem initial_holes : holes (r.extend r.initial).toState = (r.extend r.initial).empty :=
  (r.extend r.initial).holes_toState

private theorem initial_outside_hole (q : Cell r.outputWidth r.outputHeight)
    (hout : ¬r.InsideCell q) (hq : q ∈ holes (r.extend r.initial).toState) : q ∈ r.auxiliaryHoles := by
  rw [r.initial_holes] at hq
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hq
    exact False.elim (hout ⟨by change 2 ≤ a.1.val + 2; omega, a.2.isLt⟩)
  · exact hq

private theorem outside_hole_source {s : PushFS.State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s)
    (q : Cell r.outputWidth r.outputHeight) (hout : ¬r.InsideCell q)
    (hq : q ∈ holes s) : q ∈ r.auxiliaryHoles := by
  apply r.initial_outside_hole q hout
  induction hr with
  | refl => exact hq
  | @tail u v _ hm ih =>
    have hne : q ≠ v.player := fun he => hout (he ▸ hm.2)
    exact ih (hole_source_of_ne_player hm.1.choose_spec hne hq)

private theorem hole_support {s : PushFS.State r.outputWidth r.outputHeight}
    (hr : @Reachable r.outputWidth r.outputHeight r.compile.board none (r.extend r.initial).toState s)
    (q : Cell r.outputWidth r.outputHeight) (hq : q ∈ holes s) :
    q.1.val < 2 ∨ q.2.val < r.height := by
  have hi : PushS.Support.Supported {q : Cell r.outputWidth r.outputHeight |
      q.1.val < 2 ∨ q.2.val < r.height} (r.extend r.initial).toState := by
    intro a ha
    have hh : a ∈ (r.extend r.initial).empty := by
      rw [← r.initial_holes]
      exact (mem_holes _).mpr ha
    rcases Finset.mem_union.mp hh with hs | hh
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hs
      exact Or.inr b.2.isLt
    · rcases Finset.mem_insert.mp hh with rfl | hh
      · exact Or.inl (by change 1 < 2; omega)
      · exact Or.inl (Finset.mem_filter.mp hh).2.1
  exact (Support.southeast_compl_axisConvex 2 r.height).reachable_target hr hi q ((mem_holes _).mp hq)

private theorem auxiliary_on_source_row (q : Cell r.outputWidth r.outputHeight)
    (hq : q ∈ r.auxiliaryHoles) (hy : q.2.val < r.height) : q = r.entry := by
  have hx : q.1.val < 2 := by
    rcases Finset.mem_insert.mp hq with he | he
    · rw [he]
      change 1 < 2
      omega
    · exact (Finset.mem_filter.mp he).2.1
  exact (r.west_holes_on_source_rows r.initial q hx hy).mp (Finset.mem_union_right _ hq)

private theorem exit_geometry {s t : PushFS.State r.outputWidth r.outputHeight} {d : Direction}
    (hs : r.Inside s) (hx : t.player.1.val < 2) (ha : Adjacent d s.player t.player) :
    d = .west ∧ s.player.1.val = 2 ∧ t.player.1.val = 1 ∧ t.player.2.val = s.player.2.val := by
  obtain ⟨hsx, hsy⟩ := hs
  cases d <;> simp only [Adjacent] at ha
  all_goals first | omega | exact ⟨rfl, by omega, by omega, congrArg Fin.val ha.2⟩

private theorem first_exit_goal {s t : PushFS.State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s) (hs : r.Inside s)
    (hm : @Step r.outputWidth r.outputHeight r.compile.board none s t) (ht : ¬r.Inside t) :
    s.player = r.embed r.sourceGoal ∧ r.entry ∈ holes s := by
  have hreal := r.prefix_real hr
  have htv := PushFS.Reachable.valid (hreal.tail hm) r.compile.initial_valid
  have hsup := r.hole_support (hreal.tail hm) t.player (player_mem_holes htv)
  have htx : t.player.1.val < 2 := by dsimp [Inside, InsideCell] at ht; omega
  obtain ⟨d, hm⟩ := hm
  obtain ⟨rfl, hsx, htx, hty⟩ := r.exit_geometry hs htx (players_adjacent hm)
  cases hm with
  | walk _ ha _ he _ =>
    have hempty : t.player ∈ holes s := (mem_holes _).mpr he
    have haux := r.outside_hole_source hr t.player (by intro hi; have := hi.1; omega) hempty
    have hentry := r.auxiliary_on_source_row t.player haux (by have := hs.2; omega)
    refine ⟨?_, hentry ▸ hempty⟩
    apply Prod.ext <;> apply Fin.ext
    · exact hsx
    · have hy := congrArg (fun q => q.2.val) hentry
      exact hty.symm.trans hy
  | @push n _ hn _ run hp hb =>
    let q := run.cell ⟨n + 1, by omega⟩
    have hpos := run.position ⟨n + 1, by omega⟩
    have hlane := run.lane ⟨n + 1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpos hlane
    have hqx : q.1.val ≤ 0 := by dsimp [q]; omega
    have hqy : q.2.val < r.height := by dsimp [q]; have := hs.2; omega
    have haux := r.outside_hole_source hr q (by intro hi; have := hi.1; omega)
      ((mem_holes _).mpr run.empty)
    have he := r.auxiliary_on_source_row q haux hqy
    have := congrArg (fun q => q.1.val) he
    change q.1.val = 1 at this
    omega

private instance (q : Cell r.outputWidth r.outputHeight) : Decidable (r.InsideCell q) :=
  inferInstanceAs (Decidable (2 ≤ q.1.val ∧ q.2.val < r.height))

private instance (s : PushFS.State r.outputWidth r.outputHeight) : Decidable (r.Inside s) :=
  inferInstanceAs (Decidable (2 ≤ s.player.1.val ∧ s.player.2.val < r.height))

/-- The exact original source bitmap, with its goal as the outside-player placeholder. -/
def cropState (s : PushFS.State r.outputWidth r.outputHeight) : PushFS.State r.width r.height :=
  ⟨if hi : 2 ≤ s.player.1.val ∧ s.player.2.val < r.height then
    (⟨s.player.1.val - 2, by have := s.player.1.isLt; dsimp [outputWidth] at this; have := hi.1; omega⟩,
      ⟨s.player.2.val, hi.2⟩)
  else r.sourceGoal, Finset.univ.filter fun q => r.embed q ∈ s.boxes⟩

private theorem crop_player {s : PushFS.State r.outputWidth r.outputHeight} (hs : r.Inside s) :
    r.embed (r.cropState s).player = s.player := by
  change 2 ≤ s.player.1.val ∧ s.player.2.val < r.height at hs
  simp only [cropState, dite_eq_left hs]
  apply Prod.ext <;> apply Fin.ext
  · change s.player.1.val - 2 + 2 = s.player.1.val
    have := hs.1
    omega
  · rfl

private theorem crop_boxes (s : PushFS.State r.outputWidth r.outputHeight) (q : Cell r.width r.height) :
    q ∈ (r.cropState s).boxes ↔ r.embed q ∈ s.boxes := by
  simp only [cropState, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem crop_initial : r.cropState (r.extend r.initial).toState = r.initial.toState := by
  apply State.ext
  · apply r.embed_injective
    exact r.crop_player r.initial_inside
  · ext q
    rw [r.crop_boxes]
    change r.embed q ∈ (r.extend r.initial).emptyᶜ ↔ q ∈ r.initial.emptyᶜ
    simp only [Finset.mem_compl, r.embed_mem_extend]

private theorem crop_valid {s : PushFS.State r.outputWidth r.outputHeight}
    (hs : r.Inside s) (hv : @State.Valid r.outputWidth r.outputHeight r.compile.board s) :
    @State.Valid r.width r.height r.source.board (r.cropState s) := by
  refine ⟨by exact Finset.notMem_empty _, Finset.disjoint_empty_right _, ?_⟩
  intro hbox
  have hphys := (r.crop_boxes s _).mp hbox
  rw [r.crop_player hs] at hphys
  exact hv.2.2 hphys

private theorem inside_convex : Support.AxisConvex {q : Cell r.outputWidth r.outputHeight | r.InsideCell q} := by
  intro d a b q ha hb hl hq hlo hhi
  obtain ⟨hax, hay⟩ := ha
  obtain ⟨hbx, hby⟩ := hb
  change 2 ≤ q.1.val ∧ q.2.val < r.height
  cases d <;> simp only [Direction.position, Direction.lane] at hl hq hlo hhi <;> omega

private theorem run_inside {s t : PushFS.State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s) (hs : r.Inside s)
    (run : @Run r.outputWidth r.outputHeight r.compile.board d s n) (hb : t.boxes =
      insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (he : r.entry ∈ holes t) : ∀ i, r.InsideCell (run.cell i) := by
  apply r.inside_convex.run run hs
  by_contra hout
  let q := run.cell ⟨n + 1, by omega⟩
  have haux := r.outside_hole_source hr q hout ((mem_holes _).mpr run.empty)
  have hqe : q = r.entry := by
    rcases Finset.mem_insert.mp haux with hh | hh
    · exact hh
    · have hlow := (Finset.mem_filter.mp hh).2
      have hlane := run.lane ⟨n + 1, by omega⟩
      rcases hs with ⟨hsx, hsy⟩
      cases d <;> simp only [Direction.lane] at hlane <;> dsimp [q] at hlow <;> omega
  exact (mem_holes _).mp he (by rw [hb, ← hqe]; exact Finset.mem_insert_self _ _)

private theorem embed_adjacent (d : Direction) (p q : Cell r.width r.height) :
    Adjacent d (r.embed p) (r.embed q) ↔ Adjacent d p q := by
  cases d <;> simp only [Adjacent, embed, Fin.ext_iff] <;> omega

private theorem crop_move {s t : PushFS.State r.outputWidth r.outputHeight} {d : Direction}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s) (hs : r.Inside s) (ht : r.Inside t)
    (hm : @Move r.outputWidth r.outputHeight r.compile.board none d s t) (he : r.entry ∈ holes t) :
    @Move r.width r.height r.source.board none d (r.cropState s) (r.cropState t) := by
  cases hm with
  | walk hv ha _ hempty hb =>
    refine .walk (r.crop_valid hs hv) ?_ (Finset.notMem_empty _) ?_ ?_
    · apply (r.embed_adjacent d _ _).mp
      simpa only [r.crop_player hs, r.crop_player ht] using ha
    · exact fun hh => hempty (by simpa only [r.crop_player ht] using (r.crop_boxes s _).mp hh)
    · ext p
      simp only [r.crop_boxes, hb]
  | @push n hv hn hc run hp hb =>
    have hin := r.run_inside hr hs run hb he
    let cell (i : Fin (n + 2)) : Cell r.width r.height :=
      (⟨(run.cell i).1.val - 2, by
        have hw : (run.cell i).1.val < r.width + 2 := (run.cell i).1.isLt
        have hx : 2 ≤ (run.cell i).1.val := (hin i).1
        omega⟩, ⟨(run.cell i).2.val, (hin i).2⟩)
    have hcell (i : Fin (n + 2)) : r.embed (cell i) = run.cell i := by
      apply Prod.ext <;> apply Fin.ext
      · change (run.cell i).1.val - 2 + 2 = (run.cell i).1.val
        have := (hin i).1
        omega
      · rfl
    let small : @Run r.width r.height r.source.board d (r.cropState s) n := {
      cell := cell
      start := r.embed_injective ((hcell 0).trans (run.start.trans (r.crop_player hs).symm))
      adjacent := fun i => (r.embed_adjacent d _ _).mp (by simpa only [hcell] using run.adjacent i)
      occupied := fun i => (r.crop_boxes s _).mpr (by rw [hcell]; exact run.occupied i)
      empty := fun hh => run.empty (by simpa only [hcell] using (r.crop_boxes s _).mp hh)
      floor := fun _ => Finset.notMem_empty _ }
    refine .push (r.crop_valid hs hv) hn hc small ?_ ?_
    · exact r.embed_injective ((r.crop_player ht).trans (hp.trans (hcell 1).symm))
    · ext p
      simp only [r.crop_boxes, Finset.mem_insert, Finset.mem_erase]
      change (r.embed p ∈ t.boxes) ↔ p = cell _ ∨ p ≠ cell 1 ∧ r.embed p ∈ s.boxes
      rw [hb]
      simp only [Finset.mem_insert, Finset.mem_erase, ← hcell, Ne, r.embed_injective.eq_iff]

private theorem crop_reachable {s : PushFS.State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.InsideStep (r.extend r.initial).toState s) (he : r.entry ∈ holes s) :
    @Reachable r.width r.height r.source.board none r.initial.toState (r.cropState s) := by
  revert he
  induction hr with
  | refl =>
    intro _
    simpa only [r.crop_initial] using (Relation.ReflTransGen.refl :
      @Reachable r.width r.height r.source.board none r.initial.toState r.initial.toState)
  | @tail u v hprefix hm ih =>
    intro he
    have hne : r.entry ≠ v.player := by
      intro hh
      have := hm.2.1
      rw [← hh] at this
      change 2 ≤ 1 at this
      omega
    have he' := hole_source_of_ne_player hm.1.choose_spec hne he
    exact (ih he').tail ⟨hm.1.choose,
      r.crop_move hprefix (r.prefix_inside hprefix) hm.2 hm.1.choose_spec he⟩

/-- Every successful physical dock trajectory reaches the original left-boundary player goal first. -/
private theorem source_solvable_of_compile (hs : r.compile.Solvable) : r.source.Solvable := by
  change ∃ finish : PushFS.State r.outputWidth r.outputHeight,
    @Reachable r.outputWidth r.outputHeight r.compile.board none
      (r.extend r.initial).toState finish ∧ finish.player = r.target at hs
  obtain ⟨finish, hr, ht⟩ := hs
  obtain ⟨s, t, hprefix, hsin, hmove, htout, _⟩ := Path.first_exit hr r.initial_inside (by
    intro hin
    have := hin.1
    rw [ht] at this
    change 2 ≤ 0 at this
    omega)
  obtain ⟨hgoal, hentry⟩ := r.first_exit_goal hprefix hsin hmove htout
  refine ⟨r.cropState s, r.crop_reachable hprefix hentry, ?_⟩
  apply r.embed_injective
  exact (r.crop_player hsin).trans hgoal

/-- The southwest dock preserves ordinary player-goal solvability in both directions. -/
theorem compile_solvable_iff : r.compile.Solvable ↔ r.source.Solvable :=
  ⟨r.source_solvable_of_compile, r.compile_solvable_of_source⟩

end PushPuzzle.Push.CornerDock.Input
