/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockReverse
import all Push.CornerDockReverse

/-! A dock solution retains the actual source prefix and its exact bitmap, for cyclic reader composition. -/

@[expose] public section
namespace PushPuzzle.Push.CornerDock.Input

open PushFS PushS

variable (r : Input)

/-- The complete source rectangle inside the dock. -/
def SourceInside (s : State r.outputWidth r.outputHeight) : Prop :=
  2 ≤ s.player.1.val ∧ s.player.2.val < r.height

/-- A real dock step still inside its original source. -/
def SourceStep (s t : State r.outputWidth r.outputHeight) : Prop :=
  Step r.compile.board none s t ∧ r.SourceInside t

/-- Crop the exact source boxes, with the old goal as the outside-player placeholder. -/
def sourceState (s : State r.outputWidth r.outputHeight) : State r.width r.height := r.cropState s

theorem sourceInside_prefix {s : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.SourceStep r.compile.initial s) : r.SourceInside s :=
  r.prefix_inside hr

theorem sourceState_initial : r.sourceState r.compile.initial = r.initial.toState := r.crop_initial

theorem sourceState_hole (s : State r.outputWidth r.outputHeight) (q : Cell r.width r.height) :
    q ∈ holes (r.sourceState s) ↔ r.embed q ∈ holes s := by
  simp only [mem_holes, sourceState, r.crop_boxes]

/-- Cropping preserves the number of holes in each actual source-column prefix. -/
theorem sourceState_column_card (s : State r.outputWidth r.outputHeight) (x cutoff : ℕ)
    (hx : x < r.width) (hc : cutoff ≤ r.height) :
    ((holes (r.sourceState s)).filter fun q => q.1.val = x ∧ q.2.val < cutoff).card =
      ((holes s).filter fun q => q.1.val = x + 2 ∧ q.2.val < cutoff).card := by
  have heq : (((holes (r.sourceState s)).filter fun q => q.1.val = x ∧ q.2.val < cutoff).image r.embed) =
      ((holes s).filter fun q => q.1.val = x + 2 ∧ q.2.val < cutoff) := by
    ext q
    constructor
    · intro hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha, hax, hay⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨(r.sourceState_hole s a).mp ha, by change a.1.val + 2 = x + 2; omega, hay⟩
    · intro hq
      obtain ⟨hq, hqx, hqy⟩ := Finset.mem_filter.mp hq
      let a : Cell r.width r.height := (⟨x, hx⟩, ⟨q.2.val, hqy.trans_le hc⟩)
      have he : r.embed a = q := by
        apply Prod.ext <;> apply Fin.ext
        · exact hqx.symm
        · rfl
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
        ⟨(r.sourceState_hole s a).mpr (he.symm ▸ hq), rfl, hqy⟩, he⟩
  rw [← heq, Finset.card_image_of_injective _ r.embed_injective]

theorem sourceState_player {s : State r.outputWidth r.outputHeight} (hs : r.SourceInside s) :
    r.embed (r.sourceState s).player = s.player := r.crop_player hs

/-- The dock entry remains empty throughout a preceding path that stays in the source. -/
theorem entry_hole_source {s t : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.SourceStep s t) (he : r.entry ∈ holes t) : r.entry ∈ holes s := by
  induction hr with
  | refl => exact he
  | @tail u v hsu hm ih =>
    have hne : r.entry ≠ v.player := by
      intro hh
      have hx := hm.2.1
      rw [← hh] at hx
      change 2 ≤ 1 at hx
      omega
    exact ih (hole_source_of_ne_player hm.1.choose_spec hne he)

/-- A real pre-exit dock step crops to its precise original complete source step. -/
theorem sourceState_step {s t : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (hm : r.SourceStep s t) (he : r.entry ∈ holes t) :
    Step r.source.board none (r.sourceState s) (r.sourceState t) :=
  ⟨hm.1.choose, r.crop_move hr (r.prefix_inside hr) hm.2 hm.1.choose_spec he⟩

/-- Crop any chosen segment of the same pre-exit physical source trace. -/
theorem sourceState_between {s t : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (hr : Relation.ReflTransGen r.SourceStep s t) (he : r.entry ∈ holes t) :
    Reachable r.source.board none (r.sourceState s) (r.sourceState t) := by
  have hpath : Relation.ReflTransGen (fun a b =>
      Step r.source.board none (r.sourceState a) (r.sourceState b)) s t := by
    apply Path.enrich hr
    intro a b hsa hm hbt
    exact r.sourceState_step (hpre.trans hsa) hm (r.entry_hole_source hbt he)
  exact hpath.lift r.sourceState (fun _ _ h => h)

/-- Crop a chosen source prefix while retaining any additional endpoint predicate. -/
theorem sourceState_prefix_keeping {P : State r.width r.height → Prop}
    {t : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (fun a b => r.SourceStep a b ∧ P (r.sourceState b))
      r.compile.initial t) (he : r.entry ∈ holes t) :
    Relation.ReflTransGen (fun a b => Step r.source.board none a b ∧ P b)
      r.initial.toState (r.sourceState t) := by
  have hpath : Relation.ReflTransGen (fun a b =>
      Step r.source.board none (r.sourceState a) (r.sourceState b) ∧ P (r.sourceState b))
      r.compile.initial t := by
    apply Path.enrich hr
    intro a b hsa hm hbt
    have hpre := Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hsa
    have hpost := Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbt
    exact ⟨r.sourceState_step hpre hm.1 (r.entry_hole_source hpost he), hm.2⟩
  have hmapped : Relation.ReflTransGen (fun a b => Step r.source.board none a b ∧ P b)
      (r.sourceState r.compile.initial) (r.sourceState t) :=
    hpath.lift r.sourceState (fun _ _ h => h)
  rwa [r.sourceState_initial] at hmapped

/-- A successful dock trace contains an exact source goal prefix and its matching source bitmap. -/
structure GoalPrefix (finish : State r.outputWidth r.outputHeight) where
  state : State r.outputWidth r.outputHeight
  before : Relation.ReflTransGen r.SourceStep r.compile.initial state
  after : Reachable r.compile.board none state finish
  player : state.player = r.embed r.sourceGoal
  entry_empty : r.entry ∈ holes state
  reachable : Reachable r.source.board none r.initial.toState (r.sourceState state)

theorem goalPrefix {finish : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.board none r.compile.initial finish) (ht : finish.player = r.target) :
    Nonempty (r.GoalPrefix finish) := by
  obtain ⟨s, t, hprefix, hsin, hmove, htout, htf⟩ := Path.first_exit
    (α := State r.outputWidth r.outputHeight) hr r.initial_inside (by
      intro hin
      have := hin.1
      rw [ht] at this
      change 2 ≤ 0 at this
      omega)
  obtain ⟨hgoal, hentry⟩ := r.first_exit_goal hprefix hsin hmove htout
  exact ⟨⟨s, hprefix, (Relation.ReflTransGen.single hmove).trans htf,
    hgoal, hentry, r.crop_reachable hprefix hentry⟩⟩

end PushPuzzle.Push.CornerDock.Input
