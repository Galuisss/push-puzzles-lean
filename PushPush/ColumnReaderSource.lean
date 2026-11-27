/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderCrop
public import Push.ColumnScanSoundness

/-! A successful maximum-sliding reader retains a genuine maximum-sliding source prefix. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)
open Push.StripFrontier

variable (r : Push.ColumnScan.Input)

/-- The committed landing and its exact source bitmap, reachable with maximum slides. -/
structure SourceWitness (finish : State r.outputWidth r.outputHeight) where
  state : State r.outputWidth r.outputHeight
  before : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
    r.initialState.toState state
  landing : state.player = r.landing
  suffix : PushFS.Reachable r.compile.board none state finish
  source : Reachable r.initial.toState (r.cropState state)
  tailState : State r.outputWidth r.outputHeight
  tailPath : Reachable tailState finish
  bridge : PushFS.Reachable r.compile.board none state tailState
  tailCrop : r.cropState tailState = r.cropState state

private theorem outside_exit_witness {s t finish : State r.outputWidth r.outputHeight}
    {d : PushFS.Direction} {n k : ℕ} (slide : Slide d s n k)
    (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (hp : t.player = slide.cell ⟨1, by omega⟩) (hb : t.boxes = slide.boxes)
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (hsource : Reachable r.initial.toState (r.cropState s))
    (htfMax : Reachable t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : ¬r.SourceInside s) (j : Fin (k + 1))
    (hbad : ¬ North r.width r.targetLevel (slide.stage j)) : Nonempty (SourceWitness r finish) := by
  have htf := htfMax.unit_expansion r.compile.board rfl
  have hcrop := hsource.valid (Finset.notMem_compl.mpr r.initial.player_empty)
  have hout := outside_slide_avoids r slide hn hk hv hp hb hpre htf hfx hfy hs hcrop
  let R := fun u v : State r.outputWidth r.outputHeight =>
    PushFS.Step r.compile.board none u v ∧ r.cropState v = r.cropState s
  have hstage (i : Fin (k + 1)) : Relation.ReflTransGen R (slide.stage 0) (slide.stage i) := by
    induction i using Fin.induction with
    | zero => exact .refl
    | succ i ih => exact ih.tail ⟨⟨d, slide.stage_move hn hv i r.compile.board.goals⟩,
        crop_stage r slide hs hout i.succ⟩
  have hpath : Relation.ReflTransGen R s (slide.stage j) := by
    simpa only [slide.stage_zero] using hstage j
  have hN := reachable_north hpre (r.initial_north r.width)
  obtain ⟨a, b, hab, _, habStep, hbSouth, hbj⟩ := Push.Path.first_exit hpath hN hbad
  have hcropa : r.cropState a = r.cropState s := by
    induction hab with
    | refl => rfl
    | tail _ hm _ => exact hm.1.2
  have hprea := hpre.trans (Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm.1.1, hm.2⟩) _ _ hab)
  have hend : (⟨slide.cell ⟨1, by omega⟩, slide.boxes⟩ : State _ _) = t := State.ext hp.symm hb.symm
  have hjt : PushFS.Reachable r.compile.board none (slide.stage j) t :=
    hend ▸ slide.stage_finish hn hk hv r.compile.board.goals j
  have hbt := (Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hbj).trans hjt
  have hbf := hbt.trans htf
  have hbS : b.player.1.val < r.width ∧ r.targetLevel ≤ b.player.2.val := by
    simpa only [North, not_imp, not_lt] using hbSouth
  have hland := r.first_south_landing hprea habStep.1 hbS hbf hfx hfy
  refine ⟨{
    state := a
    before := hprea
    landing := hland
    suffix := (Relation.ReflTransGen.single habStep.1).trans hbf
    source := by simpa only [hcropa] using hsource
    tailState := t
    tailPath := htfMax
    bridge := (Relation.ReflTransGen.single habStep.1).trans hbt
    tailCrop := ?_
  }⟩
  exact (outside_push_crop r slide hn hk hv hp hb hpre htf hfx hfy hs hcrop).trans hcropa.symm

private theorem process_move {s t finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s)
    (hsource : Reachable r.initial.toState (r.cropState s)) (hm : Step s t)
    (htfMax : Reachable t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    Nonempty (SourceWitness r finish) ∨
      (Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
        r.initialState.toState t ∧ Reachable r.initial.toState (r.cropState t)) := by
  classical
  have htf := htfMax.unit_expansion r.compile.board rfl
  have hcrop := hsource.valid (Finset.notMem_compl.mpr r.initial.player_empty)
  obtain ⟨d, hm⟩ := hm
  cases hm with
  | walk hv ha he hb =>
    have hm0 : PushFS.Step r.compile.board none s t := ⟨d, .walk
      ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩ ha (Finset.notMem_empty _) he hb⟩
    by_cases htN : North r.width r.targetLevel t
    · right
      refine ⟨hpre.tail ⟨hm0, htN⟩, ?_⟩
      rcases step_crop r hpre ⟨d, .walk hv ha he hb⟩ htN htf hfx hfy hcrop with heq | hstep
      · simpa only [heq] using hsource
      · exact hsource.tail hstep
    · left
      have htS : t.player.1.val < r.width ∧ r.targetLevel ≤ t.player.2.val := by
        simpa only [North, not_imp, not_lt] using htN
      exact ⟨{
        state := s
        before := hpre
        landing := r.first_south_landing hpre hm0 htS htf hfx hfy
        suffix := (Relation.ReflTransGen.single hm0).trans htf
        source := hsource
        tailState := s
        tailPath := (Relation.ReflTransGen.single ⟨d, Move.walk hv ha he hb⟩).trans htfMax
        bridge := .refl
        tailCrop := rfl
      }⟩
  | @push n k hv hn hk slide hp hb =>
    by_cases hs : r.SourceInside s
    · right
      have hin := inside_slide r slide hn hk hv hp hb hpre htf hfx hfy hs
      exact ⟨hpre.trans (inside_slide_north r slide hn hk hv hp hb hpre htf hfx hfy hs),
        hsource.tail ⟨d, crop_push r slide hn hk hv hp hb hin⟩⟩
    · by_cases hall : ∀ j : Fin (k + 1), North r.width r.targetLevel (slide.stage j)
      · right
        have hr := slide.unit_expansion_player_prefix hn hk hv r.compile.board.goals
          (fun p => p.1.val < r.width → p.2.val < r.targetLevel) hall
        have he : (⟨slide.cell ⟨1, by omega⟩, slide.boxes⟩ : State _ _) = t := State.ext hp.symm hb.symm
        refine ⟨hpre.trans (he ▸ hr), ?_⟩
        have hc := outside_push_crop r slide hn hk hv hp hb hpre htf hfx hfy hs hcrop
        simpa only [hc] using hsource
      · left
        obtain ⟨j, hj⟩ := not_forall.mp hall
        exact outside_exit_witness r slide hn hk hv hp hb hpre hsource htfMax hfx hfy hs j hj

/-- Every successful maximum-sliding reader has a landing witness with a maximum-sliding source path. -/
theorem source_witness {finish : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.initial finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    Nonempty (SourceWitness r finish) := by
  have track {u : State r.outputWidth r.outputHeight} (hu : Reachable r.compile.initial u) :
      Reachable u finish → Nonempty (SourceWitness r finish) ∨
        (Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
          r.initialState.toState u ∧ Reachable r.initial.toState (r.cropState u)) := by
    induction hu with
    | refl =>
      intro _
      right
      refine ⟨.refl, ?_⟩
      rw [show r.cropState r.compile.initial = r.initial.toState from r.cropState_initial]
    | tail _ hm ih =>
      intro huf
      have hprev := (Relation.ReflTransGen.single hm).trans huf
      rcases ih hprev with hw | ⟨hpre, hsource⟩
      · exact Or.inl hw
      · exact process_move r hpre hsource hm huf hfx hfy
  rcases track hr .refl with hw | ⟨hpre, _⟩
  · exact hw
  · have hN := reachable_north hpre (r.initial_north r.width)
    have hx : finish.player.1.val < r.width := by rw [hfx]; exact r.width_pos
    exact False.elim (by have := hN hx; omega)

/-- A maximum-sliding solution witnesses all column quotas in one reachable source corner state. -/
theorem source_corner_quotas {finish : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.initial finish) (hp : finish.player = r.target) :
    ∃ s : State r.width r.height, Reachable r.initial.toState s ∧ s.player = r.sourceCorner ∧
      ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (s.boxesᶜ.filter fun p => p.1 = i).card := by
  have hfx : finish.player.1.val = 0 := congrArg (fun q => q.1.val) hp
  have hfy : finish.player.2.val = r.targetLevel := congrArg (fun q => q.2.val) hp
  obtain ⟨w⟩ := source_witness r hr hfx hfy.ge
  refine ⟨r.cropState w.state, w.source, ?_, ?_⟩
  · apply r.cropPlayer_outside
    intro hs
    have hx := hs.1
    rw [w.landing] at hx
    change r.width < r.width at hx
    omega
  · intro i
    have hq := r.landing_column_quotas w.before w.suffix hfx hfy w.landing i
    rwa [r.crop_column_card w.state i] at hq

end PushPuzzle.PushPush.ColumnReader
