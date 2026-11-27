/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.CyclicSourceLift
public import PushPush.DockForward
public import PushPush.ColumnReaderStatic
public import Push.CyclicPeelingCompletenessDock
import all Push.CyclicPeelingCompletenessDock
import all Push.CornerDockReverse

/-! Exact selected source remainders have complete maximum-sliding cyclic executions. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell State)
open Push.Cyclic

private def ReaderFinish (I : Push.Instance) (w h : ℕ) (E : Finset (Cell w h)) : Prop :=
  ∃ t : State I.width I.height, ReadPath I.initial t ∧ t.player = I.target ∧
    (∀ p : Cell w h, p ∈ E ↔ ∃ q ∈ PushS.holes t, q.1.val = p.1.val ∧ q.2.val = p.2.val) ∧
    (∀ q : Cell I.width I.height, w < q.1.val → h ≤ q.2.val → q ∈ PushS.holes t) ∧
    ∀ q ∈ PushS.holes t, q.2.val < h → q.1.val < w

private theorem readerFinish (r : Push.ColumnScan.Input) {E : Finset (Cell r.width r.height)}
    (hcorner : r.initial.player = r.sourceCorner)
    (H : WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas)) r.initial.empty E) :
    ReaderFinish r.compile r.width r.height E := by
  obtain ⟨t, hr, hp, hmap, hroom, hsupport⟩ := ColumnReader.compile_loose_frame r hcorner H
  refine ⟨t, hr, hp, ?_, ?_, hsupport⟩
  · intro p
    constructor
    · intro hp
      exact ⟨r.embed p, (hmap p).mpr hp, rfl, rfl⟩
    · rintro ⟨q, hq, hx, hy⟩
      exact (hmap p).mp ((Prod.ext (Fin.ext hx) (Fin.ext hy) : q = r.embed p) ▸ hq)
  · intro q hx hy
    exact hroom (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy⟩)

private theorem read_live (r : Push.ColumnScan.Input) {s : State r.width r.height}
    (hcard : (PushS.holes s).card = r.initial.empty.card) (hv : s.player ∉ s.boxes)
    (hp : s.player = r.sourceCorner) {E : Finset (Cell r.width r.height)}
    (H : WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas)) (PushS.holes s) E) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath (r.liftState s) t ∧ t.player = r.target ∧
      (∀ p : Cell r.width r.height, r.embed p ∈ PushS.holes t ↔ p ∈ E) ∧
      r.room ⊆ PushS.holes t ∧ ∀ q ∈ PushS.holes t, q.2.val < r.height → q.1.val < r.width := by
  let U : PushS.HoleState r.width r.height := ⟨s.player, PushS.holes s, Finset.mem_compl.mpr hv⟩
  have hU : U.toState = s := by
    apply State.ext
    · rfl
    · simp only [PushS.HoleState.toState, U, PushS.holes, compl_compl]
  have hf : ReaderFinish (r.withInitial U hcard).compile r.width r.height E :=
    readerFinish (r.withInitial U hcard) hp H
  rw [r.withInitial_compile U hcard] at hf
  obtain ⟨t, ht, htp, hmap, hroom, hsupport⟩ := hf
  change ReadPath (r.liftState U.toState) t at ht
  rw [hU] at ht
  refine ⟨t, ht, htp, ?_, ?_, hsupport⟩
  · intro p
    constructor
    · intro hh
      exact (hmap p).mpr ⟨r.embed p, hh, rfl, rfl⟩
    · intro hh
      obtain ⟨q, hq, hx, hy⟩ := (hmap p).mp hh
      exact (Prod.ext (Fin.ext hx) (Fin.ext hy) : q = r.embed p) ▸ hq
  · intro q hq
    obtain ⟨_, hx, hy⟩ := Finset.mem_filter.mp hq
    exact hroom q hx hy

/-- The canonical dock bitmap together with its genuine maximum-sliding computation. -/
structure CanonicalDock (r : Push.ColumnScan.Input) (E : Finset (Cell r.width r.height))
    extends Push.Cyclic.CanonicalDock r E where
  actual : Reachable (dock r).compile.initial state.toState

theorem canonical_dock (r : Push.ColumnScan.Input) {s : State r.width r.height}
    (hr : Reachable r.initial.toState s) (hp : s.player = r.sourceCorner)
    {E : Finset (Cell r.width r.height)}
    (H : WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas)) (PushS.holes s) E) :
    Nonempty (CanonicalDock r E) := by
  have hv := hr.valid (Finset.notMem_compl.mpr r.initial.player_empty)
  have hc : (PushS.holes s).card = r.initial.empty.card := by
    have hb := hr.card_boxes
    change s.boxes.card = r.initial.emptyᶜ.card at hb
    simp only [PushS.holes, Finset.card_compl] at hb ⊢
    have := Finset.card_le_univ s.boxes
    have := Finset.card_le_univ r.initial.empty
    omega
  obtain ⟨u, hread, hup, hE, hroom, hsupport⟩ := read_live (wideReader r) hc hv hp H
  have htcorner : r.sourceCorner ∉ s.boxes := hp ▸ hv
  have hprefix := sourceLift_reachable r hr htcorner
  rw [sourceLift_initial] at hprefix
  have hreader := hprefix.trans (CornerDock.lift_readPath (dock r) hread)
  let U : PushS.HoleState (dock r).width (dock r).height :=
    ⟨u.player, PushS.holes u, Finset.mem_compl.mpr (hread.valid (by
      intro hh
      exact hv (((wideReader r).liftState_mem_boxes s _).mp hh)))⟩
  have hU : U.toState = u := by
    apply State.ext
    · rfl
    · simp only [PushS.HoleState.toState, U, PushS.holes, compl_compl]
  obtain ⟨a, ha, hap, hready⟩ := CornerDock.goal_to_ready (dock r) U hup
  have hlift : (dock r).liftState u = ((dock r).extend U).toState := by
    rw [← hU]
    exact (dock r).liftState_toState U
  have hactual := hreader.trans (hlift.symm ▸ ha)
  have hordinary := Reachable.unit_expansion hactual (dock r).compile.board rfl
  have hready' : Push.CornerDock.Backup.Ready (dock r) u a := hU ▸ hready
  refine ⟨{
    state := a
    reachable := hordinary
    player := hap
    data := ?_
    sourceRows := dock_data_support r u hsupport a hordinary hready'
    southern := ?_
    stock := dock_room_stock r u a hready' hroom
    actual := hactual
  }⟩
  · ext p
    simp only [sourceData, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hready'.source ((wideReader r).embed p)).trans (hE p)
  · intro q hq hy
    have hh := (dock r).hole_support hordinary q (a.holes_toState.symm ▸ hq)
    change q.1.val < 2 ∨ q.2.val < (wideReader r).outputHeight at hh
    omega

end PushPuzzle.PushPush.Cyclic
