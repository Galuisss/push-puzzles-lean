/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicInventory
public import Push.ColumnScanForwardExact
public import Push.ColumnScanSourceLiftComplete
import all Push.ColumnScanForwardExact

/-! Run the first exact reader after an arbitrary real source computation. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private def ReaderFinish (I : Push.Instance) (w h : ℕ) (E : Finset (Cell w h)) : Prop :=
  ∃ t : State I.width I.height,
    Reachable I.board none I.initial t ∧ t.player = I.target ∧
    (∀ p : Cell w h, p ∈ E ↔ ∃ q ∈ holes t, q.1.val = p.1.val ∧ q.2.val = p.2.val) ∧
    (∀ q : Cell I.width I.height, w < q.1.val → h ≤ q.2.val → q ∈ holes t) ∧
    ∀ q ∈ holes t, q.2.val < h → q.1.val < w

private theorem readerFinish (r : ColumnScan.Input) {E : Finset (Cell r.width r.height)}
    (hcorner : r.initial.player = r.sourceCorner)
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) r.initial.empty = some E) :
    ReaderFinish r.compile r.width r.height E := by
  unfold ReaderFinish
  dsimp only [ColumnScan.Input.compile]
  have hquotas (i : Fin r.width) : r.quotas.getD i.val 0 ≤ (r.columnSources i).card := by
    have h := r.static_columns_card heval i
    omega
  obtain ⟨t, hr, ht, hroom, hread, hsupport⟩ := r.compile_run_exact_source_supported hcorner hquotas
  have hE : r.sourceHolesAt t = E := Option.some.inj (hread.symm.trans heval)
  refine ⟨t.toState, hr, ht, ?_, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have hh : r.embed p ∈ t.empty := (r.mem_sourceHolesAt t p).mp (hE ▸ hp)
      refine ⟨r.embed p, ?_, rfl, rfl⟩
      change r.embed p ∈ t.emptyᶜᶜ
      rw [compl_compl]
      exact hh
    · rintro ⟨q, hq, hx, hy⟩
      have he : q = r.embed p := Prod.ext (Fin.ext hx) (Fin.ext hy)
      apply hE ▸ (r.mem_sourceHolesAt t p).mpr
      have hh : q ∈ t.empty := by
        change q ∈ t.emptyᶜᶜ at hq
        rwa [compl_compl] at hq
      exact he ▸ hh
  · intro q hx hy
    rw [HoleState.holes_toState]
    exact hroom (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy⟩)
  · intro q hq hy
    apply hsupport q _ hy
    change q ∈ t.emptyᶜᶜ at hq
    rwa [compl_compl] at hq

/-- Replay the live source prefix, then realize its exact static first-round remainder and retain every room hole. -/
theorem first_round_exact_supported (r : ColumnScan.Input) {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hcorner : s.player = r.sourceCorner) {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E) :
    ∃ t : State r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t ∧ t.player = r.target ∧
      (∀ p : Cell r.width r.height, r.embed p ∈ holes t ↔ p ∈ E) ∧ r.room ⊆ holes t ∧
      ∀ q ∈ holes t, q.2.val < r.height → q.1.val < r.width := by
  have hv := hr.valid (r.initial.valid r.sourceBoard rfl)
  let U : HoleState r.width r.height := ⟨s.player, holes s, player_mem_holes hv⟩
  have hU : U.toState = s := by
    apply State.ext
    · rfl
    · simp only [HoleState.toState, U, holes, compl_compl]
  have hcard : U.empty.card = r.initial.empty.card := by
    change (holes s).card = r.initial.empty.card
    rw [card_holes_reachable hr, r.initial.holes_toState]
  have hfinish : ReaderFinish (r.withInitial U hcard).compile r.width r.height E :=
    readerFinish (r.withInitial U hcard) hcorner heval
  rw [r.withInitial_compile U hcard] at hfinish
  obtain ⟨t, ht, hp, hmap, hroom, hsupport⟩ := hfinish
  have hprefix : Reachable r.compile.board none r.compile.initial (r.liftState U.toState) := by
    rw [hU]
    exact r.lift_source_initial_reachable hr
  refine ⟨t, hprefix.trans (ht.reboard rfl), hp, ?_, ?_, hsupport⟩
  · intro p
    constructor
    · intro hh
      exact (hmap p).mpr ⟨r.embed p, hh, rfl, rfl⟩
    · intro hp
      obtain ⟨q, hq, hx, hy⟩ := (hmap p).mp hp
      exact (Prod.ext (Fin.ext hx) (Fin.ext hy) : q = r.embed p) ▸ hq
  · intro q hq
    obtain ⟨_, hx, hy⟩ := Finset.mem_filter.mp hq
    exact hroom q hx hy

/-- Replay the source prefix and exact canonical reader, retaining the full eastern room. -/
theorem first_round_exact (r : ColumnScan.Input) {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hcorner : s.player = r.sourceCorner) {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E) :
    ∃ t : State r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t ∧ t.player = r.target ∧
      (∀ p : Cell r.width r.height, r.embed p ∈ holes t ↔ p ∈ E) ∧ r.room ⊆ holes t := by
  obtain ⟨t, ht, hp, hE, hroom, _⟩ := first_round_exact_supported r hr hcorner heval
  exact ⟨t, ht, hp, hE, hroom⟩

end PushPuzzle.Push.Cyclic
