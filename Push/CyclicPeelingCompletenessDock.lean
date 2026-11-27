/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicTwoRoundCompletenessReader
public import Push.CornerDockBackupCanonical
public import Push.CyclicStaticSuffix
public import Push.CyclicNorthwest
import all Push.CyclicInventory
import all Push.CornerDockReverse

/-! The exact canonical dock bitmap supplies both source data and independent cleanup inventory. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS CornerDock.Backup

/-- A concrete canonical dock endpoint with exact data, supported auxiliaries, and payable row cleanup. -/
structure CanonicalDock (r : ColumnScan.Input) (E : Finset (Cell r.width r.height)) where
  state : HoleState (dock r).outputWidth (dock r).outputHeight
  reachable : Reachable (dock r).compile.board none (dock r).compile.initial state.toState
  player : state.player = (dock r).target
  data : sourceData r state.empty = E
  sourceRows : ∀ q ∈ state.empty, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2
  southern : ∀ q ∈ state.empty, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2
  stock : ∀ row ∈ auxiliaryRows r, r.width + 2 ≤ (state.empty.filter fun q => q.2.val = row).card

private theorem dock_data_support (r : ColumnScan.Input)
    (source : State (dock r).width (dock r).height)
    (hs : ∀ q ∈ holes source, q.2.val < r.height → q.1.val < r.width)
    (a : HoleState (dock r).outputWidth (dock r).outputHeight)
    (ha : Reachable (dock r).compile.board none (dock r).compile.initial a.toState)
    (hready : Ready (dock r) source a) :
    ∀ q ∈ a.empty, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2 := by
  intro q hq hy
  have hlevel := (wideReader r).targetLevel_lower
  have hx : 2 ≤ q.1.val := by
    by_contra hx
    have hb := dock_northwest_full r ha q (by omega) (by
      change r.height + max r.sourceHoles r.width < _ at hlevel; omega)
    exact (mem_holes _).mp (a.holes_toState.symm ▸ hq) hb
  refine ⟨hx, ?_⟩
  let p : Cell (dock r).width (dock r).height :=
    (⟨q.1.val - 2, by have := q.1.isLt; change q.1.val < (dock r).width + 2 at this; omega⟩,
      ⟨q.2.val, by change q.2.val < r.height + (wideReader r).length; omega⟩)
  have hp : (dock r).embed p = q :=
    Prod.ext (Fin.ext (by dsimp [p, CornerDock.Input.embed]; omega)) (Fin.ext rfl)
  have hps := (hready.source p).mp (hp.symm ▸ hq)
  have hright := hs p hps hy
  change q.1.val - 2 < r.width at hright
  omega

private theorem dock_room_stock (r : ColumnScan.Input)
    (source : State (dock r).width (dock r).height)
    (a : HoleState (dock r).outputWidth (dock r).outputHeight)
    (hready : Ready (dock r) source a) (hroom : (wideReader r).room ⊆ holes source) :
    ∀ row ∈ auxiliaryRows r, r.width + 2 ≤ (a.empty.filter fun q => q.2.val = row).card := by
  intro row hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  let level : Fin ((wideReader r).outputHeight - r.height) := ⟨j, List.mem_range.mp hj⟩
  let f := fun i : Fin (r.width + 2) => (dock r).embed (reserveCell r (i, level))
  have hinj : Function.Injective f := fun _ _ he => congrArg Prod.fst
    (reserveCell_injective r ((dock r).embed_injective he))
  have hsub : Finset.univ.image f ⊆ a.empty.filter (fun q => q.2.val = r.height + j) := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_filter.mpr
    constructor
    · apply (hready.source (reserveCell r (i, level))).mpr
      apply hroom
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · change r.width < r.width + 1 + i.val; omega
      · change r.height ≤ r.height + j; omega
    · rfl
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

/-- The real source computation and exact first read yield the full supported canonical dock bitmap. -/
theorem canonical_dock (r : ColumnScan.Input) {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s) (hcorner : s.player = r.sourceCorner)
    {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E) :
    Nonempty (CanonicalDock r E) := by
  obtain ⟨source, hs, hsp, hE, hroom, hsupport⟩ := first_round_exact_supported (wideReader r) hr hcorner heval
  obtain ⟨a, ha, hap, hready⟩ := compile_ready (dock r) (hs.reboard rfl) hsp
  refine ⟨⟨a, ha, hap, ?_, dock_data_support r source hsupport a ha hready, ?_,
    dock_room_stock r source a hready hroom⟩⟩
  · ext p
    simp only [sourceData, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hready.source ((wideReader r).embed p)).trans (hE p)
  · intro q hq hy
    have h := (dock r).hole_support ha q (a.holes_toState.symm ▸ hq)
    change q.1.val < 2 ∨ q.2.val < (wideReader r).outputHeight at h
    omega

end PushPuzzle.Push.Cyclic
