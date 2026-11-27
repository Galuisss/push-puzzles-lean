/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateFirstRodStep
public import Push.AcceptanceAxisReadoutOuter
import all Push.AcceptanceFrontTrain
import all PushS.PortWalkBudget
import all PushS.PortGatePageWindow
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality

/-! The original upper first rod on a gate middle column remains anchored before the four-hole deficit is cancelled. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceFrontTrain

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hs : upper.side = .upper) (hp : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hg hk hu hs hp

private theorem gate_fullAxis_front_initial :
    Nonempty (FrontTrain (w := p.W + 1) (h := p.H + 1) .south (p.x (g.left + 1)) (readDepth p upper.level - 1)
      (BoxMask.keep ((I).initial : State (p.W + 1) (p.H + 1)) (ordinaryAxis p (g.left + 1)))) := by
  classical
  let b := gateAxisTrainBlocks p upper (l.canonical initial)
  have gap := l.gateAxisTrainBlocks_gapped p hl hM hu (l.canonical initial)
  have source := l.physicalInstance_gateAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hg hk hu hs hp
  have sep : b.asThree.Separated := ⟨gap.le, by change b.last + (0 : ℕ) ≤ b.last; omega⟩
  have sourceFixed : (lineBoxes .south (p.x (g.left + 1))
      (BoxMask.keep ((I).initial : State (p.W + 1) (p.H + 1)) (gateAxis p (g.left + 1))) :
        Finset (Cell (p.W + 1) (p.H + 1))).image Direction.south.position = b.slots := source
  let train := FrontTrain.ofThreeSlots sep sourceFixed
  have first : train.first = 1 := rfl
  refine ⟨⟨1, train.position, ?_, ?_, ?_⟩⟩
  · intro i
    have occupied := train.occupied i
    change train.position i ∈ ((((I).initial.boxes : Finset (Cell (p.W + 1) (p.H + 1))) ∩
      gateAxis p (g.left + 1)).filter fun q : Cell (p.W + 1) (p.H + 1) => Direction.south.lane q = p.x (g.left + 1)) at occupied
    obtain ⟨hb, hr⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp occupied).1
    have data := (Finset.mem_filter.mp hr).2
    change train.position i ∈ ((((I).initial.boxes : Finset (Cell (p.W + 1) (p.H + 1))) ∩
      ordinaryAxis p (g.left + 1)).filter fun q : Cell (p.W + 1) (p.H + 1) => Direction.south.lane q = p.x (g.left + 1))
    exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hb,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, data.1, data.2.1, by omega⟩⟩, data.1⟩
  · intro i
    simpa only [first] using train.coordinates i
  · intro q hq
    change q ∈ ((((I).initial.boxes : Finset (Cell (p.W + 1) (p.H + 1))) ∩
      ordinaryAxis p (g.left + 1)).filter fun q : Cell (p.W + 1) (p.H + 1) => Direction.south.lane q = p.x (g.left + 1)) at hq
    have hpos := (Finset.mem_filter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).2).2.2.1
    change (1 : ℤ) ≤ (q.2.val : ℤ)
    omega

include hgate

/-- The real gate middle column preserves its original upper first train even while boxes may leave the lower gate work row. -/
theorem canonical_gate_fullAxis_front_train {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Nonempty (FrontTrain (w := p.W + 1) (h := p.H + 1) .south (p.x (g.left + 1)) (readDepth p upper.level - 1)
      (BoxMask.keep u (ordinaryAxis p (g.left + 1)))) := by
  obtain ⟨train⟩ := gate_fullAxis_front_initial l p hl hM haxes initial target hg hk hu hs hp
  have positive := (l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)).1
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := ordinaryAxis p (g.left + 1)
  have decorated : Relation.ReflTransGen (fun a b => EditingStep
      (w := p.W + 1) (h := p.H + 1) (I).board none .south (p.x (g.left + 1))
      (readDepth p upper.level - 1) p.D (BoxMask.keep a R) (BoxMask.keep b R)) (I).initial u := by
    apply Path.enrich hsu
    intro a b hsa step hbu
    exact canonical_gate_fullAxis_editing_step l p hl hM haxes initial target hgate hi upper hu hs hp
      hsa step (hbu.trans hut) accepted
  exact train.editing_reachable positive (decorated.lift (fun a => BoxMask.keep a R) (fun _ _ h => h))

/-- A terminal box next to the top frame anchors the preserved gate-column first train at coordinate one. -/
theorem canonical_gate_fullAxis_front_anchored {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∃ train : FrontTrain (w := p.W + 1) (h := p.H + 1) .south (p.x (g.left + 1)) (readDepth p upper.level - 1)
      (BoxMask.keep t (ordinaryAxis p (g.left + 1))), train.first = 1 := by
  obtain ⟨train⟩ := canonical_gate_fullAxis_front_train l p hl hM haxes initial target hgate hg hk hu hs hp run .refl accepted
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := ordinaryAxis p (g.left + 1)
  have mask : (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep t R) :
      Finset (Cell (p.W + 1) (p.H + 1))) = t.boxes ∩ R :=
    BoxMask.lineBoxes_keep (fun _ hq => (Finset.mem_filter.mp hq).2.1) t
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have hxW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le haxes) 0
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let top : Cell (p.W + 1) (p.H + 1) := (⟨p.x (g.left + 1), by omega⟩, ⟨1, by omega⟩)
  have ht := AcceptanceAxisReadout.canonical_main_frame_neighbor_empty l p hl hM haxes initial target run accepted
    (gate_center_lt l hl hi) top rfl (Or.inl rfl)
  have topBox : top ∈ t.boxes := by simpa only [mem_holes, not_not] using ht
  have topRail : top ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [top]; omega, by dsimp only [top]; omega⟩
  have topLine : top ∈ lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep t R) := by
    rw [mask]
    exact Finset.mem_inter.mpr ⟨topBox, topRail⟩
  have firstLe : train.first ≤ 1 := train.least top topLine
  have positive := (l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)).1
  change 0 < readDepth p upper.level - 1 at positive
  let i : Fin (readDepth p upper.level - 1) := ⟨0, positive⟩
  have firstBox := train.occupied i
  change train.position i ∈ lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep t R) at firstBox
  rw [mask] at firstBox
  have ypos := (Finset.mem_filter.mp (Finset.mem_inter.mp firstBox).2).2.2.1
  have firstCoord := train.coordinates i
  change ((train.position i).2.val : ℤ) = train.first + (0 : ℕ) at firstCoord
  exact ⟨train, by omega⟩

/-- Every original upper first-rod box on a true gate middle column is terminally occupied without a four-hole axis certificate. -/
theorem canonical_gate_upper_first_rod_full {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy0 : 1 ≤ q.2.val) (hy : q.2.val < readDepth p upper.level) : q ∈ t.boxes := by
  obtain ⟨train, first⟩ := canonical_gate_fullAxis_front_anchored l p hl hM haxes initial target hgate
    hg hk hu hs hp run accepted
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have hb := train.box_of_bounds q hx (by rw [first]; change (1 : ℤ) ≤ (q.2.val : ℤ); omega)
    (by rw [first]; change (q.2.val : ℤ) < 1 + (readDepth p upper.level - 1 : ℕ); omega)
  exact (Finset.mem_inter.mp hb).1

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
