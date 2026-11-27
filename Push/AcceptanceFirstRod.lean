/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceFirstRodStep
public import Push.AcceptanceAxisReadoutOuter

/-! The actual accepted terminal upper first rod is anchored at the frame before ordinary-axis inventory cancellation. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceFrontTrain

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {upper lower : Endpoint}
  (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
  (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hu hlow hsuSide hslSide hport

/-- The actual ordinary-axis prefix retains its first consecutive train even when lower input increases the axis inventory. -/
theorem canonical_ordinaryAxis_front_train {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Nonempty (FrontTrain .south (p.x upper.port) (readDepth p upper.level - 1)
      (BoxMask.keep u (ordinaryAxis p upper.port))) := by
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := ordinaryAxis p upper.port
  let b := ordinaryAxisTrainBlocks p upper lower (l.canonical initial)
  have positive := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  have gapped := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow (l.canonical initial)
  have source := l.physicalInstance_ordinaryAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hu hlow hsuSide hslSide hport
  let train := FrontTrain.ofThreeSlots ⟨gapped.1.le, gapped.2.le⟩ source
  have decorated : Relation.ReflTransGen
      (fun a b => GrowingStep (w := p.W + 1) (h := p.H + 1) (I).board none .south (p.x upper.port) p.D
        (BoxMask.keep a R) (BoxMask.keep b R)) (I).initial u := by
    apply Path.enrich hsu
    intro a b hsa step hbu
    exact canonical_ordinaryAxis_growing_step l p hl hM haxes initial target hgate hu hlow hsuSide hslSide hport
      hsa step (hbu.trans hut) accepted
  have path := decorated.lift (fun a => BoxMask.keep a R) (fun _ _ h => h)
  exact train.reachable positive.1 path

/-- The terminal frame-neighbor box fixes the preserved first train at coordinate one. -/
theorem canonical_ordinaryAxis_front_anchored {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∃ train : FrontTrain .south (p.x upper.port) (readDepth p upper.level - 1)
      (BoxMask.keep t (ordinaryAxis p upper.port)), train.first = 1 := by
  obtain ⟨train⟩ := canonical_ordinaryAxis_front_train l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport run .refl accepted
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := ordinaryAxis p upper.port
  have hon : ∀ q ∈ R, Direction.south.lane q = p.x upper.port := fun q hq => (Finset.mem_filter.mp hq).2.1
  have mask : (lineBoxes .south (p.x upper.port) (BoxMask.keep t R) :
      Finset (Cell (p.W + 1) (p.H + 1))) = t.boxes ∩ R := BoxMask.lineBoxes_keep hon t
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl hu).trans_le haxes) 0
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let top : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨1, by omega⟩)
  have ht := AcceptanceAxisReadout.canonical_main_frame_neighbor_empty l p hl hM haxes initial target run accepted
    (l.endpoints_port_lt hl hu) top rfl (Or.inl rfl)
  have topBox : top ∈ t.boxes := by simpa only [mem_holes, not_not] using ht
  have topRail : top ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [top]; omega, by dsimp only [top]; omega⟩
  have topLine : top ∈ lineBoxes .south (p.x upper.port) (BoxMask.keep t R) := by
    rw [mask]
    exact Finset.mem_inter.mpr ⟨topBox, topRail⟩
  have firstLe : train.first ≤ 1 := train.least top topLine
  have positive := (l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)).1
  change 0 < readDepth p upper.level - 1 at positive
  let i : Fin (readDepth p upper.level - 1) := ⟨0, positive⟩
  have firstBox := train.occupied i
  change train.position i ∈ lineBoxes .south (p.x upper.port) (BoxMask.keep t R) at firstBox
  rw [mask] at firstBox
  have rail := (Finset.mem_inter.mp firstBox).2
  have ypos := (Finset.mem_filter.mp rail).2.2.1
  have firstCoord := train.coordinates i
  change ((train.position i).2.val : ℤ) = train.first + (0 : ℕ) at firstCoord
  exact ⟨train, by omega⟩

/-- Every box of the actual terminal upper first rod remains occupied before any five-hole axis certificate is assumed. -/
theorem canonical_upper_first_rod_full {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x upper.port)
    (hy0 : 1 ≤ q.2.val) (hy : q.2.val < readDepth p upper.level) : q ∈ t.boxes := by
  obtain ⟨train, first⟩ := canonical_ordinaryAxis_front_anchored l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport run accepted
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have hb := train.box_of_bounds q hx (by rw [first]; change (1 : ℤ) ≤ (q.2.val : ℤ); omega)
    (by rw [first]; change (q.2.val : ℤ) < 1 + (readDepth p upper.level - 1 : ℕ); omega)
  exact (Finset.mem_inter.mp hb).1

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
