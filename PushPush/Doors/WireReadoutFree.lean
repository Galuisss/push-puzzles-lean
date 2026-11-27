/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutFault

/-! Globally empty private columns and single-pin fault inventory updates. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction)

namespace Layout

theorem pins_not_free_column (L : Layout) (i : ℕ) {p : ℕ × ℕ} (hp : p ∈ L.pins) :
    p.1 ≠ wireA i + 1 ∧ p.1 ≠ wireB i - 1 ∧ p.1 ≠ wireC i + 1 := by
  obtain ⟨⟨e, j⟩, _, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  exact L.pin_not_in_free_column i j e hp

end Layout

namespace Source.Stock

variable {I : Source.Instance}

theorem raw_column_empty (storage : Bool) (S : Stock I) (x : ℕ)
    (hx : x < (layout storage I).rackX - 1)
    (hpin : ∀ p ∈ (layout storage I).pins, p.1 ≠ x) (hsignal : S.signal.1 ≠ x)
    {p : ℕ × ℕ} (hp : p.1 = x) : p ∉ S.rawBoxes storage := by
  intro hb
  rcases Finset.mem_union.mp hb with hstationary | hsignal'
  · exact S.private_clear storage (by omega) (fun h => hpin p h hp) hstationary
  · have he := congrArg Prod.fst (Finset.mem_singleton.mp hsignal')
    exact hsignal (by omega)

end Source.Stock

namespace Source.WireFault

variable {storage : Bool} {I : Instance} {S : Stock I}

/-- A single reverse pin move keeps the original signal and moves exactly one original pin. -/
def single (signal removed landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (removed.1.val, removed.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = S.signal) : WireFault storage I S where
  removed := {removed}
  added := {landed}
  signal := signal
  removed_pin := by intro p hp; have he := Finset.mem_singleton.mp hp; exact he ▸ hpin
  signal_raw := hsignal

theorem single_boxes (signal removed landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (removed.1.val, removed.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = S.signal) :
    (single signal removed landed hpin hsignal).boxes = insert landed ((S.boxes storage).erase removed) := by
  ext p
  simp [boxes, single, Finset.mem_sdiff, Finset.mem_erase, and_comm]

theorem single_missing (signal removed landed : Cell (layout storage I).width (layout storage I).height)
    (hpin : (removed.1.val, removed.2.val) ∈ (layout storage I).pins)
    (hsignal : (signal.1.val, signal.2.val) = S.signal) (hne : removed ≠ landed) :
    removed ∉ (single signal removed landed hpin hsignal).boxes := by
  rw [single_boxes]
  simp [hne]

end Source.WireFault
end PushPuzzle.PushPush.Doors
