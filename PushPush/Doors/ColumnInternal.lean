/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnHorizontal

/-! All private-turn pin faults contradict the original private-column counts. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)

private theorem wire_vertical_direction (L : Layout) (i : ℕ) (e : Wire) (corner : Fin 7)
    (hc : corner.val = 1 ∨ corner.val = 3 ∨ corner.val = 5) :
    wireDirection L i e corner = .north ∨ wireDirection L i e corner = .south := by
  rcases hc with hc | hc | hc
  · have he : corner = 1 := Fin.ext hc
    subst corner
    change (if e.sourceSouth then Direction.south else .north) = .north ∨
      (if e.sourceSouth then Direction.south else .north) = .south
    cases e.sourceSouth <;> simp
  · have he : corner = 3 := Fin.ext hc
    subst corner
    change (if L.wireY i e < L.wireV i e then Direction.south else .north) = .north ∨
      (if L.wireY i e < L.wireV i e then Direction.south else .north) = .south
    split <;> simp
  · have he : corner = 5 := Fin.ext hc
    subst corner
    change (if e.targetSouth then Direction.south else .north) = .north ∨
      (if e.targetSouth then Direction.south else .north) = .south
    cases e.targetSouth <;> simp

namespace Stock

variable {I : Instance}

/-- Exact terminal pin positions are unnecessary: the original number of boxes
in each private column already rejects every internal routing-pin move. -/
theorem internal_pin_reject_columns (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (hlo : 0 < corner.val) (hhi : corner.val < 6)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val
      (layout storage I).wires[index] corner)
    (hregister : ∀ door, S.register door ≠ .erase)
    {s t final : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    (hsuffix : Reachable t final) (hcorridor : ProtectedCorridor storage I t final)
    (hterminal : PrivateColumnInventory storage I final.boxes)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) ∈
      (layout storage I).pins) : False := by
  have hc : corner = 1 ∨ corner = 2 ∨ corner = 3 ∨ corner = 4 ∨ corner = 5 := by
    have hcv : corner.val = 1 ∨ corner.val = 2 ∨ corner.val = 3 ∨ corner.val = 4 ∨ corner.val = 5 := by omega
    simpa [Fin.ext_iff] using hcv
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact S.private_vertical_pin_reject_columns storage index 1 (by decide) (by decide)
      (wire_vertical_direction _ _ _ 1 (Or.inl rfl)) hsignal hregister
      (S.first_corner_reverse_clear storage index hsignal) hstock ht hsuffix hcorridor hterminal r hn hk hb hfirst
  · exact S.horizontal_pin_reject_columns storage index 2 (Or.inl rfl) hsignal hregister
      hstock ht hsuffix hcorridor hterminal r hn hk hb hfirst
  · by_cases hsame : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index]) =
          (layout storage I).wires[index].sourceSouth
    · obtain ⟨E, hboxes⟩ := S.sameSignB_pin_fault storage index hsignal hsame hstock ht r hn hk hb hfirst
      exact E.reject_columns hregister hboxes hsuffix hcorridor hterminal
    · exact S.private_vertical_pin_reject_columns storage index 3 (by decide) (by decide)
        (wire_vertical_direction _ _ _ 3 (Or.inr (Or.inl rfl))) hsignal hregister
        (S.middle_corner_reverse_clear storage index hsignal hsame)
        hstock ht hsuffix hcorridor hterminal r hn hk hb hfirst
  · exact S.horizontal_pin_reject_columns storage index 4 (Or.inr rfl) hsignal hregister
      hstock ht hsuffix hcorridor hterminal r hn hk hb hfirst
  · by_cases hsame : (layout storage I).wires[index].targetSouth =
        decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
          (layout storage I).wireV index.val (layout storage I).wires[index])
    · obtain ⟨E, hboxes⟩ := S.sameSignC_pin_fault storage index hsignal hsame hstock ht r hn hk hb hfirst
      exact E.reject_columns hregister hboxes hsuffix hcorridor hterminal
    · exact S.private_vertical_pin_reject_columns storage index 5 (by decide) (by decide)
        (wire_vertical_direction _ _ _ 5 (Or.inr (Or.inr rfl))) hsignal hregister
        (S.last_vertical_reverse_clear storage index hsignal hsame)
        hstock ht hsuffix hcorridor hterminal r hn hk hb hfirst

end Stock
end PushPuzzle.PushPush.Doors.Source
