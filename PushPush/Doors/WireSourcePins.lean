/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourceUnique
public import PushPush.Doors.WireGeometry

/-! Every routing pin in a compiled source has a private row. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors

namespace Layout

private theorem wireY_lt_wireV (L : Layout) (i : ℕ) (e : Wire) :
    decide (L.wireY i e < L.wireV i e) = !(e.sourceSouth && e.targetSouth) := by
  cases hs : e.sourceSouth <;> cases ht : e.targetSouth <;>
    simp [wireY, wireV, level, shift, hs, ht] <;> omega

private def privatePins (L : Layout) (i : ℕ) (e : Wire) : List (ℕ × ℕ) :=
  [(wireA i, beside e.sourceSouth (L.wireY i e)), (wireB i + 1, L.wireY i e),
    (wireB i, beside (decide (L.wireY i e < L.wireV i e)) (L.wireV i e)),
    (wireC i - 1, L.wireV i e)]

private theorem privatePins_outer (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    {p : ℕ × ℕ} (hp : p ∈ L.privatePins i e) :
    p.2 + 2 < L.shift ∨ L.depth + L.shift + 2 < p.2 := by
  simp only [privatePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [L.wireY_lt_wireV] <;>
    cases hs : e.sourceSouth <;> cases ht : e.targetSouth <;>
    simp [wireY, wireV, level, beside, shift, hs, ht] <;> omega

-- Enumerate private-pin choices and both wire orientation bits.
set_option maxHeartbeats 800000 in
private theorem privatePins_same_row (L : Layout) (i j : ℕ) (e f : Wire)
    (hi : i < L.wires.length) (hj : j < L.wires.length) {p q : ℕ × ℕ}
    (hp : p ∈ L.privatePins i e) (hq : q ∈ L.privatePins j f) (hy : p.2 = q.2) : p = q := by
  simp only [privatePins, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [L.wireY_lt_wireV] at hy ⊢ <;>
    cases hs : e.sourceSouth <;> cases ht : e.targetSouth <;>
    cases hs' : f.sourceSouth <;> cases ht' : f.targetSouth <;>
    simp only [wireY, wireV, level, beside, hs, ht, hs', ht', Bool.and_self,
      Bool.and_false, Bool.and_true, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at hy ⊢ <;>
    apply Prod.ext <;> dsimp [wireA, wireB, wireC, shift] at * <;> omega

theorem wireY_neighbor_outer (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (side : Bool) :
    (beside side (L.wireY i e)) + 1 < L.shift ∨
      L.depth + L.shift + 1 < beside side (L.wireY i e) := by
  cases hs : e.sourceSouth <;> cases side <;>
    simp [wireY, level, beside, shift, hs] <;> omega

theorem wireV_neighbor_outer (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (side : Bool) :
    (beside side (L.wireV i e)) + 1 < L.shift ∨
      L.depth + L.shift + 1 < beside side (L.wireV i e) := by
  cases ht : e.targetSouth <;> cases side <;>
    simp [wireV, level, beside, shift, ht] <;> omega

-- Enumerate private-pin choices and both wire orientation bits.
set_option maxHeartbeats 800000 in
private theorem privatePins_nearY (L : Layout) (i j : ℕ) (e f : Wire)
    (hi : i < L.wires.length) (hj : j < L.wires.length) (side : Bool) {p : ℕ × ℕ}
    (hp : p ∈ L.privatePins j f) (hy : p.2 = beside side (L.wireY i e)) :
    side = e.sourceSouth ∧ p = (wireA i, beside e.sourceSouth (L.wireY i e)) := by
  simp only [privatePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    simp only [L.wireY_lt_wireV] at hy ⊢ <;>
    cases hs : e.sourceSouth <;>
    cases hs' : f.sourceSouth <;> cases ht' : f.targetSouth <;> cases side <;>
    simp only [wireY, wireV, level, beside, hs, hs', ht', Bool.and_self,
      Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, Bool.false_eq_true, Bool.true_eq_false,
      true_and, false_and] at hy ⊢ <;>
    try omega
  all_goals try { dsimp only [shift] at hy; omega }
  all_goals
    apply Prod.ext <;> dsimp [wireA, wireB, wireC, shift] at * <;> omega

-- Enumerate private-pin choices and both wire orientation bits.
set_option maxHeartbeats 800000 in
private theorem privatePins_nearV (L : Layout) (i j : ℕ) (e f : Wire)
    (hi : i < L.wires.length) (hj : j < L.wires.length) (side : Bool) {p : ℕ × ℕ}
    (hident : i = j → e = f)
    (hp : p ∈ L.privatePins j f) (hy : p.2 = beside side (L.wireV i e)) :
    side = decide (L.wireY i e < L.wireV i e) ∧
      p = (wireB i, beside (decide (L.wireY i e < L.wireV i e)) (L.wireV i e)) := by
  simp only [privatePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    simp only [L.wireY_lt_wireV] at hy ⊢ <;>
    cases hs : e.sourceSouth <;> cases ht : e.targetSouth <;>
    cases hs' : f.sourceSouth <;> cases ht' : f.targetSouth <;> cases side <;>
    simp only [wireY, wireV, level, beside, ht, hs', ht', Bool.and_self,
      Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, Bool.true_eq_false,
      true_and, false_and] at hy ⊢ <;>
    try omega
  all_goals try { dsimp only [shift] at hy; omega }
  all_goals
    have hij : i = j := by omega
    have hsides := congrArg Wire.sourceSouth (hident hij)
    rw [hs, hs'] at hsides
    cases hsides
  all_goals
    apply Prod.ext <;> dsimp [wireA, wireB, wireC, shift] at * <;> omega

end Layout

namespace Source

theorem wire_target_ge (storage : Bool) (I : Instance) {e : Wire}
    (he : e ∈ (layout storage I).wires) : 10 ≤ e.target := by
  simp only [layout, wires, List.mem_append] at he
  rcases he with (((he | he) | he) | he) | he
  · obtain ⟨i, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> dsimp <;> omega
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    dsimp [arrivalWire, inputRow]
    omega
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    dsimp
    split <;> omega
  · obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    simp only [List.mem_ite_nil_right, List.mem_singleton] at he
    obtain ⟨_, rfl⟩ := he
    dsimp [inputRow]
    omega
  · cases storage
    · simp at he
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      dsimp
      omega

theorem beside_add (side : Bool) (row shift : ℕ) (hrow : 0 < row) :
    Layout.beside side (row + shift) = Layout.beside side row + shift := by
  cases side <;> dsimp [Layout.beside] <;> omega

private theorem wire_index_eq (storage : Bool) (I : Instance) {e f : Wire} {i j : ℕ}
    (hi : (e, i) ∈ ((layout storage I).wires).zipIdx)
    (hj : (f, j) ∈ ((layout storage I).wires).zipIdx) (heq : e = f) : i = j := by
  obtain ⟨hi, he⟩ := List.mem_zipIdx' hi
  obtain ⟨hj, hf⟩ := List.mem_zipIdx' hj
  have hn := (wires_sources_nodup storage I).of_map Wire.source
  have hinj := List.nodup_iff_injective_getElem.mp hn
  have hfin : (⟨i, hi⟩ : Fin ((layout storage I).wires.length)) = ⟨j, hj⟩ := hinj (by
    change ((layout storage I).wires)[i] = ((layout storage I).wires)[j]
    rw [← he, ← hf, heq])
  exact congrArg Fin.val hfin

/-- Any two original routing pins on the same row are the same physical box cell. -/
theorem pins_same_row (storage : Bool) (I : Instance) {p q : ℕ × ℕ}
    (hp : p ∈ (layout storage I).pins) (hq : q ∈ (layout storage I).pins)
    (hy : p.2 = q.2) : p = q := by
  let L := layout storage I
  obtain ⟨⟨e, i⟩, hei, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  obtain ⟨⟨f, j⟩, hfj, hq⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hq)
  change p ∈ L.wirePins i e at hp
  change q ∈ L.wirePins j f at hq
  have hi := (List.mem_zipIdx' hei).1
  have hj := (List.mem_zipIdx' hfj).1
  have he : e ∈ L.wires := by
    rw [(List.mem_zipIdx' hei).2]
    exact List.getElem_mem hi
  have hf : f ∈ L.wires := by
    rw [(List.mem_zipIdx' hfj).2]
    exact List.getElem_mem hj
  have hefit := wires_fit storage I he
  have hffit := wires_fit storage I hf
  change e.source ≤ L.depth ∧ e.target ≤ L.depth at hefit
  change f.source ≤ L.depth ∧ f.target ≤ L.depth at hffit
  have hetarget := wire_target_ge storage I he
  have hftarget := wire_target_ge storage I hf
  have headd := beside_add e.targetSouth e.target L.shift (by omega)
  have hfadd := beside_add f.targetSouth f.target L.shift (by omega)
  have hp' : p = (Layout.wireA i - 1, e.source + L.shift) ∨
      p = (Layout.wireC i, Layout.beside e.targetSouth (e.target + L.shift)) ∨
      p ∈ L.privatePins i e := by
    simp only [Layout.wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Layout.privatePins]
  have hq' : q = (Layout.wireA j - 1, f.source + L.shift) ∨
      q = (Layout.wireC j, Layout.beside f.targetSouth (f.target + L.shift)) ∨
      q ∈ L.privatePins j f := by
    simp only [Layout.wirePins, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Layout.privatePins]
  rcases hp' with rfl | rfl | hp'
  · rcases hq' with rfl | rfl | hq'
    · have hef := wires_eq_of_source_eq storage I he hf (by simpa only using Nat.add_right_cancel hy)
      have hij := wire_index_eq storage I hei hfj hef
      subst f
      subst j
      rfl
    · rw [hfadd] at hy
      exact False.elim (wire_source_ne_terminalPin storage I he hf (by omega))
    · have hout := L.privatePins_outer j f hj hq'
      omega
  · rcases hq' with rfl | rfl | hq'
    · rw [headd] at hy
      exact False.elim (wire_source_ne_terminalPin storage I hf he (by omega))
    · rw [headd, hfadd] at hy
      have hef := wires_eq_of_pinRow_eq storage I he hf (by exact Nat.add_right_cancel hy)
      have hij := wire_index_eq storage I hei hfj hef
      subst f
      subst j
      rfl
    · have hout := L.privatePins_outer j f hj hq'
      dsimp [Layout.beside] at hy
      split at hy <;> omega
  · rcases hq' with rfl | rfl | hq'
    · have hout := L.privatePins_outer i e hi hp'
      omega
    · have hout := L.privatePins_outer i e hi hp'
      dsimp [Layout.beside] at hy
      split at hy <;> omega
    · exact L.privatePins_same_row i j e f hi hj hp' hq' hy

/-- Pin rows lie in a private outer band or on a launch/invalid-output row. -/
theorem pins_row_cases (storage : Bool) (I : Instance) {p : ℕ × ℕ}
    (hp : p ∈ (layout storage I).pins) :
    (p.2 + 2 < (layout storage I).shift ∨
      (layout storage I).depth + (layout storage I).shift + 2 < p.2) ∨
    ∃ e ∈ (layout storage I).wires,
      p.2 = e.source + (layout storage I).shift ∨
        p.2 = pinRow e + (layout storage I).shift := by
  let L := layout storage I
  obtain ⟨⟨e, i⟩, hei, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  change p ∈ L.wirePins i e at hp
  have hi := (List.mem_zipIdx' hei).1
  have he : e ∈ L.wires := by
    rw [(List.mem_zipIdx' hei).2]
    exact List.getElem_mem hi
  have ht := wire_target_ge storage I he
  simp only [Layout.wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨e, he, Or.inl rfl⟩
  · exact Or.inl (L.privatePins_outer i e hi (by simp [Layout.privatePins]))
  · exact Or.inl (L.privatePins_outer i e hi (by simp [Layout.privatePins]))
  · exact Or.inl (L.privatePins_outer i e hi (by simp [Layout.privatePins]))
  · exact Or.inl (L.privatePins_outer i e hi (by simp [Layout.privatePins]))
  · exact Or.inr ⟨e, he, Or.inr (beside_add _ _ _ (by omega))⟩

/-- The row beside a private Y track contains its A pin exactly on the original
source-side sign; the other sign has no original pin. -/
theorem pins_at_Y_neighbor (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (side : Bool) {p : ℕ × ℕ}
    (hp : p ∈ (layout storage I).pins)
    (hy : p.2 = Layout.beside side ((layout storage I).wireY i e)) :
    side = e.sourceSouth ∧ p = (Layout.wireA i,
      Layout.beside e.sourceSouth ((layout storage I).wireY i e)) := by
  let L := layout storage I
  have hi := (List.mem_zipIdx' hei).1
  have hout := L.wireY_neighbor_outer i e hi side
  obtain ⟨⟨f, j⟩, hfj, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  have hj := (List.mem_zipIdx' hfj).1
  have hf : f ∈ L.wires := (List.mem_zipIdx' hfj).2.symm ▸ List.getElem_mem hj
  have hfit := wires_fit storage I hf
  change f.source ≤ L.depth ∧ f.target ≤ L.depth at hfit
  change p ∈ L.wirePins j f at hp
  change p.2 = Layout.beside side (L.wireY i e) at hy
  have hp' : p ∈ L.privatePins j f := by
    simp only [Layout.wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp at hy
      exact False.elim (by omega)
    · simp [Layout.privatePins]
    · simp [Layout.privatePins]
    · simp [Layout.privatePins]
    · simp [Layout.privatePins]
    · have hb : L.shift ≤ Layout.beside f.targetSouth (f.target + L.shift) + 1 ∧
          Layout.beside f.targetSouth (f.target + L.shift) ≤ L.depth + L.shift + 1 := by
        cases f.targetSouth <;> simp only [Layout.beside, Bool.false_eq_true, ite_false, ite_true] <;> omega
      exact False.elim (by dsimp only at hy; omega)
  exact L.privatePins_nearY i j e f hi hj side hp' hy

/-- The row beside a private V track contains its B pin exactly on the Y-to-V
travel sign. -/
theorem pins_at_V_neighbor (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (side : Bool) {p : ℕ × ℕ}
    (hp : p ∈ (layout storage I).pins)
    (hy : p.2 = Layout.beside side ((layout storage I).wireV i e)) :
    side = decide ((layout storage I).wireY i e < (layout storage I).wireV i e) ∧
      p = (Layout.wireB i, Layout.beside
        (decide ((layout storage I).wireY i e < (layout storage I).wireV i e))
        ((layout storage I).wireV i e)) := by
  let L := layout storage I
  have hi := (List.mem_zipIdx' hei).1
  have hout := L.wireV_neighbor_outer i e hi side
  obtain ⟨⟨f, j⟩, hfj, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  have hj := (List.mem_zipIdx' hfj).1
  have hf : f ∈ L.wires := (List.mem_zipIdx' hfj).2.symm ▸ List.getElem_mem hj
  have hfit := wires_fit storage I hf
  change f.source ≤ L.depth ∧ f.target ≤ L.depth at hfit
  change p ∈ L.wirePins j f at hp
  change p.2 = Layout.beside side (L.wireV i e) at hy
  have hp' : p ∈ L.privatePins j f := by
    simp only [Layout.wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp at hy
      exact False.elim (by omega)
    · simp [Layout.privatePins]
    · simp [Layout.privatePins]
    · simp [Layout.privatePins]
    · simp [Layout.privatePins]
    · have hb : L.shift ≤ Layout.beside f.targetSouth (f.target + L.shift) + 1 ∧
          Layout.beside f.targetSouth (f.target + L.shift) ≤ L.depth + L.shift + 1 := by
        cases f.targetSouth <;> simp only [Layout.beside, Bool.false_eq_true, ite_false, ite_true] <;> omega
      exact False.elim (by dsimp only at hy; omega)
  apply L.privatePins_nearV i j e f hi hj side ?_ hp' hy
  intro hij
  subst j
  exact (List.mem_zipIdx' hei).2.trans (List.mem_zipIdx' hfj).2.symm

end Source
end PushPuzzle.PushPush.Doors
