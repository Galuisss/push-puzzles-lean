/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireSourceClear
public import PushPush.Doors.WireSourceMembers
import Mathlib.Data.List.GetD

/-! Finite physical coordinates of the seven normal routing slides. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

def wirePositionRaw (L : Layout) (i : ℕ) (e : Wire) (j : Fin 8) : ℕ × ℕ :=
  (L.wirePath i e).getD j.val (0, 0)

def wireStopRaw (L : Layout) (i : ℕ) (e : Wire) (j : Fin 7) : ℕ × ℕ :=
  if j.val < 6 then (L.wirePins i e).getD j.val (0, 0)
  else (L.rackX, e.target + L.shift)

def wireDirection (L : Layout) (i : ℕ) (e : Wire) (j : Fin 7) : Direction :=
  match j.val with
  | 0 => .west
  | 1 => if e.sourceSouth then .south else .north
  | 2 => .east
  | 3 => if L.wireY i e < L.wireV i e then .south else .north
  | 4 => .west
  | 5 => if e.targetSouth then .south else .north
  | _ => .east

theorem wirePositionRaw_mem (L : Layout) (i : ℕ) (e : Wire) (j : Fin 8) :
    wirePositionRaw L i e j ∈ L.wirePath i e := by
  have hj : j.val < (L.wirePath i e).length := by simp [Layout.wirePath]
  rw [wirePositionRaw, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

def wirePosition (storage : Bool) (I : Instance) (i : ℕ) (hi : i < (layout storage I).wires.length)
    (e : Wire) (he : e ∈ (layout storage I).wires) (j : Fin 8) :
    Cell (layout storage I).width (layout storage I).height :=
  let p := wirePositionRaw (layout storage I) i e j
  have hb := (layout storage I).wirePath_interior hi e (wires_fit storage I he).1
    (wires_fit storage I he).2 (wirePositionRaw_mem _ i e j)
  (layout storage I).point p (by dsimp [p]; omega) (by dsimp [p]; omega)

@[simp] theorem wirePosition_raw (storage : Bool) (I : Instance) (i : ℕ)
    (hi : i < (layout storage I).wires.length) (e : Wire) (he : e ∈ (layout storage I).wires)
    (j : Fin 8) :
    ((wirePosition storage I i hi e he j).1.val, (wirePosition storage I i hi e he j).2.val) =
      wirePositionRaw (layout storage I) i e j := rfl

theorem wireStopRaw_interior (L : Layout) {i : ℕ} (hi : i < L.wires.length) (e : Wire)
    (hs : e.source ≤ L.depth) (ht : e.target ≤ L.depth) (j : Fin 7) :
    0 < (wireStopRaw L i e j).1 ∧ (wireStopRaw L i e j).1 < L.width - 1 ∧
      0 < (wireStopRaw L i e j).2 ∧ (wireStopRaw L i e j).2 < L.height - 1 := by
  unfold wireStopRaw
  split
  · have hj : j.val < (L.wirePins i e).length := by simp [Layout.wirePins]; omega
    rw [List.getD_eq_getElem _ _ hj]
    exact L.wirePins_interior hi e hs ht (List.getElem_mem hj)
  · have hy := L.translated_bounds ht
    dsimp
    unfold Layout.width Layout.rackX
    omega

def wireStop (storage : Bool) (I : Instance) (i : ℕ) (hi : i < (layout storage I).wires.length)
    (e : Wire) (he : e ∈ (layout storage I).wires) (j : Fin 7) :
    Cell (layout storage I).width (layout storage I).height :=
  let p := wireStopRaw (layout storage I) i e j
  have hb := wireStopRaw_interior (layout storage I) hi e (wires_fit storage I he).1
    (wires_fit storage I he).2 j
  (layout storage I).point p (by dsimp [p]; omega) (by dsimp [p]; omega)

@[simp] theorem wireStop_raw (storage : Bool) (I : Instance) (i : ℕ)
    (hi : i < (layout storage I).wires.length) (e : Wire) (he : e ∈ (layout storage I).wires)
    (j : Fin 7) :
    ((wireStop storage I i hi e he j).1.val, (wireStop storage I i hi e he j).2.val) =
      wireStopRaw (layout storage I) i e j := rfl

theorem wire_leg_geometry (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (hs : e.source ≤ L.depth) (ht : e.target ≤ L.depth) (j : Fin 7)
    (source dest stop : Cell L.width L.height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw L i e j.castSucc)
    (hdest : (dest.1.val, dest.2.val) = wirePositionRaw L i e j.succ)
    (hstop : (stop.1.val, stop.2.val) = wireStopRaw L i e j) :
    (wireDirection L i e j).lane dest = (wireDirection L i e j).lane source ∧
      (wireDirection L i e j).position source < (wireDirection L i e j).position dest ∧
      Adjacent (wireDirection L i e j) dest stop := by
  have hY := L.wireY_source_gap i e hi hs
  have hV := L.wireV_target_gap i e hi ht
  have hYV := L.wire_levels_separated i e
  have hYpos := (L.wireY_bounds hi e).1
  have hVpos := (L.wireV_bounds hi e).1
  have hshift : 0 < L.shift := by unfold Layout.shift; omega
  rcases j with ⟨j, hj⟩
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hjcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wirePositionRaw, wireStopRaw, Layout.wirePath, Layout.wirePins] at hsource hdest hstop <;>
    cases hsouth : e.sourceSouth <;> cases htsouth : e.targetSouth <;>
    by_cases hlt : L.wireY i e < L.wireV i e <;>
    simp only [wireDirection, Layout.beside, hsouth, htsouth, hlt, decide_true, decide_false,
      Bool.false_eq_true, ite_false, ite_true, Direction.lane, Direction.position, Adjacent]
      at hstop hY hV ⊢ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    dsimp [Layout.wireA, Layout.wireB, Layout.wireC, Layout.rackX] at * <;>
    omega

theorem wirePosition_columns (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (j : Fin 8) : (wirePositionRaw L i e j).1 ∈ L.columns := by
  have hp := wirePositionRaw_mem L i e j
  have hprivate : ∀ offset ∈ ([7, 8, 14, 15, 24, 25] : List ℕ), 30 * i + offset ∈ L.columns := by
    intro offset ho
    apply List.mem_toFinset.mpr
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
    omega
  simp only [Layout.wirePath, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with he | he | he | he | he | he | he | he <;> rw [he]
  · exact L.working_mem_columns
  · exact hprivate 8 (by simp)
  · exact hprivate 8 (by simp)
  · exact hprivate 24 (by simp)
  · exact hprivate 24 (by simp)
  · exact hprivate 15 (by simp)
  · exact hprivate 15 (by simp)
  · exact L.working_mem_columns

theorem wireStopRaw_pin_mem (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7) (hj : j.val < 6) :
    wireStopRaw (layout storage I) i e j ∈ (layout storage I).pins := by
  apply List.mem_toFinset.mpr
  apply List.mem_flatMap.mpr
  refine ⟨(e, i), hei, ?_⟩
  simp only [wireStopRaw, ite_eq_left hj]
  have hj' : j.val < ((layout storage I).wirePins i e).length := by simpa [Layout.wirePins] using hj
  rw [List.getD_eq_getElem _ _ hj']
  exact List.getElem_mem hj'

theorem wireStopRaw_mem (storage : Bool) (I : Instance) {e : Wire} {i : ℕ}
    (hei : (e, i) ∈ ((layout storage I).wires).zipIdx) (j : Fin 7) :
    wireStopRaw (layout storage I) i e j ∈ (layout storage I).fixed := by
  have he : e ∈ (layout storage I).wires :=
    (List.mem_zipIdx' hei).2.symm ▸ List.getElem_mem (List.mem_zipIdx' hei).1
  by_cases hj : j.val < 6
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (wireStopRaw_pin_mem storage I hei j hj))
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp only [wireStopRaw, ite_eq_right hj, Layout.rack, List.mem_toFinset]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨e.target, wire_target_rack_mem storage I he, rfl⟩

/-- A row or column contains at most one original routing pin. -/
theorem pin_lane_unique (storage : Bool) (I : Instance) (d : Direction)
    (p q : Cell (layout storage I).width (layout storage I).height)
    (hp : (p.1.val, p.2.val) ∈ (layout storage I).pins)
    (hq : (q.1.val, q.2.val) ∈ (layout storage I).pins)
    (hlane : d.lane p = d.lane q) : p = q := by
  have he : (p.1.val, p.2.val) = (q.1.val, q.2.val) := by
    cases d
    · exact (layout storage I).pins_same_column hp hq hlane
    · exact pins_same_row storage I hp hq hlane
    · exact (layout storage I).pins_same_column hp hq hlane
    · exact pins_same_row storage I hp hq hlane
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

/-- Before the pin that stops a leg, its entire line is free of other routing pins. -/
theorem pin_ray_clear (storage : Bool) (I : Instance) (d : Direction)
    (p stop : Cell (layout storage I).width (layout storage I).height)
    (hstop : (stop.1.val, stop.2.val) ∈ (layout storage I).pins)
    (hlane : d.lane p = d.lane stop) (hpos : d.position p < d.position stop) :
    (p.1.val, p.2.val) ∉ (layout storage I).pins := by
  intro hp
  have he := pin_lane_unique storage I d p stop hp hstop hlane
  subst p
  exact (lt_irrefl _) hpos

/-- A route interval stays strictly west of the working column except at its two ports. -/
theorem wire_interval_location (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (j : Fin 7) (source dest p : Cell L.width L.height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw L i e j.castSucc)
    (hdest : (dest.1.val, dest.2.val) = wirePositionRaw L i e j.succ)
    (hlane : (wireDirection L i e j).lane p = (wireDirection L i e j).lane source)
    (hlo : (wireDirection L i e j).position source ≤ (wireDirection L i e j).position p)
    (hhi : (wireDirection L i e j).position p ≤ (wireDirection L i e j).position dest) :
    p.1.val < L.rackX - 1 ∨
      (j.val = 0 ∧ (p.1.val, p.2.val) = (L.rackX - 1, e.source + L.shift)) ∨
      (j.val = 6 ∧ (p.1.val, p.2.val) = (L.rackX - 1, e.target + L.shift)) := by
  have hA : Layout.wireA i + 2 < L.rackX - 1 := by unfold Layout.wireA Layout.rackX; omega
  have hB : Layout.wireB i + 2 < L.rackX - 1 := by unfold Layout.wireB Layout.rackX; omega
  have hC : Layout.wireC i + 2 < L.rackX - 1 := by unfold Layout.wireC Layout.rackX; omega
  rcases j with ⟨j, hj⟩
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hjcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wirePositionRaw, Layout.wirePath] at hsource hdest
  · simp only [wireDirection, Direction.lane, Direction.position] at hlane hlo hhi
    by_cases hx : p.1.val < L.rackX - 1
    · exact Or.inl hx
    · exact Or.inr (Or.inl ⟨rfl, Prod.ext (by omega) (hlane.trans hsource.2)⟩)
  · cases hs : e.sourceSouth <;> simp [wireDirection, hs, Direction.lane] at hlane
    all_goals
      apply Or.inl
      have hx : p.1.val = Layout.wireA i := hlane.trans hsource.1
      rw [hx]
      omega
  · simp only [wireDirection, Direction.position] at hhi
    apply Or.inl
    have hb : dest.1.val < L.rackX - 1 := by rw [hdest.1]; omega
    omega
  · by_cases hlt : L.wireY i e < L.wireV i e <;>
      simp [wireDirection, hlt, Direction.lane] at hlane
    all_goals
      apply Or.inl
      have hx : p.1.val = Layout.wireB i := hlane.trans hsource.1
      rw [hx]
      omega
  · simp only [wireDirection, Direction.position] at hlo
    apply Or.inl
    have hb : source.1.val < L.rackX - 1 := by rw [hsource.1]; omega
    omega
  · cases ht : e.targetSouth <;> simp [wireDirection, ht, Direction.lane] at hlane
    all_goals
      apply Or.inl
      have hx : p.1.val = Layout.wireC i := hlane.trans hsource.1
      rw [hx]
      omega
  · simp only [wireDirection, Direction.lane, Direction.position] at hlane hlo hhi
    by_cases hx : p.1.val < L.rackX - 1
    · exact Or.inl hx
    · exact Or.inr (Or.inr ⟨rfl, Prod.ext (by omega) (hlane.trans hsource.2)⟩)

/-- All push supports are private except the initial empty rack support. -/
theorem wire_support_location (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (j : Fin 7) (source support : Cell L.width L.height)
    (hsource : (source.1.val, source.2.val) = wirePositionRaw L i e j.castSucc)
    (hsupport : Adjacent (wireDirection L i e j).opposite source support) :
    support.1.val < L.rackX - 1 ∨
      (j.val = 0 ∧ (support.1.val, support.2.val) = (L.rackX, e.source + L.shift)) := by
  have hA : Layout.wireA i + 2 < L.rackX - 1 := by unfold Layout.wireA Layout.rackX; omega
  have hB : Layout.wireB i + 2 < L.rackX - 1 := by unfold Layout.wireB Layout.rackX; omega
  have hC : Layout.wireC i + 2 < L.rackX - 1 := by unfold Layout.wireC Layout.rackX; omega
  have hP : 0 < L.rackX := by unfold Layout.rackX; omega
  rcases j with ⟨j, hj⟩
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hjcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wirePositionRaw, Layout.wirePath] at hsource
  · simp only [wireDirection, Direction.opposite, Adjacent] at hsupport
    exact Or.inr ⟨rfl, Prod.ext (by omega) (congrArg Fin.val hsupport.2 |>.trans hsource.2)⟩
  · cases hs : e.sourceSouth <;> simp [wireDirection, hs, Direction.opposite, Adjacent] at hsupport
    all_goals
      apply Or.inl
      have hx : support.1.val = Layout.wireA i := (congrArg Fin.val hsupport.1).trans hsource.1
      rw [hx]
      omega
  · simp only [wireDirection, Direction.opposite, Adjacent] at hsupport
    apply Or.inl
    omega
  · by_cases hlt : L.wireY i e < L.wireV i e <;>
      simp [wireDirection, hlt, Direction.opposite, Adjacent] at hsupport
    all_goals
      apply Or.inl
      have hx : support.1.val = Layout.wireB i := (congrArg Fin.val hsupport.1).trans hsource.1
      rw [hx]
      omega
  · simp only [wireDirection, Direction.opposite, Adjacent] at hsupport
    apply Or.inl
    omega
  · cases ht : e.targetSouth <;> simp [wireDirection, ht, Direction.opposite, Adjacent] at hsupport
    all_goals
      apply Or.inl
      have hx : support.1.val = Layout.wireC i := (congrArg Fin.val hsupport.1).trans hsource.1
      rw [hx]
      omega
  · simp only [wireDirection, Direction.opposite, Adjacent] at hsupport
    apply Or.inl
    omega

end PushPuzzle.PushPush.Doors.Source
