/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMesh
public import PushS.FiniteSourcePorts
public import PushS.FiniteRoutingMeshPortOwners

/-! A real occupant of a coarse-grid edge comes from exactly one of its two incident source cells. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

private theorem vertical_boundary_origins (w : ℕ) (gx gy t : ℕ) (ht : t ≤ tileStride w) (r a : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w (w+1) face a)
    (he : macroShift w r a = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    r.2 = gy ∧ ((r.1 = gx ∧ InCollar w .west a) ∨ (r.1+1 = gx ∧ InCollar w .east a)) := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*r.1+a.1 = tileStride w*gx+padding w at hx
  change tileStride w*r.2+a.2 = tileStride w*gy+padding w+t at hy
  have hcases : (r.1 = gx ∧ InCollar w .west a) ∨
      (r.1+1 = gx ∧ InCollar w .east a) := boundary_axis_origins w gx r.1 a.1 ha.1 hx
  have hb : padding w+25*spacing w ≤ a.2+(w+1) ∧ a.2 ≤ padding w+25*spacing w+(w+1) := by
    rcases hcases with h | h
    · exact hband .west h.2
    · exact hband .east h.2
  exact ⟨(port_band_index w (w+1) r.2 gy t a.2 (by unfold spacing; omega) ht hb hy).1,hcases⟩

private theorem horizontal_boundary_origins (w : ℕ) (gx gy t : ℕ) (ht : t ≤ tileStride w) (r a : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w (w+1) face a)
    (he : macroShift w r a = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    r.1 = gx ∧ ((r.2 = gy ∧ InCollar w .north a) ∨ (r.2+1 = gy ∧ InCollar w .south a)) := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*r.1+a.1 = tileStride w*gx+padding w+t at hx
  change tileStride w*r.2+a.2 = tileStride w*gy+padding w at hy
  have hcases : (r.2 = gy ∧ InCollar w .north a) ∨
      (r.2+1 = gy ∧ InCollar w .south a) := boundary_axis_origins w gy r.2 a.2 ha.2 hy
  have hb : padding w+25*spacing w ≤ a.1+(w+1) ∧ a.1 ≤ padding w+25*spacing w+(w+1) := by
    rcases hcases with h | h
    · exact hband .north h.2
    · exact hband .south h.2
  exact ⟨(port_band_index w (w+1) r.1 gx t a.1 (by unfold spacing; omega) ht hb hx).1,hcases⟩

theorem vertical_unused_clear (w : ℕ) (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .west)
    (r a : ℕ × ℕ) (ha : a.1 < tileSide w ∧ a.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w (w+1) face a)
    (hport : ∀ face, InCollar w face a → ∃ incoming, LocalPort (CellPlan.cell (v,r)) face incoming) :
    macroShift w r a ≠ (tileStride w*gx+padding w,tileStride w*gy+padding w+t) := by
  intro he
  obtain ⟨hy,h⟩ := vertical_boundary_origins w gx gy t ht r a ha hband he
  rcases h with h | h
  · have hr : r = (gx,gy) := Prod.ext h.1 hy
    obtain ⟨incoming,hp⟩ := hport .west h.2
    exact hn (hr ▸ local_port_used v r .west incoming hp)
  · have hnb : PushFS.Reduction.neighbor .east r = some (gx,gy) := travels_neighbor ⟨hy,h.1.symm⟩
    obtain ⟨incoming,hp⟩ := hport .east h.2
    exact hn ((CellPlan.used_reciprocal v hP hT hnb).mp (local_port_used v r .east incoming hp))

theorem horizontal_unused_clear (w : ℕ) (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .north)
    (r a : ℕ × ℕ) (ha : a.1 < tileSide w ∧ a.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w (w+1) face a)
    (hport : ∀ face, InCollar w face a → ∃ incoming, LocalPort (CellPlan.cell (v,r)) face incoming) :
    macroShift w r a ≠ (tileStride w*gx+padding w+t,tileStride w*gy+padding w) := by
  intro he
  obtain ⟨hx,h⟩ := horizontal_boundary_origins w gx gy t ht r a ha hband he
  rcases h with h | h
  · have hr : r = (gx,gy) := Prod.ext hx h.1
    obtain ⟨incoming,hp⟩ := hport .north h.2
    exact hn (hr ▸ local_port_used v r .north incoming hp)
  · have hnb : PushFS.Reduction.neighbor .south r = some (gx,gy) := travels_neighbor ⟨hx,h.1.symm⟩
    obtain ⟨incoming,hp⟩ := hport .south h.2
    exact hn ((CellPlan.used_reciprocal v hP hT hnb).mp (local_port_used v r .south incoming hp))

end PushPuzzle.PushS.FiniteSourceInventory
