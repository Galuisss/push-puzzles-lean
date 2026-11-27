/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortBounds
public import PushS.FiniteRoutingBoundary
public import PushFS.Reduction.CellExterior

/-! Literal common-axis macrocell contacts and separated producer/consumer inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction
open Cslib.Complexity.NCL

theorem neighbor_travels {d : Direction} {p r : GridRouting.Point} (hn : neighbor d p = some r) :
    Travels d p r 1 := by
  cases d <;> dsimp [PushFS.Reduction.neighbor,Travels] at * <;>
    (try split_ifs at hn) <;> simp_all [Prod.ext_iff] <;> omega

theorem travels_neighbor {d : Direction} {p r : GridRouting.Point} (ht : Travels d p r 1) :
    neighbor d p = some r := by
  cases d <;> dsimp [PushFS.Reduction.neighbor,Travels] at * <;>
    (try split_ifs) <;> simp_all [Prod.ext_iff]

theorem neighbor_ne {d : Direction} {p r : GridRouting.Point} (hn : neighbor d p = some r) : p ≠ r := by
  have ht := neighbor_travels hn
  intro he
  rw [he] at ht
  cases d <;> dsimp [Travels] at ht <;> omega

theorem macro_contact (w : ℕ) (p r a b : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w) (hb : b.1 < tileSide w ∧ b.2 < tileSide w)
    (hactor : ∀ face, InCollar w face a → SameLane face (Line.along w face (boundaryPoint w face) 0) a)
    (hne : p ≠ r) (he : macroShift w p a = macroShift w r b) :
    ∃ d, neighbor d p = some r ∧ InCollar w d a ∧ InCollar w d.opposite b := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*p.1+a.1 = tileStride w*r.1+b.1 at hx
  change tileStride w*p.2+a.2 = tileStride w*r.2+b.2 at hy
  by_cases hpx : p.1 = r.1
  · have hpy : p.2 ≠ r.2 := fun h => hne (Prod.ext hpx h)
    rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with h | h
    · exact ⟨.south,travels_neighbor (show Travels .south p r 1 from ⟨hpx,h.1⟩),h.2⟩
    · exact ⟨.north,travels_neighbor (show Travels .north p r 1 from ⟨hpx,h.1⟩),h.2⟩
  · rcases macro_axis_collar w p.1 r.1 a.1 b.1 ha.1 hb.1 hx hpx with h | h
    · have hla := hactor .east h.2.1
      dsimp [SameLane,Line.along,boundaryPoint] at hla
      have hpy : p.2 = r.2 := by
        by_contra hpy
        rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
      exact ⟨.east,travels_neighbor (show Travels .east p r 1 from ⟨hpy,h.1⟩),h.2⟩
    · have hla := hactor .west h.2.1
      dsimp [SameLane,Line.along,boundaryPoint] at hla
      have hpy : p.2 = r.2 := by
        by_contra hpy
        rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
      exact ⟨.west,travels_neighbor (show Travels .west p r 1 from ⟨hpy,h.1⟩),h.2⟩

theorem macro_port_owned_ne (w : ℕ) (d : Direction) (p r a b : ℕ × ℕ) (incoming : Bool)
    (hn : neighbor d p = some r) (ha : PortOwnedBound w d incoming a)
    (hb : PortOwnedBound w d.opposite (!incoming) b) : macroShift w p a ≠ macroShift w r b := by
  have ht := neighbor_travels hn
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*p.1+a.1 = tileStride w*r.1+b.1 at hx
  change tileStride w*p.2+a.2 = tileStride w*r.2+b.2 at hy
  cases d with
  | north =>
    change p.1 = r.1 ∧ p.2 = r.2+1 at ht
    rw [ht.2,Nat.mul_add,Nat.mul_one] at hy
    cases incoming <;> dsimp [PortOwnedBound,Direction.opposite] at ha hb <;> omega
  | east =>
    change p.2 = r.2 ∧ r.1 = p.1+1 at ht
    rw [ht.2,Nat.mul_add,Nat.mul_one] at hx
    cases incoming <;> dsimp [PortOwnedBound,Direction.opposite] at ha hb <;> omega
  | south =>
    change p.1 = r.1 ∧ r.2 = p.2+1 at ht
    rw [ht.2,Nat.mul_add,Nat.mul_one] at hy
    cases incoming <;> dsimp [PortOwnedBound,Direction.opposite] at ha hb <;> omega
  | west =>
    change p.2 = r.2 ∧ p.1 = r.1+1 at ht
    rw [ht.2,Nat.mul_add,Nat.mul_one] at hx
    cases incoming <;> dsimp [PortOwnedBound,Direction.opposite] at ha hb <;> omega

theorem macro_neighbor_travels (w : ℕ) (d : Direction) (p r : GridRouting.Point)
    (hn : PushFS.Reduction.neighbor d p = some r) :
    Travels d (tileStride w*p.1,tileStride w*p.2) (tileStride w*r.1,tileStride w*r.2) (tileStride w) := by
  have ht := neighbor_travels hn
  cases d <;> dsimp [Travels] at * <;>
    constructor
  all_goals first
    | exact congrArg (fun x => tileStride w*x) ht.1
    | (rw [ht.2,Nat.mul_add,Nat.mul_one])

theorem macro_boundary_seam (w : ℕ) (d : Direction) (p r : GridRouting.Point) (incoming : Bool)
    (hn : PushFS.Reduction.neighbor d p = some r) :
    macroShift w p (boundarySlot w d incoming true) =
      macroShift w r (boundarySlot w d.opposite (!incoming) false) := by
  cases incoming
  · simpa only [macroShift,shift,Bool.not_true,Bool.not_false] using
      boundary_seam w d (tileStride w*p.1,tileStride w*p.2) (tileStride w*r.1,tileStride w*r.2) true
        (macro_neighbor_travels w d p r hn)
  · have h := boundary_seam w d.opposite (tileStride w*r.1,tileStride w*r.2)
      (tileStride w*p.1,tileStride w*p.2) false
      (macro_neighbor_travels w d.opposite r p (neighbor_reverse hn))
    simpa only [macroShift,shift,Bool.not_false,Bool.not_true,Direction.opposite_opposite] using h.symm

end PushPuzzle.PushS.FiniteRouting
