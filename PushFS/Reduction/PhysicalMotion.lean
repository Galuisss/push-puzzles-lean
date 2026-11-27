/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.PrimitiveMotion
public import PushFS.Reduction.PhysicalInterior

/-! Every actual macrocell identity moves by one cell or stays in the strict interior at both endpoints. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalTiles

open Gadgets.Wires GateTileRouting.FullGateStatics
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

private theorem base_motion (k : Catalog.Kind) (a b : Bool) : SlotMotion (Catalog.baseMatching k a b) := by
  cases k
  · exact chain_motion 200000 (by decide) a b
  · exact (chain_motion 200000 (by decide) a b).reflectX
  · exact (chain_motion 198061 (by decide) a b).transpose.reflectX
  · exact normal_motion 99970 98999 (by decide) (by decide) a b
  · exact (out_motion 99970 98979 (by decide) (by decide) a b).reflectX
  · exact (in_motion 98981 99969 (by decide) (by decide) a b).reflectX.transpose
  · exact (normal_motion 99001 99969 (by decide) (by decide) a b).reflectX.transpose.reflectX

private theorem catalog_motion (k : Catalog.Kind) (a b : Bool) : SlotMotion
    (Catalog.slotMatching k a b) :=
  SlotMotion.atlas (Catalog.atlas k a b) (fun _=>base_motion k a b)

private theorem matching_motion (k : Key) : SlotMotion (matching k) := by
  cases k with
  | inl g=>exact full_motion g
  | inr a=>exact catalog_motion a.1 a.2.1 a.2.2

private theorem deep_inner (k : Key) (p : Cell (piece k).width (piece k).height) (hp : Cell.Deep p) : Inner k p := by
  cases k
  · change 7≤p.1.val ∧p.1.val+7<200007 ∧7≤p.2.val ∧p.2.val+7<198068 at hp
    change 7≤0+p.1.val ∧0+p.1.val<200000 ∧7≤0+p.2.val ∧0+p.2.val<198061
    omega
  · change 7≤p.1.val ∧p.1.val+7<200005 ∧7≤p.2.val ∧p.2.val+7<198066 at hp
    change 7≤1+p.1.val ∧1+p.1.val<200000 ∧7≤1+p.2.val ∧1+p.2.val<198061
    omega

/-- All actual identities whose movement exceeds one cell stay deep inside their one physical macrocell. -/
theorem slot_motion (k : Key) (l : Labels k) :
    Cell.UnitClose ((matching k).source l) ((matching k).target l) ∨
      Inner k ((matching k).source l) ∧Inner k ((matching k).target l) := by
  rcases (matching_motion k).bound l with hh|⟨hp,hq⟩
  · exact Or.inl hh
  · exact Or.inr ⟨deep_inner k _ hp,deep_inner k _ hq⟩

end PushPuzzle.PushFS.Reduction.PhysicalTiles
