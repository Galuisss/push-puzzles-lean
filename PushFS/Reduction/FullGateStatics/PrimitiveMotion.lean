/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.SlotMotion
public import PushFS.Reduction.FullGateStatics.Primitive

/-! Unit endpoint movement and the seven-cell margins of every actual gate and wire primitive. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem tile_motion : ∀(kind a b : Bool) (l : Fin (Chain.Tile.count kind)),
    Cell.UnitClose (Chain.Tile.position kind a l) (Chain.Tile.position kind b l) ∨
      Cell.Deep (Chain.Tile.position kind a l) ∧Cell.Deep (Chain.Tile.position kind b l) := by decide +kernel

theorem chain_motion (n : ℕ) (hn : 2301≤n) (a b : Bool) : SlotMotion (Chain.slotMatching n hn a b) where
  bound l:=by
    have hh:=SlotMotion.translate_pair (W:=n+5) (H:=21) (Chain.offset n l.1.val) 0
      (Chain.fit n hn l.1) (by omega)
      _ _ (tile_motion (Chain.kind n l.1) a b l.2)
    exact hh

private theorem flip_motion (a b : Bool) : SlotMotion (Flip.checked.slotMatching a b) where
  bound l:=by
    have hh : ∀(a b : Bool) (l : Fin 9),Cell.UnitClose (Flip.template.position a l) (Flip.template.position b l) ∨
      Cell.Deep (Flip.template.position a l) ∧Cell.Deep (Flip.template.position b l) := by decide +kernel
    exact hh a b l

private theorem turn_motion (a b : Bool) : SlotMotion (Turn.checked.slotMatching a b) where
  bound l:=by
    have hh : ∀(a b : Bool) (l : Fin 29),Cell.UnitClose (Turn.template.position a l) (Turn.template.position b l) ∨
      Cell.Deep (Turn.template.position a l) ∧Cell.Deep (Turn.template.position b l) := by decide +kernel
    exact hh a b l

private theorem flipped_motion (n : ℕ) (hn : 2301≤n) (a b : Bool) : SlotMotion
    (FlippedChain.slotMatching n hn a b) := by
  apply SlotMotion.atlas
  intro i
  fin_cases i
  · exact chain_motion n hn a b
  · exact flip_motion a b

private theorem short_motion (kind : ShortCorners.Kind) (a b : Bool) : SlotMotion (ShortCorners.slotMatching kind a b) where
  bound l:=by
    have hh : ∀(kind : ShortCorners.Kind) (a b : Bool) (l : Fin (ShortCorners.count kind)),
        Cell.UnitClose ((ShortCorners.template kind).position a l) ((ShortCorners.template kind).position b l) ∨
          Cell.Deep ((ShortCorners.template kind).position a l) ∧Cell.Deep ((ShortCorners.template kind).position b l) := by
      decide +kernel
    exact hh kind a b l

private theorem core_motion_checked : ∀kind : Bool,(Gates.slots kind).all fun s=>
    decide (Cell.UnitClose s.zero s.one ∨Cell.Deep s.zero ∧Cell.Deep s.one) := by decide +kernel

private theorem gate_motion (kind : Bool) (a b : Gates.Signals) : SlotMotion
    (Gates.slotMatching kind a b) where
  bound l:=by
    let s:=(Gates.slots kind)[l.val]
    have hh:=of_decide_eq_true (List.all_eq_true.mp (core_motion_checked kind) s (List.getElem_mem l.isLt))
    change Cell.UnitClose (s.position a) (s.position b) ∨Cell.Deep (s.position a) ∧Cell.Deep (s.position b)
    unfold Gates.Slot.position
    split <;> split
    · left; dsimp only [Cell.UnitClose]; omega
    · rcases hh with hh|⟨hp,hq⟩
      · left; dsimp only [Cell.UnitClose] at *; omega
      · exact Or.inr ⟨hq,hp⟩
    · exact hh
    · left; dsimp only [Cell.UnitClose]; omega

private theorem buffer_motion (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (i : Fin 4) :
    SlotMotion (GateLead.matching kind n hn a b i) := by
  fin_cases i
  · exact gate_motion kind a b
  · cases kind
    · exact (chain_motion n hn a.left b.left).reorient ⟨false,true,true⟩
    · exact (chain_motion n hn a.left b.left).reflectX
  · exact (chain_motion n hn a.upper b.upper).reorient ⟨true,true,true⟩
  · exact (chain_motion n hn (!a.right) (!b.right)).reflectY

private theorem lineBase_motion (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) : SlotMotion (lineMatching f n hn a b) := by
  cases f
  · exact chain_motion n hn a b
  · exact flipped_motion n hn a b

private theorem line_motion (k : Key) (i : ℕ) (hi : i<(curve k).length) (a b : Bool) :
    SlotMotion (lineSlotMatching k i hi a b) :=
  (lineBase_motion (fillerFlip k i) (fillerSpan k i) (filler_shape k i hi).2.1 a b).reorient
    (lineOrientation (original k i).travel (fillerFlip k i))

private theorem corner_motion (k : Key) (i : ℕ) (a b : Bool) : SlotMotion
    (cornerMatching k i a b) :=
  (short_motion (cornerKind k i) a b).reorient (cornerOrientation k i)

private theorem primitive_motion (g : GateTileState) (i : Inventory.Index g) : SlotMotion
    (Inventory.matching g i) := by
  rcases i with i|(⟨role,j|j⟩|role)
  · exact buffer_motion _ _ _ _ _ i
  · exact line_motion _ _ j.isLt _ _
  · exact corner_motion _ _ _ _
  · exact ⟨fun l=>Fin.elim0 l⟩

theorem full_motion (g : GateTileState) : SlotMotion (fullSlotMatching g) :=
  SlotMotion.atlas (fullAtlas g) (fun i=>primitive_motion g ((numbering g).symm i))

theorem normal_motion (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    SlotMotion (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching := by
  apply SlotMotion.atlas
  intro i
  fin_cases i
  · exact (chain_motion m hm a b).reflectX
  · exact turn_motion a b
  · exact (chain_motion n hn a b).transpose.reflectX

theorem out_motion (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    SlotMotion (Catalog.Out.atlas m n hm hn (Catalog.Out.uniform a) (Catalog.Out.uniform b)).slotMatching := by
  apply SlotMotion.atlas
  intro i
  fin_cases i
  · exact (chain_motion m hm a b).reflectX
  · exact turn_motion a b
  · exact (flipped_motion n hn a b).transpose.reflectX

theorem in_motion (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool) :
    SlotMotion (Catalog.In.atlas m n hm hn (Catalog.In.uniform a) (Catalog.In.uniform b)).slotMatching := by
  apply SlotMotion.atlas
  intro i
  fin_cases i
  · exact (flipped_motion m hm a b).transpose.reflectX.transpose.reflectX
  · exact turn_motion a b
  · exact (chain_motion n hn a b).transpose.reflectX

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
