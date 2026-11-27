/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.LayoutGeometry
public import PushFS.Encoding
public import PushS.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Unary chamber recipes and polynomial-time emission of their full dense boards. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open Turing.MultiTapeTM

/-- All physical coordinates are represented in unary. -/
enc_structure encWire : Wire where
  source : encUnary, sourceSouth : encBool, target : encUnary, targetSouth : encBool

/-- The finite geometric recipe retains every static and dynamic box. -/
enc_structure encLayout : Layout where
  depth : encUnary, rackRows : (encList encUnary), dividers : (encList encUnary),
  caps : (encList encUnary), dataRows : (encList encUnary), goalRows : (encList encUnary),
  launch : encUnary, stop : encUnary, wires : (encList encWire)

namespace Layout

/-- Explicit coordinates of all wire pins. -/
def pinList (L : Layout) : List (ℕ × ℕ) :=
  L.wires.zipIdx.flatMap fun (e, i) => L.wirePins i e

/-- Explicit coordinates of the rack inventory. -/
def rackList (L : Layout) : List (ℕ × ℕ) :=
  (L.rackRows.map fun y => (L.rackX, y + L.shift)) ++
    L.dividers.flatMap (fun y =>
      [(L.rackX, y + L.shift - 1), (L.rackX, y + L.shift + 1)])

/-- Explicit coordinates of chamber dividers and endpoint caps. -/
def blockerList (L : Layout) : List (ℕ × ℕ) :=
  (L.dividers ++ L.caps).map fun y => (L.rackX - 1, y + L.shift)

/-- The complete initial coordinate list. -/
def initialList (L : Layout) : List (ℕ × ℕ) :=
  L.pinList ++ L.rackList ++ L.blockerList ++
    (L.launch :: L.dataRows).map (fun y => (L.rackX - 1, y + L.shift))

/-- The complete exact-target coordinate list. -/
def goalList (L : Layout) : List (ℕ × ℕ) :=
  L.pinList ++ L.rackList ++ L.blockerList ++
    (L.stop :: L.goalRows).map (fun y => (L.rackX - 1, y + L.shift))

@[simp] theorem initialList_toFinset (L : Layout) : L.initialList.toFinset = L.initialRaw := by
  simp [initialList, initialRaw, fixed, pins, rack, blockers, pinList, rackList, blockerList]

@[simp] theorem goalList_toFinset (L : Layout) : L.goalList.toFinset = L.goalsRaw := by
  simp [goalList, goalsRaw, fixed, pins, rack, blockers, pinList, rackList, blockerList]

/-- A raw coordinate pair uses the common unary product encoding. -/
abbrev encPoint := encPair encUnary encUnary

@[fun_prop] theorem shift_polyTime : ComputableInPolyTime shift encLayout encUnary := by
  unfold shift
  fun_prop

@[fun_prop] theorem rackX_polyTime : ComputableInPolyTime rackX encLayout encUnary := by
  unfold rackX
  fun_prop

@[fun_prop] theorem width_polyTime : ComputableInPolyTime width encLayout encUnary := by
  unfold width
  fun_prop

@[fun_prop] theorem height_polyTime : ComputableInPolyTime height encLayout encUnary := by
  unfold height
  fun_prop

@[fun_prop] theorem level_polyTime :
    ComputableInPolyTime (fun q : Layout × ℕ × Bool => q.1.level q.2.1 q.2.2)
      (encPair encLayout (encPair encUnary encBool)) encUnary := by
  unfold level
  fun_prop

@[fun_prop] theorem beside_polyTime :
    ComputableInPolyTime (fun q : Bool × ℕ => beside q.1 q.2)
      (encPair encBool encUnary) encUnary := by
  unfold beside
  fun_prop

@[fun_prop] theorem wirePins_polyTime :
    ComputableInPolyTime (fun q : Layout × Wire × ℕ => q.1.wirePins q.2.2 q.2.1)
      (encPair encLayout (encPair encWire encUnary)) (encList encPoint) := by
  unfold wirePins wireA wireB wireC wireY wireV level beside encPoint
  fun_prop

@[fun_prop] theorem pinList_polyTime :
    ComputableInPolyTime pinList encLayout (encList encPoint) := by
  unfold pinList
  fun_prop

@[fun_prop] theorem rackList_polyTime :
    ComputableInPolyTime rackList encLayout (encList encPoint) := by
  unfold rackList encPoint
  fun_prop

@[fun_prop] theorem blockerList_polyTime :
    ComputableInPolyTime blockerList encLayout (encList encPoint) := by
  unfold blockerList encPoint
  fun_prop

@[fun_prop] theorem initialList_polyTime :
    ComputableInPolyTime initialList encLayout (encList encPoint) := by
  unfold initialList encPoint
  fun_prop

@[fun_prop] theorem goalList_polyTime :
    ComputableInPolyTime goalList encLayout (encList encPoint) := by
  unfold goalList encPoint
  fun_prop

/-- Membership in an explicitly listed coordinate inventory. -/
def stockTest (q : List (ℕ × ℕ) × (ℕ × ℕ)) : Bool := q.1.contains q.2

@[fun_prop] theorem stockTest_polyTime :
    ComputableInPolyTime stockTest (encPair (encList encPoint) encPoint) encBool := by
  have he : ComputableInPolyTime (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1 == p.2)
      (encPair encPoint encPoint) encBool :=
    ComputableInPolyTime.beq (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _)
  change ComputableInPolyTime
    (fun q : List (ℕ × ℕ) × (ℕ × ℕ) => q.1.contains q.2)
    (encPair (encList encPoint) encPoint) encBool
  simpa only [List.contains_eq_any_beq, Function.comp_def] using
    ComputableInPolyTime.anyWithEncoding he (ComputableInPolyTime.snd _ _)
      (ComputableInPolyTime.fst (encList encPoint) encPoint)

/-- Four dense cell flags for the actual wall-free board. -/
def tile (q : Layout × ℕ × ℕ) : PushFS.Encoding.Tile :=
  ⟨false, stockTest (q.1.goalList, q.2), stockTest (q.1.initialList, q.2),
    decide (q.2.1 = q.1.width - 1 ∧ q.2.2 = q.1.height - 1)⟩

@[fun_prop] theorem tile_polyTime :
    ComputableInPolyTime tile (encPair encLayout encPoint) PushFS.Encoding.encTile := by
  unfold tile encPoint
  open scoped PushFS.Encoding in fun_prop

/-- Emit every physical cell, with unary dimensions and dense row-major flags. -/
def emit (L : Layout) : PushFS.Encoding.Data :=
  ⟨L.width, L.height, (List.range L.height).map fun y =>
    (List.range L.width).map fun x => tile (L, x, y)⟩

@[fun_prop] theorem emit_polyTime :
    ComputableInPolyTime emit encLayout PushFS.Encoding.encData := by
  unfold emit
  open scoped PushFS.Encoding in fun_prop

/-- Attach equal storage inventory to the actual rasterized board. -/
def toStorage (L : Layout)
    (hc : (L.raster L.initialRaw).card = (L.raster L.goalsRaw).card) : PushS.Instance :=
  PushS.Instance.ofState (L.raster L.goalsRaw) L.initial L.initial_player_empty hc

/-- The cell emitter agrees with the actual unlabelled finite storage instance. -/
private theorem tile_eq (L : Layout)
    (hc : (L.raster L.initialRaw).card = (L.raster L.goalsRaw).card)
    (p : PushFS.Cell L.width L.height) :
    tile (L, p.1.val, p.2.val) =
      PushFS.Encoding.tile (L.toStorage hc).board (L.toStorage hc).initial p := by
  have hi : stockTest (L.initialList, (p.1.val, p.2.val)) =
      decide ((p.1.val, p.2.val) ∈ L.initialRaw) := by
    simp only [stockTest, List.contains_eq_mem]
    rw [← L.initialList_toFinset]
    simp only [List.mem_toFinset]
  have hg : stockTest (L.goalList, (p.1.val, p.2.val)) =
      decide ((p.1.val, p.2.val) ∈ L.goalsRaw) := by
    simp only [stockTest, List.contains_eq_mem]
    rw [← L.goalList_toFinset]
    simp only [List.mem_toFinset]
  change PushFS.Encoding.Tile.mk false _ _ _ =
    ⟨decide (p ∈ (∅ : Finset (PushFS.Cell L.width L.height))),
      decide (p ∈ L.raster L.goalsRaw), decide (p ∈ L.raster L.initialRaw),
      decide (p = L.corner)⟩
  simp [hi, hg, corner, Prod.ext_iff, Fin.ext_iff]

/-- The emitted rectangle is exactly the actual instance's dense standard data. -/
theorem data_eq (L : Layout)
    (hc : (L.raster L.initialRaw).card = (L.raster L.goalsRaw).card) :
    PushFS.Encoding.data (L.toStorage hc).toInstance = emit L := by
  have hw : (L.toStorage hc).width = L.width := rfl
  have hh : (L.toStorage hc).height = L.height := rfl
  change PushFS.Encoding.Data.mk L.width L.height (PushFS.Encoding.rows _ _) =
    PushFS.Encoding.Data.mk L.width L.height ((List.range L.height).map fun y =>
      (List.range L.width).map fun x => tile (L, x, y))
  congr 1
  apply List.ext_getElem
  · simp [PushFS.Encoding.rows, hh]
  · intro y hy _
    have hy' : y < L.height := by simpa [PushFS.Encoding.rows, hh] using hy
    simp only [PushFS.Encoding.rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp [hw]
    · intro x hx _
      have hx' : x < L.width := by simpa [hw] using hx
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact (L.tile_eq hc (⟨x, hx'⟩, ⟨y, hy'⟩)).symm

/-- Actual storage instances compute the same dense words as the explicit recipe emitter. -/
theorem toStorage_polyTime {α : Type} {enc : α ↪ List Bool} {recipe : α → Layout}
    (hr : ComputableInPolyTime recipe enc encLayout)
    (hc : ∀ a, ((recipe a).raster (recipe a).initialRaw).card =
      ((recipe a).raster (recipe a).goalsRaw).card) :
    ComputableInPolyTime (fun a => (recipe a).toStorage (hc a)) enc PushS.encoding :=
  (emit_polyTime.comp hr).of_enc_eq
    (fun a => congrArg PushFS.Encoding.encData ((recipe a).data_eq (hc a)))

end Layout
end PushPuzzle.PushPush.Doors
