/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Reduction.PlacedBitmap
public import PushFS.StaticTracks
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Tauto

/-! Assemble complete owned inventories over the literal union of their placed walls. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction

/-- Actual pieces, complete physical identities, and their rectangular placement coordinates. -/
structure InventoryAssembly (n W H : ℕ) (Label : Fin n → Type) [∀ i, Fintype (Label i)] where
  piece : Fin n → Instance
  matching : ∀ i, SlotMatching (piece i) (Label i)
  dx : Fin n → ℕ
  dy : Fin n → ℕ
  fitsX : ∀ i, dx i+(piece i).width ≤ W
  fitsY : ∀ i, dy i+(piece i).height ≤ H
  player : Cell W H

namespace InventoryAssembly

open scoped Classical
variable {n W H : ℕ} {Label : Fin n → Type} [∀ i, Fintype (Label i)]

def embedding (A : InventoryAssembly n W H Label) (i : Fin n) :
    GridEmbedding (A.piece i).width (A.piece i).height W H :=
  GridEmbedding.translate (A.dx i) (A.dy i) (A.fitsX i) (A.fitsY i)

/-- A unique proof identity for every owned box in the complete assembly. -/
abbrev PhysicalLabel (_A : InventoryAssembly n W H Label) := (i : Fin n) × Label i

/-- The actual owned labels of one emitted primitive inside the complete inventory. -/
def labelEmbedding (A : InventoryAssembly n W H Label) (i : Fin n) : Label i ↪ A.PhysicalLabel where
  toFun := Sigma.mk i
  inj' a b h := by cases h; rfl

def source (A : InventoryAssembly n W H Label) (l : A.PhysicalLabel) : Cell W H :=
  (A.embedding l.1).cells ((A.matching l.1).source l.2)

def target (A : InventoryAssembly n W H Label) (l : A.PhysicalLabel) : Cell W H :=
  (A.embedding l.1).cells ((A.matching l.1).target l.2)

def walls (A : InventoryAssembly n W H Label) : Finset (Cell W H) :=
  Finset.univ.biUnion fun i => (A.piece i).board.walls.map (A.embedding i).cells

theorem wall_mem_of_piece (A : InventoryAssembly n W H Label) (i : Fin n)
    (p : Cell (A.piece i).width (A.piece i).height) (hp : p ∈ (A.piece i).board.walls) :
    (A.embedding i).cells p ∈ A.walls :=
  Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_map.mpr ⟨p,hp,rfl⟩⟩

def board (A : InventoryAssembly n W H Label) : Board W H :=
  ⟨A.walls, Finset.univ.image A.target⟩

def initial (A : InventoryAssembly n W H Label) : State W H :=
  ⟨A.player, Finset.univ.image A.source⟩

/-- Coordinate ownership and actor clearance for a concrete placed inventory. -/
structure Admissible (A : InventoryAssembly n W H Label) : Prop where
  source_injective : Function.Injective A.source
  target_injective : Function.Injective A.target
  source_floor : ∀ l, A.source l ∉ A.walls
  target_floor : ∀ l, A.target l ∉ A.walls
  player_floor : A.player ∉ A.walls
  player_empty : ∀ l, A.player ≠ A.source l

/-- Positive horizontal placement offsets reserve an exterior player cell at column zero. -/
theorem player_floor_of_dx_pos (A : InventoryAssembly n W H Label) (hp : A.player.1.val = 0)
    (hx : ∀ i, 0 < A.dx i) : A.player ∉ A.walls := by
  intro hm
  obtain ⟨i,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,_,he⟩ := Finset.mem_map.mp hm
  have hX := congrArg (fun p : Cell W H => p.1.val) he
  change A.dx i+p.1.val = A.player.1.val at hX
  have hi := hx i
  omega

theorem player_empty_of_dx_pos (A : InventoryAssembly n W H Label) (hp : A.player.1.val = 0)
    (hx : ∀ i, 0 < A.dx i) (l : A.PhysicalLabel) : A.player ≠ A.source l := by
  intro he
  have hX := congrArg (fun p : Cell W H => p.1.val) he
  change A.player.1.val = A.dx l.1+_ at hX
  have hi := hx l.1
  omega

theorem mem_boxes_iff (A : InventoryAssembly n W H Label) (p : Cell W H) :
    p ∈ A.initial.boxes ↔ ∃ i q, q ∈ (A.piece i).initial.boxes ∧ (A.embedding i).cells q = p := by
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨i, (A.matching i).source l, ?_, rfl⟩
    rw [← (A.matching i).source_image]
    exact Finset.mem_map.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · rintro ⟨i, q, hq, rfl⟩
    rw [← (A.matching i).source_image] at hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_image.mpr ⟨⟨i,l⟩, Finset.mem_univ _, rfl⟩

theorem mem_goals_iff (A : InventoryAssembly n W H Label) (p : Cell W H) :
    p ∈ A.board.goals ↔ ∃ i q, q ∈ (A.piece i).board.goals ∧ (A.embedding i).cells q = p := by
  constructor
  · intro hp
    obtain ⟨⟨i,l⟩, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨i, (A.matching i).target l, ?_, rfl⟩
    rw [← (A.matching i).target_image]
    exact Finset.mem_map.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · rintro ⟨i, q, hq, rfl⟩
    rw [← (A.matching i).target_image] at hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_image.mpr ⟨⟨i,l⟩, Finset.mem_univ _, rfl⟩

/-- Complete unlabelled storage with the actual union of all placed walls and actors. -/
def puzzle (A : InventoryAssembly n W H Label) (ha : A.Admissible) : Instance where
  width := W
  height := H
  board := A.board
  initial := A.initial
  goals_floor := by
    apply Finset.disjoint_left.mpr
    intro p hw hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    exact ha.target_floor l hw
  initial_valid := by
    refine ⟨ha.player_floor, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro p hp hw
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
      exact ha.source_floor l hw
    · intro hp
      obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
      exact ha.player_empty l he.symm
  boxes_eq_goals := by
    change (Finset.univ.image A.source).card = (Finset.univ.image A.target).card
    rw [Finset.card_image_of_injective _ ha.source_injective,
      Finset.card_image_of_injective _ ha.target_injective]

/-- Explicit placed slot paths establish the source-to-target matching of the complete board. -/
def slotMatching (A : InventoryAssembly n W H Label) (ha : A.Admissible)
    (hc : ∀ l, SameComponent A.board (A.source l) (A.target l)) :
    SlotMatching (A.puzzle ha) A.PhysicalLabel where
  source := ⟨A.source, ha.source_injective⟩
  target := ⟨A.target, ha.target_injective⟩
  source_image := Finset.map_eq_image _ _
  target_image := Finset.map_eq_image _ _
  connected := hc

def input (A : InventoryAssembly n W H Label) : Bitmap.Input :=
  ⟨W, H, A.player.1.val, A.player.2.val,
    List.ofFn fun i => Bitmap.instancePatch (A.piece i) (A.dx i) (A.dy i)⟩

private theorem flag_truth (A : InventoryAssembly n W H Label) (p : Cell W H)
    (select : Encoding.Tile → Bool) (hempty : select Bitmap.emptyTile = false) :
    Bitmap.flag select (A.input, p.1.val, p.2.val) = true ↔
      ∃ i q, (A.embedding i).cells q = p ∧
        select (Encoding.tile (A.piece i).board (A.piece i).initial q) = true := by
  simp only [Bitmap.flag, input, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨patch, ⟨i, rfl⟩, hp⟩
    exact ⟨i, (Bitmap.instancePatch_truth (A.piece i) (A.dx i) (A.dy i)
      (A.fitsX i) (A.fitsY i) p select hempty).mp hp⟩
  · rintro ⟨i, hp⟩
    exact ⟨_, ⟨i, rfl⟩, (Bitmap.instancePatch_truth (A.piece i) (A.dx i) (A.dy i)
      (A.fitsX i) (A.fitsY i) p select hempty).mpr hp⟩

/-- Tilewise machine output agrees with the actual union board and complete inventory. -/
private theorem tile_eq (A : InventoryAssembly n W H Label) (p : Cell W H) :
    Bitmap.tile (A.input, p.1.val, p.2.val) = Encoding.tile A.board A.initial p := by
  have hw : Bitmap.flag Encoding.Tile.wall (A.input, p.1.val, p.2.val) = decide (p ∈ A.board.walls) := by
    apply Bool.eq_iff_iff.mpr
    rw [flag_truth A p _ rfl]
    simp only [Encoding.tile, decide_eq_true_eq, board, walls, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_map]
    tauto
  have hg : Bitmap.flag Encoding.Tile.goal (A.input, p.1.val, p.2.val) = decide (p ∈ A.board.goals) := by
    apply Bool.eq_iff_iff.mpr
    rw [flag_truth A p _ rfl]
    simp only [Encoding.tile, decide_eq_true_eq]
    rw [A.mem_goals_iff p]
    tauto
  have hb : Bitmap.flag Encoding.Tile.box (A.input, p.1.val, p.2.val) = decide (p ∈ A.initial.boxes) := by
    apply Bool.eq_iff_iff.mpr
    rw [flag_truth A p _ rfl]
    simp only [Encoding.tile, decide_eq_true_eq]
    rw [A.mem_boxes_iff p]
    tauto
  have hp : decide (p.1.val = A.player.1.val ∧ p.2.val = A.player.2.val) = decide (p = A.player) := by
    simp only [Prod.ext_iff, Fin.ext_iff]
  change Encoding.Tile.mk _ _ _ _ = Encoding.Tile.mk _ _ _ _
  rw [hw, hg, hb]
  exact congrArg (Encoding.Tile.mk _ _ _) hp

/-- The standard dense instance encoding is exactly the actual primitive-patch rasterizer output. -/
theorem data_eq (A : InventoryAssembly n W H Label) (ha : A.Admissible) :
    Encoding.data (A.puzzle ha) = Bitmap.emit A.input := by
  change Encoding.Data.mk W H (Encoding.rows A.board A.initial) =
    Encoding.Data.mk W H ((List.range H).map fun y => (List.range W).map fun x => Bitmap.tile (A.input, x, y))
  congr 1
  apply List.ext_getElem
  · simp only [Encoding.rows, List.length_ofFn, List.length_map, List.length_range]
  · intro y hy _
    have hy' : y < H := by simpa only [Encoding.rows, List.length_ofFn] using hy
    simp only [Encoding.rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range]
    · intro x hx _
      have hx' : x < W := by simpa only [List.length_ofFn] using hx
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact (A.tile_eq (⟨x, hx'⟩, ⟨y, hy'⟩)).symm

end InventoryAssembly
end PushPuzzle.PushFS.Reduction
