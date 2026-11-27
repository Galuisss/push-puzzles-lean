/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AxisCharts
public import PushFS.AxisIsometry
public import Mathlib.Data.Fintype.Sigma

/-!
# Complete storage instances assembled from overlapping glyph rectangles

Walls may overlap. Each physical box and target has one owner, while local
wall predicates agree on rectangle overlaps. These coordinate conditions give
a legal global instance and a static source-to-target matching of every box.
An actual chart cover then supplies the complete global SCC certificate.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction


/-- A finite physical atlas, with every glyph's actual box identities and translated coordinates. -/
structure StorageAtlas (n W H : ℕ) (Label : Fin n → Type) [∀ i, Fintype (Label i)] where
  /-- Complete oriented local instances, including auxiliary boxes. -/
  piece : Fin n → Instance
  /-- Actual source and target slots on each local wall graph. -/
  matching : ∀ i, SlotMatching (piece i) (Label i)
  /-- Unary horizontal offsets. -/
  dx : Fin n → ℕ
  /-- Unary vertical offsets. -/
  dy : Fin n → ℕ
  /-- Every declared rectangle fits horizontally. -/
  fitsX : ∀ i, dx i + (piece i).width ≤ W
  /-- Every declared rectangle fits vertically. -/
  fitsY : ∀ i, dy i + (piece i).height ≤ H
  /-- Coincident local cells have the same wall marker. -/
  walls_compatible : ∀ i j (p : Cell (piece i).width (piece i).height)
      (q : Cell (piece j).width (piece j).height),
    (dx i + p.1.val, dy i + p.2.val) = (dx j + q.1.val, dy j + q.2.val) →
      (p ∈ (piece i).board.walls ↔ q ∈ (piece j).board.walls)
  /-- Different local source identities have different atlas owners. -/
  source_owners : ∀ i j (l : Label i) (k : Label j),
    (dx i + ((matching i).source l).1.val, dy i + ((matching i).source l).2.val) =
      (dx j + ((matching j).source k).1.val, dy j + ((matching j).source k).2.val) → i = j
  /-- Different local target identities have different atlas owners. -/
  target_owners : ∀ i j (l : Label i) (k : Label j),
    (dx i + ((matching i).target l).1.val, dy i + ((matching i).target l).2.val) =
      (dx j + ((matching j).target k).1.val, dy j + ((matching j).target k).2.val) → i = j
  /-- The one global player coordinate. -/
  player : Cell W H
  /-- The player lies outside every actual wall. -/
  player_floor : ∀ i p, p ∈ (piece i).board.walls →
    (player.1.val, player.2.val) ≠ (dx i + p.1.val, dy i + p.2.val)
  /-- The player lies outside every actual initial physical slot. -/
  player_empty : ∀ i l,
    (player.1.val, player.2.val) ≠
      (dx i + ((matching i).source l).1.val, dy i + ((matching i).source l).2.val)

namespace StorageAtlas

open scoped Classical

variable {n W H : ℕ} {Label : Fin n → Type} [∀ i, Fintype (Label i)]

/-- The actual translation of one complete glyph rectangle. -/
def embedding (A : StorageAtlas n W H Label) (i : Fin n) :
    GridEmbedding (A.piece i).width (A.piece i).height W H :=
  GridEmbedding.translate (A.dx i) (A.dy i) (A.fitsX i) (A.fitsY i)

@[simp] theorem embedding_x (A : StorageAtlas n W H Label) (i : Fin n)
    (p : Cell (A.piece i).width (A.piece i).height) :
    ((A.embedding i).cells p).1.val = A.dx i + p.1.val := rfl

@[simp] theorem embedding_y (A : StorageAtlas n W H Label) (i : Fin n)
    (p : Cell (A.piece i).width (A.piece i).height) :
    ((A.embedding i).cells p).2.val = A.dy i + p.2.val := rfl

/-- A single physical identity across all glyphs. -/
abbrev PhysicalLabel (_A : StorageAtlas n W H Label) := (i : Fin n) × Label i

/-- Every physical initial slot, with cross-glyph ownership proved. -/
def source (A : StorageAtlas n W H Label) : A.PhysicalLabel ↪ Cell W H where
  toFun l := (A.embedding l.1).cells ((A.matching l.1).source l.2)
  inj' := by
    rintro ⟨i, l⟩ ⟨j, k⟩ he
    have hij := A.source_owners i j l k (by
      simpa only [embedding_x, embedding_y] using
        congrArg (fun p : Cell W H => (p.1.val, p.2.val)) he)
    subst j
    have hlk := (A.matching i).source.injective ((A.embedding i).cells.injective he)
    exact congrArg (Sigma.mk i) hlk

/-- Every physical target slot, with cross-glyph ownership proved. -/
def target (A : StorageAtlas n W H Label) : A.PhysicalLabel ↪ Cell W H where
  toFun l := (A.embedding l.1).cells ((A.matching l.1).target l.2)
  inj' := by
    rintro ⟨i, l⟩ ⟨j, k⟩ he
    have hij := A.target_owners i j l k (by
      simpa only [embedding_x, embedding_y] using
        congrArg (fun p : Cell W H => (p.1.val, p.2.val)) he)
    subst j
    have hlk := (A.matching i).target.injective ((A.embedding i).cells.injective he)
    exact congrArg (Sigma.mk i) hlk

/-- Every wall of every actual oriented glyph, with overlapping cells unioned. -/
def walls (A : StorageAtlas n W H Label) : Finset (Cell W H) :=
  Finset.univ.biUnion fun i => (A.piece i).board.walls.map (A.embedding i).cells

/-- Complete global walls and all unlabelled targets. -/
def board (A : StorageAtlas n W H Label) : Board W H :=
  ⟨A.walls, Finset.univ.map A.target⟩

/-- The one actual player and all unlabelled physical boxes. -/
def initial (A : StorageAtlas n W H Label) : State W H :=
  ⟨A.player, Finset.univ.map A.source⟩

/-- Rectangle overlap compatibility gives exact local-to-global wall agreement. -/
theorem walls_agree (A : StorageAtlas n W H Label) (i : Fin n) :
    (A.embedding i).WallsAgree (A.piece i).board A.board := by
  intro p
  constructor
  · intro hp
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hj
    apply (A.walls_compatible i j p q ?_).mpr hq
    simpa only [embedding_x, embedding_y] using
      congrArg (fun p : Cell W H => (p.1.val, p.2.val)) he.symm
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_map.mpr ⟨p, hp, rfl⟩⟩

private theorem source_mem (A : StorageAtlas n W H Label) (i : Fin n) (l : Label i) :
    (A.matching i).source l ∈ (A.piece i).initial.boxes := by
  rw [← (A.matching i).source_image]
  exact Finset.mem_map.mpr ⟨l, Finset.mem_univ _, rfl⟩

private theorem target_mem (A : StorageAtlas n W H Label) (i : Fin n) (l : Label i) :
    (A.matching i).target l ∈ (A.piece i).board.goals := by
  rw [← (A.matching i).target_image]
  exact Finset.mem_map.mpr ⟨l, Finset.mem_univ _, rfl⟩

/-- The global box set is exactly the union of all actual local box sets. -/
theorem mem_boxes_iff (A : StorageAtlas n W H Label) (p : Cell W H) :
    p ∈ A.initial.boxes ↔ ∃ i q, q ∈ (A.piece i).initial.boxes ∧ (A.embedding i).cells q = p := by
  constructor
  · intro hp
    obtain ⟨⟨i, l⟩, _, rfl⟩ := Finset.mem_map.mp hp
    exact ⟨i, (A.matching i).source l, A.source_mem i l, rfl⟩
  · rintro ⟨i, q, hq, rfl⟩
    rw [← (A.matching i).source_image] at hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_map.mpr ⟨⟨i, l⟩, Finset.mem_univ _, rfl⟩

/-- The global unlabelled targets are exactly the union of all local target sets. -/
theorem mem_goals_iff (A : StorageAtlas n W H Label) (p : Cell W H) :
    p ∈ A.board.goals ↔ ∃ i q, q ∈ (A.piece i).board.goals ∧ (A.embedding i).cells q = p := by
  constructor
  · intro hp
    obtain ⟨⟨i, l⟩, _, rfl⟩ := Finset.mem_map.mp hp
    exact ⟨i, (A.matching i).target l, A.target_mem i l, rfl⟩
  · rintro ⟨i, q, hq, rfl⟩
    rw [← (A.matching i).target_image] at hq
    obtain ⟨l, _, rfl⟩ := Finset.mem_map.mp hq
    exact Finset.mem_map.mpr ⟨⟨i, l⟩, Finset.mem_univ _, rfl⟩

/-- Every target is floor on the complete union board. -/
theorem goals_floor (A : StorageAtlas n W H Label) : Disjoint A.board.walls A.board.goals := by
  apply Finset.disjoint_left.mpr
  intro p hp hg
  obtain ⟨⟨i, l⟩, _, rfl⟩ := Finset.mem_map.mp hg
  exact Finset.disjoint_left.mp (A.piece i).goals_floor
    ((A.walls_agree i _).mp hp) (A.target_mem i l)

/-- All initial actors are legal on the actual union of glyph walls. -/
theorem initial_valid (A : StorageAtlas n W H Label) : A.initial.Valid A.board := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    obtain ⟨i, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q, hq, he⟩ := Finset.mem_map.mp hp
    apply A.player_floor i q hq
    change (A.embedding i).cells q = A.player at he
    simpa only [embedding_x, embedding_y] using
      congrArg (fun p : Cell W H => (p.1.val, p.2.val)) he.symm
  · apply Finset.disjoint_left.mpr
    intro p hp hw
    obtain ⟨⟨i, l⟩, _, rfl⟩ := Finset.mem_map.mp hp
    exact Finset.disjoint_left.mp (A.piece i).initial_valid.2.1
      (A.source_mem i l) ((A.walls_agree i _).mp hw)
  · intro hp
    obtain ⟨⟨i, l⟩, _, he⟩ := Finset.mem_map.mp hp
    apply A.player_empty i l
    change (A.embedding i).cells ((A.matching i).source l) = A.player at he
    simpa only [embedding_x, embedding_y] using
      congrArg (fun p : Cell W H => (p.1.val, p.2.val)) he.symm

/-- The complete physical storage puzzle, with no goal identity added to its semantics. -/
def puzzle (A : StorageAtlas n W H Label) : Instance where
  width := W
  height := H
  board := A.board
  initial := A.initial
  goals_floor := A.goals_floor
  initial_valid := A.initial_valid
  boxes_eq_goals := by simp only [initial, board, Finset.card_map]

/-- Every physical box retains its local source-to-target static component after assembly. -/
def slotMatching (A : StorageAtlas n W H Label) : SlotMatching A.puzzle A.PhysicalLabel where
  source := A.source
  target := A.target
  source_image := rfl
  target_image := rfl
  connected l := ⟨GridEmbedding.staticReach (A.walls_agree l.1) ((A.matching l.1).connected l.2).1,
    GridEmbedding.staticReach (A.walls_agree l.1) ((A.matching l.1).connected l.2).2⟩

end StorageAtlas
end PushPuzzle.PushFS.Reduction
