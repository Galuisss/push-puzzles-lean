/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCore
public import PushS.FiniteGateState
public import PushS.FiniteFlipMacros
public import PushS.FiniteTurnMacros
import Mathlib.Tactic.FinCases

/-! The real AND protection turn, upper turn, and flip placements. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateTools

set_option maxRecDepth 8192

open PushFS FiniteGeometry FiniteGateCore
open FiniteGateState
open FiniteTools (radius flipActive flipMacroBoard turnActive turnMacroBoard)

def s (w : ℕ) : ℕ := origin w-6*w-9
def t (w : ℕ) : ℕ := origin w-6*w-21
def flipY (w : ℕ) : ℕ := origin w-3*w-9

/-- Reflect the standard corner about its actual protection anchor `(s,0)`. -/
def protectionEmbedding (w : ℕ) :
    GridEmbedding (FiniteTools.side w) (FiniteTools.side w) (side w) (side w) where
  cells := {
    toFun p :=
      (⟨s w+radius w-p.1.val, by unfold s radius origin side; omega⟩,
       ⟨origin w+radius w-p.2.val, by unfold radius origin side; omega⟩)
    inj' := by
      intro p q he
      have hpX := p.1.isLt
      have hpY := p.2.isLt
      have hqX := q.1.isLt
      have hqY := q.2.isLt
      have hx := congrArg (fun r : Cell (side w) (side w) => r.1.val) he
      have hy := congrArg (fun r : Cell (side w) (side w) => r.2.val) he
      dsimp at hx hy
      apply Prod.ext <;> apply Fin.ext <;>
        dsimp [s, radius, origin, FiniteTools.side] at * <;> omega }
  direction := Direction.opposite
  adjacent := by
    intro d p q ha
    have hpX := p.1.isLt
    have hpY := p.2.isLt
    have hqX := q.1.isLt
    have hqY := q.2.isLt
    cases d <;> simp [Adjacent, Direction.opposite] at ha ⊢ <;>
      dsimp [s, radius, origin, FiniteTools.side] at * <;> omega

/-- The standard upper corner is translated to the actual western roof anchor. -/
def upperEmbedding (w : ℕ) :
    GridEmbedding (FiniteTools.side w) (FiniteTools.side w) (side w) (side w) :=
  GridEmbedding.translate (s w-radius w) (t w-radius w)
    (by simp only [s, radius, origin, side, FiniteTools.side]; omega)
    (by simp only [t, radius, origin, side, FiniteTools.side]; omega)

def flipDirection : Direction → Direction
  | .north => .east
  | .east => .north
  | .south => .west
  | .west => .south

/-- Rotate and reflect the standard flip to the actual vertical AND input branch. -/
def flipEmbedding (w : ℕ) :
    GridEmbedding (FiniteTools.side w) (FiniteTools.side w) (side w) (side w) where
  cells := {
    toFun p :=
      (⟨s w+radius w-p.2.val, by unfold s radius origin side; omega⟩,
       ⟨flipY w+radius w-p.1.val, by unfold flipY radius origin side; omega⟩)
    inj' := by
      intro p q he
      have hpX := p.1.isLt
      have hpY := p.2.isLt
      have hqX := q.1.isLt
      have hqY := q.2.isLt
      have hx := congrArg (fun r : Cell (side w) (side w) => r.1.val) he
      have hy := congrArg (fun r : Cell (side w) (side w) => r.2.val) he
      dsimp at hx hy
      apply Prod.ext <;> apply Fin.ext <;>
        dsimp [s, flipY, radius, origin, FiniteTools.side] at * <;> omega }
  direction := flipDirection
  adjacent := by
    intro d p q ha
    have hpX := p.1.isLt
    have hpY := p.2.isLt
    have hqX := q.1.isLt
    have hqY := q.2.isLt
    cases d <;> simp [Adjacent, flipDirection] at ha ⊢ <;>
      dsimp [s, flipY, radius, origin, FiniteTools.side] at * <;> omega

attribute [local irreducible] FiniteGeometry.side FiniteTools.side

private theorem protection_floor (w : ℕ) (hw : 2 ≤ w) (p : Cell (FiniteTools.side w)
    (FiniteTools.side w))
    (hp : p ∈ turnActive w) : (protectionEmbedding w).cells p ∉ andWalls w := by
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  intro hg
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
  have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> simp [andRectangle, protectionEmbedding, s, radius, origin] at hi' <;>
    dsimp [radius] at hp' <;> omega

private theorem upper_floor (w : ℕ) (hw : 2 ≤ w) (p : Cell (FiniteTools.side w)
    (FiniteTools.side w))
    (hp : p ∈ turnActive w) : (upperEmbedding w).cells p ∉ andWalls w := by
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  intro hg
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
  have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;>
    simp [andRectangle, upperEmbedding, GridEmbedding.translate, s, t, radius, origin] at hi' <;>
    dsimp [radius] at hp' <;> omega

set_option maxHeartbeats 400000 in
private theorem flip_floor (w : ℕ) (hw : 2 ≤ w) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ flipActive w) : (flipEmbedding w).cells p ∉ andWalls w := by
  obtain ⟨hxl, hxh, hyl, hyh, hfree⟩ := (Finset.mem_filter.mp hp).2
  intro hg
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hg
  have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;>
    simp [andRectangle, flipEmbedding, s, flipY, radius, origin] at hi' <;>
    dsimp [radius] at hxl hxh hyl hyh
  all_goals first
    | omega
    | apply hfree; apply Finset.mem_biUnion.mpr
      refine ⟨0, Finset.mem_univ _, ?_⟩
      apply (Rectangle.mem_cells _ _ _ _).mpr
      simp [FiniteTools.flipRectangle, radius]
      omega
    | apply hfree; apply Finset.mem_biUnion.mpr
      refine ⟨1, Finset.mem_univ _, ?_⟩
      apply (Rectangle.mem_cells _ _ _ _).mpr
      simp [FiniteTools.flipRectangle, radius]
      omega
    | apply hfree; apply Finset.mem_biUnion.mpr
      refine ⟨2, Finset.mem_univ _, ?_⟩
      apply (Rectangle.mem_cells _ _ _ _).mpr
      simp [FiniteTools.flipRectangle, radius]
      omega
    | apply hfree; apply Finset.mem_biUnion.mpr
      refine ⟨3, Finset.mem_univ _, ?_⟩
      apply (Rectangle.mem_cells _ _ _ _).mpr
      simp [FiniteTools.flipRectangle, radius]
      omega

/-- The actual physical boxes shared with the protection turn. -/
def protectionLabel (w : ℕ) : FiniteTools.TurnLabel → AndLabel w
  | .predecessor => .guard 1
  | .horizontal => .guard 0
  | .vertical => .lower ⟨w+4, by omega⟩
  | .successor => .lower ⟨w+3, by omega⟩

def protectionPhases (w : ℕ) (X : AndPhases w) (q : Bool) : AndPhases w :=
  { X with
    guard := Function.update (Function.update X.guard 1 false) 0 q
    lower := Function.update (Function.update X.lower ⟨w+3, by omega⟩ true) ⟨w+4, by omega⟩ q }

/-- The actual shared boxes at the upper concave turn. -/
def upperLabel (w : ℕ) : FiniteTools.TurnLabel → AndLabel w
  | .predecessor => .west 1
  | .horizontal => .west 0
  | .vertical => .upper 0
  | .successor => .upper 1

def upperPhases (w : ℕ) (X : AndPhases w) (q : Bool) : AndPhases w :=
  { X with
    west := Function.update (Function.update X.west 1 true) 0 (!q)
    upper := Function.update (Function.update X.upper 1 false) 0 (!q) }

/-- The two neighbors and all three working boxes of the vertical thick flip. -/
def flipLabel (w : ℕ) : FiniteTools.FlipLabel → AndLabel w
  | .predecessor => .lower 1
  | .left => .lower 0
  | .middle => .middle
  | .right => .upper ⟨w+4, by omega⟩
  | .successor => .upper ⟨w+3, by omega⟩

def flipPhases (w : ℕ) (X : AndPhases w) (q : Bool) : AndPhases w :=
  { X with
    lower := Function.update (Function.update X.lower 1 false) 0 q
    upper := Function.update (Function.update X.upper ⟨w+3, by omega⟩ true) ⟨w+4, by omega⟩ q
    middle := ⟨3*q.toNat, by have := Bool.toNat_le q; omega⟩ }

private theorem protection_slot (w : ℕ) (X : AndPhases w) (q : Bool) (l : FiniteTools.TurnLabel) :
    andMixedCell w (protectionPhases w X q) (protectionLabel w l) =
      (protectionEmbedding w).cells (FiniteTools.turnMixedCell w q q l) := by
  have hq := Bool.toNat_le q
  cases l <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [andMixedCell, protectionPhases, protectionLabel, protectionEmbedding,
      FiniteTools.turnMixedCell, FiniteTools.turnMixedPoint, andCell, andPoint,
      Function.update, s, radius, origin] <;> omega

private theorem upper_slot (w : ℕ) (X : AndPhases w) (q : Bool) (l : FiniteTools.TurnLabel) :
    andMixedCell w (upperPhases w X q) (upperLabel w l) =
      (upperEmbedding w).cells (FiniteTools.turnMixedCell w q q l) := by
  cases q <;> cases l <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [andMixedCell, upperPhases, upperLabel, upperEmbedding, GridEmbedding.translate,
      FiniteTools.turnMixedCell, FiniteTools.turnMixedPoint, andCell, andPoint,
      Function.update, s, t, radius, origin] <;> omega

private theorem flip_slot (w : ℕ) (X : AndPhases w) (q : Bool) (l : FiniteTools.FlipLabel) :
    andMixedCell w (flipPhases w X q) (flipLabel w l) =
      (flipEmbedding w).cells (FiniteTools.flipCell w q l) := by
  have hq := Bool.toNat_le q
  cases l <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [andMixedCell, flipPhases, flipLabel, flipEmbedding, FiniteTools.flipCell,
      FiniteTools.flipPoint, andCell, andPoint, Function.update, s, flipY, radius, origin] <;> omega

theorem andMixedCell_floor (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (l : AndLabel w) :
    andMixedCell w X l ∉ andWalls w := by
  cases l with
  | west i => exact andCell_not_wall w hw _ _ _ _
  | upper i => exact andCell_not_wall w hw _ _ _ _
  | lower i => exact andCell_not_wall w hw _ _ _ _
  | guard i => exact andCell_not_wall w hw _ _ _ _
  | branchB i => exact andCell_not_wall w hw _ _ _ _
  | branchC i => exact andCell_not_wall w hw _ _ _ _
  | middle =>
    intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
    have hm := X.middle.isLt
    fin_cases i <;> simp [andRectangle, andMixedCell, origin] at hi' <;> omega
  | triggerA =>
    intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
    have hm := X.triggerA.isLt
    fin_cases i <;> simp [andRectangle, andMixedCell, origin] at hi' <;> omega

/-- The rest of the physical inventory excludes shared tool boxes by their actual source labels. -/
def outside {L : Type} [Fintype L] (w : ℕ) (X : AndPhases w) (label : L → AndLabel w) :
    Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => l ∉ Finset.univ.image label).image (andMixedCell w X)

private theorem outside_floor {L : Type} [Fintype L] (w : ℕ) (hw : 2 ≤ w)
    (X : AndPhases w) (label : L → AndLabel w) : Disjoint (outside w X label) (andWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact andMixedCell_floor w hw X l

private theorem protection_rest (w : ℕ) (X : AndPhases w) (q : Bool) (l : AndLabel w)
    (hl : l ∉ Finset.univ.image (protectionLabel w)) :
    andMixedCell w (protectionPhases w X q) l = andMixedCell w X l := by
  have hsel (i) : protectionLabel w i ∈ Finset.univ.image (protectionLabel w) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  cases l with
  | guard i =>
    have h0 : i ≠ 0 := by intro he; subst i; exact hl (hsel .horizontal)
    have h1 : i ≠ 1 := by intro he; subst i; exact hl (hsel .predecessor)
    simp [andMixedCell, protectionPhases, Function.update, h0, h1]
  | lower i =>
    have h0 : i ≠ ⟨w+4, by omega⟩ := by intro he; subst i; exact hl (hsel .vertical)
    have h1 : i ≠ ⟨w+3, by omega⟩ := by intro he; subst i; exact hl (hsel .successor)
    simp [andMixedCell, protectionPhases, Function.update, h0, h1]
  | _ => rfl

private theorem upper_rest (w : ℕ) (X : AndPhases w) (q : Bool) (l : AndLabel w)
    (hl : l ∉ Finset.univ.image (upperLabel w)) :
    andMixedCell w (upperPhases w X q) l = andMixedCell w X l := by
  have hsel (i) : upperLabel w i ∈ Finset.univ.image (upperLabel w) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  cases l with
  | west i =>
    have h0 : i ≠ 0 := by intro he; subst i; exact hl (hsel .horizontal)
    have h1 : i ≠ 1 := by intro he; subst i; exact hl (hsel .predecessor)
    simp [andMixedCell, upperPhases, Function.update, h0, h1]
  | upper i =>
    have h0 : i ≠ 0 := by intro he; subst i; exact hl (hsel .vertical)
    have h1 : i ≠ 1 := by intro he; subst i; exact hl (hsel .successor)
    simp [andMixedCell, upperPhases, Function.update, h0, h1]
  | _ => rfl

private theorem flip_rest (w : ℕ) (X : AndPhases w) (q : Bool) (l : AndLabel w)
    (hl : l ∉ Finset.univ.image (flipLabel w)) :
    andMixedCell w (flipPhases w X q) l = andMixedCell w X l := by
  have hsel (i) : flipLabel w i ∈ Finset.univ.image (flipLabel w) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  cases l with
  | lower i =>
    have h0 : i ≠ 0 := by intro he; subst i; exact hl (hsel .left)
    have h1 : i ≠ 1 := by intro he; subst i; exact hl (hsel .predecessor)
    simp [andMixedCell, flipPhases, Function.update, h0, h1]
  | upper i =>
    have h0 : i ≠ ⟨w+4, by omega⟩ := by intro he; subst i; exact hl (hsel .right)
    have h1 : i ≠ ⟨w+3, by omega⟩ := by intro he; subst i; exact hl (hsel .successor)
    simp [andMixedCell, flipPhases, Function.update, h0, h1]
  | middle => exact False.elim (hl (hsel .middle))
  | _ => rfl

private theorem image_split {α β γ δ : Type} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (label : α → β) (f g : β → δ) (localCell : α → γ) (e : γ ↪ δ)
    (hslot : ∀ i, g (label i) = e (localCell i))
    (hrest : ∀ l, l ∉ Finset.univ.image label → g l = f l) :
    Finset.univ.image g = (Finset.univ.image localCell).map e ∪
      (Finset.univ.filter fun l => l ∉ Finset.univ.image label).image f := by
  ext p
  constructor
  · intro hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases hl : l ∈ Finset.univ.image label
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hl
      apply Finset.mem_union_left
      exact Finset.mem_map.mpr ⟨localCell i,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, (hslot i).symm⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩,
        (hrest l hl).symm⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_image.mpr ⟨label i, Finset.mem_univ _, hslot i⟩
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, hrest l (Finset.mem_filter.mp hl).2⟩

theorem protection_inventory (w : ℕ) (X : AndPhases w) (q : Bool) :
    andMixedBoxes w (protectionPhases w X q) =
      (FiniteTools.turnBoxes w q).map (protectionEmbedding w).cells ∪ outside w X (protectionLabel w) :=
  image_split _ _ _ _ _ (protection_slot w X q) (protection_rest w X q)

theorem upper_inventory (w : ℕ) (X : AndPhases w) (q : Bool) :
    andMixedBoxes w (upperPhases w X q) =
      (FiniteTools.turnBoxes w q).map (upperEmbedding w).cells ∪ outside w X (upperLabel w) :=
  image_split _ _ _ _ _ (upper_slot w X q) (upper_rest w X q)

theorem flip_inventory (w : ℕ) (X : AndPhases w) (q : Bool) :
    andMixedBoxes w (flipPhases w X q) =
      (FiniteTools.flipBoxes w q).map (flipEmbedding w).cells ∪ outside w X (flipLabel w) :=
  image_split _ _ _ _ _ (flip_slot w X q) (flip_rest w X q)

theorem protection_region (w : ℕ) {p : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hp : p ∈ turnActive w) :
    s w ≤ ((protectionEmbedding w).cells p).1.val ∧
      ((protectionEmbedding w).cells p).1.val ≤ s w+4 ∧
      origin w-4 ≤ ((protectionEmbedding w).cells p).2.val ∧
      ((protectionEmbedding w).cells p).2.val ≤ origin w := by
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  simp [protectionEmbedding, s, origin, radius] at hp' ⊢
  omega

theorem upper_region (w : ℕ) {p : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hp : p ∈ turnActive w) :
    s w-4 ≤ ((upperEmbedding w).cells p).1.val ∧ ((upperEmbedding w).cells p).1.val ≤ s w ∧
      t w ≤ ((upperEmbedding w).cells p).2.val ∧ ((upperEmbedding w).cells p).2.val ≤ t w+4 := by
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  simp [upperEmbedding, GridEmbedding.translate, s, t, origin, radius] at hp' ⊢
  omega

theorem flip_region (w : ℕ) {p : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hp : p ∈ flipActive w) :
    s w-w-1 ≤ ((flipEmbedding w).cells p).1.val ∧
      ((flipEmbedding w).cells p).1.val ≤ s w+w+1 ∧
      flipY w-w-5 ≤ ((flipEmbedding w).cells p).2.val ∧
      ((flipEmbedding w).cells p).2.val ≤ flipY w+w+2 := by
  obtain ⟨hxl, hxh, hyl, hyh, _⟩ := (Finset.mem_filter.mp hp).2
  simp [flipEmbedding, s, flipY, origin, radius] at hxl hxh hyl hyh ⊢
  omega

private theorem protection_outside_avoids (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ turnActive w) :
    (protectionEmbedding w).cells p ∉ outside w X (protectionLabel w) := by
  intro hf
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hf
  have hn := (Finset.mem_filter.mp hl).2
  have hsel (i) : protectionLabel w i ∈ Finset.univ.image (protectionLabel w) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hr := protection_region w hp
  rw [← he] at hr
  cases l with
  | guard i =>
    have h0 : i.val ≠ 0 := by intro hv; have he : i = 0 := Fin.ext hv; subst i; exact hn (hsel .horizontal)
    have h1 : i.val ≠ 1 := by intro hv; have he : i = 1 := Fin.ext hv; subst i; exact hn (hsel .predecessor)
    have hb := Bool.toNat_le (X.guard i)
    dsimp [andMixedCell, andCell, andPoint, s, origin] at hr
    omega
  | lower i =>
    have h0 : i.val ≠ w+4 := by
      intro hv
      have he : i = ⟨w+4, by omega⟩ := Fin.ext hv
      apply hn
      refine Finset.mem_image.mpr ⟨.vertical, Finset.mem_univ _, ?_⟩
      exact congrArg AndLabel.lower he.symm
    have h1 : i.val ≠ w+3 := by
      intro hv
      have he : i = ⟨w+3, by omega⟩ := Fin.ext hv
      apply hn
      refine Finset.mem_image.mpr ⟨.successor, Finset.mem_univ _, ?_⟩
      exact congrArg AndLabel.lower he.symm
    have hb := Bool.toNat_le (X.lower i)
    have hi := i.isLt
    dsimp [andMixedCell, andCell, andPoint, s, origin] at hr
    omega
  | west i =>
    have hb := Bool.toNat_le (X.west i)
    dsimp [andMixedCell, andCell, andPoint, s, origin] at hr
    omega
  | upper i =>
    have hb := Bool.toNat_le (X.upper i)
    have hi := i.isLt
    dsimp [andMixedCell, andCell, andPoint, s, origin] at hr
    omega
  | middle =>
    have hm := X.middle.isLt
    dsimp [andMixedCell, s, origin] at hr
    omega
  | triggerA =>
    have hm := X.triggerA.isLt
    dsimp [andMixedCell, s, origin] at hr
    omega
  | branchB i =>
    dsimp [andMixedCell, andCell, andPoint, s, origin] at hr
    omega
  | branchC i =>
    have hb := Bool.toNat_le (X.branchC i)
    dsimp [andMixedCell, andCell, andPoint, s, origin] at hr
    omega

theorem protection_frame (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteWireFrame.Frame (turnActive w) (protectionEmbedding w) (andBoard w goals)
      (outside w X (protectionLabel w)) :=
  ⟨protection_floor w hw, protection_outside_avoids w hw X, outside_floor w hw X _⟩

theorem protection_forward (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (protectionPhases w X false)⟩
      ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .horizontal0),
        andMixedBoxes w (protectionPhases w X true)⟩ := by
  have hh := FiniteTools.turn_forward_placed w (protectionEmbedding w) (protection_frame w hw X goals)
  simpa only [GridEmbedding.extend, protection_inventory] using hh

theorem protection_backward (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (protectionPhases w X true)⟩
      ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .vertical1),
        andMixedBoxes w (protectionPhases w X false)⟩ := by
  have hh := FiniteTools.turn_backward_placed w (protectionEmbedding w) (protection_frame w hw X goals)
  simpa only [GridEmbedding.extend, protection_inventory] using hh

private theorem upper_outside_avoids (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ turnActive w) :
    (upperEmbedding w).cells p ∉ outside w X (upperLabel w) := by
  intro hf
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hf
  have hn := (Finset.mem_filter.mp hl).2
  have hsel (i) : upperLabel w i ∈ Finset.univ.image (upperLabel w) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hr := upper_region w hp
  rw [← he] at hr
  cases l with
  | west i =>
    have h0 : i.val ≠ 0 := by intro hv; have he : i = 0 := Fin.ext hv; subst i; exact hn (hsel .horizontal)
    have h1 : i.val ≠ 1 := by intro hv; have he : i = 1 := Fin.ext hv; subst i; exact hn (hsel .predecessor)
    have hb := Bool.toNat_le (X.west i)
    have hi := i.isLt
    dsimp [andMixedCell, andCell, andPoint, s, t, origin] at hr
    omega
  | upper i =>
    have h0 : i.val ≠ 0 := by intro hv; have he : i = 0 := Fin.ext hv; subst i; exact hn (hsel .vertical)
    have h1 : i.val ≠ 1 := by intro hv; have he : i = 1 := Fin.ext hv; subst i; exact hn (hsel .successor)
    have hb := Bool.toNat_le (X.upper i)
    dsimp [andMixedCell, andCell, andPoint, s, t, origin] at hr
    omega
  | lower i =>
    have hb := Bool.toNat_le (X.lower i)
    dsimp [andMixedCell, andCell, andPoint, s, t, origin] at hr
    omega
  | guard i =>
    dsimp [andMixedCell, andCell, andPoint, s, t, origin] at hr
    omega
  | middle =>
    have hm := X.middle.isLt
    dsimp [andMixedCell, s, t, origin] at hr
    omega
  | triggerA =>
    dsimp [andMixedCell, s, t, origin] at hr
    omega
  | branchB i =>
    dsimp [andMixedCell, andCell, andPoint, s, t, origin] at hr
    omega
  | branchC i =>
    have hb := Bool.toNat_le (X.branchC i)
    dsimp [andMixedCell, andCell, andPoint, s, t, origin] at hr
    omega

theorem upper_frame (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteWireFrame.Frame (turnActive w) (upperEmbedding w) (andBoard w goals)
      (outside w X (upperLabel w)) :=
  ⟨upper_floor w hw, upper_outside_avoids w hw X, outside_floor w hw X _⟩

/-- Moving the upper turn forward changes its gate input phase from one to zero. -/
theorem upper_forward (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (upperPhases w X false)⟩
      ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .horizontal0),
        andMixedBoxes w (upperPhases w X true)⟩ := by
  have hh := FiniteTools.turn_forward_placed w (upperEmbedding w) (upper_frame w hw X goals)
  simpa only [GridEmbedding.extend, upper_inventory] using hh

theorem upper_backward (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (upperPhases w X true)⟩
      ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .vertical1),
        andMixedBoxes w (upperPhases w X false)⟩ := by
  have hh := FiniteTools.turn_backward_placed w (upperEmbedding w) (upper_frame w hw X goals)
  simpa only [GridEmbedding.extend, upper_inventory] using hh

private theorem flip_outside_avoids (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ flipActive w) :
    (flipEmbedding w).cells p ∉ outside w X (flipLabel w) := by
  intro hf
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hf
  have hn := (Finset.mem_filter.mp hl).2
  have hsel (i) : flipLabel w i ∈ Finset.univ.image (flipLabel w) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hr := flip_region w hp
  rw [← he] at hr
  cases l with
  | lower i =>
    have h0 : i.val ≠ 0 := by intro hv; have he : i = 0 := Fin.ext hv; subst i; exact hn (hsel .left)
    have h1 : i.val ≠ 1 := by intro hv; have he : i = 1 := Fin.ext hv; subst i; exact hn (hsel .predecessor)
    have hb := Bool.toNat_le (X.lower i)
    dsimp [andMixedCell, andCell, andPoint, s, flipY, origin] at hr
    omega
  | upper i =>
    have h0 : i.val ≠ w+4 := by
      intro hv
      have he : i = ⟨w+4, by omega⟩ := Fin.ext hv
      apply hn
      refine Finset.mem_image.mpr ⟨.right, Finset.mem_univ _, ?_⟩
      exact congrArg AndLabel.upper he.symm
    have h1 : i.val ≠ w+3 := by
      intro hv
      have he : i = ⟨w+3, by omega⟩ := Fin.ext hv
      apply hn
      refine Finset.mem_image.mpr ⟨.successor, Finset.mem_univ _, ?_⟩
      exact congrArg AndLabel.upper he.symm
    have hb := Bool.toNat_le (X.upper i)
    have hi := i.isLt
    dsimp [andMixedCell, andCell, andPoint, s, flipY, origin] at hr
    omega
  | middle => exact hn (hsel .middle)
  | west i =>
    dsimp [andMixedCell, andCell, andPoint, s, flipY, origin] at hr
    omega
  | guard i =>
    dsimp [andMixedCell, andCell, andPoint, s, flipY, origin] at hr
    omega
  | triggerA =>
    dsimp [andMixedCell, s, flipY, origin] at hr
    omega
  | branchB i =>
    dsimp [andMixedCell, andCell, andPoint, s, flipY, origin] at hr
    omega
  | branchC i =>
    have hb := Bool.toNat_le (X.branchC i)
    dsimp [andMixedCell, andCell, andPoint, s, flipY, origin] at hr
    omega

theorem flip_frame (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    FiniteWireFrame.Frame (flipActive w) (flipEmbedding w) (andBoard w goals)
      (outside w X (flipLabel w)) :=
  ⟨flip_floor w hw, flip_outside_avoids w hw X, outside_floor w hw X _⟩

theorem flip_forward (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .rightSupport),
        andMixedBoxes w (flipPhases w X false)⟩
      ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .left0),
        andMixedBoxes w (flipPhases w X true)⟩ := by
  have hh := FiniteTools.flip_forward_placed w hw (flipEmbedding w) (flip_frame w hw X goals)
  simpa only [GridEmbedding.extend, flip_inventory] using hh

theorem flip_backward (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .leftReverseSupport),
        andMixedBoxes w (flipPhases w X true)⟩
      ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .right1),
        andMixedBoxes w (flipPhases w X false)⟩ := by
  have hh := FiniteTools.flip_backward_placed w hw (flipEmbedding w) (flip_frame w hw X goals)
  simpa only [GridEmbedding.extend, flip_inventory] using hh

end PushPuzzle.PushS.FiniteGateTools
