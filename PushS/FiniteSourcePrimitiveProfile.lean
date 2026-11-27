/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceProfile

/-! Actual primitive-by-primitive inventories inside one source-tile update. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PrimitiveProfile

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL
open scoped Classical

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes Raster.width Raster.height

/-- Every actual emitted primitive is independently at its literal source or target slots. -/
def position (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (l : (inventory w hw v).PhysicalLabel) :
    Cell (width w v) (height w v) :=
  if phase l.1 then (inventory w hw v).target l else (inventory w hw v).source l

/-- The complete actual physical stock during a primitive update sequence. -/
noncomputable def boxes (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) : Finset (Cell (width w v) (height w v)) :=
  Finset.univ.image (position w hw v phase)

/-- Actual primitive stock, with the specified real player cell. -/
noncomputable def state (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (player : Cell (width w v) (height w v)) :
    State (width w v) (height w v) := ⟨player,boxes w hw v phase⟩

/-- The actual physical identities not participating in the selected local macro. -/
noncomputable def outside (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (selected : Finset (inventory w hw v).PhysicalLabel) :
    Finset (Cell (width w v) (height w v)) :=
  (Finset.univ \ selected).image (position w hw v phase)

/-- Every complete physical inventory splits at an arbitrary real local identity selection. -/
private theorem split (phase : Fin (codes w v).length → Bool)
    (selected : Finset (inventory w hw v).PhysicalLabel) :
    boxes w hw v phase = selected.image (position w hw v phase) ∪ outside w hw v phase selected := by
  unfold boxes outside
  rw [← Finset.image_union]
  congr 1
  ext l
  simp

/-- Selecting the entire owner primitive keeps the actual unselected global stock fixed. -/
private theorem outside_update (phase : Fin (codes w v).length → Bool) (i : Fin (codes w v).length)
    (selected : Finset (inventory w hw v).PhysicalLabel)
    (hcover : (inventory w hw v).pieceLabels i ⊆ selected) :
    outside w hw v (Function.update phase i true) selected = outside w hw v phase selected := by
  apply Finset.image_congr
  intro l hl
  have hn : l.1 ≠ i := by
    intro he
    exact (Finset.mem_sdiff.mp hl).2 (hcover ((inventory w hw v).mem_pieceLabels i l |>.mpr he))
  simp only [position,Function.update_of_ne hn]

/-- Every source/target primitive mixture remains literal floor on the actual emitted global board. -/
theorem floor (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool) :
    Disjoint (boxes w hw v phase) (inventory w hw v).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hm
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  unfold position at hm
  split at hm
  · exact ha.target_floor l hm
  · exact ha.source_floor l hm

/-- The actual remaining stock has global floor independently of the current local macro. -/
theorem outside_floor (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (selected : Finset (inventory w hw v).PhysicalLabel) :
    Disjoint (outside w hw v phase selected) (inventory w hw v).walls := by
  apply (floor ha phase).mono_left
  intro p hp
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩

/-- All interfaces from neighboring owners are retained explicitly in the selected local inventory. -/
private theorem selected_slots {α : Type} [Fintype α] {a b : ℕ}
    (phase : Fin (codes w v).length → Bool) (labels : α ↪ (inventory w hw v).PhysicalLabel)
    (e : GridEmbedding a b (width w v) (height w v)) (slots : α → Cell a b)
    (hslots : ∀ l,position w hw v phase (labels l) = e.cells (slots l)) :
    (Finset.univ.map labels).image (position w hw v phase) = (Finset.univ.image slots).map e.cells := by
  simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def]
  exact congrArg (Finset.image · Finset.univ) (funext hslots)

/-- Lift a concrete local primitive run to the exact complete current and next actual global stocks. -/
theorem selection_run {α : Type} [Fintype α] {a b : ℕ}
    (phase : Fin (codes w v).length → Bool) (i : Fin (codes w v).length)
    (labels : α ↪ (inventory w hw v).PhysicalLabel)
    (hcover : (inventory w hw v).pieceLabels i ⊆ Finset.univ.map labels)
    (e : GridEmbedding a b (width w v) (height w v)) (initial final : α → Cell a b)
    (hinitial : ∀ l,position w hw v phase (labels l) = e.cells (initial l))
    (hfinal : ∀ l,position w hw v (Function.update phase i true) (labels l) = e.cells (final l))
    (B : Board (width w v) (height w v)) (p q : Cell a b)
    (hr : Reachable B (some 1)
      (e.extend (outside w hw v phase (Finset.univ.map labels)) ⟨p,Finset.univ.image initial⟩)
      (e.extend (outside w hw v phase (Finset.univ.map labels)) ⟨q,Finset.univ.image final⟩)) :
    Reachable B (some 1) (state w hw v phase (e.cells p))
      (state w hw v (Function.update phase i true) (e.cells q)) := by
  have hsi := (split phase (Finset.univ.map labels)).trans
    (congrArg (· ∪ outside w hw v phase (Finset.univ.map labels))
      (selected_slots phase labels e initial hinitial))
  have hsf := split (Function.update phase i true) (Finset.univ.map labels)
  rw [outside_update phase i _ hcover,selected_slots _ labels e final hfinal] at hsf
  change Reachable B (some 1) ⟨e.cells p,_⟩ ⟨e.cells q,_⟩ at hr
  change Reachable B (some 1) ⟨e.cells p,_⟩ ⟨e.cells q,_⟩
  simpa only [hsi,hsf] using hr

/-- Idle primitives whose actual slots agree need no physical move during a selected-edge traversal. -/
theorem idle (phase : Fin (codes w v).length → Bool) (i : Fin (codes w v).length)
    (hc : (((codes w v).get i).2).SamePhase) (player : Cell (width w v) (height w v)) :
    state w hw v phase player = state w hw v (Function.update phase i true) player := by
  apply State.ext
  · rfl
  · change Finset.univ.image (position w hw v phase) = Finset.univ.image (position w hw v (Function.update phase i true))
    congr 1
    funext l
    by_cases hi : l.1 = i
    · have he : (inventory w hw v).source l = (inventory w hw v).target l := by
        rcases l with ⟨j,l⟩
        dsimp at hi
        subst j
        apply congrArg ((inventory w hw v).embedding i).cells
        exact PrimitiveCode.matching_samePhase w hw _ hc l
      simp only [position,hi,Function.update_self,he,ite_self]
    · simp only [position,Function.update_of_ne hi]

end PushPuzzle.PushS.FiniteSourceInventory.PrimitiveProfile
