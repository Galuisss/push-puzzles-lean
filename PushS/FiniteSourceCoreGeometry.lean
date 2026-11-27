/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreTracks

/-! Literal placement, walls and complete rails of the actual emitted core entry. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateMatching

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)

attribute [local irreducible] codes width height FiniteGeometry.side InventoryAssembly.board InventoryAssembly.walls

theorem fits : s.offsetX+FiniteGeometry.side w ≤ width w v ∧ s.offsetY+FiniteGeometry.side w ≤ height w v := by
  have hx := (inventory w hw v).fitsX s.index
  have hy := (inventory w hw v).fitsY s.index
  change tileStride w*((codes w v).get s.index).1.1+PrimitiveCode.offsetX w ((codes w v).get s.index).2+
    (PrimitiveCode.instanceOf w hw ((codes w v).get s.index).2).width ≤ width w v at hx
  change tileStride w*((codes w v).get s.index).1.2+PrimitiveCode.offsetY w ((codes w v).get s.index).2+
    (PrimitiveCode.instanceOf w hw ((codes w v).get s.index).2).height ≤ height w v at hy
  rw [s.code_eq] at hx hy
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind <;> constructor
  all_goals first
    | simpa only [PrimitiveCode.offsetX,PrimitiveCode.instanceOf,coreInstance,FiniteGateCore.andInstance,
        FiniteGateCore.orInstance,offsetX,Nat.add_assoc,Bool.false_eq_true,↓reduceIte] using hx
    | simpa only [PrimitiveCode.offsetY,PrimitiveCode.instanceOf,coreInstance,FiniteGateCore.andInstance,
        FiniteGateCore.orInstance,offsetY,Nat.add_assoc,Bool.false_eq_true,↓reduceIte] using hy

theorem embedding_translate (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    s.embedding.cells p = (GridEmbedding.translate s.offsetX s.offsetY s.fits.1 s.fits.2).cells p := by
  apply Prod.ext <;> apply Fin.ext
  · exact s.embedding_x p
  · exact s.embedding_y p

theorem andLabel_injective (hg : s.gate.core.isAND = true) : Function.Injective (s.andLabel hg) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact primitiveLabel_injective w hw v index (.core _) he

theorem orLabel_injective (hg : s.gate.core.isAND = false) : Function.Injective (s.orLabel hg) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact primitiveLabel_injective w hw v index (.core _) he
  · cases hg

theorem and_walls (hg : s.gate.core.isAND = true) (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ andWalls w) :
    s.embedding.cells p ∈ (inventory w hw v).board.walls := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · simp only [InventoryAssembly.board]
    exact wall_primitiveEmbedding w hw v index (.core _) he p hp

theorem or_walls (hg : s.gate.core.isAND = false) (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) (hp : p ∈ orWalls w) :
    s.embedding.cells p ∈ (inventory w hw v).board.walls := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · simp only [InventoryAssembly.board]
    exact wall_primitiveEmbedding w hw v index (.core _) he p hp
  · cases hg

theorem and_full_rail_floor (hg : s.gate.core.isAND = true) (r : FiniteCoreRails.AndRail) (i : Fin (r.count w)) :
    s.embedding.cells (r.cell w i) ∉ (inventory w hw v).board.walls := by
  simp only [InventoryAssembly.board]
  exact andFullRail_floor w hw v ((codes w v).get s.index).1 s.gate s.mem_codes hg r i _ (s.embedding_coordinates _)

theorem or_full_rail_floor (hg : s.gate.core.isAND = false) (r : FiniteCoreRails.OrRail) (i : Fin (r.count w)) :
    s.embedding.cells (r.cell w i) ∉ (inventory w hw v).board.walls := by
  simp only [InventoryAssembly.board]
  exact orFullRail_floor w hw v ((codes w v).get s.index).1 s.gate s.mem_codes hg r i _ (s.embedding_coordinates _)

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
