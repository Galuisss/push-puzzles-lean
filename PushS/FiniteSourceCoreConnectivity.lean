/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreRailFloor
public import PushS.FiniteSourceReadoutLabels
public import PushS.FiniteSourceLineGlyph

/-! Every actual core identity connects its arbitrary normal slots through its complete global support rail. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateMatching

attribute [local irreducible] codes width height FiniteGeometry.side InventoryAssembly.board InventoryAssembly.walls

structure CoreSite (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) where
  index : Fin (codes w v).length
  gate : GateTileState
  code_eq : ((codes w v).get index).2 = .core gate

namespace CoreSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)

def embedding : GridEmbedding (FiniteGeometry.side w) (FiniteGeometry.side w) (width w v) (height w v) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind <;> exact primitiveEmbedding w hw v index (.core _) he

def label (l : (PrimitiveCode.core s.gate).Labels w) : (inventory w hw v).PhysicalLabel :=
  primitiveLabel w hw v s.index (.core s.gate) s.code_eq l

def andLabel (hg : s.gate.core.isAND = true) (l : AndLabel w) : (inventory w hw v).PhysicalLabel := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact primitiveLabel w hw v index (.core _) he l

def orLabel (hg : s.gate.core.isAND = false) (l : OrLabel w) : (inventory w hw v).PhysicalLabel := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact primitiveLabel w hw v index (.core _) he l
  · cases hg

theorem and_source_actual (hg : s.gate.core.isAND = true) (l : AndLabel w) :
    (inventory w hw v).source (s.andLabel hg l) = s.embedding.cells
      (andCell w s.gate.core.initial.left s.gate.core.initial.upper s.gate.core.initial.right l) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact source_primitiveLabel w hw v index (.core _) he l

theorem and_target_actual (hg : s.gate.core.isAND = true) (l : AndLabel w) :
    (inventory w hw v).target (s.andLabel hg l) = s.embedding.cells
      (andCell w s.gate.core.target.left s.gate.core.target.upper s.gate.core.target.right l) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact target_primitiveLabel w hw v index (.core _) he l

theorem or_source_actual (hg : s.gate.core.isAND = false) (l : OrLabel w) :
    (inventory w hw v).source (s.orLabel hg l) = s.embedding.cells
      (orCell w s.gate.core.initial.left s.gate.core.initial.upper s.gate.core.initial.right l) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact source_primitiveLabel w hw v index (.core _) he l
  · cases hg

theorem or_target_actual (hg : s.gate.core.isAND = false) (l : OrLabel w) :
    (inventory w hw v).target (s.orLabel hg l) = s.embedding.cells
      (orCell w s.gate.core.target.left s.gate.core.target.upper s.gate.core.target.right l) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact target_primitiveLabel w hw v index (.core _) he l
  · cases hg

theorem mem_codes : (((codes w v).get s.index).1,PrimitiveCode.core s.gate) ∈ codes w v := by
  have he : (codes w v).get s.index = (((codes w v).get s.index).1,PrimitiveCode.core s.gate) :=
    Prod.ext rfl s.code_eq
  exact he ▸ List.get_mem (codes w v) s.index

theorem embedding_coordinates (p : Cell (FiniteGeometry.side w) (FiniteGeometry.side w)) :
    coordinates (s.embedding.cells p) = macroShift w ((codes w v).get s.index).1 (coreWorld w p) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  all_goals
    change coordinates ((primitiveEmbedding w hw v index (.core _) he).cells p) = _
    rw [primitiveEmbedding_coordinates w hw v index (.core _) he p]
    have hx : (inventory w hw v).dx index = tileStride w*((codes w v).get index).1.1+padding w+coreOffset w := by
      change tileStride w*((codes w v).get index).1.1+PrimitiveCode.offsetX w ((codes w v).get index).2 = _
      rw [he]
      simp only [PrimitiveCode.offsetX,Nat.add_assoc]
    have hy : (inventory w hw v).dy index = tileStride w*((codes w v).get index).1.2+padding w+coreOffset w := by
      change tileStride w*((codes w v).get index).1.2+PrimitiveCode.offsetY w ((codes w v).get index).2 = _
      rw [he]
      simp only [PrimitiveCode.offsetY,Nat.add_assoc]
    rw [hx,hy]
    simp only [shiftPoint,macroShift,coreWorld,coordinates,Nat.add_assoc]

private theorem and_rail_floor (hg : s.gate.core.isAND = true) (l : AndLabel w) (i : Fin
    (andTravel l+3)) :
    s.embedding.cells (andLine w l i) ∉ (inventory w hw v).board.walls := by
  simp only [InventoryAssembly.board]
  exact andRail_floor w hw v ((codes w v).get s.index).1 s.gate s.mem_codes hg l i _ (s.embedding_coordinates _)

private theorem or_rail_floor (hg : s.gate.core.isAND = false) (l : OrLabel w) (i : Fin 4) :
    s.embedding.cells (orLine w l i) ∉ (inventory w hw v).board.walls := by
  simp only [InventoryAssembly.board]
  exact orRail_floor w hw v ((codes w v).get s.index).1 s.gate s.mem_codes hg l i _ (s.embedding_coordinates _)

theorem and_normal_connected (hg : s.gate.core.isAND = true) (a b c a' b' c' : Bool) (l : AndLabel w) :
    SameComponent (inventory w hw v).board (s.embedding.cells (andCell w a b c l))
      (s.embedding.cells (andCell w a' b' c' l)) := by
  have hh := sameComponent_line (B := (inventory w hw v).board)
    (fun i => s.embedding.cells (andLine w l i)) (s.and_rail_floor hg l)
    (fun i => s.embedding.adjacent _ _ _ (andLine_adjacent w l i))
    (andSlotIndex l a b c) (andSlotIndex l a' b' c')
    (by dsimp [andSlotIndex]; split <;> cases l <;> simp [andTravel])
    (by dsimp [andSlotIndex]; split <;> cases l <;> simp [andTravel])
  simpa only [andLine_slot] using hh

theorem or_normal_connected (hg : s.gate.core.isAND = false) (a b c a' b' c' : Bool) (l : OrLabel w) :
    SameComponent (inventory w hw v).board (s.embedding.cells (orCell w a b c l))
      (s.embedding.cells (orCell w a' b' c' l)) := by
  have hh := sameComponent_line (B := (inventory w hw v).board)
    (fun i => s.embedding.cells (orLine w l i)) (s.or_rail_floor hg l)
    (fun i => s.embedding.adjacent _ _ _ (orLine_adjacent w l i))
    (orSlotIndex l a b c) (orSlotIndex l a' b' c')
    (by dsimp [orSlotIndex]; split <;> decide)
    (by dsimp [orSlotIndex]; split <;> decide)
  simpa only [orLine_slot] using hh

private theorem and_source_target_connected (hg : s.gate.core.isAND = true) (l : AndLabel w) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source (s.andLabel hg l))
      ((inventory w hw v).target (s.andLabel hg l)) := by
  rw [s.and_source_actual hg l,s.and_target_actual hg l]
  exact s.and_normal_connected hg _ _ _ _ _ _ l

private theorem or_source_target_connected (hg : s.gate.core.isAND = false) (l : OrLabel w) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source (s.orLabel hg l))
      ((inventory w hw v).target (s.orLabel hg l)) := by
  rw [s.or_source_actual hg l,s.or_target_actual hg l]
  exact s.or_normal_connected hg _ _ _ _ _ _ l

private theorem source_target_connected (l : (PrimitiveCode.core s.gate).Labels w) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source (s.label l))
      ((inventory w hw v).target (s.label l)) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact (⟨index,⟨⟨false,initial,target⟩,incoming,pattern,rotation⟩,he⟩ : CoreSite w hw v).or_source_target_connected rfl l
  · exact (⟨index,⟨⟨true,initial,target⟩,incoming,pattern,rotation⟩,he⟩ : CoreSite w hw v).and_source_target_connected rfl l

private theorem primitive_surjective (i : Fin (codes w v).length) (c : PrimitiveCode)
    (hc : ((codes w v).get i).2 = c) (l : (inventory w hw v).PhysicalLabel) (hi : l.1 = i) :
    ∃ q,primitiveLabel w hw v i c hc q = l := by
  subst c
  rcases l with ⟨j,l⟩
  dsimp at hi
  subst j
  exact ⟨l,rfl⟩

theorem owner_connected (l : (inventory w hw v).PhysicalLabel) (hl : l.1 = s.index) :
    SameComponent (inventory w hw v).board ((inventory w hw v).source l) ((inventory w hw v).target l) := by
  have hsurj : ∃ q,s.label q = l := primitive_surjective s.index (.core s.gate) s.code_eq l hl
  obtain ⟨q,rfl⟩ := hsurj
  exact s.source_target_connected q

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
