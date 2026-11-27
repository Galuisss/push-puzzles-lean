/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceArmEndpoints
public import PushS.FiniteGateSelected

/-! Selected real gate branches update precisely their actual core owner in the whole-board inventory. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateSelected
open FiniteGateCanonicalAccess FiniteGateFaceBridge FiniteGateFaceGeometry
open scoped Classical

attribute [local irreducible] codes width height inventory FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : CoreSite w hw v)

/-- The actual global identities of this AND core's complete working stock. -/
def andLabels (hg : s.gate.core.isAND = true) : AndLabel w ↪ (inventory w hw v).PhysicalLabel := by
  refine ⟨s.andLabel hg,?_⟩
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact primitiveLabel_injective w hw v index (.core _) he

/-- The actual global identities of this OR core's complete working stock. -/
def orLabels (hg : s.gate.core.isAND = false) : OrLabel w ↪ (inventory w hw v).PhysicalLabel := by
  refine ⟨s.orLabel hg,?_⟩
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact primitiveLabel_injective w hw v index (.core _) he
  · cases hg

private theorem primitiveLabels_cover (i : Fin (codes w v).length) (c : PrimitiveCode)
    (hc : ((codes w v).get i).2 = c) : (inventory w hw v).pieceLabels i ⊆
      Finset.univ.map ⟨primitiveLabel w hw v i c hc,primitiveLabel_injective w hw v i c hc⟩ := by
  subst c
  intro l hl
  rcases l with ⟨j,l⟩
  have hj := (inventory w hw v).mem_pieceLabels i ⟨j,l⟩ |>.mp hl
  dsimp at hj
  subst j
  exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩

theorem andLabels_cover (hg : s.gate.core.isAND = true) :
    (inventory w hw v).pieceLabels s.index ⊆ Finset.univ.map (s.andLabels hg) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact primitiveLabels_cover index (.core _) he

theorem orLabels_cover (hg : s.gate.core.isAND = false) :
    (inventory w hw v).pieceLabels s.index ⊆ Finset.univ.map (s.orLabels hg) := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact primitiveLabels_cover index (.core _) he
  · cases hg

theorem andLabels_owner (hg : s.gate.core.isAND = true) (l : AndLabel w) : (s.andLabels hg l).1 = s.index := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · cases hg
  · exact primitiveLabel_owner w hw v index (.core _) he l

theorem orLabels_owner (hg : s.gate.core.isAND = false) (l : OrLabel w) : (s.orLabels hg l).1 = s.index := by
  rcases s with ⟨index,⟨⟨kind,initial,target⟩,incoming,pattern,rotation⟩,he⟩
  cases kind
  · exact primitiveLabel_owner w hw v index (.core _) he l
  · cases hg

/-- Every selected actual core identity occupies exactly its source or target normal slot. -/
private theorem and_current (hg : s.gate.core.isAND = true) (phase : Fin (codes w v).length → Bool)
    (q : Bool) (hq : phase s.index = q) (l : AndLabel w) :
    PrimitiveProfile.position w hw v phase (s.andLabels hg l) = s.embedding.cells
      (andCell w (if q then s.gate.core.target.left else s.gate.core.initial.left)
        (if q then s.gate.core.target.upper else s.gate.core.initial.upper)
        (if q then s.gate.core.target.right else s.gate.core.initial.right) l) := by
  cases q
  · simp only [PrimitiveProfile.position,s.andLabels_owner hg,hq,Bool.false_eq_true,ite_false]
    simpa only [andLabels,Function.Embedding.coeFn_mk] using s.and_source_actual hg l
  · simp only [PrimitiveProfile.position,s.andLabels_owner hg,hq,ite_true]
    simpa only [andLabels,Function.Embedding.coeFn_mk] using s.and_target_actual hg l

/-- Every selected actual OR identity occupies exactly its source or target normal slot. -/
private theorem or_current (hg : s.gate.core.isAND = false) (phase : Fin (codes w v).length → Bool)
    (q : Bool) (hq : phase s.index = q) (l : OrLabel w) :
    PrimitiveProfile.position w hw v phase (s.orLabels hg l) = s.embedding.cells
      (orCell w (if q then s.gate.core.target.left else s.gate.core.initial.left)
        (if q then s.gate.core.target.upper else s.gate.core.initial.upper)
        (if q then s.gate.core.target.right else s.gate.core.initial.right) l) := by
  cases q
  · simp only [PrimitiveProfile.position,s.orLabels_owner hg,hq,Bool.false_eq_true,ite_false]
    simpa only [orLabels,Function.Embedding.coeFn_mk] using s.or_source_actual hg l
  · simp only [PrimitiveProfile.position,s.orLabels_owner hg,hq,ite_true]
    simpa only [orLabels,Function.Embedding.coeFn_mk] using s.or_target_actual hg l

/-- The selected actual AND branch updates its whole owner while preserving every other real primitive. -/
theorem and_run (hg : s.gate.core.isAND = true) (phase : Fin (codes w v).length → Bool)
    (fresh : phase s.index = false) (B : Board (width w v) (height w v))
    (S : AndStep w s.embedding B (PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.andLabels hg)))
      s.gate.core.initial s.gate.core.target)
    (Ai : AndAccess w s.embedding B ((andBoxes w s.gate.core.initial.left s.gate.core.initial.upper
      s.gate.core.initial.right).map s.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.andLabels hg))))
    (Af : AndAccess w s.embedding B ((andBoxes w s.gate.core.target.left s.gate.core.target.upper
      s.gate.core.target.right).map s.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.andLabels hg)))) :
    Reachable B (some 1)
      (PrimitiveProfile.state w hw v phase (s.embedding.cells (dock w true true)))
      (PrimitiveProfile.state w hw v (Function.update phase s.index true) (s.embedding.cells (dock w true true))) := by
  apply PrimitiveProfile.selection_run phase s.index (s.andLabels hg) (s.andLabels_cover hg) s.embedding
    (andCell w s.gate.core.initial.left s.gate.core.initial.upper s.gate.core.initial.right)
    (andCell w s.gate.core.target.left s.gate.core.target.upper s.gate.core.target.right)
    (s.and_current hg phase false fresh)
    (s.and_current hg (Function.update phase s.index true) true (Function.update_self _ _ _)) B _ _
  exact S.canonical_run w hw s.embedding Ai Af

/-- The selected actual OR branch updates its whole owner while preserving every other real primitive. -/
theorem or_run (hg : s.gate.core.isAND = false) (phase : Fin (codes w v).length → Bool)
    (fresh : phase s.index = false) (B : Board (width w v) (height w v))
    (S : OrStep w s.embedding B (PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.orLabels hg)))
      s.gate.core.initial s.gate.core.target)
    (Ai : Access w false s.embedding B ((orBoxes w s.gate.core.initial.left s.gate.core.initial.upper
      s.gate.core.initial.right).map s.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.orLabels hg))))
    (Af : Access w false s.embedding B ((orBoxes w s.gate.core.target.left s.gate.core.target.upper
      s.gate.core.target.right).map s.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.orLabels hg)))) :
    Reachable B (some 1)
      (PrimitiveProfile.state w hw v phase (s.embedding.cells (dock w false true)))
      (PrimitiveProfile.state w hw v (Function.update phase s.index true) (s.embedding.cells (dock w false true))) := by
  apply PrimitiveProfile.selection_run phase s.index (s.orLabels hg) (s.orLabels_cover hg) s.embedding
    (orCell w s.gate.core.initial.left s.gate.core.initial.upper s.gate.core.initial.right)
    (orCell w s.gate.core.target.left s.gate.core.target.upper s.gate.core.target.right)
    (s.or_current hg phase false fresh)
    (s.or_current hg (Function.update phase s.index true) true (Function.update_self _ _ _)) B _ _
  exact S.canonical_run w hw s.embedding Ai Af

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
