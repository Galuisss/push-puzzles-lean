/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateSelectedSlots
public import PushFS.Reduction.AnnulusShortFrames

/-! Protected-corner player transit in every actual complete independently mixed gate profile. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profileOutside selectedMarks cornerKind cornerOrientation

theorem corner_foreign_line (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1))
    (p : Cell (ShortCorners.width (cornerKind (key g r) k.val)) (ShortCorners.height (cornerKind (key g r) k.val)))
    (hp : (armCornerEmbedding g r k).cells p∈profileOutside g f (cornerIndex g r k)) :
    ∃j : Fin (curve (key g r)).length,(j.val=k.val ∨j.val=k.val+1) ∧
      ∃q : Cell (Inventory.piece g (lineIndex g r j)).width (Inventory.piece g (lineIndex g r j)).height,
        q∈selectedMarks g (f (lineIndex g r j)) (lineIndex g r j) ∧
          (primitiveEmbedding g (lineIndex g r j)).cells q=(armCornerEmbedding g r k).cells p := by
  obtain ⟨i,hik,q,hq,he⟩:=(mem_profileOutside g f (cornerIndex g r k) _).mp hp
  have hc : Inventory.contact g (cornerIndex g r k) i=true := by
    by_contra hc
    have hf : Inventory.contact g (cornerIndex g r k) i=false := Bool.eq_false_iff.mpr hc
    apply Inventory.no_coincident g _ i (Ne.symm hik) hf ((cornerIso (key g r) k.val).geometry.cells p) q
    exact congrArg (fun p : C=>(p.1.val,p.2.val)) he.symm
  rcases i with i | (⟨s,j|j⟩|s)
  · simp only [cornerIndex,Inventory.contact,Bool.false_eq_true] at hc
  · simp only [cornerIndex,Inventory.contact,decide_eq_true_eq] at hc
    have hrs : s=r := hc.1.symm
    subst s
    exact ⟨j,hc.2,q,hq,he⟩
  · simp only [cornerIndex,Inventory.contact,Bool.false_eq_true] at hc
  · simp only [cornerIndex,Inventory.contact,Bool.false_eq_true] at hc

theorem corner_profile_collar (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1)) :
    Polyline.Frame.fixed (armCornerEmbedding g r k) (profileOutside g f (cornerIndex g r k))⊆
      ShortCorners.allNeighbors (cornerKind (key g r) k.val) := by
  intro p hp
  obtain ⟨j,hj,q,hq,he⟩:=corner_foreign_line g f r k p ((Polyline.Frame.mem_fixed _ _ p).mp hp)
  obtain ⟨l,hl⟩:=selected_line_coordinates g f r j q hq
  have he':=congrArg (fun p : C=>(p.1.val,p.2.val)) he
  have hs:=hl.symm.trans (he'.trans (arm_corner_coordinates g r k p))
  clear hp he he' hl hq q
  rcases hj with hj|hj
  · exact near_selected_line_walking (key g r) j.val k.val hj j.isLt (cornerOutLine g r k).isLt
      (armPhase g f r (lineIndex g r j)) (Inventory.targetPhase g r) l p hs
  · exact far_selected_line_walking (key g r) j.val k.val hj j.isLt (cornerOutLine g r k).isLt
      (armPhase g f r (lineIndex g r j)) (Inventory.targetPhase g r) l p hs

end PushPuzzle.PushFS.Reduction.GateTileRouting
