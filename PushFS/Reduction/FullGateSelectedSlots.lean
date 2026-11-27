/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateProfiles
public import PushFS.Reduction.AnnulusFrontierBuffer

/-! Every actual mixed-profile box has its original primitive identity and its selected literal phase coordinates. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profileOutside

def armPhase (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3) (i : Inventory.Index g) : Bool :=
  if f i then Inventory.targetPhase g r else Inventory.initialPhase g r

private theorem selectedMarks_label (g : GateTileState) (b : Bool) (i : Inventory.Index g)
    (q : Cell (Inventory.piece g i).width (Inventory.piece g i).height) (hq : q∈selectedMarks g b i) :
    ∃l : Inventory.Labels g i,(if b then (Inventory.matching g i).target l else (Inventory.matching g i).source l)=q := by
  cases b
  · change q∈(Inventory.piece g i).initial.boxes at hq
    rw [←(Inventory.matching g i).source_image] at hq
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hq
    exact ⟨l,he⟩
  · change q∈(Inventory.piece g i).board.goals at hq
    rw [←(Inventory.matching g i).target_image] at hq
    obtain ⟨l,_,he⟩:=Finset.mem_map.mp hq
    exact ⟨l,he⟩

private theorem line_target_source_placed (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (o : RectOrientation) (dx dy : ℕ) (l : lineLabels flip n) :
    o.coordinates (lineBase flip n hn a b).width (lineBase flip n hn a b).height dx dy ((lineMatching flip n hn a b).target l)=
      o.coordinates (lineBase flip n hn b b).width (lineBase flip n hn b b).height dx dy ((lineMatching flip n hn b b).source l) := by
  cases flip
  · rfl
  · change FlippedChain.Label n at l
    change o.coordinates (n+25) 21 dx dy ((FlippedChain.slotMatching n hn a b).target l)=
      o.coordinates (n+25) 21 dx dy ((FlippedChain.slotMatching n hn b b).source l)
    rw [FlippedChain.target_position,FlippedChain.source_position]

theorem selected_line_coordinates (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length)
    (q : Cell (Inventory.piece g (lineIndex g r j)).width (Inventory.piece g (lineIndex g r j)).height)
    (hq : q∈selectedMarks g (f (lineIndex g r j)) (lineIndex g r j)) :
    ∃l : lineLabels (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val),
      ((Inventory.offset g (lineIndex g r j)).1+q.1.val,(Inventory.offset g (lineIndex g r j)).2+q.2.val)=
        (lineOrientation (original (key g r) j.val).travel (fillerFlip (key g r) j.val)).coordinates
          (lineBase (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
            (armPhase g f r (lineIndex g r j)) (Inventory.targetPhase g r)).width
          (lineBase (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
            (armPhase g f r (lineIndex g r j)) (Inventory.targetPhase g r)).height
          (lineOffset (key g r) j.val).1 (lineOffset (key g r) j.val).2
          ((lineMatching (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
            (armPhase g f r (lineIndex g r j)) (Inventory.targetPhase g r)).source l) := by
  obtain ⟨l,hl⟩:=selectedMarks_label g (f (lineIndex g r j)) (lineIndex g r j) q hq
  cases hf : f (lineIndex g r j)
  · simp only [hf,Bool.false_eq_true,ite_false] at hl
    subst q
    have hphase : armPhase g f r (lineIndex g r j)=Inventory.initialPhase g r := by simp only [armPhase,hf,Bool.false_eq_true,ite_false]
    rw [hphase]
    exact ⟨l,line_source_coordinates (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r) l⟩
  · simp only [hf,ite_true] at hl
    subst q
    have hphase : armPhase g f r (lineIndex g r j)=Inventory.targetPhase g r := by simp only [armPhase,hf,ite_true]
    rw [hphase]
    refine ⟨l,?_⟩
    have ht:=line_target_coordinates (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r) l
    exact ht.trans (line_target_source_placed (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
      (filler_shape (key g r) j.val j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r)
      (lineOrientation (original (key g r) j.val).travel (fillerFlip (key g r) j.val))
      (lineOffset (key g r) j.val).1 (lineOffset (key g r) j.val).2 l)

theorem selected_corner_coordinates (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1))
    (q : Cell (Inventory.piece g (cornerIndex g r j)).width (Inventory.piece g (cornerIndex g r j)).height)
    (hq : q∈selectedMarks g (f (cornerIndex g r j)) (cornerIndex g r j)) :
    ∃l : Fin (ShortCorners.count (cornerKind (key g r) j.val)),
      ((Inventory.offset g (cornerIndex g r j)).1+q.1.val,(Inventory.offset g (cornerIndex g r j)).2+q.2.val)=
        (cornerOrientation (key g r) j.val).coordinates _ _ (cornerOffset (key g r) j.val).1 (cornerOffset (key g r) j.val).2
          ((ShortCorners.template (cornerKind (key g r) j.val)).position (armPhase g f r (cornerIndex g r j)) l) := by
  obtain ⟨l,hl⟩:=selectedMarks_label g (f (cornerIndex g r j)) (cornerIndex g r j) q hq
  cases hf : f (cornerIndex g r j)
  · simp only [hf,Bool.false_eq_true,ite_false] at hl
    subst q
    simp only [armPhase,hf,Bool.false_eq_true,ite_false]
    exact ⟨l,corner_source_coordinates (key g r) j.val (Inventory.initialPhase g r) (Inventory.targetPhase g r) l⟩
  · simp only [hf,ite_true] at hl
    subst q
    simp only [armPhase,hf,ite_true]
    exact ⟨l,corner_target_coordinates (key g r) j.val (Inventory.initialPhase g r) (Inventory.targetPhase g r) l⟩

theorem selected_buffer_coordinates (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (q : Cell (Inventory.piece g (.inl (frontierBufferIndex r))).width (Inventory.piece g (.inl (frontierBufferIndex r))).height)
    (hq : q∈selectedMarks g (f (.inl (frontierBufferIndex r))) (.inl (frontierBufferIndex r))) :
    ∃l : Chain.Label 2301,
      ((Inventory.offset g (.inl (frontierBufferIndex r))).1+q.1.val,
        (Inventory.offset g (.inl (frontierBufferIndex r))).2+q.2.val)=
        (frontierOrientation g.core.isAND r).coordinates 2306 21
          (frontierBufferOffset g r).1 (frontierBufferOffset g r).2
          (Chain.position 2301 (by omega) (Chain.uniform 2301 (armPhase g f r (.inl (frontierBufferIndex r)))) l) := by
  obtain ⟨l,hl⟩:=selectedMarks_label g (f (.inl (frontierBufferIndex r))) (.inl (frontierBufferIndex r)) q hq
  cases hf : f (.inl (frontierBufferIndex r))
  · simp only [hf,Bool.false_eq_true,ite_false] at hl
    subst q
    simp only [armPhase,hf,Bool.false_eq_true,ite_false]
    exact ⟨l,frontier_buffer_source_coordinates g r l⟩
  · simp only [hf,ite_true] at hl
    subst q
    simp only [armPhase,hf,ite_true]
    exact ⟨l,frontier_buffer_target_coordinates g r l⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
