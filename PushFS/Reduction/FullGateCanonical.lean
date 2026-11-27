/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateArmSweep
public import PushFS.Reduction.FullGateBufferProfileMacros

/-! Complete actual full-gate canonical macros for every legal single-port NCL change. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profile profileOutside cornerKind cornerOrientation

theorem changed_claims (a b : Gates.Signals) (hs : Gates.singleChange a b) :
    gateClaim a (Gates.changingPort a b)≠gateClaim b (Gates.changingPort a b) ∧
      ∀r : Fin 3,r≠Gates.changingPort a b →gateClaim a r=gateClaim b r := by
  have hh : ∀a b c x y z : Bool,Gates.singleChange ⟨a,b,c⟩ ⟨x,y,z⟩ →
      gateClaim ⟨a,b,c⟩ (Gates.changingPort ⟨a,b,c⟩ ⟨x,y,z⟩)≠gateClaim ⟨x,y,z⟩ (Gates.changingPort ⟨a,b,c⟩ ⟨x,y,z⟩) ∧
      ∀r : Fin 3,r≠Gates.changingPort ⟨a,b,c⟩ ⟨x,y,z⟩ →gateClaim ⟨a,b,c⟩ r=gateClaim ⟨x,y,z⟩ r := by decide +kernel
  exact hh a.left a.upper a.right b.left b.upper b.right hs

private theorem line_diagonal (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (hab : a=b) :
    (lineBase flip n hn a b).initial.boxes=(lineBase flip n hn a b).board.goals := by
  subst b
  cases flip
  · rfl
  · exact (FlippedChain.initial_boxes n hn (FlippedChain.uniform a) (FlippedChain.uniform a)).trans
      (FlippedChain.goals_eq n hn (FlippedChain.uniform a) (FlippedChain.uniform a)).symm

private theorem marks_at (g : GateTileState) (f : Inventory.Index g→Bool)
    (j : Fin (Fintype.card (Inventory.Index g))) :
    ((fullAtlas g).pieceMarks (profileMask g f) j).map ((fullAtlas g).embedding j).cells=
      (selectedMarks g (f ((Inventory.numbering g).symm j)) ((Inventory.numbering g).symm j)).map
        (primitiveEmbedding g ((Inventory.numbering g).symm j)).cells := rfl

private theorem profiles_equal {n W H : ℕ} {Label : Fin n→Type} [∀i,Fintype (Label i)]
    (A : StorageAtlas n W H Label) (f h : Fin n→Bool)
    (hm : ∀i,(A.pieceMarks f i).map (A.embedding i).cells=(A.pieceMarks h i).map (A.embedding i).cells) :
    A.profileBoxes f=A.profileBoxes h := by
  unfold StorageAtlas.profileBoxes
  exact Finset.biUnion_congr rfl (fun i _=>hm i)

/-- Committed buffer pieces and the changed arm already give the complete target inventory. -/
theorem profile_finished (g : GateTileState) (f : Inventory.Index g→Bool)
    (hs : Gates.singleChange g.core.initial g.core.target)
    (hf : ∀i : Fin 4,f (.inl i)=true)
    (hl : ∀j,f (lineIndex g (Gates.changingPort g.core.initial g.core.target) j)=true)
    (hc : ∀j,f (cornerIndex g (Gates.changingPort g.core.initial g.core.target) j)=true) (p : C) :
    profile g f p=⟨p,(fullPuzzle g).board.goals⟩ := by
  apply State.ext
  · unfold profile StorageAtlas.profileAt
    rfl
  · unfold profile StorageAtlas.profileAt
    change (fullAtlas g).profileBoxes (profileMask g f)=(fullPuzzle g).board.goals
    have hm : ∀i : Inventory.Index g,
        (selectedMarks g (f i) i).map (primitiveEmbedding g i).cells=
          (selectedMarks g true i).map (primitiveEmbedding g i).cells:=by
      rintro (i|(⟨s,j|j⟩|s))
      · rw [hf i]
      · change (selectedMarks g (f (lineIndex g s j)) (lineIndex g s j)).map
          (primitiveEmbedding g (lineIndex g s j)).cells=
          (selectedMarks g true (lineIndex g s j)).map (primitiveEmbedding g (lineIndex g s j)).cells
        by_cases he : s=Gates.changingPort g.core.initial g.core.target
        · subst s
          rw [hl j]
        · rw [line_marks_map,line_marks_map]
          have hphase : Inventory.initialPhase g s=Inventory.targetPhase g s:=(changed_claims _ _ hs).2 s he
          cases hf' : f (lineIndex g s j)
          · simp only [Bool.false_eq_true,ite_false,ite_true]
            exact congrArg (fun boxes=>boxes.map (lineEmbedding g s j).cells)
              (line_diagonal _ _ _ _ _ hphase)
          · rfl
      · change (selectedMarks g (f (cornerIndex g s j)) (cornerIndex g s j)).map
          (primitiveEmbedding g (cornerIndex g s j)).cells=
          (selectedMarks g true (cornerIndex g s j)).map (primitiveEmbedding g (cornerIndex g s j)).cells
        by_cases he : s=Gates.changingPort g.core.initial g.core.target
        · subst s
          rw [hc j]
        · rw [corner_marks_map,corner_marks_map]
          have hphase : Inventory.initialPhase g s=Inventory.targetPhase g s:=(changed_claims _ _ hs).2 s he
          cases f (cornerIndex g s j) <;> simp only [Bool.false_eq_true,ite_false,ite_true,hphase]
      · cases f (.inr (.inr s)) <;> rfl
    have hh:=profiles_equal (fullAtlas g) (profileMask g f) (profileMask g (fun _=>true)) (fun j=>by
      rw [marks_at,marks_at]
      exact hm ((Inventory.numbering g).symm j))
    exact hh.trans (fullAtlas g).profile_target

theorem commitBuffer_arm_fresh (g : GateTileState) (r : Fin 3) :
    ∀j,commitBuffer g (fun _=>false) (armNode g r j)=false := by
  intro j
  unfold armNode
  split_ifs <;> rfl

end PushPuzzle.PushFS.Reduction.GateTileRouting
