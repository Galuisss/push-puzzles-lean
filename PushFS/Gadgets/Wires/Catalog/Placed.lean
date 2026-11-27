/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageRaster

/-! One real complete physical glyph placed in its actual larger finite logic-cell rectangle. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Reduction

variable {I : Instance} {L : Type} [Fintype L] {W H : ℕ}

def placedAtlas (M : SlotMatching I L) (dx dy : ℕ) (hx : dx+I.width≤W) (hy : dy+I.height≤H) :
    StorageAtlas 1 W H (fun _=>L) where
  piece:=fun _=>I
  matching:=fun _=>M
  dx:=fun _=>dx
  dy:=fun _=>dy
  fitsX:=fun _=>hx
  fitsY:=fun _=>hy
  walls_compatible:=by
    intro i j p q he
    have heq : p=q := by
      apply Prod.ext <;> apply Fin.ext
      · have hh:=congrArg Prod.fst he; omega
      · have hh:=congrArg Prod.snd he; omega
    subst q
    rfl
  source_owners:=fun _ _ _ _ _=>Subsingleton.elim _ _
  target_owners:=fun _ _ _ _ _=>Subsingleton.elim _ _
  player:=(GridEmbedding.translate dx dy hx hy).cells I.initial.player
  player_floor:=by
    intro i p hp he
    have heq : I.initial.player=p := by
      apply Prod.ext <;> apply Fin.ext
      · have hh:=congrArg Prod.fst he; change dx+I.initial.player.1.val=dx+p.1.val at hh; omega
      · have hh:=congrArg Prod.snd he; change dy+I.initial.player.2.val=dy+p.2.val at hh; omega
    exact I.initial_valid.1 (heq ▸ hp)
  player_empty:=by
    intro i l he
    have heq : I.initial.player=M.source l := by
      apply Prod.ext <;> apply Fin.ext
      · have hh:=congrArg Prod.fst he; change dx+I.initial.player.1.val=dx+(M.source l).1.val at hh; omega
      · have hh:=congrArg Prod.snd he; change dy+I.initial.player.2.val=dy+(M.source l).2.val at hh; omega
    apply I.initial_valid.2.2
    rw [heq,←M.source_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
