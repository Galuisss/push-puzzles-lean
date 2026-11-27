/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageRaster

/-! Translate a complete finite glyph atlas into a larger explicit rectangle. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.StorageAtlas


variable {n W H W' H' : ℕ} {Label : Fin n → Type} [∀ i,Fintype (Label i)]

/-- The same complete physical inventories at a common actual translated placement. -/
def translate (A : StorageAtlas n W H Label) (dx dy : ℕ) (hx : dx+W≤W') (hy : dy+H≤H') :
    StorageAtlas n W' H' Label where
  piece := A.piece
  matching := A.matching
  dx i := dx+A.dx i
  dy i := dy+A.dy i
  fitsX i := by have hh:=A.fitsX i; omega
  fitsY i := by have hh:=A.fitsY i; omega
  walls_compatible := by
    intro i j p q he
    apply A.walls_compatible i j p q
    have heX := congrArg Prod.fst he
    have heY := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at heX heY ⊢ <;> omega
  source_owners := by
    intro i j l k he
    apply A.source_owners i j l k
    have heX := congrArg Prod.fst he
    have heY := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at heX heY ⊢ <;> omega
  target_owners := by
    intro i j l k he
    apply A.target_owners i j l k
    have heX := congrArg Prod.fst he
    have heY := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at heX heY ⊢ <;> omega
  player := (⟨dx+A.player.1.val,by have hh:=A.player.1.isLt; omega⟩,
    ⟨dy+A.player.2.val,by have hh:=A.player.2.isLt; omega⟩)
  player_floor := by
    intro i p hp he
    apply A.player_floor i p hp
    have heX := congrArg Prod.fst he
    have heY := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at heX heY ⊢ <;> omega
  player_empty := by
    intro i l he
    apply A.player_empty i l
    have heX := congrArg Prod.fst he
    have heY := congrArg Prod.snd he
    apply Prod.ext <;> dsimp only at heX heY ⊢ <;> omega

/-- Primitive placements use the same exact grid embedding after the common translation. -/
theorem translate_embedding (A : StorageAtlas n W H Label) (dx dy : ℕ)
    (hx : dx+W≤W') (hy : dy+H≤H') (i : Fin n) (p : Cell (A.piece i).width (A.piece i).height) :
    ((A.translate dx dy hx hy).embedding i).cells p=
      (GridEmbedding.translate dx dy hx hy).cells ((A.embedding i).cells p) := by
  apply Prod.ext <;> apply Fin.ext
  · change dx+A.dx i+p.1.val=dx+(A.dx i+p.1.val)
    omega
  · change dy+A.dy i+p.2.val=dy+(A.dy i+p.2.val)
    omega

private theorem translate_source (A : StorageAtlas n W H Label) (dx dy : ℕ)
    (hx : dx+W≤W') (hy : dy+H≤H') (l : A.PhysicalLabel) :
    (A.translate dx dy hx hy).source l=
      (GridEmbedding.translate dx dy hx hy).cells (A.source l) :=
  translate_embedding A dx dy hx hy l.1 ((A.matching l.1).source l.2)

theorem translate_initial (A : StorageAtlas n W H Label) (dx dy : ℕ)
    (hx : dx+W≤W') (hy : dy+H≤H') :
    (A.translate dx dy hx hy).initial=
      (GridEmbedding.translate dx dy hx hy).extend ∅ A.initial := by
  apply State.ext
  · rfl
  change Finset.univ.map (A.translate dx dy hx hy).source=(Finset.univ.map A.source).map _∪∅
  rw [Finset.union_empty,Finset.map_map]
  apply congrArg (fun j : A.PhysicalLabel ↪ Cell W' H' => Finset.univ.map j)
  apply Function.Embedding.ext
  exact translate_source A dx dy hx hy


end PushPuzzle.PushFS.Reduction.StorageAtlas
