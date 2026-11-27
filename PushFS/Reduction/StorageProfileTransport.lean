/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageProfiles
public import PushFS.Reduction.TranslateAtlas

/-! Independently selected complete inventories commute with actual atlas translation. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.StorageAtlas

open scoped Classical
variable {n w h W H : ℕ} {Label : Fin n→Type} [∀i,Fintype (Label i)]

theorem profileBoxes_translate (A : StorageAtlas n w h Label) (f : Fin n→Bool)
    (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H) :
    (A.translate dx dy hx hy).profileBoxes f=(A.profileBoxes f).map (GridEmbedding.translate dx dy hx hy).cells := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
    obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hi
    refine Finset.mem_map.mpr ⟨(A.embedding i).cells q,?_,?_⟩
    · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_map.mpr ⟨q,hq,rfl⟩⟩
    · exact (A.translate_embedding dx dy hx hy i q).symm.trans he
  · intro hp
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hq
    obtain ⟨u,hu,rfl⟩:=Finset.mem_map.mp hi
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_map.mpr ⟨u,hu,A.translate_embedding dx dy hx hy i u⟩⟩

end PushPuzzle.PushFS.Reduction.StorageAtlas
