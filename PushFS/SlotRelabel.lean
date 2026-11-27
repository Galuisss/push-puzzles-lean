/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.LabelOrder

/-! Change the proof indexing of the actual physical identities while preserving their complete storage matching. -/

@[expose] public section

namespace PushPuzzle.PushFS.SlotMatching


open scoped Classical

variable {I : Instance} {L K : Type} [Fintype L] [Fintype K]

def relabel (M : SlotMatching I L) (e : K≃L) : SlotMatching I K where
  source:=e.toEmbedding.trans M.source
  target:=e.toEmbedding.trans M.target
  source_image:=by
    rw [←M.source_image]
    ext p
    simp only [Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.trans_apply,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨e k,hk⟩
    · rintro ⟨l,hl⟩
      exact ⟨e.symm l,by rwa [Equiv.apply_symm_apply]⟩
  target_image:=by
    rw [←M.target_image]
    ext p
    simp only [Finset.mem_map,Finset.mem_univ,true_and,Function.Embedding.trans_apply,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨k,hk⟩
      exact ⟨e k,hk⟩
    · rintro ⟨l,hl⟩
      exact ⟨e.symm l,by rwa [Equiv.apply_symm_apply]⟩
  connected l:=M.connected (e l)


end PushPuzzle.PushFS.SlotMatching
