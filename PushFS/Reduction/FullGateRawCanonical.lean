/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateRawPhases

/-! Explicit primitive-by-primitive canonical identity transport through gate phase assignments. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires
set_option maxRecDepth 65536

def flagLabelEquiv (g : GateTileState) (a b : Gates.Signals) : (i : Inventory.Index g)→
    Inventory.Labels g i≃Inventory.Labels (withFlags g a b) i
  | .inl _=>Equiv.refl _
  | .inr (.inl ⟨_,.inl _⟩)=>Equiv.refl _
  | .inr (.inl ⟨_,.inr _⟩)=>Equiv.refl _
  | .inr (.inr _)=>Equiv.refl _

def rawFlagsEquiv (g : GateTileState) (a b : Gates.Signals) : RawLabel g≃RawLabel (withFlags g a b) :=
  Equiv.sigmaCongrRight (flagLabelEquiv g a b)

private theorem rawFlagsEquiv_apply (g : GateTileState) (a b : Gates.Signals)
    (i : Inventory.Index g) (l : Inventory.Labels g i) :
    rawFlagsEquiv g a b ⟨i,l⟩=⟨i,flagLabelEquiv g a b i l⟩ := rfl

private theorem line_source_retarget (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b d : Bool)
    (o : RectOrientation) (dx dy : ℕ) (l : lineLabels flip n) :
    o.coordinates (lineBase flip n hn a b).width (lineBase flip n hn a b).height dx dy
        ((lineMatching flip n hn a b).source l)=
      o.coordinates (lineBase flip n hn a d).width (lineBase flip n hn a d).height dx dy
        ((lineMatching flip n hn a d).source l) := by
  cases flip
  · change o.coordinates (n+5) 21 dx dy (Chain.position n hn (Chain.uniform n a) l)=
      o.coordinates (n+5) 21 dx dy (Chain.position n hn (Chain.uniform n a) l)
    rfl
  · change FlippedChain.Label n at l
    change o.coordinates (n+25) 21 dx dy ((FlippedChain.slotMatching n hn a b).source l)=
      o.coordinates (n+25) 21 dx dy ((FlippedChain.slotMatching n hn a d).source l)
    rw [FlippedChain.source_position,FlippedChain.source_position]

private theorem rawSource_retarget (g : GateTileState) (a b d : Gates.Signals) (l : RawLabel g) :
    rawSource (withFlags g a b) (rawFlagsEquiv g a b l)=rawSource (withFlags g a d) (rawFlagsEquiv g a d l) := by
  rcases l with ⟨i,l⟩
  rw [rawFlagsEquiv_apply g a b i l,rawFlagsEquiv_apply g a d i l]
  rcases i with i | (⟨role,j | j⟩ | role)
  · fin_cases i <;> rfl
  · let q := key g role
    have hh := line_source_retarget (fillerFlip q j.val) (fillerSpan q j.val)
      (filler_shape q j.val j.isLt).2.1 (gateClaim a role) (gateClaim b role) (gateClaim d role)
      (lineOrientation (original q j.val).travel (fillerFlip q j.val))
      (lineOffset q j.val).1 (lineOffset q j.val).2 l
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh
  · rfl
  · exact l.elim0

private theorem placed_line_target_source (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (o : RectOrientation) (dx dy : ℕ) (l : lineLabels flip n) :
    o.coordinates (lineBase flip n hn a b).width (lineBase flip n hn a b).height dx dy
        ((lineMatching flip n hn a b).target l)=
      o.coordinates (lineBase flip n hn b a).width (lineBase flip n hn b a).height dx dy
        ((lineMatching flip n hn b a).source l) := by
  cases flip
  · change o.coordinates (n+5) 21 dx dy (Chain.position n hn (Chain.uniform n b) l)=
      o.coordinates (n+5) 21 dx dy (Chain.position n hn (Chain.uniform n b) l)
    rfl
  · change FlippedChain.Label n at l
    change o.coordinates (n+25) 21 dx dy ((FlippedChain.slotMatching n hn a b).target l)=
      o.coordinates (n+25) 21 dx dy ((FlippedChain.slotMatching n hn b a).source l)
    rw [FlippedChain.target_position,FlippedChain.source_position]

/-- Every actual goal identity is the source identity of the reversed canonical assignment. -/
private theorem rawTarget_source (g : GateTileState) (a b : Gates.Signals) (l : RawLabel g) :
    rawTarget (withFlags g a b) (rawFlagsEquiv g a b l)=
      rawSource (withFlags g b a) (rawFlagsEquiv g b a l) := by
  rcases l with ⟨i,l⟩
  rw [rawFlagsEquiv_apply g a b i l,rawFlagsEquiv_apply g b a i l]
  rcases i with i | (⟨role,j | j⟩ | role)
  · fin_cases i <;> rfl
  · let q := key g role
    have hh := placed_line_target_source (fillerFlip q j.val) (fillerSpan q j.val)
      (filler_shape q j.val j.isLt).2.1 (gateClaim a role) (gateClaim b role)
      (lineOrientation (original q j.val).travel (fillerFlip q j.val))
      (lineOffset q j.val).1 (lineOffset q j.val).2 l
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh
  · rfl
  · exact l.elim0

private theorem rawTarget_reinitial (g : GateTileState) (a c b : Gates.Signals) (l : RawLabel g) :
    rawTarget (withFlags g a b) (rawFlagsEquiv g a b l)=
      rawTarget (withFlags g c b) (rawFlagsEquiv g c b l) := by
  rw [rawTarget_source,rawTarget_source]
  exact rawSource_retarget g b a c l

/-- At the target orientation every real box occupies its own literal goal slot. -/
private theorem rawTarget_canonical (g : GateTileState) (a b : Gates.Signals) (l : RawLabel g) :
    rawTarget (withFlags g a b) (rawFlagsEquiv g a b l)=
      rawSource (withFlags g b b) (rawFlagsEquiv g b b l) :=
  (rawTarget_source g a b l).trans (rawSource_retarget g b a b l)

open scoped Classical

theorem full_initial_mem (g : GateTileState) (p : C) :
    p∈(fullAtlas g).initial.boxes ↔ ∃l : RawLabel g,rawSource g l=p := by
  change p∈(fullPuzzle g).initial.boxes ↔_
  erw [← (rawSlotMatching g).source_image,Finset.mem_map]
  constructor
  · rintro ⟨⟨i,l⟩,_,he⟩
    exact ⟨⟨i,l⟩,(raw_source g i l).symm.trans he⟩
  · rintro ⟨⟨i,l⟩,he⟩
    refine ⟨⟨i,l⟩,?_,(raw_source g i l).trans he⟩
    simp only [Finset.mem_univ]

theorem full_goals_mem (g : GateTileState) (p : C) :
    p∈(fullAtlas g).board.goals ↔ ∃l : RawLabel g,rawTarget g l=p := by
  change p∈(fullPuzzle g).board.goals ↔_
  erw [← (rawSlotMatching g).target_image,Finset.mem_map]
  constructor
  · rintro ⟨⟨i,l⟩,_,he⟩
    exact ⟨⟨i,l⟩,(raw_target g i l).symm.trans he⟩
  · rintro ⟨⟨i,l⟩,he⟩
    refine ⟨⟨i,l⟩,?_,(raw_target g i l).trans he⟩
    simp only [Finset.mem_univ]

theorem full_initial_retarget (g : GateTileState) (a b d : Gates.Signals) :
    @Eq (Finset C) (fullPuzzle (withFlags g a b)).initial.boxes (fullPuzzle (withFlags g a d)).initial.boxes := by
  change (fullAtlas (withFlags g a b)).initial.boxes=(fullAtlas (withFlags g a d)).initial.boxes
  apply Finset.ext
  intro p
  rw [full_initial_mem,full_initial_mem]
  constructor
  · rintro ⟨l,hl⟩
    obtain ⟨l,rfl⟩ := (rawFlagsEquiv g a b).surjective l
    exact ⟨rawFlagsEquiv g a d l,(rawSource_retarget g a b d l).symm.trans hl⟩
  · rintro ⟨l,hl⟩
    obtain ⟨l,rfl⟩ := (rawFlagsEquiv g a d).surjective l
    exact ⟨rawFlagsEquiv g a b l,(rawSource_retarget g a d b l).symm.trans hl⟩

theorem full_goals_reinitial (g : GateTileState) (a c b : Gates.Signals) :
    @Eq (Finset C) (fullPuzzle (withFlags g a b)).board.goals (fullPuzzle (withFlags g c b)).board.goals := by
  change (fullAtlas (withFlags g a b)).board.goals=(fullAtlas (withFlags g c b)).board.goals
  apply Finset.ext
  intro p
  rw [full_goals_mem,full_goals_mem]
  constructor
  · rintro ⟨l,hl⟩
    obtain ⟨l,rfl⟩ := (rawFlagsEquiv g a b).surjective l
    exact ⟨rawFlagsEquiv g c b l,(rawTarget_reinitial g a c b l).symm.trans hl⟩
  · rintro ⟨l,hl⟩
    obtain ⟨l,rfl⟩ := (rawFlagsEquiv g c b).surjective l
    exact ⟨rawFlagsEquiv g a b l,(rawTarget_reinitial g c a b l).symm.trans hl⟩

/-- The complete target bitmap equals the real canonical box bitmap at the target assignment. -/
theorem full_goals_canonical (g : GateTileState) (a b : Gates.Signals) :
    @Eq (Finset C) (fullPuzzle (withFlags g a b)).board.goals (fullPuzzle (withFlags g b b)).initial.boxes := by
  change (fullAtlas (withFlags g a b)).board.goals=(fullAtlas (withFlags g b b)).initial.boxes
  apply Finset.ext
  intro p
  rw [full_goals_mem,full_initial_mem]
  constructor
  · rintro ⟨l,hl⟩
    obtain ⟨l,rfl⟩ := (rawFlagsEquiv g a b).surjective l
    exact ⟨rawFlagsEquiv g b b l,(rawTarget_canonical g a b l).symm.trans hl⟩
  · rintro ⟨l,hl⟩
    obtain ⟨l,rfl⟩ := (rawFlagsEquiv g b b).surjective l
    exact ⟨rawFlagsEquiv g a b l,(rawTarget_canonical g a b l).trans hl⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
