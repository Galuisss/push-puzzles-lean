/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCompiler

/-! Every actual core, straight piece, and turn fits in the common physical tile. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

def PatchFits (w : ℕ) (p : Bitmap.Patch) : Prop :=
  p.x+p.bitmap.width ≤ tileSide w ∧ p.y+p.bitmap.height ≤ tileSide w

def SegmentGood (w : ℕ) (s : Segment) : Prop :=
  (s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) ∧
    90*(w+3) ≤ segmentLength s ∧
    (s.start.1 ≤ tileStride w ∧ s.start.2 ≤ tileStride w) ∧
    (s.finish.1 ≤ tileStride w ∧ s.finish.2 ≤ tileStride w)

theorem startTrim_bound (segments : List Segment) (i : ℕ) : startTrim segments i ≤ 1 := by
  unfold startTrim
  split_ifs <;> omega

theorem finishTrim_bound (segments : List Segment) (i : ℕ) : finishTrim segments i ≤ 2 := by
  unfold finishTrim
  split_ifs <;> omega

private theorem getD_mem {α : Type} {l : List α} {n : ℕ} (d : α) (hn : n < l.length) :
    l.getD n d ∈ l :=
  List.mem_iff_get.mpr ⟨⟨n,hn⟩,(List.getD_eq_get l d ⟨n,hn⟩).symm⟩

theorem trimmedSegment_good (w : ℕ) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s) (i : ℕ) (hi : i < segments.length) :
    ((trimmedSegment segments i).start.1 = (trimmedSegment segments i).finish.1 ∨
      (trimmedSegment segments i).start.2 = (trimmedSegment segments i).finish.2) ∧
      17*w+61 ≤ segmentLength (trimmedSegment segments i) ∧
      ((trimmedSegment segments i).start.1 ≤ tileStride w ∧ (trimmedSegment segments i).start.2 ≤ tileStride w) ∧
      ((trimmedSegment segments i).finish.1 ≤ tileStride w ∧ (trimmedSegment segments i).finish.2 ≤ tileStride w) := by
  have hs := hg (segmentAt segments i) (getD_mem _ hi)
  have hf := startTrim_bound segments i
  have hb := finishTrim_bound segments i
  have hsum : startTrim segments i+finishTrim segments i ≤ segmentLength (segmentAt segments i) := by
    unfold SegmentGood at hs
    omega
  have ht := trimmed_travels (segmentAt segments i) hs.1 _ _ hsum
  have hlen := trimmed_length (segmentAt segments i) hs.1 _ _ hsum
  have hbds := advance_bounded (segmentDirection (segmentAt segments i)) _ _ _
    (startTrim segments i) (finishTrim segments i) (tileStride w)
    (segment_travels (segmentAt segments i) hs.1) hsum hs.2.2.1 hs.2.2.2
  refine ⟨?_,?_,⟨hbds.1,hbds.2.1⟩,hbds.2.2⟩
  · cases hd : segmentDirection (segmentAt segments i) <;>
      simp only [hd, Travels] at ht <;> tauto
  · change 17*w+61 ≤ segmentLength (trimmed (segmentAt segments i) _ _)
    rw [hlen]
    have hl := hs.2.1
    omega

/-- The concrete emitted patch list contains no clipped primitive. -/
theorem pathPatches_fit (w : ℕ) (hw : 2 ≤ w) (segments : List Segment)
    (hg : ∀ s ∈ segments, SegmentGood w s)
    (initialSide targetSide keepEndpoint initial target : Bool) :
    ∀ p ∈ pathPatches w hw segments initialSide targetSide keepEndpoint initial target, PatchFits w p := by
  intro p hp
  obtain ⟨i,hi,hp⟩ := List.mem_flatMap.mp hp
  have hi' := List.mem_range.mp hi
  have hs := hg (segmentAt segments i) (getD_mem _ hi')
  have htrim := trimmedSegment_good w segments hg i hi'
  rcases List.mem_append.mp hp with hp | hp
  · have he := List.mem_singleton.mp hp
    subst p
    exact linePatch_fits w hw _ _ _ _ _ _ _ htrim.1 htrim.2.1 htrim.2.2.1 htrim.2.2.2
  · split_ifs at hp
    · have he := List.mem_singleton.mp hp
      subst p
      exact Turn.patch_fits w _ _ _ _ _ hs.2.2.2
    · simp at hp

private theorem segment_start_mem (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) :
    s.Contains s.start := by
  rcases hs with hx | hy
  · exact Or.inl ⟨hx,rfl,min_le_left _ _,le_max_left _ _⟩
  · exact Or.inr ⟨hy,rfl,min_le_left _ _,le_max_left _ _⟩

private theorem segment_finish_mem (s : Segment) (hs : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) :
    s.Contains s.finish := by
  rcases hs with hx | hy
  · exact Or.inl ⟨hx,hx.symm,min_le_right _ _,le_max_right _ _⟩
  · exact Or.inr ⟨hy,hy.symm,min_le_right _ _,le_max_right _ _⟩

theorem route_segment_good (w : ℕ) (kind : Bool) (q : Key) {s : Segment} (hs : s ∈ route w kind q) :
    (s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2) ∧
      100*(w+3) ≤ segmentLength s ∧
      (s.start.1 ≤ tileStride w ∧ s.start.2 ≤ tileStride w) ∧
      (s.finish.1 ≤ tileStride w ∧ s.finish.2 ≤ tileStride w) := by
  have hl := route_segment_length w kind q hs
  have ha : s.start.1 = s.finish.1 ∨ s.start.2 = s.finish.2 := by tauto
  have hp := route_trace_bounded w kind q ⟨s,hs,segment_start_mem s ha⟩
  have hq := route_trace_bounded w kind q ⟨s,hs,segment_finish_mem s ha⟩
  refine ⟨ha,?_,?_,?_⟩
  · unfold segmentLength
    unfold FiniteGeometry.origin at hl
    omega
  all_goals dsimp [side, tileStride] at *; omega

theorem armRoute_good (w : ℕ) (g : GateTileState) (role : Fin 3) :
    ∀ s ∈ armRoute w g role, SegmentGood w s := by
  intro s hs
  obtain ⟨i,hi,hsi⟩ := List.mem_mapIdx.mp hs
  have hr := route_segment_good w g.core.isAND (g.pattern,g.rotation,role)
    (List.mem_iff_getElem.mpr ⟨i,hi,rfl⟩)
  split_ifs at hsi with hlast
  · subst s
    have hbit := Bool.toNat_le (g.incoming.get role)
    have hsum : 0+(g.incoming.get role).toNat ≤
        segmentLength ((route w g.core.isAND (g.pattern,g.rotation,role))[i]) := by omega
    have ht := advance_travels _ _ _ _ 0 (g.incoming.get role).toNat
      (segment_travels _ hr.1) hsum
    have hb := advance_bounded _ _ _ _ 0 (g.incoming.get role).toNat (tileStride w)
      (segment_travels _ hr.1) hsum hr.2.2.1 hr.2.2.2
    have hz : ∀ d p, advance d p 0 = p := by intro d p; cases d <;> simp [advance]
    simp only [hz] at ht hb
    have hlen := segmentLength_of_travels _ _ _ _ ht
    refine ⟨?_,?_,hr.2.2.1,hb.2.2⟩
    · cases hd : segmentDirection ((route w g.core.isAND (g.pattern,g.rotation,role))[i]) <;>
        simp only [hd, Travels] at ht <;> tauto
    · rw [hlen]
      have hl := hr.2.1
      omega
  · subst s
    exact ⟨hr.1,by have hh := hr.2.1; omega,hr.2.2⟩

theorem wireRoute_good (w : ℕ) (kind : Catalog.Kind) : ∀ s ∈ wireRoute w kind, SegmentGood w s := by
  intro s hs
  cases kind <;> simp [wireRoute, wireVertices] at hs <;>
    rcases hs with rfl | rfl <;>
    dsimp [SegmentGood, segmentLength, tileStride, spacing] <;> omega

private theorem corePatch_fits (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) : PatchFits w
    (corePatch w hw g) := by
  cases h : g.core.isAND <;>
    simp [PatchFits, corePatch, coreInstance, h,
      Bitmap.instancePatch, Encoding.data, FiniteGateCore.andInstance, FiniteGateCore.orInstance]
  all_goals unfold FiniteGeometry.side coreOffset tileSide tileStride spacing padding; omega

theorem gatePatches_fit (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    ∀ p ∈ gatePatches w hw g, PatchFits w p := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · subst p
    exact corePatch_fits w hw g
  · obtain ⟨role,_,hp⟩ := List.mem_flatMap.mp hp
    exact pathPatches_fit w hw _ (armRoute_good w g role) _ _ _ _ _ p hp

theorem wirePatches_fit (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    ∀ p ∈ wirePatches w hw q, PatchFits w p :=
  pathPatches_fit w hw _ (wireRoute_good w q.1) _ _ _ _ _

end PushPuzzle.PushS.FiniteRouting
