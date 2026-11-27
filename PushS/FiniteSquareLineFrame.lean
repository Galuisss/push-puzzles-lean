/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSquareLine
public import PushS.FiniteLineFrame

/-! Ambient replay of horizontal or vertical sweeps with narrow active footprints. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSquareLine.Sweep

open PushFS FiniteLineMacros

variable {N W H : ℕ}

/-- The actual orientation of the line in the square source board. -/
def embedding (S : Sweep N) : GridEmbedding N N N N :=
  (if S.vertical then GridIsometry.transpose N N else GridIsometry.refl N N).embedding

@[simp] theorem embedding_apply (S : Sweep N) (p : Cell N N) : S.embedding.cells p = S.map p := by
  cases S with
  | mk L v => cases v <;> rfl

/-- Only the working track and adjacent walking lane participate in the sweep. -/
def active (S : Sweep N) : Finset (Cell N N) := S.line.active.map S.embedding.cells

private theorem lineFrame {S : Sweep N} {e : GridEmbedding N N W H} {B : Board W H}
    {fixed : Finset (Cell W H)} (F : FiniteWireFrame.Frame S.active e B fixed) :
    FiniteWireFrame.Frame S.line.active (S.embedding.trans e) B fixed where
  floor p hp := F.floor (S.embedding.cells p) (Finset.mem_map.mpr ⟨p, hp, rfl⟩)
  fixed_avoids p hp := F.fixed_avoids (S.embedding.cells p) (Finset.mem_map.mpr ⟨p, hp, rfl⟩)
  fixed_floor := F.fixed_floor

private theorem extend_orientation (S : Sweep N) (e : GridEmbedding N N W H)
    (fixed : Finset (Cell W H)) (j : ℕ) :
    (S.embedding.trans e).extend fixed ⟨(S.line.hub, S.line.lane), Finset.univ.image (S.line.position j)⟩ =
      e.extend fixed ⟨S.hub, Finset.univ.image (S.position j)⟩ := by
  apply State.ext
  · change e.cells (S.embedding.cells (S.line.hub, S.line.lane)) = e.cells (S.map _)
    rw [embedding_apply]
  · simp [GridEmbedding.extend, GridEmbedding.trans, Finset.map_eq_image, Finset.image_image,
      position, embedding_apply, Function.comp_def]

theorem forward_placed (S : Sweep N) (e : GridEmbedding N N W H) {B : Board W H}
    {fixed : Finset (Cell W H)} (F : FiniteWireFrame.Frame S.active e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨S.hub, Finset.univ.image (S.position 0)⟩)
      (e.extend fixed ⟨S.hub, Finset.univ.image (S.position S.line.count)⟩) := by
  have hr := S.line.forward_placed (S.embedding.trans e) (lineFrame F)
  simpa only [extend_orientation] using hr

theorem backward_placed (S : Sweep N) (e : GridEmbedding N N W H) {B : Board W H}
    {fixed : Finset (Cell W H)} (F : FiniteWireFrame.Frame S.active e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨S.hub, Finset.univ.image (S.position S.line.count)⟩)
      (e.extend fixed ⟨S.hub, Finset.univ.image (S.position 0)⟩) := by
  have hr := S.line.backward_placed (S.embedding.trans e) (lineFrame F)
  simpa only [extend_orientation] using hr

/-- Travel along the exposed lane at any sweep frontier. -/
theorem Frame.lane_walk {S : Sweep N} {B : Board N N} {fixed : Finset (Cell N N)}
    (F : S.Frame B fixed) (j : ℕ) (a b : Fin N)
    (ha : S.line.laneSegment a) (hb : S.line.laneSegment b) :
    Reachable B (some 1) ⟨S.map (a, S.line.lane), S.boxes fixed j⟩
      ⟨S.map (b, S.line.lane), S.boxes fixed j⟩ := by
  obtain ⟨L, vertical⟩ := S
  cases vertical with
  | false =>
    have hF : L.Frame B fixed := ⟨F.fixed_floor, F.track_free, F.lane_free⟩
    change Reachable B (some 1) ⟨(a, L.lane), L.boxes fixed j⟩ ⟨(b, L.lane), L.boxes fixed j⟩
    exact hF.lane_walk j a b ha hb
  | true =>
    have hF : FiniteVerticalLineMacros.Frame L B fixed := ⟨F.fixed_floor, F.track_free, F.lane_free⟩
    change Reachable B (some 1)
      ⟨(L.lane, a), FiniteVerticalLineMacros.boxes L fixed j⟩
      ⟨(L.lane, b), FiniteVerticalLineMacros.boxes L fixed j⟩
    exact hF.lane_walk j a b ha hb

end PushPuzzle.PushS.FiniteSquareLine.Sweep
