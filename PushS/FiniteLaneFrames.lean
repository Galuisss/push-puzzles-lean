/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAFrame

/-! Ambient travel along the same narrow lanes used by the straight push programs. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS FiniteLineMacros FiniteSquareLine

variable {w h W H : ℕ}

namespace FiniteLineMacros.Line

private theorem laneProofFrame (L : Line w h) :
    L.Frame (FiniteWireFrame.board L.active ∅) ∅ where
  fixed_floor := Finset.disjoint_empty_left _
  track_free _x hx := ⟨(FiniteWireFrame.floor_iff _ _ _).mpr
    ((L.mem_active _).mpr (Or.inl ⟨rfl, hx⟩)), Finset.notMem_empty _⟩
  lane_free _x hx := ⟨(FiniteWireFrame.floor_iff _ _ _).mpr
    ((L.mem_active _).mpr (Or.inr ⟨rfl, hx⟩)), Finset.notMem_empty _⟩

/-- Walk the exposed lane at any frontier under the sweep's original narrow frame. -/
private theorem lane_walk_placed (L : Line w h) (e : GridEmbedding w h W H) {B : Board W H}
    {fixed : Finset (Cell W H)} (F : FiniteWireFrame.Frame L.active e B fixed)
    (j : ℕ) (a b : Fin w) (ha : L.laneSegment a) (hb : L.laneSegment b) :
    Reachable B (some 1)
      (e.extend fixed ⟨(a,L.lane), Finset.univ.image (L.position j)⟩)
      (e.extend fixed ⟨(b,L.lane), Finset.univ.image (L.position j)⟩) := by
  have hr := (laneProofFrame L).lane_walk j a b ha hb
  simp only [boxes, Finset.empty_union] at hr
  exact F.replay hr

end FiniteLineMacros.Line

namespace FiniteSquareLine.Sweep

private theorem point_orientation (S : Sweep w) (e : GridEmbedding w w W H)
    (fixed : Finset (Cell W H)) (j : ℕ) (p : Cell w w) :
    (S.embedding.trans e).extend fixed ⟨p, Finset.univ.image (S.line.position j)⟩ =
      e.extend fixed ⟨S.map p, Finset.univ.image (S.position j)⟩ := by
  apply State.ext
  · change e.cells (S.embedding.cells p) = e.cells (S.map p)
    rw [embedding_apply]
  · simp [GridEmbedding.extend, GridEmbedding.trans, Finset.map_eq_image,
      Finset.image_image, position, embedding_apply, Function.comp_def]

/-- Replay the real walking lane of a horizontal or vertical straight program. -/
private theorem lane_walk_placed (S : Sweep w) (e : GridEmbedding w w W H) {B : Board W H}
    {fixed : Finset (Cell W H)} (F : FiniteWireFrame.Frame S.active e B fixed)
    (j : ℕ) (a b : Fin w) (ha : S.line.laneSegment a) (hb : S.line.laneSegment b) :
    Reachable B (some 1)
      (e.extend fixed ⟨S.map (a,S.line.lane), Finset.univ.image (S.position j)⟩)
      (e.extend fixed ⟨S.map (b,S.line.lane), Finset.univ.image (S.position j)⟩) := by
  have F' : FiniteWireFrame.Frame S.line.active (S.embedding.trans e) B fixed := {
    floor p hp := F.floor (S.embedding.cells p) (Finset.mem_map.mpr ⟨p,hp,rfl⟩)
    fixed_avoids p hp := F.fixed_avoids (S.embedding.cells p) (Finset.mem_map.mpr ⟨p,hp,rfl⟩)
    fixed_floor := F.fixed_floor }
  have hr := S.line.lane_walk_placed (S.embedding.trans e) F' j a b ha hb
  simpa only [point_orientation] using hr

end FiniteSquareLine.Sweep

namespace FiniteGateAStraight.Segment

open FiniteGeometry FiniteGateState

/-- Lane travel keeps the entire mixed gate stock, including all shared tool neighbors. -/
theorem lane_walk_placed (w : ℕ) (b c q : Bool) (k : Segment)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (k.sweep w).active e B ((k.fixed w b c).map e.cells ∪ extra))
    (a d : Fin (side w)) (ha : (k.sweep w).line.laneSegment a)
    (hd : (k.sweep w).line.laneSegment d) :
    Reachable B (some 1)
      (e.extend extra ⟨(k.sweep w).map (a,(k.sweep w).line.lane),
        andMixedBoxes w (stage w b c (k.endpoint q))⟩)
      (e.extend extra ⟨(k.sweep w).map (d,(k.sweep w).line.lane),
        andMixedBoxes w (stage w b c (k.endpoint q))⟩) := by
  have he (p : Cell (side w) (side w)) :
      e.extend ((k.fixed w b c).map e.cells ∪ extra)
        ⟨p, Finset.univ.image ((k.sweep w).position (if q then k.count w else 0))⟩ =
      e.extend extra ⟨p, andMixedBoxes w (stage w b c (k.endpoint q))⟩ := by
    apply State.ext
    · rfl
    · rw [← k.boxes_endpoint w b c q]
      simp only [GridEmbedding.extend, Sweep.boxes, Finset.map_union]
      ac_rfl
  have hr := (k.sweep w).lane_walk_placed e F (if q then k.count w else 0) a d ha hd
  simpa only [he] using hr

end FiniteGateAStraight.Segment
end PushPuzzle.PushS
