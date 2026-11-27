/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FrameWalking
public import PushS.PortEndpointIndexing
public import PushS.PortLayoutCoordinates
import all PushS.PortSegments
import all PushS.PortSegmentBounds
import all PushS.PortEndpointSeparation

/-!
# Walking from the actual empty frame to endpoint streets

The complete encoded hole set contains every cell of each actual endpoint's f/r corridor.
The long corridor segments survive conditional point rounding. Explicit frame and vertical
walks reach their precise player cells while keeping the complete box set fixed.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The actual long f street or short r reader street of an ordinary endpoint. -/
inductive EndpointStreet where
  | f
  | r
  deriving DecidableEq

namespace EndpointStreet

/-- Read the selected street column from the actual endpoint coordinates. -/
def column (k : EndpointStreet) (p : Scales.Parameters) (e : Endpoint) : ℕ :=
  match k with
  | .f => (auxiliary (coordinates p) e).1
  | .r => (auxiliary (coordinates p) e).2

/-- The actual f column is one allocated long-branch length outward from the axis. -/
theorem column_f (p : Scales.Parameters) (e : Endpoint) :
    EndpointStreet.f.column p e = if e.inward then p.x e.port - readLength p e.level
      else p.x e.port + readLength p e.level := by rfl

/-- The actual r reader column is two cells inward from the axis. -/
theorem column_r (p : Scales.Parameters) (e : Endpoint) :
    EndpointStreet.r.column p e = if e.inward then p.x e.port + 2 else p.x e.port - 2 := by rfl

/-- Last depth of the corresponding actual vertical corridor, measured from its page frame. -/
@[expose] def limit (k : EndpointStreet) (p : Scales.Parameters) (e : Endpoint) : ℕ :=
  match k with
  | .f => readDepth p e.level + 2
  | .r => readDepth p e.level - 1

private theorem column_le (k : EndpointStreet) (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    k.column p e ≤ p.W := by
  have hb := l.endpoints_port_lt hl he
  have hm := auxiliary_margin p e (by omega)
  cases k <;> dsimp only [column] <;> omega

private theorem limit_le (k : EndpointStreet) (p : Scales.Parameters) (e : Endpoint) :
    k.limit p e < p.H := by
  have hd := readDepth_add_lt_H p e.level
  cases k <;> dsimp only [limit] <;> omega

end EndpointStreet

/-- The actual finite cell at the specified depth on the selected f/r corridor. -/
@[expose] def endpointStreetCell (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet)
    (depth : ℕ) (hd : depth ≤ k.limit p e) : Cell (p.W + 1) (p.H + 1) :=
  (⟨k.column p e, by have := k.column_le l p hl ha e he; omega⟩,
    ⟨if e.side = .upper then depth else p.H - depth, by
      have := k.limit_le p e
      split <;> omega⟩)

private def streetSegment (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet) : Segment :=
  segment (k.column p e) (onSide (coordinates p) e.side 1) (k.column p e)
    (onSide (coordinates p) e.side (k.limit p e))

private theorem streetSegment_mem (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (k : EndpointStreet) : streetSegment p e k ∈ endpointFixedSegments l (coordinates p) e := by
  have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
  cases k <;>
    simp [streetSegment, EndpointStreet.column, EndpointStreet.limit, endpointFixedSegments, hd]

private theorem streetSegment_ne (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint)
    (he : e ∈ l.endpoints) (k : EndpointStreet) :
    (streetSegment p e k).start ≠ (streetSegment p e k).finish := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hlo := readDepth_ge p hj hm
  have hhi := readDepth_add_lt_H p e.level
  have hH : (coordinates p).H = p.H := rfl
  intro h
  have hy := congrArg (fun q : ℕ × ℕ => q.2) h
  cases k <;> cases hs : e.side <;>
    simp only [streetSegment, EndpointStreet.limit, segment, onSide, hs, hH,
      reduceCtorEq, ite_true, ite_false] at hy <;> omega

private theorem long_segment_mem_fixed (l : PortLayout) (p : Scales.Parameters)
    {s : Segment} (hs : s ∈ interiorFixed l (coordinates p)) (hne : s.start ≠ s.finish) :
    s ∈ l.fixedSegments p := by
  unfold fixedSegments
  apply List.mem_append_right
  unfold markedInterior
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  split
  · apply List.mem_map.mpr
    exact ⟨s, hs, by simp [shiftPoint, hne]⟩
  · exact hs

private theorem streetSegment_fixed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint)
    (he : e ∈ l.endpoints) (k : EndpointStreet) : streetSegment p e k ∈ l.fixedSegments p := by
  apply long_segment_mem_fixed l p _ (streetSegment_ne l p hl hM e he k)
  unfold interiorFixed
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨e, he, streetSegment_mem l p e k⟩

/-- Every specified f/r corridor cell is a real hole of the complete marked encoding. -/
theorem endpointStreet_hole (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) (depth : ℕ)
    (hd : depth ≤ k.limit p e) :
    endpointStreetCell l p hl ha e he k depth hd ∈
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change holeTest (l.encodedSegments p state,
    k.column p e, if e.side = .upper then depth else p.H - depth) = true
  apply (l.holeTest_encodedSegments p state _).mpr
  left
  by_cases hz : depth = 0
  · subst depth
    apply l.horizontal_frame_empty p _ (k.column_le l p hl ha e he)
    cases e.side <;> simp
  · apply (holeTest_eq_true _ _).mpr
    refine ⟨streetSegment p e k, streetSegment_fixed l p hl hM e he k, ?_⟩
    have hb := k.limit_le p e
    have hH : (coordinates p).H = p.H := rfl
    cases hs : e.side <;>
      simp only [streetSegment, segment, Segment.Contains, onSide, hs, hH,
        reduceCtorEq, ite_true, ite_false] <;> omega

/-- The complete physical encoding with the player at the empty north-west frame corner. -/
@[expose] def cornerState (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    HoleState (p.W + 1) (p.H + 1) where
  player := (⟨0, by omega⟩, ⟨0, by omega⟩)
  empty := SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)
  player_empty := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (l.holeTest_encodedSegments p state (0, 0)).mpr
      (Or.inl (l.horizontal_frame_empty p (Or.inl rfl) (Nat.zero_le _)))

/-- The same complete hole set with its player at the precise selected endpoint street cell. -/
@[expose] def endpointStreetState (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) (depth : ℕ)
    (hd : depth ≤ k.limit p e) : HoleState (p.W + 1) (p.H + 1) :=
  (l.cornerState p state).walk (endpointStreetCell l p hl ha e he k depth hd)
    (by exact endpointStreet_hole l p hl hM ha state e he k depth hd)

/-- The point on the north or south frame directly above or below the specified column. -/
@[expose] def pageFrameCell (p : Scales.Parameters) (side : Side) (x : Fin (p.W + 1)) :
    Cell (p.W + 1) (p.H + 1) :=
  (x, ⟨if side = .upper then 0 else p.H, by split <;> omega⟩)

/-- The selected north/south frame cell is empty in every complete physical encoding. -/
theorem pageFrame_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (side : Side) (x : Fin (p.W + 1)) : pageFrameCell p side x ∈ (l.cornerState p state).empty := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (l.holeTest_encodedSegments p state _).mpr
  left
  apply l.horizontal_frame_empty p _ (by have := x.isLt; omega)
  cases side <;> simp [pageFrameCell]

/-- The complete physical hole set with the player at a specified page-frame cell. -/
@[expose] def pageFrameState (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (side : Side) (x : Fin (p.W + 1)) : HoleState (p.W + 1) (p.H + 1) :=
  (l.cornerState p state).walk (pageFrameCell p side x) (l.pageFrame_hole p state side x)

private theorem west_frame_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (y : Fin (p.H + 1)) : ((0 : Fin (p.W + 1)), y) ∈ (l.cornerState p state).empty := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (l.holeTest_encodedSegments p state (0, y.val)).mpr
    (Or.inl (l.vertical_frame_empty p (Or.inl rfl) (by have := y.isLt; omega)))

private theorem walk_west_frame (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    Reachable B cap (l.cornerState p state).toState (l.pageFrameState p state .lower 0).toState := by
  exact (l.cornerState p state).walk_along B hB cap .south p.H
    (fun y => (0, y)) rfl (by intro i; constructor <;> rfl) (l.west_frame_hole p state)

private theorem walk_horizontal_frame (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ)
    (side : Side) (x : Fin (p.W + 1)) :
    Reachable B cap (l.pageFrameState p state side 0).toState (l.pageFrameState p state side x).toState := by
  let cell : Fin (x.val + 1) → Cell (p.W + 1) (p.H + 1) :=
    fun i => pageFrameCell p side ⟨i.val, by have := x.isLt; omega⟩
  exact (l.pageFrameState p state side 0).walk_along B hB cap .east x.val cell rfl
    (by intro i; constructor <;> rfl) (fun i => l.pageFrame_hole p state side _)

/-- Walk from `(0,0)` along the actual frame to any north/south page-frame cell. -/
theorem pageFrame_reachable (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ)
    (side : Side) (x : Fin (p.W + 1)) :
    Reachable B cap (l.cornerState p state).toState (l.pageFrameState p state side x).toState := by
  cases side with
  | upper => exact walk_horizontal_frame l p state B hB cap .upper x
  | lower =>
    exact (walk_west_frame l p state B hB cap).trans
      (walk_horizontal_frame l p state B hB cap .lower x)

private theorem walk_endpoint_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) (depth : ℕ)
    (hd : depth ≤ k.limit p e) (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    Reachable B cap
      (l.pageFrameState p state e.side (endpointStreetCell l p hl ha e he k depth hd).1).toState
      (l.endpointStreetState p hl hM ha state e he k depth hd).toState := by
  let cell : Fin (depth + 1) → Cell (p.W + 1) (p.H + 1) := fun i =>
    endpointStreetCell l p hl ha e he k i.val (by have := i.isLt; omega)
  let direction : Direction := if e.side = .upper then .south else .north
  have hadj (i : Fin depth) : Adjacent direction (cell i.castSucc) (cell i.succ) := by
    have hb := k.limit_le p e
    have hi := i.isLt
    cases hs : e.side <;>
      simp only [cell, endpointStreetCell, direction, hs, reduceCtorEq, ite_true, ite_false,
        Adjacent, Fin.val_castSucc, Fin.val_succ]
    all_goals constructor
    all_goals first | trivial | omega
  exact (l.pageFrameState p state e.side (endpointStreetCell l p hl ha e he k depth hd).1).walk_along
    B hB cap direction depth cell rfl hadj
    (fun i => endpointStreet_hole l p hl hM ha state e he k i.val (by have := i.isLt; omega))

/-- Reach any actual f/r corridor depth from `(0,0)` using frame and corridor walks only. -/
theorem endpointStreet_reachable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) (depth : ℕ)
    (hd : depth ≤ k.limit p e) (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    Reachable B cap (l.cornerState p state).toState
      (l.endpointStreetState p hl hM ha state e he k depth hd).toState :=
  (l.pageFrame_reachable p state B hB cap e.side
    (endpointStreetCell l p hl ha e he k depth hd).1).trans
      (walk_endpoint_street l p hl hM ha state e he k depth hd B hB cap)

/-- The walking target has exactly the requested player and the original complete box set. -/
theorem endpointStreetState_spec (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) (depth : ℕ)
    (hd : depth ≤ k.limit p e) :
    (l.endpointStreetState p hl hM ha state e he k depth hd).player =
        endpointStreetCell l p hl ha e he k depth hd ∧
      (l.endpointStreetState p hl hM ha state e he k depth hd).toState.boxes =
        (l.cornerState p state).toState.boxes := ⟨rfl, rfl⟩

end PushPuzzle.PushS.PortLayout
