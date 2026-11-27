/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSideStock
public import PushS.FiniteRoutingActorBounds

/-! Deep working-row cells meet only their own primitive's normal stock. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

/-- A row point with two clear support cells at both shared interfaces. -/
@[expose]
def DeepBand (w : ℕ) (c : LineCode) (a : ℕ × ℕ) : Prop :=
  Outward (segmentDirection c.segment)
      (Line.along w (segmentDirection c.segment) c.segment.start 3) a ∧
    Outward (segmentDirection c.segment).opposite
      (Line.along w (segmentDirection c.segment).opposite c.segment.finish 2) a

namespace DeepBand

private theorem next_collinear_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode}
    (hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection c.segment = segmentDirection d.segment)
    (hjoin : c.segment.finish = d.segment.start)
    {a : ℕ × ℕ} (ha : DeepBand w c a) (goal : Bool) (l : (PrimitiveCode.line d).Labels w) :
    a ≠ (PrimitiveCode.line d).actor w hw goal l := by
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  let phase := if goal then d.target else d.initial
  have hb := Line.positions_bounds w hw phase _ (Line.position_mem w _ phase l.val)
  rw [line_actor w hw d hd goal l,←hdir,←hjoin]
  intro he
  have h := ha.2
  rw [he] at h
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at h htravel <;>
    dsimp [Outward,Line.along,advance,Travels,Direction.opposite] at h htravel <;> unfold padding at h <;> omega

private theorem previous_collinear_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode}
    (_hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection d.segment = segmentDirection c.segment)
    (hjoin : d.segment.finish = c.segment.start)
    {a : ℕ × ℕ} (ha : DeepBand w c a) (goal : Bool) (l : (PrimitiveCode.line d).Labels w) :
    a ≠ (PrimitiveCode.line d).actor w hw goal l := by
  have ht := segment_travels d.segment hd.1
  rw [hdir,hjoin] at ht
  let phase := if goal then d.target else d.initial
  have hb := Line.positions_bounds w hw phase _ (Line.position_mem w _ phase l.val)
  have hlen := Line.program_span_of_bound w _ (d.above != d.desiredSide) hd.2.1
  rw [hlen] at hb
  have hphase := Bool.toNat_le phase
  dsimp only [phase] at hb hphase
  rw [line_actor w hw d hd goal l,hdir]
  intro he
  have h := ha.1
  rw [he] at h
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at h ht <;>
    dsimp [Outward,Line.along,Travels,Direction.opposite] at h ht <;> unfold padding at h <;> omega

private theorem incoming_turn_actor_ne {w : ℕ} (hw : 2 ≤ w) {c : LineCode} {t : TurnCode}
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    {a : ℕ × ℕ} (ha : DeepBand w c a) (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn t).actor w hw goal l := by
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  rw [hd,hf] at htravel
  rw [turn_actor w hw t ht goal l]
  intro he
  have h := ha.2
  rw [he,hd,hf] at h
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at h htravel <;>
    dsimp [Outward,Line.along,Travels,advance,Direction.opposite] at h htravel <;>
    (try split_ifs at h) <;> unfold padding at * <;> omega

private theorem outgoing_turn_actor_ne {w : ℕ} (hw : 2 ≤ w) {c : LineCode} {t : TurnCode}
    (_hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    {a : ℕ × ℕ} (ha : DeepBand w c a) (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn t).actor w hw goal l := by
  rw [turn_actor w hw t ht goal l]
  intro he
  have h := ha.1
  rw [he,hd,hs] at h
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at h <;>
    dsimp [Outward,Line.along,advance,Direction.opposite] at h <;>
    (try split_ifs at h) <;> unfold padding at * <;> omega

private theorem incoming_outgoing_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode} {t : TurnCode}
    (H : JunctionContract w c t d) {a : ℕ × ℕ} (ha : DeepBand w c a)
    (goal : Bool) (l : (PrimitiveCode.line d).Labels w) :
    a ≠ (PrimitiveCode.line d).actor w hw goal l := by
  have h0 := outward_along_mono w (segmentDirection c.segment).opposite c.segment.finish a 0 2 (by decide) ha.2
  have hb : Outward (segmentDirection c.segment).opposite (Line.along w (segmentDirection c.segment) c.segment.finish 0) a := by
    cases hd : segmentDirection c.segment <;> simpa only [hd,Direction.opposite,Line.along,Nat.add_zero,Nat.sub_zero] using h0
  exact H.incoming_ray_actor_ne hw hb goal l

private theorem outgoing_incoming_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode} {t : TurnCode}
    (H : JunctionContract w c t d) {a : ℕ × ℕ} (ha : DeepBand w d a)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    a ≠ (PrimitiveCode.line c).actor w hw goal l := by
  exact H.outgoing_ray_actor_ne hw
    (outward_along_mono w (segmentDirection d.segment) d.segment.start a 1 3 (by decide) ha.1) goal l

end DeepBand

namespace LineCode

theorem deep_row_band (w : ℕ) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment) :
    DeepBand w c (Line.along w (segmentDirection c.segment) c.segment.start n) := by
  have ht := segment_travels c.segment hc.1
  cases hd : segmentDirection c.segment <;> simp only [DeepBand,hd] at ht ⊢ <;>
    dsimp [Outward,Line.along,Direction.opposite,Travels] at ht ⊢ <;> unfold padding <;> omega

theorem deep_row_nearTrace (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment) :
    c.NearTrace w (Line.along w (segmentDirection c.segment) c.segment.start n) := by
  obtain ⟨u,hu,ha⟩ := c.row_footprint w hw hc n (by omega)
  refine ⟨u,hu,?_⟩
  rw [rowWorld_eq] at ha
  exact nearby_of_le (by omega) ha

private theorem horizontal_inner (w x x' y : ℕ) (hne : x ≠ x')
    (h0 : ∀ face, InCollar w face (x,y) → SameLane face (Line.along w face (boundaryPoint w face) 0) (x,y))
    (h1 : ∀ face, InCollar w face (x',y) → SameLane face (Line.along w face (boundaryPoint w face) 0) (x',y)) :
    padding w+2 ≤ y ∧ y+2 ≤ tileStride w+padding w := by
  have hp : 2 ≤ padding w := by unfold padding; omega
  constructor
  · by_contra hh
    have h0' := h0 .north (by change y ≤ 2*padding w; omega)
    have h1' := h1 .north (by change y ≤ 2*padding w; omega)
    change padding w+25*spacing w = x at h0'
    change padding w+25*spacing w = x' at h1'
    exact hne (h0'.symm.trans h1')
  · by_contra hh
    have h0' := h0 .south (by change tileStride w ≤ y; omega)
    have h1' := h1 .south (by change tileStride w ≤ y; omega)
    change padding w+25*spacing w = x at h0'
    change padding w+25*spacing w = x' at h1'
    exact hne (h0'.symm.trans h1')

private theorem vertical_inner (w x y y' : ℕ) (hne : y ≠ y')
    (h0 : ∀ face, InCollar w face (x,y) → SameLane face (Line.along w face (boundaryPoint w face) 0) (x,y))
    (h1 : ∀ face, InCollar w face (x,y') → SameLane face (Line.along w face (boundaryPoint w face) 0) (x,y')) :
    padding w+2 ≤ x ∧ x+2 ≤ tileStride w+padding w := by
  have hp : 2 ≤ padding w := by unfold padding; omega
  constructor
  · by_contra hh
    have h0' := h0 .west (by change x ≤ 2*padding w; omega)
    have h1' := h1 .west (by change x ≤ 2*padding w; omega)
    change padding w+25*spacing w = y at h0'
    change padding w+25*spacing w = y' at h1'
    exact hne (h0'.symm.trans h1')
  · by_contra hh
    have h0' := h0 .east (by change tileStride w ≤ x; omega)
    have h1' := h1 .east (by change tileStride w ≤ x; omega)
    change padding w+25*spacing w = y at h0'
    change padding w+25*spacing w = y' at h1'
    exact hne (h0'.symm.trans h1')

private theorem deep_row_bounds_of_lanes (w : ℕ) (c : LineCode) (hg : LineGood w c.segment)
    (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment)
    (hrow0 : ∀ face, InCollar w face (Line.along w (segmentDirection c.segment) c.segment.start 0) →
      SameLane face (Line.along w face (boundaryPoint w face) 0)
        (Line.along w (segmentDirection c.segment) c.segment.start 0))
    (hrow1 : ∀ face, InCollar w face (Line.along w (segmentDirection c.segment) c.segment.start (segmentLength c.segment)) →
      SameLane face (Line.along w face (boundaryPoint w face) 0)
        (Line.along w (segmentDirection c.segment) c.segment.start (segmentLength c.segment))) :
    let a := Line.along w (segmentDirection c.segment) c.segment.start n
    padding w+2 ≤ a.1 ∧ a.1+2 ≤ tileStride w+padding w ∧
      padding w+2 ≤ a.2 ∧ a.2+2 ≤ tileStride w+padding w := by
  have ht := segment_travels c.segment hg.1
  have hlen := hg.2.1
  have hstart := hg.2.2.1
  have hfinish := hg.2.2.2
  dsimp only
  cases hd : segmentDirection c.segment <;>
    simp only [hd] at hrow0 hrow1 ht ⊢ <;>
    dsimp only [Line.along,Travels,Nat.sub_zero,Nat.add_zero] at hrow0 hrow1 ht ⊢
  · have htrans := vertical_inner w _ _ _ (by unfold padding; omega) hrow0 hrow1
    clear hrow0 hrow1 hg
    unfold padding at *
    omega
  · have htrans := horizontal_inner w _ _ _ (by unfold padding; omega) hrow0 hrow1
    clear hrow0 hrow1 hg
    unfold padding at *
    omega
  · have htrans := vertical_inner w _ _ _ (by unfold padding; omega) hrow0 hrow1
    clear hrow0 hrow1 hg
    unfold padding at *
    omega
  · have htrans := horizontal_inner w _ _ _ (by unfold padding; omega) hrow0 hrow1
    clear hrow0 hrow1 hg
    unfold padding at *
    omega

theorem deep_row_inner_bounds (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code)
    (c : LineCode) (hc : .line c ∈ FiniteSourceInventory.localCodes w code)
    (hg : LineGood w c.segment) (n : ℕ) (hn : 3 ≤ n) (hn' : n+2 ≤ segmentLength c.segment) :
    let a := Line.along w (segmentDirection c.segment) c.segment.start n
    padding w+2 ≤ a.1 ∧ a.1+2 ≤ tileStride w+padding w ∧
      padding w+2 ≤ a.2 ∧ a.2+2 ≤ tileStride w+padding w := by
  have hrow0 (face : Direction) :
      InCollar w face (Line.along w (segmentDirection c.segment) c.segment.start 0) →
      SameLane face (Line.along w face (boundaryPoint w face) 0)
        (Line.along w (segmentDirection c.segment) c.segment.start 0) := by
    have he := LineCode.rowWorld_eq w hw c hg 0 (Nat.zero_le _)
    simpa only [he] using local_row_collar_lane w hw code c hc hg 0 (Nat.zero_le _) face
  have hrow1 (face : Direction) :
      InCollar w face (Line.along w (segmentDirection c.segment) c.segment.start (segmentLength c.segment)) →
      SameLane face (Line.along w face (boundaryPoint w face) 0)
        (Line.along w (segmentDirection c.segment) c.segment.start (segmentLength c.segment)) := by
    have he := LineCode.rowWorld_eq w hw c hg (segmentLength c.segment) (Nat.le_succ _)
    simpa only [he] using local_row_collar_lane w hw code c hc hg (segmentLength c.segment) (Nat.le_succ _) face
  exact deep_row_bounds_of_lanes w c hg n hn hn' hrow0 hrow1

end LineCode

namespace PathSpec

private theorem deep_ne_line_actor (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length)
    (a : ℕ × ℕ) (hp : (P.line i).NearTrace w a) (ha : DeepBand w (P.line i) a)
    (hown : ∀ goal l, a ≠ (PrimitiveCode.line (P.line i)).actor w hw goal l)
    (goal : Bool) (l : (PrimitiveCode.line (P.line j)).Labels w) :
    a ≠ (PrimitiveCode.line (P.line j)).actor w hw goal l := by
  by_cases he : i = j
  · subst j
    exact hown goal l
  by_cases he' : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · exact ha.incoming_outgoing_actor_ne hw (P.junction_contract w G i ht) goal l
    · have H := P.collinear_contract w G i hj ht
      exact ha.next_collinear_actor_ne hw H.first_good H.next_good H.directions H.joined goal l
  by_cases he'' : i = j+1
  · subst i
    by_cases ht : P.hasTurn j
    · exact ha.outgoing_incoming_actor_ne hw (P.junction_contract w G j ht) goal l
    · have H := P.collinear_contract w G j hi ht
      exact ha.previous_collinear_actor_ne hw H.next_good H.first_good H.directions H.joined goal l
  exact P.nearTrace_ne_line_actor_far w hw G i j hi hj (by omega) hp goal l

private theorem deep_ne_turn_actor (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (a : ℕ × ℕ) (hp : (P.line i).NearTrace w a) (ha : DeepBand w (P.line i) a)
    (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn (P.turn j)).actor w hw goal l := by
  have H := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    exact ha.incoming_turn_actor_ne hw H.incoming_good H.perpendicular H.incoming_direction H.incoming_finish goal l
  by_cases he' : i = j+1
  · subst i
    exact ha.outgoing_turn_actor_ne hw H.outgoing_good H.perpendicular H.outgoing_direction H.outgoing_start goal l
  exact P.nearTrace_ne_turn_actor_far w hw G i j hi hj he he' hp goal l

theorem deep_ne_codes_actor (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length)
    (a : ℕ × ℕ) (hp : (P.line i).NearTrace w a) (ha : DeepBand w (P.line i) a)
    (hown : ∀ goal l, a ≠ (PrimitiveCode.line (P.line i)).actor w hw goal l)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (goal : Bool) (l : c.Labels w) :
    a ≠ c.actor w hw goal l := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  have hj' := List.mem_range.mp hj
  rcases (P.mem_block j c).mp hc with rfl | ⟨ht,rfl⟩
  · exact P.deep_ne_line_actor w hw G i j hi hj' a hp ha hown goal l
  · exact P.deep_ne_turn_actor w hw G i j hi ht a hp ha goal l

end PathSpec

end PushPuzzle.PushS.FiniteRouting
