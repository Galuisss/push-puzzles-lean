/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionClearance
public import PushS.FiniteRoutingGateRows
public import PushS.FiniteRoutingWorldCoordinates

/-! Normal inventory misses the two exposed sides of every actual routed line. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

/-- Eliminate an actual local primitive entry into its gate or wire source cell. -/
theorem localCodes_elim {w : ℕ} {code : CellPlan.Code} {c : PrimitiveCode}
    (hc : c ∈ FiniteSourceInventory.localCodes w code) {R : Prop}
    (gate : ∀ g : CellPlan.Gate, c ∈ gateCodes w g.2 → R)
    (wire : ∀ q : CellPlan.Wire, c ∈ wireCodes w q.2 → R) : R := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code => cases code with
    | inl g => exact gate g hc
    | inr q => exact wire q hc

/-- Dispatch two actual local primitives using their common source cell. -/
theorem localCodes_pair_elim {w : ℕ} {code : CellPlan.Code} {c d : PrimitiveCode}
    (hc : c ∈ FiniteSourceInventory.localCodes w code)
    (hd : d ∈ FiniteSourceInventory.localCodes w code) {R : Prop}
    (gate : ∀ g : CellPlan.Gate, c ∈ gateCodes w g.2 → d ∈ gateCodes w g.2 → R)
    (wire : ∀ q : CellPlan.Wire, c ∈ wireCodes w q.2 → d ∈ wireCodes w q.2 → R) : R := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code => cases code with
    | inl g => exact gate g hc hd
    | inr q => exact wire q hc hd

/-- The exposed side beyond the held first interface, including a straight terminal cap. -/
@[expose]
def CapSideBand (w : ℕ) (c : LineCode) (a : ℕ × ℕ) : Prop :=
  Outward (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 1) a ∧
    ¬SameLane (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0) a

/-- Moving the reference point farther along a ray strengthens its outward bound. -/
theorem outward_along_mono (w : ℕ) (d : Direction) (p a : ℕ × ℕ) (m n : ℕ)
    (hmn : m ≤ n) (ha : Outward d (Line.along w d p n) a) : Outward d (Line.along w d p m) a := by
  cases d <;> dsimp [Outward,Line.along] at ha ⊢ <;> omega

/-- An outgoing-side marker lies beyond every actor on the incoming perpendicular ray. -/
theorem JunctionContract.outgoing_ray_actor_ne {w : ℕ} {c d : LineCode} {t : TurnCode}
    (H : JunctionContract w c t d) (hw : 2 ≤ w) {a : ℕ × ℕ}
    (hb : Outward (segmentDirection d.segment) (Line.along w (segmentDirection d.segment) d.segment.start 1) a)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) : a ≠ (PrimitiveCode.line c).actor w hw goal l := by
  obtain ⟨n,hn,he⟩ := incoming_line_actor_ray w hw c t H.incoming_good H.incoming_last
    H.incoming_direction H.incoming_finish goal l
  rw [he]
  intro heq
  have h := hb
  rw [heq,H.outgoing_direction,H.outgoing_start] at h
  have ht := H.perpendicular
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at h <;>
    dsimp [Outward,Line.along,advance,Direction.opposite] at h <;> unfold padding at h <;> omega

/-- An incoming-side marker stops before the perpendicular outgoing ray. -/
theorem JunctionContract.incoming_ray_actor_ne {w : ℕ} {c d : LineCode} {t : TurnCode}
    (H : JunctionContract w c t d) (hw : 2 ≤ w) {a : ℕ × ℕ}
    (hb : Outward (segmentDirection c.segment).opposite (Line.along w (segmentDirection c.segment) c.segment.finish 0) a)
    (goal : Bool) (l : (PrimitiveCode.line d).Labels w) : a ≠ (PrimitiveCode.line d).actor w hw goal l := by
  obtain ⟨n,hn,he⟩ := outgoing_line_actor_ray w hw d t H.outgoing_good H.outgoing_first
    H.outgoing_direction H.outgoing_start goal l
  rw [he]
  intro heq
  have h := hb
  rw [heq,H.incoming_direction,H.incoming_finish] at h
  have ht := H.perpendicular
  have htravel := segment_travels c.segment H.incoming_good.1
  have hlen := H.incoming_good.2.1
  rw [H.incoming_direction,H.incoming_finish] at htravel
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at h htravel <;>
    dsimp [Outward,Line.along,advance,Direction.opposite,Travels] at h htravel <;> unfold padding at h <;> omega

namespace CapSideBand

private theorem own_actor_ne {w : ℕ} (hw : 2 ≤ w) {c : LineCode} (hc : LineGood w c.segment)
    {a : ℕ × ℕ} (ha : CapSideBand w c a) (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    a ≠ (PrimitiveCode.line c).actor w hw goal l := by
  rw [line_actor w hw c hc goal l]
  intro he
  apply ha.2
  rw [he]
  cases d : segmentDirection c.segment <;> simp [SameLane,Line.along]

private theorem collinear_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode}
    (hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection c.segment = segmentDirection d.segment)
    (hjoin : c.segment.finish = d.segment.start)
    {a : ℕ × ℕ} (ha : CapSideBand w c a) (goal : Bool) (l : (PrimitiveCode.line d).Labels w) :
    a ≠ (PrimitiveCode.line d).actor w hw goal l := by
  have ht := segment_travels c.segment hc.1
  rw [line_actor w hw d hd goal l,←hdir,←hjoin]
  intro he
  apply ha.2
  rw [he]
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at ht ⊢ <;>
    dsimp [Travels,SameLane,Line.along] at ht ⊢ <;> omega

private theorem previous_collinear_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode}
    (_hc : LineGood w c.segment) (hd : LineGood w d.segment)
    (hdir : segmentDirection d.segment = segmentDirection c.segment)
    (hjoin : d.segment.finish = c.segment.start)
    {a : ℕ × ℕ} (ha : CapSideBand w c a) (goal : Bool) (l : (PrimitiveCode.line d).Labels w) :
    a ≠ (PrimitiveCode.line d).actor w hw goal l := by
  have ht := segment_travels d.segment hd.1
  rw [hdir,hjoin] at ht
  rw [line_actor w hw d hd goal l,hdir]
  intro he
  apply ha.2
  rw [he]
  cases hdi : segmentDirection c.segment <;> simp only [hdi] at ht ⊢ <;>
    dsimp [Travels,SameLane,Line.along] at ht ⊢ <;> omega

private theorem outgoing_turn_actor_ne {w : ℕ} (hw : 2 ≤ w) {c : LineCode} {t : TurnCode}
    (_hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    {a : ℕ × ℕ} (ha : CapSideBand w c a) (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn t).actor w hw goal l := by
  rw [turn_actor w hw t ht goal l]
  intro he
  have h0 := ha.1
  have hn := ha.2
  rw [he,hd,hs] at h0 hn
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at h0 hn <;>
    dsimp [Outward,SameLane,Line.along,advance,Direction.opposite] at h0 hn <;>
    split_ifs at h0 hn <;> unfold padding at * <;> omega

private theorem outgoing_incoming_actor_ne {w : ℕ} (hw : 2 ≤ w) {c d : LineCode} {t : TurnCode}
    (H : JunctionContract w c t d) {a : ℕ × ℕ} (ha : CapSideBand w d a)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    a ≠ (PrimitiveCode.line c).actor w hw goal l := by
  exact H.outgoing_ray_actor_ne hw ha.1 goal l

end CapSideBand

/-- The longitudinal interior of a line, away from its working axis. -/
@[expose]
def SideBand (w : ℕ) (c : LineCode) (a : ℕ × ℕ) : Prop :=
  Outward (segmentDirection c.segment)
      (Line.along w (segmentDirection c.segment) c.segment.start 1) a ∧
    Outward (segmentDirection c.segment).opposite
      (Line.along w (segmentDirection c.segment) c.segment.finish 0) a ∧
    ¬SameLane (segmentDirection c.segment)
      (Line.along w (segmentDirection c.segment) c.segment.start 0) a

namespace SideBand

private theorem incoming_turn_actor_ne {w : ℕ} (hw : 2 ≤ w) {c : LineCode} {t : TurnCode}
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    {a : ℕ × ℕ} (ha : SideBand w c a) (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn t).actor w hw goal l := by
  have htravel := segment_travels c.segment hc.1
  have hlen := hc.2.1
  rw [hd,hf] at htravel
  rw [turn_actor w hw t ht goal l]
  intro he
  have h0 := ha.1
  have h1 := ha.2.1
  have hn := ha.2.2
  rw [he,hd,hf] at h1
  rw [he,hd] at hn
  have hi := Bool.toNat_le t.initial
  have hg := Bool.toNat_le t.target
  cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases l <;>
    simp [hdi,hdo,Perpendicular,rightTurn,Direction.opposite] at ht <;>
    simp only [hdi,hdo] at h1 hn htravel <;>
    dsimp [Outward,SameLane,Line.along,Travels,advance,Direction.opposite] at h1 hn htravel <;>
    split_ifs at h1 hn <;> unfold padding at * <;> omega

end SideBand

namespace LineCode

/-- Native coordinates of the actual rotated placement, centered at the held first slot. -/
theorem actionWorld_native (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w)) :
    c.actionWorld w hw p = match segmentDirection c.segment with
      | .east => (padding w+c.segment.start.1+p.1.val-FiniteTools.radius w,
          padding w+c.segment.start.2+p.2.val-FiniteTools.radius w)
      | .south => (padding w+c.segment.start.1+FiniteTools.radius w-p.2.val,
          padding w+c.segment.start.2+p.1.val-FiniteTools.radius w)
      | .west => (padding w+c.segment.start.1+FiniteTools.radius w-p.1.val,
          padding w+c.segment.start.2+FiniteTools.radius w-p.2.val)
      | .north => (padding w+c.segment.start.1+p.2.val-FiniteTools.radius w,
          padding w+c.segment.start.2+FiniteTools.radius w-p.1.val) := by
  rw [c.actionWorld_eq w hw p]
  have ht := segment_travels c.segment hc.1
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [Line.rotatedCoordinates,Travels,Line.offsetX,Line.offsetY,Line.anchor] at ht ⊢ <;>
    apply Prod.ext <;> simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,hlen,padding] at * <;> omega

/-- Bounds of an actual line-action cell after replacing its compiled program span. -/
theorem action_cell_bounds (w : ℕ) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w)) :
    p.1.val < 2*FiniteTools.radius w+segmentLength c.segment+2 ∧ p.2.val < 2*FiniteTools.radius w+1 := by
  simpa only [Line.width,Line.height,FiniteTools.side,Line.program_span_of_bound w _ _ hc.2.1] using And.intro p.1.isLt p.2.isLt

theorem sideBand_of_interior (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ p.1.val)
    (hx' : p.1.val ≤ FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)))
    (hy : p.2.val ≠ FiniteTools.radius w) : SideBand w c (c.actionWorld w hw p) := by
  have ht := segment_travels c.segment hc.1
  rw [c.actionWorld_native w hw hc p]
  have ⟨hpx,hpy⟩ := c.action_cell_bounds w hc p
  have hlen := Line.program_span_of_bound w _ (c.above != c.desiredSide) hc.2.1
  cases hd : segmentDirection c.segment <;> simp only [SideBand,hd] at ht ⊢ <;>
    dsimp [Outward,SameLane,Travels,Line.along,Direction.opposite] at ht ⊢ <;>
    simp only [FiniteTools.radius,hlen,padding] at * <;> omega

end LineCode

namespace LineCode

/-- A world point within the action margin of a literal line segment. -/
@[expose]
def NearTrace (w : ℕ) (c : LineCode) (a : ℕ × ℕ) : Prop :=
  ∃ u, c.segment.Contains u ∧ Nearby (w+2) a (padding w+u.1,padding w+u.2)

theorem interior_nearTrace (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hx : FiniteTools.radius w+1 ≤ p.1.val)
    (hx' : p.1.val ≤ FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)))
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1) :
    c.NearTrace w (c.actionWorld w hw p) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  let n := p.1.val-FiniteTools.radius w
  have hn : n ≤ segmentLength c.segment := by change _ ≤ FiniteTools.radius w+Line.span w atoms at hx'; omega
  have ht := segment_travels c.segment hc.1
  refine ⟨advance (segmentDirection c.segment) c.segment.start n,advance_contains _ _ _ _ n ht hn,?_⟩
  rw [c.actionWorld_native w hw hc p]
  have ⟨hpx,hpy⟩ := c.action_cell_bounds w hc p
  change p.1.val ≤ FiniteTools.radius w+Line.span w atoms at hx'
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [n,Nearby,advance,Travels] at ht ⊢ <;>
    simp only [FiniteTools.radius,hlen,padding] at * <;> omega

end LineCode

private structure LineCode.SideMarker (w : ℕ) (c : LineCode) (a : ℕ × ℕ) : Prop where
  nearTrace : c.NearTrace w a
  side : CapSideBand w c a
  beforeTurn : c.last = false → Outward (segmentDirection c.segment).opposite
    (Line.along w (segmentDirection c.segment) c.segment.finish 0) a

namespace PathSpec

theorem side_at (P : PathSpec) (w : ℕ) (G : P.Geometry w) (i : ℕ)
    (hi : i < P.segments.length) {a : ℕ × ℕ} (hp : (P.line i).NearTrace w a) :
    ∃ u, (segmentAt P.segments i).Contains u ∧ Nearby (w+2) a (padding w+u.1,padding w+u.2) := by
  obtain ⟨u,hu,ha⟩ := hp
  have hs := G.good _ (P.segment_mem i hi)
  exact ⟨u,trimmed_trace_subset _ hs.1 _ _
    (by have hf := startTrim_bound P.segments i; have hb := finishTrim_bound P.segments i
        have hl := hs.2.1; omega) hu,ha⟩

/-- A near-trace line marker avoids normal actors on every nonadjacent path line. -/
theorem nearTrace_ne_line_actor_far (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length) (hij : i+1 < j ∨ j+1 < i)
    {a : ℕ × ℕ} (hp : (P.line i).NearTrace w a) (goal : Bool) (l : (PrimitiveCode.line (P.line j)).Labels w) :
    a ≠ (PrimitiveCode.line (P.line j)).actor w hw goal l := by
  obtain ⟨u,hu,hu'⟩ := P.side_at w G i hi hp
  obtain ⟨v,hv,hv'⟩ := P.line_actor_at w hw G j hj goal l
  rcases hij with hij | hij
  · exact P.marks_ne w G i j hi hj hij (w+2) 1 (by unfold FiniteGeometry.origin; omega) hu hv hu' hv'
  · exact Ne.symm (P.marks_ne w G j i hj hi hij 1 (w+2) (by unfold FiniteGeometry.origin; omega) hv hu hv' hu')

/-- A near-trace line marker avoids a turn not adjoining that line. -/
theorem nearTrace_ne_turn_actor_far (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j) (hne : i ≠ j) (hne' : i ≠ j+1)
    {a : ℕ × ℕ} (hp : (P.line i).NearTrace w a) (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn (P.turn j)).actor w hw goal l := by
  obtain ⟨u,hu,hu'⟩ := P.side_at w G i hi hp
  have hv' := P.turn_actor_at w hw G j hj goal l
  by_cases hij : i < j
  · rw [P.join_eq w G j hj.1] at hv'
    exact P.marks_ne w G i (j+1) hi hj.1 (by omega) (w+2) 2 (by unfold FiniteGeometry.origin; omega)
      hu (P.start_contains w G (j+1) hj.1) hu' hv'
  · exact Ne.symm (P.marks_ne w G j i (by have := hj.1; omega) hi (by omega) 2 (w+2)
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by have := hj.1; omega)) hu hv' hu')

private theorem side_ne_line_actor (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length)
    (a : ℕ × ℕ) (h : (P.line i).SideMarker w a)
    (goal : Bool) (l : (PrimitiveCode.line (P.line j)).Labels w) :
    a ≠ (PrimitiveCode.line (P.line j)).actor w hw goal l := by
  by_cases he : i = j
  · subst j
    exact h.side.own_actor_ne hw (P.line_good w G i hi) goal l
  by_cases he' : j = i+1
  · subst j
    by_cases ht : P.hasTurn i
    · have H := P.junction_contract w G i ht
      exact H.incoming_ray_actor_ne hw (h.beforeTurn H.incoming_last) goal l
    · have H := P.collinear_contract w G i hj ht
      exact h.side.collinear_actor_ne hw H.first_good H.next_good H.directions H.joined goal l
  by_cases he'' : i = j+1
  · subst i
    by_cases ht : P.hasTurn j
    · exact h.side.outgoing_incoming_actor_ne hw (P.junction_contract w G j ht) goal l
    · have H := P.collinear_contract w G j hi ht
      exact h.side.previous_collinear_actor_ne hw H.next_good H.first_good H.directions H.joined goal l
  exact P.nearTrace_ne_line_actor_far w hw G i j hi hj (by omega) h.nearTrace goal l

private theorem side_ne_turn_actor (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (a : ℕ × ℕ) (h : (P.line i).SideMarker w a)
    (goal : Bool) (l : Fin 2) :
    a ≠ (PrimitiveCode.turn (P.turn j)).actor w hw goal l := by
  have H := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    exact SideBand.incoming_turn_actor_ne hw H.incoming_good H.perpendicular H.incoming_direction H.incoming_finish
      ⟨h.side.1,h.beforeTurn H.incoming_last,h.side.2⟩ goal l
  by_cases he' : i = j+1
  · subst i
    exact h.side.outgoing_turn_actor_ne hw H.outgoing_good H.perpendicular H.outgoing_direction H.outgoing_start goal l
  exact P.nearTrace_ne_turn_actor_far w hw G i j hi hj he he' h.nearTrace goal l

private theorem side_ne_codes_actor (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length)
    (a : ℕ × ℕ) (h : (P.line i).SideMarker w a)
    (c : PrimitiveCode) (hc : c ∈ P.codes) (goal : Bool) (l : c.Labels w) :
    a ≠ c.actor w hw goal l := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  have hj' := List.mem_range.mp hj
  rcases (P.mem_block j c).mp hc with rfl | ⟨ht,rfl⟩
  · exact P.side_ne_line_actor w hw G i j hi hj' a h goal l
  · exact P.side_ne_turn_actor w hw G i j hi ht a h goal l

end PathSpec

/-- A normal core actor stays outside a padded marker on an arm tail. -/
theorem core_tail_actor_ne (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) (margin : ℕ)
    (hm : margin ≤ FiniteGeometry.origin w) {u a : ℕ × ℕ}
    (hu : ∃ s ∈ (armRoute w g role).tail, s.Contains u)
    (ha : Nearby margin a (padding w+u.1,padding w+u.2))
    (goal : Bool) (l : (PrimitiveCode.core g).Labels w) : a ≠ (PrimitiveCode.core g).actor w hw goal l :=
  core_tail_ne w hw g role margin hm hu ha
    (if goal then (PrimitiveCode.matching w hw (.core g)).target l else (PrimitiveCode.matching w hw (.core g)).source l)

private theorem gate_side_actor_ne (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : .line c ∈ gateCodes w g)
    (a : ℕ × ℕ) (h : c.SideMarker w a)
    (d : PrimitiveCode) (hd : d ∈ gateCodes w g) (goal : Bool) (l : d.Labels w) :
    a ≠ d.actor w hw goal l := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  obtain ⟨u,hu,hu'⟩ := P.side_at w G i hi h.nearTrace
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · by_cases hz : i = 0
    · subst i
      intro he
      have h0 := h.side.1
      have hn := h.side.2
      rw [he,armSpec_first_direction,armSpec_first_start] at h0 hn
      have ho : Outward (PortAnnulus.innerDirection role)
          (Line.along w (PortAnnulus.innerDirection role) (corePort w g.core.isAND role) 0)
          ((PrimitiveCode.core g).actor w hw goal l) := by
        cases hdir : PortAnnulus.innerDirection role <;> simp only [hdir] at h0 ⊢ <;>
          dsimp [Outward,Line.along] at h0 ⊢ <;> omega
      exact hn (core_actor_outward_lane w hw g role goal l ho)
    · exact core_tail_actor_ne w hw g role (w+2) (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi (by omega),hu⟩ hu' goal l
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases he : role = other
    · subst other
      exact P.side_ne_codes_actor w hw G i hi a h d hd goal l
    · obtain ⟨v,hv,hv'⟩ := (armSpec w g other).code_actor_trace w hw (armSpec_geometry w g other) d hd goal l
      apply footprint_ne (w := w) (m := w+2) (n := 2) _ hu' hv'
      intro hnear
      exact armRoutes_separated_wide w g he ⟨_,P.segment_mem i hi,hu⟩ hv (nearby_of_le (by omega) hnear)

/-- Side markers need the finish bound only when the line enters a turn. -/
theorem local_side_actor_ne_of_guard (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : c.NearTrace w (c.actionWorld w hw p))
    (ha : CapSideBand w c (c.actionWorld w hw p))
    (hguard : c.last = false → Outward (segmentDirection c.segment).opposite
      (Line.along w (segmentDirection c.segment) c.segment.finish 0) (c.actionWorld w hw p))
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : d.Labels w) :
    c.actionWorld w hw p ≠ d.actor w hw goal l := by
  exact localCodes_pair_elim hc hd
    (fun g hcg hdg => gate_side_actor_ne w hw g.2 c hcg _ ⟨hp,ha,hguard⟩ d hdg goal l)
    (fun q hcq hdq => by
      obtain ⟨i,hi,rfl⟩ := (wireSpec w q.2).line_code_origin c hcq
      exact (wireSpec w q.2).side_ne_codes_actor w hw (wireSpec_geometry w q.2) i hi _ ⟨hp,ha,hguard⟩ d hdq goal l)

/-- The longitudinal interior side band avoids every normal actor of its source cell. -/
theorem local_side_actor_ne (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : c.NearTrace w (c.actionWorld w hw p))
    (ha : SideBand w c (c.actionWorld w hw p))
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : d.Labels w) :
    c.actionWorld w hw p ≠ d.actor w hw goal l := by
  exact local_side_actor_ne_of_guard w hw code c hc p hp ⟨ha.1,ha.2.2⟩ (fun _ => ha.2.1) d hd goal l

end PushPuzzle.PushS.FiniteRouting
