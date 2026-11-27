/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPieces
public import PushS.FiniteCoreChartSafe
public import PushS.FiniteRoutingTurnClassifier
public import PushS.FiniteRoutingOrientedClassifier

/-! The complete actual rail and sink stencil inventory of every emitted primitive. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.PrimitiveCode

open PushFS PushFS.Reduction FiniteGeometry FiniteGateTracks FiniteGateStencils

attribute [local irreducible] side andWalls orWalls Line.width Line.height Line.walls FiniteTools.side

def Charts : PrimitiveCode → Type
  | .core g => match g.core.isAND with | true => AndChart | false => Unit
  | .line _ | .turn _ => Unit

/-- Actual translated stencils, in the exact dimensions and orientation of the emitted piece. -/
def chart (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    c.Charts → TranslatedAxisChart (c.instanceOf w hw).width (c.instanceOf w hw).height := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind
    · exact fun _ => orJunction w
    · exact andChart w hw
  | line c =>
    exact fun _ => Line.orientedRailChart w hw _ (Line.program_nonempty _ _ _) c.above
      (segmentDirection c.segment)
  | turn c => exact fun _ => Turn.stencilChart w c.incoming c.outgoing

theorem chart_walls (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (i : c.Charts)
    (p : Cell (c.chart w hw i).width (c.chart w hw i).height)
    (hp : p ∈ (c.chart w hw i).board.walls) :
    (c.chart w hw i).embedding.cells p ∈ (c.instanceOf w hw).board.walls := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind
    · change (orJunction w).embedding.cells p ∈ orWalls w
      exact orJunction_walls w hw p hp
    · change (andChart w hw i).embedding.cells p ∈ andWalls w
      exact andChart_walls w hw i p hp
  | line c => exact Line.orientedRailChart_walls w hw _ _ c.above _ p hp
  | turn c => exact Turn.stencilChart_walls w hw _ _ p hp

private theorem and_active (w : ℕ) (hw : 2 ≤ w) (s : PushFS.Gadgets.Gates.Signals) (l : AndLabel w) :
    ∃ i q, (andChart w hw i).embedding.cells q = andCell w s.left s.upper s.right l ∧
      (andChart w hw i).classifier.name q ≠ .outside := by
  obtain ⟨i,q,hq,hn⟩ := andNormal_represented w hw s.left s.upper s.right l
  refine ⟨i,q,hq,?_⟩
  intro hh
  rw [hh] at hn
  exact andTrack_active w l hn.symm

private theorem or_active (w : ℕ) (hw : 2 ≤ w) (s : PushFS.Gadgets.Gates.Signals) (l : OrLabel w) :
    ∃ q, (orJunction w).embedding.cells q = orCell w s.left s.upper s.right l ∧
      (orJunction w).classifier.name q ≠ .outside := by
  obtain ⟨q,hq,hn⟩ := orNormal_represented w hw s.left s.upper s.right l
  refine ⟨q,hq,?_⟩
  intro hh
  rw [hh] at hn
  exact orTrack_active w l hn.symm

private theorem line_active (w : ℕ) (hw : 2 ≤ w) (atoms : List Line.Atom) (above phase : Bool)
    (hne : atoms ≠ []) (d : Direction) (l : Line.Label w atoms) :
    ∃ q, (Line.orientedRailChart w hw atoms hne above d).embedding.cells q =
        (Line.rotation w atoms d).cells (Line.cell w hw atoms phase l) ∧
      (Line.orientedRailChart w hw atoms hne above d).classifier.name q ≠ .outside := by
  obtain ⟨q,hq,hn⟩ := Line.orientedRailChart_normal w hw atoms hne above d phase l
  refine ⟨q,hq,?_⟩
  intro hh
  rw [hh] at hn
  cases d <;> cases hn

/-- Every actual owned source and target label is active on one of its piece's literal stencils. -/
theorem chart_actor (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (goal : Bool) (l : c.Labels w) :
    ∃ i q, (c.chart w hw i).embedding.cells q =
        (if goal then (c.matching w hw).target l else (c.matching w hw).source l) ∧
      (c.chart w hw i).classifier.name q ≠ .outside := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind
    · cases goal
      · obtain ⟨q,hq,hn⟩ := or_active w hw s l
        exact ⟨(),q,hq,hn⟩
      · obtain ⟨q,hq,hn⟩ := or_active w hw t l
        exact ⟨(),q,hq,hn⟩
    · cases goal
      · exact and_active w hw s l
      · exact and_active w hw t l
  | line c =>
    cases goal
    · obtain ⟨q,hq,hn⟩ := line_active w hw _ c.above c.initial (Line.program_nonempty _ _ _) _ l.val
      exact ⟨(),q,hq,hn⟩
    · obtain ⟨q,hq,hn⟩ := line_active w hw _ c.above c.target (Line.program_nonempty _ _ _) _ l.val
      exact ⟨(),q,hq,hn⟩
  | turn c =>
    cases goal
    · obtain ⟨q,hq,hn⟩ := Turn.stencilChart_normal_active w c.incoming c.outgoing c.initial l
      exact ⟨(),q,hq,hn⟩
    · obtain ⟨q,hq,hn⟩ := Turn.stencilChart_normal_active w c.incoming c.outgoing c.target l
      exact ⟨(),q,hq,hn⟩

/-- The literal two rail ends, or three routed core ends, continued by neighboring pieces. -/
def Exit (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    Cell (c.instanceOf w hw).width (c.instanceOf w hw).height → Prop := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind
    · exact OrExit w
    · exact AndExit w
  | line c =>
    let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
    exact fun p => p = (Line.rotation w atoms (segmentDirection c.segment)).cells (Line.startCell w atoms) ∨
      p = (Line.rotation w atoms (segmentDirection c.segment)).cells (Line.cell w hw atoms true (Line.lastLabel w atoms))
  | turn c =>
    exact fun p => p = (Turn.orientation w c.incoming c.outgoing).cells
        ((Turn.stencilEmbedding w).cells ((0,3) : Cell 7 7)) ∨
      p = (Turn.orientation w c.incoming c.outgoing).cells
        ((Turn.stencilEmbedding w).cells ((3,6) : Cell 7 7))

def Owner (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (level : ℕ) : Prop :=
  ∃ i q, Interior q ∧ (c.chart w hw i).embedding.cells q = p ∧
    level ≤ ((c.chart w hw i).classifier.name q).level

/-- Every actual active floor cell has a safe interior owner or is a named endpoint of this real piece. -/
theorem chart_owner_or_exit (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (i : c.Charts)
    (p : Cell (c.chart w hw i).width (c.chart w hw i).height)
    (hp : (c.chart w hw i).classifier.name p ≠ .outside)
    (hf : (c.chart w hw i).embedding.cells p ∉ (c.instanceOf w hw).board.walls) :
    c.Exit w hw ((c.chart w hw i).embedding.cells p) ∨
      c.Owner w hw ((c.chart w hw i).embedding.cells p) ((c.chart w hw i).classifier.name p).level := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind
    · rcases orJunction_owner_or_exit w p hp with he | ⟨q,hx,hx',hy,hy',he,hl⟩
      · exact Or.inl he
      · exact Or.inr ⟨(),q,⟨hx,hx',hy,hy'⟩,he,hl⟩
    · rcases andChart_owner_or_exit w hw i p hp hf with he | ⟨j,q,hx,hx',hy,hy',he,hl⟩
      · exact Or.inl he
      · exact Or.inr ⟨j,q,⟨hx,hx',hy,hy'⟩,he,hl⟩
  | line c =>
    rcases Line.orientedRailChart_interior_or_ends w hw _ _ c.above _ p hp with hi | he
    · exact Or.inr ⟨(),p,hi,rfl,le_rfl⟩
    · exact Or.inl he
  | turn c =>
    rcases Turn.stencilChart_interior_or_ends w c.incoming c.outgoing p hp with hi | he
    · exact Or.inr ⟨(),p,hi,rfl,le_rfl⟩
    · exact Or.inl he

end PushPuzzle.PushS.FiniteRouting.PrimitiveCode
