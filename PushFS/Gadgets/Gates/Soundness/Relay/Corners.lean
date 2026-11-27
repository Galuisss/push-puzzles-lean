/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.Sinks
public import PushFS.Gadgets.Wires.Soundness.Corner

/-! The two actual guarded AND turns propagate signals through their real immutable corner cells. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


open Wires.Soundness Wires.Polyline

variable {I : Instance} {L : Type} [Fintype L]

/-- Transport the literal two-box corner obstruction along a complete physical path. -/
theorem oriented_corner_good {M : SlotMatching I L} {S final : LabelledState L I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (e : GridIsometry I.width I.height I.width I.height) (j y : ℕ) (i k : L)
    (hw : Corner.Walls (e.board I.board) j y)
    (shape : ∀ U, Successful M U final → Corner.Shape j y (pair (I:=e.reorientInstance I) (orientLabels e U) i k))
    (hstart : j+1<(e.cells (M.source i)).1.val ∨ y+1<(e.cells (M.source k)).2.val)
    (hfinish : j+1<(e.cells (M.target i)).1.val ∨ y+1<(e.cells (M.target k)).2.val) :
    j+1<(e.cells (S.position i)).1.val ∨ y+1<(e.cells (S.position k)).2.val := by
  have step U V (hu : Successful M U final) (hv : Successful M V final) (hs : LabelledState.Step I.board U V) :
      Corner.GeometricStep (e.board I.board) j y (pair (I:=e.reorientInstance I) (orientLabels e U) i k)
        (pair (I:=e.reorientInstance I) (orientLabels e V) i k) :=
    ⟨shape U hu,shape V hv,pair_tracked (I:=e.reorientInstance I) (orient_step e hs) i k⟩
  have hb:=map_successful (fun U=>pair (I:=e.reorientInstance I) (orientLabels e U) i k)
    h.before .refl h.after h.solved step
  have ha:=map_successful (fun U=>pair (I:=e.reorientInstance I) (orientLabels e U) i k)
    h.after h.before .refl h.solved step
  have hf : Corner.Good j y (pair (I:=e.reorientInstance I) (orientLabels e final) i k) := by
    change j+1<(e.cells (final.position i)).1.val ∨ y+1<(e.cells (final.position k)).2.val
    rw [h.target ho cert]
    exact hfinish
  exact Corner.good_on_successful_path (initial:=pair (I:=e.reorientInstance I) (orientLabels e M.initialLabelled) i k)
    hw hstart hf hb ha

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph

open Relay Wires.Soundness Wires.Polyline

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {A : AxisTracks I}
    (g : GateGlyph M A true)

private theorem track_literal (s : Signals) :
    axisName true (position true s 0)=.horizontal 90 ∧
    axisName true (position true s 8)=.vertical 39 ∧
    axisName true (position true s 37)=.horizontal 29 ∧
    axisName true (position true s 36)=.vertical 39 := by
  have check : ∀a b c : Bool,
    axisName true (position true ⟨a,b,c⟩ 0)=.horizontal 90 ∧
    axisName true (position true ⟨a,b,c⟩ 8)=.vertical 39 ∧
    axisName true (position true ⟨a,b,c⟩ 37)=.horizontal 29 ∧
    axisName true (position true ⟨a,b,c⟩ 36)=.vertical 39 := by decide +kernel
  exact check s.left s.upper s.right

private theorem lower_normal (s : Signals) :
    ((position true s 0).1.val=41 ∧ (position true s 8).2.val+1=90) ∨
    ((position true s 0).1.val=40 ∧ (position true s 8).2.val+2=90) := by
  have check : ∀a b c : Bool,
    ((position true ⟨a,b,c⟩ 0).1.val=41 ∧ (position true ⟨a,b,c⟩ 8).2.val+1=90) ∨
    ((position true ⟨a,b,c⟩ 0).1.val=40 ∧ (position true ⟨a,b,c⟩ 8).2.val+2=90) := by decide +kernel
  exact check s.left s.upper s.right

private theorem upper_normal (s : Signals) :
    ((position true s 37).1.val+2=39 ∧ (position true s 36).2.val=30) ∨
    ((position true s 37).1.val+1=39 ∧ (position true s 36).2.val=31) := by
  have check : ∀a b c : Bool,
    ((position true ⟨a,b,c⟩ 37).1.val+2=39 ∧ (position true ⟨a,b,c⟩ 36).2.val=30) ∨
    ((position true ⟨a,b,c⟩ 37).1.val+1=39 ∧ (position true ⟨a,b,c⟩ 36).2.val=31) := by decide +kernel
  exact check s.left s.upper s.right

private theorem lower_walls : Corner.Walls ((GridIsometry.reflectY I.width I.height).board I.board)
    (g.dx+39) (I.height-(g.dy+91)) := by
  have hn := (GridIsometry.reflectY I.width I.height).mem_walls I.board
    ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,91)) |>.mpr
    ((g.walls _).mpr (by decide +kernel))
  have hw := (GridIsometry.reflectY I.width I.height).mem_walls I.board
    ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (38,90)) |>.mpr
    ((g.walls _).mpr (by decide +kernel))
  constructor
  · intro p hx hy
    have he : p=(GridIsometry.reflectY I.width I.height).cells
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,91)) := by
      apply Prod.ext <;> apply Fin.ext
      · exact hx
      · change p.2.val=I.height-(g.dy+91+1)
        have hh:=g.fit_y
        omega
    exact he ▸ hn
  · intro p hx hy
    have he : p=(GridIsometry.reflectY I.width I.height).cells
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (38,90)) := by
      apply Prod.ext <;> apply Fin.ext
      · change p.1.val=g.dx+38
        omega
      · exact hy
    exact he ▸ hw

private theorem upper_walls : Corner.Walls ((GridIsometry.reflectX I.width I.height).board I.board)
    (I.width-(g.dx+40)) (g.dy+29) := by
  have hn := (GridIsometry.reflectX I.width I.height).mem_walls I.board
    ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,28)) |>.mpr
    ((g.walls _).mpr (by decide +kernel))
  have hw := (GridIsometry.reflectX I.width I.height).mem_walls I.board
    ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (40,29)) |>.mpr
    ((g.walls _).mpr (by decide +kernel))
  constructor
  · intro p hx hy
    have he : p=(GridIsometry.reflectX I.width I.height).cells
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,28)) := by
      apply Prod.ext <;> apply Fin.ext
      · change p.1.val=I.width-(g.dx+39+1)
        omega
      · change p.2.val=g.dy+28
        omega
    exact he ▸ hn
  · intro p hx hy
    have he : p=(GridIsometry.reflectX I.width I.height).cells
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (40,29)) := by
      apply Prod.ext <;> apply Fin.ext
      · change p.1.val=I.width-(g.dx+40+1)
        have hh:=g.fit_x
        omega
      · exact hy
    exact he ▸ hw

/-- The protected lower fanout corner transmits inward A motion into its actual upward rail. -/
theorem lower_turn {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I) (ho : M.Ordered) :
    (S.position (g.labels 0)).1.val≤g.dx+40 → (S.position (g.labels 8)).2.val+2≤g.dy+90 := by
  let e:=GridIsometry.reflectY I.width I.height
  have hH : A.name (M.source (g.labels 0))=.horizontal (g.dy+90) := by
    rw [g.tracks,(track_literal g.initialSignals).1]
    rfl
  have hV : A.name (M.source (g.labels 8))=.vertical (g.dx+39) := by
    rw [g.tracks,(track_literal g.initialSignals).2.1]
    rfl
  have shape U (hu : Successful M U final) : Corner.Shape (g.dx+39) (I.height-(g.dy+91))
      (pair (I:=e.reorientInstance I) (orientLabels e U) (g.labels 0) (g.labels 8)) := by
    have hrow:=hu.line A true _ _ hH
    have hcol:=hu.line A false _ _ hV
    have hbefore:=above_immobile hu A true (g.dy+90) (g.labels 0) hH
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,90)) rfl (g.immobile_corner false)
    have hafter:=below_immobile hu A false (g.dx+39) (g.labels 8) hV
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,90)) rfl (g.immobile_corner false)
    have hs0 : g.dx+39<coord true (M.source (g.labels 0)) := by
      rw [g.source_coord]
      change g.dx+39<g.dx+(position true g.initialSignals 0).1.val
      rcases lower_normal g.initialSignals with hh|hh <;> omega
    have hs8 : coord false (M.source (g.labels 8))<g.dy+90 := by
      rw [g.source_coord]
      change g.dy+(position true g.initialSignals 8).2.val<g.dy+90
      rcases lower_normal g.initialSignals with hh|hh <;> omega
    have hb:=hbefore hs0
    have ha:=hafter hs8
    refine ⟨(orientLabels e U).position_mem _,(orientLabels e U).position_mem _,?_,hb,hcol,?_⟩
    · change I.height-((U.position (g.labels 0)).2.val+1)=I.height-(g.dy+91)
      change (U.position (g.labels 0)).2.val=g.dy+90 at hrow
      omega
    · change I.height-(g.dy+91)<I.height-((U.position (g.labels 8)).2.val+1)
      change (U.position (g.labels 8)).2.val<g.dy+90 at ha
      have hh:=g.fit_y
      omega
  have normal (s : Signals) : g.dx+39+1<
      (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (position true s 0))).1.val ∨
      I.height-(g.dy+91)+1<
      (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (position true s 8))).2.val := by
    change g.dx+39+1<g.dx+(position true s 0).1.val ∨
      I.height-(g.dy+91)+1<I.height-(g.dy+(position true s 8).2.val+1)
    have hh:=g.fit_y
    rcases lower_normal s with hn|hn <;> omega
  have hn0:=normal g.initialSignals
  have hn1:=normal g.targetSignals
  rw [←g.sources,←g.sources] at hn0
  rw [←g.targets,←g.targets] at hn1
  have hg:=oriented_corner_good h cert ho e _ _ (g.labels 0) (g.labels 8) g.lower_walls shape hn0 hn1
  change g.dx+39+1<(S.position (g.labels 0)).1.val ∨
    I.height-(g.dy+91)+1<I.height-((S.position (g.labels 8)).2.val+1) at hg
  have hh:=g.fit_y
  omega

/-- The protected upper fanout corner transmits the real upward rail into the westward rail. -/
theorem upper_turn {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I) (ho : M.Ordered) :
    (S.position (g.labels 36)).2.val≤g.dy+30 → (S.position (g.labels 37)).1.val+2≤g.dx+39 := by
  let e:=GridIsometry.reflectX I.width I.height
  have hH : A.name (M.source (g.labels 37))=.horizontal (g.dy+29) := by
    rw [g.tracks,(track_literal g.initialSignals).2.2.1]
    rfl
  have hV : A.name (M.source (g.labels 36))=.vertical (g.dx+39) := by
    rw [g.tracks,(track_literal g.initialSignals).2.2.2]
    rfl
  have shape U (hu : Successful M U final) : Corner.Shape (I.width-(g.dx+40)) (g.dy+29)
      (pair (I:=e.reorientInstance I) (orientLabels e U) (g.labels 37) (g.labels 36)) := by
    have hrow:=hu.line A true _ _ hH
    have hcol:=hu.line A false _ _ hV
    have hbefore:=below_immobile hu A true (g.dy+29) (g.labels 37) hH
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,29)) rfl (g.immobile_corner true)
    have hafter:=above_immobile hu A false (g.dx+39) (g.labels 36) hV
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,29)) rfl (g.immobile_corner true)
    have hs37 : coord true (M.source (g.labels 37))<g.dx+39 := by
      rw [g.source_coord]
      change g.dx+(position true g.initialSignals 37).1.val<g.dx+39
      rcases upper_normal g.initialSignals with hh|hh <;> omega
    have hs36 : g.dy+29<coord false (M.source (g.labels 36)) := by
      rw [g.source_coord]
      change g.dy+29<g.dy+(position true g.initialSignals 36).2.val
      rcases upper_normal g.initialSignals with hh|hh <;> omega
    have hb:=hbefore hs37
    have ha:=hafter hs36
    refine ⟨(orientLabels e U).position_mem _,(orientLabels e U).position_mem _,hrow,?_,?_,ha⟩
    · change I.width-(g.dx+40)<I.width-((U.position (g.labels 37)).1.val+1)
      change (U.position (g.labels 37)).1.val<g.dx+39 at hb
      have hh:=g.fit_x
      omega
    · change I.width-((U.position (g.labels 36)).1.val+1)=I.width-(g.dx+40)
      change (U.position (g.labels 36)).1.val=g.dx+39 at hcol
      omega
  have normal (s : Signals) : I.width-(g.dx+40)+1<
      (e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (position true s 37))).1.val ∨
      g.dy+29+1<(e.cells ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (position true s 36))).2.val := by
    change I.width-(g.dx+40)+1<I.width-(g.dx+(position true s 37).1.val+1) ∨
      g.dy+29+1<g.dy+(position true s 36).2.val
    have hh:=g.fit_x
    rcases upper_normal s with hn|hn <;> omega
  have hn0:=normal g.initialSignals
  have hn1:=normal g.targetSignals
  rw [←g.sources,←g.sources] at hn0
  rw [←g.targets,←g.targets] at hn1
  have hg:=oriented_corner_good h cert ho e _ _ (g.labels 37) (g.labels 36) g.upper_walls shape hn0 hn1
  change I.width-(g.dx+40)+1<I.width-((S.position (g.labels 37)).1.val+1) ∨
    g.dy+29+1<(S.position (g.labels 36)).2.val at hg
  have hh:=g.fit_x
  omega

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph
