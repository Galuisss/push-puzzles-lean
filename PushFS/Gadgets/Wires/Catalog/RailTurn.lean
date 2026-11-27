/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RailBarriers
public import PushFS.Gadgets.Wires.Soundness.Turn
public import PushFS.StaticPlacement

/-! Actual endpoint signal propagation through the full guarded turn and its traversable flip. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness

variable {I : Instance} {Label : Type} [Fintype Label]

/-- Static placement of all 29 physical identities in the exact full turn stencil. -/
structure TurnRailGlyph (M : SlotMatching I Label) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+45 ≤ I.width
  fit_y : dy+41 ≤ I.height
  initialPhase : Bool
  targetPhase : Bool
  labels : Fin 29 ↪ Label
  walls : (GridEmbedding.translate dx dy fit_x fit_y).WallsAgree (Turn.template.board ∅) I.board
  sources : ∀ i, M.source (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (Turn.template.position initialPhase i)
  targets : ∀ i, M.target (labels i) = (GridEmbedding.translate dx dy fit_x fit_y).cells
    (Turn.template.position targetPhase i)

namespace TurnRailGlyph

variable {M : SlotMatching I Label} (g : TurnRailGlyph M)
    {S final : LabelledState Label I.width I.height}

theorem component (i j : Fin 29) (harm : (i.val < 14 ∧ j.val < 14) ∨ (14 ≤ i.val ∧ 14 ≤ j.val)) :
    PushFS.component I.board (M.source (g.labels i)) = PushFS.component I.board (M.source (g.labels j)) := by
  rw [g.sources,g.sources]
  have hh := TurnGeometry.slots_component g.initialPhase i j harm
  exact component_eq_iff.mpr ⟨GridEmbedding.staticReach g.walls hh.1,GridEmbedding.staticReach g.walls hh.2⟩

private theorem endpoints : ∀phase : Bool,
    (Turn.template.position phase 13).1.val≠(Turn.template.position phase 0).1.val ∧
      (Turn.template.position phase 28).2.val≠(Turn.template.position phase 14).2.val := by decide +kernel

def horizontalRail : SourceRail M true (g.dy+9) where
  anchor:=g.labels 0
  witness:=M.source (g.labels 13)
  connected:=g.component 13 0 (Or.inl ⟨by decide,by decide⟩)
  different:=by
    rw [g.sources,g.sources]
    change g.dx+_≠g.dx+_
    have hh:=(endpoints g.initialPhase).1
    omega
  anchor_cross:=by
    rw [g.sources]
    change g.dy+(Turn.template.position g.initialPhase 0).2.val=g.dy+9
    rw [(TurnGeometry.arms g.initialPhase 0).1 (by decide) |>.1]

def verticalRail : SourceRail M false (g.dx+10) where
  anchor:=g.labels 14
  witness:=M.source (g.labels 28)
  connected:=g.component 28 14 (Or.inr ⟨by decide,by decide⟩)
  different:=by
    rw [g.sources,g.sources]
    change g.dy+_≠g.dy+_
    have hh:=(endpoints g.initialPhase).2
    omega
  anchor_cross:=by
    rw [g.sources]
    change g.dx+(Turn.template.position g.initialPhase 14).1.val=g.dx+10
    rw [(TurnGeometry.arms g.initialPhase 14).2 (by decide) |>.1]

private theorem horizontal_component (i : Fin 29) (hi : i.val<14) :
    PushFS.component I.board (M.source (g.labels i))=PushFS.component I.board (M.source g.horizontalRail.anchor) :=
  g.component i 0 (Or.inl ⟨hi,by decide⟩)
theorem vertical_component (i : Fin 29) (hi : 14≤i.val) :
    PushFS.component I.board (M.source (g.labels i))=PushFS.component I.board (M.source g.verticalRail.anchor) :=
  g.component i 14 (Or.inr ⟨hi,by decide⟩)

private theorem horizontal_gap (h : Successful M S final) (cert : Certificate I)
    (i j : Fin 29) (hij : i < j) (hj : j.val < 14) :
    (S.position (g.labels j)).1.val+2 ≤ (S.position (g.labels i)).1.val := by
  have hi : i.val < 14 := Nat.lt_trans hij hj
  have ho : (M.source (g.labels j)).1.val < (M.source (g.labels i)).1.val := by
    rw [g.sources,g.sources]
    exact Nat.add_lt_add_left (TurnGeometry.horizontal_order g.initialPhase i j hij hj) _
  exact g.horizontalRail.gap h cert (g.labels j) (g.labels i)
    (g.horizontal_component j hj) (g.horizontal_component i hi) ho

private theorem vertical_gap (h : Successful M S final) (cert : Certificate I)
    (i j : Fin 29) (hi : 14 ≤ i.val) (hij : i < j) :
    (S.position (g.labels i)).2.val+2 ≤ (S.position (g.labels j)).2.val := by
  have hj : 14 ≤ j.val := le_trans hi (le_of_lt hij)
  have ho : (M.source (g.labels i)).2.val < (M.source (g.labels j)).2.val := by
    rw [g.sources,g.sources]
    exact Nat.add_lt_add_left (TurnGeometry.vertical_order g.initialPhase i j hi hij) _
  exact g.verticalRail.gap h cert (g.labels i) (g.labels j)
    (g.vertical_component i hi) (g.vertical_component j hj) ho

private theorem immobile_corner (q : PushFS.Cell I.width I.height) :
    ¬Displacement I.board ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (10,9)) q := by
  intro hd
  obtain ⟨q',_,hd'⟩:=GridEmbedding.displacement_preimage g.dx g.dy g.fit_x g.fit_y g.walls
    (p:=(10,9)) (by decide) hd
  have check : ∀d : Direction, Gates.staticStep Turn.template.wall d (10,9)=none := by decide +kernel
  obtain ⟨d,hd'⟩:=(displacement_iff_staticStep (Turn.template.wall_correct ∅) _ _).mp hd'
  rw [check] at hd'
  contradiction

/-- Actual C2 and the literal immobile corner keep both identities on the open arms. -/
private theorem corner_shape (h : Successful M S final) (cert : Certificate I) :
    Corner.Shape (g.dx+10) (g.dy+9) (pair S (g.labels 13) (g.labels 14)) := by
  refine ⟨S.position_mem _,S.position_mem _,
    g.horizontalRail.current_line h cert _ (g.horizontal_component 13 (by decide)),?_,
    g.verticalRail.current_line h cert _ (g.vertical_component 14 (by decide)),?_⟩
  · apply g.horizontalRail.above_immobile h cert _ (g.horizontal_component 13 (by decide))
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (10,9)) rfl g.immobile_corner
    rw [g.sources]
    have hh:=(TurnGeometry.arms g.initialPhase 13).1 (by decide)
    change g.dx+10<g.dx+_
    omega
  · apply g.verticalRail.above_immobile h cert _ (g.vertical_component 14 (by decide))
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (10,9)) rfl g.immobile_corner
    rw [g.sources]
    have hh:=(TurnGeometry.arms g.initialPhase 14).2 (by decide)
    change g.dy+9<g.dy+_
    omega

private theorem corner_walls : Corner.Walls I.board (g.dx+10) (g.dy+9) := by
  have north : ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (10,8)) ∈ I.board.walls :=
    (g.walls _).mpr (by decide +kernel)
  have west : ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (9,9)) ∈ I.board.walls :=
    (g.walls _).mpr (by decide +kernel)
  refine ⟨?_,?_⟩
  · intro p hx hy
    have he : p = (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (10,8) := by
      apply Prod.ext <;> apply Fin.ext
      · exact hx
      · change p.2.val = g.dy+8
        omega
    exact he ▸ north
  · intro p hx hy
    have he : p = (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (9,9) := by
      apply Prod.ext <;> apply Fin.ext
      · change p.1.val = g.dx+9
        omega
      · exact hy
    exact he ▸ west

/-- The protected corner remains logically open throughout arbitrary successful motion. -/
private theorem corner_good (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) :
    g.dx+11 < (S.position (g.labels 13)).1.val ∨ g.dy+10 < (S.position (g.labels 14)).2.val := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) :
      Corner.GeometricStep I.board (g.dx+10) (g.dy+9) (pair U (g.labels 13) (g.labels 14))
        (pair V (g.labels 13) (g.labels 14)) := ⟨g.corner_shape hu cert,g.corner_shape hv cert,pair_tracked hs _ _⟩
  have hb := map_successful (fun U => pair U (g.labels 13) (g.labels 14)) h.before .refl h.after h.solved hstep
  have ha := map_successful (fun U => pair U (g.labels 13) (g.labels 14)) h.after h.before .refl h.solved hstep
  have hs0 : Corner.Good (g.dx+10) (g.dy+9) (pair M.initialLabelled (g.labels 13) (g.labels 14)) := by
    change g.dx+10+1 < (M.source (g.labels 13)).1.val ∨ g.dy+9+1 < (M.source (g.labels 14)).2.val
    rw [g.sources,g.sources]
    have hh := TurnGeometry.corner_normal g.initialPhase
    change g.dx+10+1 < g.dx+_ ∨ g.dy+9+1 < g.dy+_
    omega
  have hs1 : Corner.Good (g.dx+10) (g.dy+9) (pair final (g.labels 13) (g.labels 14)) := by
    have ht := h.target ho cert
    change g.dx+10+1 < (final.position (g.labels 13)).1.val ∨ g.dy+9+1 < (final.position (g.labels 14)).2.val
    rw [ht,g.targets,g.targets]
    have hh := TurnGeometry.corner_normal g.targetPhase
    change g.dx+10+1 < g.dx+_ ∨ g.dy+9+1 < g.dy+_
    omega
  exact Corner.good_on_successful_path g.corner_walls hs0 hs1 hb ha

private theorem flip_strip (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (r : Fin 2) :
    (S.position (g.labels (if r=0 then 4 else 3))).1.val+1 < g.dx+(if r=0 then 31 else 34) ∨
      g.dx+(if r=0 then 32 else 35) < (S.position (g.labels (if r=0 then 3 else 2))).1.val := by
  have hw : StripWalls (Turn.template.board ∅) (if r=0 then 31 else 34) (if r=0 then 31 else 34) 9 := by
    by_cases hr : r=0
    · simpa only [hr,ite_true] using TurnGeometry.strip31
    · simpa only [hr,ite_false] using TurnGeometry.strip34
  have hhi : (if r=0 then 31 else 34) < 45 := by split <;> decide
  have hamb := hw.translate hhi (by decide) (by decide) g.dx g.dy g.fit_x g.fit_y g.walls
  have hh := g.horizontalRail.strip_good h cert ho _ _ (g.labels (if r=0 then 4 else 3))
    (g.labels (if r=0 then 3 else 2)) hamb
    (g.horizontal_component _ (by split <;> decide)) (g.horizontal_component _ (by split <;> decide))
  have horder : (M.source (g.labels (if r=0 then 4 else 3))).1.val <
      (M.source (g.labels (if r=0 then 3 else 2))).1.val := by
    rw [g.sources,g.sources]
    exact Nat.add_lt_add_left
      (TurnGeometry.horizontal_order g.initialPhase _ _ (by split <;> decide) (by split <;> decide)) _
  have he : g.dx+(if r=0 then 31 else 34)+1 = g.dx+(if r=0 then 32 else 35) := by split <;> omega
  rw [← he]
  apply hh horder
  · rw [g.sources,g.sources]
    have hn := TurnGeometry.flip_normal g.initialPhase
    by_cases hr : r=0
    · simp only [hr,ite_true]
      change g.dx+_+1 < g.dx+31 ∨ g.dx+31+1 < g.dx+_
      omega
    · simp only [hr,ite_false]
      change g.dx+_+1 < g.dx+34 ∨ g.dx+34+1 < g.dx+_
      omega
  · rw [g.targets,g.targets]
    have hn := TurnGeometry.flip_normal g.targetPhase
    by_cases hr : r=0
    · simp only [hr,ite_true]
      change g.dx+_+1 < g.dx+31 ∨ g.dx+31+1 < g.dx+_
      omega
    · simp only [hr,ite_false]
      change g.dx+_+1 < g.dx+34 ∨ g.dx+34+1 < g.dx+_
      omega

/-- The east input threshold forces the south output threshold on the actual full turn. -/
theorem signal (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : (S.position (g.labels 0)).1.val ≤ g.dx+39) :
    g.dy+39 ≤ (S.position (g.labels 28)).2.val := by
  have hh0 := g.horizontal_gap h cert 0 1 (by decide) (by decide)
  have hh1 := g.horizontal_gap h cert 1 2 (by decide) (by decide)
  have hh2 := g.horizontal_gap h cert 2 3 (by decide) (by decide)
  have hh3 := g.horizontal_gap h cert 3 4 (by decide) (by decide)
  have hh4 := g.horizontal_gap h cert 4 5 (by decide) (by decide)
  have hh5 := g.horizontal_gap h cert 5 6 (by decide) (by decide)
  have hh6 := g.horizontal_gap h cert 6 7 (by decide) (by decide)
  have hh7 := g.horizontal_gap h cert 7 8 (by decide) (by decide)
  have hh8 := g.horizontal_gap h cert 8 9 (by decide) (by decide)
  have hh9 := g.horizontal_gap h cert 9 10 (by decide) (by decide)
  have hh10 := g.horizontal_gap h cert 10 11 (by decide) (by decide)
  have hh11 := g.horizontal_gap h cert 11 12 (by decide) (by decide)
  have hh12 := g.horizontal_gap h cert 12 13 (by decide) (by decide)
  have hv14 := g.vertical_gap h cert 14 15 (by decide) (by decide)
  have hv15 := g.vertical_gap h cert 15 16 (by decide) (by decide)
  have hv16 := g.vertical_gap h cert 16 17 (by decide) (by decide)
  have hv17 := g.vertical_gap h cert 17 18 (by decide) (by decide)
  have hv18 := g.vertical_gap h cert 18 19 (by decide) (by decide)
  have hv19 := g.vertical_gap h cert 19 20 (by decide) (by decide)
  have hv20 := g.vertical_gap h cert 20 21 (by decide) (by decide)
  have hv21 := g.vertical_gap h cert 21 22 (by decide) (by decide)
  have hv22 := g.vertical_gap h cert 22 23 (by decide) (by decide)
  have hv23 := g.vertical_gap h cert 23 24 (by decide) (by decide)
  have hv24 := g.vertical_gap h cert 24 25 (by decide) (by decide)
  have hv25 := g.vertical_gap h cert 25 26 (by decide) (by decide)
  have hv26 := g.vertical_gap h cert 26 27 (by decide) (by decide)
  have hv27 := g.vertical_gap h cert 27 28 (by decide) (by decide)
  have hs0 := g.flip_strip h cert ho 0
  have hs1 := g.flip_strip h cert ho 1
  have hc := g.corner_good h cert ho
  change (S.position (g.labels 4)).1.val+1 < g.dx+31 ∨ g.dx+32 < (S.position (g.labels 3)).1.val at hs0
  change (S.position (g.labels 3)).1.val+1 < g.dx+34 ∨ g.dx+35 < (S.position (g.labels 2)).1.val at hs1
  omega

end TurnRailGlyph
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
