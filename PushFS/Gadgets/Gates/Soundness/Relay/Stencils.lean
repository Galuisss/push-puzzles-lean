/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.Flip

/-! Literal protected strip walls, all physical flip identities and their two canonical normal positions. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


open Wires.Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem hStrip (kind : Bool) (x y : ℕ) (hx : x<81) (hy0 : 0<y) (hy1 : y+1<107)
    (hn : wallTest kind (⟨x,hx⟩,⟨y-1,by omega⟩)=true)
    (hs : wallTest kind (⟨x,hx⟩,⟨y+1,hy1⟩)=true) : AxisStripWalls (board kind ∅) true x x y := by
  refine ⟨?_,?_⟩
  · intro p hpy hlo hhi
    have he : p=(⟨x,hx⟩,⟨y+1,hy1⟩) := Prod.ext (Fin.ext (by change p.1.val=x; omega)) (Fin.ext hpy)
    exact (wallTest_correct kind ∅ p).mp (he ▸ hs)
  · intro p hpy hlo hhi
    have he : p=(⟨x,hx⟩,⟨y-1,by omega⟩) := Prod.ext (Fin.ext (by change p.1.val=x; omega)) (Fin.ext (by change p.2.val=y-1; omega))
    exact (wallTest_correct kind ∅ p).mp (he ▸ hn)

private theorem vStrip (kind : Bool) (y x : ℕ) (hy : y<107) (hx0 : 0<x) (hx1 : x+1<81)
    (hl : wallTest kind (⟨x-1,by omega⟩,⟨y,hy⟩)=true)
    (hr : wallTest kind (⟨x+1,hx1⟩,⟨y,hy⟩)=true) : AxisStripWalls (board kind ∅) false y y x := by
  refine ⟨?_,?_⟩
  · intro p hpx hlo hhi
    obtain ⟨q,rfl⟩:=(GridIsometry.transpose 81 107).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    have he : q=(⟨x+1,hx1⟩,⟨y,hy⟩) := by
      apply Prod.ext <;> apply Fin.ext
      · exact hpx
      · change q.2.val=y
        change y≤q.2.val at hlo
        change q.2.val≤y at hhi
        omega
    exact (wallTest_correct kind ∅ q).mp (he ▸ hr)
  · intro p hpx hlo hhi
    obtain ⟨q,rfl⟩:=(GridIsometry.transpose 81 107).cells.surjective p
    apply (GridIsometry.mem_walls _ _ _).mpr
    have he : q=(⟨x-1,by omega⟩,⟨y,hy⟩) := by
      apply Prod.ext <;> apply Fin.ext
      · change q.1.val=x-1
        change q.1.val+1=x at hpx
        omega
      · change q.2.val=y
        change y≤q.2.val at hlo
        change q.2.val≤y at hhi
        omega
    exact (wallTest_correct kind ∅ q).mp (he ▸ hl)

/-- Complete true finite flip data, with no dynamic intermediate-shape premise. -/
structure FlipSpec (kind : Bool) where
  axis : Bool
  base : ℕ
  line : ℕ
  labels : Fin 3→Label kind

namespace FlipSpec

def Checked {kind : Bool} (f : FlipSpec kind) : Prop :=
  (∀ s : Signals, FlipNormal f.axis f.base (fun i=>position kind s (f.labels i))) ∧
  (∀ (s : Signals) (i : Fin 3), axisName kind (position kind s (f.labels i))=lineTag f.axis f.line) ∧
  (∀ d : ℕ, d=0 ∨ d=3 → AxisStripWalls (board kind ∅) f.axis (f.base+d) (f.base+d) f.line) ∧
  f.base+3<(if f.axis then 81 else 107) ∧ 0<f.line ∧ f.line+1<(if f.axis then 107 else 81)

end FlipSpec

def westSpec (kind : Bool) : FlipSpec kind := ⟨true,westX kind,westY kind,westFlip kind⟩
def eastSpec (kind : Bool) : FlipSpec kind := ⟨true,eastX kind,90,eastFlip kind⟩
def upperSpec (kind : Bool) : FlipSpec kind := ⟨false,16,junction kind,upperFlip kind⟩
def fanoutSpec : FlipSpec true := ⟨false,66,39,![19,18,17]⟩

theorem west_checked (kind : Bool) : (westSpec kind).Checked := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro s
    have check : ∀ (k a b c : Bool), FlipNormal true (westX k) (fun i=>position k ⟨a,b,c⟩ (westFlip k i)) := by decide +kernel
    exact check kind s.left s.upper s.right
  · intro s i
    have check : ∀ (k a b c : Bool) (i : Fin 3), axisName k (position k ⟨a,b,c⟩ (westFlip k i))=lineTag true (westY k) := by decide +kernel
    exact check kind s.left s.upper s.right i
  · intro d hd
    refine hStrip kind _ _ ?_ ?_ ?_ ?_ ?_
    all_goals cases kind <;> rcases hd with rfl|rfl <;> decide +kernel
  all_goals cases kind <;> decide

theorem east_checked (kind : Bool) : (eastSpec kind).Checked := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro s
    have check : ∀ (k a b c : Bool), FlipNormal true (eastX k) (fun i=>position k ⟨a,b,c⟩ (eastFlip k i)) := by decide +kernel
    exact check kind s.left s.upper s.right
  · intro s i
    have check : ∀ (k a b c : Bool) (i : Fin 3), axisName k (position k ⟨a,b,c⟩ (eastFlip k i))=lineTag true 90 := by decide +kernel
    exact check kind s.left s.upper s.right i
  · intro d hd
    refine hStrip kind _ _ ?_ ?_ ?_ ?_ ?_
    all_goals cases kind <;> rcases hd with rfl|rfl <;> decide +kernel
  all_goals cases kind <;> decide

theorem upper_checked (kind : Bool) : (upperSpec kind).Checked := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro s
    have check : ∀ (k a b c : Bool), FlipNormal false 16 (fun i=>position k ⟨a,b,c⟩ (upperFlip k i)) := by decide +kernel
    exact check kind s.left s.upper s.right
  · intro s i
    have check : ∀ (k a b c : Bool) (i : Fin 3), axisName k (position k ⟨a,b,c⟩ (upperFlip k i))=lineTag false (junction k) := by decide +kernel
    exact check kind s.left s.upper s.right i
  · intro d hd
    refine vStrip kind _ _ ?_ ?_ ?_ ?_ ?_
    all_goals cases kind <;> rcases hd with rfl|rfl <;> decide +kernel
  all_goals cases kind <;> decide

theorem fanout_checked : fanoutSpec.Checked := by
  refine ⟨?_,?_,?_,by decide,by decide,by decide⟩
  · intro s
    have check : ∀ (a b c : Bool), FlipNormal false 66 (fun i=>position true ⟨a,b,c⟩ (![19,18,17] i)) := by decide +kernel
    exact check s.left s.upper s.right
  · intro s i
    have check : ∀ (a b c : Bool) (i : Fin 3), axisName true (position true ⟨a,b,c⟩ (![19,18,17] i))=lineTag false 39 := by decide +kernel
    exact check s.left s.upper s.right i
  · intro d hd
    refine vStrip true _ _ ?_ ?_ ?_ ?_ ?_
    all_goals rcases hd with rfl|rfl <;> decide +kernel

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph

open Relay Wires.Soundness

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {A : AxisTracks I} {kind : Bool}
    (g : GateGlyph M A kind)

/-- Transposition commutes with the actual translated wall table. -/
private theorem transpose_walls : (GridEmbedding.translate g.dy g.dx g.fit_y g.fit_x).WallsAgree
    ((GridIsometry.transpose 81 107).board (board kind ∅))
    ((GridIsometry.transpose I.width I.height).board I.board) := by
  intro p
  obtain ⟨q,rfl⟩:=(GridIsometry.transpose 81 107).cells.surjective p
  have he : (GridIsometry.transpose I.width I.height).cells
      ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells q)=
      (GridEmbedding.translate g.dy g.dx g.fit_y g.fit_x).cells ((GridIsometry.transpose 81 107).cells q) := rfl
  rw [←he,GridIsometry.mem_walls,GridIsometry.mem_walls]
  exact g.walls q

/-- Either literal strip orientation transports from its two actual local protecting walls. -/
private theorem axisStrip_translate (axis : Bool) (lo hi line : ℕ) (hw : AxisStripWalls
    (board kind ∅) axis lo hi line)
    (hhi : hi<(if axis then 81 else 107)) (hline0 : 0<line) (hline1 : line+1<(if axis then 107 else 81)) :
    AxisStripWalls I.board axis (g.offset axis+lo) (g.offset axis+hi) (g.offset (!axis)+line) := by
  cases axis
  · exact hw.translate hhi hline0 hline1 g.dy g.dx g.fit_y g.fit_x g.transpose_walls
  · exact hw.translate hhi hline0 hline1 g.dx g.dy g.fit_x g.fit_y g.walls

/-- Every checked internal flip derives a true signal on every actual successful global physical path. -/
theorem checked_flip_signal {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I) (ho : M.Ordered) (f : FlipSpec kind) (hf : f.Checked) :
    g.offset f.axis+f.base≤coord f.axis (S.position (g.labels (f.labels 0)))+1 →
      g.offset f.axis+f.base+5≤coord f.axis (S.position (g.labels (f.labels 2))) := by
  apply g.flip_signal h cert ho f.axis f.base f.line f.labels (hf.2.1 g.initialSignals)
    (hf.1 g.initialSignals) (hf.1 g.targetSignals)
  · simpa only [Nat.add_zero] using g.axisStrip_translate f.axis (f.base+0) (f.base+0) f.line
      (hf.2.2.1 0 (Or.inl rfl)) (by have hh:=hf.2.2.2.1; omega) hf.2.2.2.2.1 hf.2.2.2.2.2
  · simpa only [Nat.add_assoc] using g.axisStrip_translate f.axis (f.base+3) (f.base+3) f.line
      (hf.2.2.1 3 (Or.inr rfl)) hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph
