/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.Gaps

/-! Two genuine protected strips propagate an internal three-slot flip on either axis. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


open Wires.Soundness

variable {w h : ℕ}

def AxisStripWalls (B : Board w h) (axis : Bool) (lo hi line : ℕ) : Prop :=
  if axis then StripWalls B lo hi line else StripWalls ((GridIsometry.transpose w h).board B) lo hi line

def key (axis : Bool) (p : Cell w h) : ℕ := if axis then p.1.val else p.2.val

def FlipNormal (axis : Bool) (base : ℕ) (p : Fin 3→Cell w h) : Prop :=
  (key axis (p 0)+2=base ∧ key axis (p 1)=base ∧ key axis (p 2)=base+4) ∨
  (key axis (p 0)+1=base ∧ key axis (p 1)=base+3 ∧ key axis (p 2)=base+5)

instance (axis : Bool) (base : ℕ) (p : Fin 3→Cell w h) : Decidable (FlipNormal axis base p) := by
  unfold FlipNormal
  infer_instance

variable {I : Instance} {L : Type} [Fintype L]

private theorem axis_strip_good {M : SlotMatching I L} {S final : LabelledState L I.width I.height}
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered) (A : AxisTracks I)
    (axis : Bool) (lo hi line : ℕ) (i j : L) (hw : AxisStripWalls I.board axis lo hi line)
    (hirow : A.name (M.source i)=lineTag axis line) (hjrow : A.name (M.source j)=lineTag axis line)
    (hij : coord axis (M.source i)<coord axis (M.source j))
    (hstart : coord axis (M.source i)+1<lo ∨ hi+1<coord axis (M.source j))
    (hfinish : coord axis (M.target i)+1<lo ∨ hi+1<coord axis (M.target j)) :
    coord axis (S.position i)+1<lo ∨ hi+1<coord axis (S.position j) := by
  cases axis
  · exact vertical_strip_good h cert ho A lo hi line i j hw hirow hjrow hij hstart hfinish
  · exact h.strip_good cert ho A lo hi line i j hw hirow hjrow hij hstart hfinish

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph

open Relay Wires.Soundness

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {A : AxisTracks I} {kind : Bool}
    (g : GateGlyph M A kind)

/-- Local rows, columns and both closed strip walls are the complete geometric premises of an internal flip. -/
theorem flip_signal {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I) (ho : M.Ordered) (axis : Bool) (base line : ℕ) (labels : Fin 3→Label kind)
    (tracks : ∀ i, axisName kind (position kind g.initialSignals (labels i))=lineTag axis line)
    (initial : Relay.FlipNormal axis base (fun i=>position kind g.initialSignals (labels i)))
    (target : Relay.FlipNormal axis base (fun i=>position kind g.targetSignals (labels i)))
    (walls0 : AxisStripWalls I.board axis (g.offset axis+base) (g.offset axis+base) (g.offset (!axis)+line))
    (walls3 : AxisStripWalls I.board axis (g.offset axis+base+3) (g.offset axis+base+3) (g.offset (!axis)+line)) :
    g.offset axis+base≤coord axis (S.position (g.labels (labels 0)))+1 →
      g.offset axis+base+5≤coord axis (S.position (g.labels (labels 2))) := by
  have ht (i : Fin 3) : A.name (M.source (g.labels (labels i)))=lineTag axis (g.offset (!axis)+line) := by
    rw [g.tracks,tracks i]
    cases axis <;> rfl
  have hi : (coord axis (M.source (g.labels (labels 0))))<(coord axis (M.source (g.labels (labels 1)))) := by
    rw [g.source_coord,g.source_coord]
    rcases initial with hh|hh <;> simp only [key] at hh <;> omega
  have hj : (coord axis (M.source (g.labels (labels 1))))<(coord axis (M.source (g.labels (labels 2)))) := by
    rw [g.source_coord,g.source_coord]
    rcases initial with hh|hh <;> simp only [key] at hh <;> omega
  have normal0 (s : Signals) (hn : Relay.FlipNormal axis base (fun i=>position kind s (labels i))) :
      g.offset axis+(key axis (position kind s (labels 0)))+1<g.offset axis+base ∨
      g.offset axis+base+1<g.offset axis+(key axis (position kind s (labels 1))) := by
    rcases hn with hh|hh <;> dsimp only at hh <;> omega
  have normal3 (s : Signals) (hn : Relay.FlipNormal axis base (fun i=>position kind s (labels i))) :
      g.offset axis+(key axis (position kind s (labels 1)))+1<g.offset axis+base+3 ∨
      g.offset axis+base+3+1<g.offset axis+(key axis (position kind s (labels 2))) := by
    rcases hn with hh|hh <;> dsimp only at hh <;> omega
  have hs0 : coord axis (M.source (g.labels (labels 0)))+1<g.offset axis+base ∨
      g.offset axis+base+1<coord axis (M.source (g.labels (labels 1))) := by
    rw [g.source_coord,g.source_coord]
    exact normal0 g.initialSignals initial
  have hf0 : coord axis (M.target (g.labels (labels 0)))+1<g.offset axis+base ∨
      g.offset axis+base+1<coord axis (M.target (g.labels (labels 1))) := by
    rw [g.target_coord,g.target_coord]
    exact normal0 g.targetSignals target
  have hs3 : coord axis (M.source (g.labels (labels 1)))+1<g.offset axis+base+3 ∨
      g.offset axis+base+3+1<coord axis (M.source (g.labels (labels 2))) := by
    rw [g.source_coord,g.source_coord]
    exact normal3 g.initialSignals initial
  have hf3 : coord axis (M.target (g.labels (labels 1)))+1<g.offset axis+base+3 ∨
      g.offset axis+base+3+1<coord axis (M.target (g.labels (labels 2))) := by
    rw [g.target_coord,g.target_coord]
    exact normal3 g.targetSignals target
  have hl:=axis_strip_good h cert ho A axis _ _ _ _ _ walls0 (ht 0) (ht 1) hi hs0 hf0
  have hr:=axis_strip_good h cert ho A axis _ _ _ _ _ walls3 (ht 1) (ht 2) hj hs3 hf3
  omega

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph
