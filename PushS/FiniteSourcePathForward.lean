/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathWave

/-! Complete actual path propagation by the strict line and four-box turn macros. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height inventory Line.width Line.height LineSite.atoms

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

namespace PathSite

variable (s : PathSite w hw v P) (G : P.Geometry w)

/-- The actual real player dock of each emitted instruction. -/
def eventDock : PathEvent P → Cell (width w v) (height w v)
  | .line i => (s.line i).actualEmbedding.cells (Line.outerHub w (s.line i).atoms)
  | .turn i hi => (s.turn G i hi).actualEmbedding.cells (FiniteTools.turnDock w)

/-- Each real instruction uses its literal narrow action footprint and exact remaining global stock. -/
def EventFrame (E : s.Endpoints) (B : Board (width w v) (height w v))
    (phase : Fin (codes w v).length → Bool) : PathEvent P → Prop
  | .line i => FiniteWireFrame.Frame
      (Line.Action.active w (s.line i).atoms (s.line i).code.above (s.line i).code.last)
      (s.line i).actualEmbedding B
      (PrimitiveProfile.outside w hw v phase (Finset.univ.map (s.selection G E i).labels))
  | .turn i hi => FiniteWireFrame.Frame (FiniteTools.turnActive w) (s.turn G i hi).actualEmbedding B
      (PrimitiveProfile.outside w hw v phase (Finset.univ.map (TurnStep.mk s G i hi).labels))

/-- The actual external interfaces stay prepared while this path's interior propagates. -/
structure BoundaryReady (E : s.Endpoints) (base : Fin (codes w v).length → Bool) : Prop where
  first_external : ∀ a : PathEvent P,a.owner s ≠ E.first.1
  final_external : ∀ h (a : PathEvent P),a.owner s ≠ (E.final h).1
  first_low : base E.first.1 = P.initial
  final_high : ∀ h,base (E.final h).1 = !P.initial

/-- One physical event advances the explicit whole-board propagation wave. -/
private theorem event_run (ha : (inventory w hw v).Admissible) (E : s.Endpoints)
    (base : Fin (codes w v).length → Bool) (hbase : ∀ a : PathEvent P,base (a.owner s) = false)
    (R : s.BoundaryReady E base) (hb : P.target = !P.initial)
    (B : Board (width w v) (height w v)) (cut : ℕ) (hcut : cut < waveLength (P := P))
    (a : PathEvent P) (haRank : a.rank = waveRank (P := P) cut)
    (F : s.EventFrame G E B (s.wave base cut) a) :
    Reachable B (some 1)
      (PrimitiveProfile.state w hw v (s.wave base cut) (s.eventDock G a))
      (PrimitiveProfile.state w hw v (s.wave base (cut+1)) (s.eventDock G a)) := by
  rw [s.wave_step G base hbase cut hcut a haRank]
  have H := s.wave_frontier G base hbase cut hcut a haRank
  cases a with
  | line i =>
    apply (s.selection G E i).run (s.line i) ha (s.wave base cut)
      (s.line_ready G ha E _ i H (by
        rw [s.wave_outside base cut _ R.first_external]
        exact R.first_low) (by
        intro h
        rw [s.wave_outside base cut _ (R.final_external h)]
        exact R.final_high h)) (by
          rw [s.line_target,s.line_initial]
          exact hb) B F
  | turn i hi =>
    exact (TurnStep.mk s G i hi).run (s.wave base cut) (s.turn_ready G _ i hi H) hb B F

/-- Explicit same-stock walks connect the global anchor and each real instruction dock. -/
structure WaveAccess (base : Fin (codes w v).length → Bool)
    (B : Board (width w v) (height w v)) (anchor : Cell (width w v) (height w v)) : Prop where
  enter : ∀ cut,cut < waveLength (P := P) → ∀ a : PathEvent P,a.rank = waveRank (P := P) cut →
    Reachable B (some 1) (PrimitiveProfile.state w hw v (s.wave base cut) anchor)
      (PrimitiveProfile.state w hw v (s.wave base cut) (s.eventDock G a))
  leave : ∀ cut,cut < waveLength (P := P) → ∀ a : PathEvent P,a.rank = waveRank (P := P) cut →
    Reachable B (some 1) (PrimitiveProfile.state w hw v (s.wave base (cut+1)) (s.eventDock G a))
      (PrimitiveProfile.state w hw v (s.wave base (cut+1)) anchor)

/-- Replay every real line and turn, with all shared identities and the full actual global stock retained. -/
theorem path_forward (ha : (inventory w hw v).Admissible) (E : s.Endpoints)
    (base : Fin (codes w v).length → Bool) (hbase : ∀ a : PathEvent P,base (a.owner s) = false)
    (R : s.BoundaryReady E base) (hb : P.target = !P.initial)
    (B : Board (width w v) (height w v)) (anchor : Cell (width w v) (height w v))
    (F : ∀ cut,cut < waveLength (P := P) → ∀ a : PathEvent P,a.rank = waveRank (P := P) cut →
      s.EventFrame G E B (s.wave base cut) a)
    (W : s.WaveAccess G base B anchor) :
    Reachable B (some 1) (PrimitiveProfile.state w hw v base anchor)
      (PrimitiveProfile.state w hw v (s.wave base (waveLength (P := P))) anchor) := by
  have hr : ∀ n,n ≤ waveLength (P := P) → Reachable B (some 1)
      (PrimitiveProfile.state w hw v base anchor) (PrimitiveProfile.state w hw v (s.wave base n) anchor) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [s.wave_zero]
    | succ n ih =>
      intro hn
      have hlt : n < waveLength (P := P) := by omega
      have hi := ih (by omega)
      by_cases he : ∃ a : PathEvent P,a.rank = waveRank (P := P) n
      · obtain ⟨a,haRank⟩ := he
        exact hi.trans ((W.enter n hlt a haRank).trans
          ((s.event_run G ha E base hbase R hb B n hlt a haRank (F n hlt a haRank)).trans
            (W.leave n hlt a haRank)))
      · rw [s.wave_skip G base hbase n hlt he]
        exact hi
  exact hr _ le_rfl

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
