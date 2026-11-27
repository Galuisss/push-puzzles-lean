/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateBoundarySlots

/-! The completed actual path wave is exactly the corresponding complete source-tile stock update. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

/-- Every actual primitive owner reads its source tile's current phase. -/
def tilePhases (phase : GridRouting.Point → Bool) (i : Fin (codes w v).length) : Bool :=
  phase ((codes w v).get i).1

/-- Every emitted path instruction is one of the literal line or turn events. -/
private theorem PathEvent.of_mem (c : PrimitiveCode)
    (hc : c ∈ P.codes) : ∃ a : PathEvent P,a.code = c := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · exact ⟨.line ⟨i,hi'⟩,rfl⟩
  · exact ⟨.turn ⟨i,hi'⟩ ht,rfl⟩

namespace PathSite

variable (s : PathSite w hw v P)

/-- Every real global entry at this path instruction is selected by its actual event owner. -/
theorem owner_covers (ha : (inventory w hw v).Admissible) (i : Fin (codes w v).length)
    (hloc : ((codes w v).get i).1 = s.location) (hc : ((codes w v).get i).2 ∈ P.codes) :
    ∃ a : PathEvent P,a.owner s = i := by
  obtain ⟨a,haCode⟩ := PathEvent.of_mem _ hc
  refine ⟨a,code_get_injective ha ?_⟩
  change (codes w v).get (s.index a.code a.member) = (codes w v).get i
  rw [s.get_index]
  exact Prod.ext hloc.symm haCode

/-- An untouched source tile makes every one of its actual path primitives fresh. -/
theorem path_fresh (phase : GridRouting.Point → Bool) (hp : phase s.location = false) :
    ∀ a : PathEvent P,tilePhases phase (a.owner s) = false := by
  intro a
  unfold tilePhases
  rw [a.owner_location]
  exact hp

/-- When the path is the tile's complete code list, the wave updates exactly that tile's real owners. -/
private theorem wave_complete (ha : (inventory w hw v).Admissible)
    (hc : localCodes w (CellPlan.cell (v,s.location)) = P.codes)
    (base : Fin (codes w v).length → Bool) :
    s.wave base (waveLength (P := P)) = fun i =>
      if ((codes w v).get i).1 = s.location then true else base i := by
  funext i
  rw [s.wave_final]
  congr 1
  apply propext
  constructor
  · rintro ⟨a,rfl⟩
    exact a.owner_location s
  · intro hloc
    apply s.owner_covers ha i hloc
    rw [←hc]
    have hi := code_local w v ((codes w v).get i) (List.get_mem _ _)
    rw [hloc] at hi
    exact hi

/-- A complete ordinary wire path ends at precisely the source-tile profile after its actual stock update. -/
private theorem wire_wave_state {a : PushFS.Gadgets.Wires.Catalog.Bitmap.Args}
    (t : PathSite w hw v (wireSpec w a)) (ha : (inventory w hw v).Admissible)
    (e : ℕ) (hc : CellPlan.cell (v,t.location) = some (.inr (e,a)))
    (phase : GridRouting.Point → Bool) (player : Cell (width w v) (height w v)) :
    PrimitiveProfile.state w hw v (t.wave (tilePhases phase) (waveLength (P := wireSpec w a))) player =
      PrimitiveProfile.state w hw v (tilePhases (Function.update phase t.location true)) player := by
  rw [t.wave_complete ha (by rw [hc]; rfl)]
  congr 1
  funext i
  simp only [tilePhases,Function.update_apply]

/-- Actual full-wire execution changes the whole tile profile with every global box retained. -/
theorem wire_tile_forward {a : PushFS.Gadgets.Wires.Catalog.Bitmap.Args}
    (t : PathSite w hw v (wireSpec w a)) (ha : (inventory w hw v).Admissible)
    (e : ℕ) (hc : CellPlan.cell (v,t.location) = some (.inr (e,a)))
    (phase : GridRouting.Point → Bool) (hp : phase t.location = false)
    (E : t.Endpoints) (R : t.BoundaryReady E (tilePhases phase)) (hb : a.2.2 = !a.2.1)
    (B : Board (width w v) (height w v))
    (F : ∀ cut,cut < waveLength (P := wireSpec w a) → ∀ b : PathEvent (wireSpec w a),
      b.rank = waveRank (P := wireSpec w a) cut →
      t.EventFrame (wireSpec_geometry w a) E B (t.wave (tilePhases phase) cut) b)
    (W : t.WaveAccess (wireSpec_geometry w a) (tilePhases phase) B (inventory w hw v).player) :
    Reachable B (some 1) (profileState w hw v phase)
      (profileState w hw v (Function.update phase t.location true)) := by
  have hr := t.path_forward (wireSpec_geometry w a) ha E (tilePhases phase) (t.path_fresh phase hp) R hb B
    (inventory w hw v).player F W
  rw [t.wire_wave_state ha e hc] at hr
  exact hr

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
