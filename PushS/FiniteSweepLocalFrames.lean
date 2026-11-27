/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSquareLineFrame
public import PushS.FiniteFramePlacement

/-! The original local sweep contract supplies its exact local replay footprint. -/

public section
namespace PushPuzzle.PushS.FiniteSquareLine.Sweep

open PushFS

variable {N : ℕ}

/-- The real track and lane frame exposes exactly the local cells used by the ambient sweep macro. -/
theorem Frame.toWireFrame {S : Sweep N} {B : Board N N} {fixed : Finset (Cell N N)} (F : S.Frame B fixed) :
    FiniteWireFrame.Frame S.active (GridIsometry.refl N N).embedding B fixed := by
  apply FiniteWireFrame.Frame.of_free F.fixed_floor
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [FiniteLineMacros.Line.mem_active] at hq
  change Free B fixed (S.embedding.cells q)
  rw [embedding_apply]
  rcases hq with ⟨hy,hx⟩ | ⟨hy,hx⟩
  · have he : S.map q = S.map (q.1,S.line.row) := congrArg S.map (Prod.ext rfl hy)
    exact he.symm ▸ F.track_free q.1 hx
  · have he : S.map q = S.map (q.1,S.line.lane) := congrArg S.map (Prod.ext rfl hy)
    exact he.symm ▸ F.lane_free q.1 hx

end PushPuzzle.PushS.FiniteSquareLine.Sweep
