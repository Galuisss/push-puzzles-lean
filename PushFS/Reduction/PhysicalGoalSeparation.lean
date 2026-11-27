/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalInventory
public import PushFS.Reduction.PhysicalSlotNearby

/-! Adjacent goals of the actual whole physical board have one common macrocell owner. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction


theorem Adjacent.nearby {W H : ℕ} {d : Direction} {p q : Cell W H} (h : Adjacent d p q) :
    Nearby 1 (p.1.val,p.2.val) (q.1.val,q.2.val) := by
  cases d <;> simp only [Adjacent,Fin.ext_iff] at h <;> dsimp only [Nearby] <;> omega

namespace PhysicalInventory

end PhysicalInventory
end PushPuzzle.PushFS.Reduction
