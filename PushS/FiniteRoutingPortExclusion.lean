/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingRelay

/-! Opposite high slots of one real physical box cannot both be reached. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS

private theorem opposite_portHigh {W H : ℕ} (d : Direction) (low high actual : Cell W H)
    (h : Adjacent d low high) : ¬(PortHigh d high actual ∧ PortHigh d.opposite low actual) := by
  cases d <;> simp only [PortHigh,Outward,coordinates,Direction.opposite,Adjacent,Fin.ext_iff] at h ⊢ <;> omega

namespace PhysicalPort

/-- Three literal data fields determine a placed physical readout port. -/
theorem ext_coordinates {I : PushFS.Instance} {L : Type}
    (p q : PhysicalPort (I := I) (GlobalLabel := L))
    (hl : p.label = q.label) (hs : coordinates p.slot = coordinates q.slot)
    (hd : p.direction = q.direction) : p = q := by
  have he := (Fin.val_injective.prodMap Fin.val_injective) hs
  cases p
  cases q
  cases hl
  cases he
  cases hd
  rfl

theorem exclusive_of_opposite {I : PushFS.Instance} {L : Type} [Fintype L]
    (p q : PhysicalPort (I := I) (GlobalLabel := L)) (S : LabelledState L I.width I.height)
    (hl : p.label = q.label) (hd : q.direction = p.direction.opposite)
    (hs : Adjacent p.direction q.slot p.slot) : ¬(p.High S ∧ q.High S) := by
  change ¬(PortHigh p.direction p.slot (S.position p.label) ∧ PortHigh q.direction q.slot (S.position q.label))
  rw [←hl,hd]
  exact opposite_portHigh p.direction q.slot p.slot (S.position p.label) hs

end PhysicalPort
end PushPuzzle.PushS.FiniteRouting
