/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingReadoutSlots

/-! Complete physical line selectors from the actual owned stock and its neighboring endpoint owners. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Readout

open PushFS

variable {GlobalLabel : Type}

def ownedIndex (w : ℕ) (atoms : List Atom) (last : Bool) (l : Label w atoms)
    (hfirst : l.val ≠ 0) (hlast : ¬(last = false ∧ l = cutLastLabel w atoms)) : OwnedLabel w atoms false last :=
  ⟨l, Or.inr (by omega), by
    cases last
    · apply Or.inr
      have hl := l.isLt
      have hlen := Terminal.length_eq w atoms
      have hv := Terminal.last_val w atoms
      have hne : l.val ≠ (cutLastLabel w atoms).val := fun hh => hlast ⟨rfl, Fin.ext hh⟩
      omega
    · exact Or.inl rfl⟩

/-- The emitted line owns its interiors; both shared endpoints select their real neighboring owners. -/
def completeLabels (w : ℕ) (atoms : List Atom) (last : Bool)
    (first : GlobalLabel) (final : last = false → GlobalLabel)
    (owned : OwnedLabel w atoms false last → GlobalLabel) (l : Label w atoms) : GlobalLabel :=
  if hfirst : l.val = 0 then first
  else if hlast : last = false ∧ l = cutLastLabel w atoms then final hlast.1
  else owned (ownedIndex w atoms last l hfirst hlast)

/-- A source or target slot equation for every real owner yields the entire completed physical slot map. -/
theorem completeLabels_slots (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last q : Bool)
    (first : GlobalLabel) (final : last = false → GlobalLabel)
    (owned : OwnedLabel w atoms false last → GlobalLabel)
    {W H : ℕ} (e : GridEmbedding (width w atoms) (height w) W H) (F : GlobalLabel → Cell W H)
    (hfirst : F first = e.cells (cell w hw atoms q (cutFirstLabel w atoms)))
    (hfinal : ∀ hl, F (final hl) = e.cells (cell w hw atoms q (cutLastLabel w atoms)))
    (howned : ∀ l, F (owned l) = e.cells (ownedCell w hw atoms false last q l)) :
    ∀ l, F (completeLabels w atoms last first final owned l) = e.cells (cell w hw atoms q l) := by
  intro l
  unfold completeLabels
  split_ifs with hf hl
  · have he : l = cutFirstLabel w atoms := Fin.ext hf
    exact hfirst.trans (congrArg (fun l => e.cells (cell w hw atoms q l)) he.symm)
  · exact (hfinal hl.1).trans (congrArg (fun l => e.cells (cell w hw atoms q l)) hl.2.symm)
  · exact howned _

variable {I : PushFS.Instance} [Fintype GlobalLabel] {M : SlotMatching I GlobalLabel} {A : ComponentTracks I}

end PushPuzzle.PushS.FiniteRouting.Line.Readout
