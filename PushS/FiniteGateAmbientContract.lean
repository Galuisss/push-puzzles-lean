/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateForwardContract
public import PushS.FiniteAtomFrames

/-! Reuse physical gate contracts under ambient placements and canonical player access. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateForwardContract

open PushFS PushFS.Gadgets

variable {w h W H : ℕ}

/-- A narrow-frame ambient run gives the corresponding macro on the complete mapped inventories. -/
def Macro.of_placed_run (e : GridEmbedding w h W H) {B : Board W H}
    (extra : Finset (Cell W H)) {initial final portals : Finset (Cell w h)}
    (entry exit : Cell w h) (hentry : entry ∈ portals) (hexit : exit ∈ portals)
    (hr : Reachable B (some 1) (e.extend extra ⟨entry, initial⟩) (e.extend extra ⟨exit, final⟩)) :
    Macro B (initial.map e.cells ∪ extra) (final.map e.cells ∪ extra) (portals.map e.cells) where
  entry := e.cells entry
  exit := e.cells exit
  entry_mem := Finset.mem_map.mpr ⟨entry, hentry, rfl⟩
  exit_mem := Finset.mem_map.mpr ⟨exit, hexit, rfl⟩
  run := hr

private theorem valid_source_of_ne {B : Board W H} {cap : Option ℕ} {s t : State W H}
    (hr : Reachable B cap s t) (hne : s ≠ t) : s.Valid B := by
  revert hne
  induction hr with
  | refl => intro hne; exact False.elim (hne rfl)
  | @tail u v hr hs ih =>
    intro _
    by_cases he : s = u
    · subst u
      exact hs.choose_spec.valid_source
    · exact ih he

/-- A nontrivial physical macro has valid, free player cells at both interfaces. -/
theorem Macro.interface_free {B : Board W H} {initial final portals : Finset (Cell W H)}
    (M : Macro B initial final portals) (hne : initial ≠ final) :
    Free B initial M.entry ∧ Free B final M.exit := by
  have hs := valid_source_of_ne M.run (fun he => hne (congrArg State.boxes he))
  have ht := M.run.valid hs
  exact ⟨⟨hs.1, hs.2.2⟩, ht.1, ht.2.2⟩

/-- Join the selected gate macro to the actual canonical player through free interface access. -/
theorem Contract.canonical_step_at {kind : Bool} {B : Board W H}
    {normal : Gates.Signals → Finset (Cell W H)} {portals : Finset (Cell W H)}
    (C : Contract kind B normal portals) (player : Gates.Signals → Cell W H)
    (access : ∀ s p, p ∈ portals → Free B (normal s) p →
      Reachable B (some 1) ⟨player s, normal s⟩ ⟨p, normal s⟩ ∧
      Reachable B (some 1) ⟨p, normal s⟩ ⟨player s, normal s⟩)
    (initial final : Gates.Signals) (hi : Gates.legal kind initial) (hf : Gates.legal kind final)
    (hs : Gates.singleChange initial final) (hne : normal initial ≠ normal final) :
    Reachable B (some 1) ⟨player initial, normal initial⟩ ⟨player final, normal final⟩ := by
  obtain ⟨M⟩ := C.canonical_step initial final hi hf hs
  obtain ⟨hentry, hexit⟩ := M.interface_free hne
  exact (access initial M.entry M.entry_mem hentry).1.trans
    (M.run.trans (access final M.exit M.exit_mem hexit).2)

end PushPuzzle.PushS.FiniteGateForwardContract
