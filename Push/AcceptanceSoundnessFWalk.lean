/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessFWalkPayment
public import Push.AcceptanceSoundnessFWalkMotion

/-! Genuine trim saturation and no-export inventories certify every actual f-corridor prefix. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

include hgate

/-- Every deepest ordinary f corridor is empty at every actual prefix of the same accepted play. -/
theorem canonical_last_fwalk_empty_at (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    endpointFWalk p e ⊆ PushS.holes u := by
  have hf := canonical_last_fwalk_terminal l p hl hM haxes initial target (hsu.trans hut) ha e he heM
  have hpath := canonical_last_fwalk_forward_between l p hl hM haxes initial target hgate e he heM hsu hut .refl ha
  have hfinal : Disjoint t.boxes (endpointFWalk p e) :=
    Finset.disjoint_left.mpr (fun q hb hq => (PushS.mem_holes _).mp (hf hq) hb)
  have hsource := Inventory.reachable_source_empty hpath hfinal
  exact fun q hq => (PushS.mem_holes _).mpr (fun hb => Finset.disjoint_left.mp hsource hb hq)

/-- The descending deeper-walk invariant certifies the current complete f corridor at every real prefix. -/
theorem canonical_level_fwalk_empty_at_of_deeper (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hP : DeeperWalkInvariant l p hl hM haxes initial target e.level t) : endpointFWalk p e ⊆ PushS.holes u := by
  have hf := canonical_level_fwalk_terminal_of_deeper l p hl hM haxes initial target hgate (hsu.trans hut) ha e he heM hP
  have hpath := canonical_level_fwalk_forward_between_of_deeper l p hl hM haxes initial target hgate e he heM hsu hut .refl ha hP
  have hfinal : Disjoint t.boxes (endpointFWalk p e) :=
    Finset.disjoint_left.mpr (fun q hb hq => (PushS.mem_holes _).mp (hf hq) hb)
  have hsource := Inventory.reachable_source_empty hpath hfinal
  exact fun q hq => (PushS.mem_holes _).mpr (fun hb => Finset.disjoint_left.mp hsource hb hq)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
