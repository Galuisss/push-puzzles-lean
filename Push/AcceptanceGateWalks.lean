/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalks
public import Push.AcceptanceGatePrivateWalk

/-! Complete accepted-source gate walk and private closure certificates after the actual ordinary descent. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- All actual ordinary and gate public corridors are empty at every accepted source prefix. -/
theorem canonical_publicWalkInvariant {t : State (p.W + 1) (p.H + 1)}
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    PublicWalkInvariant l p hl hM haxes initial target t :=
  canonical_publicWalkInvariant_of_ordinary l p hl hM haxes initial target hgate accepted
    (fun _ hs ht => canonical_ordinaryWalks_empty l p hl hM haxes initial target hgate hs ht accepted)

/-- Every actual gate interlevel marker stays empty and unvisited on the accepted trajectory. -/
theorem canonical_gate_interlevel_excluded {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Blocked.Excluded (l.gateInterlevelMarkers p) u :=
  canonical_gate_interlevel_excluded_of_deeper l p hl hM haxes initial target hsu hut accepted
    (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht accepted)

/-- Both actual half-depth gate markers stay empty and unvisited on the accepted trajectory. -/
theorem canonical_gate_halfMarkers_excluded {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Blocked.Excluded (l.gateHalfMarkers p) u :=
  canonical_gate_half_excluded_of_public l p hl hM haxes initial target hsu hut accepted
    (canonical_publicWalkInvariant l p hl hM haxes initial target hgate accepted)

/-- Every accepted source prefix avoids the complete actual private gate closure. -/
theorem canonical_gate_private_avoiding_prefix {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none (l.gatePrivateBlockers p hl hM haxes hi)) (I).initial u :=
  canonical_gate_private_avoiding_of_walks l p hl hM haxes initial target hgate hi hsu hut accepted
    (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht accepted)
    (canonical_publicWalkInvariant l p hl hM haxes initial target hgate accepted)

/-- Every complete actual next push ray avoids those same private gate blockers. -/
theorem canonical_gate_private_step_avoiding {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Freeze.AvoidingStep (I).board none (l.gatePrivateBlockers p hl hM haxes hi) u v :=
  canonical_gate_private_step_avoiding_of_walks l p hl hM haxes initial target hgate hi hsu step hvt accepted
    (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht accepted)
    (canonical_publicWalkInvariant l p hl hM haxes initial target hgate accepted)

/-- All four actual long gate corridors stay empty at every accepted source prefix. -/
theorem canonical_gate_publicWalk_empty {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : gatePublicWalk p middle ⊆ holes u :=
  canonical_gate_publicWalk_empty_of_deeper l p hl hM haxes initial target hgate hi hsu hut accepted
    (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht accepted)

/-- The actual private cap and four-cell branch stay empty at every accepted source prefix. -/
theorem canonical_gate_privateWalk_empty {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : gatePrivateWalk p middle ⊆ holes u :=
  canonical_gate_privateWalk_empty_of_walks l p hl hM haxes initial target hgate hi hsu hut accepted
    (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 hs ht accepted)
    (canonical_publicWalkInvariant l p hl hM haxes initial target hgate accepted)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
