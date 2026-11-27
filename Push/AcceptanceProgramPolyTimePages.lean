/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeRequests
public import Push.AcceptanceProgramNarrowSignals
import all PushS.PortSegments
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals

/-! Actual main-axis and upper-probe requests from bounded endpoint levels. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS Turing.MultiTapeTM Push.AcceptanceProgram

attribute [local fun_prop] endpoints_polyTime encEndpoint_side_polyTime encEndpoint_level_polyTime encEndpoint_port_polyTime

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)
  (hpages : ∀ a, (layout a).pages.Valid)
  (hhighest : ∀ a, (layout a).pages.highest ≤ (p a).levels)

include hl haxes hlevels hpages hhighest

/-- Every actual endpoint emits its main-axis span using the genuine bounded scale lookup. -/
private theorem acceptance_endpointRequests_polyTime (side : Side) :
    ComputableInPolyTime (fun a => ((layout a).endpoints.filter fun e => e.side == side).map
      fun e => ((p a).x e.port, (p a).Y e.level + 2)) enc Push.Scan.encRequests := by
  have hD : ComputableInPolyTime (fun q : α × Endpoint => (p q.1).D) (encPair enc encEndpoint) encUnary :=
    (computableInPolyTime_D haxes hlevels).comp (ComputableInPolyTime.fst _ _)
  have htable : ComputableInPolyTime (fun q : α × Endpoint => fullDepthTable (p q.1))
      (encPair enc encEndpoint) (encList encUnary) :=
    (fullDepthTable_polyTime haxes hlevels).comp (ComputableInPolyTime.fst _ _)
  have hbeq : ComputableInPolyTime (fun s : Side => s == side) encSide encBool := .of_finite _
  have hfiltered : ComputableInPolyTime (fun a => (layout a).endpoints.filter fun e => e.side == side)
      enc (encList encEndpoint) := by fun_prop
  have hcallback : ComputableInPolyTime (fun q : α × Endpoint =>
      ((q.2.port + 1) * (p q.1).D, (fullDepthTable (p q.1)).getD q.2.level 0 + 2))
      (encPair enc encEndpoint) (encPair encUnary encUnary) := by fun_prop
  have hraw := ComputableInPolyTime.mapWithInput
    (f := fun a e => ((e.port + 1) * (p a).D, (fullDepthTable (p a)).getD e.level 0 + 2)) hfiltered hcallback
  exact hraw.of_enc_eq (fun a => by
    apply congrArg Push.Scan.encRequests
    apply List.map_congr_left
    intro e he
    obtain ⟨_, hbound⟩ := (layout a).endpoints_level_bounds (p a) (hpages a) (hhighest a) (List.mem_filter.mp he).1
    rw [fullDepthTable_getD _ hbound]
    rfl)

/-- The actual upper-axis probe rows emit from their original endpoint requests. -/
theorem acceptance_probeRows_polyTime :
    ComputableInPolyTime (fun a => probeRows (layout a) (p a)) enc encLaneSet := by
  have hr := acceptance_endpointRequests_polyTime hl haxes hlevels hpages hhighest .upper
  have hs : ComputableInPolyTime (fun a =>
      ((((layout a).endpoints.filter fun e => e.side == .upper).map
        fun e => ((p a).x e.port, (p a).Y e.level + 2)).map Prod.snd).toFinset) enc encLaneSet := by fun_prop
  exact hs.of_enc_eq (fun a => by
    apply congrArg encLaneSet
    simp only [probeRows, List.map_map, Function.comp_def])

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {layout : α → PortLayout} {p : α → Scales.Parameters} {M : ℕ}
  (hl : ComputableInPolyTime layout enc encPortLayout)
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)
  (hpages : ∀ a, (layout a).pages.Valid)
  (hhighest : ∀ a, (layout a).pages.highest ≤ (p a).levels)

include hl haxes hlevels hpages hhighest

/-- The actual main-axis prefix block emits in standard polynomial time on either page. -/
theorem mainRound_polyTime (side : Side) :
    ComputableInPolyTime (fun a => mainRound (layout a) (p a) side) enc encTemplate := by
  have hr := acceptance_endpointRequests_polyTime hl haxes hlevels hpages hhighest side
  unfold mainRound
  fun_prop

end PushPuzzle.Push.AcceptanceProgram
