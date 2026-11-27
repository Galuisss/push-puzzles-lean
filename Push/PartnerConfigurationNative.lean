/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationOrdered
public import PushS.PortConstraintStep

/-! Standard native weighted configuration equivalence of the actual reader-partner compiler. -/

public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

/-- The actual repaired native weighted graph has exactly the original native configuration reachability. -/
theorem repairAxes_nativeReachable_iff {l : PortLayout} (hl : l.pages.Valid) (axes next : List Bool)
    (hlen : axes.length = l.portCount) (hnlen : next.length = l.portCount) :
    (repair l).layout.graphData.graph.Reachable
        ((repair l).layout.graphData.config (repairAxes l axes))
        ((repair l).layout.graphData.config (repairAxes l next)) ↔
      l.graphData.graph.Reachable (l.graphData.config axes) (l.graphData.config next) :=
  ((repair l).layout.graphData_reachable_iff
    ((repair l).layout.graphData_bounded_of_pages (repair_valid hl)) _ _
    (repairAxes_length l axes hlen) (repairAxes_length l next hnlen)).trans
      ((repairAxes_reachable_iff hl axes next hlen hnlen).trans
        (l.graphData_reachable_iff (l.graphData_bounded_of_pages hl) axes next hlen hnlen).symm)

end PushPuzzle.Push.Partner.Cuts
