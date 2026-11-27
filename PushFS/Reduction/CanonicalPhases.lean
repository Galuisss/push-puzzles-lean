/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateStraight

/-! Actual gate claims and ordinary-wire phases are bound to the same original source orientation bits. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan Gadgets Gadgets.Wires

/-- Read an inward claim from the real left/upper/outward-right physical flag convention. -/
def gateClaim (a : Gates.Signals) (role : Fin 3) : Bool :=
  if role=2 then !a.right else a.get role

theorem gateSignals_claim (p : OrderedPorts) (bits : List Bool) (role : Fin 3) :
    gateClaim (gateSignals (p,bits)) role=decide ((p.port role).In (fun e=>bits.getD e false)) := by
  fin_cases role <;> simp [gateClaim,gateSignals,OrderedPorts.signals,OrderedPorts.port,Gates.Signals.get]

/-- The actual annular arm phase agrees with the ordinary wire phase at an output and is complementary at an input. -/
theorem gateSignals_wire_phase (p : OrderedPorts) (bits : List Bool) (role : Fin 3) :
    gateClaim (gateSignals (p,bits)) role=
      if (p.port role).dir then bits.getD (p.port role).edge false else !(bits.getD (p.port role).edge false) := by
  rw [gateSignals_claim]
  have hh : ∀ a b : Bool,decide (a=b)=(if b then a else !a) := by decide +kernel
  exact hh _ _

namespace CellPlan

/-- Every actual gate-input neighbor carries the original edge and both complete canonical wire phases. -/
theorem input_cell (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords q.1) (role : Fin 3) (hin : (v.ports.port role).dir=true) :
    ∃ p k,neighbor (v.portDirection role) (refinePoint v.point)=some p ∧
      cell (q,p)=some (.inr ((v.ports.port role).edge,
        (k,!(q.2.1.getD (v.ports.port role).edge false),!(q.2.2.getD (v.ports.port role).edge false)))) ∧
      Catalog.sourceDirection k=(v.portDirection role).opposite ∧
      Catalog.targetDirection k=(v.portDirection role).opposite ∧ (k=.east ∨ k=.west ∨ k=.south) := by
  obtain ⟨p,k,hp,hv',he,hk,hs,ht,hstraight⟩ := Raster.gate_input_straight hP hT hv role hin
  refine ⟨p,k,hp,?_,hs,ht,hstraight⟩
  simp only [cell,hv',Option.elim_none,ordinary,he,Option.elim_some,wireData,hk,Option.map_some]

/-- Every actual gate-output neighbor carries the original edge and both complete canonical wire phases. -/
theorem output_cell (q : Source) (hP : q.1.checkPlane=true) (hT : q.1.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords q.1) (role : Fin 3) (hout : (v.ports.port role).dir=false) :
    ∃ p k,neighbor (v.portDirection role) (refinePoint v.point)=some p ∧
      cell (q,p)=some (.inr ((v.ports.port role).edge,
        (k,!(q.2.1.getD (v.ports.port role).edge false),!(q.2.2.getD (v.ports.port role).edge false)))) ∧
      Catalog.sourceDirection k=v.portDirection role ∧ Catalog.targetDirection k=v.portDirection role ∧
      (k=.east ∨ k=.west ∨ k=.south) := by
  obtain ⟨p,k,hp,hv',he,hk,hs,ht,hstraight⟩ := Raster.gate_output_straight hP hT hv role hout
  refine ⟨p,k,hp,?_,hs,ht,hstraight⟩
  simp only [cell,hv',Option.elim_none,ordinary,he,Option.elim_some,wireData,hk,Option.map_some]

end CellPlan
end PushPuzzle.PushFS.Reduction
