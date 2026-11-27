/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryFailureOnset
public import PushS.PortOrdinaryFailureTrap
import all PushS.PortBackground
import all PushS.PortSegments

/-! Every actual successful prefix avoids every ordinary W fault, with arbitrary current player position. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem initial_outside (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) (e : Endpoint) :
    (l.physicalInstance p hl hM ha initial target).initial.player ∉ ordinaryPocket p e := by
  have zero_outside (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = 0) : q ∉ ordinaryPocket p e := by
    intro hin
    have hx0 := readLength_add_lt_x p e.port 0
    simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, hx] at hin
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at hin <;> omega
  exact zero_outside _ rfl

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial : SignalState)
  (axes : List Bool) (hlegal : l.InputLegal axes) (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial (l.canonical axes)

include hlegal he

/-- No actual ordinary endpoint has a W fault at any prefix of a successful run to a legal canonical target. -/
theorem physicalInstance_ordinary_failure_absent {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : ¬Nonempty (OrdinaryFaultReadout p e u) := by
  let Inv (s : State (p.W + 1) (p.H + 1)) := ¬Nonempty (OrdinaryFaultReadout p e s)
  have hstart : Inv (I).initial := by
    rintro ⟨fault⟩
    exact l.physicalInstance_ordinary_failure_impossible p hl hM ha initial axes hlegal e he .refl (hsu.trans hut) ht
      fault (initial_outside l p hl hM ha initial (l.canonical axes) e)
  have hpath : Relation.ReflTransGen (fun a b => Step (I).board none a b ∧ (Inv a → Inv b)) (I).initial u := by
    apply enrich_path hsu
    intro a b hIa hm hbu
    refine ⟨hm, ?_⟩
    rintro hsource ⟨fault⟩
    have hbt := hbu.trans hut
    have hout := l.physicalInstance_ordinary_failure_onset p hl hM ha initial (l.canonical axes) e he hIa hm hbt ht fault hsource
    exact l.physicalInstance_ordinary_failure_impossible p hl hM ha initial axes hlegal e he (hIa.tail hm) hbt ht fault hout
  have hpres : Inv (I).initial → Inv u :=
    hpath.trans_induction_on (motive := fun {a b} _ => Inv a → Inv b)
      (fun _ => id) (fun hm => hm.2) (fun _ _ h₁ h₂ => h₂ ∘ h₁)
  exact hpres hstart

/-- Every decoded ordinary endpoint receives an actual axis input or at least two horizontal near holes. -/
theorem physicalInstance_ordinary_endpoint_supplied {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {parameter shift horizontal : ℕ}
    (haxis : EndpointAxisReadout p e u parameter shift) (hread : EndpointHorizontalReadout p e u horizontal) :
    parameter ≤ 1 ∨ 2 ≤ horizontal := by
  by_contra hbad
  apply l.physicalInstance_ordinary_failure_absent p hl hM ha initial axes hlegal e he hsu hut ht
  exact ⟨⟨parameter, shift, horizontal, haxis, by omega, hread, by omega⟩⟩

end Solution
end PushPuzzle.PushS.PortLayout
