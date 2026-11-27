/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointReadouts
public import PushS.PortEndpointReadoutUnique
public import PushS.PortInputStep
import all PushS.PortAxisGroups
import all PushS.PortAxisTrainReadout
import all PushS.PortGateAxisTrainReadout
import CslibFrontier.Foundations.Data.List.Lookup

/-! The actual physical axis inputs as one original port-order Boolean array. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- One port-order bit array read from all actual upper ordinary half-axis words. -/
structure AxisReadout (l : PortLayout) (p : Scales.Parameters)
    (u : State (p.W + 1) (p.H + 1)) (axes : List Bool) : Prop where
  axes_length : axes.length = l.portCount
  upper_exists (e : Endpoint) (endpoint : e ∈ l.endpoints) (side : e.side = .upper) :
    ∃ parameter shift, EndpointAxisReadout p e u parameter shift
  upper (e : Endpoint) (endpoint : e ∈ l.endpoints) (side : e.side = .upper)
      {parameter shift : ℕ} (word : EndpointAxisReadout p e u parameter shift) :
    axes.getD e.port false = true ↔ parameter ≤ 1

/-- A decoded original Boolean array together with its actual complete physical readout. -/
structure DecodedAxes (l : PortLayout) (p : Scales.Parameters) (u : State (p.W + 1) (p.H + 1)) where
  axes : List Bool
  readout : l.AxisReadout p u axes

/-- Upper ordinary input absence is the complementary threshold on its actual parameter. -/
theorem AxisReadout.upper_false_iff {l : PortLayout} {p : Scales.Parameters}
    {u : State (p.W + 1) (p.H + 1)} {axes : List Bool} (hr : l.AxisReadout p u axes)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .upper) {parameter shift : ℕ}
    (word : EndpointAxisReadout p e u parameter shift) : axes.getD e.port false = false ↔ 2 ≤ parameter := by
  rw [Bool.eq_false_iff, ne_eq, hr.upper e he hs word]
  omega

/-- The actual upper half-axis words determine the entire original Boolean array uniquely. -/
theorem AxisReadout.unique {l : PortLayout} {p : Scales.Parameters}
    (hl : l.pages.Valid) {u : State (p.W + 1) (p.H + 1)} {axes next : List Bool}
    (hr : l.AxisReadout p u axes) (hs : l.AxisReadout p u next) : axes = next := by
  apply List.ext_getElem (hr.axes_length.trans hs.axes_length.symm)
  intro i hi hj
  have hip : i < l.portCount := by simpa only [hr.axes_length] using hi
  obtain ⟨e, he, hside, hp⟩ := l.endpoints_upper_exists hl hip
  obtain ⟨parameter, shift, word⟩ := hr.upper_exists e he hside
  have h0 := hr.upper e he hside word
  have h1 := hs.upper e he hside word
  rw [hp] at h0 h1
  have hb : axes.getD i false = next.getD i false := Bool.eq_iff_iff.mpr (h0.trans h1.symm)
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hb

/-- A genuine ordinary shared-axis readout interprets its lower input as the complement of the same decoded bit. -/
theorem AxisReadout.lower_false_iff {l : PortLayout} {p : Scales.Parameters}
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {u : State (p.W + 1) (p.H + 1)} {axes : List Bool} (hr : l.AxisReadout p u axes)
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hp : lower.port = upper.port)
    {a : OrdinaryAxisPlacement} (joint : OrdinaryAxisReadout p upper lower u a)
    {parameter shift : ℕ} (word : EndpointAxisReadout p lower u parameter shift) :
    parameter ≤ 1 ↔ axes.getD lower.port false = false := by
  have hupper := hr.upper upper hu hsu (joint.upper_endpoint hsu)
  have heq := l.endpoint_axis_parameter_unique p hl hM ha hlow word (joint.lower_endpoint hsl hp)
  have hbound := joint.parameter_le
  rw [hp, Bool.eq_false_iff, ne_eq, hupper]
  unfold OrdinaryAxisPlacement.lowerParameter at heq
  omega

/-- The actual lower gate-middle input is the complement of the same original decoded axis bit. -/
theorem AxisReadout.gate_middle_false_iff {l : PortLayout} {p : Scales.Parameters}
    {u : State (p.W + 1) (p.H + 1)} {axes : List Bool} (hr : l.AxisReadout p u axes)
    {g : Placement} {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper)
    (hp : upper.port = g.left + 1) {a : GateAxisPlacement} (joint : GateAxisReadout p g upper u a) :
    2 ≤ a.parameter ↔ axes.getD (g.left + 1) false = false := by
  have hupper := hr.upper upper hu hsu (joint.upper_endpoint hsu hp)
  rw [← hp, Bool.eq_false_iff, ne_eq, hupper]
  omega

private theorem parameter_supplied (depth : ℕ) (bit : Bool) :
    ((depth : ℤ) + 4 - ((depth : ℤ) + 2 + bit.toNat)).toNat ≤ 1 ↔ bit = true := by
  cases bit <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.false_eq_true, iff_false, iff_true] <;> omega

private theorem encoded_ordinary_upper (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hp : lower.port = upper.port) :
    ∃ parameter shift, EndpointAxisReadout p upper s parameter shift ∧
      (parameter ≤ 1 ↔ state.axes.getD upper.port false = true) := by
  let b := ordinaryAxisTrainBlocks p upper lower state
  have hslots := l.encodedSegments_ordinaryAxis_train_slots p hl hM ha state hu hlow hsu hsl hp s hholes
  rw [BoxMask.lineBoxes_keep (axis := .south) (lane := p.x upper.port)
    (fun _ hq => (Finset.mem_filter.mp hq).2.1)] at hslots
  have hshape : OrdinaryAxisTrainShape p upper lower s b :=
    ⟨rfl, rfl, rfl, l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow state, hslots⟩
  have hword := (hshape.readout (l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow state)).upper_endpoint hsu
  refine ⟨_, _, hword, ?_⟩
  change ((readDepth p upper.level : ℤ) + 4 -
    ((readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat)).toNat ≤ 1 ↔ _
  exact parameter_supplied _ _

private theorem encoded_gate_upper (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    ∃ parameter shift, EndpointAxisReadout p upper s parameter shift ∧
      (parameter ≤ 1 ↔ state.axes.getD upper.port false = true) := by
  let b := gateAxisTrainBlocks p upper state
  have hslots := l.encodedSegments_gateAxis_train_slots p hl hM ha state hg hk hu hsu hp s hholes
  rw [BoxMask.lineBoxes_keep (axis := .south) (lane := p.x (g.left + 1))
    (fun _ hq => (Finset.mem_filter.mp hq).2.1)] at hslots
  have hshape : GateAxisTrainShape p g upper s b :=
    ⟨rfl, rfl, l.gateAxisTrainBlocks_gapped p hl hM hu state, hslots⟩
  have hword := (hshape.readout (l.gateAxisTrainBlocks_positive p hl hM hu state)).upper_endpoint hsu hp
  refine ⟨_, _, hword, ?_⟩
  change ((readDepth p upper.level : ℤ) + 4 -
    ((readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat)).toNat ≤ 1 ↔ _
  exact parameter_supplied _ _

private theorem encoded_upper_word (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (e : Endpoint) (he : e ∈ l.endpoints) (hs : e.side = .upper) :
    ∃ parameter shift, EndpointAxisReadout p e s parameter shift ∧
      (parameter ≤ 1 ↔ state.axes.getD e.port false = true) := by
  obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
  have ordinary (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) :
      ∃ parameter shift, EndpointAxisReadout p e s parameter shift ∧
        (parameter ≤ 1 ↔ state.axes.getD e.port false = true) := by
    obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
    exact encoded_ordinary_upper l p hl hM ha state s hholes he hlow hs (hls.trans groups.lower_side) hlp
  rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
  · exact ordinary (Or.inl hleft)
  · exact ordinary (Or.inr hright)
  · cases hk : groups.lower.gate with
    | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
    | some kind => exact encoded_gate_upper l p hl hM ha state s hholes groups.lower_mem hk he hs hmid

/-- A complete original signal encoding reads exactly its original full axis array. -/
theorem encodedSegments_axisReadout (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hlen : state.axes.length = l.portCount) : l.AxisReadout p s state.axes := by
  refine ⟨hlen, ?_, ?_⟩
  · intro e he hs
    obtain ⟨parameter, shift, word, _⟩ := encoded_upper_word l p hl hM ha state s hholes e he hs
    exact ⟨parameter, shift, word⟩
  · intro e he hs parameter shift word
    obtain ⟨parameter', shift', hword, hread⟩ := encoded_upper_word l p hl hM ha state s hholes e he hs
    have heq := l.endpoint_axis_parameter_unique p hl hM ha he hword word
    rw [← heq]
    exact hread.symm

/-- Every physical readout of a complete original encoding equals its full original axis array. -/
theorem AxisReadout.encoded_eq {l : PortLayout} {p : Scales.Parameters}
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {s : State (p.W + 1) (p.H + 1)} {axes : List Bool} (hr : l.AxisReadout p s axes)
    (state : SignalState)
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hlen : state.axes.length = l.portCount) : axes = state.axes :=
  hr.unique hl (l.encodedSegments_axisReadout p hl hM ha state s hholes hlen)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every successful physical prefix has a genuine readout as one existing port-order Boolean array. -/
theorem physicalInstance_axisReadout_exists {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : ∃ axes, l.AxisReadout p u axes := by
  classical
  have hex (i : Fin l.portCount) : ∃ e : Endpoint, e ∈ l.endpoints ∧ e.side = .upper ∧ e.port = i.val ∧
      ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
    obtain ⟨e, he, hs, hp⟩ := l.endpoints_upper_exists hl i.isLt
    obtain ⟨parameter, shift, word⟩ := l.physicalInstance_endpoint_axis_readout p hl hM ha initial target e he hsu hut ht
    exact ⟨e, he, hs, hp, parameter, shift, word⟩
  choose endpoint endpoint_mem endpoint_side endpoint_port parameter shift word using hex
  let axes := List.ofFn fun i : Fin l.portCount => decide (parameter i ≤ 1)
  refine ⟨axes, ⟨by simp only [axes, List.length_ofFn], ?_, ?_⟩⟩
  · intro e he _
    exact l.physicalInstance_endpoint_axis_readout p hl hM ha initial target e he hsu hut ht
  · intro e he hs parameter' shift' word'
    let i : Fin l.portCount := ⟨e.port, l.endpoints_port_lt hl he⟩
    have heq : endpoint i = e := l.endpoints_key_injective hl (endpoint_mem i) he
      ((endpoint_side i).trans hs.symm) (endpoint_port i)
    have hword : EndpointAxisReadout p e u (parameter i) (shift i) := heq ▸ word i
    have hparameter := l.endpoint_axis_parameter_unique p hl hM ha he hword word'
    change (List.ofFn fun j : Fin l.portCount => decide (parameter j ≤ 1)).getD e.port false = true ↔ _
    rw [List.getD_ofFn_of_lt _ (l.endpoints_port_lt hl he) false]
    change decide (parameter i ≤ 1) = true ↔ _
    rw [decide_eq_true_eq, hparameter]

/-- Package the actual original axis array and its complete physical readout at any successful prefix. -/
theorem physicalInstance_decodedAxes_nonempty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : Nonempty (l.DecodedAxes p u) := by
  obtain ⟨axes, hr⟩ := l.physicalInstance_axisReadout_exists p hl hM ha initial target hsu hut ht
  exact ⟨⟨axes, hr⟩⟩

/-- Any actual lower ordinary endpoint reads the false input of its unique decoded original axis. -/
theorem physicalInstance_decoded_lower {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {axes : List Bool} (hr : l.AxisReadout p u axes)
    {lower : Endpoint} (hlow : lower ∈ l.endpoints) (hsl : lower.side = .lower)
    {parameter shift : ℕ} (word : EndpointAxisReadout p lower u parameter shift) :
    parameter ≤ 1 ↔ axes.getD lower.port false = false := by
  obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl hlow)
  obtain ⟨a, joint⟩ := l.physicalInstance_ordinaryAxis_train_readout p hl hM ha initial target hu hlow hsuSide hsl hp.symm hsu hut ht
  exact hr.lower_false_iff hl hM ha hu hlow hsuSide hsl hp.symm joint word

/-- The actual initial physical readout restores its entire original axis array. -/
theorem physicalInstance_decoded_initial {axes : List Bool} (hr : l.AxisReadout p (I).initial axes)
    (hlen : initial.axes.length = l.portCount) : axes = initial.axes :=
  hr.encoded_eq hl hM ha initial (l.physicalInstance_initial_holes p hl hM ha initial target) hlen

/-- The actual storage goal readout restores the entire original target axis array. -/
theorem physicalInstance_decoded_goal {t : State (p.W + 1) (p.H + 1)} (ht : t.boxes = (I).board.goals)
    {axes : List Bool} (hr : l.AxisReadout p t axes) (hlen : target.axes.length = l.portCount) : axes = target.axes := by
  apply hr.encoded_eq hl hM ha target _ hlen
  change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
  rw [ht]
  exact l.physicalInstance_goal_holes p hl hM ha initial target

end Solution

/-- A readout of the emitted canonical initial state restores the exact original interface word. -/
theorem canonicalInstance_decoded_initial (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
    (hlen : initial.length = l.portCount) {axes : List Bool}
    (hr : l.AxisReadout p (l.canonicalInstance p hl hM ha initial target).initial axes) : axes = initial :=
  l.physicalInstance_decoded_initial p hl hM ha (l.canonical initial) (l.canonical target) hr hlen

/-- A readout of the emitted exact canonical storage goal restores the complete original target word. -/
theorem canonicalInstance_decoded_goal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
    (hlen : target.length = l.portCount) {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (l.canonicalInstance p hl hM ha initial target).board.goals)
    {axes : List Bool} (hr : l.AxisReadout p t axes) : axes = target :=
  l.physicalInstance_decoded_goal p hl hM ha (l.canonical initial) (l.canonical target) ht hr hlen

end PushPuzzle.PushS.PortLayout
