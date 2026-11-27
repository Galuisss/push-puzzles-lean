/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.NCL.Asynchronous

/-!
# Decoding asynchronous inward-port claims

A port claims inflow when its physical trigger crosses the inward threshold.
Opposite ports of one edge are exclusive. The two false claims denote an edge
in transit. Weighted gate legality is exactly legality of this decoded partial
orientation. Changing one physical trigger changes at most one source edge.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.NCL.PortClaims

open Cslib.Complexity Cslib.Complexity.NCL

variable {V E : Type*}

/-- Inward activation at each reference port. -/
abbrev Claims (E : Type*) := Port E → Bool

/-- An edge cannot provide inflow to both of its ends. -/
def Exclusive (c : Claims E) : Prop := ∀ e, ¬(c ⟨e, true⟩ = true ∧ c ⟨e, false⟩ = true)

/-- The observed inward weighted flow at a vertex. -/
def inflow (v : Vertex E) (c : Claims E) : ℕ :=
  (v.ports.map fun p => if c p.port then p.weight else 0).sum

/-- One observed weighted vertex constraint. -/
def Satisfied (v : Vertex E) (c : Claims E) : Prop := v.minInflow ≤ inflow v c

/-- Permuting a vertex's actual weighted ports retains its observation constraint. -/
theorem satisfied_iff_of_perm {v w : Vertex E} (hp : v.ports.Perm w.ports)
    (hm : v.minInflow = w.minInflow) (c : Claims E) : Satisfied v c ↔ Satisfied w c := by
  rw [Satisfied, Satisfied, inflow, inflow, hm, (hp.map _).sum_nat]

/-- Read claims through an actual edge renaming, retaining the reference direction. -/
def pullback {E' : Type*} (f : E → E') (c : Claims E') : Claims E := fun p => c (p.map f)

/-- Edge renaming preserves the observed numerical inflow exactly. -/
theorem inflow_map {E' : Type*} (f : E → E') (v : Vertex E) (c : Claims E') :
    inflow (v.map f) c = inflow v (pullback f c) := by
  simp only [inflow, Vertex.map, List.map_map]
  rfl

/-- Every actual weighted gate constraint holds using the observed inward claims. -/
def Legal (G : ConstraintGraph V E) (c : Claims E) : Prop :=
  ∀ v, (G v).minInflow ≤ inflow (G v) c

/-- Both claims false leave the edge in transit. -/
def decode (c : Claims E) : Asynchronous.Orientation E := fun e =>
  if c ⟨e, true⟩ then some true else if c ⟨e, false⟩ then some false else none

/-- Under physical endpoint exclusivity, precisely the active port receives decoded inflow. -/
private theorem assigned_iff {c : Claims E} (hc : Exclusive c) (p : Port E) :
    decode c p.edge = some p.dir ↔ c p = true := by
  obtain ⟨e, d⟩ := p
  have he := hc e
  cases ht : c ⟨e, true⟩ <;> cases hf : c ⟨e, false⟩ <;> cases d <;>
    simp_all [decode]

/-- The gate predicates become the exact partial-orientation legality predicate. -/
private theorem legal_decode_iff {G : ConstraintGraph V E} {c : Claims E} (hc : Exclusive c) :
    Asynchronous.Legal G (decode c) ↔ Legal G c := by
  unfold Asynchronous.Legal Asynchronous.inflow Legal inflow
  simp_rw [assigned_iff hc]

/-- A port observation step changes at most one underlying edge and retains the gate and wire facts. -/
def Step (G : ConstraintGraph V E) (c d : Claims E) : Prop :=
  Exclusive c ∧ Legal G c ∧ Exclusive d ∧ Legal G d ∧
    (c = d ∨ ∃ e, ∀ p : Port E, p.edge ≠ e → d p = c p)

/-- The stronger physical fact that one trigger changes implies the edge-local observation step. -/
theorem step_of_single_port {G : ConstraintGraph V E} {c d : Claims E}
    (hc : Exclusive c) (hlc : Legal G c) (hd : Exclusive d) (hld : Legal G d)
    (p : Port E) (hsame : ∀ q, q ≠ p → d q = c q) : Step G c d := by
  refine ⟨hc, hlc, hd, hld, Or.inr ⟨p.edge, fun q hq => hsame q ?_⟩⟩
  intro he
  exact hq (congrArg Port.edge he)

/-- Every observation step is zero or one legal asynchronous NCL edge step. -/
private theorem Step.decode {G : ConstraintGraph V E} {c d : Claims E} (hs : Step G c d) :
    decode c = decode d ∨ Asynchronous.Step G (decode c) (decode d) := by
  obtain ⟨hc, hlc, hd, hld, he | ⟨e, hsame⟩⟩ := hs
  · exact Or.inl (by cases he; rfl)
  · refine Or.inr ⟨(legal_decode_iff hc).mpr hlc, (legal_decode_iff hd).mpr hld, e, ?_⟩
    intro f hf
    have ht := hsame ⟨f, true⟩ hf
    have hb := hsame ⟨f, false⟩ hf
    change (if d ⟨f, true⟩ then some true else if d ⟨f, false⟩ then some false else none) =
      (if c ⟨f, true⟩ then some true else if c ⟨f, false⟩ then some false else none)
    rw [ht, hb]

/-- Preserve an entire arbitrary interleaving of gate and wire observations. -/
private theorem reachable_decode {G : ConstraintGraph V E} {c d : Claims E}
    (hr : Relation.ReflTransGen (Step G) c d) :
    Relation.ReflTransGen (Asynchronous.Step G) (decode c) (decode d) := by
  induction hr with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs.decode with he | he
    · exact he ▸ ih
    · exact ih.tail he

/-- The complete port activation supplied by an ordinary source orientation. -/
def full (s : E → Bool) : Claims E := fun p => decide (p.In s)

private theorem full_eq_true (s : E → Bool) (p : Port E) : full s p = true ↔ p.In s := by
  simp only [full, decide_eq_true_eq]

private theorem full_exclusive (s : E → Bool) : Exclusive (full s) := by
  intro e
  cases hb : s e <;> simp [full, Port.In, hb]

private theorem decode_full (s : E → Bool) : decode (full s) = Asynchronous.full s := by
  funext e
  cases hb : s e <;> simp [decode, full, Port.In, Asynchronous.full, hb]

private theorem legal_full (G : ConstraintGraph V E) (s : E → Bool) : Legal G
    (full s) ↔ G.Legal s := by
  rw [← legal_decode_iff (full_exclusive s), decode_full, Asynchronous.legal_full]

variable [DecidableEq E]

private theorem full_step {G : ConstraintGraph V E} {s t : E → Bool} (hs : G.Step s t) :
    Step G (full s) (full t) := by
  obtain ⟨hs, ht, e, rfl⟩ := hs
  refine ⟨full_exclusive s, (legal_full G s).mpr hs, full_exclusive _,
    (legal_full G _).mpr ht, Or.inr ⟨e, ?_⟩⟩
  intro p hp
  apply Bool.eq_iff_iff.mpr
  rw [full_eq_true, full_eq_true]
  change reverse s e p.edge = p.dir ↔ s p.edge = p.dir
  rw [reverse, Function.update_of_ne hp]

/-- Exclusive legal port observations recover exactly ordinary reachability at complete endpoints. -/
theorem full_reachable_iff {G : ConstraintGraph V E} {s t : E → Bool} :
    Relation.ReflTransGen (Step G) (full s) (full t) ↔ G.Reachable s t := by
  constructor
  · intro hr
    have hd := reachable_decode hr
    rw [decode_full, decode_full] at hd
    exact Asynchronous.full_reachable_iff.mp hd
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail (full_step hs)

end PushPuzzle.NCL.PortClaims
