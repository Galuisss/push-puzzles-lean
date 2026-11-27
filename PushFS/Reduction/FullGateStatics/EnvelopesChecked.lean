/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Envelopes

/-! Phase-local canonical goal separation at the actual primitive seams. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private abbrev withTarget (g : GateTileState) (b : Gates.Signals) : GateTileState :=
  {g with core := {g.core with target := b}}

private theorem indices_target (g : GateTileState) (b : Gates.Signals) :
    indices (withTarget g b) = indices g := rfl

private theorem rectangle_target (g : GateTileState) (b : Gates.Signals) (i : Inventory.Index g) :
    rectangle (withTarget g b) i = rectangle g i := by
  rcases i with i | (⟨role,j | j⟩ | role) <;> rfl

private def Inside (r : Envelope) (box : Rectangle) : Prop :=
  r.loX ≤ r.hiX ∧ r.loY ≤ r.hiY ∧
  box.x < r.loX ∧ r.hiX + 1 < box.x + box.width ∧
    box.y < r.loY ∧ r.hiY + 1 < box.y + box.height

private theorem inside_apart {r s : Envelope} {a b : Rectangle}
    (hr : Inside r a) (hs : Inside s b) (h : a.Disjoint b) : r.Apart s := by
  dsimp [Inside, Rectangle.Disjoint, Envelope.Apart] at *
  omega

private theorem placed_inside (o : RectOrientation) (w h dx dy : ℕ) (r : Envelope)
    (hr : Inside r ⟨0, 0, w, h⟩) :
    Inside (r.placed o w h dx dy) ⟨dx, dy, o.width w h, o.height w h⟩ := by
  rcases o with ⟨swap, fx, fy⟩
  cases swap <;> cases fx <;> cases fy <;>
    simp only [Inside, Envelope.placed, RectOrientation.point, RectOrientation.width,
      RectOrientation.height, Bool.false_eq_true, reduceIte, Nat.zero_add] at hr ⊢ <;> omega

private theorem rail_inside (n : ℕ) (hn : 2 ≤ n) (flip phase : Bool) :
    Inside (Envelope.rail n flip phase) ⟨0, 0, n + (if flip then 25 else 5), 21⟩ := by
  have hp := Bool.toNat_le phase
  cases flip <;> simp only [Inside, Envelope.rail, Bool.false_eq_true, reduceIte,
    Nat.zero_add] <;> omega

/-- A canonical interval controlled by one target port. -/
private structure PhaseEnvelope where
  port : Fin 3
  zero : Envelope
  one : Envelope

private def PhaseEnvelope.eval (r : PhaseEnvelope) (b : Gates.Signals) : Envelope :=
  if b.get r.port then r.one else r.zero

private def PhaseEnvelope.span (r : PhaseEnvelope) : Envelope := r.zero.join r.one

private def PhaseEnvelope.apart (r s : PhaseEnvelope) : Bool :=
  decide (r.span.Apart s.span) ||
    if r.port = s.port then decide (r.zero.Apart s.zero ∧ r.one.Apart s.one)
    else decide (r.zero.Apart s.zero ∧ r.zero.Apart s.one ∧
      r.one.Apart s.zero ∧ r.one.Apart s.one)

private theorem PhaseEnvelope.apart_sound (r s : PhaseEnvelope) (h : r.apart s = true)
    (b : Gates.Signals) : (r.eval b).Apart (s.eval b) := by
  simp only [PhaseEnvelope.apart, Bool.or_eq_true] at h
  rcases h with h | h
  · have hh := of_decide_eq_true h
    cases hr : b.get r.port <;> cases hs : b.get s.port <;>
      simp only [PhaseEnvelope.eval, hr, hs, Bool.false_eq_true, reduceIte] <;>
      dsimp only [PhaseEnvelope.span, Envelope.join, Envelope.Apart] at hh ⊢ <;> omega
  · by_cases hp : r.port = s.port
    · rw [ite_eq_left hp] at h
      have hh := of_decide_eq_true h
      cases hb : b.get s.port
      · simpa only [PhaseEnvelope.eval, hp, hb, Bool.false_eq_true, reduceIte] using hh.1
      · simpa only [PhaseEnvelope.eval, hp, hb, Bool.false_eq_true, reduceIte] using hh.2
    · rw [ite_eq_right hp] at h
      have hh := of_decide_eq_true h
      cases hr : b.get r.port <;> cases hs : b.get s.port <;>
        simp only [PhaseEnvelope.eval, hr, hs, Bool.false_eq_true, reduceIte]
      all_goals first | exact hh.1 | exact hh.2.1 | exact hh.2.2.1 | exact hh.2.2.2


private instance (r : Envelope) (box : Rectangle) : Decidable (Inside r box) := by
  unfold Inside
  infer_instance

private theorem core_inside_checked : ∀ kind : Bool,
    (Gates.slots kind).all (fun s => decide
      (Inside (Envelope.point (s.zero.1.val, s.zero.2.val)) ⟨0, 0, 81, 107⟩ ∧
       Inside (Envelope.point (s.one.1.val, s.one.2.val)) ⟨0, 0, 81, 107⟩)) = true := by
  decide +kernel

private theorem core_inside (kind : Bool) (s : Gates.Slot) (hs : s ∈ Gates.slots kind)
    (b : Gates.Signals) :
    Inside (Envelope.point ((s.position b).1.val, (s.position b).2.val)) ⟨0, 0, 81, 107⟩ := by
  have h := of_decide_eq_true (List.all_eq_true.mp (core_inside_checked kind) s hs)
  cases hb : b.get s.port <;> simp only [Gates.Slot.position, hb, Bool.false_eq_true, reduceIte]
  · exact h.1
  · exact h.2

private theorem short_inside : ∀ (k : ShortCorners.Kind) (b : Bool)
    (l : Fin (ShortCorners.count k)),
    Inside (Envelope.point (((ShortCorners.template k).position b l).1.val,
      ((ShortCorners.template k).position b l).2.val)) ⟨0, 0, ShortCorners.width k, ShortCorners.height k⟩ := by
  decide +kernel

private theorem point_shift_inside (p : ℕ × ℕ) (dx dy w h : ℕ)
    (hp : Inside (Envelope.point p) ⟨0, 0, w, h⟩) :
    Inside (Envelope.point (dx + p.1, dy + p.2)) ⟨dx, dy, w, h⟩ := by
  dsimp only [Inside, Envelope.point] at *
  omega

private theorem envelopes_inside (g : GateTileState) (i : Inventory.Index g)
    (r : Envelope) (hr : r ∈ envelopes g i) : Inside r (rectangle g i) := by
  rcases i with i | (⟨role,j | j⟩ | role)
  · fin_cases i
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact point_shift_inside _ _ _ _ _ (core_inside g.core.isAND s hs g.core.target)
    all_goals
      have he := List.mem_singleton.mp hr
      subst r
      exact placed_inside _ _ _ _ _ _ (rail_inside 2301 (by omega) false _)
  · have he := List.mem_singleton.mp hr
    subst r
    exact placed_inside _ _ _ _ _ _ (rail_inside _ (by
      have h := (filler_shape (key g role) j.val j.isLt).2.1
      omega) _ _)
  · obtain ⟨l, _, rfl⟩ := List.mem_map.mp hr
    have h := placed_inside (cornerOrientation (key g role) j.val)
      (ShortCorners.width (cornerKind (key g role) j.val))
      (ShortCorners.height (cornerKind (key g role) j.val))
      (cornerOffset (key g role) j.val).1 (cornerOffset (key g role) j.val).2 _
      (short_inside (cornerKind (key g role) j.val) (targetPhase g role) l)
    simpa only [Envelope.placed, Envelope.point, min_self, max_self, rectangle, geometricOffset, dimensions] using h
  · cases hr

private theorem envelopes_inside_target (g : GateTileState) (b : Gates.Signals) (i : Inventory.Index g)
    (r : Envelope) (hr : r ∈ envelopes (withTarget g b) i) : Inside r (rectangle g i) := by
  simpa only [rectangle_target] using envelopes_inside (withTarget g b) i r hr

private def roleEnvelope (port : Fin 3) (f : Bool → Envelope) : PhaseEnvelope :=
  ⟨port, f (gateClaim ⟨false, false, false⟩ port), f (gateClaim ⟨true, true, true⟩ port)⟩

private theorem roleEnvelope_eval (port : Fin 3) (f : Bool → Envelope) (b : Gates.Signals) :
    (roleEnvelope port f).eval b = f (gateClaim b port) := by
  fin_cases port
  · cases hb : b.left <;> simp [roleEnvelope, PhaseEnvelope.eval, gateClaim, Gates.Signals.get, hb]
  · cases hb : b.upper <;> simp [roleEnvelope, PhaseEnvelope.eval, gateClaim, Gates.Signals.get, hb]
  · cases hb : b.right <;> simp [roleEnvelope, PhaseEnvelope.eval, gateClaim, Gates.Signals.get, hb]

private def lineEnvelope (g : GateTileState) (role : Fin 3) (j : ℕ) (b : Bool) : Envelope :=
  Envelope.placed (lineOrientation (original (key g role) j).travel (fillerFlip (key g role) j))
    (lineWidth (key g role) j) 21 (lineOffset (key g role) j).1 (lineOffset (key g role) j).2
    (Envelope.rail (fillerSpan (key g role) j) (fillerFlip (key g role) j) b)

private def cornerEnvelope (g : GateTileState) (role : Fin 3) (j : ℕ)
    (l : Fin (ShortCorners.count (cornerKind (key g role) j))) (b : Bool) : Envelope :=
  let p := (ShortCorners.template (cornerKind (key g role) j)).position b l
  let q := (cornerOrientation (key g role) j).point (ShortCorners.width (cornerKind (key g role) j))
    (ShortCorners.height (cornerKind (key g role) j)) (p.1.val, p.2.val)
  Envelope.point ((cornerOffset (key g role) j).1 + q.1, (cornerOffset (key g role) j).2 + q.2)

private def phasedEnvelopes (g : GateTileState) : Inventory.Index g → List PhaseEnvelope
  | .inl i =>
    let dx := (geometricOffset g (.inl i)).1
    let dy := (geometricOffset g (.inl i)).2
    Fin.cases
      ((Gates.slots g.core.isAND).map fun s =>
        ⟨s.port, Envelope.point (dx + s.zero.1.val, dy + s.zero.2.val),
          Envelope.point (dx + s.one.1.val, dy + s.one.2.val)⟩)
      (Fin.cases
        [roleEnvelope 0 (fun b => Envelope.placed (westFrame g.core.isAND) 2306 21 dx dy (Envelope.rail 2301 false b))]
        (Fin.cases
          [roleEnvelope 1 (fun b => Envelope.placed northFrame 2306 21 dx dy (Envelope.rail 2301 false b))]
          (fun _ => [roleEnvelope 2 (fun b => Envelope.placed eastFrame 2306 21 dx dy (Envelope.rail 2301 false b))]))) i
  | .inr (.inl ⟨role, .inl j⟩) => [roleEnvelope role (lineEnvelope g role j.val)]
  | .inr (.inl ⟨role, .inr j⟩) =>
      (List.finRange (ShortCorners.count (cornerKind (key g role) j.val))).map fun l =>
        roleEnvelope role (cornerEnvelope g role j.val l)
  | .inr (.inr _) => []

private theorem envelopes_phased (g : GateTileState) (b : Gates.Signals) (i : Inventory.Index g) :
    envelopes (withTarget g b) i = (phasedEnvelopes g i).map (fun r => r.eval b) := by
  rcases i with i | (⟨role,j | j⟩ | role)
  · fin_cases i
    · simp only [envelopes, withTarget, phasedEnvelopes, Fin.mk_zero, Fin.cases_zero, List.map_map]
      apply List.map_congr_left
      intro s _
      cases hb : b.get s.port <;>
        simp [Gates.Slot.position, PhaseEnvelope.eval, hb, geometricOffset]
    all_goals
      simp only [envelopes, withTarget, phasedEnvelopes, Fin.mk_zero, Fin.cases_zero, Fin.cases_succ',
        List.map_cons, List.map_nil, roleEnvelope_eval]
      rfl
  · change [lineEnvelope g role j.val (gateClaim b role)] = _
    simp only [phasedEnvelopes, List.map_cons, List.map_nil, roleEnvelope_eval]
  · change (List.finRange _).map (fun l => cornerEnvelope g role j.val l (gateClaim b role)) = _
    simp only [phasedEnvelopes, List.map_map, Function.comp_def, roleEnvelope_eval]
  · rfl


private def Covers (outer inner : Envelope) : Prop :=
  outer.loX ≤ inner.loX ∧ inner.hiX ≤ outer.hiX ∧
    outer.loY ≤ inner.loY ∧ inner.hiY ≤ outer.hiY

private theorem hull_covers (rs : List Envelope) (r : Envelope) (hr : r ∈ rs) :
    Covers (Envelope.hull rs) r := by
  induction rs with
  | nil => cases hr
  | cons s rs ih =>
    cases rs with
    | nil =>
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
    | cons t rs =>
      rcases List.mem_cons.mp hr with rfl | hr
      · dsimp only [Covers, Envelope.hull, Envelope.join]
        omega
      · have h := ih hr
        dsimp only [Covers, Envelope.hull, Envelope.join] at h ⊢
        omega

private def familySpan (rs : List PhaseEnvelope) : List Envelope :=
  rs.flatMap fun r => [r.zero, r.one]

private theorem eval_mem_span (rs : List PhaseEnvelope) (r : PhaseEnvelope)
    (hr : r ∈ rs) (b : Gates.Signals) : r.eval b ∈ familySpan rs := by
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  cases hb : b.get r.port <;> simp [PhaseEnvelope.eval, hb]

private def familyApart (rs ss : List PhaseEnvelope) : Bool :=
  if (Envelope.hull (familySpan rs)).Apart (Envelope.hull (familySpan ss)) then true
  else rs.all fun r => ss.all fun s => r.apart s

private theorem familyApart_sound (rs ss : List PhaseEnvelope) (hc : familyApart rs ss = true)
    (r s : PhaseEnvelope) (hr : r ∈ rs) (hs : s ∈ ss) (b : Gates.Signals) :
    (r.eval b).Apart (s.eval b) := by
  by_cases hh : (Envelope.hull (familySpan rs)).Apart (Envelope.hull (familySpan ss))
  · have h1 := hull_covers _ _ (eval_mem_span rs r hr b)
    have h2 := hull_covers _ _ (eval_mem_span ss s hs b)
    dsimp only [Covers, Envelope.Apart] at h1 h2 hh ⊢
    omega
  · rw [familyApart, ite_eq_right hh] at hc
    exact PhaseEnvelope.apart_sound r s
      (List.all_eq_true.mp (List.all_eq_true.mp hc r hr) s hs) b

private def noncontact (g : GateTileState) (i j : Inventory.Index g) : Prop :=
  i ≠ j ∧ contact g i j = false ∧ contact g j i = false

private instance (g : GateTileState) (i j : Inventory.Index g) : Decidable (noncontact g i j) := by
  unfold noncontact
  infer_instance

private def contactPair (g : GateTileState) (a b : Inventory.Index g × ℕ) : Bool :=
  if b.2 ≤ a.2 ∨ noncontact g a.1 b.1 then true
  else familyApart (phasedEnvelopes g a.1) (phasedEnvelopes g b.1)

/-- Only unordered seam contacts need local certificates. -/
private def contactsTest (g : GateTileState) : Bool :=
  (indices g).zipIdx.all fun a => (indices g).zipIdx.all fun b => contactPair g a b

private theorem familyApart_envelopes (g : GateTileState) (phase : Gates.Signals) (i j : Inventory.Index g)
    (hf : familyApart (phasedEnvelopes g i) (phasedEnvelopes g j) = true)
    (r s : Envelope) (hr : r ∈ envelopes (withTarget g phase) i) (hs : s ∈ envelopes (withTarget g phase) j) : r.Apart s := by
  rw [envelopes_phased g phase i] at hr
  rw [envelopes_phased g phase j] at hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs
  exact familyApart_sound _ _ hf u v hu hv phase

private theorem apart_symm {r s : Envelope} (h : r.Apart s) : s.Apart r := by
  dsimp only [Envelope.Apart] at *
  omega

private theorem contacts_pair (g : GateTileState) (phase : Gates.Signals) (hc : contactsTest g = true)
    (a b : Inventory.Index g × ℕ) (ha : a ∈ (indices g).zipIdx) (hb : b ∈ (indices g).zipIdx)
    (hne : a.2 ≠ b.2) (r s : Envelope) (hr : r ∈ envelopes (withTarget g phase) a.1) (hs : s ∈ envelopes (withTarget g phase) b.1) :
    r.Apart s := by
  by_cases h : noncontact g a.1 b.1
  · exact inside_apart (envelopes_inside_target g phase a.1 r hr) (envelopes_inside_target g phase b.1 s hs)
      (Inventory.separated g a.1 b.1 h.1 h.2.1)
  · by_cases hab : a.2 < b.2
    · have hf := List.all_eq_true.mp (List.all_eq_true.mp hc a ha) b hb
      have hn : ¬(b.2 ≤ a.2 ∨ noncontact g a.1 b.1) := not_or.mpr ⟨by omega, h⟩
      rw [contactPair, ite_eq_right hn] at hf
      exact familyApart_envelopes g phase a.1 b.1 hf r s hr hs
    · have hf := List.all_eq_true.mp (List.all_eq_true.mp hc b hb) a ha
      have hn : ¬(a.2 ≤ b.2 ∨ noncontact g b.1 a.1) := by
        rintro (hn | hn)
        · omega
        · exact h ⟨Ne.symm hn.1, hn.2.2, hn.2.1⟩
      rw [contactPair, ite_eq_right hn] at hf
      exact apart_symm (familyApart_envelopes g phase b.1 a.1 hf s r hs hr)

set_option backward.isDefEq.respectTransparency false in
private theorem contactsTest_sound (g : GateTileState) (phase : Gates.Signals) (hc : contactsTest g = true) :
    envelopesApart (withTarget g phase) = true := by
  simp only [envelopesApart, indices_target]
  simp only [List.zipIdx_map, List.all_map, Function.comp_def]
  apply List.all_eq_true.mpr
  rintro ⟨i, a⟩ hi
  apply List.all_eq_true.mpr
  rintro ⟨j, b⟩ hj
  dsimp only [Prod.map, id]
  split
  · rfl
  · rename_i hn
    apply List.all_eq_true.mpr
    intro r hr
    apply List.all_eq_true.mpr
    intro s hs
    exact decide_eq_true (contacts_pair g phase hc (i, a) (j, b) hi hj
      (fun h => hn (Or.inl h)) r s hr hs)


set_option maxHeartbeats 0 in
private theorem contacts_checked : ∀ k : Geometry, contactsTest (ofGeometry k) = true := by
  rintro ⟨kind, pattern, rotation, incoming⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals
    rcases incoming with ⟨left, upper, right⟩
    cases left <;> cases upper <;> cases right <;> decide +kernel

theorem envelopesApart_all (g : GateTileState) : envelopesApart g = true := by
  rw [← envelopesApart_geometry g]
  exact contactsTest_sound (ofGeometry (geometry g)) g.core.target (contacts_checked (geometry g))

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
