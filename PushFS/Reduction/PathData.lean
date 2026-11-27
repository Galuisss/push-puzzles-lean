/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerRoutes

/-!
# Endpoint certificates for emitted route data

`Connects` states that a finite segment list is the exact serialization of an
orthogonal path. Concatenation and translation preserve both endpoints and
the complete trace. Every computed routing-band curve has this certificate.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open NCL.GridRouting

/-- A segment program with its exact source and target endpoints. -/
def Connects (ss : List Segment) (p q : Point) : Prop :=
  ∃ r : NCL.GridRouting.Path p q, segments r = ss

/-- A single horizontal instruction joins its two stated endpoints. -/
theorem Connects.horizontal (x x' y : ℕ) :
    Connects [⟨(x, y), (x', y)⟩] (x, y) (x', y) :=
  ⟨NCL.GridRouting.Path.horizontal x x' y, rfl⟩

/-- A single downward instruction joins its two stated endpoints. -/
theorem Connects.vertical (x y y' : ℕ) (h : y ≤ y') :
    Connects [⟨(x, y), (x, y')⟩] (x, y) (x, y') :=
  ⟨NCL.GridRouting.Path.vertical x y y' h, rfl⟩

/-- Join two actual finite segment programs at their common endpoint. -/
theorem Connects.append {ss tt : List Segment} {p q r : Point}
    (hs : Connects ss p q) (ht : Connects tt q r) : Connects (ss ++ tt) p r := by
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨t, rfl⟩ := ht
  exact ⟨s.comp t, rfl⟩

/-- Translate a serialized route and its two endpoints together. -/
theorem Connects.translate {ss : List Segment} {p q : Point}
    (hs : Connects ss p q) (dx dy : ℕ) :
    Connects (ss.map (fun s => s.translate dx dy))
      (p.1 + dx, p.2 + dy) (q.1 + dx, q.2 + dy) := by
  obtain ⟨s, rfl⟩ := hs
  exact ⟨s.translate dx dy, segments_translate s dx dy⟩

/-- Every serialized grid point stays between the actual endpoint rows. -/
theorem Connects.row_bounds {ss : List Segment} {p q u : Point} (hs : Connects ss p q)
    (hu : ∃ s ∈ ss, s.Contains u) : p.2 ≤ u.2 ∧ u.2 ≤ q.2 := by
  obtain ⟨r, rfl⟩ := hs
  exact r.row_bounds ((mem_segments_iff r u).mp hu)

/-- The explicit six-segment program, with dependent endpoint types. -/
def Band.path (b : Band) (i : Fin b.source.length) :
    NCL.GridRouting.Path (b.source.getD i.val 0, 0)
      (b.target.getD i.val 0, 2 * (b.source.length + 1)) :=
  let n := b.source.length
  let s := b.source.getD i.val 0
  let t := b.target.getD i.val 0
  let mid := (b.source ++ b.target).sum + i.val + 1
  (NCL.GridRouting.Path.vertical s 0 (n - i.val) (by omega)).comp
    ((NCL.GridRouting.Path.horizontal s mid (n - i.val)).comp
      ((NCL.GridRouting.Path.vertical mid (n - i.val) (n + 1) (by omega)).comp
        ((NCL.GridRouting.Path.vertical mid (n + 1) (i.val + 1 + (n + 1)) (by omega)).comp
          ((NCL.GridRouting.Path.horizontal mid t (i.val + 1 + (n + 1))).comp
            (NCL.GridRouting.Path.vertical t (i.val + 1 + (n + 1)) (2 * (n + 1)) (by
              have := i.isLt
              omega))))))

/-- All six emitted segments agree exactly with this endpoint-typed path. -/
private theorem Band.segments_path (b : Band) (i : Fin b.source.length) :
    segments (b.path i) = Band.curve (b, i.val) := by
  simp [Band.path, Band.curve, segments, two_mul, Nat.add_assoc]

/-- Every computed route in a band joins its declared standard boundaries. -/
private theorem Band.curve_connects (b : Band) (i : Fin b.source.length) :
    Connects (Band.curve (b, i.val)) (b.source.getD i.val 0, 0)
      (b.target.getD i.val 0, 2 * (b.source.length + 1)) :=
  ⟨b.path i, b.segments_path i⟩

namespace Plan

/-- The upper program joins its real standard port to the expanded input column. -/
theorem Layer.upper_connects (l : Layer) (i : Fin l.before.wires.length) :
    Connects (Band.curve (l.upperBand, i.val)) (4 * i.val, 0)
      (expanded l.instruction.data.offset l.instruction.data.inputs.length i.val, l.middleY) := by
  have hlen : l.upperBand.source.length = l.before.wires.length := by simp [Layer.upperBand]
  have hc := l.upperBand.curve_connects ⟨i.val, by rw [hlen]; exact i.isLt⟩
  simpa [Layer.upperBand, Layer.middleY, List.getD_eq_getElem?_getD, i.isLt] using hc

/-- The lower program joins the expanded output column to its real standard port. -/
theorem Layer.lower_connects (l : Layer) (i : Fin l.after.wires.length) :
    Connects ((Band.curve (l.lowerBand, i.val)).map (fun s => s.translate 0 (l.middleY + 2)))
      (expanded l.instruction.data.offset l.instruction.data.outputs.length i.val, l.middleY + 2)
      (4 * i.val, l.height) := by
  have hlen : l.lowerBand.source.length = l.after.wires.length := by simp [Layer.lowerBand]
  have hc := (l.lowerBand.curve_connects ⟨i.val, by rw [hlen]; exact i.isLt⟩).translate 0 (l.middleY + 2)
  simpa [Layer.lowerBand, Layer.middleY, Layer.height, List.getD_eq_getElem?_getD,
    i.isLt, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc

end Plan
end PushPuzzle.PushFS.Reduction
