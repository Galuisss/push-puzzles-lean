/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardStock

/-! One actual travelling-signal slide, preserving every original door register. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

theorem boxes_at_signal (storage : Bool) (S : Stock I)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hsignal : S.signal = (p.1.val, p.2.val)) :
    S.boxes storage = insert p (S.stationary storage) := by
  have hx : S.signal.1 < (layout storage I).width := by rw [hsignal]; exact p.1.isLt
  have hy : S.signal.2 < (layout storage I).height := by rw [hsignal]; exact p.2.isLt
  rw [S.boxes_eq_insert_signal storage hx hy]
  congr 1
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst hsignal
  · exact congrArg Prod.snd hsignal

/-- Move the unique signal to its next stopped location and return the player to the corner. -/
theorem slide_signal (storage : Bool) (S : Stock I) (d : Direction)
    (source dest stop support : Cell (layout storage I).width (layout storage I).height)
    (hsignal : S.signal = (source.1.val, source.2.val))
    (hsourcecol : source.1.val ∈ (layout storage I).columns)
    (hdestcol : dest.1.val ∈ (layout storage I).columns)
    (hsourcey : 0 < source.2.val) (hdesty : 0 < dest.2.val)
    (hsource : source ∉ S.stationary storage)
    (hsupport : support ∉ insert source (S.stationary storage))
    (hfirst : Adjacent d support source) (hlane : d.lane dest = d.lane source)
    (hforward : d.position source < d.position dest)
    (hclear : ∀ p : Cell (layout storage I).width (layout storage I).height,
      d.lane p = d.lane source → d.position source < d.position p →
      d.position p ≤ d.position dest → p ∉ S.stationary storage)
    (hstop : Adjacent d dest stop) (hstop_mem : stop ∈ S.stationary storage) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := (dest.1.val, dest.2.val)} : Stock I).canonical storage) := by
  have hr := (layout storage I).slide_from_corner (S.stationary storage) d source dest stop support
    (fun _ hp => S.stationary_columns storage hp) (fun _ hp => S.stationary_top storage hp)
    hsourcecol hdestcol hsourcey hdesty hsource hsupport hfirst hlane hforward hclear hstop hstop_mem
  change Finite.Reachable 1 ⟨(layout storage I).corner, S.boxes storage⟩
    ⟨(layout storage I).corner, ({S with signal := (dest.1.val, dest.2.val)} : Stock I).boxes storage⟩
  rw [S.boxes_at_signal storage source hsignal,
    boxes_at_signal storage ({S with signal := (dest.1.val, dest.2.val)} : Stock I) dest rfl]
  exact hr

end PushPuzzle.PushPush.Doors.Source.Stock
