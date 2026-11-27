/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineStrips

/-! Exact label-indexed threshold transmission through every concrete routing atom. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Readout

open PushFS PushFS.Gadgets.Wires.Soundness
open FiniteTools (radius paritySpan)

def endpointLabel (w : ℕ) (a : Atom) (post : List Atom) : Label w (a::post) :=
  tailLabel w [a] post (cutFirstLabel w post)

def headAt (w : ℕ) (pre post : List Atom) (a : Atom) : Label w (pre++a::post) :=
  tailLabel w pre (a::post) (cutFirstLabel w (a::post))

def endAt (w : ℕ) (pre post : List Atom) (a : Atom) : Label w (pre++a::post) :=
  tailLabel w pre (a::post) (endpointLabel w a post)

def middleAt (w : ℕ) (pre post : List Atom) : Label w (pre++ .flip::post) :=
  tailLabel w pre (.flip::post) (Tool.Flip.headLabel w post 1)

private theorem endpoint_position (w : ℕ) (a : Atom) (post : List Atom) (q : Bool) :
    position w (a::post) q (endpointLabel w a post) = a.span w+q.toNat := by
  have hh := tail_position w [a] post q (cutFirstLabel w post)
  simp only [List.singleton_append] at hh
  simpa only [endpointLabel, position_first, span_cons, span_nil, Nat.add_zero] using hh

private theorem headAt_position (w : ℕ) (pre post : List Atom) (a : Atom) (q : Bool) :
    position w (pre++a::post) q (headAt w pre post a) = span w pre+q.toNat := by
  rw [headAt, tail_position, position_first]

private theorem endAt_position (w : ℕ) (pre post : List Atom) (a : Atom) (q : Bool) :
    position w (pre++a::post) q (endAt w pre post a) = span w pre+a.span w+q.toNat := by
  rw [endAt, tail_position, endpoint_position]
  omega

private theorem middleAt_position (w : ℕ) (pre post : List Atom) (q : Bool) :
    position w (pre++ .flip::post) q (middleAt w pre post) = span w pre+w+3*q.toNat := by
  rw [middleAt, tail_position, Tool.Flip.head_position]
  simp [Nat.add_assoc]

theorem headAt_val (w : ℕ) (pre post : List Atom) (a : Atom) :
    (headAt w pre post a).val = ownedCount w pre := by simp [headAt, tailLabel, cutFirstLabel]

theorem endAt_val (w : ℕ) (pre post : List Atom) (a : Atom) :
    (endAt w pre post a).val = ownedCount w pre+ownedCount w [a] := by
  simp [endAt, endpointLabel, tailLabel, cutFirstLabel]

private theorem middleAt_val (w : ℕ) (pre post : List Atom) :
    (middleAt w pre post).val = ownedCount w pre+1 := rfl

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]
    {M : SlotMatching I GlobalLabel} {A : ComponentTracks I} {w : ℕ} {above : Bool}
    {S final : LabelledState GlobalLabel I.width I.height}

namespace LineGlyph

theorem stock_signal (pre post : List Atom) (n : ℕ)
    (g : LineGlyph M A w (pre++ .line n::post) above)
    (h : Successful M S final) (cert : Certificate I)
    (hin : g.High S (headAt w pre post (.line n))) : g.High S (endAt w pre post (.line n)) := by
  have hg := g.gap_span h cert (headAt w pre post (.line n)) (endAt w pre post (.line n))
    (by rw [headAt_val, endAt_val]; simp)
  simp only [headAt_val, endAt_val, ownedCount_line, Nat.add_sub_cancel_left] at hg
  dsimp [High] at hin ⊢
  rw [headAt_position] at hin
  rw [endAt_position]
  dsimp [Atom.span] at *
  omega

theorem flip_signal (pre post : List Atom)
    (g : LineGlyph M A w (pre++ .flip::post) above)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.High S (headAt w pre post .flip)) : g.High S (endAt w pre post .flip) := by
  have hs := flip_strips w g.hw pre post above
  have hleft := g.strip_walls (by have := g.hw; omega) (by
    unfold width
    simp only [span_append, span_cons, Atom.span]
    unfold radius; omega) hs.1
  have hright := g.strip_walls (by have := g.hw; omega) (by
    unfold width
    simp only [span_append, span_cons, Atom.span]
    unfold radius; omega) hs.2
  have hl := h.strip_good_component cert ho A _ _ _ (g.labels (headAt w pre post .flip)) (g.labels (middleAt w pre post))
    hleft (g.tracks _) (g.tracks _) (g.source_order _ _ (by rw [headAt_val,middleAt_val]; omega))
    (by
      rw [g.sources,g.sources]
      change g.dx+(radius w+position w _ g.initialPhase (headAt w pre post .flip))+1 < _ ∨ _ <
        g.dx+(radius w+position w _ g.initialPhase (middleAt w pre post))
      rw [headAt_position,middleAt_position]
      cases g.initialPhase <;> simp <;> omega)
    (by
      rw [g.targets,g.targets]
      change g.dx+(radius w+position w _ g.targetPhase (headAt w pre post .flip))+1 < _ ∨ _ <
        g.dx+(radius w+position w _ g.targetPhase (middleAt w pre post))
      rw [headAt_position,middleAt_position]
      cases g.targetPhase <;> simp <;> omega)
  have hr := h.strip_good_component cert ho A _ _ _ (g.labels (middleAt w pre post)) (g.labels (endAt w pre post .flip))
    hright (g.tracks _) (g.tracks _) (g.source_order _ _ (by rw [middleAt_val,endAt_val,ownedCount_flip]; omega))
    (by
      rw [g.sources,g.sources]
      change g.dx+(radius w+position w _ g.initialPhase (middleAt w pre post))+1 < _ ∨ _ <
        g.dx+(radius w+position w _ g.initialPhase (endAt w pre post .flip))
      rw [middleAt_position,endAt_position]
      cases g.initialPhase <;> simp [Atom.span] <;> omega)
    (by
      rw [g.targets,g.targets]
      change g.dx+(radius w+position w _ g.targetPhase (middleAt w pre post))+1 < _ ∨ _ <
        g.dx+(radius w+position w _ g.targetPhase (endAt w pre post .flip))
      rw [middleAt_position,endAt_position]
      cases g.targetPhase <;> simp [Atom.span] <;> omega)
  simp only [Good, pair] at hl hr
  dsimp [High] at hin ⊢
  rw [headAt_position] at hin
  rw [endAt_position]
  dsimp [Atom.span] at *
  omega

theorem parity_signal (pre post : List Atom)
    (g : LineGlyph M A w (pre++ .parity::post) above)
    (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.High S (headAt w pre post .parity)) : g.High S (endAt w pre post .parity) := by
  have hm := FiniteTools.paritySpan_bounds w
  have hs := g.strip_walls (by omega) (by
    unfold width
    simp only [span_append, span_cons, Atom.span]
    unfold radius; omega) (parity_strip w g.hw pre post above)
  have hg := h.strip_good_component cert ho A _ _ _ (g.labels (headAt w pre post .parity)) (g.labels (endAt w pre post .parity))
    hs (g.tracks _) (g.tracks _) (g.source_order _ _ (by rw [headAt_val,endAt_val,ownedCount_parity]; omega))
    (by
      rw [g.sources,g.sources]
      change g.dx+(radius w+position w _ g.initialPhase (headAt w pre post .parity))+1 < _ ∨ _ <
        g.dx+(radius w+position w _ g.initialPhase (endAt w pre post .parity))
      rw [headAt_position,endAt_position]
      cases g.initialPhase <;> simp [Atom.span] <;> omega)
    (by
      rw [g.targets,g.targets]
      change g.dx+(radius w+position w _ g.targetPhase (headAt w pre post .parity))+1 < _ ∨ _ <
        g.dx+(radius w+position w _ g.targetPhase (endAt w pre post .parity))
      rw [headAt_position,endAt_position]
      cases g.targetPhase <;> simp [Atom.span] <;> omega)
  simp only [Good, pair] at hg
  dsimp [High] at hin ⊢
  rw [headAt_position] at hin
  rw [endAt_position]
  dsimp [Atom.span] at *
  omega

end LineGlyph
end PushPuzzle.PushS.FiniteRouting.Line.Readout
