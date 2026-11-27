/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Divider

/-! End caps two cells from a permanent isolated divider are frozen by the final target. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h P : ℕ} {d : Direction} {s t u : State w h}

/-- An end cap uses a hollow rack cell and stands two cells from a guarded divider. -/
structure CapGuard (P : ℕ) (s : State w h) (divider cap : Cell w h) : Prop where
  /-- The neighboring divider's fixed rack pattern. -/
  dividerGuard : DividerGuard P s divider
  /-- The cap lies two cells north or south of the divider. -/
  gap : ∃ e middle, (e = .north ∨ e = .south) ∧
    Adjacent e divider middle ∧ Adjacent e middle cap
  /-- The rack is hollow opposite the cap. -/
  hole : ∃ e, Adjacent .east cap e ∧ e.1.val = P ∧ e ∉ s.boxes

theorem CapGuard.congr {p q : Cell w h} (hg : CapGuard P s p q)
    (hrack : line .south P t.boxes = line .south P s.boxes) : CapGuard P t p q := by
  refine ⟨hg.dividerGuard.congr hrack, hg.gap, ?_⟩
  obtain ⟨e, he, hx, hem⟩ := hg.hole
  exact ⟨e, he, hx, fun ht => hem ((rack_mem_iff hx hrack).mp ht)⟩

private theorem isolated_empty {p q : Cell w h} {e : Direction}
    (hp : VerticallyIsolated s p) (he : e = .north ∨ e = .south)
    (ha : Adjacent e p q) : q ∉ s.boxes := by
  apply hp.2 q
  rcases he with rfl | rfl
  · exact Or.inl ha
  · exact Or.inr ha

/-- A protected end cap is never a destination of a positive slide. -/
theorem Slide.cap_not_after {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hs : Supported .east P s) (ht : ∀ z ∈ r.boxes, ¬ Boundary z)
    {p q : Cell w h} (hg : CapGuard P s p q) (hps : VerticallyIsolated s p)
    (hp' : VerticallyIsolated (State.mk s.player r.boxes) p) : q ∉ r.after := by
  by_cases hd : d = .east ∨ d = .west
  · obtain ⟨e, he, hx, hem⟩ := hg.hole
    exact r.horizontal_after_not_divider hn hk hd hs ht he hx hem
  · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
    have hpa : p ∉ r.after := by
      intro hpa
      obtain ⟨z, hz, ha⟩ := r.after_neighbor hn ht hpa
      exact isolated_empty hp' hdv ha hz
    have hpb : p ∉ r.before :=
      (Finset.mem_sdiff.mp ((Finset.mem_union.mp hp'.1).resolve_right hpa)).2
    obtain ⟨e, middle, he, hfirst, hsecond⟩ := hg.gap
    have hdpar : d = e ∨ d = e.opposite := by
      rcases hdv with rfl | rfl <;> rcases he with rfl | rfl <;>
        simp [Direction.opposite]
    intro hqa
    rcases hdpar with rfl | hdrev
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hqa
      have hqpos := r.position ⟨k + i.val + 1, by omega⟩
      have hqlane := r.lane ⟨k + i.val + 1, by omega⟩
      rw [hi] at hqpos hqlane
      have hsource := r.occupied i
      have hspos := r.position ⟨i.val + 1, by omega⟩
      have hslane := r.lane ⟨i.val + 1, by omega⟩
      have hfirstp := hfirst.position
      have hfirstl := hfirst.lane
      have hsecondp := hsecond.position
      have hsecondl := hsecond.lane
      dsimp only at hqpos hspos
      have hneq : d.position (r.cell ⟨i.val + 1, by omega⟩) ≠ d.position middle := by
        intro heq
        have hcell : r.cell ⟨i.val + 1, by omega⟩ = middle := by
          apply d.cell_ext
          · exact hslane.trans (hqlane.symm.trans hsecondl)
          · exact heq
        exact isolated_empty hps he hfirst (hcell ▸ hsource)
      apply hpb
      apply r.before_of_between hps.1
      · exact hfirstl.symm.trans (hsecondl.symm.trans hqlane)
      · omega
      · omega
    · obtain ⟨z, hz, ha⟩ := r.after_neighbor hn ht hqa
      rw [hdrev] at ha
      have hzm : z = middle := ha.functional hsecond.reverse
      exact isolated_empty hp' he hfirst (hzm ▸ hz)

/-- A slide cannot newly occupy an end cap while preserving its divider and forbidden gap. -/
private theorem Move.cap_source (hm : Move d s t) (hs : Supported .east P s) (ht : Interior t)
    (hrack : line .south P t.boxes = line .south P s.boxes)
    {p q : Cell w h} (hg : CapGuard P s p q) (hp : VerticallyIsolated t p)
    (hq : q ∈ t.boxes) : q ∈ s.boxes := by
  have hps := hm.divider_isolated_source hs ht hrack hg.dividerGuard hp
  cases hm with
  | walk _ _ _ hb => exact hb ▸ hq
  | @push n k hv hn hk r _ hb =>
    have hti : ∀ z ∈ r.boxes, ¬ Boundary z := by simpa only [Interior, hb] using ht
    have hq' : q ∈ r.boxes := hb ▸ hq
    have hp' : VerticallyIsolated (State.mk t.player r.boxes) p := by
      simpa only [VerticallyIsolated, hb] using hp
    have hp'' : VerticallyIsolated (State.mk s.player r.boxes) p := hp'
    have hqa := r.cap_not_after hn hk hs hti hg hps hp''
    exact (Finset.mem_sdiff.mp ((Finset.mem_union.mp hq').resolve_right hqa)).1

/-- The exact final cap target forces the cap to have stayed occupied from the start. -/
private theorem Reachable.cap_source (hr : Reachable s t) (hs : Supported .east P s)
    (ht : Interior t)
    (hrack : line .south P t.boxes = line .south P s.boxes)
    {p q : Cell w h} (hg : CapGuard P s p q) (hp : VerticallyIsolated t p)
    (hq : q ∈ t.boxes) : q ∈ s.boxes := by
  induction hr with
  | refl => exact hq
  | @tail v t hr hm ih =>
    have hv := hm.choose_spec.interior_source ht
    have hvrack := Reachable.rack_frozen hr (Relation.ReflTransGen.single hm) hs ht hrack
    have hvs := Reachable.supported hr hv hs
    have hvg := hg.congr hvrack
    have hvp := hm.choose_spec.divider_isolated_source hvs ht (hrack.trans hvrack.symm)
      hvg.dividerGuard hp
    have hvq := hm.choose_spec.cap_source hvs ht (hrack.trans hvrack.symm) hvg hp hq
    exact ih hv hvrack hvp hvq

/-- Every intermediate state keeps a required cap on its original cell. -/
theorem Reachable.cap_frozen (hprefix : Reachable s u) (hsuffix : Reachable u t)
    (hs : Supported .east P s) (ht : Interior t)
    (hrack : line .south P t.boxes = line .south P s.boxes)
    {p q : Cell w h} (hg : CapGuard P s p q) (hp : VerticallyIsolated t p)
    (hq : q ∈ t.boxes) : q ∈ u.boxes := by
  have hu := hsuffix.interior_source ht
  have hurack := hprefix.rack_frozen hsuffix hs ht hrack
  exact hsuffix.cap_source (hprefix.supported hu hs) ht (hrack.trans hurack.symm)
    (hg.congr hurack) hp hq

end PushPuzzle.PushPush
