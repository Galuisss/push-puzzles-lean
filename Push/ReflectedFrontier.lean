/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.StripFrontier
public import PushFS.Isometry
public import Push.FirstExit

/-! The strip budget reflected vertically bounds attempts to return to the source from below. -/

@[expose] public section
namespace PushPuzzle.Push.ReflectedFrontier

open PushFS PushS StripFrontier

variable {w h : ℕ}

def mirror (s : State w h) : State w h := (GridIsometry.reflectY w h).state s

private theorem mirror_cell (q : Cell w h) : (GridIsometry.reflectY w h).cells q =
    (q.1, q.2.rev) := rfl

@[simp] theorem mirror_x (s : State w h) : (mirror s).player.1.val = s.player.1.val := rfl

@[simp] theorem mirror_y (s : State w h) : (mirror s).player.2.val = h - 1 - s.player.2.val := by
  change (s.player.2.rev).val = _
  dsimp [Fin.rev]
  omega

private theorem mirror_holes (s : State w h) :
    holes (mirror s) = (holes s).map (GridIsometry.reflectY w h).cells.toEmbedding := by
  ext p
  obtain ⟨q, rfl⟩ := (GridIsometry.reflectY w h).cells.surjective p
  simp only [mirror, mem_holes, GridIsometry.mem_boxes]
  simp

/-- Holes in the source rows of a western strip. -/
def source (cut height : ℕ) (s : State w h) : Finset (Cell w h) :=
  (holes s).filter fun q => q.1.val < cut ∧ q.2.val < height

private theorem south_mirror {height : ℕ} (hheight : height ≤ h) (cut : ℕ) (s : State w h) :
    south cut (h - height) (mirror s) =
      (source cut height s).map (GridIsometry.reflectY w h).cells.toEmbedding := by
  rw [south, mirror_holes, Finset.filter_map]
  congr 1
  ext q
  simp only [source, Finset.mem_filter]
  have hq := q.2.isLt
  change (q ∈ holes s ∧ (q.1.val < cut ∧ h - height ≤ (q.2.rev).val)) ↔
    q ∈ holes s ∧ (q.1.val < cut ∧ q.2.val < height)
  dsimp [Fin.rev]
  have heq : h - height ≤ h - (q.2.val + 1) ↔ q.2.val < height := by omega
  rw [heq]

private theorem south_mirror_card {height : ℕ} (hheight : height ≤ h) (cut : ℕ) (s : State w h) :
    (south cut (h - height) (mirror s)).card = (source cut height s).card := by
  rw [south_mirror hheight, Finset.card_map]

/-- Avoiding the source is the reflected northern-player condition. -/
private theorem north_mirror {height : ℕ} (hheight : height ≤ h) (cut : ℕ) (s : State w h) :
    North cut (h - height) (mirror s) ↔ (s.player.1.val < cut → height ≤ s.player.2.val) := by
  unfold North
  rw [mirror_x, mirror_y]
  have := s.player.2.isLt
  omega

/-- A gap in the real buffer is exactly a split frontier in the vertically reflected board. -/
private theorem split_mirror {cut height level : ℕ} (hheight : height ≤ h) (hlevel : level < h)
    {s : State w h}
    (hs : ∀ q ∈ holes s, q.1.val < cut → q.2.val < height ∨ level ≤ q.2.val) :
    Split cut (h - height) (h - 1 - level) (mirror s) := by
  intro p hp hx
  obtain ⟨q, rfl⟩ := (GridIsometry.reflectY w h).cells.surjective p
  have hq : q ∈ holes s := by
    simpa only [mem_holes, mirror, GridIsometry.mem_boxes] using hp
  have hqx : q.1.val < cut := hx
  have hqs := hs q hq hqx
  rw [mirror_cell]
  change (q.2.rev).val ≤ h - 1 - level ∨ h - height ≤ (q.2.rev).val
  have := q.2.isLt
  dsimp [Fin.rev]
  omega

/-- A source-avoiding real prefix transports to the existing strip-budget relation. -/
private theorem mirror_prefix {B : Board w h} {cap : Option ℕ} {s t : State w h} {cut height : ℕ}
    (hheight : height ≤ h)
    (hr : Relation.ReflTransGen (fun a b => Step B cap a b ∧
      (b.player.1.val < cut → height ≤ b.player.2.val)) s t) :
    Relation.ReflTransGen (NorthStep ((GridIsometry.reflectY w h).board B) cap cut (h - height))
      (mirror s) (mirror t) := by
  apply hr.lift mirror
  intro a b hm
  exact ⟨⟨(GridIsometry.reflectY w h).directions hm.1.choose,
    (GridIsometry.reflectY w h).move hm.1.choose_spec⟩, (north_mirror hheight cut b).mpr hm.2⟩

/-- A separated southern reader cannot reach source rows behind a permanently occupied side boundary. -/
theorem no_source_return {B : Board w h} {cap : Option ℕ} {s t : State w h}
    {cut height level : ℕ} (hheight : height ≤ h) (hlevel : level < h)
    (hsvalid : s.Valid B)
    (hsplit : ∀ q ∈ holes s, q.1.val < cut → q.2.val < height ∨ level ≤ q.2.val)
    (hsOutside : s.player.1.val < cut → height ≤ s.player.2.val)
    (hgap : height + (source cut height s).card < level)
    (hboundary : ∀ u, Reachable B cap s u → ∀ p : Cell w h,
      p.1.val = cut → p.2.val < height → p ∈ u.boxes)
    (hr : Reachable B cap s t) : t.player.1.val < cut → height ≤ t.player.2.val := by
  classical
  by_contra ht
  obtain ⟨u, v, hsu, hu, huv, hv, hvf⟩ := Path.first_exit
    (P := fun u : State w h => u.player.1.val < cut → height ≤ u.player.2.val) hr hsOutside ht
  have hvIn : v.player.1.val < cut ∧ v.player.2.val < height := by
    by_contra h
    apply hv
    intro hx
    omega
  have hmirror := mirror_prefix hheight hsu
  obtain ⟨f, huSplit, huNorth, _, hb⟩ := reachable_budget hmirror
    (split_mirror hheight hlevel hsplit) ((north_mirror hheight cut s).mpr hsOutside)
  rw [south_mirror_card hheight cut s] at hb
  have hgap' : f + 1 < h - height := by omega
  let e := GridIsometry.reflectY w h
  have hm := e.move huv.choose_spec
  have hvx : (mirror v).player.1.val < cut := hvIn.1
  have hvy : h - height ≤ (mirror v).player.2.val := by
    rw [mirror_y]
    have := v.player.2.isLt
    omega
  obtain ⟨hd, hux, _⟩ := enter_west hm huSplit huNorth hgap' hvx hvy
  have ha := players_adjacent hm
  rw [hd] at ha
  have hupy : u.player.2.val < height := by
    have hay := congrArg Fin.val ha.2
    change (mirror v).player.2.val = (mirror u).player.2.val at hay
    rw [mirror_y, mirror_y] at hay
    have hyu := u.player.2.isLt
    have hyv := v.player.2.isLt
    omega
  have hsu' : Reachable B cap s u :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hsu
  exact (Reachable.valid hsu' hsvalid).2.2 (hboundary u hsu' u.player hux hupy)

end PushPuzzle.Push.ReflectedFrontier
