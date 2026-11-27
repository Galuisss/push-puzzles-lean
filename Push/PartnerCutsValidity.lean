/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsInventory
import all Push.PartnerValidity
import all Push.PartnerInventory

/-! Lower-page noncrossing and indexed validity of the actual common-cut compiler. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS PageLevels

private theorem mapGroup_left (cut count : ℕ) (g : LowerGroup) :
    (mapGroup cut count g).shape.left = shift cut count g.shape.left := by cases g <;> rfl

private theorem mapGroup_right {l : PortLayout} {cut count : ℕ} (hs : SafeCut l cut)
    (g : LowerGroup) (hg : g ∈ l.lowerGroups) :
    (mapGroup cut count g).shape.right = shift cut count g.shape.right := by
  cases g with
  | wire a b => rfl
  | gate kind first => exact (shift_gate (count := count) (hs kind first hg)).2.symm

private def mapShape (cut count : ℕ) : Group → Group
  | .wire a b => .wire (shift cut count a) (shift cut count b)
  | .triple a => .triple (shift cut count a)

private theorem mapGroup_shape (cut count : ℕ) (g : LowerGroup) :
    (mapGroup cut count g).shape = mapShape cut count g.shape := by cases g <;> rfl

private theorem compatible_shift {g k g' k' : Group} {cut count : ℕ} (hc : Compatible g k)
    (hgl : g'.left = shift cut count g.left) (hgr : g'.right = shift cut count g.right)
    (hkl : k'.left = shift cut count k.left) (hkr : k'.right = shift cut count k.right) : Compatible g' k' := by
  have hm := shift_strictMono cut count
  rcases hc with h | h | h | h
  · exact Or.inl (hgr ▸ hkl ▸ hm h)
  · exact Or.inr (Or.inl (hkr ▸ hgl ▸ hm h))
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    rcases h with ⟨hl, hr, hs⟩
    refine ⟨hgl ▸ hkl ▸ hm.monotone hl, hkr ▸ hgr ▸ hm.monotone hr, ?_⟩
    rcases hs with h | h
    · exact Or.inl (hgl ▸ hkl ▸ hm h)
    · exact Or.inr (hkr ▸ hgr ▸ hm h)
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    rcases h with ⟨hl, hr, hs⟩
    refine ⟨hkl ▸ hgl ▸ hm.monotone hl, hgr ▸ hkr ▸ hm.monotone hr, ?_⟩
    rcases hs with h | h
    · exact Or.inl (hkl ▸ hgl ▸ hm h)
    · exact Or.inr (hgr ▸ hkr ▸ hm h)

private theorem fresh_group_compatible {g g' : Group} {cut count a b : ℕ}
    (ha : cut ≤ a) (hb : b < cut + 2 * count)
    (hgl : g'.left = shift cut count g.left) (hgr : g'.right = shift cut count g.right) :
    Compatible (.wire a b) g' := by
  unfold Compatible Group.Contains
  rw [hgl, hgr]
  simp only [Group.left, Group.right]
  unfold shift
  split_ifs <;> omega

private theorem lowerPiece_compatible {cut count : ℕ} {p q : (ℕ × ℕ) × ℕ}
    (hp : p.2 < count) (hq : q.2 < count) (hne : (lowerPiece cut count p).shape ≠ (lowerPiece cut count q).shape) :
    Compatible (lowerPiece cut count p).shape (lowerPiece cut count q).shape := by
  have hij : p.2 ≠ q.2 := by
    intro he
    exact hne (by simp only [lowerPiece, he])
  unfold Compatible Group.Contains
  simp only [lowerPiece, LowerGroup.shape, Group.left, Group.right, left, right]
  omega

private theorem compile_lower_word {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) :
    (pageWord (compile l cut).pages.lowerPage).Perm (List.range (compile l cut).portCount) := by
  have hi := compile_inventory (inventory_of_pages hl) cut hc hs
  have he : pageWord (compile l cut).pages.lowerPage = (compile l cut).lowerGroups.flatMap groupPorts := by
    simp only [pageWord, PortLayout.pages, Pages.lowerPage, List.flatMap_map]
    apply List.flatMap_congr
    intro g _
    cases g <;> rfl
  rw [he]
  exact hi.lower

/-- All fresh lower wires are nested within the inserted block and preserve the original lower page. -/
theorem compile_lower_valid {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) : (compile l cut).pages.lowerPage.Valid := by
  apply page_valid_of_word (hw := compile_lower_word hl hc hs)
  · intro g hg
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hg
    rcases List.mem_append.mp hraw with hold | hnew
    · obtain ⟨old, hmem, rfl⟩ := List.mem_map.mp hold
      have hb := page_bound_mem hl.lower (List.mem_map.mpr ⟨old, hmem, rfl⟩)
      rw [mapGroup_left, mapGroup_right hs old hmem]
      exact ⟨shift_strictMono cut _ hb.1, shift_lt cut _ hb.2⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hnew
      have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      have hb := right_bounds (cut := cut) hj
      exact ⟨left_lt_right hj, by change right cut _ p.2 < l.portCount + 2 * _; omega⟩
  · intro g hg k hk hne
    obtain ⟨rawg, hrawg, rfl⟩ := List.mem_map.mp hg
    obtain ⟨rawk, hrawk, rfl⟩ := List.mem_map.mp hk
    rcases List.mem_append.mp hrawg with hg | hg
    · obtain ⟨oldg, holdg, rfl⟩ := List.mem_map.mp hg
      rcases List.mem_append.mp hrawk with hk | hk
      · obtain ⟨oldk, holdk, rfl⟩ := List.mem_map.mp hk
        have he : oldg.shape ≠ oldk.shape := by
          intro he
          exact hne (by rw [mapGroup_shape, mapGroup_shape, he])
        have hcomp := page_compatible_mem hl.lower (List.mem_map.mpr ⟨oldg, holdg, rfl⟩)
          (List.mem_map.mpr ⟨oldk, holdk, rfl⟩) he
        exact compatible_shift hcomp (mapGroup_left cut _ oldg) (mapGroup_right hs oldg holdg)
          (mapGroup_left cut _ oldk) (mapGroup_right hs oldk holdk)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
        have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
        exact (fresh_group_compatible (left_bounds (cut := cut) hj).1
          (right_bounds (cut := cut) hj).2 (mapGroup_left cut _ oldg) (mapGroup_right hs oldg holdg)).symm
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      rcases List.mem_append.mp hrawk with hk | hk
      · obtain ⟨oldk, holdk, rfl⟩ := List.mem_map.mp hk
        exact fresh_group_compatible (left_bounds (cut := cut) hj).1
          (right_bounds (cut := cut) hj).2 (mapGroup_left cut _ oldk) (mapGroup_right hs oldk holdk)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
        have hqj : q.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hq
        exact lowerPiece_compatible hj hqj hne

end PushPuzzle.Push.Partner.Cuts
