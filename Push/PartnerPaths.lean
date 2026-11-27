/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerEar

/-! The literal ear subdivision preserves all old WIRE connectivity in both directions. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

/-- Travel through one actual upper arc or lower WIRE, retaining its endpoint identities. -/
inductive WireAdjacent (l : PortLayout) : ℕ → ℕ → Prop
  | upper {a b} : (a, b) ∈ l.upperPairs → WireAdjacent l a b
  | upper_rev {a b} : (a, b) ∈ l.upperPairs → WireAdjacent l b a
  | lower {a b} : LowerGroup.wire a b ∈ l.lowerGroups → WireAdjacent l a b
  | lower_rev {a b} : LowerGroup.wire a b ∈ l.lowerGroups → WireAdjacent l b a

abbrev WireConnected (l : PortLayout) := Relation.ReflTransGen (WireAdjacent l)

private theorem WireAdjacent.symm {l : PortLayout} {a b : ℕ} (h : WireAdjacent l a b) :
    WireAdjacent l b a := by
  cases h with
  | upper h => exact .upper_rev h
  | upper_rev h => exact .upper h
  | lower h => exact .lower_rev h
  | lower_rev h => exact .lower h

theorem WireConnected.symm {l : PortLayout} {a b : ℕ} (h : WireConnected l a b) :
    WireConnected l b a := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact (Relation.ReflTransGen.single hab.symm).trans ih

private theorem adjacent_sortPair {l : PortLayout} {a b : ℕ}
    (hp : sortPair a b ∈ l.upperPairs) : WireAdjacent l a b := by
  by_cases h : a ≤ b
  · exact .upper (by simpa only [sortPair, min_eq_left h, max_eq_right h] using hp)
  · have hle : b ≤ a := by omega
    exact .upper_rev (by simpa only [sortPair, min_eq_right hle, max_eq_left hle] using hp)

/-- The two replacement arcs and the new WIRE form the original edge's explicit three-step path. -/
private theorem ear_path (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) :
    WireConnected (ear l cut ab) (shift cut ab.1) (shift cut ab.2) := by
  have ha : WireAdjacent (ear l cut ab) (shift cut ab.1) (cut + 1) :=
    adjacent_sortPair List.mem_cons_self
  have hb : WireAdjacent (ear l cut ab) (shift cut ab.2) cut :=
    adjacent_sortPair (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ((Relation.ReflTransGen.single ha).tail
    (WireAdjacent.lower_rev (ear_wire_mem l cut ab))).tail hb.symm

private theorem ear_upper_path {l : PortLayout} {cut : ℕ} {ab xy : ℕ × ℕ}
    (hp : xy ∈ l.upperPairs) :
    WireConnected (ear l cut ab) (shift cut xy.1) (shift cut xy.2) := by
  by_cases he : xy = ab
  · subst xy
    exact ear_path l cut ab
  · apply Relation.ReflTransGen.single
    apply WireAdjacent.upper
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨xy, (List.mem_erase_of_ne he).mpr hp, rfl⟩

/-- Every actual old WIRE step lifts through the concrete ear. -/
private theorem ear_adjacent_lift {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} {a b : ℕ}
    (h : WireAdjacent l a b) :
    WireConnected (ear l cut ab) (shift cut a) (shift cut b) := by
  cases h with
  | upper hp => exact ear_upper_path hp
  | upper_rev hp => exact (ear_upper_path hp).symm
  | lower hp => exact .single (.lower (mapGroup_mem_ear hp))
  | lower_rev hp => exact .single (.lower_rev (mapGroup_mem_ear hp))

private theorem ear_connected_lift {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} {a b : ℕ}
    (h : WireConnected l a b) :
    WireConnected (ear l cut ab) (shift cut a) (shift cut b) := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.trans (ear_adjacent_lift hab)

/-- Contract the two fresh ports back onto their original edge's endpoints. -/
def collapse (cut : ℕ) (ab : ℕ × ℕ) (i : ℕ) : ℕ :=
  if i = cut then ab.2 else if i = cut + 1 then ab.1 else if i < cut then i else i - 2

private theorem collapse_shift (cut : ℕ) (ab : ℕ × ℕ) (i : ℕ) : collapse cut ab
    (shift cut i) = i := by
  simp only [collapse, ite_eq_right (shift_ne_cut cut i), ite_eq_right (shift_ne_cut_succ cut i)]
  unfold shift
  split_ifs <;> omega

@[simp] theorem collapse_cut (cut : ℕ) (ab : ℕ × ℕ) : collapse cut ab cut = ab.2 := by
  simp only [collapse, ite_true]

@[simp] theorem collapse_cut_succ (cut : ℕ) (ab : ℕ × ℕ) : collapse cut ab (cut + 1) = ab.1 := by
  simp only [collapse, show cut + 1 ≠ cut by omega, ite_false, ite_true]

private theorem collapse_sortPair {f : ℕ → ℕ} {a b : ℕ} (hf : f a = f b) :
    f (sortPair a b).1 = f (sortPair a b).2 := by
  by_cases h : a ≤ b
  · simpa only [sortPair, min_eq_left h, max_eq_right h] using hf
  · simpa only [sortPair, min_eq_right (by omega : b ≤ a), max_eq_left (by omega : b ≤ a)] using hf.symm

private theorem ear_upper_project {l : PortLayout} {cut : ℕ} {ab xy : ℕ × ℕ}
    (hp : xy ∈ (ear l cut ab).upperPairs) :
    WireConnected l (collapse cut ab xy.1) (collapse cut ab xy.2) := by
  simp only [ear, List.mem_cons] at hp
  rcases hp with rfl | rfl | hp
  · have he := collapse_sortPair (f := collapse cut ab)
      ((collapse_shift cut ab ab.1).trans (collapse_cut_succ cut ab).symm)
    rw [he]
  · have he := collapse_sortPair (f := collapse cut ab)
      ((collapse_shift cut ab ab.2).trans (collapse_cut cut ab).symm)
    rw [he]
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
    simp only [mapPair, collapse_shift]
    exact .single (.upper (List.mem_of_mem_erase hold))

private theorem ear_lower_project {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} {a b : ℕ}
    (hab : ab ∈ l.upperPairs) (hp : LowerGroup.wire a b ∈ (ear l cut ab).lowerGroups) :
    WireConnected l (collapse cut ab a) (collapse cut ab b) := by
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨old, hold, he⟩ := List.mem_map.mp hp
    cases old with
    | gate kind first => cases he
    | wire x y =>
      simp only [mapGroup, LowerGroup.wire.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      simp only [collapse_shift]
      exact .single (.lower hold)
  · have he := List.mem_singleton.mp hp
    cases he
    simp only [collapse_cut, collapse_cut_succ]
    exact .single (.upper_rev hab)

/-- Every new actual WIRE step contracts to a path on the old layout. -/
private theorem ear_adjacent_project {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} {a b : ℕ}
    (hab : ab ∈ l.upperPairs) (h : WireAdjacent (ear l cut ab) a b) :
    WireConnected l (collapse cut ab a) (collapse cut ab b) := by
  cases h with
  | upper hp => exact ear_upper_project hp
  | upper_rev hp => exact (ear_upper_project hp).symm
  | lower hp => exact ear_lower_project hab hp
  | lower_rev hp => exact (ear_lower_project hab hp).symm

/-- The ear introduces exactly a subdivision and preserves connectivity of every original port pair. -/
theorem ear_connected_iff {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} (hab : ab ∈ l.upperPairs)
    (a b : ℕ) :
    WireConnected (ear l cut ab) (shift cut a) (shift cut b) ↔ WireConnected l a b := by
  constructor
  · intro hr
    have hp : ∀ {x y}, WireConnected (ear l cut ab) x y →
        WireConnected l (collapse cut ab x) (collapse cut ab y) := by
      intro x y hr
      induction hr with
      | refl => exact .refl
      | tail _ h ih => exact ih.trans (ear_adjacent_project hab h)
    simpa only [collapse_shift] using hp hr
  · exact ear_connected_lift

end PushPuzzle.Push.Partner
