/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsValidity
import all Push.PartnerCutsValidity
import all Push.PartnerValidity
import all Push.PartnerInventory
import all Push.PartnerUpperValidity

/-! Left and right upper fragments of the actual common-cut compiler form valid noncrossing pages. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS PageLevels

private def upperShape (cut count : ℕ) (p : (ℕ × ℕ) × ℕ) (leftSide : Bool) : Group :=
  if leftSide then .wire (shift cut count p.1.1) (left cut count p.2)
  else .wire (right cut count p.2) (shift cut count p.1.2)

private theorem zip_payload_eq {xs : List (ℕ × ℕ)} {p q : (ℕ × ℕ) × ℕ}
    (hp : p ∈ xs.zipIdx) (hq : q ∈ xs.zipIdx) (he : p.2 = q.2) : p.1 = q.1 := by
  have hi := List.mem_zipIdx_iff_getElem?.mp hp
  have hj := List.mem_zipIdx_iff_getElem?.mp hq
  rw [he] at hi
  exact Option.some.inj (hi.symm.trans hj)

private theorem active_zip_nested {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {p q : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) (hq : q ∈ (active l cut).zipIdx)
    (hij : p.2 < q.2) : p.1.1 < q.1.1 ∧ q.1.2 < p.1.2 := by
  have hi : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hj : q.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hq
  have hpi := List.fst_eq_of_mem_zipIdx hp
  have hpj := List.fst_eq_of_mem_zipIdx hq
  simp only [Nat.sub_zero] at hpi hpj
  have h := active_nested hl cut (i := ⟨p.2, hi⟩) (j := ⟨q.2, hj⟩) hij
  simpa only [List.get_eq_getElem, ← hpi, ← hpj] using h

private theorem compile_upper_cases (l : PortLayout) (cut : ℕ) (g : Group)
    (hg : g ∈ (compile l cut).pages.upperPage.groups) :
    (∃ p ∈ (active l cut).zipIdx, ∃ side, g = upperShape cut (active l cut).length p side) ∨
      ∃ ab ∈ passive l cut, g = .wire (shift cut (active l cut).length ab.1) (shift cut (active l cut).length ab.2) := by
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hg
  rcases List.mem_append.mp hab with hnew | hold
  · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp hnew
    simp only [upperPiece, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact Or.inl ⟨p, hp, true, rfl⟩
    · exact Or.inl ⟨p, hp, false, rfl⟩
  · obtain ⟨ab, hm, rfl⟩ := List.mem_map.mp hold
    exact Or.inr ⟨ab, hm, rfl⟩

private theorem upperShape_bound {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {p : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) (side : Bool) :
    (upperShape cut (active l cut).length p side).left < (upperShape cut (active l cut).length p side).right ∧
      (upperShape cut (active l cut).length p side).right < l.portCount + 2 * (active l cut).length := by
  obtain ⟨hm, ha, hb⟩ := (mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
  have hbound := page_bound_mem hl.upper (List.mem_map.mpr ⟨p.1, hm, rfl⟩)
  change p.1.1 < p.1.2 ∧ p.1.2 < l.portCount at hbound
  have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hlft := left_bounds (cut := cut) hj
  have hrgt := right_bounds (cut := cut) hj
  cases side <;> simp only [upperShape, Bool.false_eq_true, ite_false, ite_true, Group.left, Group.right]
  all_goals unfold shift; split_ifs <;> omega

private theorem upperShape_compatible_lt {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {p q : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) (hq : q ∈ (active l cut).zipIdx)
    (hij : p.2 < q.2) (side other : Bool) :
    Compatible (upperShape cut (active l cut).length p side) (upperShape cut (active l cut).length q other) := by
  have hn := active_zip_nested hl hp hq hij
  obtain ⟨_, hpa, hpb⟩ := (mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
  obtain ⟨_, hqa, hqb⟩ := (mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hq)
  have hi : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hj : q.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hq
  cases side <;> cases other <;>
    simp only [upperShape, Bool.false_eq_true, ite_false, ite_true, Compatible, Group.Contains,
      Group.left, Group.right, left, right]
  all_goals unfold shift; split_ifs <;> omega

private theorem upperShape_compatible {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {p q : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) (hq : q ∈ (active l cut).zipIdx)
    (side other : Bool) (hne : upperShape cut (active l cut).length p side ≠ upperShape cut (active l cut).length q other) :
    Compatible (upperShape cut (active l cut).length p side) (upperShape cut (active l cut).length q other) := by
  rcases lt_trichotomy p.2 q.2 with hij | hij | hij
  · exact upperShape_compatible_lt hl hp hq hij side other
  · have hpq : p = q := Prod.ext (zip_payload_eq hp hq hij) hij
    subst q
    obtain ⟨_, hpa, hpb⟩ := (mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
    have hi : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
    cases side <;> cases other
    · exact (hne rfl).elim
    · simp only [upperShape, Bool.false_eq_true, ite_false, ite_true, Compatible, Group.Contains,
        Group.left, Group.right, left, right]
      unfold shift
      split_ifs <;> omega
    · simp only [upperShape, Bool.false_eq_true, ite_false, ite_true, Compatible, Group.Contains,
        Group.left, Group.right, left, right]
      unfold shift
      split_ifs <;> omega
    · exact (hne rfl).elim
  · exact (upperShape_compatible_lt hl hq hp hij other side).symm

private theorem upperShape_passive_compatible {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    {p : (ℕ × ℕ) × ℕ} (hp : p ∈ (active l cut).zipIdx) (side : Bool)
    {ab : ℕ × ℕ} (hab : ab ∈ passive l cut) :
    Compatible (upperShape cut (active l cut).length p side)
      (.wire (shift cut (active l cut).length ab.1) (shift cut (active l cut).length ab.2)) := by
  obtain ⟨hpm, hpa, hpb⟩ := (mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
  obtain ⟨hm, hnot⟩ := (mem_passive l cut ab).mp hab
  have hbound := page_bound_mem hl.upper (List.mem_map.mpr ⟨ab, hm, rfl⟩)
  change ab.1 < ab.2 ∧ ab.2 < l.portCount at hbound
  have hne : p.1 ≠ ab := by intro he; rw [he] at hpa hpb; exact hnot ⟨hpa, hpb⟩
  have hleft : p.1.1 ≠ ab.1 := by
    intro he
    exact hne (shared_upper (inventory_of_pages hl) hpm hm (i := p.1.1)
      (by simp [pairPorts]) (by simp [pairPorts, he]))
  have hright : p.1.2 ≠ ab.2 := by
    intro he
    exact hne (shared_upper (inventory_of_pages hl) hpm hm (i := p.1.2)
      (by simp [pairPorts]) (by simp [pairPorts, he]))
  have hcomp := page_compatible_mem hl.upper (List.mem_map.mpr ⟨p.1, hpm, rfl⟩)
    (List.mem_map.mpr ⟨ab, hm, rfl⟩) (by intro he; exact hne (Prod.ext (Group.wire.inj he).1 (Group.wire.inj he).2))
  have hi : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hleftBound := left_bounds (cut := cut) hi
  have hrightBound := right_bounds (cut := cut) hi
  simp only [Compatible, Group.Contains, Group.left, Group.right] at hcomp
  rcases p with ⟨⟨pa, pb⟩, pi⟩
  rcases ab with ⟨a, b⟩
  dsimp only at *
  cases side <;> simp only [upperShape, Bool.false_eq_true, ite_false, ite_true, Compatible,
    Group.Contains, Group.left, Group.right]
  all_goals unfold shift; split_ifs <;> omega

private theorem compile_upper_word {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) :
    (pageWord (compile l cut).pages.upperPage).Perm (List.range (compile l cut).portCount) := by
  have hi := compile_inventory (inventory_of_pages hl) cut hc hs
  have he : pageWord (compile l cut).pages.upperPage = (compile l cut).upperPairs.flatMap pairPorts := by
    simp only [pageWord, PortLayout.pages, Pages.upperPage, List.flatMap_map]
    rfl
  rw [he]
  exact hi.upper

/-- Both sides of the common-cut block retain every original upper noncrossing relation. -/
private theorem compile_upper_valid {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) : (compile l cut).pages.upperPage.Valid := by
  apply page_valid_of_word (hw := compile_upper_word hl hc hs)
  · intro g hg
    rcases compile_upper_cases l cut g hg with ⟨p, hp, side, rfl⟩ | ⟨ab, hab, rfl⟩
    · exact upperShape_bound hl hp side
    · obtain ⟨hm, _⟩ := (mem_passive l cut ab).mp hab
      have hb := page_bound_mem hl.upper (List.mem_map.mpr ⟨ab, hm, rfl⟩)
      exact ⟨shift_strictMono cut _ hb.1, shift_lt cut _ hb.2⟩
  · intro g hg k hk hne
    rcases compile_upper_cases l cut g hg with ⟨p, hp, side, rfl⟩ | ⟨ab, hab, rfl⟩
    · rcases compile_upper_cases l cut k hk with ⟨q, hq, other, rfl⟩ | ⟨xy, hxy, rfl⟩
      · exact upperShape_compatible hl hp hq side other hne
      · exact upperShape_passive_compatible hl hp side hxy
    · rcases compile_upper_cases l cut k hk with ⟨q, hq, other, rfl⟩ | ⟨xy, hxy, rfl⟩
      · exact (upperShape_passive_compatible hl hq other hab).symm
      · have hneq : Group.wire ab.1 ab.2 ≠ .wire xy.1 xy.2 := by
          intro he
          have hpairs : ab = xy := Prod.ext (Group.wire.inj he).1 (Group.wire.inj he).2
          exact hne (hpairs ▸ rfl)
        have hcomp := page_compatible_mem hl.upper
          (List.mem_map.mpr ⟨ab, ((mem_passive l cut ab).mp hab).1, rfl⟩)
          (List.mem_map.mpr ⟨xy, ((mem_passive l cut xy).mp hxy).1, rfl⟩) hneq
        exact compatible_shift hcomp rfl rfl rfl rfl

/-- The actual simultaneous cut is a complete valid standard two-page port layout. -/
theorem compile_valid {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount) (hs : SafeCut l cut) : (compile l cut).pages.Valid := by
  refine ⟨compile_upper_valid hl hc hs, compile_lower_valid hl hc hs, ?_⟩
  intro i
  obtain ⟨ab, _, he⟩ := List.mem_map.mp (List.get_mem (compile l cut).pages.upperPage.groups i)
  exact ⟨ab.1, ab.2, he.symm⟩

end PushPuzzle.Push.Partner.Cuts
