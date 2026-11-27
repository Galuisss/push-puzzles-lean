/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsRepair

/-! Literal three-edge paths and their contraction through every common cut. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

private theorem zip_getD {xs : List (ℕ × ℕ)} {p : (ℕ × ℕ) × ℕ} (hp : p ∈ xs.zipIdx) :
    xs.getD p.2 (0, 0) = p.1 := by
  simp only [List.getD_eq_getElem?_getD, List.mem_zipIdx_iff_getElem?.mp hp, Option.getD_some]

private theorem active_zip_exists {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} (hm : ab ∈ active l cut) :
    ∃ j, (ab, j) ∈ (active l cut).zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
  refine ⟨i.val, List.mem_zipIdx_iff_getElem?.mpr ?_⟩
  rw [List.getElem?_eq_getElem i.isLt]
  exact congrArg some (List.get_eq_getElem.symm.trans hi)

/-- Each actual split arc has its literal left-upper, lower-WIRE, right-upper path. -/
private theorem compile_active_path {l : PortLayout} {cut : ℕ} {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ (active l cut).zipIdx) :
    WireConnected (compile l cut) (shift cut (active l cut).length p.1.1)
      (shift cut (active l cut).length p.1.2) := by
  have hleft : (shift cut (active l cut).length p.1.1, left cut (active l cut).length p.2) ∈
      (compile l cut).upperPairs := by
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self⟩
  have hright : (right cut (active l cut).length p.2, shift cut (active l cut).length p.1.2) ∈
      (compile l cut).upperPairs := by
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_of_mem _ List.mem_cons_self⟩
  have hwire : LowerGroup.wire (left cut (active l cut).length p.2) (right cut (active l cut).length p.2) ∈
      (compile l cut).lowerGroups :=
    List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact ((Relation.ReflTransGen.single (WireAdjacent.upper hleft)).tail (.lower hwire)).tail (.upper hright)

private theorem compile_upper_lift {l : PortLayout} {cut : ℕ} {a b : ℕ}
    (hab : (a, b) ∈ l.upperPairs) :
    WireConnected (compile l cut) (shift cut (active l cut).length a) (shift cut (active l cut).length b) := by
  by_cases hcross : a < cut ∧ cut ≤ b
  · obtain ⟨j, hj⟩ := active_zip_exists ((mem_active l cut (a, b)).mpr ⟨hab, hcross⟩)
    exact compile_active_path hj
  · exact .single (.upper ((compile_old_pair_mem l cut (a, b)).mpr ((mem_passive l cut _).mpr ⟨hab, hcross⟩)))

private theorem compile_adjacent_lift {l : PortLayout} {cut : ℕ} {a b : ℕ} (h : WireAdjacent l a b) :
    WireConnected (compile l cut) (shift cut (active l cut).length a) (shift cut (active l cut).length b) := by
  cases h with
  | upper hp => exact compile_upper_lift hp
  | upper_rev hp => exact (compile_upper_lift hp).symm
  | lower hp =>
    exact .single (.lower (List.mem_append_left _ (List.mem_map.mpr ⟨_, hp, rfl⟩)))
  | lower_rev hp =>
    exact .single (.lower_rev (List.mem_append_left _ (List.mem_map.mpr ⟨_, hp, rfl⟩)))

/-- Contract the actual fresh left and right ports onto their original arc's corresponding endpoints. -/
def collapse (l : PortLayout) (cut i : ℕ) : ℕ :=
  let xs := active l cut
  let count := xs.length
  if i < cut then i
  else if i < cut + count then (xs.getD (cut + count - 1 - i) (0, 0)).1
  else if i < cut + 2 * count then (xs.getD (i - cut - count) (0, 0)).2
  else i - 2 * count

private theorem collapse_shift (l : PortLayout) (cut i : ℕ) :
    collapse l cut (shift cut (active l cut).length i) = i := by
  unfold collapse shift
  dsimp only
  split_ifs <;> omega

private theorem collapse_left {l : PortLayout} {cut : ℕ} {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ (active l cut).zipIdx) : collapse l cut (left cut (active l cut).length p.2) = p.1.1 := by
  have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hb := left_bounds (cut := cut) hj
  have hidx : cut + (active l cut).length - 1 - left cut (active l cut).length p.2 = p.2 := by
    unfold left
    omega
  simp only [collapse, ite_eq_right (show ¬left cut (active l cut).length p.2 < cut by omega),
    ite_eq_left hb.2, hidx, zip_getD hp]

private theorem collapse_right {l : PortLayout} {cut : ℕ} {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ (active l cut).zipIdx) : collapse l cut (right cut (active l cut).length p.2) = p.1.2 := by
  have hj : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  have hb := right_bounds (cut := cut) hj
  have hidx : right cut (active l cut).length p.2 - cut - (active l cut).length = p.2 := by
    unfold right
    omega
  simp only [collapse, ite_eq_right (show ¬right cut (active l cut).length p.2 < cut by omega),
    ite_eq_right (show ¬right cut (active l cut).length p.2 < cut + (active l cut).length by omega),
    ite_eq_left hb.2, hidx, zip_getD hp]

private theorem compile_upper_project {l : PortLayout} {cut : ℕ} {a b : ℕ}
    (hab : (a, b) ∈ (compile l cut).upperPairs) : WireConnected l (collapse l cut a) (collapse l cut b) := by
  rcases List.mem_append.mp hab with hnew | hold
  · obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hnew
    simp only [upperPiece, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with he | he
    · cases he
      rw [collapse_shift, collapse_left hp]
    · cases he
      rw [collapse_right hp, collapse_shift]
  · obtain ⟨ab, hpassive, he⟩ := List.mem_map.mp hold
    cases he
    simp only [collapse_shift]
    exact .single (.upper ((mem_passive l cut ab).mp hpassive).1)

private theorem compile_lower_project {l : PortLayout} {cut : ℕ} {a b : ℕ}
    (hab : LowerGroup.wire a b ∈ (compile l cut).lowerGroups) :
    WireConnected l (collapse l cut a) (collapse l cut b) := by
  rcases List.mem_append.mp hab with hold | hnew
  · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
    cases old with
    | gate kind first => cases he
    | wire x y =>
      simp only [mapGroup, LowerGroup.wire.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      simp only [collapse_shift]
      exact .single (.lower hmem)
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp hnew
    cases he
    rw [collapse_left hp, collapse_right hp]
    exact .single (.upper ((mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)).1)

private theorem compile_adjacent_project {l : PortLayout} {cut : ℕ} {a b : ℕ}
    (h : WireAdjacent (compile l cut) a b) : WireConnected l (collapse l cut a) (collapse l cut b) := by
  cases h with
  | upper hp => exact compile_upper_project hp
  | upper_rev hp => exact (compile_upper_project hp).symm
  | lower hp => exact compile_lower_project hp
  | lower_rev hp => exact (compile_lower_project hp).symm

/-- The actual simultaneous cut preserves WIRE connectivity between every pair of old incidences. -/
private theorem compile_connected_iff (l : PortLayout) (cut a b : ℕ) :
    WireConnected (compile l cut) (shift cut (active l cut).length a) (shift cut (active l cut).length b) ↔
      WireConnected l a b := by
  constructor
  · intro hr
    have hp : ∀ {x y}, WireConnected (compile l cut) x y → WireConnected l (collapse l cut x) (collapse l cut y) := by
      intro x y hr
      induction hr with
      | refl => exact .refl
      | tail _ hm ih => exact ih.trans (compile_adjacent_project hm)
    simpa only [collapse_shift] using hp hr
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.trans (compile_adjacent_lift hm)

private theorem cutAt_connected_iff (s : BufferState) (cut : ℕ) {i j : ℕ}
    (hi : i < s.ports.length) (hj : j < s.ports.length) :
    WireConnected (cutAt s cut).layout ((cutAt s cut).port i) ((cutAt s cut).port j) ↔
      WireConnected s.layout (s.port i) (s.port j) := by
  unfold cutAt
  split_ifs
  · have hget (k : ℕ) (hk : k < s.ports.length) :
        (s.ports.map (shift cut (active s.layout cut).length)).getD k 0 =
          shift cut (active s.layout cut).length (s.port k) := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hk), List.getElem_map]
      unfold BufferState.port
      rw [List.getD_eq_getElem _ _ hk]
    change WireConnected _ ((s.ports.map _).getD i 0) ((s.ports.map _).getD j 0) ↔ _
    rw [hget i hi, hget j hj]
    exact compile_connected_iff _ _ _ _
  · rfl

private theorem scan_connected_iff (s : BufferState) (positions : List ℕ) {i j : ℕ}
    (hi : i < s.ports.length) (hj : j < s.ports.length) :
    WireConnected (scan s positions).layout ((scan s positions).port i) ((scan s positions).port j) ↔
      WireConnected s.layout (s.port i) (s.port j) := by
  induction positions generalizing s with
  | nil => rfl
  | cons cut rest ih =>
    have hi' : i < (cutAt s cut).ports.length := by rwa [cutAt_length]
    have hj' : j < (cutAt s cut).ports.length := by rwa [cutAt_length]
    exact (ih (cutAt s cut) hi' hj').trans (cutAt_connected_iff s cut hi hj)

/-- The complete actual reader-partner repair keeps exactly the original WIRE connectivity. -/
theorem repair_connected_iff (l : PortLayout) {i j : ℕ} (hi : i < l.portCount) (hj : j < l.portCount) :
    WireConnected (repair l).layout ((repair l).port i) ((repair l).port j) ↔ WireConnected l i j := by
  have hi' : i < (bufferInternal l).ports.length := by rwa [bufferInternal_length]
  have hj' : j < (bufferInternal l).ports.length := by rwa [bufferInternal_length]
  exact (scan_connected_iff (bufferInternal l) _ hi' hj').trans (bufferInternal_connected_iff l hi hj)

end PushPuzzle.Push.Partner.Cuts
