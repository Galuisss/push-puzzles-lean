/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainRigidity
import all PushS.OrderedSlots

/-! One complete consecutive train stays a complete interval along native line dynamics. -/

public section
namespace PushPuzzle.PushS.RowLabels


open PushFS

private theorem interval_card (first : ℤ) (len : ℕ) : (Finset.Ico first (first + len)).card = len := by
  rw [Int.card_Ico]
  simp only [add_sub_cancel_left, Int.toNat_natCast]

/-- An ordered complete train interval has its literal consecutive marked coordinates. -/
theorem OrderedLineState.interval_coordinates {w h len : ℕ} {axis : Direction} {lane : ℕ}
    (S : OrderedLineState len w h axis lane) (first : ℤ)
    (hslots : (lineBoxes axis lane S.state).image axis.position = Finset.Ico first (first + len)) :
    ∀ j : Fin len, axis.position (S.position j) = first + j.val := by
  have hmem (j : Fin len) : axis.position (S.position j) ∈ Finset.Ico first (first + len) := by
    rw [← hslots]
    exact Finset.mem_image.mpr ⟨S.position j, S.toLineState.position_mem j, rfl⟩
  have hcanonical (j : Fin len) : first + (j.val : ℤ) ∈ Finset.Ico first (first + len) := by
    have hj := j.isLt
    simp only [Finset.mem_Ico]
    omega
  have hmono : StrictMono (fun j : Fin len => first + (j.val : ℤ)) := by
    intro i j hij
    have hij' : i.val < j.val := hij
    change first + (i.val : ℤ) < first + (j.val : ℤ)
    omega
  have he := (Finset.orderEmbOfFin_unique (interval_card first len) hmem S.ordered).trans
    (Finset.orderEmbOfFin_unique (interval_card first len) hcanonical hmono).symm
  exact congrFun he

/-- A native line trajectory preserves a single initial consecutive train and its entire fixed length. -/
theorem interval_admissible {w h : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
    {s u : State w h} {len : ℕ} (hlen : 0 < len) (first : ℤ)
    (hr : Relation.ReflTransGen (LineAdmissible B cap axis lane) s u)
    (hslots : (lineBoxes axis lane s).image axis.position = Finset.Ico first (first + len)) :
    ∃ next : ℤ, (lineBoxes axis lane u).image axis.position = Finset.Ico next (next + len) := by
  have hcardSlots := interval_card first len
  have hcard : (lineBoxes axis lane s).card = len :=
    (Finset.card_image_of_injOn (position_injOn axis lane s)).symm.trans
      ((congrArg Finset.card hslots).trans hcardSlots)
  obtain ⟨S, hS⟩ : ∃ S : OrderedLineState len w h axis lane, S.state = s :=
    ⟨OrderedLineState.ofState s axis lane hcard, OrderedLineState.ofState_state _ _ _ _⟩
  have hcoordinates := S.interval_coordinates first (by rw [hS]; exact hslots)
  rw [← hS] at hr
  obtain ⟨M, hM, hreach⟩ := lift_reachable S.toLineState hr
  have hoff := hreach.block_offset (start := 0) (len := len) (a := first) hlen (by omega)
    (fun j hj => by simpa only [Nat.zero_add] using hcoordinates ⟨j, hj⟩)
  simp only [Nat.zero_add] at hoff
  let next := axis.position (M.position ⟨0, hlen⟩)
  refine ⟨next, ?_⟩
  rw [← hM, ← M.boxes_image]
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    have he := hoff j.val j.isLt
    simp only [Finset.mem_Ico]
    have hj := j.isLt
    change axis.position (M.position j) = next + j.val at he
    omega
  · intro hx
    have hx' := Finset.mem_Ico.mp hx
    have hxval : (((x - next).toNat : ℕ) : ℤ) = x - next := Int.toNat_of_nonneg (by omega)
    let j : Fin len := ⟨(x - next).toNat, by omega⟩
    have he := hoff j.val j.isLt
    change axis.position (M.position j) = next + j.val at he
    refine Finset.mem_image.mpr ⟨M.position j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [he]
    change next + ((x - next).toNat : ℤ) = x
    omega

end PushPuzzle.PushS.RowLabels
