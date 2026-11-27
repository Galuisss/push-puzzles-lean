/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineFrame

/-! Concrete ordinary-stock frames with their shared first and final endpoints held fixed. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Stock

open PushFS

def lane (w : ℕ) (above : Bool) (pre : List Atom) : Fin (height w) :=
  ⟨if exitSide above pre then FiniteTools.radius w+1 else FiniteTools.radius w-1, by
    unfold height FiniteTools.side FiniteTools.radius
    split <;> omega⟩

def line (w : ℕ) (pre post : List Atom) (n : ℕ) (above : Bool) :
    FiniteLineMacros.Line (width w (pre++ .line n::post)) (height w) where
  count := n-1
  base := FiniteTools.radius w+span w pre+2
  base_pos := by omega
  fits := by unfold width; simp only [span_append, span_cons, Atom.span]; unfold FiniteTools.radius; omega
  row := workY w
  lane := lane w above pre
  entry := if exitSide above pre then .north else .south
  crossing := by
    intro x
    cases hs : exitSide above pre <;> simp [Adjacent, lane, workY, hs, FiniteTools.radius]
  hub := ⟨FiniteTools.radius w+span w pre+1, by unfold width; simp only [span_append, span_cons, Atom.span]; omega⟩

def label (w : ℕ) (pre post : List Atom) (n : ℕ) (hn : 0 < n) (i : Fin (n-1)) :
    Label w (pre++ .line n::post) :=
  tailLabel w pre (.line n::post) (lineLabel w n post ⟨i.val+1, by have := i.isLt; omega⟩)

private theorem label_val (w : ℕ) (pre post : List Atom) (n : ℕ) (hn : 0 < n) (i : Fin (n-1)) :
    (label w pre post n hn i).val = ownedCount w pre+1+i.val := by
  dsimp [label, tailLabel, lineLabel]
  omega

def fixed (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) :
    Finset (Cell (width w (pre++ .line n::post)) (height w)) :=
  (Finset.univ.filter fun l : Label w (pre++ .line n::post) =>
    l.val ≤ ownedCount w pre ∨ ownedCount w pre+n ≤ l.val).image
      (cutCell w hw (ownedCount w pre+1) (pre++ .line n::post))

attribute [local irreducible] width height

private theorem slot (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (j : ℕ) (i : Fin (n-1)) :
    cutCell w hw (ownedCount w pre+1+j) (pre++ .line n::post) (label w pre post n hn i) =
      (line w pre post n above).position j i := by
  have hi := i.isLt
  by_cases hij : i.val < j
  · rw [cutCell, ite_eq_left (by rw [label_val]; omega)]
    apply Prod.ext <;> apply Fin.ext
    · change FiniteTools.radius w+position w (pre++ .line n::post) false (label w pre post n hn i) = _
      change _ = FiniteTools.radius w+span w pre+2+2*i.val+(if i.val < j then 0 else 1)
      rw [show label w pre post n hn i = tailLabel w pre (.line n::post) (lineLabel w n post ⟨i.val+1, by omega⟩) from rfl, tail_position, line_position]
      simp [hij]
      omega
    · rfl
  · rw [cutCell, ite_eq_right (by rw [label_val]; omega)]
    apply Prod.ext <;> apply Fin.ext
    · change FiniteTools.radius w+position w (pre++ .line n::post) true (label w pre post n hn i) = _
      change _ = FiniteTools.radius w+span w pre+2+2*i.val+(if i.val < j then 0 else 1)
      rw [show label w pre post n hn i = tailLabel w pre (.line n::post) (lineLabel w n post ⟨i.val+1, by omega⟩) from rfl, tail_position, line_position]
      simp [hij]
      omega
    · rfl

private theorem fixed_cell (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (j : ℕ) (hj : j ≤ n-1) (l : Label w (pre++ .line n::post))
    (hl : l.val ≤ ownedCount w pre ∨ ownedCount w pre+n ≤ l.val) :
    cutCell w hw (ownedCount w pre+1+j) (pre++ .line n::post) l =
      cutCell w hw (ownedCount w pre+1) (pre++ .line n::post) l := by
  rcases hl with hl | hl
  · simp only [cutCell, ite_eq_left (by omega : l.val < ownedCount w pre+1+j),
      ite_eq_left (by omega : l.val < ownedCount w pre+1)]
  · simp only [cutCell, ite_eq_right (by omega : ¬l.val < ownedCount w pre+1+j),
      ite_eq_right (by omega : ¬l.val < ownedCount w pre+1)]

/-- The cut inventory contains precisely this stock's interior and the unchanged real surrounding boxes. -/
theorem inventory (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (j : ℕ) (hj : j ≤ n-1) :
    cutBoxes w hw (ownedCount w pre+1+j) (pre++ .line n::post) =
      (line w pre post n above).boxes (fixed w hw pre post n) j := by
  ext p
  constructor
  · intro hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases hl : l.val ≤ ownedCount w pre ∨ ownedCount w pre+n ≤ l.val
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩,
        (fixed_cell w hw pre post n hn j hj l hl).symm⟩
    · have hi : l.val-ownedCount w pre-1 < n-1 := by omega
      let i : Fin (n-1) := ⟨l.val-ownedCount w pre-1, hi⟩
      have he : label w pre post n hn i = l := by
        apply Fin.ext
        rw [label_val]
        dsimp [i]
        omega
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        ((slot w hw pre post n hn above j i).symm.trans (congrArg (cutCell w hw _ _) he))⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _,
        fixed_cell w hw pre post n hn j hj l (Finset.mem_filter.mp hl).2⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨label w pre post n hn i, Finset.mem_univ _, slot w hw pre post n hn above j i⟩

def first (w : ℕ) (pre post : List Atom) (n : ℕ) (hn : 0 < n) : Label w (pre++ .line n::post) :=
  tailLabel w pre (.line n::post) (lineLabel w n post ⟨0, hn⟩)

def last (w : ℕ) (pre post : List Atom) (n : ℕ) : Label w (pre++ .line n::post) :=
  tailLabel w pre (.line n::post) (lineEndpointLabel w n post)

private theorem first_x (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n) :
    (cutCell w hw (ownedCount w pre+1) (pre++ .line n::post) (first w pre post n hn)).1.val =
      FiniteTools.radius w+span w pre := by
  rw [cutCell, ite_eq_left (by dsimp [first, tailLabel, lineLabel]; omega)]
  change FiniteTools.radius w+position w _ false _ = _
  unfold first
  rw [tail_position, line_position]
  simp

private theorem last_x (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n) :
    (cutCell w hw (ownedCount w pre+1) (pre++ .line n::post) (last w pre post n)).1.val =
      FiniteTools.radius w+span w pre+2*n+1 := by
  rw [cutCell, ite_eq_right (by dsimp [last, tailLabel, lineEndpointLabel]; omega)]
  change FiniteTools.radius w+position w _ true _ = _
  unfold last
  rw [tail_position, line_endpoint_position]
  simp [Nat.add_assoc]

/-- The complete ordinary stock has its own exposed lane and preserves every surrounding box. -/
theorem frame (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) :
    (line w pre post n above).Frame (macroBoard w (pre++ .line n::post) above)
      (fixed w hw pre post n) := by
  have hfixed : ∀ p ∈ fixed w hw pre post n,
      p ∉ (macroBoard w (pre++ .line n::post) above).walls := by
    intro p hp
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
    exact (FiniteWireFrame.floor_iff _ _ _).mpr
      (cutCell_active w hw (ownedCount w pre+1) _ above l)
  refine ⟨Finset.disjoint_left.mpr hfixed, ?_, ?_⟩
  · intro x hx
    have hxlo : FiniteTools.radius w+span w pre+1 ≤ x.val := by
      dsimp [line, FiniteLineMacros.Line.track] at hx
      omega
    have hxhi : x.val ≤ FiniteTools.radius w+span w pre+2*n := by
      dsimp [line, FiniteLineMacros.Line.track] at hx
      omega
    refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, ?_⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by omega, ?_, ?_, ?_, row_floor w _ above _ rfl⟩
      · simp only [span_append, span_cons, Atom.span]; omega
      all_goals dsimp [line, workY]; unfold FiniteTools.radius; omega
    · intro hp
      obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
      have hxe := congrArg (fun p : Cell (width w (pre++ .line n::post)) (height w) => p.1.val) he
      rcases (Finset.mem_filter.mp hl).2 with hl | hl
      · have hord := cutCell_order w hw (ownedCount w pre+1) (pre++ .line n::post)
          l (first w pre post n hn) (by dsimp [first, tailLabel, lineLabel]; exact hl)
        rw [first_x] at hord
        change _ = x.val at hxe
        omega
      · have hord := cutCell_order w hw (ownedCount w pre+1) (pre++ .line n::post)
          (last w pre post n) l (by dsimp [last, tailLabel, lineEndpointLabel]; exact hl)
        rw [last_x w hw pre post n hn] at hord
        change _ = x.val at hxe
        omega
  · intro x hx
    have hxlo : FiniteTools.radius w+span w pre+1 ≤ x.val := by
      dsimp [line, FiniteLineMacros.Line.laneSegment] at hx
      omega
    have hxhi : x.val ≤ FiniteTools.radius w+span w pre+2*n := by
      dsimp [line, FiniteLineMacros.Line.laneSegment] at hx
      omega
    refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, ?_⟩
    · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by omega, ?_, ?_, ?_, ?_⟩
      · simp only [span_append, span_cons, Atom.span]; omega
      · cases hs : exitSide above pre <;> dsimp [line, lane] <;> rw [hs] <;>
          simp only [Bool.false_eq_true, ite_false, ite_true] <;> unfold FiniteTools.radius <;> omega
      · cases hs : exitSide above pre <;> dsimp [line, lane] <;> rw [hs] <;>
          simp only [Bool.false_eq_true, ite_false, ite_true] <;> unfold FiniteTools.radius <;> omega
      · exact stock_face_floor w hw pre post above n ha _ hxlo hxhi (by
          cases hs : exitSide above pre <;> simp [line, lane, Exposed, hs, FiniteTools.radius])
    · intro hp
      obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
      have hye := congrArg (fun p : Cell (width w (pre++ .line n::post)) (height w) => p.2.val) he
      have hrow := (cutCell_coordinates w hw (ownedCount w pre+1) (pre++ .line n::post) l).2
      change (cutCell w hw (ownedCount w pre+1) (pre++ .line n::post) l).2.val = (lane w above pre).val at hye
      rw [hrow] at hye
      cases hs : exitSide above pre <;> simp [lane, hs, FiniteTools.radius] at hye

private theorem high_to_low (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩ := by
  have hr := (frame w hw pre post n hn above ha).forward
  have hzero := inventory w hw pre post n hn above 0 (by omega)
  have hfull := inventory w hw pre post n hn above (n-1) (by omega)
  simp only [Nat.add_zero] at hzero
  have he : ownedCount w pre+1+(n-1) = ownedCount w pre+n := by omega
  rw [he] at hfull
  change Reachable _ _ ⟨_, (line w pre post n above).boxes _ 0⟩
    ⟨_, (line w pre post n above).boxes _ (n-1)⟩ at hr
  rw [← hzero, ← hfull] at hr
  exact hr

private theorem low_to_high (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane),
        cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩ := by
  have hr := (frame w hw pre post n hn above ha).backward
  have hzero := inventory w hw pre post n hn above 0 (by omega)
  have hfull := inventory w hw pre post n hn above (n-1) (by omega)
  simp only [Nat.add_zero] at hzero
  have he : ownedCount w pre+1+(n-1) = ownedCount w pre+n := by omega
  rw [he] at hfull
  change Reachable _ _ ⟨_, (line w pre post n above).boxes _ (n-1)⟩
    ⟨_, (line w pre post n above).boxes _ 0⟩ at hr
  rw [← hzero, ← hfull] at hr
  exact hr

theorem hub_free (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) (cut : ℕ) (y : Fin (height w))
    (hy : min (lane w above pre).val (laneY w (!(exitSide above pre))).val ≤ y.val)
    (hy' : y.val ≤ max (lane w above pre).val (laneY w (!(exitSide above pre))).val) :
    Free (macroBoard w (pre++ .line n::post) above) (cutBoxes w hw cut (pre++ .line n::post))
      ((line w pre post n above).hub, y) := by
  have hylo : FiniteTools.radius w-w-1 ≤ y.val := by
    cases hs : exitSide above pre <;> simp [lane, laneY, hs] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  have hyhi : y.val ≤ FiniteTools.radius w+w+1 := by
    cases hs : exitSide above pre <;> simp [lane, laneY, hs] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  have hyn : y.val ≠ FiniteTools.radius w := by
    cases hs : exitSide above pre <;> simp [lane, laneY, hs] at hy hy' ⊢ <;> unfold FiniteTools.radius at * <;> omega
  refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ?_, ?_⟩
  · simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, hylo, hyhi, ?_⟩
    · dsimp [line]; omega
    · dsimp [line]; simp only [span_append, span_cons, Atom.span]; omega
    · apply stock_face_floor w hw pre post above n ha
      · dsimp [line]; omega
      · dsimp [line]; omega
      · cases hs : exitSide above pre <;> simp [lane, laneY, Exposed, hs] at hy hy' ⊢ <;>
          unfold FiniteTools.radius at * <;> omega
  · intro hp
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
    have hye := congrArg (fun p : Cell (width w (pre++ .line n::post)) (height w) => p.2.val) he
    have hrow := (cutCell_coordinates w hw cut (pre++ .line n::post) l).2
    change (cutCell w hw cut (pre++ .line n::post) l).2.val = y.val at hye
    omega

private theorem hub_to_outer (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) (cut : ℕ) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨outerCell w _ (!(exitSide above pre)) (line w pre post n above).hub, cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw cut _ above)
  exact hub_free w hw pre post n hn above ha cut

private theorem outer_to_hub (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w) (cut : ℕ) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨outerCell w _ (!(exitSide above pre)) (line w pre post n above).hub, cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  apply walk_vertical (cutBoxes_macro_floor w hw cut _ above)
  intro y hy hy'
  exact hub_free w hw pre post n hn above ha cut y (by simpa only [min_comm, line] using hy)
    (by simpa only [max_comm, line] using hy')

private theorem hub_reachable (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) (cut : ℕ) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  apply (outer_macro_connected_of_flip w hw cut _ hflip above true (!(exitSide above pre))
    (outerHubX w _) (line w pre post n above).hub (by dsimp [outerHubX]; omega)
    (by dsimp [outerHubX]; omega) (by dsimp [line]; omega)
    (by dsimp [line]; simp only [span_append, span_cons, Atom.span]; omega)).trans
  exact outer_to_hub w hw pre post n hn above ha cut

private theorem hub_return (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) (cut : ℕ) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨((line w pre post n above).hub, (line w pre post n above).lane), cutBoxes w hw cut (pre++ .line n::post)⟩
      ⟨outerHub w _, cutBoxes w hw cut (pre++ .line n::post)⟩ := by
  apply (hub_to_outer w hw pre post n hn above ha cut).trans
  exact outer_macro_connected_of_flip w hw cut _ hflip above (!(exitSide above pre)) true
    (line w pre post n above).hub (outerHubX w _) (by dsimp [line]; omega)
    (by dsimp [line]; simp only [span_append, span_cons, Atom.span]; omega)
    (by dsimp [outerHubX]; omega) (by dsimp [outerHubX]; omega)

theorem sweep_low_high (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩ :=
  (hub_reachable w hw pre post n hn above ha hflip _).trans
    ((low_to_high w hw pre post n hn above ha).trans (hub_return w hw pre post n hn above ha hflip _))

theorem sweep_high_low (w : ℕ) (hw : 2 ≤ w) (pre post : List Atom) (n : ℕ) (hn : 0 < n)
    (above : Bool) (ha : ∀ a ∈ pre++ .line n::post, a.Valid w)
    (hflip : ∃ left right, pre++ .line n::post = left++ .flip::right) :
    Reachable (macroBoard w (pre++ .line n::post) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+1) (pre++ .line n::post)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w pre+n) (pre++ .line n::post)⟩ :=
  (hub_reachable w hw pre post n hn above ha hflip _).trans
    ((high_to_low w hw pre post n hn above ha).trans (hub_return w hw pre post n hn above ha hflip _))

end PushPuzzle.PushS.FiniteRouting.Line.Stock
