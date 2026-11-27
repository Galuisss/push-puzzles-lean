/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateOutputs

/-! Release the prepared output trigger from its input-side entrance. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateOutputReturn

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateOutputs

attribute [local irreducible] side

/-- Enter from the left, push the output boundary right, and return to the same entrance. -/
theorem push_right_via_mouth {W H : ℕ} {B : Board W H} {boxes : Finset (Cell W H)}
    (hboxes : Disjoint boxes B.walls) (mouth support src dst : Fin W) (u y : Fin H)
    (hentry : Adjacent .south (mouth, u) (mouth, y))
    (hexit : Adjacent .north (mouth, y) (mouth, u))
    (hax : Adjacent .east (support, y) (src, y))
    (hxd : Adjacent .east (src, y) (dst, y)) (hmouth : mouth.val ≤ support.val)
    (hsource : (src, y) ∈ boxes) (hdest : Free B boxes (dst, y))
    (hupper : Free B boxes (mouth, u))
    (hrow : ∀ x : Fin W, mouth.val ≤ x.val → x.val < src.val → Free B boxes (x, y)) :
    Reachable B (some 1) ⟨(mouth, u), boxes⟩
      ⟨(mouth, u), insert (dst, y) (boxes.erase (src, y))⟩ := by
  have hax' := hax
  have hxd' := hxd
  simp only [Adjacent] at hax' hxd'
  have hmouthfree := hrow mouth (by omega) (by omega)
  have hsupport := hrow support hmouth (by omega)
  have hdown : SingleMoveView B .south (⟨(mouth, u), boxes⟩ : State W H) ⟨(mouth, y), boxes⟩ :=
    SingleMoveView.walk ⟨hupper.1, hboxes, hupper.2⟩ hentry hmouthfree.1 hmouthfree.2
  have hin := walk_horizontal hboxes mouth support y (by
    intro x hx hx'
    apply hrow x <;> omega)
  have hpush : SingleMoveView B .east (⟨(support, y), boxes⟩ : State W H)
      ⟨(src, y), insert (dst, y) (boxes.erase (src, y))⟩ :=
    SingleMoveView.push ⟨hsupport.1, hboxes, hsupport.2⟩ hax hsource hxd hdest.1 hdest.2
  have hnewrow : ∀ x : Fin W, mouth.val ≤ x.val → x.val ≤ src.val →
      Free B (insert (dst, y) (boxes.erase (src, y))) (x, y) := by
    intro x hx hx'
    by_cases he : x = src
    · subst x
      refine ⟨fun hw => Finset.disjoint_left.mp hboxes hsource hw, ?_⟩
      intro hm
      rcases Finset.mem_insert.mp hm with he | he
      · have hxval : src.val = dst.val := congrArg (fun p : Cell W H => p.1.val) he
        omega
      · exact (Finset.mem_erase.mp he).1 rfl
    · have hf := hrow x hx (by have := Fin.val_ne_of_ne he; omega)
      refine ⟨hf.1, ?_⟩
      intro hmem
      rcases Finset.mem_insert.mp hmem with he' | he'
      · have hxval : x.val = dst.val := congrArg (fun p : Cell W H => p.1.val) he'
        omega
      · exact hf.2 (Finset.mem_of_mem_erase he')
  have hout := walk_horizontal hpush.valid_target.2.1 src mouth y (by
    intro x hx hx'
    apply hnewrow x <;> omega)
  have hu_ne : u ≠ y := by
    intro he
    exact hentry.ne (by rw [he])
  have hupper' : Free B (insert (dst, y) (boxes.erase (src, y))) (mouth, u) := by
    refine ⟨hupper.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hu_ne (congrArg Prod.snd he)
    · exact hupper.2 (Finset.mem_of_mem_erase he)
  have hup : SingleMoveView B .north
      (⟨(mouth, y), insert (dst, y) (boxes.erase (src, y))⟩ : State W H)
      ⟨(mouth, u), insert (dst, y) (boxes.erase (src, y))⟩ := SingleMoveView.walk
    ⟨(hnewrow mouth (by omega) (by omega)).1, hpush.valid_target.2.1,
      (hnewrow mouth (by omega) (by omega)).2⟩ hexit hupper'.1 hupper'.2
  exact (((Relation.ReflTransGen.single ⟨.south, Move.single_iff.mpr hdown⟩).trans hin).tail
    ⟨.east, Move.single_iff.mpr hpush⟩).trans (hout.tail ⟨.north, Move.single_iff.mpr hup⟩)


/-- Restore the full normal inventory by releasing its prepared output trigger. -/
private theorem finish_right_via_mouth {W H : ℕ} {B : Board W H} {boxes : Finset (Cell W H)}
    (hboxes : Disjoint boxes B.walls) (mouth support old normal : Fin W) (u y : Fin H)
    (hentry : Adjacent .south (mouth, u) (mouth, y))
    (hexit : Adjacent .north (mouth, y) (mouth, u))
    (hax : Adjacent .east (support, y) (old, y))
    (hxn : Adjacent .east (old, y) (normal, y)) (hmouth : mouth.val ≤ support.val)
    (hnormal : (normal, y) ∈ boxes) (hold : Free B boxes (old, y))
    (hupper : Free B boxes (mouth, u))
    (hrow : ∀ x : Fin W, mouth.val ≤ x.val → x.val < old.val → Free B boxes (x, y)) :
    Reachable B (some 1) ⟨(mouth, u), insert (old, y) (boxes.erase (normal, y))⟩
      ⟨(mouth, u), boxes⟩ := by
  have hprepared : Disjoint (insert (old, y) (boxes.erase (normal, y))) B.walls :=
    Finset.disjoint_insert_left.mpr ⟨hold.1, hboxes.mono_left (Finset.erase_subset _ _)⟩
  have hrestore : insert (normal, y)
      ((insert (old, y) (boxes.erase (normal, y))).erase (old, y)) = boxes := by
    rw [Finset.erase_insert (fun hm => hold.2 (Finset.mem_of_mem_erase hm))]
    exact Finset.insert_erase hnormal
  have hnew : Free B (insert (old, y) (boxes.erase (normal, y))) (normal, y) := by
    refine ⟨fun hw => Finset.disjoint_left.mp hboxes hnormal hw, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hxn.ne he.symm
    · exact (Finset.mem_erase.mp he).1 rfl
  have hupper' : Free B (insert (old, y) (boxes.erase (normal, y))) (mouth, u) := by
    refine ⟨hupper.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · have hrowne : u ≠ y := fun hu => hentry.ne (by rw [hu])
      exact hrowne (congrArg Prod.snd he)
    · exact hupper.2 (Finset.mem_of_mem_erase he)
  have hrow' : ∀ x : Fin W, mouth.val ≤ x.val → x.val < old.val →
      Free B (insert (old, y) (boxes.erase (normal, y))) (x, y) := by
    intro x hx hx'
    have hf := hrow x hx hx'
    refine ⟨hf.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · have hxe : x.val = old.val := congrArg (fun p : Cell W H => p.1.val) he
      omega
    · exact hf.2 (Finset.mem_of_mem_erase he)
  have hr := push_right_via_mouth hprepared mouth support old normal u y
    hentry hexit hax hxn hmouth (Finset.mem_insert_self _ _) hnew hupper' hrow'
  simpa only [hrestore] using hr

/-- Release C after all output-tail boxes have reached their new normal slots. -/
theorem and_C_release (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 3 1, andOutputBoxes w true true false⟩
      ⟨point w 3 1, andBoxes w true true false⟩ := by
  rw [← andOutputBoxes_initial w hw true true]
  have hnormal : point w (w+5) 0 ∈ andBoxes w true true false := by
    have he : andCell w true true false (.branchC 0) = point w (w+5) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  refine finish_right_via_mouth (andBoxes_disjoint_walls w hw true true false)
    (point w 3 1).1 (point w (w+3) 0).1
    (point w (w+4) 0).1 (point w (w+5) 0).1
    (point w 3 1).2 (point w 3 0).2 ?_ ?_ ?_ ?_ ?_ hnormal ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply and_row_free w hw true true false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false]; omega
  · apply and_above_free w hw true true false goals
    all_goals dsimp only [point]
    all_goals first | exact Or.inr rfl | (unfold origin; omega)
  · intro x hx hx'
    apply and_row_free w hw true true false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false] at *; omega

/-- Release C after all output-tail boxes have reached their new normal slots. -/
private theorem or_C_release_A (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 3 1, orOutputBoxes w true b false⟩
      ⟨point w 3 1, orBoxes w true b false⟩ := by
  rw [← orOutputBoxes_initial w hw true b]
  have hnormal : point w (w+6) 0 ∈ orBoxes w true b false := by
    have he : orCell w true b false (.branchC 0) = point w (w+6) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  refine finish_right_via_mouth (orBoxes_disjoint_walls w hw true b false)
    (point w 3 1).1 (point w (w+4) 0).1
    (point w (w+5) 0).1 (point w (w+6) 0).1
    (point w 3 1).2 (point w 3 0).2 ?_ ?_ ?_ ?_ ?_ hnormal ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply or_row_free w hw true b false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false]; omega
  · apply or_above_free w hw true b false goals
    all_goals dsimp only [point]
    all_goals unfold origin; omega
  · intro x hx hx'
    apply or_row_free w hw true b false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false] at *; omega

/-- Release C after all output-tail boxes have reached their new normal slots. -/
theorem or_C_release_B (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 4 1, orOutputBoxes w false true false⟩
      ⟨point w 4 1, orBoxes w false true false⟩ := by
  rw [← orOutputBoxes_initial w hw false true]
  have hnormal : point w (w+6) 0 ∈ orBoxes w false true false := by
    have he : orCell w false true false (.branchC 0) = point w (w+6) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  refine finish_right_via_mouth (orBoxes_disjoint_walls w hw false true false)
    (point w 4 1).1 (point w (w+4) 0).1
    (point w (w+5) 0).1 (point w (w+6) 0).1
    (point w 4 1).2 (point w 4 0).2 ?_ ?_ ?_ ?_ ?_ hnormal ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply or_row_free w hw false true false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · apply or_above_free w hw false true false goals
    all_goals dsimp only [point]
    all_goals first | exact Or.inr rfl | (unfold origin; omega)
  · intro x hx hx'
    apply or_row_free w hw false true false goals
    all_goals simp only [point, Bool.toNat_false] at *; omega

/-- Update the full tail first, leaving only the prepared output trigger. -/
theorem and_C_tail_backward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+6) 1, andBoxes w a b true⟩
      ⟨point w (w+6) 1, andOutputBoxes w a b false⟩ := by
  have hr := (andOutputFrame w hw a b goals).backward
  have hzero := andOutputLine_boxes w a b false
  change (outputLine w 6).boxes (andOutputFixed w a b) 0 = andOutputBoxes w a b false at hzero
  have hfull := andOutputLine_boxes w a b true
  change (outputLine w 6).boxes (andOutputFixed w a b) (w+4) = andOutputBoxes w a b true at hfull
  change Reachable (andBoard w goals) (some 1)
    ⟨point w (w+6) 1, (outputLine w 6).boxes (andOutputFixed w a b) (w+4)⟩
    ⟨point w (w+6) 1, (outputLine w 6).boxes (andOutputFixed w a b) 0⟩ at hr
  rw [hfull, hzero, andOutputBoxes_true] at hr
  exact hr

/-- Update the full tail first, leaving only the prepared output trigger. -/
theorem or_C_tail_backward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orBoxes w a b true⟩
      ⟨point w (w+7) 1, orOutputBoxes w a b false⟩ := by
  have hr := (orOutputFrame w hw a b goals).backward
  have hzero := orOutputLine_boxes w a b false
  change (outputLine w 7).boxes (orOutputFixed w a b) 0 = orOutputBoxes w a b false at hzero
  have hfull := orOutputLine_boxes w a b true
  change (outputLine w 7).boxes (orOutputFixed w a b) (w+4) = orOutputBoxes w a b true at hfull
  change Reachable (orBoard w goals) (some 1)
    ⟨point w (w+7) 1, (outputLine w 7).boxes (orOutputFixed w a b) (w+4)⟩
    ⟨point w (w+7) 1, (outputLine w 7).boxes (orOutputFixed w a b) 0⟩ at hr
  rw [hfull, hzero, orOutputBoxes_true] at hr
  exact hr

/-- Complete output release, retaining its explicit exterior entrance connection. -/
theorem and_C_backward (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (andBoard w goals) (some 1)
      ⟨point w (w+6) 1, andOutputBoxes w true true false⟩
      ⟨point w 3 1, andOutputBoxes w true true false⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+6) 1, andBoxes w true true true⟩
      ⟨point w 3 1, andBoxes w true true false⟩ :=
  (and_C_tail_backward w hw true true goals).trans
    (hconnect.trans (and_C_release w hw goals))

/-- Complete output release, retaining its explicit exterior entrance connection. -/
theorem or_C_backward_A (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orOutputBoxes w true b false⟩
      ⟨point w 3 1, orOutputBoxes w true b false⟩) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orBoxes w true b true⟩
      ⟨point w 3 1, orBoxes w true b false⟩ :=
  (or_C_tail_backward w hw true b goals).trans
    (hconnect.trans (or_C_release_A w hw b goals))

/-- Complete output release, retaining its explicit exterior entrance connection. -/
theorem or_C_backward_B (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orOutputBoxes w false true false⟩
      ⟨point w 4 1, orOutputBoxes w false true false⟩) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orBoxes w false true true⟩
      ⟨point w 4 1, orBoxes w false true false⟩ :=
  (or_C_tail_backward w hw false true goals).trans
    (hconnect.trans (or_C_release_B w hw goals))

end PushPuzzle.PushS.FiniteGateOutputReturn
