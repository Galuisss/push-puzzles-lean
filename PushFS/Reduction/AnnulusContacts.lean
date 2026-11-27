/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusRectangles

/-! Actual rectangle separation reduces every whole-annulus wall and slot-ownership check to its true local contacts. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


/-- The already assembled four genuine buffered-core pieces satisfy their complete wall contract. -/
theorem buffer_walls (g : GateTileState) (i j : Fin 4)
    (p : Cell (piece g (.inl i)).width (piece g (.inl i)).height)
    (q : Cell (piece g (.inl j)).width (piece g (.inl j)).height)
    (he : ((offset g (.inl i)).1+p.1.val,(offset g (.inl i)).2+p.2.val)=
      ((offset g (.inl j)).1+q.1.val,(offset g (.inl j)).2+q.2.val)) :
    p∈(piece g (.inl i)).board.walls ↔ q∈(piece g (.inl j)).board.walls :=
  (bufferAtlas g).walls_compatible i j p q he

theorem buffer_source_owners (g : GateTileState) (i j : Fin 4)
    (l : Labels g (.inl i)) (k : Labels g (.inl j))
    (he : ((offset g (.inl i)).1+((matching g (.inl i)).source l).1.val,
      (offset g (.inl i)).2+((matching g (.inl i)).source l).2.val)=
      ((offset g (.inl j)).1+((matching g (.inl j)).source k).1.val,
      (offset g (.inl j)).2+((matching g (.inl j)).source k).2.val)) : i=j :=
  (bufferAtlas g).source_owners i j l k he

theorem buffer_target_owners (g : GateTileState) (i j : Fin 4)
    (l : Labels g (.inl i)) (k : Labels g (.inl j))
    (he : ((offset g (.inl i)).1+((matching g (.inl i)).target l).1.val,
      (offset g (.inl i)).2+((matching g (.inl i)).target l).2.val)=
      ((offset g (.inl j)).1+((matching g (.inl j)).target k).1.val,
      (offset g (.inl j)).2+((matching g (.inl j)).target k).2.val)) : i=j :=
  (bufferAtlas g).target_owners i j l k he

theorem no_coincident (g : GateTileState) (i j : Index g) (hij : i≠j) (hc : contact g i j=false)
    (p : Cell (piece g i).width (piece g i).height) (q : Cell (piece g j).width (piece g j).height) :
    ((offset g i).1+p.1.val,(offset g i).2+p.2.val)≠((offset g j).1+q.1.val,(offset g j).2+q.2.val) := by
  intro he
  apply Rectangle.no_common (separated g i j hij hc) (p:=(p.1.val,p.2.val)) (q:=(q.1.val,q.2.val))
  · simpa only [rectangle,← (piece_dimensions g i).1,← (piece_dimensions g i).2] using And.intro p.1.isLt p.2.isLt
  · simpa only [rectangle,← (piece_dimensions g j).1,← (piece_dimensions g j).2] using And.intro q.1.isLt q.2.isLt
  · simpa only [rectangle,geometricOffset_eq] using he

/-- Every needed contact is between actual adjacent complete storage pieces. -/
structure ContactProofs (g : GateTileState) : Prop where
  walls : ∀ i j,contact g i j=true → ∀ (p : Cell (piece g i).width (piece g i).height)
      (q : Cell (piece g j).width (piece g j).height),
    ((offset g i).1+p.1.val,(offset g i).2+p.2.val)=((offset g j).1+q.1.val,(offset g j).2+q.2.val) →
      (p∈(piece g i).board.walls ↔ q∈(piece g j).board.walls)
  sources : ∀ i j,contact g i j=true → ∀ (l : Labels g i) (k : Labels g j),
    ((offset g i).1+((matching g i).source l).1.val,(offset g i).2+((matching g i).source l).2.val)=
      ((offset g j).1+((matching g j).source k).1.val,(offset g j).2+((matching g j).source k).2.val) → i=j
  targets : ∀ i j,contact g i j=true → ∀ (l : Labels g i) (k : Labels g j),
    ((offset g i).1+((matching g i).target l).1.val,(offset g i).2+((matching g i).target l).2.val)=
      ((offset g j).1+((matching g j).target k).1.val,(offset g j).2+((matching g j).target k).2.val) → i=j

namespace ContactProofs

variable {g : GateTileState} (h : ContactProofs g)

include h in
theorem walls_compatible (i j : Index g) (p : Cell (piece g i).width (piece g i).height)
    (q : Cell (piece g j).width (piece g j).height)
    (he : ((offset g i).1+p.1.val,(offset g i).2+p.2.val)=((offset g j).1+q.1.val,(offset g j).2+q.2.val)) :
    p∈(piece g i).board.walls ↔ q∈(piece g j).board.walls := by
  by_cases hij : i=j
  · subst j
    have hpq : p=q := by
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      apply Prod.ext <;> apply Fin.ext <;> dsimp only at hx hy ⊢ <;> omega
    cases hpq
    rfl
  · cases hc : contact g i j with
    | false => exact False.elim (no_coincident g i j hij hc p q he)
    | true => exact h.walls i j hc p q he

include h in
theorem source_owners (i j : Index g) (l : Labels g i) (k : Labels g j)
    (he : ((offset g i).1+((matching g i).source l).1.val,(offset g i).2+((matching g i).source l).2.val)=
      ((offset g j).1+((matching g j).source k).1.val,(offset g j).2+((matching g j).source k).2.val)) : i=j := by
  by_cases hij : i=j
  · exact hij
  · cases hc : contact g i j with
    | false => exact False.elim (no_coincident g i j hij hc _ _ he)
    | true => exact h.sources i j hc l k he

include h in
theorem target_owners (i j : Index g) (l : Labels g i) (k : Labels g j)
    (he : ((offset g i).1+((matching g i).target l).1.val,(offset g i).2+((matching g i).target l).2.val)=
      ((offset g j).1+((matching g j).target k).1.val,(offset g j).2+((matching g j).target k).2.val)) : i=j := by
  by_cases hij : i=j
  · exact hij
  · cases hc : contact g i j with
    | false => exact False.elim (no_coincident g i j hij hc _ _ he)
    | true => exact h.targets i j hc l k he

end ContactProofs
end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
