/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusFrontierContract
public import PushFS.Reduction.AnnulusShortContacts

/-! All actual annular contact proofs follow from the three buffered frontiers and the complete checked short-turn joints. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem short_walls (g : GateTileState) (role : Fin 3)
    (j : Fin (curve (key g role)).length) (k : Fin ((curve (key g role)).length-1))
    (h : j.val=k.val ∨ j.val=k.val+1)
    (p : Cell (piece g (.inr (.inl ⟨role,.inl j⟩))).width (piece g (.inr (.inl ⟨role,.inl j⟩))).height)
    (q : Cell (piece g (.inr (.inl ⟨role,.inr k⟩))).width (piece g (.inr (.inl ⟨role,.inr k⟩))).height)
    (he : ((offset g (.inr (.inl ⟨role,.inl j⟩))).1+p.1.val,(offset g (.inr (.inl ⟨role,.inl j⟩))).2+p.2.val)=
      ((offset g (.inr (.inl ⟨role,.inr k⟩))).1+q.1.val,(offset g (.inr (.inl ⟨role,.inr k⟩))).2+q.2.val)) :
    p∈(piece g (.inr (.inl ⟨role,.inl j⟩))).board.walls ↔ q∈(piece g (.inr (.inl ⟨role,.inr k⟩))).board.walls := by
  rcases j with ⟨j,hj⟩
  rcases k with ⟨k,hk⟩
  change j=k ∨ j=k+1 at h
  rcases h with h | h
  · subst j
    exact near_wall_contact (key g role) k (by omega) (initialPhase g role) (targetPhase g role) p q he
  · subst j
    exact far_wall_contact (key g role) k (by omega) (initialPhase g role) (targetPhase g role) p q he

private theorem short_sources (g : GateTileState) (role : Fin 3)
    (j : Fin (curve (key g role)).length) (k : Fin ((curve (key g role)).length-1))
    (h : j.val=k.val ∨ j.val=k.val+1)
    (l : Labels g (.inr (.inl ⟨role,.inl j⟩))) (m : Labels g (.inr (.inl ⟨role,.inr k⟩))) :
    ((offset g (.inr (.inl ⟨role,.inl j⟩))).1+((matching g (.inr (.inl ⟨role,.inl j⟩))).source l).1.val,
      (offset g (.inr (.inl ⟨role,.inl j⟩))).2+((matching g (.inr (.inl ⟨role,.inl j⟩))).source l).2.val)≠
    ((offset g (.inr (.inl ⟨role,.inr k⟩))).1+((matching g (.inr (.inl ⟨role,.inr k⟩))).source m).1.val,
      (offset g (.inr (.inl ⟨role,.inr k⟩))).2+((matching g (.inr (.inl ⟨role,.inr k⟩))).source m).2.val) := by
  rcases j with ⟨j,hj⟩
  rcases k with ⟨k,hk⟩
  change j=k ∨ j=k+1 at h
  rcases h with h | h
  · subst j
    exact near_source_disjoint (key g role) k (by omega) (initialPhase g role) (targetPhase g role) l m
  · subst j
    exact far_source_disjoint (key g role) k (by omega) (initialPhase g role) (targetPhase g role) l m

private theorem short_targets (g : GateTileState) (role : Fin 3)
    (j : Fin (curve (key g role)).length) (k : Fin ((curve (key g role)).length-1))
    (h : j.val=k.val ∨ j.val=k.val+1)
    (l : Labels g (.inr (.inl ⟨role,.inl j⟩))) (m : Labels g (.inr (.inl ⟨role,.inr k⟩))) :
    ((offset g (.inr (.inl ⟨role,.inl j⟩))).1+((matching g (.inr (.inl ⟨role,.inl j⟩))).target l).1.val,
      (offset g (.inr (.inl ⟨role,.inl j⟩))).2+((matching g (.inr (.inl ⟨role,.inl j⟩))).target l).2.val)≠
    ((offset g (.inr (.inl ⟨role,.inr k⟩))).1+((matching g (.inr (.inl ⟨role,.inr k⟩))).target m).1.val,
      (offset g (.inr (.inl ⟨role,.inr k⟩))).2+((matching g (.inr (.inl ⟨role,.inr k⟩))).target m).2.val) := by
  rcases j with ⟨j,hj⟩
  rcases k with ⟨k,hk⟩
  change j=k ∨ j=k+1 at h
  rcases h with h | h
  · subst j
    exact near_target_disjoint (key g role) k (by omega) (initialPhase g role) (targetPhase g role) l m
  · subst j
    exact far_target_disjoint (key g role) k (by omega) (initialPhase g role) (targetPhase g role) l m

theorem contactProofs (g : GateTileState) (f : FrontierContactProofs g) : ContactProofs g where
  walls := by
    intro i j hc p q he
    rcases i with coreI | (⟨roleI,lineI | cornerI⟩ | capI) <;>
      rcases j with coreJ | (⟨roleJ,lineJ | cornerJ⟩ | capJ)
    all_goals simp only [contact,decide_eq_true_eq,Bool.false_eq_true] at hc
    · exact buffer_walls g coreI coreJ p q he
    · exact f.walls coreI roleJ lineJ hc.1 hc.2 p q he
    · exact (f.walls coreJ roleI lineI hc.1 hc.2 q p he.symm).symm
    · have hrole := hc.1
      subst roleJ
      exact short_walls g roleI lineI cornerJ hc.2 p q he
    · have hrole := hc.1
      subst roleJ
      exact (short_walls g roleI lineJ cornerI hc.2 q p he.symm).symm
  sources := by
    intro i j hc l k he
    rcases i with coreI | (⟨roleI,lineI | cornerI⟩ | capI) <;>
      rcases j with coreJ | (⟨roleJ,lineJ | cornerJ⟩ | capJ)
    all_goals simp only [contact,decide_eq_true_eq,Bool.false_eq_true] at hc
    · cases buffer_source_owners g coreI coreJ l k he
      rfl
    · exact False.elim (f.sources coreI roleJ lineJ hc.1 hc.2 l k he)
    · exact False.elim (f.sources coreJ roleI lineI hc.1 hc.2 k l he.symm)
    · have hrole := hc.1
      subst roleJ
      exact False.elim (short_sources g roleI lineI cornerJ hc.2 l k he)
    · have hrole := hc.1
      subst roleJ
      exact False.elim (short_sources g roleI lineJ cornerI hc.2 k l he.symm)
  targets := by
    intro i j hc l k he
    rcases i with coreI | (⟨roleI,lineI | cornerI⟩ | capI) <;>
      rcases j with coreJ | (⟨roleJ,lineJ | cornerJ⟩ | capJ)
    all_goals simp only [contact,decide_eq_true_eq,Bool.false_eq_true] at hc
    · cases buffer_target_owners g coreI coreJ l k he
      rfl
    · exact False.elim (f.targets coreI roleJ lineJ hc.1 hc.2 l k he)
    · exact False.elim (f.targets coreJ roleI lineI hc.1 hc.2 k l he.symm)
    · have hrole := hc.1
      subst roleJ
      exact False.elim (short_targets g roleI lineI cornerJ hc.2 l k he)
    · have hrole := hc.1
      subst roleJ
      exact False.elim (short_targets g roleI lineJ cornerI hc.2 k l he.symm)

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
