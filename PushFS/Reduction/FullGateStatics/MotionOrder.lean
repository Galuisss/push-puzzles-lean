/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.MotionEnclosed
public import PushFS.Reduction.FullGateStatics.MotionsChecked

/-! Disjoint full motion intervals preserve physical order across primitive owners. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem mapped_index_mem {α β : Type} (xs : List α) (f : α→β) (n : ℕ) (hn : n<xs.length) (a : α) (ha : xs[n]=a) :
    (f a,n)∈(xs.map f).zipIdx := by
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simp only [List.getElem?_map,List.getElem?_eq_getElem hn,ha,Option.map_some]

theorem interval_order (r s : Envelope) (p q u v : ℕ×ℕ)
    (hp : r.Contains p) (hq : s.Contains q) (hu : r.Contains u) (hv : s.Contains v)
    (ha : r.MotionApart s) :
    (p.2=q.2 →p.1<q.1 →u.1<v.1) ∧(p.1=q.1 →p.2<q.2 →u.2<v.2) := by
  dsimp only [Envelope.Contains,Envelope.MotionApart] at *
  constructor <;> intros <;> omega

private theorem motions_order (g : GateTileState) (hc : motionsApart g=true)
    (i j : Inventory.Index g) (hij : i≠j) (r s : Envelope) (hr : r∈motionEnvelopes g i) (hs : s∈motionEnvelopes g j)
    (p q u v : ℕ×ℕ) (hp : r.Contains p) (hq : s.Contains q) (hu : r.Contains u) (hv : s.Contains v) :
    (p.2=q.2 →p.1<q.1 →u.1<v.1) ∧(p.1=q.1 →p.2<q.2 →u.2<v.2) := by
  obtain ⟨a,ha,hea⟩:=List.mem_iff_getElem.mp (Inventory.mem_indices g i)
  obtain ⟨b,hb,heb⟩:=List.mem_iff_getElem.mp (Inventory.mem_indices g j)
  have hab : a≠b:=by rintro rfl; exact hij (hea.symm.trans heb)
  let f:=fun k : Inventory.Index g=>let es:=motionEnvelopes g k; (es,Envelope.hull es)
  have hma:=mapped_index_mem (Inventory.indices g) f a ha i hea
  have hmb:=mapped_index_mem (Inventory.indices g) f b hb j heb
  have hh:=List.all_eq_true.mp (List.all_eq_true.mp hc (f i,a) hma) (f j,b) hmb
  by_cases hsep : (Envelope.hull (motionEnvelopes g i)).MotionApart (Envelope.hull (motionEnvelopes g j))
  · exact interval_order _ _ p q u v (Envelope.hull_contains _ r hr _ hp) (Envelope.hull_contains _ s hs _ hq)
      (Envelope.hull_contains _ r hr _ hu) (Envelope.hull_contains _ s hs _ hv) hsep
  · have hnot : ¬(a=b ∨(Envelope.hull (motionEnvelopes g i)).MotionApart (Envelope.hull (motionEnvelopes g j))) :=
      not_or.mpr ⟨hab,hsep⟩
    change (if a=b ∨(Envelope.hull (motionEnvelopes g i)).MotionApart (Envelope.hull (motionEnvelopes g j)) then true else
      (motionEnvelopes g i).all fun r=>(motionEnvelopes g j).all fun s=>decide (r.MotionApart s))=true at hh
    rw [ite_eq_right hnot] at hh
    have ht:=of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hh r hr) s hs)
    exact interval_order r s p q u v hp hq hu hv ht

/-- Different primitive identities retain both coordinate orders whenever their source slots share a rail. -/
theorem different_primitive_order (g : GateTileState) (i j : Inventory.Index g) (hij : i≠j)
    (l : Inventory.Labels g i) (k : Inventory.Labels g j) :
    ((rawSource g ⟨i,l⟩).2=(rawSource g ⟨j,k⟩).2 →
      (rawSource g ⟨i,l⟩).1.val<(rawSource g ⟨j,k⟩).1.val →
      (rawTarget g ⟨i,l⟩).1.val<(rawTarget g ⟨j,k⟩).1.val) ∧
    ((rawSource g ⟨i,l⟩).1=(rawSource g ⟨j,k⟩).1 →
      (rawSource g ⟨i,l⟩).2.val<(rawSource g ⟨j,k⟩).2.val →
      (rawTarget g ⟨i,l⟩).2.val<(rawTarget g ⟨j,k⟩).2.val) := by
  obtain ⟨r,hr,hp,hu⟩:=raw_motion_enclosed g i l
  obtain ⟨s,hs,hq,hv⟩:=raw_motion_enclosed g j k
  have hh:=motions_order g (motionsApart_all g) i j hij r s hr hs _ _ _ _ hp hq hu hv
  exact ⟨fun he ho=>hh.1 (congrArg Fin.val he) ho,fun he ho=>hh.2 (congrArg Fin.val he) ho⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
