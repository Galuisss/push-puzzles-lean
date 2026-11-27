/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Enclosed

/-! The finite phase-envelope test certifies actual separation of all goals in different physical primitives. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem mapped_index_mem {α β : Type} (xs : List α) (f : α→β) (n : ℕ) (hn : n<xs.length) (a : α) (ha : xs[n]=a) :
    (f a,n)∈(xs.map f).zipIdx := by
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simp only [List.getElem?_map,List.getElem?_eq_getElem hn,ha,Option.map_some]

/-- Every different pair of primitive indices is compared, with interval hulls used only as a proved shortcut. -/
private theorem envelopesApart_sound (g : GateTileState) (hc : envelopesApart g=true)
    (i j : Inventory.Index g) (hij : i≠j) (r s : Envelope) (hr : r∈envelopes g i) (hs : s∈envelopes g j)
    (p q : C) (hp : r.Contains (p.1.val,p.2.val)) (hq : s.Contains (q.1.val,q.2.val)) (d : Direction) :
    ¬Adjacent d p q := by
  obtain ⟨u,hu,heu⟩:=List.mem_iff_getElem.mp (Inventory.mem_indices g i)
  obtain ⟨v,hv,hev⟩:=List.mem_iff_getElem.mp (Inventory.mem_indices g j)
  have huv : u≠v := by rintro rfl; exact hij (heu.symm.trans hev)
  let f:=fun k : Inventory.Index g=>let es:=envelopes g k; (es,Envelope.hull es)
  have hmu:=mapped_index_mem (Inventory.indices g) f u hu i heu
  have hmv:=mapped_index_mem (Inventory.indices g) f v hv j hev
  have hh:=List.all_eq_true.mp (List.all_eq_true.mp hc (f i,u) hmu) (f j,v) hmv
  by_cases hsep : (Envelope.hull (envelopes g i)).Apart (Envelope.hull (envelopes g j))
  · exact Envelope.apart_not_adjacent _ _ p q (Envelope.hull_contains _ r hr _ hp)
      (Envelope.hull_contains _ s hs _ hq) hsep d
  · have hnot : ¬(u=v ∨(Envelope.hull (envelopes g i)).Apart (Envelope.hull (envelopes g j))) :=
      not_or.mpr ⟨huv,hsep⟩
    change (if u=v ∨(Envelope.hull (envelopes g i)).Apart (Envelope.hull (envelopes g j)) then true else
      (envelopes g i).all fun r=>(envelopes g j).all fun s=>decide (r.Apart s))=true at hh
    rw [ite_eq_right hnot] at hh
    have ht:=of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hh r hr) s hs)
    exact Envelope.apart_not_adjacent r s p q hp hq ht d

theorem targets_of_different_primitives (g : GateTileState) (hc : envelopesApart g=true)
    (i j : Inventory.Index g) (hij : i≠j) (l : Inventory.Labels g i) (k : Inventory.Labels g j) (d : Direction) :
    ¬Adjacent d (rawTarget g ⟨i,l⟩) (rawTarget g ⟨j,k⟩) := by
  obtain ⟨r,hr,hp⟩:=raw_target_enclosed g i l
  obtain ⟨s,hs,hq⟩:=raw_target_enclosed g j k
  exact envelopesApart_sound g hc i j hij r s hr hs _ _ hp hq d

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
