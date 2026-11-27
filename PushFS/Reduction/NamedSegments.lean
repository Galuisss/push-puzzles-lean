/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.MiddleFlow

/-! Exact ordered instructions of one named source edge, retaining every actual source-layer connection. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction

def Route.edgeSegments (q : List Route × ℕ) : List Segment :=
  q.1.flatMap fun r => if r.edge=q.2 then r.path else []

@[fun_prop] theorem Route.edgeSegments_polyTime :
    ComputableInPolyTime Route.edgeSegments (encPair (encList encRoute) encUnary) (encList encSegment) := by
  unfold Route.edgeSegments
  fun_prop

theorem Route.mem_edgeSegments (rs : List Route) (e : ℕ) (s : Segment) :
    s ∈ edgeSegments (rs,e) ↔ ∃ r∈rs,r.edge=e ∧ s∈r.path := by
  constructor
  · intro hs
    obtain ⟨r,hr,hs⟩ := List.mem_flatMap.mp hs
    split_ifs at hs with he
    · exact ⟨r,hr,he,hs⟩
    · cases hs
  · rintro ⟨r,hr,he,hs⟩
    exact List.mem_flatMap.mpr ⟨r,hr,by simpa only [he,ite_true] using hs⟩

theorem Route.edgeSegments_trace (rs : List Route) (e : ℕ) (p : GridRouting.Point) :
    HasPoint (edgeSegments (rs,e)) p ↔ Trace rs e p := by
  constructor
  · rintro ⟨s,hs,hp⟩
    obtain ⟨r,hr,he,hs⟩ := (mem_edgeSegments rs e s).mp hs
    exact ⟨r,hr,he,s,hs,hp⟩
  · rintro ⟨r,hr,he,s,hs,hp⟩
    exact ⟨s,(mem_edgeSegments rs e s).mpr ⟨r,hr,he,hs⟩,hp⟩

theorem Route.edgeSegments_arcs (rs : List Route) (e : ℕ) (d : Direction) (p : GridRouting.Point) :
    HasArc (edgeSegments (rs,e)) d p ↔ ∃ r∈rs,r.edge=e ∧ ∃ s∈r.path,s.Arc d p := by
  constructor
  · rintro ⟨s,hs,hp⟩
    obtain ⟨r,hr,he,hs⟩ := (mem_edgeSegments rs e s).mp hs
    exact ⟨r,hr,he,s,hs,hp⟩
  · rintro ⟨r,hr,he,s,hs,hp⟩
    exact ⟨s,(mem_edgeSegments rs e s).mpr ⟨r,hr,he,hs⟩,hp⟩

theorem Route.edgeSegments_append (rs ts : List Route) (e : ℕ) :
    edgeSegments (rs++ts,e)=edgeSegments (rs,e)++edgeSegments (ts,e) := by simp [edgeSegments]

theorem Route.edgeSegments_translate (rs : List Route) (e dx dy : ℕ) :
    edgeSegments (rs.map (fun r=>r.translate dx dy),e)=
      (edgeSegments (rs,e)).map (fun s=>s.translate dx dy) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [edgeSegments,Route.translate] at ih
    by_cases he : r.edge=e <;> simp [edgeSegments,Route.translate,he,ih]

theorem Route.edgeSegments_refined (rs : List Route) (e : ℕ) :
    edgeSegments (rs.map Route.refined,e)=(edgeSegments (rs,e)).map Segment.refined := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [edgeSegments] at ih
    by_cases he : r.edge=e <;> simp [edgeSegments,Route.refined,he,ih]

private theorem flatMap_only {α β : Type} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (i : α) (hi : i∈xs) (f : α → List β) (hout : ∀ j∈xs,j≠i → f j=[]) : xs.flatMap f=f i := by
  induction xs with
  | nil => cases hi
  | cons j xs ih =>
    rcases List.nodup_cons.mp hn with ⟨hj,hn⟩
    by_cases he : j=i
    · subst j
      have hnil : xs.flatMap f=[] := List.flatMap_eq_nil_iff.mpr (by
        intro j hj'
        exact hout j (List.mem_cons_of_mem _ hj') (fun he => hj (he ▸ hj')))
      simp only [List.flatMap_cons,hnil,List.append_nil]
    · have hi' : i∈xs := (List.mem_cons.mp hi).resolve_left (Ne.symm he)
      have hj' : f j=[] := hout j (List.mem_cons_self ..) he
      rw [List.flatMap_cons,hj',List.nil_append]
      exact ih hn hi' (fun j hj' => hout j (List.mem_cons_of_mem _ hj'))

namespace Plan

/-- Filtering the actual layer by an old live edge leaves exactly its own full serialized connection. -/
theorem Layer.incoming_segments {l : Layer} (hn : Numbered l.before) (i : Fin l.before.wires.length) :
    Route.edgeSegments (l.connections,l.before.wires.getD i.val 0)=(l.incomingRoute i.val).path := by
  have hid : l.before.wires.getD i.val 0<l.before.next := hn.getD_lt i.isLt
  change ((List.range l.before.wires.length).map l.incomingRoute ++
    (List.range l.instruction.data.outputs.length).map l.createdRoute).flatMap _=_
  rw [List.flatMap_append,List.flatMap_map,List.flatMap_map]
  have hold : (List.range l.before.wires.length).flatMap
      (fun j=>if (l.incomingRoute j).edge=l.before.wires.getD i.val 0 then (l.incomingRoute j).path else [])=
      (l.incomingRoute i.val).path := by
    rw [flatMap_only _ List.nodup_range i.val (List.mem_range.mpr i.isLt)]
    · simp [Layer.incomingRoute]
    · intro j hj hji
      have he : l.before.wires.getD j 0≠l.before.wires.getD i.val 0 :=
        fun hh=>hji (hn.getD_injective (List.mem_range.mp hj) i.isLt hh)
      simp only [Layer.incomingRoute,he,ite_false]
  have hnew : (List.range l.instruction.data.outputs.length).flatMap
      (fun j=>if (l.createdRoute j).edge=l.before.wires.getD i.val 0 then (l.createdRoute j).path else [])=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    have he : l.before.next+j≠l.before.wires.getD i.val 0 := by omega
    simp only [Layer.createdRoute,he,ite_false]
  rw [hold,hnew,List.append_nil]

/-- Filtering by a newly created edge leaves exactly its actual vertex-to-cut instruction list. -/
theorem Layer.created_segments {l : Layer} (hn : Numbered l.before) (i : Fin l.instruction.data.outputs.length) :
    Route.edgeSegments (l.connections,l.before.next+i.val)=(l.createdRoute i.val).path := by
  change ((List.range l.before.wires.length).map l.incomingRoute ++
    (List.range l.instruction.data.outputs.length).map l.createdRoute).flatMap _=_
  rw [List.flatMap_append,List.flatMap_map,List.flatMap_map]
  have hold : (List.range l.before.wires.length).flatMap
      (fun j=>if (l.incomingRoute j).edge=l.before.next+i.val then (l.incomingRoute j).path else [])=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j hj
    have hj' := hn.getD_lt (List.mem_range.mp hj)
    have he : l.before.wires.getD j 0≠l.before.next+i.val := by omega
    simp only [Layer.incomingRoute,he,ite_false]
  have hnew : (List.range l.instruction.data.outputs.length).flatMap
      (fun j=>if (l.createdRoute j).edge=l.before.next+i.val then (l.createdRoute j).path else [])=
      (l.createdRoute i.val).path := by
    rw [flatMap_only _ List.nodup_range i.val (List.mem_range.mpr i.isLt)]
    · simp [Layer.createdRoute]
    · intro j _ hji
      have he : l.before.next+j≠l.before.next+i.val := by omega
      simp only [Layer.createdRoute,he,ite_false]
  rw [hold,hnew,List.nil_append]

end Plan
end PushPuzzle.PushFS.Reduction
