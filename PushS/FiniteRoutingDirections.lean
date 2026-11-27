/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCompilerBounds

/-! Actual directed corner contracts of all emitted gate and wire paths. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

instance (d e : Direction) : Decidable (Perpendicular d e) := by unfold Perpendicular; infer_instance

theorem segmentDirection_of_travels (d : Direction) (p q : ℕ × ℕ) (length : ℕ)
    (h : Travels d p q length) (hl : 0 < length) : segmentDirection ⟨p,q⟩ = d := by
  cases d <;> dsimp [Travels,segmentDirection] at * <;>
    split_ifs <;> first | rfl | omega

theorem segmentDirection_of_runs (d : Direction) (p q : ℕ × ℕ)
    (h : PortAnnulus.Runs d p q) : segmentDirection ⟨p,q⟩ = d := by
  cases d <;> dsimp [PortAnnulus.Runs,segmentDirection] at * <;>
    split_ifs <;> first | rfl | omega

theorem segmentDirection_scale (factor : ℕ) (hf : 0 < factor) (s : Segment) :
    segmentDirection (scaleSegment factor s) = segmentDirection s := by
  simp only [segmentDirection,scaleSegment,scalePoint,Nat.mul_left_cancel_iff hf,Nat.mul_lt_mul_left hf]

def adapterDirections (role : Fin 3) : List Direction :=
  if role = 0 then [.west,.north,.west,.south,.west]
  else if role = 1 then [.north,.east,.north,.west,.north]
  else [.east,.south,.east,.north,.east]

private theorem adapter_runs (w : ℕ) (kind : Bool) (role : Fin 3) :
    List.Forall₂ (fun s d => PortAnnulus.Runs d s.start s.finish)
      (adapter w kind role) (adapterDirections role) := by
  cases kind <;> fin_cases role <;>
    simp [adapter,adapterVertices,corePort,adapterDirections,PortAnnulus.Runs,spacing] <;> omega

private theorem directions_of_runs {segments : List Segment} {directions : List Direction}
    (h : List.Forall₂ (fun s d => PortAnnulus.Runs d s.start s.finish) segments directions) :
    segments.map segmentDirection = directions := by
  induction h with
  | nil => rfl
  | @cons s d segments directions hs ht ih =>
    rw [List.map_cons,segmentDirection_of_runs d s.start s.finish hs,ih]

private theorem adapter_directions (w : ℕ) (kind : Bool) (role : Fin 3) :
    (adapter w kind role).map segmentDirection = adapterDirections role :=
  directions_of_runs (adapter_runs w kind role)

private theorem curve_directions (w : ℕ) (q : Key) :
    (curve w q).map segmentDirection = (PortAnnulus.curve q).map segmentDirection := by
  simp only [curve,List.map_map]
  congr 1
  funext s
  exact segmentDirection_scale _ (spacing_pos w) s

private def Allowed (d e : Direction) : Prop := d = e ∨ Perpendicular d e

private instance (d e : Direction) : Decidable (Allowed d e) := by unfold Allowed; infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_directions_chain : ∀ q : Key,
    ((PortAnnulus.curve q).map segmentDirection).IsChain Allowed := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem source_first_direction : ∀ q : Key,
    ((PortAnnulus.curve q).map segmentDirection).headD .north = PortAnnulus.innerDirection q.2.2 := by
  decide +kernel

private theorem curve_first_direction (w : ℕ) (q : Key) :
    ((curve w q).map segmentDirection).headD .north = PortAnnulus.innerDirection q.2.2 := by
  rw [curve_directions]
  exact source_first_direction q

private theorem option_getD_of_mem {α : Type} {o : Option α} {a : α} (fallback : α)
    (ha : a ∈ o) : o.getD fallback = a := by cases o <;> simp_all

/-- The full raw route has only genuine right/left turns and its one collinear adapter seam. -/
private theorem route_directions_chain (w : ℕ) (kind : Bool) (q : Key) :
    ((route w kind q).map segmentDirection).IsChain (fun d e => d = e ∨ Perpendicular d e) := by
  change ((route w kind q).map segmentDirection).IsChain Allowed
  rw [route,List.map_append]
  apply List.IsChain.append
  · rw [adapter_directions]
    rcases q with ⟨p,r,role⟩
    fin_cases role <;> simp [adapterDirections,Allowed,Perpendicular,rightTurn,Direction.opposite]
  · rw [curve_directions]
    exact source_directions_chain q
  · intro d hd e he
    have hd' : d = PortAnnulus.innerDirection q.2.2 := by
      rw [adapter_directions] at hd
      rcases q with ⟨p,r,role⟩
      fin_cases role <;> simpa [adapterDirections,PortAnnulus.innerDirection,eq_comm] using hd
    have he' : e = PortAnnulus.innerDirection q.2.2 := by
      have hh := option_getD_of_mem .north he
      have hh' : ((curve w q).map segmentDirection).headD .north = e := by
        simpa only [List.headD_eq_head?_getD] using hh
      exact hh'.symm.trans (curve_first_direction w q)
    exact Or.inl (hd'.trans he'.symm)

theorem armRoute_directions (w : ℕ) (g : GateTileState) (role : Fin 3) :
    (armRoute w g role).map segmentDirection =
      (route w g.core.isAND (g.pattern,g.rotation,role)).map segmentDirection := by
  apply List.ext_getElem
  · simp [armRoute]
  · intro i hi hj
    have hi' : i < (route w g.core.isAND (g.pattern,g.rotation,role)).length := by
      simpa only [armRoute,List.length_map,List.length_mapIdx] using hi
    have hr := route_segment_good w g.core.isAND (g.pattern,g.rotation,role)
      (List.mem_iff_getElem.mpr ⟨i,hi',rfl⟩)
    simp only [armRoute,List.getElem_map,List.getElem_mapIdx]
    split_ifs with hlast
    · have hbit := Bool.toNat_le (g.incoming.get role)
      have hsum : 0+(g.incoming.get role).toNat ≤
          segmentLength ((route w g.core.isAND (g.pattern,g.rotation,role))[i]) := by omega
      have ht := advance_travels _ _ _ _ 0 (g.incoming.get role).toNat
        (segment_travels _ hr.1) hsum
      have hz : ∀ d p, advance d p 0 = p := by intro d p; cases d <;> simp [advance]
      simp only [hz] at ht
      exact segmentDirection_of_travels _ _ _ _ ht (by have hh := hr.2.1; omega)
    · rfl

theorem armRoute_directions_chain (w : ℕ) (g : GateTileState) (role : Fin 3) :
    ((armRoute w g role).map segmentDirection).IsChain (fun d e => d = e ∨ Perpendicular d e) := by
  rw [armRoute_directions]
  exact route_directions_chain w g.core.isAND _

theorem wireRoute_directions_chain (w : ℕ) (kind : Catalog.Kind) :
    ((wireRoute w kind).map segmentDirection).IsChain (fun d e => d = e ∨ Perpendicular d e) := by
  cases kind <;> simp [wireRoute,wireVertices,segmentDirection,Perpendicular,rightTurn,
    Direction.opposite,tileStride,spacing]

end PushPuzzle.PushS.FiniteRouting
