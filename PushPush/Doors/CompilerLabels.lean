/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.Basic

/-! Dense room labels for binary-labelled self-closing door networks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open Cslib.Complexity
open Turing.MultiTapeTM

namespace Source

attribute [local fun_prop] SelfClosingDoor.encTunnel_source_polyTime
  SelfClosingDoor.encTunnel_target_polyTime SelfClosingDoor.encDoor_zero_polyTime
  SelfClosingDoor.encDoor_one_polyTime SelfClosingDoor.encInstance_start_polyTime
  SelfClosingDoor.encInstance_target_polyTime SelfClosingDoor.encInstance_doors_polyTime

abbrev Instance := SelfClosingDoor.Instance
abbrev State := SelfClosingDoor.State

/-- The explicit endpoint table includes the start and target, with duplicates retained. -/
def labels (I : Instance) : List ℕ :=
  I.start :: I.target :: I.doors.flatMap (fun e =>
    [e.zero.source, e.zero.target, e.one.source, e.one.target])

theorem length_labels (I : Instance) : (labels I).length = 4 * I.doors.length + 2 := by
  simp only [labels, List.length_cons]
  induction I.doors with
  | nil => simp
  | cons e es ih => simp_all [List.flatMap_cons]; omega

/-- First-occurrence room labels have unary size bounded by the door count. -/
def rank (I : Instance) (location : ℕ) : ℕ := (labels I).idxOf location

theorem rank_lt (I : Instance) {v : ℕ} (hv : v ∈ labels I) :
    rank I v < 4 * I.doors.length + 2 := by
  rw [← length_labels]
  exact List.idxOf_lt_length_iff.mpr hv

theorem rank_eq_iff (I : Instance) {u v : ℕ} (hu : u ∈ labels I) :
    rank I u = rank I v ↔ u = v := List.idxOf_inj hu

@[simp] theorem start_mem (I : Instance) : I.start ∈ labels I := by simp [labels]
@[simp] theorem target_mem (I : Instance) : I.target ∈ labels I := by simp [labels]

theorem tunnel_source_mem (I : Instance) (i : Fin I.doors.length) (b : Bool) :
    (I.doors[i].tunnel b).source ∈ labels I := by
  have he : I.doors[i] ∈ I.doors := List.getElem_mem _
  have hm : (I.doors[i].tunnel b).source ∈
      I.doors.flatMap (fun e => [e.zero.source, e.zero.target, e.one.source, e.one.target]) := by
    apply List.mem_flatMap.mpr
    refine ⟨_, he, ?_⟩
    cases b <;> simp [SelfClosingDoor.Door.tunnel]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

theorem tunnel_target_mem (I : Instance) (i : Fin I.doors.length) (b : Bool) :
    (I.doors[i].tunnel b).target ∈ labels I := by
  have he : I.doors[i] ∈ I.doors := List.getElem_mem _
  have hm : (I.doors[i].tunnel b).target ∈
      I.doors.flatMap (fun e => [e.zero.source, e.zero.target, e.one.source, e.one.target]) := by
    apply List.mem_flatMap.mpr
    refine ⟨_, he, ?_⟩
    cases b <;> simp [SelfClosingDoor.Door.tunnel]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)

/-- Replace only location labels, preserving door identities and state bits. -/
def mapTunnel (f : ℕ → ℕ) (e : SelfClosingDoor.Tunnel) : SelfClosingDoor.Tunnel :=
  ⟨f e.source, f e.target⟩

/-- Both tunnels of the same original door retain their original index. -/
def mapDoor (f : ℕ → ℕ) (e : SelfClosingDoor.Door) : SelfClosingDoor.Door :=
  ⟨mapTunnel f e.zero, mapTunnel f e.one, e.initial⟩

/-- Relabel the player's room without altering the door register. -/
def mapState (f : ℕ → ℕ) (s : State) : State := ⟨f s.location, s.bits⟩

/-- Relabel all explicit endpoints and the two distinguished locations. -/
def mapInstance (f : ℕ → ℕ) (I : Instance) : Instance :=
  ⟨I.doors.map (mapDoor f), f I.start, f I.target⟩

@[simp] theorem mapDoor_tunnel (f : ℕ → ℕ) (e : SelfClosingDoor.Door) (b : Bool) :
    (mapDoor f e).tunnel b = mapTunnel f (e.tunnel b) := by
  cases b <;> rfl

@[simp] theorem mapInstance_initial (f : ℕ → ℕ) (I : Instance) :
    (mapInstance f I).initial = mapState f I.initial := by
  simp [mapInstance, mapState, SelfClosingDoor.Instance.initial, mapDoor, List.map_map]

theorem reachable_location_mem (I : Instance) {s : State}
    (hr : SelfClosingDoor.Reachable I.doors I.initial s) : s.location ∈ labels I := by
  induction hr with
  | refl => exact start_mem I
  | tail _ hs _ =>
    obtain ⟨_, i, _, rfl⟩ := hs
    exact tunnel_target_mem I i _

@[fun_prop] theorem labels_polyTime :
    ComputableInPolyTime labels SelfClosingDoor.encInstance (encList encNat) := by
  unfold labels
  fun_prop

@[fun_prop] theorem rank_polyTime :
    ComputableInPolyTime (fun q : Instance × ℕ => rank q.1 q.2)
      (encPair SelfClosingDoor.encInstance encNat) encUnary := by
  unfold rank
  fun_prop

end Source
end PushPuzzle.PushPush.Doors
