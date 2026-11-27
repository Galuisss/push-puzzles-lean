/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRouting
import Mathlib.Tactic.FinCases

/-! Explicit integer adapters from each unchanged thick core to its annular ports. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

/-- The actual no-inflow slot of each complete core's west, north, and east port. -/
def corePort (w : ℕ) (kind : Bool) (role : Fin 3) : ℕ × ℕ :=
  let c := 25 * spacing w
  if role = 0 then
    if kind then (c-8*w-16,c-6*w-21) else (c-2*w-7,c)
  else if role = 1 then
    if kind then (c+3,c-8*w-31) else (c+4,c-2*w-13)
  else if kind then (c+3*w+12,c) else (c+3*w+13,c)

/-- The outermost physical AND box on each of the three complete core tails. -/
def andPortLabel (w : ℕ) (role : Fin 3) : FiniteGeometry.AndLabel w :=
  if role = 0 then .west ⟨w+3, by omega⟩
  else if role = 1 then .branchB ⟨4*w+15, by omega⟩
  else .branchC ⟨w+4, by omega⟩

def orPortLabel (w : ℕ) (role : Fin 3) : FiniteGeometry.OrLabel w :=
  if role = 0 then .left ⟨w+4, by omega⟩
  else if role = 1 then .branchB ⟨w+6, by omega⟩
  else .branchC ⟨w+4, by omega⟩

/-- The source inward bit at a physical W/N/E port. -/
def portInflow (a b c : Bool) (role : Fin 3) : Bool :=
  if role = 0 then a else if role = 1 then b else !c

/-- One actual outward unit step represents inward supply to a gate. -/
def portPosition (role : Fin 3) (p : ℕ × ℕ) (inflow : Bool) : ℕ × ℕ :=
  if role = 0 then (p.1-inflow.toNat,p.2)
  else if role = 1 then (p.1,p.2-inflow.toNat)
  else (p.1+inflow.toNat,p.2)

/-- The adapter anchor is exactly the named normal AND endpoint's no-inflow slot. -/
theorem andPort_position (w : ℕ) (a b c : Bool) (role : Fin 3) :
    (coreOffset w + (FiniteGeometry.andPoint w a b c (andPortLabel w role)).1,
      coreOffset w + (FiniteGeometry.andPoint w a b c (andPortLabel w role)).2) =
    portPosition role (corePort w true role) (portInflow a b c role) := by
  cases a <;> cases b <;> cases c <;> fin_cases role <;>
    apply Prod.ext <;>
    simp [andPortLabel, FiniteGeometry.andPoint, coreOffset, FiniteGeometry.origin,
      portPosition, corePort, portInflow, spacing] <;> omega

theorem orPort_position (w : ℕ) (a b c : Bool) (role : Fin 3) :
    (coreOffset w + (FiniteGeometry.orPoint w a b c (orPortLabel w role)).1,
      coreOffset w + (FiniteGeometry.orPoint w a b c (orPortLabel w role)).2) =
    portPosition role (corePort w false role) (portInflow a b c role) := by
  cases a <;> cases b <;> cases c <;> fin_cases role <;>
    apply Prod.ext <;>
    simp [orPortLabel, FiniteGeometry.orPoint, coreOffset, FiniteGeometry.origin,
      portPosition, corePort, portInflow, spacing] <;> omega

/-- Six literal waypoints give five long orthogonal segments for each real port. -/
def adapterVertices (w : ℕ) (kind : Bool) (role : Fin 3) : List (ℕ × ℕ) :=
  let s := spacing w
  let p := corePort w kind role
  if role = 0 then
    [p,(24*s,p.2),(24*s,23*s),(22*s,23*s),(22*s,25*s),(20*s,25*s)]
  else if role = 1 then
    [p,(p.1,24*s),(27*s,24*s),(27*s,22*s),(25*s,22*s),(25*s,20*s)]
  else [p,(26*s,p.2),(26*s,27*s),(28*s,27*s),(28*s,25*s),(30*s,25*s)]

def adapter (w : ℕ) (kind : Bool) (role : Fin 3) : List Segment :=
  (adapterVertices w kind role).zipWith Segment.mk (adapterVertices w kind role).tail

theorem adapter_length (w : ℕ) (kind : Bool) (role : Fin 3) :
    (adapter w kind role).length = 5 := by
  fin_cases role <;> simp [adapter, adapterVertices]

/-- The actual small core offsets are joined to the table's exact inner anchors. -/
theorem adapter_endpoints (w : ℕ) (kind : Bool) (role : Fin 3) :
    (adapterVertices w kind role).headD (0,0) = corePort w kind role ∧
      (adapterVertices w kind role).getLastD (0,0) =
        scalePoint (spacing w) (PortAnnulus.innerPoint role) ∧
      PortAnnulus.Runs (PortAnnulus.innerDirection role) (corePort w kind role)
        ((adapterVertices w kind role).getD 1 (0,0)) ∧
      PortAnnulus.Runs (PortAnnulus.innerDirection role)
        ((adapterVertices w kind role).getD 4 (0,0))
        (scalePoint (spacing w) (PortAnnulus.innerPoint role)) := by
  cases kind <;> fin_cases role <;>
    simp [adapterVertices, corePort, scalePoint, PortAnnulus.innerPoint,
      PortAnnulus.innerDirection, PortAnnulus.Runs, spacing] <;> omega

theorem adapter_joined (w : ℕ) (kind : Bool) (role : Fin 3) :
    (adapter w kind role).IsChain (fun s t => s.finish = t.start) := by
  fin_cases role <;> simp [adapter, adapterVertices, List.isChain_cons_cons]

/-- Every adapter segment has room for width-`w` utilities and a linear walking margin. -/
theorem adapter_segment_length (w : ℕ) (kind : Bool) (role : Fin 3)
    {s : Segment} (hs : s ∈ adapter w kind role) :
    (s.start.1 = s.finish.1 ∧ min s.start.2 s.finish.2 + FiniteGeometry.origin w ≤
      max s.start.2 s.finish.2) ∨
    (s.start.2 = s.finish.2 ∧ min s.start.1 s.finish.1 + FiniteGeometry.origin w ≤
      max s.start.1 s.finish.1) := by
  cases kind <;> fin_cases role <;>
    simp [adapter, adapterVertices, corePort, spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    simp [FiniteGeometry.origin] <;> omega

/-- The adapter's complete trace fits in the same explicit tile as the annulus. -/
theorem adapter_trace_bounded (w : ℕ) (kind : Bool) (role : Fin 3) {p : ℕ × ℕ}
    (hp : ∃ s ∈ adapter w kind role, s.Contains p) :
    p.1 < side w ∧ p.2 < side w := by
  obtain ⟨s, hs, hp⟩ := hp
  have hb := Segment.coordinate_bounds hp
  cases kind <;> fin_cases role <;>
    simp [adapter, adapterVertices, corePort, spacing] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    dsimp [side, spacing] at * <;> omega

end PushPuzzle.PushS.FiniteRouting
