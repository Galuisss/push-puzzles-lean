/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramFrame
public import PushS.PortStreetSeparation
public import PushS.PortWalkBudget
import all PushS.PortSegments

/-! The marked source's actual multilevel acceptance-round schedule. -/

public section

namespace PushPuzzle.PushS.PortLayout

/-- Actual guard columns recomputed from the marked emitter's fixed geometry. -/
def acceptanceGuardCoordinates (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  guardColumns l (coordinates p) (l.fixedSegments p)

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- An actual emitted auxiliary column, retaining its page and first interlevel marker. -/
structure PageColumn where
  column : ℕ
  level : ℕ
  privateColumn : Bool

/-- The actual ordinary f/r columns and the lower gate's four public and one private columns. -/
def pageColumns (l : PortLayout) (p : Scales.Parameters) (side : Side) : List PageColumn :=
  ((l.endpoints.filter fun e => e.side == side).flatMap fun e =>
    [⟨EndpointStreet.f.column p e, e.level, false⟩, ⟨EndpointStreet.r.column p e, e.level, false⟩]) ++
  if side = .lower then
    l.gateCenterCoordinates.flatMap fun i =>
      [⟨p.x i - 2, 1, false⟩, ⟨p.x i + 4, 1, true⟩,
        ⟨p.x i + 6, 1, false⟩, ⟨p.x i + 8, 1, false⟩, ⟨p.x i + 12, 1, false⟩]
  else []

/-- All true main axes in their original port numbering. -/
def axes (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  ((List.range l.portCount).map p.x).toFinset

/-- The original gate-center axes. -/
def cores (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  (l.gateCenterCoordinates.map p.x).toFinset

/-- All original non-frame streets other than the main axes. -/
def auxiliaries (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  (l.streetColumnCoordinates p).toFinset \ (axes l p ∪ {0, p.W})

/-- The actual marked far horizontal separator columns. -/
def guards (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  (l.acceptanceGuardCoordinates p).toFinset

/-- The lower gate's two independent short-train sample columns. -/
def samples (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  (l.gateCenterCoordinates.flatMap fun i => [p.x i + 2, p.x i + 10]).toFinset

/-- The emitter's complete two-page working rows, including the outer frame. -/
def workRows (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  ([0, p.H] ++ (l.workingDepthCoordinates p).flatMap fun y => [y, p.H - y]).toFinset

/-- All central, half-depth, and successive-level acceptance rows. -/
def cutRows (p : Scales.Parameters) : Finset ℕ :=
  ([p.D, p.H - p.Y 1 / 2] ++ (List.range (p.levels - 1)).flatMap fun k =>
    let y := (p.Y (k + 1) + p.Y (k + 2)) / 2
    [y, p.H - y]).toFinset

/-- All upper-axis probe rows emitted by the actual upper endpoints. -/
def probeRows (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  ((l.endpoints.filter fun e => e.side == .upper).map fun e => p.Y e.level + 2).toFinset

def prefixRequests (lanes : Finset ℕ) (span : ℕ → ℕ) : List (ℕ × ℕ) :=
  lanes.sort.map fun lane => (lane, span lane)

def readRows (p : Scales.Parameters) (side : Direction) (rows : Finset ℕ) : Template :=
  .read side (prefixRequests rows fun _ => p.W + 1)

def readColumns (p : Scales.Parameters) (side : Direction) (cols : Finset ℕ) : Template :=
  .read side (prefixRequests cols fun _ => p.H + 1)

/-- Depth of the first interlevel marker, or the outer central flank at the deepest level. -/
def trimDepth (p : Scales.Parameters) (level : ℕ) : ℕ :=
  if level < p.levels then (p.Y level + p.Y (level + 1)) / 2 else p.D - 2

def trimRound (l : PortLayout) (p : Scales.Parameters) (side : Side) : Template :=
  .read (if side = .upper then .north else .south)
    (((pageColumns l p side).filter fun a => !a.privateColumn).map fun a =>
      (a.column, trimDepth p a.level))

private def mainTop (l : PortLayout) (p : Scales.Parameters) : Template :=
  .read .north ((l.endpoints.filter fun e => e.side == .upper).map fun e => (p.x e.port, p.Y e.level + 2))

private def mainBottom (l : PortLayout) (p : Scales.Parameters) : Template :=
  .read .south ((l.endpoints.filter fun e => e.side == .lower).map fun e => (p.x e.port, p.Y e.level + 2))

private def live (l : PortLayout) (p : Scales.Parameters) (side : Side) : Finset ℕ :=
  (((pageColumns l p side).filter fun a => decide (1 ≤ a.level ∧ a.level < p.levels)).map PageColumn.column).toFinset

private def levelColumns (l : PortLayout) (p : Scales.Parameters) (side : Side) (j : ℕ) : Finset ℕ :=
  (((pageColumns l p side).filter fun a => a.level == j).map PageColumn.column).toFinset

private def lowerFinish (p : Scales.Parameters) (cols : Finset ℕ) : Template :=
  .read .south (prefixRequests cols fun _ => p.D + 1)

/-- Two blocks per allocated nondeepest level, with the lower half-depth check kept separate. -/
def pageChecks (l : PortLayout) (p : Scales.Parameters) (side : Side) : List Template :=
  (if side = .lower then
    [lowerFinish p (auxiliaries l p \ live l p side),
      readRows p .west {p.H - p.Y 1 / 2}, .clear .north (cores l p)]
   else [.clear .north (auxiliaries l p \ live l p side)]) ++
  (List.range (p.levels - 1)).flatMap fun k =>
    let j := k + 1
    let y := (p.Y j + p.Y (j + 1)) / 2
    [readRows p .west {if side = .upper then y else p.H - y},
      if side = .lower then lowerFinish p (levelColumns l p side j)
      else .clear .north (levelColumns l p side j)]

/-- The source rows retained until the main-axis and marker probes have completed. -/
def keepRows (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  workRows l p ∪ cutRows p ∪ {p.D - 2, p.D + 2, p.D - 4, p.D + 4}

/-- The temporary neighboring rows around every allocated work level, on both pages. -/
def neighboringRows (p : Scales.Parameters) : Finset ℕ :=
  ((List.range p.levels).flatMap fun k =>
    let y := p.Y (k + 1)
    [y - 1, y + 1, p.H - (y - 1), p.H - (y + 1)]).toFinset

/-- The exact row set allowed by the first post-trim row clear. -/
def firstRowKeep (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  keepRows l p ∪ neighboringRows p

/-- The two inner side bands cleared immediately after reading the full frame. -/
def sideBands (p : Scales.Parameters) (k : ℕ) : Finset ℕ :=
  (Finset.range (p.W + 1)).filter fun x => (1 ≤ x ∧ x ≤ k) ∨ (p.W - k ≤ x ∧ x < p.W)

/-- The first thirteen actual-source rounds, through the upper horizontal-guard marker. -/
def preparation (l : PortLayout) (p : Scales.Parameters) (interiorHoles : ℕ) : List Template :=
  let k := interiorHoles
  let keep := keepRows l p
  let neighbors := neighboringRows p
  let privateCols := (((pageColumns l p .lower).filter PageColumn.privateColumn).map PageColumn.column).toFinset
  frameSchedule p.W p.H ++
    [.clear .north (sideBands p k),
      trimRound l p .lower, trimRound l p .upper,
      .clear .west (Finset.range (p.H + 1) \ (keep ∪ neighbors)), mainTop l p, mainBottom l p,
      .clear .west (Finset.range (p.H + 1) \ (keep ∪ {p.H - p.Y 1 - 1})),
      .read .south (prefixRequests privateCols fun _ => p.Y 1 + 3),
      readRows p .east {p.D - 2, p.D + 2},
      .read .north (prefixRequests (guards l p) fun _ => p.D - 4), readRows p .west {p.D - 4}]

/-- The complete actual two-page schedule, before expanding any round into its separate lines. -/
def schedule (l : PortLayout) (p : Scales.Parameters) (interiorHoles : ℕ) : List Template :=
  let ordinary := axes l p \ cores l p
  let lowerWork := p.H - p.Y 1
  preparation l p interiorHoles ++
    [readRows p .west (probeRows l p), .clear .east (probeRows l p),
      .read .north (prefixRequests ordinary (fun _ => p.H + 1) ++ prefixRequests (cores l p) (fun _ => lowerWork)),
      .clear .north ordinary,
      .clear .west (Finset.range (p.H + 1) \ (workRows l p ∪ cutRows p ∪ {p.D + 4})),
      .read .north (prefixRequests (cores l p) fun _ => lowerWork + 1),
      readColumns p .south (guards l p), .clear .north (guards l p),
      .read .south (prefixRequests (samples l p) fun _ => p.D - 4), readRows p .east {p.D + 4},
      readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p)),
      .clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p))] ++
    pageChecks l p .lower ++ pageChecks l p .upper

/-- Preparation uses thirteen blocks, independently of the number of emitted lines. -/
theorem preparation_length (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    (preparation l p k).length = 13 := by simp only [preparation, frameSchedule,
      List.length_append, List.length_cons, List.length_nil]

/-- Each page contributes two blocks per nondeepest level. -/
theorem pageChecks_length (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    (pageChecks l p side).length = (if side = .lower then 3 else 1) + 2 * (p.levels - 1) := by
  cases side <;> simp [pageChecks, List.length_flatMap, Nat.mul_comm] <;> omega

/-- The actual full multilevel schedule has only a linear number of same-direction blocks. -/
theorem schedule_length (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    (schedule l p k).length = 4 * p.levels + 25 := by
  simp only [schedule, List.length_append, preparation_length, pageChecks_length,
    List.length_cons, List.length_nil, ite_true, ite_false, reduceCtorEq]
  have := p.levels_pos
  omega

end PushPuzzle.Push.AcceptanceProgram
