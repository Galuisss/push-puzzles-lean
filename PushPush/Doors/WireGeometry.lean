/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.LayoutGeometry
public import PushPush.Doors.WireCorner

/-! The private wire levels and the actual right-angle corner geometry. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction Adjacent)

namespace Layout

theorem wire_levels_separated (L : Layout) (i : ℕ) (e : Wire) :
    L.wireY i e + 10 ≤ L.wireV i e ∨ L.wireV i e + 10 ≤ L.wireY i e := by
  cases hs : e.sourceSouth <;> cases ht : e.targetSouth <;>
    simp [wireY, wireV, level, shift, hs, ht] <;> omega

theorem wireY_source_gap (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (hsource : e.source ≤ L.depth) :
    if e.sourceSouth then e.source + L.shift + 10 ≤ L.wireY i e
    else L.wireY i e + 10 ≤ e.source + L.shift := by
  cases hs : e.sourceSouth <;> simp [wireY, level, shift, hs] <;> omega

theorem wireV_target_gap (L : Layout) (i : ℕ) (e : Wire) (hi : i < L.wires.length)
    (htarget : e.target ≤ L.depth) :
    if e.targetSouth then L.wireV i e + 10 ≤ e.target + L.shift
    else e.target + L.shift + 10 ≤ L.wireV i e := by
  cases ht : e.targetSouth <;> simp [wireV, level, shift, ht] <;> omega

/-- Adjacent columns beside each private vertical track contain no initial pin. -/
theorem pin_not_in_free_column (L : Layout) (i : ℕ) (j : ℕ) (f : Wire)
    {p : ℕ × ℕ} (hp : p ∈ L.wirePins j f) :
    p.1 ≠ wireA i + 1 ∧ p.1 ≠ wireB i - 1 ∧ p.1 ≠ wireC i + 1 := by
  simp only [wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [wireA, wireB, wireC] <;> omega

end Layout

namespace Wire

variable {w h : ℕ}

private theorem corner_east (signal previous stop : Cell w h)
    (hside : previous.1 = signal.1 ∧
      (previous.2.val + 1 = signal.2.val ∨ previous.2.val = signal.2.val + 1))
    (hlane : stop.2 = signal.2) (hgap : signal.1.val + 3 ≤ stop.1.val) :
    Corner .east signal previous stop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hside.2 with hn | hs
    · exact ⟨.north, hside.1, hn⟩
    · exact ⟨.south, hside.1, hs⟩
  · simp only [Direction.lane]
    rcases hside.2 with hn | hs <;> omega
  · exact congrArg Fin.val hlane
  · simp only [Direction.position]
    omega

private theorem corner_west (signal previous stop : Cell w h)
    (hside : previous.1 = signal.1 ∧
      (previous.2.val + 1 = signal.2.val ∨ previous.2.val = signal.2.val + 1))
    (hlane : stop.2 = signal.2) (hgap : stop.1.val + 3 ≤ signal.1.val) :
    Corner .west signal previous stop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hside.2 with hn | hs
    · exact ⟨.north, hside.1, hn⟩
    · exact ⟨.south, hside.1, hs⟩
  · simp only [Direction.lane]
    rcases hside.2 with hn | hs <;> omega
  · exact congrArg Fin.val hlane
  · simp only [Direction.position]
    omega

private theorem corner_south (signal previous stop : Cell w h)
    (hside : previous.2 = signal.2 ∧
      (previous.1.val + 1 = signal.1.val ∨ previous.1.val = signal.1.val + 1))
    (hlane : stop.1 = signal.1) (hgap : signal.2.val + 3 ≤ stop.2.val) :
    Corner .south signal previous stop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hside.2 with hw | he
    · exact ⟨.west, hw, hside.1⟩
    · exact ⟨.east, he, hside.1⟩
  · simp only [Direction.lane]
    rcases hside.2 with hw | he <;> omega
  · exact congrArg Fin.val hlane
  · simp only [Direction.position]
    omega

private theorem corner_north (signal previous stop : Cell w h)
    (hside : previous.2 = signal.2 ∧
      (previous.1.val + 1 = signal.1.val ∨ previous.1.val = signal.1.val + 1))
    (hlane : stop.1 = signal.1) (hgap : stop.2.val + 3 ≤ signal.2.val) :
    Corner .north signal previous stop := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hside.2 with hw | he
    · exact ⟨.west, hw, hside.1⟩
    · exact ⟨.east, he, hside.1⟩
  · simp only [Direction.lane]
    rcases hside.2 with hw | he <;> omega
  · exact congrArg Fin.val hlane
  · simp only [Direction.position]
    omega

/-- Direction of the leg leaving one of the five private wire corners. -/
def privateDirection (L : Layout) (i : ℕ) (e : Doors.Wire) (j : Fin 5) : Direction :=
  match j.val with
  | 0 => if e.sourceSouth then .south else .north
  | 1 => .east
  | 2 => if L.wireY i e < L.wireV i e then .south else .north
  | 3 => .west
  | _ => if e.targetSouth then .south else .north

/-- The literal eight-point route and six pins form the five private corners. -/
theorem layout_private_corner (L : Layout) (i : ℕ) (e : Doors.Wire) (hi : i < L.wires.length)
    (hsource : e.source ≤ L.depth) (htarget : e.target ≤ L.depth) (j : Fin 5)
    (signal previous stop : Cell L.width L.height)
    (hsignal : (signal.1.val, signal.2.val) = (L.wirePath i e).getD (j.val + 1) (0, 0))
    (hprevious : (previous.1.val, previous.2.val) = (L.wirePins i e).getD j.val (0, 0))
    (hstop : (stop.1.val, stop.2.val) = (L.wirePins i e).getD (j.val + 1) (0, 0)) :
    Corner (privateDirection L i e j) signal previous stop := by
  have hY := L.wireY_source_gap i e hi hsource
  have hV := L.wireV_target_gap i e hi htarget
  have hYV := L.wire_levels_separated i e
  have hYpos : 0 < L.wireY i e := by
    unfold Layout.wireY Layout.level
    split <;> omega
  have hVpos : 0 < L.wireV i e := by
    unfold Layout.wireV Layout.level
    split <;> omega
  rcases j with ⟨j, hj⟩
  have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hjcases with rfl | rfl | rfl | rfl | rfl
  · simp [Layout.wirePath, Layout.wirePins] at hsignal hprevious hstop
    cases hs : e.sourceSouth
    · simp [privateDirection, hs] at hY ⊢
      apply corner_north
      · exact ⟨Fin.ext (by omega), Or.inl (by dsimp [Layout.wireA] at *; omega)⟩
      · exact Fin.ext (by omega)
      · simp [Layout.beside, hs] at hstop
        omega
    · simp [privateDirection, hs] at hY ⊢
      apply corner_south
      · exact ⟨Fin.ext (by omega), Or.inl (by dsimp [Layout.wireA] at *; omega)⟩
      · exact Fin.ext (by omega)
      · simp [Layout.beside, hs] at hstop
        omega
  · simp [Layout.wirePath, Layout.wirePins] at hsignal hprevious hstop
    change Corner .east signal previous stop
    apply corner_east
    · refine ⟨Fin.ext (by omega), ?_⟩
      cases hs : e.sourceSouth <;> simp [Layout.beside, hs] at hprevious <;> omega
    · exact Fin.ext (by omega)
    · dsimp [Layout.wireA, Layout.wireB] at *
      omega
  · simp [Layout.wirePath, Layout.wirePins] at hsignal hprevious hstop
    by_cases hlt : L.wireY i e < L.wireV i e
    · simp [privateDirection, hlt] at hstop ⊢
      apply corner_south
      · exact ⟨Fin.ext (by omega), Or.inr (by omega)⟩
      · exact Fin.ext (by omega)
      · simp [Layout.beside] at hstop
        omega
    · simp [privateDirection, hlt] at hstop ⊢
      apply corner_north
      · exact ⟨Fin.ext (by omega), Or.inr (by omega)⟩
      · exact Fin.ext (by omega)
      · simp [Layout.beside] at hstop
        omega
  · simp [Layout.wirePath, Layout.wirePins] at hsignal hprevious hstop
    change Corner .west signal previous stop
    apply corner_west
    · refine ⟨Fin.ext (by omega), ?_⟩
      by_cases hlt : L.wireY i e < L.wireV i e <;>
        simp [Layout.beside, hlt] at hprevious <;> omega
    · exact Fin.ext (by omega)
    · dsimp [Layout.wireB, Layout.wireC] at *
      omega
  · simp [Layout.wirePath, Layout.wirePins] at hsignal hprevious hstop
    cases ht : e.targetSouth
    · simp [privateDirection, ht] at hV ⊢
      apply corner_north
      · exact ⟨Fin.ext (by omega), Or.inl (by dsimp [Layout.wireC] at *; omega)⟩
      · exact Fin.ext (by omega)
      · simp [Layout.beside, ht] at hstop
        omega
    · simp [privateDirection, ht] at hV ⊢
      apply corner_south
      · exact ⟨Fin.ext (by omega), Or.inl (by dsimp [Layout.wireC] at *; omega)⟩
      · exact Fin.ext (by omega)
      · simp [Layout.beside, ht] at hstop
        omega

/-- The extra attraction after reversing the B-column pin, when both signs agree. -/
theorem layout_B_same_sign (L : Layout) (i : ℕ) (e : Doors.Wire)
    (hsame : decide (L.wireY i e < L.wireV i e) = e.sourceSouth)
    (near previous extra remote : Cell L.width L.height)
    (hnear : (near.1.val, near.2.val) =
      (Layout.wireB i, Layout.beside (decide (L.wireY i e < L.wireV i e)) (L.wireY i e)))
    (hprevious : (previous.1.val, previous.2.val) = (Layout.wireB i, L.wireY i e))
    (hextra : (extra.1.val, extra.2.val) = (Layout.wireB i + 1, L.wireY i e))
    (hremote : (remote.1.val, remote.2.val) =
      (Layout.wireA i, Layout.beside e.sourceSouth (L.wireY i e))) :
    Corner .west near previous remote ∧ Adjacent .east previous extra := by
  have hYpos : 0 < L.wireY i e := by
    unfold Layout.wireY Layout.level
    split <;> omega
  simp only [Prod.mk.injEq] at hnear hprevious hextra hremote
  constructor
  · apply corner_west
    · refine ⟨Fin.ext (by omega), ?_⟩
      rw [hsame] at hnear
      cases hs : e.sourceSouth <;> simp [Layout.beside, hs] at hnear <;> omega
    · apply Fin.ext
      rw [hsame] at hnear
      omega
    · dsimp [Layout.wireA, Layout.wireB] at *
      omega
  · exact ⟨by omega, Fin.ext (by omega)⟩

/-- The symmetric extra attraction after reversing the C-column pin. -/
theorem layout_C_same_sign (L : Layout) (i : ℕ) (e : Doors.Wire)
    (hsame : e.targetSouth = decide (L.wireY i e < L.wireV i e))
    (near previous extra remote : Cell L.width L.height)
    (hnear : (near.1.val, near.2.val) =
      (Layout.wireC i, Layout.beside e.targetSouth (L.wireV i e)))
    (hprevious : (previous.1.val, previous.2.val) = (Layout.wireC i, L.wireV i e))
    (hextra : (extra.1.val, extra.2.val) = (Layout.wireC i - 1, L.wireV i e))
    (hremote : (remote.1.val, remote.2.val) =
      (Layout.wireB i, Layout.beside (decide (L.wireY i e < L.wireV i e)) (L.wireV i e))) :
    Corner .east near previous remote ∧ Adjacent .west previous extra := by
  have hVpos : 0 < L.wireV i e := by
    unfold Layout.wireV Layout.level
    split <;> omega
  simp only [Prod.mk.injEq] at hnear hprevious hextra hremote
  constructor
  · apply corner_east
    · refine ⟨Fin.ext (by omega), ?_⟩
      cases hs : e.targetSouth <;> simp [Layout.beside, hs] at hnear <;> omega
    · apply Fin.ext
      rw [hsame] at hnear
      omega
    · dsimp [Layout.wireB, Layout.wireC] at *
      omega
  · constructor
    · dsimp [Layout.wireC] at *
      omega
    · exact Fin.ext (by omega)

end Wire
end PushPuzzle.PushPush.Doors
