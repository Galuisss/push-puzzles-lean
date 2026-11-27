/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingWireCollars
public import PushS.FiniteSourceInventory

/-! Source macrocell contact geometry for the actual finite-force primitive emitter. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def macroShift (w : ℕ) (p a : ℕ × ℕ) : ℕ × ℕ :=
  (tileStride w*p.1+a.1,tileStride w*p.2+a.2)

theorem local_world_bounds (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (hc : PatchFits w (c.patch w hw))
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) :
    (c.world w hw p).1 < tileSide w ∧ (c.world w hw p).2 < tileSide w := by
  have hx := p.1.isLt
  have hy := p.2.isLt
  change c.offsetX w+(c.instanceOf w hw).width ≤ tileSide w ∧
    c.offsetY w+(c.instanceOf w hw).height ≤ tileSide w at hc
  dsimp [PrimitiveCode.world]
  omega

theorem local_actor_bounds (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (hc : PatchFits w (c.patch w hw))
    (goal : Bool) (l : c.Labels w) :
    (c.actor w hw goal l).1 < tileSide w ∧ (c.actor w hw goal l).2 < tileSide w :=
  local_world_bounds w hw c hc _

theorem local_actor_collar_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.actor w hw goal l) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_actor_collar_lane w hw g.2 c hc goal l face hf
    | inr q => exact wire_actor_collar_lane w hw q.2 c hc goal l face hf

theorem local_wall_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) (c.world w hw p) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_wall_collar_off_lane w hw g.2 c hc p hp face hf
    | inr q => exact wire_wall_collar_off_lane w hw q.2 c hc p hp face hf

theorem macro_axis_close (w x y a b : ℕ) (_ha : a < tileSide w) (hb : b < tileSide w)
    (he : tileStride w*x+a = tileStride w*y+b) : x ≤ y+1 := by
  by_contra h
  have hxy : y+2 ≤ x := by omega
  have hm := Nat.mul_le_mul_left (tileStride w) hxy
  simp only [Nat.mul_add,Nat.mul_two] at hm
  have hstride : 2*padding w+1 < tileStride w := by unfold tileStride spacing padding; omega
  unfold tileSide at hb
  omega

private theorem macro_axis_step (w x y a b : ℕ) (hxy : y = x+1)
    (he : tileStride w*x+a = tileStride w*y+b) : a = tileStride w+b := by
  rw [hxy,Nat.mul_add,Nat.mul_one] at he
  omega

theorem macro_axis_collar (w x y a b : ℕ) (ha : a < tileSide w) (hb : b < tileSide w)
    (he : tileStride w*x+a = tileStride w*y+b) (hne : x ≠ y) :
    (y = x+1 ∧ tileStride w ≤ a ∧ b ≤ 2*padding w) ∨
      (x = y+1 ∧ a ≤ 2*padding w ∧ tileStride w ≤ b) := by
  have hxy := macro_axis_close w x y a b ha hb he
  have hyx := macro_axis_close w y x b a hb ha he.symm
  rcases lt_or_gt_of_ne hne with h | h
  · have hs : y = x+1 := by omega
    have hm := macro_axis_step w x y a b hs he
    unfold tileSide at ha hb
    exact Or.inl ⟨hs,by omega,by omega⟩
  · have hs : x = y+1 := by omega
    have hm := macro_axis_step w y x b a hs he.symm
    unfold tileSide at ha hb
    exact Or.inr ⟨hs,by omega,by omega⟩

/-- Local port lanes and off-lane walls exclude every foreign macrocell wall, including diagonal overlaps. -/
theorem macro_actor_wall_ne (w : ℕ) (p r a b : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w) (hb : b.1 < tileSide w ∧ b.2 < tileSide w)
    (hactor : ∀ face, InCollar w face a → SameLane face (Line.along w face (boundaryPoint w face) 0) a)
    (hwall : ∀ face, InCollar w face b → ¬SameLane face (Line.along w face (boundaryPoint w face) 0) b)
    (hlocal : p = r → a ≠ b) : macroShift w p a ≠ macroShift w r b := by
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*p.1+a.1 = tileStride w*r.1+b.1 at hx
  change tileStride w*p.2+a.2 = tileStride w*r.2+b.2 at hy
  by_cases hpx : p.1 = r.1
  · have hax : a.1 = b.1 := by rw [hpx] at hx; omega
    by_cases hpy : p.2 = r.2
    · have hay : a.2 = b.2 := by rw [hpy] at hy; omega
      exact hlocal (Prod.ext hpx hpy) (Prod.ext hax hay)
    · rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with h | h
      · have hla := hactor .south h.2.1
        have hlb := hwall .north h.2.2
        dsimp [SameLane,Line.along,boundaryPoint] at hla hlb
        omega
      · have hla := hactor .north h.2.1
        have hlb := hwall .south h.2.2
        dsimp [SameLane,Line.along,boundaryPoint] at hla hlb
        omega
  · rcases macro_axis_collar w p.1 r.1 a.1 b.1 ha.1 hb.1 hx hpx with h | h
    · have hla := hactor .east h.2.1
      have hlb := hwall .west h.2.2
      dsimp [SameLane,Line.along,boundaryPoint] at hla hlb
      by_cases hpy : p.2 = r.2
      · rw [hpy] at hy
        omega
      · rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega
    · have hla := hactor .west h.2.1
      have hlb := hwall .east h.2.2
      dsimp [SameLane,Line.along,boundaryPoint] at hla hlb
      by_cases hpy : p.2 = r.2
      · rw [hpy] at hy
        omega
      · rcases macro_axis_collar w p.2 r.2 a.2 b.2 ha.2 hb.2 hy hpy with v | v
        all_goals simp only [tileStride,spacing,padding] at *; omega

end PushPuzzle.PushS.FiniteRouting
