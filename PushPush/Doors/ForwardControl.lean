/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardJunctionMove
public import PushPush.Doors.ForwardUpdate
public import PushPush.Doors.WireSourceMembers

/-! Composing physical room and wire macros in the source network's original port order. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

/-- The rack's working-column point on a logical chamber row. -/
def atRow (storage : Bool) (I : Instance) (row : ℕ) : ℕ × ℕ :=
  ((layout storage I).rackX - 1, row + (layout storage I).shift)

/-- The concrete wire execution interface used by the finite controller composition. -/
def WireSimulation (storage : Bool) (I : Instance) : Prop :=
  ∀ (S : Stock I) (e : Wire), e ∈ (layout storage I).wires →
    S.signal = atRow storage I e.source →
    atRow storage I e.target ∉ S.registerPoints storage →
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := atRow storage I e.target} : Stock I).canonical storage)

namespace Stock

variable {I : Instance}

theorem registerPoint_before (storage : Bool) (S : Stock I) {p : ℕ × ℕ}
    (hp : p ∈ S.registerPoints storage) : p.2 < 90 * I.doors.length + (layout storage I).shift := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hi := i.isLt
  have hr := Register.row_bounds (S.register i)
  dsimp
  unfold doorBase
  omega

theorem junction_input_ready (storage : Bool) (S : Stock I) (v j p : ℕ) :
    atRow storage I (inputRow I v j p) ∉ S.registerPoints storage := by
  intro hp
  have hp := S.registerPoint_before storage hp
  dsimp [atRow, inputRow, roomBase] at hp
  omega

theorem door_input_ready (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    (incoming : Register) (hne : S.register i ≠ incoming) :
    atRow storage I (doorBase i.val + incoming.row) ∉ S.registerPoints storage := by
  intro hp
  obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
  have hj := Register.row_bounds (S.register j)
  have hi := Register.row_bounds incoming
  have hy := congrArg Prod.snd he
  dsimp [atRow] at hy
  have hji : j = i := by apply Fin.ext; unfold doorBase at hy; omega
  subst j
  apply hne
  apply Register.row_injective
  omega

/-- The actual chamber move selects an available upper output from any input slot. -/
theorem junction_upper_single (storage : Bool) (S : Stock I) (v j p : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (hp : p < slots I)
    (hused : upperUsed I v j = true)
    (hsignal : S.signal = atRow storage I (inputRow I v j p)) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := atRow storage I (upperRow I v j)} : Stock I).canonical storage) := by
  have hs : S.signal = ((layout storage I).rackX - 1,
      roomBase I v j + (10 + 8 * p) + (layout storage I).shift) := by
    simpa only [atRow, inputRow, Nat.add_assoc] using hsignal
  have hhi : 10 + 8 * p + 3 < chamberHeight I := by unfold chamberHeight; omega
  exact S.junction_exit storage v j (10 + 8 * p) hv hj (by omega) hhi false hused hs

theorem junction_upper (storage : Bool) (S : Stock I) (v j p : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (hp : p < slots I)
    (hused : upperUsed I v j = true)
    (hsignal : S.signal = atRow storage I (inputRow I v j p)) :
    Reachable (S.canonical storage)
      (({S with signal := atRow storage I (upperRow I v j)} : Stock I).canonical storage) :=
  (S.junction_upper_single storage v j p hv hj hp hused hsignal).unlimited

/-- The actual chamber move selects its lower skip output from any input slot. -/
private theorem junction_lower (storage : Bool) (S : Stock I) (v j p : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (hp : p < slots I)
    (hused : lowerUsed I v j = true)
    (hsignal : S.signal = atRow storage I (inputRow I v j p)) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := atRow storage I (lowerRow I v j)} : Stock I).canonical storage) := by
  have hs : S.signal = ((layout storage I).rackX - 1,
      roomBase I v j + (10 + 8 * p) + (layout storage I).shift) := by
    simpa only [atRow, inputRow, Nat.add_assoc] using hsignal
  have hhi : 10 + 8 * p + 3 < chamberHeight I := by unfold chamberHeight; omega
  have hr := S.junction_exit storage v j (10 + 8 * p) hv hj (by omega) hhi true hused hs
  have he : roomBase I v j + endpointOffset I true = lowerRow I v j := by
    dsimp [endpointOffset, lowerRow]
    have := chamberHeight_ge I
    omega
  simpa only [he, atRow] using hr

end Stock

namespace Stock

variable {I : Instance}

/-- Skip one candidate door channel through its real lower exit and private wire. -/
private theorem skip (storage : Bool) (S : Stock I) (hwire : WireSimulation storage I) (v j p : ℕ)
    (hv : v < (labels I).length) (hj : j < 2 * I.doors.length) (hp : p < slots I)
    (hnt : v ≠ rank I I.target)
    (hsignal : S.signal = atRow storage I (inputRow I v j p)) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := atRow storage I (inputRow I v (j + 1) 0)} : Stock I).canonical storage) := by
  have hlow : lowerUsed I v j = true := by simp [lowerUsed, hnt, hj]
  have hr := S.junction_lower storage v j p hv (by unfold slots; omega) hp hlow hsignal
  let next : Stock I := {S with signal := atRow storage I (lowerRow I v j)}
  have hw := hwire next ⟨lowerRow I v j, false, inputRow I v (j + 1) 0, true⟩
    (skip_wire_mem storage I v j hv hj hnt) rfl (next.junction_input_ready storage v (j + 1) 0)
  exact hr.trans hw

/-- Follow the real binary-choice chain to an arbitrary candidate channel. -/
private theorem skip_to (storage : Bool) (S : Stock I) (hwire : WireSimulation storage I) (v k p : ℕ)
    (hv : v < (labels I).length) (hk : k ≤ 2 * I.doors.length) (hp : p < slots I)
    (hnt : v ≠ rank I I.target)
    (hsignal : S.signal = atRow storage I (inputRow I v 0 p)) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := atRow storage I (inputRow I v k (if k = 0 then p else 0))} :
        Stock I).canonical storage) := by
  induction k with
  | zero =>
    have he : ({S with signal := atRow storage I (inputRow I v 0 p)} : Stock I) = S :=
      eq_of_register_signal rfl hsignal.symm
    simpa only [ite_true, he] using
      (Relation.ReflTransGen.refl : Finite.Reachable 1 (S.canonical storage) (S.canonical storage))
  | succ k ih =>
    have hr := ih (by omega)
    let current : Stock I :=
      {S with signal := atRow storage I (inputRow I v k (if k = 0 then p else 0))}
    have hslot : (if k = 0 then p else 0) < slots I := by
      split
      · exact hp
      · exact slots_pos I
    have hs := current.skip storage hwire v k (if k = 0 then p else 0)
      hv (by omega) hslot hnt rfl
    simpa only [Nat.succ_ne_zero, ite_false] using hr.trans hs

end Stock

namespace Stock

variable {I : Instance}

/-- Select one actual enabled-location candidate and enter its physical check slot. -/
theorem choose (storage : Bool) (S : Stock I) (hwire : WireSimulation storage I) (v k p : ℕ)
    (hv : v < (labels I).length) (hk : k < 2 * I.doors.length) (hp : p < slots I)
    (hnt : v ≠ rank I I.target) (hsource : rank I (channel I k).source = v)
    (hsignal : S.signal = atRow storage I (inputRow I v 0 p))
    (hready : atRow storage I (doorBase (k / 2) + (if channelBit k then 50 else 40)) ∉
      S.registerPoints storage) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := atRow storage I (doorBase (k / 2) + (if channelBit k then 50 else 40))} :
        Stock I).canonical storage) := by
  have hr := S.skip_to storage hwire v k p hv hk.le hp hnt hsignal
  let current : Stock I :=
    {S with signal := atRow storage I (inputRow I v k (if k = 0 then p else 0))}
  have hslot : (if k = 0 then p else 0) < slots I := by
    split
    · exact hp
    · exact slots_pos I
  have hused : upperUsed I v k = true := by simp [upperUsed, hnt, hk, hsource]
  have hu := current.junction_upper_single storage v k (if k = 0 then p else 0)
    hv (by unfold slots; omega) hslot hused rfl
  let launched : Stock I := {current with signal := atRow storage I (upperRow I v k)}
  have hw := hwire launched
    ⟨upperRow I v k, true, doorBase (k / 2) + (if channelBit k then 50 else 40), !channelBit k⟩
    (choice_wire_mem storage I v k hv hk hnt hsource) rfl hready
  exact hr.trans (hu.trans hw)

end Stock
end PushPuzzle.PushPush.Doors.Source
