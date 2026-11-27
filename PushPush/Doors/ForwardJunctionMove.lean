/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardJunction
public import PushPush.Doors.ForwardSignal

/-! Full physical endpoint selection inside a location or binary-choice chamber. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

/-- Select the northern or southern endpoint of a junction. -/
def endpointUsed (I : Instance) (v j : ℕ) (south : Bool) : Bool :=
  if south then lowerUsed I v j else upperUsed I v j

/-- The signal stops one row inside its selected endpoint cap. -/
def endpointOffset (I : Instance) (south : Bool) : ℕ := if south then chamberHeight I - 3 else 3

/-- The corresponding fixed cap is two rows inside the chamber divider. -/
def endpointCap (I : Instance) (south : Bool) : ℕ := if south then chamberHeight I - 2 else 2

/-- A chosen source endpoint has its actual ordinary cap box in the fixed inventory. -/
private theorem endpoint_cap_mem (storage : Bool) (I : Instance) (v j : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I) (south : Bool)
    (hused : endpointUsed I v j south = true) :
    ((layout storage I).rackX - 1,
      roomBase I v j + endpointCap I south + (layout storage I).shift) ∈ (layout storage I).fixed := by
  have hh := chamberHeight_ge I
  have hcap : roomBase I v j + endpointCap I south ∈ (layout storage I).caps := by
    apply List.mem_flatMap.mpr
    refine ⟨v, List.mem_range.mpr hv, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_range.mpr hj, ?_⟩
    cases south
    · simp only [endpointUsed, Bool.false_eq_true, ite_false] at hused
      simp [endpointCap, hused]
    · simp only [endpointUsed, ite_true] at hused
      have he : roomBase I v j + (chamberHeight I - 2) = roomBase I v j + chamberHeight I - 2 := by omega
      simp [endpointCap, hused, he]
  apply Finset.mem_union_right
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨roomBase I v j + endpointCap I south, List.mem_append_right _ hcap, rfl⟩

namespace Stock

variable {I : Instance}

/-- An arriving signal slides to either available exit while all door registers stay fixed. -/
theorem junction_exit (storage : Bool) (S : Stock I) (v j offset : ℕ)
    (hv : v < (labels I).length) (hj : j < slots I)
    (hlo : 3 < offset) (hhi : offset + 3 < chamberHeight I)
    (south : Bool) (hused : endpointUsed I v j south = true)
    (hsignal : S.signal = ((layout storage I).rackX - 1,
      roomBase I v j + offset + (layout storage I).shift)) :
    Finite.Reachable 1 (S.canonical storage)
      (({S with signal := ((layout storage I).rackX - 1,
        roomBase I v j + endpointOffset I south + (layout storage I).shift)} : Stock I).canonical storage) := by
  have hh := chamberHeight_ge I
  have he : 2 < endpointOffset I south ∧ endpointOffset I south + 2 < chamberHeight I := by
    cases south <;> simp only [endpointOffset, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hc : endpointCap I south < chamberHeight I := by
    cases south <;> simp only [endpointCap, Bool.false_eq_true, ite_false, ite_true] <;> omega
  let source := roomCell storage I v j offset hv hj (by omega)
  let dest := roomCell storage I v j (endpointOffset I south) hv hj (by omega)
  let stop := roomCell storage I v j (endpointCap I south) hv hj hc
  let supportOffset := if south then offset - 1 else offset + 1
  have hu : 2 < supportOffset ∧ supportOffset + 2 < chamberHeight I := by
    cases south <;> dsimp [supportOffset] <;> omega
  let support := roomCell storage I v j supportOffset hv hj (by omega)
  let d : Direction := if south then .south else .north
  have hsource : source ∉ S.stationary storage :=
    S.stationary_junction_clear storage v j source rfl (by dsimp [source]; omega) (by dsimp [source]; omega)
  have hsupport_free : support ∉ S.stationary storage :=
    S.stationary_junction_clear storage v j support rfl (by dsimp [support]; omega) (by dsimp [support]; omega)
  have hsupport_ne : support ≠ source := by
    intro heq
    have heq := congrArg (fun p => p.2.val) heq
    cases south <;> dsimp [support, source, supportOffset] at heq <;> omega
  have hstop : stop ∈ S.stationary storage := by
    apply ((layout storage I).mem_raster _ _).mpr
    exact Finset.mem_union_left _ (endpoint_cap_mem storage I v j hv hj south hused)
  have hr := S.slide_signal storage d source dest stop support hsignal
    (layout storage I).working_mem_columns (layout storage I).working_mem_columns
    (by dsimp [source]; omega) (by dsimp [dest]; omega) hsource
    (by simpa only [Finset.mem_insert, not_or] using And.intro hsupport_ne hsupport_free)
  apply hr
  · cases south <;> simp [d, Adjacent, source, support, supportOffset, roomCell, workCell, Layout.point] <;> omega
  · cases south <;> simp [d, Direction.lane, source, dest, roomCell, workCell, Layout.point]
  · cases south <;>
      simp only [d, Bool.false_eq_true, ite_false, ite_true, Direction.position]
      <;> dsimp [source, dest] <;> simp only [endpointOffset, Bool.false_eq_true, ite_false, ite_true] <;> omega
  · intro p hl hstart hend
    have hpx : p.1.val = (layout storage I).rackX - 1 := by
      cases south <;> simpa [d, Direction.lane, source] using hl
    apply S.stationary_junction_clear storage v j p hpx
    all_goals
      cases south <;> simp only [d, Bool.false_eq_true, ite_false, ite_true, Direction.position] at hstart hend
      <;> dsimp [source, dest] at hstart hend
      <;> simp only [endpointOffset, Bool.false_eq_true, ite_false, ite_true] at hstart hend <;> omega
  · cases south <;> simp [d, Adjacent, dest, stop, endpointOffset, endpointCap,
      roomCell, workCell, Layout.point] <;> omega
  · exact hstop

end Stock
end PushPuzzle.PushPush.Doors.Source
