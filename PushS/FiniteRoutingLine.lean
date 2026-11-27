/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTools
public import Mathlib.Data.List.Nodup

/-! Exact unit-box emission along the long straight fragments of a finite-force route. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS FiniteGeometry

/-- Ordinary spacing-two stock and the two concrete thick-wall tools. -/
inductive Atom
  | line (count : ℕ)
  | flip
  | parity
  deriving DecidableEq

def Atom.span (w : ℕ) : Atom → ℕ
  | .line n => 2*n
  | .flip => 2*w+2
  | .parity => FiniteTools.paritySpan w+2

def span (w : ℕ) (atoms : List Atom) : ℕ := (atoms.map (Atom.span w)).sum

@[simp] theorem span_nil (w : ℕ) : span w [] = 0 := rfl

@[simp] theorem span_cons (w : ℕ) (a : Atom) (atoms : List Atom) :
    span w (a::atoms) = a.span w + span w atoms := rfl

@[simp] theorem span_append (w : ℕ) (a b : List Atom) :
    span w (a++b) = span w a + span w b := by simp [span]

/-- Stock between neighboring tools keeps their full wall collars apart. -/
def buffer (w : ℕ) : ℕ := w+5

/-- Two mandatory face crossings, followed by the requested side and parity corrections. -/
def initialAtoms (w : ℕ) (switch odd : Bool) : List Atom :=
  [.line (buffer w), .flip, .line (buffer w), .flip] ++
    (if switch then [.line (buffer w), .flip] else []) ++
    (if odd then [.line (buffer w), .parity] else [])

/-- Exact length including the final stock collar, before the remaining even stock. -/
def budget (w : ℕ) (switch odd : Bool) : ℕ :=
  10*w+34 + (if switch then 4*w+12 else 0) +
    (if odd then FiniteTools.paritySpan w+2*w+12 else 0)

private theorem initialAtoms_span (w : ℕ) (switch odd : Bool) :
    span w (initialAtoms w switch odd) + 2*buffer w = budget w switch odd := by
  cases switch <;> cases odd <;> simp [initialAtoms, budget, buffer, Atom.span] <;> omega

private theorem budget_bound (w : ℕ) (switch odd : Bool) : budget w switch odd ≤ 17*w+61 := by
  have hm := FiniteTools.paritySpan_bounds w
  cases switch <;> cases odd <;> simp [budget] <;> omega

private theorem budget_parity (w : ℕ)
    (switch odd : Bool) : budget w switch odd % 2 = odd.toNat := by
  have hm := FiniteTools.paritySpan_odd w
  cases switch <;> cases odd <;> simp [budget] <;> omega

/-- A concrete program ending at the requested exact integer endpoint. -/
def program (w length : ℕ) (switch : Bool) : List Atom :=
  let odd := decide (length % 2 = 1)
  initialAtoms w switch odd ++ [.line (buffer w + (length-budget w switch odd)/2)]

theorem program_span_of_bound (w length : ℕ) (switch : Bool) (hl : 17*w+61 ≤ length) :
    span w (program w length switch) = length := by
  have hb := budget_bound w switch (decide (length % 2 = 1))
  have hp := initialAtoms_span w switch (decide (length % 2 = 1))
  have hm := budget_parity w switch (decide (length % 2 = 1))
  have he : (decide (length % 2 = 1) : Bool).toNat = length % 2 := by
    by_cases h : length % 2 = 1
    · simp [h]
    · have h0 : length % 2 = 0 := by omega
      simp [h0]
  rw [he] at hm
  simp only [program, span_append, span_cons, span_nil, Atom.span, Nat.add_zero]
  omega

def Atom.Valid (w : ℕ) : Atom → Prop
  | .line n => buffer w ≤ n
  | .flip | .parity => True

/-- Every emitted ordinary stock segment has a complete thick wall collar. -/
theorem program_valid (w length : ℕ) (switch : Bool) :
    ∀ a ∈ program w length switch, a.Valid w := by
  intro a ha
  cases a with
  | line n =>
    cases switch <;> by_cases h : length % 2 = 1 <;>
      simp [program, initialAtoms, h] at ha <;>
      simp only [Atom.Valid] <;> omega
  | flip | parity => trivial

/-- One side bit records the wall side at each atom's entry. -/
def Atom.nextSide (above : Bool) : Atom → Bool
  | .flip => !above
  | .line _ | .parity => above

def exitSide (above : Bool) : List Atom → Bool
  | [] => above
  | a::atoms => exitSide (a.nextSide above) atoms

theorem exitSide_append (above : Bool) (a b : List Atom) :
    exitSide above (a++b) = exitSide (exitSide above a) b := by
  induction a generalizing above with
  | nil => rfl
  | cons a atoms ih => exact ih (a.nextSide above)

/-- Only the requested side correction changes the wall side across the full program. -/
theorem program_exitSide (w length : ℕ) (switch above : Bool) :
    exitSide above (program w length switch) = if switch then !above else above := by
  cases above <;> cases switch <;> by_cases h : length % 2 = 1 <;>
    simp [program, initialAtoms, h, exitSide, Atom.nextSide]

/-- Scalar coordinates of an atom's owned boxes; its final interface belongs to its successor. -/
def Atom.positions (w : ℕ) (q : Bool) : Atom → List ℕ
  | .line n => (List.range n).map fun i => 2*i+q.toNat
  | .flip => [q.toNat,w+3*q.toNat]
  | .parity => [q.toNat]

/-- All actual working boxes, including the final shared endpoint exactly once. -/
def positions (w : ℕ) (q : Bool) : List Atom → List ℕ
  | [] => [q.toNat]
  | a::atoms => a.positions w q ++ (positions w q atoms).map (a.span w + ·)

/-- Owned atom slots precede its successor's interface by at least one empty cell. -/
theorem Atom.positions_bounds (w : ℕ) (hw : 2 ≤ w) (q : Bool) (a : Atom)
    {x : ℕ} (hx : x ∈ a.positions w q) :
    q.toNat ≤ x ∧ x+2 ≤ a.span w+q.toNat := by
  have hq := Bool.toNat_le q
  have hm := FiniteTools.paritySpan_bounds w
  cases a with
  | line n =>
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    dsimp [Atom.span]
    omega
  | flip =>
    simp only [Atom.positions, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> dsimp [Atom.span] <;> omega
  | parity =>
    have he := List.mem_singleton.mp hx
    subst x
    dsimp [Atom.span]
    omega

theorem positions_bounds (w : ℕ) (hw : 2 ≤ w) (q : Bool) (atoms : List Atom)
    {x : ℕ} (hx : x ∈ positions w q atoms) :
    q.toNat ≤ x ∧ x ≤ span w atoms+q.toNat := by
  induction atoms generalizing x with
  | nil =>
    have he := List.mem_singleton.mp hx
    subst x
    simp [span]
  | cons a atoms ih =>
    rcases List.mem_append.mp hx with hx | hx
    · have hh := a.positions_bounds w hw q hx
      simp only [span_cons]
      omega
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      have hh := ih hy
      simp only [span_cons]
      omega

theorem Atom.positions_pairwise (w : ℕ) (hw : 2 ≤ w) (q : Bool) (a : Atom) :
    (a.positions w q).Pairwise (fun x y => x+2 ≤ y) := by
  have hq := Bool.toNat_le q
  cases a with
  | line n =>
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [Atom.positions, List.length_map, List.length_range] at hi hj
    simp only [Atom.positions, List.getElem_map, List.getElem_range]
    omega
  | flip => simp [Atom.positions]; omega
  | parity => simp [Atom.positions]

/-- Complete normal inventories retain an empty cell between every two physical boxes. -/
theorem positions_pairwise (w : ℕ) (hw : 2 ≤ w) (q : Bool) (atoms : List Atom)
    : (positions w q atoms).Pairwise (fun x y => x+2 ≤ y) := by
  induction atoms with
  | nil => simp [positions]
  | cons a atoms ih =>
    apply List.pairwise_append.mpr
    refine ⟨a.positions_pairwise w hw q, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact ih.imp (by intro x y hxy; omega)
    · intro x hx y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have hh := a.positions_bounds w hw q hx
      have ht := positions_bounds w hw q atoms hz
      omega

theorem positions_nodup (w : ℕ) (hw : 2 ≤ w) (q : Bool) (atoms : List Atom)
    : (positions w q atoms).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  exact (positions_pairwise w hw q atoms).imp (by intro x y hxy; omega)

/-- Full rectangular walls of one atom, in the same local coordinate window as the tools. -/
def Atom.rectangles (w offset : ℕ) (above : Bool) : Atom → List Rectangle :=
  let r := FiniteTools.radius w
  let x := r+offset
  let near := if above then r-w else r+1
  let far := if above then r+1 else r-w
  fun a => match a with
  | .line n => [⟨x,near,2*n+2,w⟩]
  | .parity => [⟨x,near,FiniteTools.paritySpan w+4,w⟩,
      ⟨x+2,far,FiniteTools.paritySpan w,w⟩]
  | .flip => [⟨x,near,w+1,w⟩, ⟨x+w+2,near,w,w⟩,
      ⟨x+2,far,w,w⟩, ⟨x+w+3,far,w+1,w⟩]

/-- The complete literal wall rectangle list of an emitted straight program. -/
def rectangles (w offset : ℕ) (above : Bool) : List Atom → List Rectangle
  | [] => []
  | a::atoms => a.rectangles w offset above ++ rectangles w (offset+a.span w) (a.nextSide above) atoms

/-- Every emitted wall rectangle has both dimensions at least the prescribed wall width. -/
private theorem Atom.rectangles_thick (w offset : ℕ) (above : Bool) (a : Atom) (ha : a.Valid w)
    {r : Rectangle} (hr : r ∈ a.rectangles w offset above) : w ≤ r.width ∧ w ≤ r.height := by
  have hm := FiniteTools.paritySpan_bounds w
  cases a with
  | line n =>
    have hn : buffer w ≤ n := ha
    simp only [Atom.rectangles, List.mem_singleton] at hr
    subst r
    dsimp
    unfold buffer at hn
    omega
  | flip =>
    simp only [Atom.rectangles, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp <;> omega
  | parity =>
    simp only [Atom.rectangles, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp <;> omega

theorem rectangles_thick (w offset : ℕ) (above : Bool) (atoms : List Atom)
    (ha : ∀ a ∈ atoms, a.Valid w) {r : Rectangle}
    (hr : r ∈ rectangles w offset above atoms) : w ≤ r.width ∧ w ≤ r.height := by
  induction atoms generalizing offset above with
  | nil => simp [rectangles] at hr
  | cons a atoms ih =>
    rcases List.mem_append.mp hr with hr | hr
    · exact a.rectangles_thick w offset above (ha a (by simp)) hr
    · exact ih _ _ (fun b hb => ha b (by simp [hb])) hr

/-- All literal tool walls avoid the working row. -/
private theorem Atom.rectangles_off_row (w offset : ℕ) (above : Bool) (a : Atom)
    {r : Rectangle} (hr : r ∈ a.rectangles w offset above) :
    r.y+r.height ≤ FiniteTools.radius w ∨ FiniteTools.radius w < r.y := by
  cases above <;> cases a <;>
    simp [Atom.rectangles] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp [FiniteTools.radius] <;> omega

theorem rectangles_off_row (w offset : ℕ) (above : Bool) (atoms : List Atom)
    {r : Rectangle} (hr : r ∈ rectangles w offset above atoms) :
    r.y+r.height ≤ FiniteTools.radius w ∨ FiniteTools.radius w < r.y := by
  induction atoms generalizing offset above with
  | nil => simp [rectangles] at hr
  | cons a atoms ih =>
    rcases List.mem_append.mp hr with hr | hr
    · exact a.rectangles_off_row w offset above hr
    · exact ih _ _ hr

/-- Every wall stays within its atom's actual interval plus the two shared collar columns. -/
theorem Atom.rectangles_bounds (w offset : ℕ) (above : Bool) (a : Atom)
    {r : Rectangle} (hr : r ∈ a.rectangles w offset above) :
    FiniteTools.radius w+offset ≤ r.x ∧
      r.x+r.width ≤ FiniteTools.radius w+offset+a.span w+2 ∧
      0 < r.y ∧ r.y+r.height ≤ FiniteTools.side w := by
  have hm := FiniteTools.paritySpan_bounds w
  cases above <;> cases a <;>
    simp [Atom.rectangles] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;>
    dsimp [Atom.span, FiniteTools.radius, FiniteTools.side] <;> omega

theorem rectangles_bounds (w offset : ℕ) (above : Bool) (atoms : List Atom)
    {r : Rectangle} (hr : r ∈ rectangles w offset above atoms) :
    FiniteTools.radius w+offset ≤ r.x ∧
      r.x+r.width ≤ FiniteTools.radius w+offset+span w atoms+2 ∧
      0 < r.y ∧ r.y+r.height ≤ FiniteTools.side w := by
  induction atoms generalizing offset above with
  | nil => simp [rectangles] at hr
  | cons a atoms ih =>
    rcases List.mem_append.mp hr with hr | hr
    · have hh := a.rectangles_bounds w offset above hr
      simp only [span_cons]
      omega
    · have hh := ih _ _ hr
      simp only [span_cons]
      omega

private theorem Atom.rectangles_band (w offset : ℕ) (above : Bool) (a : Atom)
    {r : Rectangle} (hr : r ∈ a.rectangles w offset above) :
    FiniteTools.radius w-w ≤ r.y ∧ r.y+r.height ≤ FiniteTools.radius w+w+1 := by
  cases above <;> cases a <;>
    simp [Atom.rectangles] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp [FiniteTools.radius] <;> omega

theorem rectangles_band (w offset : ℕ) (above : Bool) (atoms : List Atom)
    {r : Rectangle} (hr : r ∈ rectangles w offset above atoms) :
    FiniteTools.radius w-w ≤ r.y ∧ r.y+r.height ≤ FiniteTools.radius w+w+1 := by
  induction atoms generalizing offset above with
  | nil => simp [rectangles] at hr
  | cons a atoms ih =>
    rcases List.mem_append.mp hr with hr | hr
    · exact a.rectangles_band w offset above hr
    · exact ih _ _ hr

theorem Atom.positions_length (w : ℕ) (a : Atom) (q : Bool) :
    (a.positions w q).length = (a.positions w false).length := by
  cases a <;> simp [Atom.positions]

theorem positions_length (w : ℕ) (atoms : List Atom) (q : Bool) :
    (positions w q atoms).length = (positions w false atoms).length := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih => simp only [positions, List.length_append, List.length_map, a.positions_length w q, ih]

/-- Each guarded rail column touches at least one of the two neighboring wall rows. -/
def RowGuard (w x : ℕ) (r : Rectangle) : Prop :=
  r.x ≤ x ∧ x < r.x+r.width ∧
    ((r.y ≤ FiniteTools.radius w-1 ∧ FiniteTools.radius w-1 < r.y+r.height) ∨
      (r.y ≤ FiniteTools.radius w+1 ∧ FiniteTools.radius w+1 < r.y+r.height))

private theorem Atom.column_guard (w : ℕ) (hw : 2 ≤ w) (offset : ℕ) (above : Bool) (a : Atom)
    {x : ℕ} (hx : FiniteTools.radius w+offset ≤ x)
    (hx' : x < FiniteTools.radius w+offset+a.span w+2) :
    ∃ r ∈ a.rectangles w offset above, RowGuard w x r := by
  have hm := FiniteTools.paritySpan_bounds w
  cases above <;> cases a <;>
    simp [Atom.rectangles, RowGuard, Atom.span, FiniteTools.radius] at * <;> omega

/-- Guard coverage includes both shared interface columns at the end of the program. -/
theorem column_guard (w : ℕ) (hw : 2 ≤ w) (offset : ℕ) (above : Bool) (atoms : List Atom)
    (hne : atoms ≠ []) {x : ℕ} (hx : FiniteTools.radius w+offset ≤ x)
    (hx' : x < FiniteTools.radius w+offset+span w atoms+2) :
    ∃ r ∈ rectangles w offset above atoms, RowGuard w x r := by
  induction atoms generalizing offset above with
  | nil => contradiction
  | cons a atoms ih =>
    by_cases ht : atoms = []
    · subst atoms
      obtain ⟨r,hr,hg⟩ := a.column_guard w hw offset above hx (by simpa only [span_cons, span_nil, Nat.add_zero] using hx')
      exact ⟨r, List.mem_append_left _ hr, hg⟩
    · by_cases hax : x < FiniteTools.radius w+offset+a.span w
      · obtain ⟨r,hr,hg⟩ := a.column_guard w hw offset above hx (by omega)
        exact ⟨r, List.mem_append_left _ hr, hg⟩
      · obtain ⟨r,hr,hg⟩ := ih (offset+a.span w) (a.nextSide above) ht (by omega)
          (by simp only [span_cons] at hx'; omega)
        exact ⟨r, List.mem_append_right _ hr, hg⟩

theorem positions_length_pos (w : ℕ) (atoms : List Atom) (q : Bool) :
    0 < (positions w q atoms).length := by
  induction atoms with
  | nil => simp [positions]
  | cons a atoms ih => simp only [positions, List.length_append, List.length_map]; omega

theorem program_nonempty (w length : ℕ) (switch : Bool) : program w length switch ≠ [] := by
  simp [program]

theorem positions_nonempty (w : ℕ) (atoms : List Atom) (q : Bool) : positions w q atoms ≠ [] := by
  intro h
  have hh := positions_length_pos w atoms q
  rw [h] at hh
  contradiction

theorem positions_last (w : ℕ) (atoms : List Atom) (q : Bool) :
    (positions w q atoms).getLast (positions_nonempty w atoms q) = span w atoms+q.toNat := by
  induction atoms with
  | nil => simp [positions, span]
  | cons a atoms ih =>
    have hne : (positions w q atoms).map (a.span w + ·) ≠ [] := by
      intro h
      have hh := congrArg List.length h
      simp only [List.length_map, List.length_nil] at hh
      have hp := positions_length_pos w atoms q
      omega
    simp only [positions, List.getLast_append_of_ne_nil _ hne, List.getLast_map, ih, span_cons]
    omega

theorem positions_head_line (w : ℕ) (q : Bool) (n : ℕ) (hn : 0 < n) (atoms : List Atom) :
    (positions w q (.line n::atoms)).headD 0 = q.toNat := by
  cases n with
  | zero => contradiction
  | succ n => simp [positions, Atom.positions, List.range_succ_eq_map]

theorem program_positions_head (w length : ℕ) (switch q : Bool) :
    (positions w q (program w length switch)).headD 0 = q.toNat := by
  unfold program initialAtoms
  simp only [List.cons_append, List.nil_append]
  exact positions_head_line w q (buffer w) (by unfold buffer; omega) _

end PushPuzzle.PushS.FiniteRouting.Line
