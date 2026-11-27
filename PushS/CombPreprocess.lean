/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding
public import CslibFrontier.Computability.Geometry.Orthogonal.PointPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Mathlib.Data.List.GetD
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Integer strip coordinates for the actual comb-contour preprocessing. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib Cslib.Orthogonal Turing.MultiTapeTM

/-- Longitudinal stride for a strip whose transverse coordinate lies in `[0,width]`. -/
@[expose] def stride (width : ℕ) : ℕ := 2 * (width + 1)

/-- Swap the strip axes, shear, and double so every displayed point has even coordinates. -/
@[expose] def point (width : ℕ) (p : Point) : Point :=
  (2 * ((stride width : ℤ) * p.2 + p.1), 2 * p.1)

/-- Apply the same actual integer map to every vertex and every point of every incidence route. -/
@[expose] def prepare (width : ℕ) (d : Graph.OrthogonalDrawing) : Graph.OrthogonalDrawing :=
  (d.1.map (point width), d.2.map fun r => r.map (point width))

private theorem stride_pos (width : ℕ) : 0 < stride width := by unfold stride; omega

/-- Distinct original integer points remain distinct after the actual preprocessing. -/
theorem point_injective (width : ℕ) : Function.Injective (point width) := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp only [point] at hx hy
  have hab : a.1 = b.1 := by omega
  have hm : (stride width : ℤ) * a.2 = (stride width : ℤ) * b.2 := by omega
  have hs : (stride width : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (stride_pos width))
  exact Prod.ext hab (mul_left_cancel₀ hs hm)

/-- Different longitudinal rows retain their order throughout the bounded strip. -/
theorem point_column_lt (width : ℕ) {a b : Point}
    (ha : 0 ≤ a.1 ∧ a.1 ≤ width) (hb : 0 ≤ b.1 ∧ b.1 ≤ width) (hy : a.2 < b.2) :
    (point width a).1 < (point width b).1 := by
  have hs : (width : ℤ) < stride width := by unfold stride; push_cast; omega
  have hp : (0 : ℤ) ≤ stride width := by exact_mod_cast (Nat.zero_le (stride width))
  have hm := mul_le_mul_of_nonneg_left (show a.2 + 1 ≤ b.2 by omega) hp
  rw [mul_add, mul_one] at hm
  dsimp only [point]
  omega

/-- No two distinct grid points in the source strip share a prepared contour column. -/
theorem point_column_injective (width : ℕ) {a b : Point}
    (ha : 0 ≤ a.1 ∧ a.1 ≤ width) (hb : 0 ≤ b.1 ∧ b.1 ≤ width)
    (he : (point width a).1 = (point width b).1) : a = b := by
  have hy : a.2 = b.2 := by
    rcases lt_trichotomy a.2 b.2 with h | h | h
    · have := point_column_lt width ha hb h; omega
    · exact h
    · have := point_column_lt width hb ha h; omega
  apply Prod.ext _ hy
  dsimp only [point] at he
  rw [hy] at he
  omega

/-- The identical linear map acts on the full real plane. -/
@[expose] noncomputable def realMap (width : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (2 * ((stride width : ℝ) * p.2 + p.1), 2 * p.1)

/-- The actual full-plane strip preparation as a real linear map. -/
@[expose] noncomputable def realLinearMap (width : ℕ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := realMap width
  map_add' a b := by ext <;> simp [realMap] <;> ring
  map_smul' t a := by ext <;> simp [realMap] <;> ring

/-- The real map agrees exactly with the emitted integer coordinates. -/
theorem realPoint_point (width : ℕ) (p : Point) :
    realPoint (point width p) = realMap width (realPoint p) := by
  ext <;> simp [realPoint, point, realMap]

/-- Real segments do not acquire identifications under the preprocessing. -/
theorem realMap_injective (width : ℕ) : Function.Injective (realMap width) := by
  intro a b h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp only [realMap] at hx hy
  have hab : a.1 = b.1 := by linarith
  have hm : (stride width : ℝ) * a.2 = (stride width : ℝ) * b.2 := by nlinarith
  have hs : (stride width : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (stride_pos width))
  exact Prod.ext hab (mul_left_cancel₀ hs hm)

/-- Every prepared continuous segment is exactly the image of the original segment. -/
private theorem segment_point (width : ℕ) (a b : Point) :
    segment (point width a) (point width b) = realMap width '' segment a b := by
  have h := image_segment ℝ (realLinearMap width).toAffineMap (realPoint a) (realPoint b)
  change realMap width '' _root_.segment ℝ (realPoint a) (realPoint b) =
    _root_.segment ℝ (realMap width (realPoint a)) (realMap width (realPoint b)) at h
  simpa only [Orthogonal.segment, realPoint_point] using h.symm

private theorem consecutivePairs_map_point (width : ℕ) (r : Route) :
    (r.map (point width)).consecutivePairs = r.consecutivePairs.map fun e => (point width e.1, point width e.2) := by
  simp only [List.consecutivePairs, ← List.map_tail, List.zip_map]
  rfl

/-- The complete prepared route support is the image of its original continuous support. -/
theorem support_map_point (width : ℕ) (r : Route) :
    support (r.map (point width)) = realMap width '' support r := by
  ext p
  simp only [support, Set.mem_ofPred_eq, consecutivePairs_map_point, List.mem_map, Set.mem_image]
  constructor
  · rintro (⟨_, ⟨a, ha, rfl⟩, rfl⟩ | ⟨_, ⟨e, he, rfl⟩, hp⟩)
    · exact ⟨realPoint a, Or.inl ⟨a, ha, rfl⟩, (realPoint_point width a).symm⟩
    · obtain ⟨q, hq, rfl⟩ := (segment_point width e.1 e.2) ▸ hp
      exact ⟨q, Or.inr ⟨e, he, hq⟩, rfl⟩
  · rintro ⟨q, ⟨a, ha, rfl⟩ | ⟨e, he, hq⟩, rfl⟩
    · exact Or.inl ⟨point width a, ⟨a, ha, rfl⟩, (realPoint_point width a).symm⟩
    · exact Or.inr ⟨(point width e.1, point width e.2), ⟨e, he, rfl⟩,
        (segment_point width e.1 e.2) ▸ Set.mem_image_of_mem _ hq⟩

private theorem mem_segment_point_iff (width : ℕ) (a b : Point) (p : ℝ × ℝ) :
    realMap width p ∈ segment (point width a) (point width b) ↔ p ∈ segment a b := by
  rw [segment_point]
  exact (realMap_injective width).mem_set_image

private theorem endpointContacts_point (width : ℕ) {a b c d : Point}
    (h : EndpointContacts a b c d) :
    EndpointContacts (point width a) (point width b) (point width c) (point width d) := by
  intro p hp hq
  obtain ⟨q, hqa, rfl⟩ := (segment_point width a b) ▸ hp
  have hqc := (mem_segment_point_iff width c d q).mp hq
  have hh := h q hqa hqc
  simp only [realPoint_point]
  exact ⟨hh.1.imp (congrArg _) (congrArg _), hh.2.imp (congrArg _) (congrArg _)⟩

/-- The actual point map preserves the full continuous simplicity of every source route. -/
private theorem isSimple_map_point (width : ℕ) {r : Route} (hr : IsSimple r) :
    IsSimple (r.map (point width)) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_map_iff (point_injective width)]
    exact hr.1
  · intro e he f hf hne
    rw [consecutivePairs_map_point] at he hf
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp he
    obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hf
    have hef : ab ≠ cd := by intro h; subst cd; exact hne rfl
    exact endpointContacts_point width (hr.2 ab hab cd hcd hef)

/-- Each prepared source segment is horizontal or has slope one, so integer cuts stay integral. -/
theorem map_segment_slopes (width : ℕ) {r : Route} (hr : IsOrthogonal r) :
    ∀ e ∈ (r.map (point width)).consecutivePairs,
      e.1.2 = e.2.2 ∨ e.1.2 - e.1.1 = e.2.2 - e.2.1 := by
  intro e he
  rw [consecutivePairs_map_point] at he
  obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp he
  rcases (hr ab hab).1 with hx | hy
  · left
    dsimp only [point]
    rw [hx]
  · right
    dsimp only [point]
    rw [hy]
    ring

/-- Whole-edge vertical windows become whole-edge horizontal windows of fixed enlarged span. -/
theorem support_window (width start span : ℕ) (r : Route)
    (hwin : ∀ p ∈ support r, 0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span) :
    ∀ p ∈ support (r.map (point width)),
      0 ≤ p.2 ∧ p.2 ≤ 2 * width ∧
      2 * stride width * (start : ℝ) ≤ p.1 ∧
      p.1 ≤ 2 * stride width * (start : ℝ) + (2 * stride width * (span : ℝ) + 2 * width) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := (support_map_point width r) ▸ hp
  obtain ⟨hx0, hxW, hy0, hyS⟩ := hwin q hq
  have hs : (0 : ℝ) ≤ stride width := by exact_mod_cast (Nat.zero_le (stride width))
  have h0 := mul_le_mul_of_nonneg_left hy0 hs
  have hS := mul_le_mul_of_nonneg_left hyS hs
  dsimp only [realMap]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith
  · nlinarith

/-- The displayed vertex positions use the same actual point map, even at raw labels. -/
theorem drawingPosition_prepare (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) (v : ℕ) :
    Graph.drawingPosition G (prepare width d) v = point width (Graph.drawingPosition G d v) := by
  have hz : point width (0, 0) = (0, 0) := by simp [point]
  simpa only [Graph.drawingPosition, prepare, hz] using
    (List.getD_map (l := d.1) (d := (0, 0)) (n := G.vertices.idxOf v) (point width))

/-- Reading a prepared incidence route retains its actual original list position. -/
theorem route_prepare (width : ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    (prepare width d).2.getD i [] = (d.2.getD i []).map (point width) := by
  simpa only [prepare, List.map_nil] using
    (List.getD_map (l := d.2) (d := []) (n := i) (List.map (point width)))

/-- Preparing an actual standard drawing preserves its full real-plane edge contact condition. -/
theorem prepare_contacts (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {i j : ℕ}
    (hi : i < G.edges.length) (hj : j < G.edges.length) (hij : i ≠ j)
    {p : ℝ × ℝ} (hp : p ∈ support ((prepare width d).2.getD i []))
    (hp' : p ∈ support ((prepare width d).2.getD j [])) :
    ∃ v ∈ G.vertices, (v = G.edges[i].1 ∨ v = G.edges[i].2) ∧
      (v = G.edges[j].1 ∨ v = G.edges[j].2) ∧
      p = realPoint (Graph.drawingPosition G (prepare width d) v) := by
  rw [route_prepare, support_map_point] at hp hp'
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, hab⟩ := hp'
  have hba := realMap_injective width hab
  subst b
  obtain ⟨v, hv, hvi, hvj, rfl⟩ := hd.contacts i hi j hj hij a ha hb
  exact ⟨v, hv, hvi, hvj, by rw [drawingPosition_prepare, realPoint_point]⟩

/-- The prepared actual route still avoids every nonincident vertex of the same graph. -/
theorem prepare_avoidsVertices (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (i : ℕ) (hi : i < G.edges.length)
    (v : ℕ) (hv : v ∈ G.vertices)
    (hp : realPoint (Graph.drawingPosition G (prepare width d) v) ∈
      support ((prepare width d).2.getD i [])) :
    v = G.edges[i].1 ∨ v = G.edges[i].2 := by
  rw [drawingPosition_prepare, realPoint_point, route_prepare, support_map_point] at hp
  exact hd.avoidsVertices i hi v hv ((realMap_injective width).mem_set_image.mp hp)

/-- Every incidence route of the actual prepared drawing retains its continuous simplicity. -/
theorem prepare_simple (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (i : ℕ) (hi : i < G.edges.length) :
    IsSimple ((prepare width d).2.getD i []) := by
  rw [route_prepare]
  exact isSimple_map_point width (hd.simple i hi)

/-- The emitted coordinate map uses the standard binary integer-point encoding. -/
@[fun_prop] theorem computableInPolyTime_point (width : ℕ) :
    ComputableInPolyTime (point width) encPoint encPoint := by
  unfold point encPoint
  fun_prop

/-- Actual vertex and route list preprocessing is polynomial-time in the standard drawing encoding. -/
@[fun_prop] theorem computableInPolyTime_prepare (width : ℕ) :
    ComputableInPolyTime (prepare width) Graph.encOrthogonalDrawing Graph.encOrthogonalDrawing := by
  have hpoint := computableInPolyTime_point width
  unfold prepare Graph.encOrthogonalDrawing encRoute
  fun_prop

end PushPuzzle.PushS.Comb
