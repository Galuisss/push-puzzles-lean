/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSourceToothContacts
import all PushS.CombToothOrder

/-! The lower comb spine joins the actual source feet in their literal physical column order. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The actual sorted tooth array retains exactly the original number of source vertices. -/
theorem vertexOrder_length (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (vertexOrder width d).length = d.1.length := by
  simpa only [List.length_zipIdx, prepare, List.length_map] using (vertexOrder_perm width d).length_eq

/-- The actual original vertex at one position in the emitted geometric tooth order. -/
@[expose] def spineVertex (width : ℕ) (d : Graph.OrthogonalDrawing) (rank : Fin d.1.length) : Fin d.1.length :=
  let k : Fin (vertexOrder width d).length := ⟨rank.val, by rw [vertexOrder_length]; exact rank.isLt⟩
  ⟨((vertexOrder width d).get k).2, by
    have h := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width d).mem_iff.mp (List.get_mem _ k))
    simpa only [prepare, List.length_map, Nat.add_zero] using h⟩

private theorem spineVertex_site (width : ℕ) (d : Graph.OrthogonalDrawing) (rank : Fin d.1.length) :
    (prepare width d).1.getD (spineVertex width d rank) (0, 0) =
      ((vertexOrder width d).get ⟨rank.val, by rw [vertexOrder_length]; exact rank.isLt⟩).1 := by
  have h := List.mem_zipIdx_iff_getElem?.mp ((vertexOrder_perm width d).mem_iff.mp
    (List.get_mem (vertexOrder width d) ⟨rank.val, by rw [vertexOrder_length]; exact rank.isLt⟩))
  change (prepare width d).1[((vertexOrder width d).get ⟨rank.val, _⟩).2]? = _ at h
  simp only [spineVertex, List.getD_eq_getElem?_getD, h, Option.getD_some]

/-- The native vertex lookup along the emitted spine retains every original source vertex. -/
theorem spineVertex_surjective (width : ℕ) (d : Graph.OrthogonalDrawing) :
    Function.Surjective (spineVertex width d) := by
  intro vertex
  obtain ⟨i, _, hv, _⟩ := ordered_site width d vertex.isLt
  let rank : Fin d.1.length := ⟨i.val, by rw [← vertexOrder_length width d]; exact i.isLt⟩
  exact ⟨rank, Fin.ext hv⟩

/-- The emitted spine follows strictly increasing physical source columns. -/
theorem spineVertex_strictMono (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    StrictMono (fun rank => ((prepare width d).1.getD (spineVertex width d rank) (0, 0)).1) := by
  intro i j hij
  change ((prepare width d).1.getD (spineVertex width d i) (0, 0)).1 <
    ((prepare width d).1.getD (spineVertex width d j) (0, 0)).1
  rw [spineVertex_site, spineVertex_site]
  exact List.pairwise_iff_get.mp (vertexOrder_strict width height hd hfit) _ _ hij

/-- The left native endpoint of one actual bottom spine segment. -/
@[expose] def spineLeft (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1)) : Fin d.1.length :=
  spineVertex width d ⟨piece.val, by have := piece.isLt; omega⟩

/-- The right native endpoint of the same actual bottom spine segment. -/
@[expose] def spineRight (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1)) : Fin d.1.length :=
  spineVertex width d ⟨piece.val + 1, by have := piece.isLt; omega⟩

/-- The genuine lower horizontal route between consecutive actual source feet. -/
@[expose] noncomputable def spinePiece (width : ℕ) (d : Graph.OrthogonalDrawing)
    (piece : Fin (d.1.length - 1)) : Cslib.Polygonal.Route :=
  Cslib.Polygonal.Route.line (complexPoint (stationPoint width d (.foot (spineLeft width d piece))))
    (complexPoint (stationPoint width d (.foot (spineRight width d piece))))

/-- The two endpoints are exactly the named feet of the two consecutive actual source teeth. -/
theorem spinePiece_endpoint (width : ℕ) (d : Graph.OrthogonalDrawing)
    (piece : Fin (d.1.length - 1)) (side : Bool) :
    (spinePiece width d piece).endpoint side =
      complexPoint (stationPoint width d (.foot (if side then spineRight width d piece else spineLeft width d piece))) := by
  cases side <;> rfl

private theorem spine_columns_strict (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) :
    ((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 <
      ((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 :=
  spineVertex_strictMono width height hd hfit (a := ⟨piece.val, by have := piece.isLt; omega⟩)
    (b := ⟨piece.val + 1, by have := piece.isLt; omega⟩) (by change piece.val < piece.val + 1; omega)

/-- Each actual bottom spine piece is nondegenerate and simple. -/
theorem spinePiece_simple (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) : (spinePiece width d piece).IsSimple := by
  apply Cslib.Polygonal.Route.isSimple_line
  intro he
  have hx := congrArg Complex.re he
  change (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) =
    (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) at hx
  exact (ne_of_lt (spine_columns_strict width height hd hfit piece)) (Int.cast_inj.mp hx)

private theorem spinePiece_eval (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1))
    (i : Fin (spinePiece width d piece).segments) (t : ℝ) :
    (spinePiece width d piece).eval i t = AffineMap.lineMap
      (complexPoint (stationPoint width d (.foot (spineLeft width d piece))))
      (complexPoint (stationPoint width d (.foot (spineRight width d piece)))) t :=
  Cslib.Polygonal.Route.eval_line _ _ i t

/-- Every real spine parameter has the exact lower height of the actual comb feet. -/
theorem spinePiece_eval_im (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1))
    (i : Fin (spinePiece width d piece).segments) (t : ℝ) :
    ((spinePiece width d piece).eval i t).im = -2 := by
  rw [spinePiece_eval]
  simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im]
  change (1 - t) * ((-2 : ℤ) : ℝ) + t * ((-2 : ℤ) : ℝ) = -2
  norm_num
  ring

private theorem spinePiece_eval_re (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1))
    (i : Fin (spinePiece width d piece).segments) (t : ℝ) :
    ((spinePiece width d piece).eval i t).re =
      (1 - t) * (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) +
        t * (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) := by
  rw [spinePiece_eval]
  simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re]
  rfl

/-- Every continuous spine point stays between its two consecutive physical source columns. -/
theorem spinePiece_column_bounds (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) (i : Fin (spinePiece width d piece).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) ≤
      ((spinePiece width d piece).eval i t).re ∧ ((spinePiece width d piece).eval i t).re ≤
        (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) := by
  have hlt : (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) <
      (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) := by
    exact_mod_cast spine_columns_strict width height hd hfit piece
  rw [spinePiece_eval_re]
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hlt.le),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hlt.le)]

end PushPuzzle.PushS.Comb
