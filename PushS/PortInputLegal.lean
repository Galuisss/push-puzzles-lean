/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortLayout

/-! Native upper/lower input constraints on the actual port-order Boolean vector. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- NCL input thresholds at every actual two-page group; true supplies the upper page. -/
structure InputLegal (l : PortLayout) (axes : List Bool) : Prop where
  /-- The supplied vector allocates exactly the actual port set. -/
  axes_length : axes.length = l.portCount
  /-- Each upper ordinary group receives at least one upper input. -/
  upper (a b : ℕ) (group : (a, b) ∈ l.upperPairs) :
    axes.getD a false = true ∨ axes.getD b false = true
  /-- Each lower ordinary group receives at least one lower input. -/
  lower_wire (a b : ℕ) (group : .wire a b ∈ l.lowerGroups) :
    axes.getD a false = false ∨ axes.getD b false = false
  /-- An OR group receives at least one of its three lower inputs. -/
  or_gate (first : ℕ) (group : .gate .orGate first ∈ l.lowerGroups) :
    axes.getD first false = false ∨ axes.getD (first + 1) false = false ∨ axes.getD (first + 2) false = false
  /-- An AND group receives its heavy right input or both light inputs. -/
  and_gate (first : ℕ) (group : .gate .andGate first ∈ l.lowerGroups) :
    axes.getD (first + 2) false = false ∨ (axes.getD first false = false ∧ axes.getD (first + 1) false = false)

/-- Legal actual interface inputs with the AND middle-light input ordered below the left-light input. -/
structure OrderedInputs (l : PortLayout) (axes : List Bool) : Prop extends l.InputLegal axes where
  /-- The actual middle lower input may be requested only while the left lower input is present. -/
  and_ordered (first : ℕ) (group : .gate .andGate first ∈ l.lowerGroups) :
    axes.getD (first + 1) false = false → axes.getD first false = false

end PushPuzzle.PushS.PortLayout
