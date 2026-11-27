/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Core
public import PushFS.Gadgets.Wires.Polyline.Reorientation
public import PushFS.Gadgets.Wires.Soundness.Pair

/-! Exact finite identities of all gate fanout rails, flips and boundary boxes. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


set_option maxRecDepth 65536
set_option maxHeartbeats 0

abbrev Label (kind : Bool) := Fin (slots kind).length
instance (kind : Bool) : NeZero (slots kind).length := by cases kind <;> exact ⟨by decide⟩

inductive Rail where
  | main | upper | incoming | west
  deriving DecidableEq

namespace Rail

def axis : Rail → Bool | .main | .west => true | _ => false
def line (kind : Bool) : Rail → ℕ | .main => 90 | .upper => junction kind | .incoming => 39 | .west => 29
def tag (kind : Bool) (r : Rail) : AxisTrack := Wires.Soundness.lineTag r.axis (r.line kind)

end Rail

def pairs : (kind : Bool) → Rail → List (Label kind × Label kind)
  | false, .main => [(25,24),(24,23),(23,22),(22,21),(21,20),(20,19),(19,18),(18,17),(17,16),(16,15),(15,14),(14,13),(13,12),(12,11),(11,10),(10,9),(9,8),(8,0),(0,1),(1,4),(4,5),(5,7),(7,66),(66,67),(67,68),(68,69),(69,70),(70,71),(71,72),(72,73),(73,74),(74,75),(75,76),(76,77)]
  | false, .upper => [(65,64),(64,63),(63,62),(62,61),(61,60),(60,59),(59,58),(58,57),(57,56),(56,55),(55,54),(54,53),(53,52),(52,51),(51,50),(50,49),(49,48),(48,47),(47,46),(46,45),(45,44),(44,43),(43,42),(42,41),(41,40),(40,39),(39,38),(38,37),(37,36),(36,35),(35,34),(34,33),(33,32),(32,31),(31,30),(30,29),(29,28),(28,27),(27,26),(26,6),(6,3),(3,2)]
  | false, .incoming => []
  | false, .west => []
  | true, .main => [(0,1),(1,4),(4,5),(5,7),(7,95),(95,96),(96,97),(97,98),(98,99),(99,100),(100,101),(101,102),(102,103),(103,104),(104,105),(105,106),(106,107)]
  | true, .upper => [(94,93),(93,92),(92,91),(91,90),(90,89),(89,88),(88,87),(87,86),(86,85),(85,84),(84,83),(83,82),(82,81),(81,80),(80,79),(79,78),(78,77),(77,76),(76,75),(75,74),(74,73),(73,72),(72,71),(71,70),(70,69),(69,68),(68,67),(67,66),(66,65),(65,64),(64,63),(63,62),(62,61),(61,60),(60,59),(59,58),(58,57),(57,56),(56,55),(55,6),(6,3),(3,2)]
  | true, .incoming => [(36,35),(35,34),(34,33),(33,32),(32,31),(31,30),(30,29),(29,28),(28,27),(27,26),(26,25),(25,24),(24,23),(23,22),(22,21),(21,20),(20,19),(19,18),(18,17),(17,16),(16,15),(15,14),(14,13),(13,12),(12,11),(11,10),(10,9),(9,8)]
  | true, .west => [(54,53),(53,52),(52,51),(51,50),(50,49),(49,48),(48,47),(47,46),(46,45),(45,44),(44,43),(43,42),(42,41),(41,40),(40,39),(39,38),(38,37)]

def outerLabel : (kind : Bool) → Fin 3 → Label kind
  | true => ![54,94,107]
  | false => ![25,65,77]

def westFlip : (kind : Bool) → Fin 3 → Label kind
  | true => ![46,45,44]
  | false => ![17,16,15]

def eastFlip : (kind : Bool) → Fin 3 → Label kind
  | true => ![98,99,100]
  | false => ![69,70,71]

def upperFlip : (kind : Bool) → Fin 3 → Label kind
  | true => ![88,87,86]
  | false => ![59,58,57]

def westX (kind : Bool) : ℕ := if kind then 19 else 20
def eastX (kind : Bool) : ℕ := if kind then 60 else 61
def westY (kind : Bool) : ℕ := if kind then 29 else 90

/-- Every declared adjacent physical pair is on its literal common rail, strictly ordered, and mutually statically reachable. -/
theorem pair_facts (kind : Bool) (r : Rail) (s : Signals) (p : Label kind×Label kind) (hp : p∈pairs kind r) :
    axisName kind (position kind s p.1)=r.tag kind ∧ axisName kind (position kind s p.2)=r.tag kind ∧
    (if r.axis then (position kind s p.1).1.val else (position kind s p.1).2.val)<(if r.axis then (position kind s p.2).1.val else (position kind s p.2).2.val) := by
  have check : ∀ (kind a b c : Bool) (r : Rail), ((pairs kind r).all fun p=>decide
      (axisName kind (position kind ⟨a,b,c⟩ p.1)=r.tag kind ∧ axisName kind (position kind ⟨a,b,c⟩ p.2)=r.tag kind ∧
        (if r.axis then (position kind ⟨a,b,c⟩ p.1).1.val else (position kind ⟨a,b,c⟩ p.1).2.val)<
        (if r.axis then (position kind ⟨a,b,c⟩ p.2).1.val else (position kind ⟨a,b,c⟩ p.2).2.val)))=true := by
    intro kind a b c r
    cases r <;> revert kind a b c <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (check kind s.left s.upper s.right r) p hp)

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay
