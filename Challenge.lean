module

public import Mathlib

/-! Statement surface for finite sequence routing and continuous timing.
The copied definitions are the actual source definitions, including all literal
binary rows and nested timing sums. P = k+2; empty vehicle traces are permitted.
Deliberate Challenge theorem placeholders are obligations for Comparator only.
No load-capacity, route-generation, global optimization or solver claim is made.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing

/-- Depot is none; customer i is some i, with customer indices Fin n. -/
abbrev Node (n : ℕ) := Option (Fin n)

/-- Routing data: allowed arcs, real travel and cost, customer windows, and load fields. This package does not certify load-capacity constraints. -/
structure Data (n : ℕ) where
  allowed : Node n → Node n → Bool
  travel : Node n → Node n → ℝ
  cost : Node n → Node n → ℝ
  opening : Fin n → ℝ
  closing : Fin n → ℝ
  demand : Fin n → ℝ
  initialLoad : ℝ
  capacity : ℝ

/-- Every consecutive arc from the given initial node through the customer list and back to the depot is allowed. -/
def AllowedFrom (D : Data n) (prev : Node n) : List (Fin n) → Prop
  | [] => D.allowed prev none = true
  | j :: js => D.allowed prev (some j) = true ∧ AllowedFrom D (some j) js

/-- Sum of consecutive real arc costs through the customer list, including the final depot return. -/
def edgeCostFrom (D : Data n) (prev : Node n) : List (Fin n) → ℝ
  | [] => D.cost prev none
  | j :: js => D.cost prev (some j) + edgeCostFrom D (some j) js

/-- Position-by-position schedule with customer opening/closing windows, travel lower bounds, and a final return lower bound. -/
def ScheduleFrom (D : Data n) (prev : Node n) (start : ℝ) :
    List (Fin n) → List ℝ → ℝ → Prop
  | [], [], ret => start + D.travel prev none ≤ ret
  | j :: js, s :: ss, ret =>
      D.opening j ≤ s ∧ s ≤ D.closing j ∧
      start + D.travel prev (some j) ≤ s ∧ ScheduleFrom D (some j) s js ss ret
  | _, _, _ => False

/-- Earliest customer clocks obtained by propagating travel and waiting until each opening time. -/
def earliestTimes (D : Data n) (prev : Node n) (start : ℝ) : List (Fin n) → List ℝ
  | [] => []
  | j :: js =>
      let s := max (D.opening j) (start + D.travel prev (some j))
      s :: earliestTimes D (some j) s js

/-- Return clock of the earliest-time recurrence, including final travel to the depot. -/
def earliestReturn (D : Data n) (prev : Node n) (start : ℝ) : List (Fin n) → ℝ
  | [] => start + D.travel prev none
  | j :: js => earliestReturn D (some j)
      (max (D.opening j) (start + D.travel prev (some j))) js

/-- Every customer clock from the earliest recurrence satisfies its closing bound. -/
def EarliestWithin (D : Data n) (prev : Node n) (start : ℝ) : List (Fin n) → Prop
  | [] => True
  | j :: js =>
      let s := max (D.opening j) (start + D.travel prev (some j))
      s ≤ D.closing j ∧ EarliestWithin D (some j) s js

/-- Initial node followed by the customer list and padding+1 depot entries. -/
def paddedWalk (prev : Node n) (js : List (Fin n)) (padding : ℕ) : List (Node n) :=
  prev :: (js.map some ++ List.replicate (padding + 1) none)

end Chapter10.Routing

namespace Chapter10.Sequence
open Chapter10.Routing

/-- Real sequence variables indexed by vehicle, one of k+2 positions, and depot/customer node. -/
abbrev Array (n v k : ℕ) := Fin v → Fin (k+2) → Node n → ℝ

/-- One chosen node at every vehicle-position pair. -/
abbrev Slots (n v k : ℕ) := Fin v → Fin (k+2) → Node n

/-- Initial position, numbered zero. -/
abbrev first (k : ℕ) : Fin (k+2) := 0

/-- Final position, numbered k+1. -/
abbrev last (k : ℕ) : Fin (k+2) := Fin.last (k+1)

/-- Explicit finite-index proof interface; support only. -/
theorem second._proof_2 (k : ℕ) : 1 < k+2 := by omega

/-- Position immediately following the initial depot. -/
abbrev second (k : ℕ) : Fin (k+2) := ⟨1, second._proof_2 k⟩

/-- Explicit finite-index proof interface; support only. -/
theorem penultimate._proof_2 (k : ℕ) : k < k+2 := by omega

/-- Position immediately preceding the final depot. -/
abbrev penultimate (k : ℕ) : Fin (k+2) := ⟨k, penultimate._proof_2 k⟩

/-- Left endpoint position of a consecutive transition. -/
abbrev left {k : ℕ} (p : Fin (k+1)) : Fin (k+2) := p.castSucc

/-- Right endpoint position of a consecutive transition. -/
abbrev right {k : ℕ} (p : Fin (k+1)) : Fin (k+2) := p.succ

/-- Every real sequence coordinate is zero or one. -/
def Binary {n v k} (x : Array n v k) : Prop :=
  ∀ a p i, x a p i = 0 ∨ x a p i = 1

/-- Each customer occurs exactly once across all vehicle-position coordinates. -/
def CustomerOnce {n v k} (x : Array n v k) : Prop :=
  ∀ i : Fin n, ∑ a, ∑ p, x a p (some i) = 1

/-- Every vehicle-position has exactly one active node. -/
def PositionOnce {n v k} (x : Array n v k) : Prop :=
  ∀ a p, ∑ i, x a p i = 1

/-- A forbidden arc has zero product of its two consecutive sequence coordinates. -/
def AllowedProducts {n v k} (D : Data n) (x : Array n v k) : Prop :=
  ∀ a p i j, D.allowed i j = false → x a (left p) i * x a (right p) j = 0

/-- After the initial position, a depot occurrence cannot be followed by a customer. -/
def AbsorbingProducts {n v k} (x : Array n v k) : Prop :=
  ∀ a (p : Fin (k+1)) (j : Fin n), 0 < p.val →
    x a (left p) none * x a (right p) (some j) = 0

/-- Literal fixed start/end depot coordinates and impossible-departure/return coordinates. -/
structure FixedRows {n v k} (D : Data n) (x : Array n v k) : Prop where
  start_depot : ∀ a, x a (first k) none = 1
  end_depot : ∀ a, x a (last k) none = 1
  start_customer : ∀ a i, x a (first k) (some i) = 0
  end_customer : ∀ a i, x a (last k) (some i) = 0
  impossible_departure : ∀ a j, D.allowed none j = false → x a (second k) j = 0
  impossible_return : ∀ a j, D.allowed j none = false → x a (penultimate k) j = 0

/-- All source sequence rows together: binary, coverage, position, allowed, absorbing, and fixed rows. -/
structure Literal {n v k} (D : Data n) (x : Array n v k) : Prop where
  binary : Binary x
  customer_once : CustomerOnce x
  position_once : PositionOnce x
  allowed : AllowedProducts D x
  absorbing : AbsorbingProducts x
  fixed : FixedRows D x

/-- Literal nested transition-cost sum over vehicles, consecutive positions, and allowed node pairs. -/
def objective {n v k} (D : Data n) (x : Array n v k) : ℝ :=
  ∑ a, ∑ p : Fin (k+1), ∑ i, ∑ j,
    if D.allowed i j then D.cost i j * x a (left p) i * x a (right p) j else 0

/-- One-hot real encoding of a chosen node in each vehicle-position slot. -/
def encode {n v k} (q : Slots n v k) : Array n v k :=
  fun a p i => if q a p = i then 1 else 0

/-- Decoded slot constraints: customer coverage, depot endpoints, allowed transitions, and absorbing depot tail. -/
structure SlotStructure {n v k} (D : Data n) (q : Slots n v k) : Prop where
  customer_once : CustomerOnce (encode q)
  start_depot : ∀ a, q a (first k) = none
  end_depot : ∀ a, q a (last k) = none
  allowed : ∀ a p, D.allowed (q a (left p)) (q a (right p)) = true
  absorbing : ∀ a (p : Fin (k+1)), 0 < p.val → q a (left p) = none →
    q a (right p) = none

/-- Ordered customer list after removing the initial depot and all remaining depot entries. -/
def decode {n v k} (q : Slots n v k) (a : Fin v) : List (Fin n) :=
  (List.ofFn fun p : Fin (k+1) => q a p.succ).filterMap id

/-- Literal nested incoming timing sum for a customer, retaining selected predecessor clocks and travel. -/
def customerRHS {n v k} (D : Data n) (x : Array n v k)
    (clock : Node n → ℝ) (i : Fin n) : ℝ :=
  ∑ a, ∑ p : Fin (k+1), ∑ j,
    if D.allowed j (some i) then
      (clock j + D.travel j (some i)) * x a (left p) j * x a (right p) (some i)
    else 0

/-- Literal nested timing sum over every transition entering the depot for one vehicle. -/
def returnRHS {n v k} (D : Data n) (x : Array n v k)
    (clock : Node n → ℝ) (a : Fin v) : ℝ :=
  ∑ p : Fin (k+1), ∑ j,
    if D.allowed j none then
      (clock j + D.travel j none) * x a (left p) j * x a (right p) none
    else 0

/-- Customer travel lower bounds, vehicle return lower bounds, and all customer time windows. -/
def LiteralTiming {n v k} (D : Data n) (x : Array n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) : Prop :=
  (∀ i, customerRHS D x clock i ≤ clock (some i)) ∧
  (∀ a, returnRHS D x clock a ≤ ret a) ∧
  (∀ i, D.opening i ≤ clock (some i) ∧ clock (some i) ≤ D.closing i)

/-- The source compiler's explicit list-index proof interface. Naming this
auxiliary theorem preserves the exact exported definition when source modules
are combined into one independent Challenge. It is proved here, not assumed. -/
theorem padSlots._proof_2 {n v k} (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (a : Fin v) (p : Fin (k+2)) :
    p.val < (paddedWalk none (js a) (k-(js a).length)).length := by
  simp only [paddedWalk, List.length_cons, List.length_append, List.length_map,
    List.length_replicate]
  have hh := hlen a
  have hp := p.isLt
  omega

/-- Canonical slots for bounded customer traces: initial depot, the trace, and enough depot padding to reach k+2 positions. -/
def padSlots {n v k} (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) : Slots n v k :=
  fun a p => (paddedWalk none (js a) (k-(js a).length))[p.val]'(padSlots._proof_2 js hlen a p)

theorem palomar_literal_iff_decoded {n v k} (D : Data n) (x : Array n v k) :
    Literal D x ↔ ∃ q : Slots n v k, x = encode q ∧ SlotStructure D q := by
  sorry

theorem palomar_literal_decodes_elementary_paths {n v k} (D : Data n) (x : Array n v k)
    (h : Literal D x) :
    ∃ q : Slots n v k, x = encode q ∧ SlotStructure D q ∧
      ∀ a, (decode q a).Nodup ∧ (decode q a).length ≤ k ∧
        AllowedFrom D none (decode q a) := by
  sorry

theorem palomar_bounded_traces_encode {n v k} (D : Data n) (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (hcover : ∀ i, ∑ a, (js a).count i = 1)
    (ha : ∀ a, AllowedFrom D none (js a)) (hdd : D.allowed none none = true)
    (hc : D.cost none none = 0) :
    Literal D (encode (padSlots js hlen)) ∧
      (∀ a, decode (padSlots js hlen) a = js a) ∧
      objective D (encode (padSlots js hlen)) = ∑ a, edgeCostFrom D none (js a) := by
  sorry

theorem palomar_decoded_cost {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (hc : D.cost none none = 0) :
    objective D (encode q) = ∑ a, edgeCostFrom D none (decode q a) := by
  sorry

theorem palomar_literal_timing_iff_schedules {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) (h : SlotStructure D q)
    (hc : clock none = 0) (ht : D.travel none none = 0) :
    LiteralTiming D (encode q) clock ret ↔
      ∀ a, ScheduleFrom D none 0 (decode q a)
        ((decode q a).map (fun j => clock (some j))) (ret a) := by
  sorry

theorem palomar_literal_timing_exists_iff {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0) :
    (∃ clock : Node n → ℝ, ∃ ret : Fin v → ℝ,
      clock none = 0 ∧ LiteralTiming D (encode q) clock ret) ↔
      ∀ a, EarliestWithin D none 0 (decode q a) := by
  sorry

theorem palomar_literal_duration_minimum {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0)
    (hw : ∀ a, EarliestWithin D none 0 (decode q a)) :
    (∃ clock : Node n → ℝ, clock none = 0 ∧
      LiteralTiming D (encode q) clock (fun a => earliestReturn D none 0 (decode q a))) ∧
    ∀ clock ret, clock none = 0 → LiteralTiming D (encode q) clock ret →
      (∑ a, earliestReturn D none 0 (decode q a)) ≤ ∑ a, ret a := by
  sorry

end Chapter10.Sequence
