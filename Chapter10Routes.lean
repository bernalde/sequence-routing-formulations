module

public import Chapter10RoutingData

@[expose] public section

/-! Author candidate for F1. Lists retain visits with their multiplicity.
Elementarity is an explicit catalogue condition. No completeness, fleet cap,
capacity constraint, or time grid is inferred from the source incidence rows. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Routing

variable {n : ℕ}

/-- Consecutive edges, including the final return to the depot. -/
def AllowedFrom (D : Data n) (prev : Node n) : List (Fin n) → Prop
  | [] => D.allowed prev none = true
  | j :: js => D.allowed prev (some j) = true ∧ AllowedFrom D (some j) js

/-- The literal sum of consecutive edge costs, with arbitrary signed costs. -/
def edgeCostFrom (D : Data n) (prev : Node n) : List (Fin n) → ℝ
  | [] => D.cost prev none
  | j :: js => D.cost prev (some j) + edgeCostFrom D (some j) js

/-- Customer position clocks and an unbounded-above return clock. -/
def ScheduleFrom (D : Data n) (prev : Node n) (start : ℝ) :
    List (Fin n) → List ℝ → ℝ → Prop
  | [], [], ret => start + D.travel prev none ≤ ret
  | j :: js, s :: ss, ret =>
      D.opening j ≤ s ∧ s ≤ D.closing j ∧
      start + D.travel prev (some j) ≤ s ∧ ScheduleFrom D (some j) s js ss ret
  | _, _, _ => False

def earliestTimes (D : Data n) (prev : Node n) (start : ℝ) : List (Fin n) → List ℝ
  | [] => []
  | j :: js =>
      let s := max (D.opening j) (start + D.travel prev (some j))
      s :: earliestTimes D (some j) s js

def earliestReturn (D : Data n) (prev : Node n) (start : ℝ) : List (Fin n) → ℝ
  | [] => start + D.travel prev none
  | j :: js => earliestReturn D (some j)
      (max (D.opening j) (start + D.travel prev (some j))) js

def EarliestWithin (D : Data n) (prev : Node n) (start : ℝ) : List (Fin n) → Prop
  | [] => True
  | j :: js =>
      let s := max (D.opening j) (start + D.travel prev (some j))
      s ≤ D.closing j ∧ EarliestWithin D (some j) s js

theorem schedule_length {D : Data n} {prev start js ss ret}
    (h : ScheduleFrom D prev start js ss ret) : ss.length = js.length := by
  induction js generalizing prev start ss with
  | nil => cases ss <;> simp_all [ScheduleFrom]
  | cons j js ih =>
    cases ss with
    | nil => simp [ScheduleFrom] at h
    | cons s ss => simpa using ih h.2.2.2

theorem earliestTimes_length (D : Data n) (prev start) (js : List (Fin n)) :
    (earliestTimes D prev start js).length = js.length := by
  induction js generalizing prev start with
  | nil => rfl
  | cons j js ih => simp [earliestTimes, ih]

/-- Earlier starting time makes the concrete recurrence dominate every feasible
position schedule. No compactness or analytic minimizer oracle is used. -/
theorem earliest_dominates {D : Data n} {prev : Node n} {e s : ℝ}
    {js : List (Fin n)} {ss : List ℝ} {ret : ℝ}
    (hes : e ≤ s) (h : ScheduleFrom D prev s js ss ret) :
    EarliestWithin D prev e js ∧
    List.Forall₂ (· ≤ ·) (earliestTimes D prev e js) ss ∧
    earliestReturn D prev e js ≤ ret := by
  induction js generalizing prev e s ss with
  | nil =>
    cases ss with
    | nil => exact ⟨trivial, .nil, le_trans (add_le_add hes le_rfl) h⟩
    | cons a as => simp [ScheduleFrom] at h
  | cons j js ih =>
    cases ss with
    | nil => simp [ScheduleFrom] at h
    | cons a as =>
      obtain ⟨ha, hb, ht, htail⟩ := h
      have hea : max (D.opening j) (e + D.travel prev (some j)) ≤ a :=
        max_le ha (le_trans (add_le_add hes le_rfl) ht)
      obtain ⟨hw, hclock, hr⟩ := ih hea htail
      exact ⟨⟨le_trans hea hb, hw⟩, .cons hea hclock, hr⟩

theorem earliest_schedule {D : Data n} {prev start js}
    (h : EarliestWithin D prev start js) :
    ScheduleFrom D prev start js (earliestTimes D prev start js)
      (earliestReturn D prev start js) := by
  induction js generalizing prev start with
  | nil => exact le_refl _
  | cons j js ih =>
    exact ⟨le_max_left _ _, h.1, le_max_right _ _, ih h.2⟩

/-- Exact schedule existence for a prescribed order; closing bounds are the
only possible obstruction after computing earliest arrival and permitted waiting. -/
theorem schedule_exists_iff (D : Data n) (prev start) (js : List (Fin n)) :
    (∃ ss ret, ScheduleFrom D prev start js ss ret) ↔ EarliestWithin D prev start js := by
  constructor
  · rintro ⟨ss, ret, h⟩
    exact (earliest_dominates (le_refl start) h).1
  · intro h
    exact ⟨_, _, earliest_schedule h⟩

theorem earliest_return_minimum {D : Data n} {prev start js}
    (h : EarliestWithin D prev start js) :
    (∃ ss, ScheduleFrom D prev start js ss (earliestReturn D prev start js)) ∧
    ∀ ss ret, ScheduleFrom D prev start js ss ret →
      earliestReturn D prev start js ≤ ret := by
  exact ⟨⟨_, earliest_schedule h⟩, fun _ _ hs => (earliest_dominates (le_refl _) hs).2.2⟩

/-- Signed load after exactly k customer visits; the empty prefix is included. -/
def prefixLoad (D : Data n) (js : List (Fin n)) (k : ℕ) : ℝ :=
  D.initialLoad + ((js.take k).map D.demand).sum

def CapacityFeasible (D : Data n) (js : List (Fin n)) : Prop :=
  ∀ k, k ≤ js.length → 0 ≤ prefixLoad D js k ∧ prefixLoad D js k ≤ D.capacity

@[simp] theorem prefixLoad_zero (D : Data n) (js : List (Fin n)) :
    prefixLoad D js 0 = D.initialLoad := by simp [prefixLoad]

@[simp] theorem prefixLoad_cons_succ (D : Data n) (j : Fin n) (js : List (Fin n)) (k : ℕ) :
    prefixLoad D (j :: js) (k + 1) = prefixLoad D js k + D.demand j := by
  simp [prefixLoad, List.take_succ_cons]
  ring

theorem capacity_initial {D : Data n} {js : List (Fin n)} (h : CapacityFeasible D js) :
    0 ≤ D.initialLoad ∧ D.initialLoad ≤ D.capacity := by
  simpa using h 0 (Nat.zero_le _)

/-- A physically usable nonempty elementary supplied column. -/
def ValidColumn (D : Data n) (js : List (Fin n)) : Prop :=
  js ≠ [] ∧ js.Nodup ∧ AllowedFrom D none js ∧
  EarliestWithin D none 0 js ∧ CapacityFeasible D js

/-- The finite catalogue itself is data; it is not asserted complete. -/
structure Catalogue (D : Data n) (r : ℕ) where
  data_nonnegative : nonnegativeTravel D
  data_ordered : orderedWindows D
  route : Fin r → List (Fin n)
  valid : ∀ j, ValidColumn D (route j)

def incidence {r : ℕ} (routes : Fin r → List (Fin n)) : Fin n → Fin r → Bool :=
  fun i j => decide (i ∈ routes j)

def occurrenceCount {r : ℕ} (routes : Fin r → List (Fin n)) (x : Bits r) (i : Fin n) : ℕ :=
  ∑ j, if x j then (routes j).count i else 0

/-- Membership incidence counts occurrences exactly under the explicit
within-column elementarity premise. This is false for general route walks. -/
theorem coverCount_eq_occurrenceCount {r : ℕ} (routes : Fin r → List (Fin n))
    (hn : ∀ j, (routes j).Nodup) (x : Bits r) (i : Fin n) :
    coverCount (incidence routes) x i = occurrenceCount routes x i := by
  classical
  unfold coverCount occurrenceCount
  apply Finset.sum_congr rfl
  intro j _
  by_cases hm : i ∈ routes j
  · have hc : (routes j).count i = 1 := List.count_eq_one_of_mem (hn j) hm
    cases hx : x j <;> simp [incidence, hm, hx, hc]
  · have hc : (routes j).count i = 0 := List.count_eq_zero.mpr hm
    cases hx : x j <;> simp [incidence, hm, hx, hc]

theorem literal_cover_iff_occurs_once {r : ℕ} (routes : Fin r → List (Fin n))
    (hn : ∀ j, (routes j).Nodup) (x : Bits r) :
    (∀ i, (∑ j, bit (incidence routes i j) * bit (x j)) = 1) ↔
      ∀ i, occurrenceCount routes x i = 1 := by
  constructor <;> intro h i
  · have he := h i
    rw [← literal_incidence_sum, coverCount_eq_occurrenceCount routes hn] at he
    exact_mod_cast he
  · rw [← literal_incidence_sum, coverCount_eq_occurrenceCount routes hn, h i]
    norm_num

theorem catalogue_feasible_iff {D : Data n} {r : ℕ} (K : Catalogue D r) (x : Bits r) :
    feasible (incidence K.route) x ↔ ∀ i, occurrenceCount K.route x i = 1 := by
  unfold feasible
  simp_rw [coverCount_eq_occurrenceCount K.route (fun j => (K.valid j).2.1)]

/-- This is the literal source cost of the chosen concrete routes. -/
def selectedRouteCost {r : ℕ} (D : Data n) (routes : Fin r → List (Fin n)) (x : Bits r) : ℝ :=
  ∑ j, if x j then edgeCostFrom D none (routes j) else 0

theorem literal_objective_eq_selectedRouteCost {r : ℕ} (D : Data n)
    (routes : Fin r → List (Fin n)) (x : Bits r) :
    cost (fun j => edgeCostFrom D none (routes j)) x = selectedRouteCost D routes x := by
  unfold cost selectedRouteCost
  apply Finset.sum_congr rfl
  intro j _
  cases hx : x j <;> simp [bit, hx]

/-- Real binary source columns are transported explicitly to the finite Bool domain. -/
def decodeColumns {r : ℕ} (u : Fin r → ℝ) : Bits r := fun j => decide (u j = 1)

theorem bit_decodeColumns {r : ℕ} (u : Fin r → ℝ)
    (hu : ∀ j, u j = 0 ∨ u j = 1) (j : Fin r) : bit (decodeColumns u j) = u j := by
  rcases hu j with h | h <;> simp [decodeColumns, bit, h]

theorem real_binary_cover_iff {r : ℕ} (routes : Fin r → List (Fin n))
    (hn : ∀ j, (routes j).Nodup) (u : Fin r → ℝ) (hu : ∀ j, u j = 0 ∨ u j = 1) :
    (∀ i, (∑ j, bit (incidence routes i j) * u j) = 1) ↔
      ∀ i, occurrenceCount routes (decodeColumns u) i = 1 := by
  simpa only [bit_decodeColumns u hu] using
    literal_cover_iff_occurs_once routes hn (decodeColumns u)

theorem real_binary_objective {r : ℕ} (D : Data n)
    (routes : Fin r → List (Fin n)) (u : Fin r → ℝ) (hu : ∀ j, u j = 0 ∨ u j = 1) :
    (∑ j, edgeCostFrom D none (routes j) * u j) =
      selectedRouteCost D routes (decodeColumns u) := by
  simpa only [cost, bit_decodeColumns u hu] using
    literal_objective_eq_selectedRouteCost D routes (decodeColumns u)

/-- Additional fleet restriction, absent from the literal incidence rows. -/
def selectedCount {r : ℕ} (x : Bits r) : ℕ := Fintype.card {j // x j = true}

theorem selectedCount_eq_sum {r : ℕ} (x : Bits r) :
    selectedCount x = ∑ j, if x j then 1 else 0 := by
  simp only [selectedCount, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Homogeneous vehicle assignment is exactly an additional at-most count cap.
This says nothing about an exactly-used fleet or dummy-route padding. -/
theorem fleet_assignment_iff {r : ℕ} (x : Bits r) (v : ℕ) :
    Nonempty ({j // x j = true} ↪ Fin v) ↔ selectedCount x ≤ v := by
  simpa [selectedCount] using
    (Function.Embedding.nonempty_iff_card_le (α := {j // x j = true}) (β := Fin v))

/-- Occurrence-feasible, minimum-cost selection in the supplied catalogue only. -/
def CatalogueMin {r : ℕ} (D : Data n) (routes : Fin r → List (Fin n)) (x : Bits r) : Prop :=
  (∀ i, occurrenceCount routes x i = 1) ∧
  ∀ y, (∀ i, occurrenceCount routes y i = 1) →
    selectedRouteCost D routes x ≤ selectedRouteCost D routes y

theorem catalogue_min_iff_routeMin {D : Data n} {r : ℕ} (K : Catalogue D r) (x : Bits r) :
    CatalogueMin D K.route x ↔
      routeMin (incidence K.route) (fun j => edgeCostFrom D none (K.route j)) x := by
  simp only [CatalogueMin, routeMin, catalogue_feasible_iff,
    literal_objective_eq_selectedRouteCost]

/-- Reuse adapter, not a new proof or credit for Prop10.B.1. The added content
is the concrete catalogue interpretation on the right. -/
theorem supplied_catalogue_penalty_adapter {D : Data n} {r : ℕ} (K : Catalogue D r)
    (ρ : ℝ) (hρ : (∑ j, |edgeCostFrom D none (K.route j)|) < ρ) (x : Bits r) :
    (energyMin (incidence K.route) (fun j => edgeCostFrom D none (K.route j)) ρ x ∧
      ∃ y, feasible (incidence K.route) y) ↔ CatalogueMin D K.route x := by
  rw [catalogue_min_iff_routeMin]
  exact source_route_penalty_proposition _ _ _ hρ _

/-- For full-physical comparisons a representation premise must be supplied.
Each competing collection must have a feasible catalogue selection of no larger
cost. The source's finite catalogue assumption does not establish this premise. -/
theorem catalogue_min_global_under_representation {D : Data n} {r : ℕ}
    (routes : Fin r → List (Fin n)) {x : Bits r} (hx : CatalogueMin D routes x)
    {Collection : Type*} (admissible : Collection → Prop) (physicalCost : Collection → ℝ)
    (represented : ∀ z, admissible z → ∃ y, (∀ i, occurrenceCount routes y i = 1) ∧
      selectedRouteCost D routes y ≤ physicalCost z) :
    ∀ z, admissible z → selectedRouteCost D routes x ≤ physicalCost z := by
  intro z hz
  obtain ⟨y, hy, hc⟩ := represented z hz
  exact le_trans (hx.2 y hy) hc

/-- Cost of an explicitly displayed node walk. -/
def walkCost (D : Data n) : List (Node n) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => D.cost a b + walkCost D (b :: rest)

theorem edgeCostFrom_eq_walkCost (D : Data n) (prev : Node n) (js : List (Fin n)) :
    edgeCostFrom D prev js = walkCost D (prev :: (js.map some ++ [none])) := by
  induction js generalizing prev with
  | nil => simp [edgeCostFrom, walkCost]
  | cons j js ih => simpa [edgeCostFrom, walkCost] using congrArg (D.cost prev (some j) + ·) (ih (some j))


/-- Under the physical travel premise, schedules have nonnegative clocks from
any nonnegative initial departure, including the return clock. -/
theorem schedule_nonnegative {D : Data n} (ht : nonnegativeTravel D)
    {prev start js ss ret} (hs : 0 ≤ start) (ha : AllowedFrom D prev js)
    (h : ScheduleFrom D prev start js ss ret) :
    List.Forall (0 ≤ ·) ss ∧ 0 ≤ ret := by
  induction js generalizing prev start ss with
  | nil =>
    cases ss with
    | nil => exact ⟨by simp, le_trans (add_nonneg hs (ht _ _ ha)) h⟩
    | cons a as => simp [ScheduleFrom] at h
  | cons j js ih =>
    cases ss with
    | nil => simp [ScheduleFrom] at h
    | cons a as =>
      have hz : 0 ≤ a := le_trans (add_nonneg hs (ht _ _ ha.1)) h.2.2.1
      obtain ⟨hn, hr⟩ := ih hz ha.2 h.2.2.2
      refine ⟨?_, hr⟩
      cases as with
      | nil => exact hz
      | cons b bs => exact ⟨hz, hn⟩

/-- Every selected supplied column gives an actual elementary route, legal
edges, position schedule, nonnegative times, and all signed load prefixes. -/
theorem selected_column_realization {D : Data n} {r : ℕ} (K : Catalogue D r)
    (x : Bits r) (j : Fin r) (_selected : x j = true) :
    K.route j ≠ [] ∧ (K.route j).Nodup ∧ AllowedFrom D none (K.route j) ∧
    CapacityFeasible D (K.route j) ∧
    ∃ ss ret, ScheduleFrom D none 0 (K.route j) ss ret ∧
      List.Forall (0 ≤ ·) ss ∧ 0 ≤ ret := by
  obtain ⟨hne, hn, ha, hw, hc⟩ := K.valid j
  have hs := earliest_schedule hw
  exact ⟨hne, hn, ha, hc, _, _, hs,
    schedule_nonnegative K.data_nonnegative (le_refl 0) ha hs⟩

@[simp] theorem decode_bit_columns {r : ℕ} (x : Bits r) :
    decodeColumns (fun j => bit (x j)) = x := by
  funext j
  cases h : x j <;> simp [decodeColumns, bit, h]

theorem encoded_columns_binary {r : ℕ} (x : Bits r) :
    ∀ j, bit (x j) = 0 ∨ bit (x j) = 1 := by
  intro j
  cases h : x j <;> simp [bit, h]

/-- The source uses a depot window opening at zero. Nonnegative physical
travel makes the final max with that opening redundant. -/
theorem earliest_return_depot_window {D : Data n} (ht : nonnegativeTravel D)
    {prev start js} (hs : 0 ≤ start) (ha : AllowedFrom D prev js)
    (hw : EarliestWithin D prev start js) :
    max 0 (earliestReturn D prev start js) = earliestReturn D prev start js := by
  exact max_eq_right (schedule_nonnegative ht hs ha (earliest_schedule hw)).2

end Chapter10.Routing


