module

public import Chapter10Routes

@[expose] public section

/-! Generic list adapters for sequence padding; no slot encoding is assumed. -/
noncomputable section
namespace Chapter10.Routing
variable {n : ℕ}

def paddedWalk (prev : Node n) (js : List (Fin n)) (padding : ℕ) : List (Node n) :=
  prev :: (js.map some ++ List.replicate (padding + 1) none)

theorem walkCost_depot_padding (D : Data n) (prev : Node n) (k : ℕ) :
    walkCost D (prev :: List.replicate (k+1) none) = D.cost prev none + k * D.cost none none := by
  induction k generalizing prev with
  | zero => simp [List.replicate_succ, walkCost]
  | succ k ih =>
    simp only [List.replicate_succ, walkCost]
    have h := ih none
    simp only [List.replicate_succ, walkCost] at h
    rw [h]
    push_cast
    ring

theorem padded_walk_cost (D : Data n) (prev : Node n) (js : List (Fin n)) (k : ℕ) :
    walkCost D (paddedWalk prev js k) = edgeCostFrom D prev js + k * D.cost none none := by
  induction js generalizing prev with
  | nil => exact walkCost_depot_padding D prev k
  | cons j js ih =>
    simp only [paddedWalk, List.map_cons, List.cons_append, walkCost, edgeCostFrom]
    rw [show walkCost D (some j :: (List.map some js ++ List.replicate (k + 1) none)) =
      edgeCostFrom D (some j) js + k * D.cost none none from ih (some j)]
    ring

theorem padded_walk_cost_zero_idle (D : Data n) (prev : Node n) (js : List (Fin n)) (k : ℕ)
    (hc : D.cost none none = 0) : walkCost D (paddedWalk prev js k) = edgeCostFrom D prev js := by
  rw [padded_walk_cost, hc, mul_zero, add_zero]

/-- Literal contribution of each consecutive edge that enters the depot.
The depot has its own fixed clock, rather than the return variable. -/
def returnContribution (D : Data n) (clock : Node n → ℝ) : List (Node n) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if b = none then clock a + D.travel a none else 0) +
      returnContribution D clock (b :: rest)

def customerEdges (D : Data n) (clock : Node n → ℝ) : List (Node n) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
    (match b with
     | none => True
     | some j => clock a + D.travel a (some j) ≤ clock (some j)) ∧
    customerEdges D clock (b :: rest)

def CustomerSteps (D : Data n) (clock : Node n → ℝ) (prev : Node n) : List (Fin n) → Prop
  | [] => True
  | j :: js => clock prev + D.travel prev (some j) ≤ clock (some j) ∧
      CustomerSteps D clock (some j) js

def FinalReturn (D : Data n) (clock : Node n → ℝ) (prev : Node n) : List (Fin n) → ℝ
  | [] => clock prev + D.travel prev none
  | j :: js => FinalReturn D clock (some j) js

def CustomerWindows (D : Data n) (clock : Node n → ℝ) (js : List (Fin n)) : Prop :=
  ∀ j ∈ js, D.opening j ≤ clock (some j) ∧ clock (some j) ≤ D.closing j

theorem returnContribution_depot_padding (D : Data n) (clock : Node n → ℝ)
    (prev : Node n) (k : ℕ) :
    returnContribution D clock (prev :: List.replicate (k+1) none) =
      clock prev + D.travel prev none + k * (clock none + D.travel none none) := by
  induction k generalizing prev with
  | zero => simp [List.replicate_succ, returnContribution]
  | succ k ih =>
    simp only [List.replicate_succ, returnContribution, ↓reduceIte]
    have h := ih none
    simp only [List.replicate_succ, returnContribution, ↓reduceIte] at h
    rw [h]
    push_cast
    ring

theorem padded_return_contribution (D : Data n) (clock : Node n → ℝ)
    (prev : Node n) (js : List (Fin n)) (k : ℕ) :
    returnContribution D clock (paddedWalk prev js k) =
      FinalReturn D clock prev js + k * (clock none + D.travel none none) := by
  induction js generalizing prev with
  | nil => exact returnContribution_depot_padding D clock prev k
  | cons j js ih =>
    simpa [paddedWalk, returnContribution, FinalReturn] using ih (some j)

theorem customerEdges_depot_padding (D : Data n) (clock : Node n → ℝ)
    (prev : Node n) (k : ℕ) : customerEdges D clock (prev :: List.replicate (k+1) none) := by
  induction k generalizing prev with
  | zero => simp [List.replicate_succ, customerEdges]
  | succ k ih =>
    simp only [List.replicate_succ, customerEdges, true_and]
    have h := ih none
    simpa only [List.replicate_succ, customerEdges, true_and] using h

theorem padded_customer_edges (D : Data n) (clock : Node n → ℝ)
    (prev : Node n) (js : List (Fin n)) (k : ℕ) :
    customerEdges D clock (paddedWalk prev js k) ↔ CustomerSteps D clock prev js := by
  induction js generalizing prev with
  | nil => exact iff_true_intro (customerEdges_depot_padding D clock prev k)
  | cons j js ih =>
    simpa only [paddedWalk, List.map_cons, List.cons_append, customerEdges, CustomerSteps] using
      and_congr_right (fun _ => ih (some j))

theorem schedule_map_clock_iff (D : Data n) (clock : Node n → ℝ)
    (prev : Node n) (js : List (Fin n)) (ret : ℝ) :
    ScheduleFrom D prev (clock prev) js (js.map (fun j => clock (some j))) ret ↔
      CustomerWindows D clock js ∧ CustomerSteps D clock prev js ∧
      FinalReturn D clock prev js ≤ ret := by
  induction js generalizing prev with
  | nil => simp [ScheduleFrom, CustomerWindows, CustomerSteps, FinalReturn]
  | cons j js ih =>
    simp only [List.map_cons, ScheduleFrom, CustomerSteps, FinalReturn, ih,
      CustomerWindows, List.mem_cons, forall_eq_or_imp]
    tauto

/-- Exact padded timing adapter under the explicit depot-clock/time repairs.
All customer windows and every actual predecessor edge remain in the premise. -/
theorem padded_timing_iff_schedule (D : Data n) (clock : Node n → ℝ)
    (js : List (Fin n)) (padding : ℕ) (ret : ℝ)
    (hclock : clock none = 0) (ht : D.travel none none = 0) :
    (CustomerWindows D clock js ∧ customerEdges D clock (paddedWalk none js padding) ∧
      returnContribution D clock (paddedWalk none js padding) ≤ ret) ↔
    ScheduleFrom D none 0 js (js.map (fun j => clock (some j))) ret := by
  rw [padded_customer_edges, padded_return_contribution, hclock, ht, add_zero, mul_zero, add_zero]
  simpa only [hclock] using (schedule_map_clock_iff D clock none js ret).symm

end Chapter10.Routing
