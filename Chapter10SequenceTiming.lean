module

public import Chapter10Sequence
public import Chapter10RoutePadding

@[expose] public section

/-! Full printed cubic timing sums and their repaired physical interpretation.
The depot clock and depot-loop time remain explicit data until the repair. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Sequence
open Chapter10.Routing

def customerRHS {n v k} (D : Data n) (x : Array n v k)
    (clock : Node n → ℝ) (i : Fin n) : ℝ :=
  ∑ a, ∑ p : Fin (k+1), ∑ j,
    if D.allowed j (some i) then
      (clock j + D.travel j (some i)) * x a (left p) j * x a (right p) (some i)
    else 0

def returnRHS {n v k} (D : Data n) (x : Array n v k)
    (clock : Node n → ℝ) (a : Fin v) : ℝ :=
  ∑ p : Fin (k+1), ∑ j,
    if D.allowed j none then
      (clock j + D.travel j none) * x a (left p) j * x a (right p) none
    else 0

def LiteralTiming {n v k} (D : Data n) (x : Array n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) : Prop :=
  (∀ i, customerRHS D x clock i ≤ clock (some i)) ∧
  (∀ a, returnRHS D x clock a ≤ ret a) ∧
  (∀ i, D.opening i ≤ clock (some i) ∧ clock (some i) ≤ D.closing i)

theorem customer_rhs_encode {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (i : Fin n) (h : SlotStructure D q) :
    customerRHS D (encode q) clock i =
      ∑ a, ∑ p : Fin (k+1), if q a (right p) = some i then
        clock (q a (left p)) + D.travel (q a (left p)) (some i) else 0 := by
  classical
  unfold customerRHS
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (q a (left p))]
  · by_cases hi : q a (right p) = some i
    · have ha := h.allowed a p
      rw [hi] at ha
      simp [encode, hi, ha]
    · simp [encode, hi]
  · intro j _ hj
    simp [encode, Ne.symm hj]
  · simp

theorem return_rhs_encode {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (a : Fin v) (h : SlotStructure D q) :
    returnRHS D (encode q) clock a =
      ∑ p : Fin (k+1), if q a (right p) = none then
        clock (q a (left p)) + D.travel (q a (left p)) none else 0 := by
  classical
  unfold returnRHS
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_eq_single (q a (left p))]
  · by_cases hi : q a (right p) = none
    · have ha := h.allowed a p
      rw [hi] at ha
      simp [encode, hi, ha]
    · simp [encode, hi]
  · intro j _ hj
    simp [encode, Ne.symm hj]
  · simp

theorem walkCost_ofFn {n m} (D : Data n) (f : Fin (m+1) → Node n) :
    walkCost D (List.ofFn f) =
      ∑ p : Fin m, D.cost (f p.castSucc) (f p.succ) := by
  induction m with
  | zero => simp [List.ofFn_succ, walkCost]
  | succ m ih =>
    rw [List.ofFn_succ]
    conv_lhs => arg 2; arg 2; rw [List.ofFn_succ]
    simp only [walkCost]
    have hh := ih (fun p => f p.succ)
    rw [List.ofFn_succ] at hh
    rw [hh, Fin.sum_univ_succ]
    rfl

theorem returnContribution_ofFn {n m} (D : Data n) (clock : Node n → ℝ)
    (f : Fin (m+1) → Node n) :
    returnContribution D clock (List.ofFn f) =
      ∑ p : Fin m, if f p.succ = none then
        clock (f p.castSucc) + D.travel (f p.castSucc) none else 0 := by
  induction m with
  | zero => simp [List.ofFn_succ, returnContribution]
  | succ m ih =>
    rw [List.ofFn_succ]
    conv_lhs => arg 3; arg 2; rw [List.ofFn_succ]
    simp only [returnContribution]
    have hh := ih (fun p => f p.succ)
    rw [List.ofFn_succ] at hh
    rw [hh, Fin.sum_univ_succ]
    rfl

theorem customerEdges_ofFn {n m} (D : Data n) (clock : Node n → ℝ)
    (f : Fin (m+1) → Node n) :
    customerEdges D clock (List.ofFn f) ↔
      ∀ p : Fin m, ∀ i, f p.succ = some i →
        clock (f p.castSucc) + D.travel (f p.castSucc) (some i) ≤ clock (some i) := by
  induction m with
  | zero => simp [List.ofFn_succ, customerEdges]
  | succ m ih =>
    rw [List.ofFn_succ]
    conv_lhs => arg 3; arg 2; rw [List.ofFn_succ]
    simp only [customerEdges]
    have hh := ih (fun p => f p.succ)
    rw [List.ofFn_succ] at hh
    rw [hh, Fin.forall_fin_succ]
    have he : ∀ p : Fin m, p.castSucc.succ = p.succ.castSucc := fun p => rfl
    cases h : f (Fin.succ 0) <;> simp only [h, he] <;> simp

theorem decoded_cost {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (hc : D.cost none none = 0) :
    objective D (encode q) = ∑ a, edgeCostFrom D none (decode q a) := by
  rw [objective_decode D q h]
  apply Finset.sum_congr rfl
  intro a _
  rw [← walkCost_ofFn]
  obtain ⟨padding, hp, _⟩ := slots_padded_trace h a
  rw [hp]
  exact padded_walk_cost_zero_idle D none (decode q a) padding hc

theorem return_rhs_decoded {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (clock : Node n → ℝ) (a : Fin v) :
    returnRHS D (encode q) clock a = returnContribution D clock (List.ofFn (q a)) := by
  rw [return_rhs_encode D q clock a h, returnContribution_ofFn]

/-- The literal return sum has one genuine return contribution and zero
padding contributions under the explicit depot repair. -/
theorem return_rhs_final {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (clock : Node n → ℝ) (a : Fin v)
    (hc : clock none = 0) (ht : D.travel none none = 0) :
    returnRHS D (encode q) clock a = FinalReturn D clock none (decode q a) := by
  rw [return_rhs_decoded D q h clock a]
  obtain ⟨padding,hp,_⟩ := slots_padded_trace h a
  rw [hp]
  change returnContribution D clock (paddedWalk none (decode q a) padding) = _
  rw [padded_return_contribution, hc, ht]
  ring

theorem idle_return_rhs_zero {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (clock : Node n → ℝ) (a : Fin v)
    (hc : clock none = 0) (ht : D.travel none none = 0) (hi : decode q a = []) :
    returnRHS D (encode q) clock a = 0 := by
  rw [return_rhs_final D q h clock a hc ht, hi]
  simp only [FinalReturn, hc, ht, add_zero]

theorem customer_has_incoming {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (i : Fin n) :
    ∃ a, ∃ p : Fin (k+1), q a (right p) = some i := by
  obtain ⟨ap, hi⟩ := customer_unique h i
  have hc : q ap.1 ap.2 = some i := (hi ap.1 ap.2).mpr rfl
  have hn : ap.2 ≠ 0 := by
    intro hz
    rw [hz, h.start_depot] at hc
    contradiction
  exact ⟨ap.1, ap.2.pred hn, by simpa only [right, Fin.succ_pred] using hc⟩

theorem customer_rhs_edge {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (h : SlotStructure D q)
    (a : Fin v) (p : Fin (k+1)) (i : Fin n) (hi : q a (right p) = some i) :
    customerRHS D (encode q) clock i =
      clock (q a (left p)) + D.travel (q a (left p)) (some i) := by
  classical
  rw [customer_rhs_encode D q clock i h, Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single p]
    · simp only [hi, ↓reduceIte]
    · intro r _ hr
      have hn : q a (right r) ≠ some i := by
        intro hc
        have he := (customer_positions_injective h hc hi).2
        exact hr (Fin.succ_injective _ he)
      simp only [if_neg hn]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro r _
    have hn : q b (right r) ≠ some i := by
      intro hc
      exact hb (customer_positions_injective h hc hi).1
    simp only [if_neg hn]
  · simp

theorem customer_rows_iff_edges {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (h : SlotStructure D q) :
    (∀ i, customerRHS D (encode q) clock i ≤ clock (some i)) ↔
      ∀ a, customerEdges D clock (List.ofFn (q a)) := by
  constructor
  · intro hc a
    apply (customerEdges_ofFn D clock (q a)).mpr
    intro p i hi
    rw [← customer_rhs_edge D q clock h a p i hi]
    exact hc i
  · intro hc i
    obtain ⟨a,p,hi⟩ := customer_has_incoming h i
    rw [customer_rhs_edge D q clock h a p i hi]
    exact (customerEdges_ofFn D clock (q a)).mp (hc a) p i hi

theorem mem_decode_of_incoming {n v k} (q : Slots n v k) (a : Fin v)
    (p : Fin (k+1)) (i : Fin n) (hi : q a (right p) = some i) : i ∈ decode q a := by
  apply List.mem_filterMap.mpr
  refine ⟨some i, List.mem_ofFn.mpr ⟨p, hi⟩, rfl⟩

theorem literal_timing_iff_schedules {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) (h : SlotStructure D q)
    (hc : clock none = 0) (ht : D.travel none none = 0) :
    LiteralTiming D (encode q) clock ret ↔
      ∀ a, ScheduleFrom D none 0 (decode q a)
        ((decode q a).map (fun j => clock (some j))) (ret a) := by
  have adapter : ∀ a, ScheduleFrom D none 0 (decode q a)
        ((decode q a).map (fun j => clock (some j))) (ret a) ↔
      CustomerWindows D clock (decode q a) ∧
      customerEdges D clock (List.ofFn (q a)) ∧ returnRHS D (encode q) clock a ≤ ret a := by
    intro a
    obtain ⟨padding, hp, _⟩ := slots_padded_trace h a
    rw [return_rhs_decoded D q h clock a, hp]
    exact (padded_timing_iff_schedule D clock (decode q a) padding (ret a) hc ht).symm
  constructor
  · rintro ⟨hi, hr, hw⟩ a
    apply (adapter a).mpr
    exact ⟨fun j _ => hw j, (customer_rows_iff_edges D q clock h).mp hi a, hr a⟩
  · intro hs
    have ha := fun a => (adapter a).mp (hs a)
    refine ⟨(customer_rows_iff_edges D q clock h).mpr (fun a => (ha a).2.1),
      fun a => (ha a).2.2, ?_⟩
    intro i
    obtain ⟨a,p,hi⟩ := customer_has_incoming h i
    exact (ha a).1 i (mem_decode_of_incoming q a p i hi)

theorem literal_timing_earliest_lower_bound {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) (h : SlotStructure D q)
    (hc : clock none = 0) (ht : D.travel none none = 0)
    (hs : LiteralTiming D (encode q) clock ret) :
    (∀ a, EarliestWithin D none 0 (decode q a)) ∧
      (∀ a, earliestReturn D none 0 (decode q a) ≤ ret a) ∧
      (∑ a, earliestReturn D none 0 (decode q a)) ≤ ∑ a, ret a := by
  have hd := (literal_timing_iff_schedules D q clock ret h hc ht).mp hs
  have he := fun a => earliest_dominates (le_refl (0 : ℝ)) (hd a)
  exact ⟨fun a => (he a).1, fun a => (he a).2.2,
    Finset.sum_le_sum (fun a _ => (he a).2.2)⟩

theorem mem_decode_iff {n v k} (q : Slots n v k) (a : Fin v) (i : Fin n) :
    i ∈ decode q a ↔ ∃ p : Fin (k+1), q a (right p) = some i := by
  simp only [decode, List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨x, ⟨p, hp⟩, hx⟩
    exact ⟨p, hp.trans hx⟩
  · rintro ⟨p,hp⟩
    exact ⟨some i, ⟨p,hp⟩, rfl⟩

theorem decode_disjoint_vehicles {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) {a b : Fin v} {i : Fin n}
    (ha : i ∈ decode q a) (hb : i ∈ decode q b) : a = b := by
  obtain ⟨p,hp⟩ := (mem_decode_iff q a i).mp ha
  obtain ⟨r,hr⟩ := (mem_decode_iff q b i).mp hb
  exact (customer_positions_injective h hp hr).1

/-- Concrete glue for the one shared clock per customer. Coverage, within-route
nodup and across-vehicle disjointness are proved from the literal source rows. -/
theorem exists_shared_clock {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (ss : Fin v → List ℝ)
    (hlen : ∀ a, (ss a).length = (decode q a).length) :
    ∃ clock : Node n → ℝ, clock none = 0 ∧
      ∀ a, (decode q a).map (fun i => clock (some i)) = ss a := by
  classical
  let Occ := Σ a : Fin v, Fin (decode q a).length
  let node : Occ → Fin n := fun ap => (decode q ap.1).get ap.2
  have hinj : Function.Injective node := by
    rintro ⟨a,p⟩ ⟨b,r⟩ he
    have ha : node ⟨a,p⟩ ∈ decode q a := List.get_mem _ _
    have hb : node ⟨a,p⟩ ∈ decode q b := by rw [he]; exact List.get_mem _ _
    have hab : a = b := decode_disjoint_vehicles h ha hb
    subst b
    have hpr : p = r := (decode_nodup h a).get_inj_iff.mp he
    subst r
    rfl
  have hsurj : Function.Surjective node := by
    intro i
    obtain ⟨a,p,hp⟩ := customer_has_incoming h i
    obtain ⟨r,hr⟩ := List.mem_iff_get.mp (mem_decode_of_incoming q a p i hp)
    exact ⟨⟨a,r⟩,hr⟩
  let e : Occ ≃ Fin n := Equiv.ofBijective node ⟨hinj,hsurj⟩
  let value : Occ → ℝ := fun ap => (ss ap.1).get (Fin.cast (hlen ap.1).symm ap.2)
  let clock : Node n → ℝ := fun i => match i with
    | none => 0
    | some j => value (e.symm j)
  refine ⟨clock, rfl, ?_⟩
  intro a
  apply List.ext_get (by simpa using (hlen a).symm)
  intro m hm hs
  have hm' : m < (decode q a).length := by simpa using hm
  have he : e.symm ((decode q a).get ⟨m,hm'⟩) = ⟨a,⟨m,hm'⟩⟩ :=
    e.symm_apply_apply ⟨a,⟨m,hm'⟩⟩
  simp only [List.get_eq_getElem, List.getElem_map]
  change value (e.symm ((decode q a).get ⟨m,hm'⟩)) = (ss a).get ⟨m,hs⟩
  rw [he]
  rfl

theorem earliest_literal_attainment {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0)
    (hw : ∀ a, EarliestWithin D none 0 (decode q a)) :
    ∃ clock : Node n → ℝ, clock none = 0 ∧
      LiteralTiming D (encode q) clock (fun a => earliestReturn D none 0 (decode q a)) := by
  obtain ⟨clock,hc,he⟩ := exists_shared_clock h
    (fun a => earliestTimes D none 0 (decode q a))
    (fun a => earliestTimes_length D none 0 (decode q a))
  refine ⟨clock,hc,(literal_timing_iff_schedules D q clock _ h hc ht).mpr ?_⟩
  intro a
  rw [he a]
  exact earliest_schedule (hw a)

theorem literal_timing_exists_iff {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0) :
    (∃ clock : Node n → ℝ, ∃ ret : Fin v → ℝ,
      clock none = 0 ∧ LiteralTiming D (encode q) clock ret) ↔
      ∀ a, EarliestWithin D none 0 (decode q a) := by
  constructor
  · rintro ⟨clock,ret,hc,hs⟩
    exact (literal_timing_earliest_lower_bound D q clock ret h hc ht hs).1
  · intro hw
    obtain ⟨clock,hc,hs⟩ := earliest_literal_attainment D q h ht hw
    exact ⟨clock,_,hc,hs⟩

/-- Actual duration attainment and a comparison with every feasible clock/return
assignment. It does not assert that arbitrary feasible return variables are tight. -/
theorem literal_duration_minimum {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0)
    (hw : ∀ a, EarliestWithin D none 0 (decode q a)) :
    (∃ clock : Node n → ℝ, clock none = 0 ∧
      LiteralTiming D (encode q) clock (fun a => earliestReturn D none 0 (decode q a))) ∧
    ∀ clock ret, clock none = 0 → LiteralTiming D (encode q) clock ret →
      (∑ a, earliestReturn D none 0 (decode q a)) ≤ ∑ a, ret a := by
  exact ⟨earliest_literal_attainment D q h ht hw,
    fun clock ret hc hs => (literal_timing_earliest_lower_bound D q clock ret h hc ht hs).2.2⟩

def closingClock {n} (D : Data n) : Node n → ℝ
  | none => 0
  | some i => D.closing i

/-- Conservative closing-window pruning is sufficient under explicit start
bounds. Depot entries have no finite upper-window pruning condition. -/
theorem closing_pruning_sufficient {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (hwin : orderedWindows D)
    (hstart : ∀ i, D.allowed none (some i) = true →
      D.travel none (some i) ≤ D.closing i)
    (hedge : ∀ i j, D.allowed (some i) (some j) = true →
      D.closing i + D.travel (some i) (some j) ≤ D.closing j) :
    LiteralTiming D (encode q) (closingClock D)
      (returnRHS D (encode q) (closingClock D)) := by
  refine ⟨?_, fun _ => le_refl _, ?_⟩
  · intro i
    obtain ⟨a,p,hi⟩ := customer_has_incoming h i
    rw [customer_rhs_edge D q (closingClock D) h a p i hi]
    have ha := h.allowed a p
    rw [hi] at ha
    cases hj : q a (left p) with
    | none => simpa [hj, closingClock] using hstart i (by simpa [hj] using ha)
    | some j => simpa [hj, closingClock] using hedge j i (by simpa [hj] using ha)
  · intro i
    exact ⟨hwin i, le_refl _⟩

end Chapter10.Sequence


