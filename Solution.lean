module

public import Chapter10SequenceRoutes

/-! Thin theorem aliases to exact reused source proofs. The Challenge is never
imported here, and no accepted proof body is modified. -/
public section
noncomputable section
open scoped BigOperators
namespace Chapter10.Sequence
open Chapter10.Routing

theorem palomar_literal_iff_decoded {n v k} (D : Data n) (x : Array n v k) :
    Literal D x ↔ ∃ q : Slots n v k, x = encode q ∧ SlotStructure D q := by
  exact literal_iff_decoded D x

theorem palomar_literal_decodes_elementary_paths {n v k} (D : Data n) (x : Array n v k)
    (h : Literal D x) :
    ∃ q : Slots n v k, x = encode q ∧ SlotStructure D q ∧
      ∀ a, (decode q a).Nodup ∧ (decode q a).length ≤ k ∧
        AllowedFrom D none (decode q a) := by
  exact literal_decodes_elementary_paths D x h

theorem palomar_bounded_traces_encode {n v k} (D : Data n) (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (hcover : ∀ i, ∑ a, (js a).count i = 1)
    (ha : ∀ a, AllowedFrom D none (js a)) (hdd : D.allowed none none = true)
    (hc : D.cost none none = 0) :
    Literal D (encode (padSlots js hlen)) ∧
      (∀ a, decode (padSlots js hlen) a = js a) ∧
      objective D (encode (padSlots js hlen)) = ∑ a, edgeCostFrom D none (js a) := by
  exact bounded_traces_encode D js hlen hcover ha hdd hc

theorem palomar_decoded_cost {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (hc : D.cost none none = 0) :
    objective D (encode q) = ∑ a, edgeCostFrom D none (decode q a) := by
  exact decoded_cost D q h hc

theorem palomar_literal_timing_iff_schedules {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) (h : SlotStructure D q)
    (hc : clock none = 0) (ht : D.travel none none = 0) :
    LiteralTiming D (encode q) clock ret ↔
      ∀ a, ScheduleFrom D none 0 (decode q a)
        ((decode q a).map (fun j => clock (some j))) (ret a) := by
  exact literal_timing_iff_schedules D q clock ret h hc ht

theorem palomar_literal_timing_exists_iff {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0) :
    (∃ clock : Node n → ℝ, ∃ ret : Fin v → ℝ,
      clock none = 0 ∧ LiteralTiming D (encode q) clock ret) ↔
      ∀ a, EarliestWithin D none 0 (decode q a) := by
  exact literal_timing_exists_iff D q h ht

theorem palomar_literal_duration_minimum {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) (ht : D.travel none none = 0)
    (hw : ∀ a, EarliestWithin D none 0 (decode q a)) :
    (∃ clock : Node n → ℝ, clock none = 0 ∧
      LiteralTiming D (encode q) clock (fun a => earliestReturn D none 0 (decode q a))) ∧
    ∀ clock ret, clock none = 0 → LiteralTiming D (encode q) clock ret →
      (∑ a, earliestReturn D none 0 (decode q a)) ≤ ∑ a, ret a := by
  exact literal_duration_minimum D q h ht hw

end Chapter10.Sequence
