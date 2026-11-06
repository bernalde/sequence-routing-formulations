module

public import Chapter10SequenceTiming
public import Chapter10RouteAllowedPadding

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter10.Sequence
open Chapter10.Routing

theorem allowedWalk_ofFn {n m} (D : Data n) (f : Fin (m+1) → Node n) :
    AllowedWalk D (List.ofFn f) ↔
      ∀ p : Fin m, D.allowed (f p.castSucc) (f p.succ) = true := by
  induction m with
  | zero => simp [List.ofFn_succ, AllowedWalk]
  | succ m ih =>
    rw [List.ofFn_succ]
    conv_lhs => arg 2; arg 2; rw [List.ofFn_succ]
    simp only [AllowedWalk]
    have hh := ih (fun p => f p.succ)
    rw [List.ofFn_succ] at hh
    rw [hh, Fin.forall_fin_succ]
    rfl

theorem decoded_allowed {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (a : Fin v) : AllowedFrom D none (decode q a) := by
  have ha := (allowedWalk_ofFn D (q a)).mpr (h.allowed a)
  obtain ⟨padding,hp,_⟩ := slots_padded_trace h a
  rw [hp] at ha
  exact padded_allowed_forward ha

theorem literal_decodes_elementary_paths {n v k} (D : Data n) (x : Array n v k)
    (h : Literal D x) :
    ∃ q : Slots n v k, x = encode q ∧ SlotStructure D q ∧
      ∀ a, (decode q a).Nodup ∧ (decode q a).length ≤ k ∧
        AllowedFrom D none (decode q a) := by
  obtain ⟨q,rfl,hq⟩ := (literal_iff_decoded D x).mp h
  exact ⟨q,rfl,hq,fun a => ⟨decode_nodup hq a, decode_length_le hq a, decoded_allowed hq a⟩⟩

theorem literal_return_nonnegative {n v k} (D : Data n) (q : Slots n v k)
    (clock : Node n → ℝ) (ret : Fin v → ℝ) (h : SlotStructure D q)
    (hc : clock none = 0) (ht : D.travel none none = 0)
    (htravel : nonnegativeTravel D) (hs : LiteralTiming D (encode q) clock ret) :
    ∀ a, 0 ≤ ret a := by
  intro a
  have hd := (literal_timing_iff_schedules D q clock ret h hc ht).mp hs a
  exact (schedule_nonnegative htravel (le_refl (0 : ℝ)) (decoded_allowed h a) hd).2

theorem padded_tail_absorbing {n} (js : List (Fin n)) (padding : ℕ) :
    (js.map some ++ List.replicate (padding+1) none).Pairwise
      (fun i j => i = none → j = none) := by
  induction js with
  | nil => simp [List.pairwise_replicate]
  | cons j js ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih⟩
    intro i hi hn
    cases hn

/-- Reverse transport for an explicitly padded family of customer traces.
Coverage is the actual source customer-count sum; it is not inferred from
disjointness, elementarity, or the fleet labels. -/
theorem padded_family_to_literal {n v k} (D : Data n) (q : Slots n v k)
    (js : Fin v → List (Fin n)) (padding : Fin v → ℕ)
    (hshape : ∀ a, List.ofFn (q a) = paddedWalk none (js a) (padding a))
    (hcover : CustomerOnce (encode q)) (ha : ∀ a, AllowedFrom D none (js a))
    (hdd : D.allowed none none = true) : Literal D (encode q) := by
  apply slots_to_literal
  refine ⟨hcover, ?_, ?_, ?_, ?_⟩
  · intro a
    have hh := congrArg List.head? (hshape a)
    simpa [List.ofFn_succ, paddedWalk] using hh
  · intro a
    have hh := congrArg List.getLast? (hshape a)
    have hlo : (List.ofFn (q a)).getLast? = some (q a (last k)) := by
      rw [List.getLast?_eq_getLast (by simp)]
      congr 1
      exact List.getLast_ofFn _
    rw [hlo] at hh
    have hr : (paddedWalk (none : Node n) (js a) (padding a)).getLast? = some none := by
      change (([none] ++ (js a).map some) ++ List.replicate (padding a+1) none).getLast? = _
      rw [List.getLast?_append, List.getLast?_replicate]
      simp
    rw [hr] at hh
    exact Option.some.inj hh
  · intro a
    apply (allowedWalk_ofFn D (q a)).mp
    rw [hshape a]
    exact padded_allowed_reverse (ha a) hdd
  · intro a p hp hn
    have hh := congrArg List.tail (hshape a)
    rw [List.ofFn_succ] at hh
    change List.ofFn (fun r : Fin (k+1) => q a r.succ) =
      (js a).map some ++ List.replicate (padding a+1) none at hh
    have hpair := padded_tail_absorbing (js a) (padding a)
    rw [← hh] at hpair
    have horder := List.pairwise_ofFn.mp hpair
    let i : Fin (k+1) := ⟨p.val-1, by omega⟩
    have hi : i.succ = left p := by apply Fin.ext; dsimp [i, left]; omega
    have hij : i < p := by change p.val-1 < p.val; omega
    exact horder hij (by simpa only [hi] using hn)

/-- Direct finite indexing of depot/customer/depot padding, with the proof of
its length carried by the input bound rather than an unchecked array access. -/
def padSlots {n v k} (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) : Slots n v k :=
  fun a p => (paddedWalk none (js a) (k-(js a).length))[p.val]'(by
    simp only [paddedWalk, List.length_cons, List.length_append, List.length_map,
      List.length_replicate]
    have hh := hlen a
    have hp := p.isLt
    omega)

theorem padSlots_shape {n v k} (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (a : Fin v) :
    List.ofFn (padSlots js hlen a) = paddedWalk none (js a) (k-(js a).length) := by
  apply List.ext_get
  · simp only [List.length_ofFn, paddedWalk, List.length_cons, List.length_append,
      List.length_map, List.length_replicate]
    have hh := hlen a
    omega
  · intro p hp hq
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    rfl

theorem sum_indicator_ofFn_count {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] {m : ℕ}
    (f : Fin m → α) (i : α) :
    (∑ p, if f p = i then (1 : ℝ) else 0) = ((List.ofFn f).count i : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ]
    rw [ih]
    by_cases he : f 0 = i
    · simp [List.count_cons, he, add_comm]
    · simp [List.count_cons, he, Ne.symm he]

theorem padded_customer_count {n} (js : List (Fin n)) (padding : ℕ) (i : Fin n) :
    (paddedWalk none js padding).count (some i) = js.count i := by
  simp only [paddedWalk, List.count_cons, List.count_append]
  have hm : (js.map some).count (some i) = js.count i := by
    induction js with
    | nil => rfl
    | cons j js ih => simp [List.count_cons, ih]
  rw [hm]
  simp [List.count_replicate]

theorem padSlots_customer_once {n v k} (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (hcover : ∀ i, ∑ a, (js a).count i = 1) :
    CustomerOnce (encode (padSlots js hlen)) := by
  intro i
  have he : ∀ a, (∑ p, encode (padSlots js hlen) a p (some i)) = ((js a).count i : ℝ) := by
    intro a
    rw [show (∑ p, encode (padSlots js hlen) a p (some i)) =
      ((List.ofFn (padSlots js hlen a)).count (some i) : ℝ) from
      sum_indicator_ofFn_count (padSlots js hlen a) (some i)]
    rw [padSlots_shape, padded_customer_count]
  simp_rw [he]
  exact_mod_cast hcover i

theorem padSlots_decode {n v k} (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (a : Fin v) : decode (padSlots js hlen) a = js a := by
  have hh := congrArg List.tail (padSlots_shape js hlen a)
  rw [List.ofFn_succ] at hh
  change List.ofFn (fun p : Fin (k+1) => padSlots js hlen a p.succ) =
    (js a).map some ++ List.replicate (k-(js a).length+1) none at hh
  unfold decode
  rw [hh]
  simp

theorem bounded_traces_encode {n v k} (D : Data n) (js : Fin v → List (Fin n))
    (hlen : ∀ a, (js a).length ≤ k) (hcover : ∀ i, ∑ a, (js a).count i = 1)
    (ha : ∀ a, AllowedFrom D none (js a)) (hdd : D.allowed none none = true)
    (hc : D.cost none none = 0) :
    Literal D (encode (padSlots js hlen)) ∧
      (∀ a, decode (padSlots js hlen) a = js a) ∧
      objective D (encode (padSlots js hlen)) = ∑ a, edgeCostFrom D none (js a) := by
  have hl := padded_family_to_literal D (padSlots js hlen) js (fun a => k-(js a).length)
    (padSlots_shape js hlen) (padSlots_customer_once js hlen hcover) ha hdd
  refine ⟨hl, padSlots_decode js hlen, ?_⟩
  rw [decoded_cost D (padSlots js hlen) (literal_to_slots hl) hc]
  simp_rw [padSlots_decode]

end Chapter10.Sequence

