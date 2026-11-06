module

public import Chapter10RoutingData

@[expose] public section

/-! Literal (10.4), with P = k+2 and zero-based finite positions. The initial
depot is excluded from the absorbing product rows, exactly as printed. -/
noncomputable section
open scoped BigOperators
namespace Chapter10.Sequence
open Chapter10.Routing

abbrev Array (n v k : ℕ) := Fin v → Fin (k+2) → Node n → ℝ
abbrev Slots (n v k : ℕ) := Fin v → Fin (k+2) → Node n
abbrev first (k : ℕ) : Fin (k+2) := 0
abbrev last (k : ℕ) : Fin (k+2) := Fin.last (k+1)
abbrev second (k : ℕ) : Fin (k+2) := ⟨1, by omega⟩
abbrev penultimate (k : ℕ) : Fin (k+2) := ⟨k, by omega⟩
abbrev left {k : ℕ} (p : Fin (k+1)) : Fin (k+2) := p.castSucc
abbrev right {k : ℕ} (p : Fin (k+1)) : Fin (k+2) := p.succ

def Binary {n v k} (x : Array n v k) : Prop :=
  ∀ a p i, x a p i = 0 ∨ x a p i = 1
def CustomerOnce {n v k} (x : Array n v k) : Prop :=
  ∀ i : Fin n, ∑ a, ∑ p, x a p (some i) = 1
def PositionOnce {n v k} (x : Array n v k) : Prop :=
  ∀ a p, ∑ i, x a p i = 1
def AllowedProducts {n v k} (D : Data n) (x : Array n v k) : Prop :=
  ∀ a p i j, D.allowed i j = false → x a (left p) i * x a (right p) j = 0
def AbsorbingProducts {n v k} (x : Array n v k) : Prop :=
  ∀ a (p : Fin (k+1)) (j : Fin n), 0 < p.val →
    x a (left p) none * x a (right p) (some j) = 0

structure FixedRows {n v k} (D : Data n) (x : Array n v k) : Prop where
  start_depot : ∀ a, x a (first k) none = 1
  end_depot : ∀ a, x a (last k) none = 1
  start_customer : ∀ a i, x a (first k) (some i) = 0
  end_customer : ∀ a i, x a (last k) (some i) = 0
  impossible_departure : ∀ a j, D.allowed none j = false → x a (second k) j = 0
  impossible_return : ∀ a j, D.allowed j none = false → x a (penultimate k) j = 0

structure Literal {n v k} (D : Data n) (x : Array n v k) : Prop where
  binary : Binary x
  customer_once : CustomerOnce x
  position_once : PositionOnce x
  allowed : AllowedProducts D x
  absorbing : AbsorbingProducts x
  fixed : FixedRows D x

def objective {n v k} (D : Data n) (x : Array n v k) : ℝ :=
  ∑ a, ∑ p : Fin (k+1), ∑ i, ∑ j,
    if D.allowed i j then D.cost i j * x a (left p) i * x a (right p) j else 0

def encode {n v k} (q : Slots n v k) : Array n v k :=
  fun a p i => if q a p = i then 1 else 0

theorem encode_binary {n v k} (q : Slots n v k) : Binary (encode q) := by
  intro a p i
  by_cases h : q a p = i <;> simp [encode, h]

theorem encode_position_once {n v k} (q : Slots n v k) : PositionOnce (encode q) := by
  classical
  intro a p
  simp [encode, eq_comm]

theorem binary_nonneg {n v k} {x : Array n v k} (h : Binary x) (a p i) : 0 ≤ x a p i := by
  rcases h a p i with h | h <;> simp [h]

theorem one_hot {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (hb : ∀ i, x i = 0 ∨ x i = 1) (hs : ∑ i, x i = 1) :
    ∃ i, ∀ j, x j = if i = j then 1 else 0 := by
  classical
  have hn : ∀ i, 0 ≤ x i := by intro i; rcases hb i with h | h <;> simp [h]
  have he : ∃ i, x i = 1 := by
    by_contra h
    push_neg at h
    have hz : ∀ i, x i = 0 := fun i => (hb i).resolve_right (h i)
    simp [hz] at hs
  obtain ⟨i, hi⟩ := he
  refine ⟨i, ?_⟩
  intro j
  by_cases hij : i = j
  · simpa [hij] using hi
  · rw [if_neg hij]
    have hez : ∑ l ∈ (Finset.univ.erase i), x l = 0 := by
      have ht := Finset.sum_erase_add (s := Finset.univ) x (Finset.mem_univ i)
      rw [hs, hi] at ht
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hn l)).mp hez j
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)

theorem one_hot_encoding {n v k} {x : Array n v k}
    (hb : Binary x) (hp : PositionOnce x) : ∃ q : Slots n v k, x = encode q := by
  classical
  have h := fun a p => one_hot (x a p) (hb a p) (hp a p)
  choose q hq using h
  exact ⟨q, funext fun a => funext fun p => funext fun i => hq a p i⟩

structure SlotStructure {n v k} (D : Data n) (q : Slots n v k) : Prop where
  customer_once : CustomerOnce (encode q)
  start_depot : ∀ a, q a (first k) = none
  end_depot : ∀ a, q a (last k) = none
  allowed : ∀ a p, D.allowed (q a (left p)) (q a (right p)) = true
  absorbing : ∀ a (p : Fin (k+1)), 0 < p.val → q a (left p) = none →
    q a (right p) = none

theorem literal_to_slots {n v k} {D : Data n} {q : Slots n v k}
    (h : Literal D (encode q)) : SlotStructure D q := by
  classical
  refine ⟨h.customer_once, ?_, ?_, ?_, ?_⟩
  · intro a
    by_contra hn
    simpa [encode, hn] using h.fixed.start_depot a
  · intro a
    by_contra hn
    simpa [encode, hn] using h.fixed.end_depot a
  · intro a p
    by_contra hn
    have hf : D.allowed (q a (left p)) (q a (right p)) = false := by
      cases he : D.allowed (q a (left p)) (q a (right p)) <;> simp_all
    have hz := h.allowed a p (q a (left p)) (q a (right p)) hf
    simp [encode] at hz
  · intro a p hp hn
    cases he : q a (right p) with
    | none => rfl
    | some j =>
      have hz := h.absorbing a p j hp
      simp [encode, hn, he] at hz

theorem slots_to_literal {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) : Literal D (encode q) := by
  classical
  refine ⟨encode_binary q, h.customer_once, encode_position_once q, ?_, ?_, ?_⟩
  · intro a p i j hd
    by_cases hi : q a (left p) = i
    · by_cases hj : q a (right p) = j
      · have ht := h.allowed a p
        rw [hi, hj, hd] at ht
        contradiction
      · simp [encode, hj]
    · simp [encode, hi]
  · intro a p j hp
    by_cases hn : q a (left p) = none
    · simp [encode, hn, h.absorbing a p hp hn]
    · simp [encode, hn]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a; simp [encode, h.start_depot a]
    · intro a; simp [encode, h.end_depot a]
    · intro a i; simp [encode, h.start_depot a]
    · intro a i; simp [encode, h.end_depot a]
    · intro a j hd
      by_cases hj : q a (second k) = j
      · have ht := h.allowed a (0 : Fin (k+1))
        have hl : left (0 : Fin (k+1)) = first k := rfl
        have hr : right (0 : Fin (k+1)) = second k := rfl
        rw [hl, hr, h.start_depot, hj, hd] at ht
        contradiction
      · exact if_neg hj
    · intro a j hd
      by_cases hj : q a (penultimate k) = j
      · have ht := h.allowed a (Fin.last k)
        have hl : left (Fin.last k) = penultimate k := rfl
        have hr : right (Fin.last k) = last k := rfl
        rw [hl, hr, h.end_depot, hj, hd] at ht
        contradiction
      · simp [encode, hj]

theorem literal_iff_decoded {n v k} (D : Data n) (x : Array n v k) :
    Literal D x ↔ ∃ q : Slots n v k, x = encode q ∧ SlotStructure D q := by
  constructor
  · intro h
    obtain ⟨q, rfl⟩ := one_hot_encoding h.binary h.position_once
    exact ⟨q, rfl, literal_to_slots h⟩
  · rintro ⟨q, rfl, h⟩
    exact slots_to_literal h

theorem objective_encode {n v k} (D : Data n) (q : Slots n v k) :
    objective D (encode q) = ∑ a, ∑ p : Fin (k+1),
      if D.allowed (q a (left p)) (q a (right p)) then
        D.cost (q a (left p)) (q a (right p)) else 0 := by
  classical
  unfold objective
  congr 1
  funext a
  congr 1
  funext p
  have inner : ∀ i, (∑ j, if D.allowed i j then
      D.cost i j * encode q a (left p) i * encode q a (right p) j else 0) =
      (if D.allowed i (q a (right p)) then
        D.cost i (q a (right p)) * encode q a (left p) i else 0) := by
    intro i
    rw [Finset.sum_eq_single (q a (right p))]
    · simp [encode]
    · intro j _ hj
      simp [encode, Ne.symm hj]
    · simp
  simp_rw [inner]
  rw [Finset.sum_eq_single (q a (left p))]
  · simp [encode]
  · intro i _ hi
    simp [encode, Ne.symm hi]
  · simp

theorem objective_decode {n v k} (D : Data n) (q : Slots n v k)
    (h : SlotStructure D q) : objective D (encode q) =
    ∑ a, ∑ p : Fin (k+1), D.cost (q a (left p)) (q a (right p)) := by
  rw [objective_encode]
  simp [h.allowed]

theorem customer_unique {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (i : Fin n) :
    ∃ ap : Fin v × Fin (k+2), ∀ a p, q a p = some i ↔ (a,p) = ap := by
  classical
  have hb : ∀ ap : Fin v × Fin (k+2),
      encode q ap.1 ap.2 (some i) = 0 ∨ encode q ap.1 ap.2 (some i) = 1 :=
    fun ap => encode_binary q ap.1 ap.2 (some i)
  have hs : ∑ ap : Fin v × Fin (k+2), encode q ap.1 ap.2 (some i) = 1 := by
    simpa only [Fintype.sum_prod_type] using h.customer_once i
  obtain ⟨ap, ha⟩ := one_hot _ hb hs
  refine ⟨ap, ?_⟩
  intro a p
  have ht := ha (a,p)
  constructor
  · intro hi
    by_contra he
    simp [encode, hi, Ne.symm he] at ht
  · intro he
    have he' : ap = (a,p) := he.symm
    simp only [he', if_pos rfl] at ht
    by_contra hi
    simp [encode, hi] at ht

theorem customer_positions_injective {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) {a b : Fin v} {p r : Fin (k+2)} {i : Fin n}
    (hp : q a p = some i) (hr : q b r = some i) : a = b ∧ p = r := by
  obtain ⟨ap, hi⟩ := customer_unique h i
  have he : (a,p) = (b,r) := (hi a p).mp hp |>.trans ((hi b r).mp hr).symm
  exact Prod.mk.inj he

theorem depot_persists {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (a : Fin v) (i j : Fin (k+2))
    (hi : 0 < i.val) (hij : i.val ≤ j.val) (hn : q a i = none) : q a j = none := by
  have aux : ∀ t (ht : t < k+2), i.val ≤ t → q a ⟨t,ht⟩ = none := by
    intro t
    induction t with
    | zero => intro ht hle; omega
    | succ t ih =>
      intro ht hle
      by_cases he : i.val = t+1
      · have hf : i = (⟨t+1,ht⟩ : Fin (k+2)) := Fin.ext he
        simpa only [← hf] using hn
      · have hl : i.val ≤ t := by omega
        have hp : t < k+1 := by omega
        have hz := ih (by omega) hl
        exact h.absorbing a ⟨t,hp⟩ (by change 0 < t; omega) hz
  exact aux j.val j.isLt hij

/-- Decoding drops the initial depot and all padding, preserving customer order. -/
def decode {n v k} (q : Slots n v k) (a : Fin v) : List (Fin n) :=
  (List.ofFn fun p : Fin (k+1) => q a p.succ).filterMap id

theorem decode_nodup {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (a : Fin v) : (decode q a).Nodup := by
  have hp : (List.ofFn fun p : Fin (k+1) => q a p.succ).Pairwise
      (fun x y => ∀ i : Fin n, x = some i → y ≠ some i) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij c hi hj
    have he := (customer_positions_injective h hi hj).2
    have hh : i = j := Fin.succ_injective _ he
    subst j
    exact (lt_irrefl i) hij
  exact hp.filterMap id (by
    intro x y hxy i hi j hj he
    subst j
    exact hxy i (by simpa using hi) (by simpa using hj))

theorem option_list_padding {α : Type*} (l : List (Option α))
    (hp : l.Pairwise (fun x y => x = none → y = none)) (hn : none ∈ l) :
    ∃ js : List α, ∃ padding : ℕ,
      l = js.map some ++ List.replicate (padding+1) none := by
  induction l with
  | nil => simp at hn
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp hp
    cases x with
    | none =>
      refine ⟨[], xs.length, ?_⟩
      have he : xs = List.replicate xs.length none :=
        List.eq_replicate_length.mpr (fun y hy => hx y hy rfl)
      simpa only [List.map_nil, List.nil_append, List.replicate_succ] using
        congrArg (List.cons none) he
    | some j =>
      obtain ⟨js, padding, he⟩ := ih hxs (by simpa using hn)
      exact ⟨j::js, padding, by simp [he]⟩

theorem slots_padded_trace {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (a : Fin v) :
    ∃ padding : ℕ, List.ofFn (q a) =
      none :: ((decode q a).map some ++ List.replicate (padding+1) none) ∧
      (decode q a).length + padding = k := by
  have hp : (List.ofFn fun p : Fin (k+1) => q a p.succ).Pairwise
      (fun x y => x = none → y = none) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij hi
    exact depot_persists h a i.succ j.succ (by simp) (by
      simp only [Fin.val_succ]; exact Nat.add_le_add_right hij.le 1) hi
  have hn : none ∈ (List.ofFn fun p : Fin (k+1) => q a p.succ) := by
    apply List.mem_ofFn.mpr
    exact ⟨Fin.last k, h.end_depot a⟩
  obtain ⟨js, padding, he⟩ := option_list_padding _ hp hn
  have hd : decode q a = js := by
    simp only [decode, he, List.filterMap_append]
    simp
  refine ⟨padding, ?_, ?_⟩
  · rw [List.ofFn_succ, h.start_depot, he, hd]
  · have hl := congrArg List.length he
    simp at hl
    rw [hd]
    omega

theorem decode_length_le {n v k} {D : Data n} {q : Slots n v k}
    (h : SlotStructure D q) (a : Fin v) : (decode q a).length ≤ k := by
  obtain ⟨padding, _, hl⟩ := slots_padded_trace h a
  omega

end Chapter10.Sequence

