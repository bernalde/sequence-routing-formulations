module

public import Chapter02Model
public import Mathlib.Tactic

@[expose] public section

/-! Literal finite route-incidence penalty model. Routing validity of supplied
columns, quantum optimization and ADMM convergence are separate obligations. -/
noncomputable section
open scoped BigOperators
namespace Chapter10

abbrev Bits (n : ℕ) := Fin n → Bool

def bit (b : Bool) : ℝ := if b then 1 else 0

def coverCount {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) (i : Fin m) : ℕ :=
  ∑ r, if A i r && x r then 1 else 0

theorem literal_incidence_sum {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) (i : Fin m) :
    (coverCount A x i : ℝ) = ∑ r, bit (A i r) * bit (x r) := by
  simp only [coverCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r _
  cases hA : A i r <;> cases hx : x r <;> simp [bit, hA, hx]

def feasible {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) : Prop :=
  ∀ i, coverCount A x i = 1

def cost {n : ℕ} (c : Fin n → ℝ) (x : Bits n) : ℝ := ∑ r, c r * bit (x r)

def penalty {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) : ℝ :=
  ∑ i, ((coverCount A x i : ℝ) - 1)^2

def energy {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ)
    (ρ : ℝ) (x : Bits n) : ℝ := cost c x + ρ * penalty A x

def routeMin {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ) (x : Bits n) : Prop :=
  feasible A x ∧ ∀ y, feasible A y → cost c x ≤ cost c y

def energyMin {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ)
    (ρ : ℝ) (x : Bits n) : Prop := ∀ y, energy A c ρ x ≤ energy A c ρ y

theorem binary_cost_change (c : ℝ) (a b : Bool) : c * bit a - c * bit b ≤ |c| := by
  cases a <;> cases b <;> simp only [bit, Bool.false_eq_true, ↓reduceIte, mul_zero, mul_one, sub_zero, sub_self, zero_sub]
  · exact abs_nonneg c
  · exact neg_le_abs c
  · exact le_abs_self c
  · exact abs_nonneg c

theorem cost_range_bound {n : ℕ} (c : Fin n → ℝ) (x y : Bits n) :
    cost c x - cost c y ≤ ∑ r, |c r| := by
  unfold cost
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun r _ => binary_cost_change (c r) (x r) (y r))

theorem integer_cover_residual_gap (k : ℕ) (hk : k ≠ 1) : (1 : ℝ) ≤ ((k : ℝ) - 1)^2 := by
  rcases k with _ | k
  · norm_num
  · have hn : 2 ≤ k+1 := by omega
    have hr : (2 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast hn
    nlinarith [sq_nonneg ((k+1 : ℕ) - (1 : ℝ))]

theorem penalty_nonnegative {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) :
    0 ≤ penalty A x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem feasible_penalty_zero {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n)
    (hf : feasible A x) : penalty A x = 0 := by
  have hh : ∀ i, coverCount A x i = 1 := hf
  simp [penalty, hh]

theorem infeasible_penalty_gap {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n)
    (hf : ¬ feasible A x) : (1 : ℝ) ≤ penalty A x := by
  obtain ⟨i, hi⟩ := not_forall.mp hf
  have hrow := integer_cover_residual_gap (coverCount A x i) hi
  have hsum : ((coverCount A x i : ℝ) - 1)^2 ≤ penalty A x := by
    unfold penalty
    exact Finset.single_le_sum (fun j _ => sq_nonneg ((coverCount A x j : ℝ) - 1)) (Finset.mem_univ i)
  exact hrow.trans hsum

theorem penalty_zero_iff_feasible {m n : ℕ} (A : Fin m → Fin n → Bool) (x : Bits n) :
    penalty A x = 0 ↔ feasible A x := by
  constructor
  · intro hz
    by_contra hf
    have hg := infeasible_penalty_gap A x hf
    linarith
  · exact feasible_penalty_zero A x

theorem feasible_energy {m n : ℕ} (A : Fin m → Fin n → Bool) (c : Fin n → ℝ)
    (ρ : ℝ) (x : Bits n) (hf : feasible A x) : energy A c ρ x = cost c x := by
  simp [energy, feasible_penalty_zero A x hf]

theorem bad_energy_exceeds_every_feasible {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ) (x y : Bits n)
    (hbad : ¬ feasible A x) (hgood : feasible A y) : energy A c ρ y < energy A c ρ x := by
  have hnorm : (0 : ℝ) ≤ ∑ r, |c r| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hr : 0 < ρ := hnorm.trans_lt hρ
  have hg := infeasible_penalty_gap A x hbad
  have hd := cost_range_bound c y x
  rw [feasible_energy A c ρ y hgood]
  unfold energy
  nlinarith

theorem route_min_implies_energy_min {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ) (x : Bits n)
    (hx : routeMin A c x) : energyMin A c ρ x := by
  intro y
  by_cases hy : feasible A y
  · simpa [feasible_energy A c ρ x hx.1, feasible_energy A c ρ y hy] using hx.2 y hy
  · exact (bad_energy_exceeds_every_feasible A c ρ hρ y x hy hx.1).le

theorem energy_min_implies_route_min {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ)
    (hnonempty : ∃ y, feasible A y) (x : Bits n) (hx : energyMin A c ρ x) : routeMin A c x := by
  have hf : feasible A x := by
    by_contra hbad
    obtain ⟨y, hy⟩ := hnonempty
    have ht := bad_energy_exceeds_every_feasible A c ρ hρ x y hbad hy
    exact (not_lt_of_ge (hx y)) ht
  refine ⟨hf, ?_⟩
  intro y hy
  simpa [feasible_energy A c ρ x hf, feasible_energy A c ρ y hy] using hx y

theorem literal_route_penalty_minimizers_exact {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ)
    (hnonempty : ∃ y, feasible A y) (x : Bits n) :
    routeMin A c x ↔ energyMin A c ρ x :=
  ⟨route_min_implies_energy_min A c ρ hρ x,
    energy_min_implies_route_min A c ρ hρ hnonempty x⟩

theorem source_route_penalty_proposition {m n : ℕ} (A : Fin m → Fin n → Bool)
    (c : Fin n → ℝ) (ρ : ℝ) (hρ : (∑ r, |c r|) < ρ) (x : Bits n) :
    (energyMin A c ρ x ∧ ∃ y, feasible A y) ↔ routeMin A c x := by
  constructor
  · intro h
    exact energy_min_implies_route_min A c ρ hρ h.2 x h.1
  · intro h
    exact ⟨route_min_implies_energy_min A c ρ hρ x h, x, h.1⟩

theorem binary_scalar_qubo_constant (a b c ρ x : ℝ) (hx : x = 0 ∨ x = 1) :
    c*x + ρ*(a*x-b)^2 = (ρ*a^2 - 2*ρ*a*b + c)*x^2 + ρ*b^2 := by
  rcases hx with rfl | rfl <;> ring

theorem missing_penalty_constant_witness : (2 : ℝ)*(0-1)^2 ≠ 1^2 := by norm_num

theorem real_residual_bound_counterexample :
    (2 : ℝ) > |1| ∧ 2*((1/10)*0-1/10)^2 < 1 + 2*((1/10)*1-1/10)^2 := by norm_num

theorem exact_threshold_can_tie : (1 : ℝ) * (0-1)^2 = 1 + 1*(1-1)^2 := by norm_num

theorem two_customer_partial_routes_exceed_factorial : (4 : ℕ) > Nat.factorial 2 := by norm_num

theorem capacity_peak_witness : (3 : ℝ) > 2 ∧ 0 ≤ 3 - 2 ∧ 3 - 2 ≤ 2 := by norm_num

theorem heterogeneous_shots_average_witness :
    (((1 : ℝ) - (1-1/10)^2) + (1-(1-9/10)^2))/2 < 1-(1-1/2)^2 := by norm_num

theorem printed_success_percentage_witness : (90 / 250 : ℝ) = 36/100 ∧ (90 /250 : ℝ) ≠ 32/100 := by norm_num

end Chapter10

#print axioms Chapter10.binary_cost_change
#print axioms Chapter10.cost_range_bound
#print axioms Chapter10.integer_cover_residual_gap
#print axioms Chapter10.penalty_nonnegative
#print axioms Chapter10.feasible_penalty_zero
#print axioms Chapter10.infeasible_penalty_gap
#print axioms Chapter10.penalty_zero_iff_feasible
#print axioms Chapter10.feasible_energy
#print axioms Chapter10.bad_energy_exceeds_every_feasible
#print axioms Chapter10.route_min_implies_energy_min
#print axioms Chapter10.energy_min_implies_route_min
#print axioms Chapter10.literal_route_penalty_minimizers_exact
#print axioms Chapter10.binary_scalar_qubo_constant
#print axioms Chapter10.missing_penalty_constant_witness
#print axioms Chapter10.real_residual_bound_counterexample
#print axioms Chapter10.exact_threshold_can_tie
#print axioms Chapter10.two_customer_partial_routes_exceed_factorial
#print axioms Chapter10.capacity_peak_witness

#print axioms Chapter10.literal_incidence_sum
#print axioms Chapter10.source_route_penalty_proposition
#print axioms Chapter10.heterogeneous_shots_average_witness
#print axioms Chapter10.printed_success_percentage_witness
