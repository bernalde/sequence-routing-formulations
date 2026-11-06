module

public import Chapter10

@[expose] public section

/-! Shared finite source data for the separately reviewed Chapter10 proposal02.
No route/penalty/convergence result is assumed by these definitions. -/
noncomputable section
namespace Chapter10.Routing

abbrev Node (n : ℕ) := Option (Fin n)

structure Data (n : ℕ) where
  allowed : Node n → Node n → Bool
  travel : Node n → Node n → ℝ
  cost : Node n → Node n → ℝ
  opening : Fin n → ℝ
  closing : Fin n → ℝ
  demand : Fin n → ℝ
  initialLoad : ℝ
  capacity : ℝ

def inWindow {n : ℕ} (D : Data n) (i : Node n) (s : ℝ) : Prop :=
  match i with
  | none => 0 ≤ s
  | some j => D.opening j ≤ s ∧ s ≤ D.closing j

def nonnegativeTravel {n : ℕ} (D : Data n) : Prop :=
  ∀ i j, D.allowed i j = true → 0 ≤ D.travel i j

def orderedWindows {n : ℕ} (D : Data n) : Prop :=
  ∀ i, D.opening i ≤ D.closing i

end Chapter10.Routing
